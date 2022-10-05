use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::Sign;
use num_bigint::{BigInt, BigUint};
use num_traits::ops::overflowing;
use num_traits::{One, Signed, Zero};
use std::ops::Shl;

use super::*;
use crate::gates::flex_gate::GateStrategy;
use crate::gates::range::RangeStrategy;
use crate::utils::modulus as native_modulus;
use crate::{gates::*, utils::*};

use super::{check_carry_to_zero, CRTInteger, OverflowInteger};
use crate::gates::{
    Context, GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::{bigint_to_fe, biguint_to_fe, decompose_bigint_option, decompose_biguint};

/// Input `a` is `OverflowInteger` of length `ka` with "signed" limbs
/// Output is `a (mod modulus)` as a proper BigInt of length `num_limbs` with limbs in [0, 2^limb_bits)`
/// * `ka` can be `>= num_limbs`
/// The witness for `out` is a BigInt in [0, modulus), but we do not constrain the inequality
/// We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    modulus: &BigUint,
    num_limbs: usize,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let ka = a.limbs.len();
    assert!(ka >= num_limbs);
    assert!(modulus.bits() <= (n * num_limbs) as u64);

    // quot <= ceil(a.max_size / modulus)
    let quot_max_size = (&a.max_size + modulus - 1usize) / modulus;
    // therefore quot will need ceil( ceil(a.max_size / modulus).bits() / n ) limbs
    let m = (quot_max_size.bits() as usize + n - 1) / n;
    assert!(m > 0);

    let a_val = value_to_option(a.to_bigint());
    // these are witness vectors:
    let (out_vec, quotient_vec) = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        (
            decompose_bigint_option::<F>(&Value::known(BigInt::from(out)), num_limbs, n),
            decompose_bigint_option::<F>(&Value::known(quotient), m, n),
        )
    } else {
        (vec![Value::unknown(); num_limbs], vec![Value::unknown(); m])
    };

    // this is a constant vector:
    // to decrease mod_vec.len(), we can store `modulus` with some overflow:
    // say `mod_vec` has limbs with at most `mod_overflow` bits
    // we just need `log_2(min(mod_limb_len,m)) + mod_overflow + n < overflow`
    let mut mod_overflow = ((&a.max_limb_size >> n) / m).bits() as usize;
    mod_overflow = std::cmp::max(mod_overflow, n);

    let mask = (BigUint::from(1u64) << mod_overflow) - 1usize;
    let mut mod_vec = Vec::with_capacity(num_limbs);
    let mut temp_mod = modulus.clone();
    while temp_mod != BigUint::zero() {
        let limb = &temp_mod & &mask;
        temp_mod = (temp_mod - &limb) >> n;
        mod_vec.push(biguint_to_fe(&limb));
    }

    // println!("ka: {}, m: {}, mod_len: {}", ka, m, mod_vec.len());

    // Goal: assign cells to `out - a + modulus * quotient`
    // 1. we do mul_no_carry(modulus, quotient) while assigning `modulus` and `quotient` as we go
    //    call the output `prod`
    // 2. for prod[i], i < k we can compute out - a + prod by using the transpose of
    //    | prod | -1 | a | prod - a | 1 | out | prod - a + out |
    //    where we assigned `out` as we go

    let k_prod = mod_vec.len() + m - 1;
    assert!(k_prod >= ka);
    if k_prod != ka {
        println!("carry_mod, k_prod: {}, ka: {}", k_prod, ka);
    }
    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(mod_vec.len());
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(m);
    // let mut prod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(num_limbs);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);

    for i in 0..k_prod {
        let (mod_cell, quot_cell, out_cell, check_cell) = {
            let mut offset = 0;

            let startj = if i >= m { i - m + 1 } else { 0 };
            let mut prod_computation: Vec<QuantumCell<F>> =
                Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, mod_vec.len()) - startj);
            let mut prod_val = Value::known(F::zero());
            prod_computation.push(Constant(F::zero()));
            let mut enable_gates = Vec::new();

            for j in startj..=i {
                if j >= mod_vec.len() {
                    break;
                }

                enable_gates.push(offset);

                if j < mod_assigned.len() {
                    // does it matter whether we are enabling equality from advice column or fixed column for constants?
                    prod_computation.push(Existing(&mod_assigned[j]));
                } else {
                    // Implies j == i && i < mod_vec.len()
                    prod_computation.push(Constant(mod_vec[j]));
                }

                if i - j < quot_assigned.len() {
                    prod_computation.push(Existing(&quot_assigned[i - j]));
                } else {
                    // Implies j == 0 && i < m
                    prod_computation.push(Witness(quotient_vec[i - j]));
                };

                prod_val = prod_val + Value::known(mod_vec[j]) * &quotient_vec[i - j];
                prod_computation.push(Witness(prod_val));

                offset += 3;
            }

            if i < ka {
                // perform step 2: compute prod - a + out
                // transpose of:
                // | prod | -1 | a | prod - a | 1 | out | prod - a + out
                // where prod is at relative row `offset`
                let prod_minus_a = prod_val - a.limbs[i].value();
                prod_computation.append(&mut vec![
                    Constant(-F::from(1)),
                    Existing(&a.limbs[i]),
                    Witness(prod_minus_a),
                ]);
                enable_gates.push(offset);

                if i < num_limbs {
                    let check_val = prod_minus_a + out_vec[i];
                    prod_computation.append(&mut vec![
                        Constant(F::one()),
                        Witness(out_vec[i]),
                        Witness(check_val),
                    ]);
                    enable_gates.push(offset + 3);
                }
            }

            // assign all the cells above
            let prod_computation_assignments = range.gate().assign_region_smart(
                ctx,
                prod_computation,
                enable_gates,
                vec![],
                vec![],
            )?;

            let mut mod_cell = None;
            let mut quot_cell = None;
            // get new assigned cells and store them
            if i < mod_vec.len() {
                // offset at j = i
                mod_cell = Some(prod_computation_assignments[3 * (i - startj) + 1].clone());
            }
            if i < m {
                // offset at j = 0
                quot_cell = Some(prod_computation_assignments[2].clone());
            }

            let mut out_cell = None;
            if i < num_limbs {
                out_cell = Some(
                    prod_computation_assignments[prod_computation_assignments.len() - 2].clone(),
                );
            }
            let check_cell = Some(prod_computation_assignments.last().unwrap().clone());
            (mod_cell, quot_cell, out_cell, check_cell)
        };
        if let Some(mc) = mod_cell {
            mod_assigned.push(mc);
        }
        if let Some(qc) = quot_cell {
            quot_assigned.push(qc);
        }
        if let Some(oc) = out_cell {
            out_assigned.push(oc);
        }
        if let Some(cc) = check_cell {
            check_assigned.push(cc);
        }
    }
    assert_eq!(mod_assigned.len(), mod_vec.len());
    assert_eq!(quot_assigned.len(), m);
    let out_max_limb_size = (BigUint::one() << n) - 1usize;
    // range check limbs of `out` are in [0, 2^n)
    for out_cell in out_assigned.iter() {
        range.range_check(ctx, out_cell, n)?;
    }

    let limb_base: F = biguint_to_fe(&(BigUint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n)
    for quot_cell in quot_assigned.iter() {
        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = {
            let out_val = quot_cell.value().map(|&a| a + limb_base);
            // | quot_cell | 2^n | 1 | quot_cell + 2^n |
            let shift_computation = range.gate().assign_region_smart(
                ctx,
                vec![
                    Existing(quot_cell),
                    Constant(limb_base),
                    Constant(F::one()),
                    Witness(out_val),
                ],
                vec![0],
                vec![],
                vec![],
            )?;
            shift_computation[3].clone()
        };

        range.range_check(ctx, &quot_shift, n + 1)?;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &out_max_limb_size
            + &a.max_limb_size
            + (BigUint::from(std::cmp::min(mod_vec.len(), m)) << (mod_overflow + n)),
        n,
        BigUint::zero(),
    );
    // check that `out - a + modulus * quotient == 0` after carry
    check_carry_to_zero::assign(range, ctx, check_overflow_int)?;
    Ok(OverflowInteger::construct(out_assigned, out_max_limb_size, n, modulus - 1usize))
}

pub fn get_carry_witness(a: &BigInt, modulus: &BigUint) -> (BigUint, BigInt) {
    if a < &BigInt::zero() {
        let a_neg = BigInt::to_biguint(&-a).unwrap();
        let quotient = (&a_neg + modulus - 1u32) / modulus;
        let out = modulus * &quotient - a_neg;
        (out, BigInt::from_biguint(Sign::Minus, quotient))
    } else {
        let a = BigInt::to_biguint(a).unwrap();
        let quotient = &a / modulus;
        (a - modulus * &quotient, quotient.into())
    }
}

#[cfg(test)]
#[test]
fn test_carry_witness() {
    let a = BigInt::from(-17);
    let modulus = BigUint::from(15u32);
    let (out, q) = get_carry_witness(&a, &modulus);
    assert_eq!(a, BigInt::from(out) + BigInt::from(modulus) * q);
}

// Input `a` is `CRTInteger` with `a.truncation` of length `k` with "signed" limbs
// Output is `out = a (mod modulus)` as CRTInteger with
// `out.value = a.value (mod modulus)`
// `out.trunction = (a (mod modulus)) % 2^t` a proper BigInt of length `k` with limbs in [0, 2^limb_bits)`
// The witness for `out.truncation` is a BigInt in [0, modulus), but we do not constrain the inequality
// `out.native = (a (mod modulus)) % (native_modulus::<F>)`
// We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
pub fn crt<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    chip: &BigIntConfig<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    modulus: &BigUint,
) -> Result<CRTInteger<F>, Error> {
    let n = a.truncation.limb_bits;
    let k = a.truncation.limbs.len();
    let trunc_len = n * k;

    #[cfg(feature = "display")]
    {
        let key = format!("carry_mod(crt) length {}", k);
        let count = ctx.op_count.entry(key).or_insert(0);
        *count += 1;
    }

    // in order for CRT method to work, we need `abs(out + modulus * quotient - a) < 2^{trunc_len - 1} * native_modulus::<F>`
    // this is ensured if `0 <= out < 2^{n*k}` and
    // `modulus * quotient` < 2^{trunc_len - 1} * native_modulus::<F> - a.max_size
    let quot_max_bits = ((BigUint::one().shl(trunc_len - 1) * native_modulus::<F>()
        - &a.truncation.max_size)
        / modulus)
        .bits() as usize;
    assert!(quot_max_bits < trunc_len);
    // Let n' <= quot_max_bits - n(k-1) - 1
    // If quot[i] <= 2^n for i < k - 1 and quot[k-1] <= 2^{n'} then
    // quot < 2^{n(k-1)+1} + 2^{n' + n(k-1)} = (2+2^{n'}) 2^{n(k-1)} < 2^{n'+1} * 2^{n(k-1)} <= 2^{quot_max_bits - n(k-1)} * 2^{n(k-1)}
    let quot_last_limb_bits = quot_max_bits - n * (k - 1) - 1;

    let out_max_bits = modulus.bits() as usize;
    assert!(out_max_bits > n * (k - 1));
    let out_last_limb_bits = out_max_bits - n * (k - 1);

    // these are witness vectors:
    // we need to find `out_vec` as a proper BigInt with k limbs
    // we need to find `quot_vec` as a proper BigInt with k limbs

    // we need to constrain that `sum_i out_vec[i] * 2^{n*i} = out_native` in `F`
    // we need to constrain that `sum_i quot_vec[i] * 2^{n*i} = quot_native` in `F`
    let (out_val, out_vec, quot_vec) = if let Some(a_big) = value_to_option(a.value.clone()) {
        let (out_val, quot_val) = get_carry_witness(&a_big, modulus);
        let out_val = BigInt::from(out_val);

        assert!(out_val < (BigInt::one() << (n * k)));
        assert!(quot_val < (BigInt::one() << quot_max_bits));

        (
            Value::known(out_val.clone()),
            // decompose_bigint_option just throws away signed limbs in index >= k
            decompose_bigint_option::<F>(&Value::known(out_val), k, n),
            decompose_bigint_option::<F>(&Value::known(quot_val), k, n),
        )
    } else {
        (Value::unknown(), vec![Value::unknown(); k], vec![Value::unknown(); k])
    };

    // let out_native = out_val.as_ref().map(|a| bigint_to_fe::<F>(a));
    // let quot_native = quot_val.map(|a| bigint_to_fe::<F>(&a));

    assert!(modulus < &(BigUint::one() << (n * k)));
    let mod_vec = decompose_biguint(modulus, k, n);
    let mod_native: F = biguint_to_fe(modulus);
    // We need to show `out - a + modulus * quotient` is:
    // - congruent to `0 (mod 2^trunc_len)`
    // - equal to 0 in native field `F`

    // Modulo 2^trunc_len, using OverflowInteger:
    // ------------------------------------------
    // Goal: assign cells to `out - a + modulus * quotient`
    // 1. we effectively do mul_no_carry::truncate(mod_vec, quot_vec) while assigning `mod_vec` and `quot_vec` as we go
    //    call the output `prod` which has len k
    // 2. for prod[i] we can compute `prod + out - a`
    //    where we assign `out_vec` as we go

    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);

    match chip.strategy {
        // strategies where we carry out school-book multiplication in some form:
        BigIntStrategy::Simple => {
            for i in 0..k {
                let (quot_cell, out_cell, check_cell) = {
                    let (quot_assigned, _, prod, gate_index) = range.gate().inner_product(
                        ctx,
                        &quot_assigned[0..i]
                            .iter()
                            .map(|a| Existing(&a))
                            .chain([Witness(quot_vec[i])])
                            .collect(),
                        &mod_vec[0..=i].iter().rev().map(|c| Constant(*c)).collect(),
                    )?;

                    let out_cell;
                    let check_cell;
                    // perform step 2: compute prod - a + out
                    let temp1 = prod.value().copied() - a.truncation.limbs[i].value();
                    let check_val = temp1 + out_vec[i];

                    match range.strategy() {
                        RangeStrategy::Vertical => {
                            // transpose of:
                            // | prod | -1 | a | prod - a | 1 | out | prod - a + out
                            // where prod is at relative row `offset`
                            let (assignments, _) = range.gate().assign_region(
                                ctx,
                                vec![
                                    Constant(-F::from(1)),
                                    Existing(&a.truncation.limbs[i]),
                                    Witness(temp1),
                                    Constant(F::one()),
                                    Witness(out_vec[i]),
                                    Witness(check_val),
                                ],
                                vec![(-1, None), (2, None)],
                                Some(gate_index),
                            )?;
                            out_cell = assignments[4].clone();
                            check_cell = assignments[5].clone();
                        }
                        RangeStrategy::PlonkPlus => {
                            // | prod | a | out | prod - a + out |
                            // selector columns:
                            // | 1    | 0 | 0   |
                            // | 0    | -1| 1   |
                            let (assignments, _) = range.gate().assign_region(
                                ctx,
                                vec![
                                    Existing(&a.truncation.limbs[i]),
                                    Witness(out_vec[i]),
                                    Witness(check_val),
                                ],
                                vec![(-1, Some([F::zero(), -F::one(), F::one()]))],
                                Some(gate_index),
                            )?;
                            out_cell = assignments[1].clone();
                            check_cell = assignments[2].clone();
                        }
                    }

                    (quot_assigned.unwrap()[i].0.clone(), out_cell, check_cell)
                };
                quot_assigned.push(quot_cell);
                out_assigned.push(out_cell);
                check_assigned.push(check_cell);
            }
        }
    }

    let out_max_limb_size = (BigUint::one() << n) - 1usize;
    // range check limbs of `out` are in [0, 2^n) except last limb should be in [0, 2^out_last_limb_bits)
    let mut out_index: usize = 0;
    for out_cell in out_assigned.iter() {
        let limb_bits = if out_index == k - 1 { out_last_limb_bits } else { n };
        range.range_check(ctx, out_cell, limb_bits)?;
        out_index = out_index + 1;
    }

    let limb_base: F = biguint_to_fe(&(BigUint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n) except for last cell check it's in [-2^quot_last_limb_bits, 2^quot_last_limb_bits)
    let mut q_index: usize = 0;
    for quot_cell in quot_assigned.iter() {
        let limb_bits = if q_index == k - 1 { quot_last_limb_bits } else { n };
        let limb_base = if q_index == k - 1 {
            biguint_to_fe(&(BigUint::one() << limb_bits))
        } else {
            limb_base
        };

        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = {
            let out_val = quot_cell.value().map(|&a| a + limb_base);
            // | quot_cell | 2^n | 1 | quot_cell + 2^n |
            let shift_computation = range.gate().assign_region_smart(
                ctx,
                vec![
                    Existing(quot_cell),
                    Constant(limb_base),
                    Constant(F::one()),
                    Witness(out_val),
                ],
                vec![0],
                vec![],
                vec![],
            )?;
            shift_computation[3].clone()
        };

        range.range_check(ctx, &quot_shift, limb_bits + 1)?;
        q_index = q_index + 1;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &out_max_limb_size + &a.truncation.max_limb_size + (BigUint::from(k) << (2 * n)),
        n,
        BigUint::zero(),
    );
    // check that `out - a + modulus * quotient == 0 mod 2^{trunc_len}` after carry
    check_carry_to_zero::truncate(range, ctx, check_overflow_int)?;

    // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
    let out_native_assigned = OverflowInteger::evaluate(range.gate(), chip, ctx, &out_assigned, n)?;
    // Constrain `quot_native = sum_i quot_assigned[i] * 2^{n*i}` in `F`
    let quot_native_assigned =
        OverflowInteger::evaluate(range.gate(), chip, ctx, &quot_assigned, n)?;

    // TODO: we can save 1 cell by connecting `out_native_assigned` computation with the following:

    // Check `out + modulus * quotient - a = 0` in native field
    // | out | modulus | quotient | a |
    let native_computation = range.gate().assign_region_smart(
        ctx,
        vec![
            Existing(&out_native_assigned),
            Constant(mod_native),
            Existing(&quot_native_assigned),
            Existing(&a.native),
        ],
        vec![0],
        vec![],
        vec![],
    )?;

    Ok(CRTInteger::construct(
        OverflowInteger::construct(out_assigned, out_max_limb_size, n, modulus - 1usize),
        out_native_assigned,
        out_val,
    ))
}
