use super::BigIntConfig;
use super::{check_carry_to_zero, CRTInteger, OverflowInteger};
use crate::bigint::{carry_mod::get_carry_witness, BigIntStrategy};
use halo2_base::{
    gates::{GateInstructions, RangeInstructions},
    utils::{
        biguint_to_fe, decompose_bigint_option, decompose_biguint, modulus as native_modulus,
        value_to_option,
    },
    AssignedValue, Context,
    QuantumCell::{self, Constant, Existing, Witness},
};
use halo2_proofs::{arithmetic::FieldExt, circuit::Value, plonk::Error};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::ops::Shl;

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Check that `a = 0 (mod modulus)`
// We constrain `a = modulus * quotient` and range check `quotient`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    modulus: &BigUint,
) -> Result<(), Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);

    // quot <= ceil(a.max_size / modulus)
    let quot_max_size = (&a.max_size + modulus - 1usize) / modulus;
    // therefore quot will need ceil( ceil(a.max_size / modulus).bits() / n ) limbs
    let m = (quot_max_size.bits() as usize + n - 1) / n;
    assert!(m > 0);

    let a_val = value_to_option(a.to_bigint());
    // these are witness vectors:
    let quotient_vec = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        assert_eq!(out, BigUint::zero());
        decompose_bigint_option::<F>(&Value::known(quotient), m, n)
    } else {
        vec![Value::unknown(); k]
    };

    // this is a constant vector:
    // to decrease mod_vec.len(), we can store `modulus` with some overflow:
    // say `mod_vec` has limbs with at most `mod_overflow` bits
    // we just need `log_2(min(mod_limb_len,m)) + mod_overflow + n < overflow`
    let mut mod_overflow = ((&a.max_limb_size >> n) / m).bits() as usize;
    mod_overflow = std::cmp::max(mod_overflow, n);

    let mask = (BigUint::from(1u64) << mod_overflow) - 1usize;
    let mut mod_vec = Vec::with_capacity(k);
    let mut temp_mod = modulus.clone();
    while temp_mod != BigUint::zero() {
        let limb = &temp_mod & &mask;
        temp_mod = (temp_mod - &limb) >> n;
        mod_vec.push(biguint_to_fe(&limb));
    }

    // Goal: assign cells to `- a + modulus * quotient`
    // 1. we do mul_no_carry(modulus, quotient) while assigning `modulus` and `quotient` as we go
    //    call the output `prod`
    // 2. for prod[i], i < k we can compute out - a + prod by using the transpose of
    //    | prod | -1 | a | prod - a |

    let k_prod = mod_vec.len() + m - 1;
    assert!(k_prod >= k);
    if k_prod != k {
        println!("check_carry_mod_to_zero, k_prod: {}, k: {}", k_prod, k);
    }
    let mut mod_assigned: Vec<AssignedValue<F>> = Vec::with_capacity(mod_vec.len());
    let mut quot_assigned: Vec<AssignedValue<F>> = Vec::with_capacity(m);
    let mut check_assigned: Vec<AssignedValue<F>> = Vec::with_capacity(k_prod);

    for i in 0..k_prod {
        let (mod_cell, quot_cell, check_cell) = {
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

            if i < k {
                // perform step 2: compute prod - a
                // transpose of:
                // | prod | -1 | a | prod - a
                // where prod is at relative row `offset`
                let check_val = prod_val - a.limbs[i].value();
                prod_computation.append(&mut vec![
                    Constant(-F::from(1)),
                    Existing(&a.limbs[i]),
                    Witness(check_val),
                ]);
                enable_gates.push(offset);
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

            let check_cell = Some(prod_computation_assignments.last().unwrap().clone());

            (mod_cell, quot_cell, check_cell)
        };
        if let Some(mc) = mod_cell {
            mod_assigned.push(mc);
        }
        if let Some(qc) = quot_cell {
            quot_assigned.push(qc);
        }
        if let Some(cc) = check_cell {
            check_assigned.push(cc);
        }
    }
    assert_eq!(mod_assigned.len(), mod_vec.len());
    assert_eq!(quot_assigned.len(), m);

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
        &a.max_limb_size + (BigUint::from(std::cmp::min(mod_vec.len(), m)) << (mod_overflow + n)),
        n,
        BigUint::zero(),
    );
    // check that `- a + modulus * quotient == 0` after carry
    check_carry_to_zero::assign(range, ctx, check_overflow_int)?;

    Ok(())
}

// same as carry_mod::crt but `out = 0` so no need to range check
pub fn crt<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    chip: &BigIntConfig<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    modulus: &BigUint,
) -> Result<(), Error> {
    let n = a.truncation.limb_bits;
    let k = a.truncation.limbs.len();
    let trunc_len = n * k;

    #[cfg(feature = "display")]
    {
        let key = format!("check_carry_mod(crt) length {}", k);
        let count = ctx.op_count.entry(key).or_insert(0);
        *count += 1;
    }

    // in order for CRT method to work, we need `abs(modulus * quotient - a) < 2^{trunc_len - 1} * native_modulus::<F>`
    // this is ensured if
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

    // these are witness vectors:
    // we need to find `quot_vec` as a proper BigInt with k limbs
    // we need to find `quot_native` as a native F element

    // we need to constrain that `sum_i quot_vec[i] * 2^{n*i} = quot_native` in `F`
    let quot_vec = if let Some(a_big) = value_to_option(a.value.clone()) {
        let (out_val, quot_val) = get_carry_witness(&a_big, modulus);
        assert_eq!(out_val, BigUint::zero());

        assert!((quot_val.bits() as usize) < quot_max_bits);
        // decompose_bigint_option just throws away signed limbs in index >= k
        decompose_bigint_option::<F>(&Value::known(quot_val), k, n)
    } else {
        vec![Value::unknown(); k]
    };

    assert!(modulus < &(BigUint::one() << (n * k)));
    let mod_vec = decompose_biguint(modulus, k, n);
    let mod_native: F = biguint_to_fe(modulus);

    // We need to show `modulus * quotient - a` is:
    // - congruent to `0 (mod 2^trunc_len)`
    // - equal to 0 in native field `F`

    // Modulo 2^trunc_len, using OverflowInteger:
    // ------------------------------------------
    // Goal: assign cells to `modulus * quotient - a`
    // 1. we effectively do mul_no_carry::truncate(mod_vec, quot_vec) while assigning `mod_vec` and `quot_vec` as we go
    //    call the output `prod` which has len k
    // 2. for prod[i] we can compute prod - a by using the transpose of
    //    | prod | -1 | a | prod - a |

    let mut quot_assigned: Vec<AssignedValue<F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedValue<F>> = Vec::with_capacity(k);

    match chip.strategy {
        BigIntStrategy::Simple => {
            for i in 0..k {
                let (quot_cell, check_cell) = {
                    let (quot_assigned, _, prod) = range.gate().inner_product(
                        ctx,
                        &quot_assigned[0..i]
                            .iter()
                            .map(|a| Existing(&a))
                            .chain([Witness(quot_vec[i])])
                            .collect(),
                        &mod_vec[0..=i].iter().rev().map(|c| Constant(*c)).collect(),
                    )?;
                    let gate_index = prod.column();

                    // perform step 2: compute prod - a + out
                    // transpose of:
                    // | prod | -1 | a | prod - a |
                    let check_val = prod.value().copied() - a.truncation.limbs[i].value();
                    let assignments = range.gate().assign_region(
                        ctx,
                        vec![
                            Constant(-F::from(1)),
                            Existing(&a.truncation.limbs[i]),
                            Witness(check_val),
                        ],
                        vec![(-1, None)],
                        Some(gate_index),
                    )?;

                    (quot_assigned.unwrap()[i].clone(), assignments[2].clone())
                };
                quot_assigned.push(quot_cell);
                check_assigned.push(check_cell);
            }
        }
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
        &a.truncation.max_limb_size + (BigUint::from(k) << (2 * n)),
        n,
        BigUint::zero(),
    );
    // check that `modulus * quotient - a == 0 mod 2^{trunc_len}` after carry
    check_carry_to_zero::truncate(range, ctx, check_overflow_int)?;

    // Constrain `quot_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
    let quot_native_assigned =
        OverflowInteger::evaluate(range.gate(), chip, ctx, &quot_assigned, n)?;

    // Check `0 + modulus * quotient - a = 0` in native field
    // | 0 | modulus | quotient | a |
    let _native_computation = range.gate().assign_region_smart(
        ctx,
        vec![
            Constant(F::from(0)),
            Constant(mod_native),
            Existing(&quot_native_assigned),
            Existing(&a.native),
        ],
        vec![0],
        vec![],
        vec![],
    )?;

    Ok(())
}
