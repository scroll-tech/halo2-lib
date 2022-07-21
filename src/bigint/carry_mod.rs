use std::ops::Shl;

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::Sign;
use num_bigint::{BigInt, BigUint};
use num_traits::ops::overflowing;
use num_traits::{One, Signed, Zero};

use super::*;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::utils::modulus as native_modulus;
use crate::{gates::*, utils::*};

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Output is `a (mod modulus)` as a proper BigInt of length `k` with limbs in [0, 2^limb_bits)`
// The witness for `out` is a BigInt in [0, modulus), but we do not constrain the inequality
// We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    modulus: &BigUint,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);

    // overflow := a.max_limb_size.bits()
    // quot <= ceil(2^overflow * 2^{n * k} / modulus) < 2^{overflow + n * k - modulus.bits() + 1}
    // there quot will need ceil( (overflow + n * k - modulus.bits() + 1 ) / n ) limbs
    let overflow = a.max_limb_size.bits() as usize;
    let m = (overflow + n * k - modulus.bits() as usize + n) / n;
    assert!(m > 0);

    let a_val = a.to_bigint();
    // these are witness vectors:
    let (out_vec, quotient_vec) = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        (
            decompose_bigint_option::<F>(&Some(BigInt::from(out)), k, n),
            decompose_bigint_option::<F>(&Some(quotient), m, n),
        )
    } else {
        (vec![None; k], vec![None; m])
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

    //println!("a_limbs: {:?}", a.limbs);
    //println!("out_vec: {:?}", out_vec);
    //println!("quot_vec: {:?}", quotient_vec);
    //println!("mod_vec: {:?}", mod_vec);

    // Goal: assign cells to `out - a + modulus * quotient`
    // 1. we do mul_no_carry(modulus, quotient) while assigning `modulus` and `quotient` as we go
    //    call the output `prod`
    // 2. for prod[i], i < k we can compute out - a + prod by using the transpose of
    //    | prod | -1 | a | prod - a | 1 | out | prod - a + out |
    //    where we assigned `out` as we go

    let k_prod = mod_vec.len() + m - 1;
    assert!(k_prod >= k);
    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(mod_vec.len());
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(m);
    // let mut prod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);

    let gate = &range.qap_config;
    for i in 0..k_prod {
        layouter.assign_region(
            || format!("carry_mod_{}", i),
            |mut region| {
                let mut offset = 0;

                let startj = if i >= m { i - m + 1 } else { 0 };
                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, mod_vec.len()) - startj);
                let mut prod_val = Some(F::zero());
                prod_computation.push(Constant(F::zero()));

                for j in startj..=i {
                    if j >= mod_vec.len() {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

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

                    prod_val = prod_val
                        .zip(quotient_vec[i - j])
                        .map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }
                // assign all the cells above
                let prod_computation_assignments =
                    gate.assign_region(prod_computation, 0, &mut region)?;

                // get new assigned cells and store them
                if i < mod_vec.len() {
                    // offset at j = i
                    mod_assigned.push(prod_computation_assignments[3 * (i - startj) + 1].clone());
                }
                if i < m {
                    // offset at j = 0
                    quot_assigned.push(prod_computation_assignments[2].clone());
                }

                if i < k {
                    // perform step 2: compute prod - a + out
                    // transpose of:
                    // | prod | -1 | a | prod - a | 1 | out | prod - a + out
                    // where prod is at relative row `offset`
                    gate.q_enable.enable(&mut region, offset)?;
                    gate.q_enable.enable(&mut region, offset + 3)?;

                    let temp1 = prod_val.zip(a.limbs[i].value()).map(|(prod, &a)| prod - a);
                    let check_val = temp1.zip(out_vec[i]).map(|(a, b)| a + b);

                    let acells = gate.assign_region(
                        vec![
                            Constant(-F::from(1)),
                            Existing(&a.limbs[i]),
                            Witness(temp1),
                            Constant(F::one()),
                            Witness(out_vec[i]),
                            Witness(check_val),
                        ],
                        offset + 1,
                        &mut region,
                    )?;

                    out_assigned.push(acells[4].clone());
                    check_assigned.push(acells[5].clone());
                } else {
                    check_assigned.push(prod_computation_assignments.last().unwrap().clone());
                }

                Ok(())
            },
        )?;
    }
    assert_eq!(mod_assigned.len(), mod_vec.len());
    assert_eq!(quot_assigned.len(), m);

    let out_max_limb_size = (BigUint::one() << n) - 1usize;
    // range check limbs of `out` are in [0, 2^n)
    for out_cell in out_assigned.iter() {
        range.range_check(layouter, out_cell, n)?;
    }

    let limb_base: F = biguint_to_fe(&(BigUint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n)
    for quot_cell in quot_assigned.iter() {
        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", n),
            |mut region| {
                gate.q_enable.enable(&mut region, 0)?;

                let out_val = quot_cell.value().map(|&a| a + limb_base);
                // | quot_cell | 2^n | 1 | quot_cell + 2^n |
                let shift_computation = gate.assign_region(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
                    0,
                    &mut region,
                )?;
                Ok(shift_computation[3].clone())
            },
        )?;

        range.range_check(layouter, &quot_shift, n + 1)?;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &out_max_limb_size
            + &a.max_limb_size
            + (BigUint::from(std::cmp::min(mod_vec.len(), m)) << (mod_overflow + n)),
        n,
    );
    // check that `out - a + modulus * quotient == 0` after carry
    check_carry_to_zero::assign(range, layouter, check_overflow_int)?;

    Ok(OverflowInteger::construct(
        out_assigned,
        out_max_limb_size,
        n,
    ))
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
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    modulus: &BigUint,
) -> Result<CRTInteger<F>, Error> {
    let n = a.truncation.limb_bits;
    let k = a.truncation.limbs.len();
    let trunc_len = n * k;

    // in order for CRT method to work, we need `abs(out + modulus * quotient - a) < 2^{trunc_len - 1} * native_modulus::<F>`
    // this is ensured if `0 <= out < 2^{n*k}` and
    // `modulus * quotient` < 2^{trunc_len - 1} * native_modulus::<F> - a.max_size
    let quot_max_bits = ((BigUint::one().shl(trunc_len - 1) * native_modulus::<F>() - &a.max_size)
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
    // we need to find `out_native` as a native F element
    // we need to find `quot_native` as a native F element

    // we need to constrain that `sum_i out_vec[i] * 2^{n*i} = out_native` in `F`
    // we need to constrain that `sum_i quot_vec[i] * 2^{n*i} = quot_native` in `F`
    let (out_val, quot_val, out_vec, quot_vec) = if let Some(a_big) = &a.value {
        let (out_val, quot_val) = get_carry_witness(a_big, modulus);
        let out_val = BigInt::from(out_val);

        assert!(out_val < (BigInt::one() << (n * k)));
        assert!(quot_val < (BigInt::one() << quot_max_bits));

        (
            Some(out_val.clone()),
            Some(quot_val.clone()),
            // decompose_bigint_option just throws away signed limbs in index >= k
            decompose_bigint_option::<F>(&Some(out_val), k, n),
            decompose_bigint_option::<F>(&Some(quot_val), k, n),
        )
    } else {
        (None, None, vec![None; k], vec![None; k])
    };

    let out_native = out_val.as_ref().map(|a| bigint_to_fe(a));
    let quot_native = quot_val.map(|a| bigint_to_fe(&a));

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
    // 2. for prod[i] we can compute out - a + prod by using the transpose of
    //    | prod | -1 | a | prod - a | 1 | out | prod - a + out |
    //    where we assign `out_vec` as we go

    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);

    for i in 0..k {
        let (mod_cell, quot_cell, out_cell, check_cell) = layouter.assign_region(
            || format!("carry_mod_{}", i),
            |mut region| {
                let mut offset = 0;

                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, k));
                let mut prod_val = Some(F::zero());
                prod_computation.push(Constant(F::zero()));

                for j in 0..std::cmp::min(i + 1, k) {
                    range.qap_config.q_enable.enable(&mut region, offset)?;

                    if j != i {
                        // does it matter whether we are enabling equality from advice column or fixed column for constants?
                        prod_computation.push(Existing(&mod_assigned[j]));
                    } else {
                        prod_computation.push(Constant(mod_vec[j]));
                    }

                    if j != 0 {
                        prod_computation.push(Existing(&quot_assigned[i - j]));
                    } else {
                        prod_computation.push(Witness(quot_vec[i - j]));
                    };

                    prod_val = prod_val
                        .zip(quot_vec[i - j])
                        .map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }
                // assign all the cells above
                let prod_computation_assignments =
                    range
                        .qap_config
                        .assign_region(prod_computation, 0, &mut region)?;

                // perform step 2: compute prod - a + out
                // transpose of:
                // | prod | -1 | a | prod - a | 1 | out | prod - a + out
                // where prod is at relative row `offset`
                range.qap_config.q_enable.enable(&mut region, offset)?;
                range.qap_config.q_enable.enable(&mut region, offset + 3)?;

                let temp1 = prod_val
                    .zip(a.truncation.limbs[i].value())
                    .map(|(prod, &a)| prod - a);
                let check_val = temp1.zip(out_vec[i]).map(|(a, b)| a + b);

                let acells = range.qap_config.assign_region(
                    vec![
                        Constant(-F::from(1)),
                        Existing(&a.truncation.limbs[i]),
                        Witness(temp1),
                        Constant(F::one()),
                        Witness(out_vec[i]),
                        Witness(check_val),
                    ],
                    offset + 1,
                    &mut region,
                )?;

                Ok((
                    // new mod_assigned cells is at
                    // offset at j = i
                    prod_computation_assignments[3 * i + 1].clone(),
                    // new quot_assigned is at
                    // offset at j = 0
                    prod_computation_assignments[2].clone(),
                    // out_assigned
                    acells[4].clone(),
                    // check_assigned
                    acells[5].clone(),
                ))
            },
        )?;
        mod_assigned.push(mod_cell);
        quot_assigned.push(quot_cell);
        out_assigned.push(out_cell);
        check_assigned.push(check_cell);
    }

    let out_max_limb_size = (BigUint::one() << n) - 1usize;
    // range check limbs of `out` are in [0, 2^n) except last limb should be in [0, 2^out_last_limb_bits)
    let mut out_index: usize = 0;
    for out_cell in out_assigned.iter() {
        let limb_bits = if out_index == k - 1 {
            out_last_limb_bits
        } else {
            n
        };
        range.range_check(layouter, out_cell, limb_bits)?;
        out_index = out_index + 1;
    }

    let limb_base: F = biguint_to_fe(&(BigUint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n) except for last cell check it's in [-2^quot_last_limb_bits, 2^quot_last_limb_bits)
    let mut q_index: usize = 0;
    for quot_cell in quot_assigned.iter() {
        let limb_bits = if q_index == k - 1 {
            quot_last_limb_bits
        } else {
            n
        };
        let limb_base = if q_index == k - 1 {
            biguint_to_fe(&(BigUint::one() << limb_bits))
        } else {
            limb_base
        };

        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", limb_bits),
            |mut region| {
                range.qap_config.q_enable.enable(&mut region, 0)?;

                let out_val = quot_cell.value().map(|&a| a + limb_base);
                // | quot_cell | 2^n | 1 | quot_cell + 2^n |
                let shift_computation = range.qap_config.assign_region(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
                    0,
                    &mut region,
                )?;
                Ok(shift_computation[3].clone())
            },
        )?;

        range.range_check(layouter, &quot_shift, limb_bits + 1)?;
        q_index = q_index + 1;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &out_max_limb_size + &a.truncation.max_limb_size + (BigUint::from(k) << (2 * n)),
        n,
    );
    // check that `out - a + modulus * quotient == 0 mod 2^{trunc_len}` after carry
    check_carry_to_zero::truncate(range, layouter, check_overflow_int)?;

    // Check `out + modulus * quotient - a = 0` in native field
    // ----------------------------------------------------
    let (out_native_assigned, quot_native_assigned) = layouter.assign_region(
        || "native carry mod",
        |mut region| {
            // | out | modulus | quotient | a |
            let native_computation = range.qap_config.assign_region(
                vec![
                    Witness(out_native),
                    Constant(mod_native),
                    Witness(quot_native),
                    Existing(&a.native),
                ],
                0,
                &mut region,
            )?;
            range.qap_config.q_enable.enable(&mut region, 0)?;
            Ok((native_computation[0].clone(), native_computation[2].clone()))
        },
    )?;

    // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
    let out_native_consistency =
        OverflowInteger::evaluate(&range.qap_config, layouter, &out_assigned, n)?;
    // Constrain `quot_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
    let quot_native_consistency =
        OverflowInteger::evaluate(&range.qap_config, layouter, &quot_assigned, n)?;
    layouter.assign_region(
        || "native consistency equals",
        |mut region| {
            region.constrain_equal(out_native_consistency.cell(), out_native_assigned.cell())?;
            region.constrain_equal(quot_native_consistency.cell(), quot_native_assigned.cell())?;
            Ok(())
        },
    )?;

    Ok(CRTInteger::construct(
        OverflowInteger::construct(out_assigned, out_max_limb_size, n),
        out_native_assigned,
        out_val,
        BigUint::one().shl(out_max_bits) - 1usize,
    ))
}
