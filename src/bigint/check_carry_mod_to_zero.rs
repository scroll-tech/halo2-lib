use std::ops::Shl;

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_bigint::Sign;
use num_traits::{One, Zero};

use super::{check_carry_to_zero, CRTInteger, OverflowInteger};
use crate::bigint::carry_mod::get_carry_witness;
use crate::gates::{
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::bigint_to_fe;
use crate::utils::biguint_to_fe;
use crate::utils::decompose_bigint_option;
use crate::utils::decompose_biguint;
use crate::utils::modulus as native_modulus;

// same as carry_mod::crt but `out = 0` so no need to range check
pub fn crt<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    modulus: &BigUint,
) -> Result<(), Error> {
    let n = a.truncation.limb_bits;
    let k = a.truncation.limbs.len();
    let trunc_len = n * k;

    // in order for CRT method to work, we need `abs(modulus * quotient - a) < 2^{trunc_len - 1} * native_modulus::<F>`
    // this is ensured if
    // `modulus * quotient` < 2^{trunc_len - 1} * native_modulus::<F> - a.max_size
    let quot_max_bits = ((BigUint::one().shl(trunc_len - 1) * native_modulus::<F>() - &a.max_size)
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
    let (quot_val, quot_vec) = if let Some(a_big) = &a.value {
        let (out_val, quot_val) = get_carry_witness(a_big, modulus);
        assert_eq!(out_val, BigUint::zero());

        assert!((quot_val.bits() as usize) < quot_max_bits);
        (
            Some(quot_val.clone()),
            // decompose_bigint_option just throws away signed limbs in index >= k
            decompose_bigint_option::<F>(&Some(quot_val), k, n),
        )
    } else {
        (None, vec![None; k])
    };

    let quot_native = quot_val.map(|a| bigint_to_fe(&a));

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

    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);

    for i in 0..k {
        let (mod_cell, quot_cell, check_cell) = layouter.assign_region(
            || format!("carry_mod_{}", i),
            |mut region| {
                let mut offset = 0;

                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(4 + 3 * std::cmp::min(i + 1, k));
                let mut prod_val = Some(F::zero());
                prod_computation.push(Constant(F::zero()));
                let mut enable_gates = Vec::new();

                for j in 0..std::cmp::min(i + 1, k) {
                    enable_gates.push(offset);

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

                    prod_val = prod_val.zip(quot_vec[i - j]).map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }

                // perform step 2: compute prod - a + out
                // transpose of:
                // | prod | -1 | a | prod - a |
                // where prod is at relative row `offset`
                enable_gates.push(offset);

                let check_val =
                    prod_val.zip(a.truncation.limbs[i].value()).map(|(prod, &a)| prod - a);

                prod_computation.append(&mut vec![
                    Constant(-F::from(1)),
                    Existing(&a.truncation.limbs[i]),
                    Witness(check_val),
                ]);
                // assign all the cells above
                let (prod_computation_assignments, column_index) =
                    range.gate().assign_region(prod_computation, 0, &mut region)?;
                for row in enable_gates {
                    range.gate().enable(&mut region, column_index, row)?;
                }

                Ok((
                    // new mod_assigned at
                    // offset at j = i
                    prod_computation_assignments[3 * i + 1].clone(),
                    // new quot_assigned at
                    // offset at j = 0
                    prod_computation_assignments[2].clone(),
                    // new check_assigned
                    prod_computation_assignments[offset + 3].clone(),
                ))
            },
        )?;
        mod_assigned.push(mod_cell);
        quot_assigned.push(quot_cell);
        check_assigned.push(check_cell);
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
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", limb_bits),
            |mut region| {
                let out_val = quot_cell.value().map(|&a| a + limb_base);
                // | quot_cell | 2^n | 1 | quot_cell + 2^n |
                let (shift_computation, column_index) = range.gate().assign_region(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
                    0,
                    &mut region,
                )?;
                range.gate().enable(&mut region, column_index, 0)?;
                Ok(shift_computation[3].clone())
            },
        )?;

        range.range_check(layouter, &quot_shift, limb_bits + 1)?;
        q_index = q_index + 1;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &a.truncation.max_limb_size + (BigUint::from(k) << (2 * n)),
        n,
    );
    // check that `modulus * quotient - a == 0 mod 2^{trunc_len}` after carry
    check_carry_to_zero::truncate(range, layouter, check_overflow_int)?;

    // Check `0 + modulus * quotient - a = 0` in native field
    // ----------------------------------------------------
    let quot_native_assigned = layouter.assign_region(
        || "native carry mod",
        |mut region| {
            // | 0 | modulus | quotient | a |
            let (native_computation, column_index) = range.gate().assign_region(
                vec![
                    Constant(F::from(0)),
                    Constant(mod_native),
                    Witness(quot_native),
                    Existing(&a.native),
                ],
                0,
                &mut region,
            )?;
            range.gate().enable(&mut region, column_index, 0)?;
            Ok(native_computation[2].clone())
        },
    )?;

    let mut pows = Vec::with_capacity(k);
    let mut running_pow = F::from(1);
    for i in 0..k {
        pows.push(Constant(running_pow));
        running_pow = running_pow * &limb_base;
    }
    // Constrain `quot_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
    let quot_native_consistency =
        OverflowInteger::evaluate(range.gate(), layouter, &quot_assigned, n)?;
    layouter.assign_region(
        || "native consistency equals",
        |mut region| {
            region.constrain_equal(quot_native_consistency.cell(), quot_native_assigned.cell())?;
            Ok(())
        },
    )?;

    Ok(())
}
