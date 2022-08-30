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

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Check that `a = 0 (mod modulus)`
// We constrain `a = modulus * quotient` and range check `quotient`
pub fn assign<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    modulus: &BigUint,
) -> Result<(), Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);

    // overflow := a.max_limb_size.bits()
    // quot <= ceil(2^overflow * 2^{n * k} / modulus) < 2^{overflow + n * k - modulus.bits() + 1}
    // therefore quot will need ceil( (overflow + n * k - modulus.bits() + 1 ) / n ) limbs
    let overflow = a.max_limb_size.bits() as usize;
    let m = (overflow + n * k - modulus.bits() as usize + n) / n;
    assert!(m > 0);

    let a_val = a.to_bigint();
    // these are witness vectors:
    let quotient_vec = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        assert_eq!(out, BigUint::zero());
        decompose_bigint_option::<F>(&Some(quotient), m, n)
    } else {
        vec![None; k]
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
    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(mod_vec.len());
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(m);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);

    for i in 0..k_prod {
        let (mod_cell, quot_cell, check_cell) = layouter.assign_region(
            || format!("check_carry_mod_to_zero_assign_{}", i),
            |mut region| {
                let mut offset = 0;

                let startj = if i >= m { i - m + 1 } else { 0 };
                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, mod_vec.len()) - startj);
                let mut prod_val = Some(F::zero());
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

                    prod_val = prod_val
                        .zip(quotient_vec[i - j])
                        .map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }

		if i < k {
		    // perform step 2: compute prod - a
                    // transpose of:
                    // | prod | -1 | a | prod - a
                    // where prod is at relative row `offset`
		    let check_val = prod_val.zip(a.limbs[i].value()).map(|(prod, &a)| prod - a);
		    prod_computation.append(&mut vec![
			Constant(-F::from(1)),
                        Existing(&a.limbs[i]),
                        Witness(check_val),
		    ]);
		    enable_gates.push(offset);
		}

                // assign all the cells above
                let (prod_computation_assignments, column_idx) =
                    range.gate().assign_region_smart(prod_computation, enable_gates, vec![], vec![], 0, &mut region)?;

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
		
                Ok((
		    mod_cell,
		    quot_cell,
		    check_cell,
		))
            },
        )?;
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
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", n),
            |mut region| {
                let out_val = quot_cell.value().map(|&a| a + limb_base);
                // | quot_cell | 2^n | 1 | quot_cell + 2^n |
                let (shift_computation, idx) = range.gate().assign_region_smart(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
		    vec![0],
		    vec![],
		    vec![],
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
        &a.max_limb_size + (BigUint::from(std::cmp::min(mod_vec.len(), m)) << (mod_overflow + n)),
        n,
    );
    // check that `- a + modulus * quotient == 0` after carry
    check_carry_to_zero::assign(range, layouter, check_overflow_int)?;

    Ok(())
}

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
            || format!("check_carry_mod_to_zero_crt_{}", i),
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
                    range.gate().assign_region_smart(prod_computation, enable_gates, vec![], vec![], 0, &mut region)?;

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
                let (shift_computation, column_index) = range.gate().assign_region_smart(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
		    vec![0],
		    vec![],
		    vec![],
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
            let (native_computation, column_index) = range.gate().assign_region_smart(
                vec![
                    Constant(F::from(0)),
                    Constant(mod_native),
                    Witness(quot_native),
                    Existing(&a.native),
                ],
		vec![0],
		vec![],
		vec![],
                0,
                &mut region,
            )?;
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
