use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::ToPrimitive;
use num_traits::{One, Zero};

use super::*;
use crate::{gates::*, utils::*};

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Output is `a (mod modulus)` as a proper BigInt of length `k` with limbs in [0, 2^limb_bits)`
// The witness for `out` is a BigInt in [0, modulus), but we do not constrain the inequality
// We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    modulus: &big_uint,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);
    assert!(modulus.bits() <= (n * k).try_into().unwrap());

    // overflow := a.max_limb_size.bits()
    // quot <= ceil(2^{overflow * k} / modulus) < 2^{overflow * k - modulus.bits() + 1}
    // there quot will need ceil( (overflow * k - modulus.bits() + 1 ) / n ) limbs
    let overflow = a.max_limb_size.bits().to_usize().unwrap();
    let m: usize = (n + overflow * k - modulus.bits().to_usize().unwrap() - 1) / n;
    assert!(m > 0);

    let a_val = a.to_bigint();
    // these are witness vectors:
    let (out_vec, quotient_vec) = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        (
            decompose_bigint_option::<F>(&Some(big_int::from(out)), k, n),
            decompose_bigint_option::<F>(&Some(quotient), m, n),
        )
    } else {
        (vec![None; k], vec![None; m])
    };
    // this is a constant vector:
    let mod_vec = decompose_biguint(&modulus, k, n);

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

    let k_prod = k + m - 1;
    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(m);
    // let mut prod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);

    let gate = &range.qap_config;
    for i in 0..k_prod {
        layouter.assign_region(
            || format!("carry_mod: prod_{}", i),
            |mut region| {
                let mut offset = 0;

                let mut prod_val = Some(F::zero());
                let mut prod_cell =
                    region.assign_advice_from_constant(|| "0", gate.value, 0, F::zero())?;
                region.constrain_constant(prod_cell.cell(), F::zero())?;

                let startj = if i >= m { i - m + 1 } else { 0 };
                for j in startj..=i {
                    if j >= k {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

                    if j < mod_assigned.len() {
                        // does it matter whether we are enabling equality from advice column or fixed column for constants?
                        mod_assigned[j].copy_advice(
                            || format!("mod_{}", j),
                            &mut region,
                            gate.value,
                            offset + 1,
                        )?;
                    } else {
                        assert_eq!(mod_assigned.len(), j);
                        // assign advice for CONSTANT mod_vec[j]
                        let cell = region.assign_advice_from_constant(
                            || format!("mod_{}", j),
                            gate.value,
                            offset + 1,
                            mod_vec[j],
                        )?;
                        region.constrain_constant(cell.cell(), mod_vec[j])?;
                        mod_assigned.push(cell);
                    };
                    if i - j < quot_assigned.len() {
                        quot_assigned[i - j].copy_advice(
                            || format!("quot_{}", i - j),
                            &mut region,
                            gate.value,
                            offset + 2,
                        )?;
                    } else {
                        assert_eq!(quot_assigned.len(), i - j);
                        let cell = region.assign_advice(
                            || format!("quot_{}", i - j),
                            gate.value,
                            offset + 2,
                            || quotient_vec[i - j].ok_or(Error::Synthesis),
                        )?;
                        quot_assigned.push(cell);
                    };

                    prod_val = prod_val
                        .zip(quotient_vec[i - j])
                        .map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_cell = region.assign_advice(
                        || "partial sum prod",
                        gate.value,
                        offset + 3,
                        || prod_val.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                // prod_assigned.push(prod_cell);

                if i < k {
                    // perform step 2: compute prod - a + out
                    gate.q_enable.enable(&mut region, offset)?;

                    let minus_1 = -F::from(1);
                    let cell = region.assign_advice_from_constant(
                        || "-1",
                        gate.value,
                        offset + 1,
                        minus_1,
                    )?;
                    region.constrain_constant(cell.cell(), minus_1)?;

                    a.limbs[i].copy_advice(
                        || format!("a_{}", i),
                        &mut region,
                        gate.value,
                        offset + 2,
                    )?;

                    // prod - a
                    let temp1 = prod_val.zip(a.limbs[i].value()).map(|(prod, &a)| prod - a);
                    region.assign_advice(
                        || format!("(mod * quot - a)_{}", i),
                        gate.value,
                        offset + 3,
                        || temp1.ok_or(Error::Synthesis),
                    )?;
                    gate.q_enable.enable(&mut region, offset + 3)?;

                    let cell = region.assign_advice_from_constant(
                        || "1",
                        gate.value,
                        offset + 4,
                        F::from(1),
                    )?;
                    region.constrain_constant(cell.cell(), F::from(1))?;

                    let out_cell = region.assign_advice(
                        || format!("out_{}", i),
                        gate.value,
                        offset + 5,
                        || out_vec[i].ok_or(Error::Synthesis),
                    )?;
                    out_assigned.push(out_cell);

                    let check_val = temp1.zip(out_vec[i]).map(|(a, b)| a + b);
                    let check_cell = region.assign_advice(
                        || format!("(mod * quot - a + out)_{}", i),
                        gate.value,
                        offset + 6,
                        || check_val.ok_or(Error::Synthesis),
                    )?;
                    check_assigned.push(check_cell)
                } else {
                    check_assigned.push(prod_cell);
                }

                Ok(())
            },
        )?;
    }
    assert_eq!(mod_assigned.len(), k);
    assert_eq!(quot_assigned.len(), m);

    let out_max_limb_size = (big_uint::one() << n) - 1usize;
    // range check limbs of `out` are in [0, 2^n)
    for out_cell in out_assigned.iter() {
        range.range_check(layouter, out_cell, n)?;
    }

    let limb_base = biguint_to_fe(&(big_uint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n)
    for quot_cell in quot_assigned.iter() {
        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", n),
            |mut region| {
                gate.q_enable.enable(&mut region, 0)?;
                quot_cell.copy_advice(|| "quot", &mut region, gate.value, 0)?;

                let cell = region.assign_advice_from_constant(|| "1", gate.value, 1, limb_base)?;
                region.constrain_constant(cell.cell(), limb_base)?;

                let cell = region.assign_advice_from_constant(|| "1", gate.value, 2, F::one())?;
                region.constrain_constant(cell.cell(), F::one())?;

                let out = quot_cell.value().map(|&a| a + limb_base);
                region.assign_advice(|| "out", gate.value, 3, || out.ok_or(Error::Synthesis))
            },
        )?;

        range.range_check(layouter, &quot_shift, n + 1)?;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &out_max_limb_size + &a.max_limb_size + (big_uint::from(std::cmp::min(k, m)) << (2 * n)),
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

pub fn get_carry_witness(a: &big_int, modulus: &big_uint) -> (big_uint, big_int) {
    if a < &big_int::zero() {
        let a_neg = big_int::to_biguint(&-a).unwrap();
        let quotient = (&a_neg + modulus - 1u32) / modulus;
        let out = modulus * &quotient - a_neg;
        (out, big_int::from_biguint(Sign::Minus, quotient))
    } else {
        let a = big_int::to_biguint(a).unwrap();
        let quotient = &a / modulus;
        (a - modulus * &quotient, quotient.into())
    }
}

#[cfg(test)]
#[test]
fn test_carry_witness() {
    let a = big_int::from(-17);
    let modulus = big_uint::from(15u32);
    let (out, q) = get_carry_witness(&a, &modulus);
    assert_eq!(a, big_int::from(out) + big_int::from(modulus) * q);
}
