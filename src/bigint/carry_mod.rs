use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::{One, Zero};

use super::*;
use crate::{gates::qap_gate, utils::*};

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Output is `a (mod modulus)` as a proper BigInt of length `k` with limbs in [0, 2^limb_bits)`
// The witness for `out` is a BigInt in [0, modulus), but we do not constrain the inequality
// We constrain `a = out + modulus * quotient` and range check `out` and `quotient`
pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    modulus: big_uint,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);
    assert!(modulus.bits() <= (n * k).try_into().unwrap());

    let a_big = a.to_signed_big();

    let limb_base = big_uint::one() << n;
    let mut r_limbs: Vec<F> = Vec::with_capacity(m * k);

    let mut out_limbs = Vec::with_capacity(k);
    for j in 0..k {
        let out_limb = layouter.assign_region(
            || format!("mod_reduce_{}", j),
            |mut region| {
                let mut offset = 0;

                let mut out_val = a.limbs[j].value().map(|a| *a);
                let mut out_limb = a.limbs[j].copy_advice(
                    || format!("limbs_{}", j),
                    &mut region,
                    gate.value,
                    offset,
                )?;

                for i in k..a.limbs.len() {
                    gate.q_enable.enable(&mut region, offset)?;

                    let r_val = &r_limbs[(i - k) * k + j];
                    let r_cell = region.assign_advice_from_constant(
                        || format!("r[{}][{}]", i, j),
                        gate.value,
                        offset + 1,
                        *r_val,
                    )?;
                    region.constrain_constant(r_cell.cell(), *r_val)?;

                    a.limbs[i].copy_advice(
                        || format!("limbs_{}", i),
                        &mut region,
                        gate.value,
                        offset + 2,
                    )?;
                    out_val = out_val
                        .zip(a.limbs[i].value())
                        .map(|(sum, c)| sum + *r_val * *c);

                    out_limb = region.assign_advice(
                        || "running sum",
                        gate.value,
                        offset + 3,
                        || out_val.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                Ok(out_limb)
            },
        )?;
        out_limbs.push(out_limb);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size + big_uint::from(a.limbs.len() - k) * &a.max_limb_size * &limb_base,
        a.limb_bits,
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
