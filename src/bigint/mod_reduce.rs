use super::OverflowInteger;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;
use num_traits::{One, Zero};

use crate::{
    gates::qap_gate,
    utils::{big_to_fe, decompose_big},
};

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    desired_num_limbs: usize,
    modulus: big_uint,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let k = desired_num_limbs;

    assert!(k < a.limbs.len());
    assert!(modulus.bits() <= (n * k).try_into().unwrap());

    let m = a.limbs.len() - k;
    let limb_base = big_uint::one() << n;
    let mut r_limbs: Vec<F> = Vec::with_capacity(m * k);

    // For i >= desired_num_limbs, compute r[i] = limb_base^i % modulus
    let mut r = limb_base.pow(k.try_into().unwrap()) % &modulus;
    for _i in k..a.limbs.len() {
        if _i > k {
            r = (r * &limb_base) % &modulus;
        }
        let mut r_temp = r.clone();
        for _j in 0..k {
            r_limbs.push(big_to_fe(&(&r_temp % &limb_base))); // r_limbs[ (i-k) * k + j ]
            r_temp = r_temp / &limb_base;
        }
        assert_eq!(r_temp, big_uint::zero());
    }

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
