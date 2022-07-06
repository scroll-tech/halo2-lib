use super::OverflowInteger;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;

use crate::{
    gates::qap_gate,
    utils::{big_to_fe, decompose_big},
};

pub fn assign(
    &self,
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    desired_num_limbs: usize,
    modulus: big_uint,
) -> Result<Self, Error> {
    let n = self.limb_bits;
    let k = desired_num_limbs;

    assert!(k < self.limbs.len());
    assert!(modulus.bits() <= (n * k).try_into().unwrap());

    let m = self.limbs.len() - k;
    let limb_base = big_uint::one() << n;
    let mut r_limbs = Vec::with_capacity(m * k);

    // For i >= desired_num_limbs, compute r[i] = limb_base^i % modulus
    let mut r = (&limb_base << k) % &modulus;
    for _i in k..self.limbs.len() {
        if _i > 0 {
            r = (r * &limb_base) % &modulus;
        }
        let mut r_temp = r.clone();
        for _j in 0..k {
            r_limbs.push(big_to_fe(&r_temp % &limb_base)); // r_limbs[ (i-k) * m + j ]
            r_temp = r_temp / &limb_base;
        }
    }

    let mut out_limbs = Vec::with_capacity(k);
    for j in 0..k {
        let out_limb = layouter.assign_region(
            || format!("mod_reduce_{}", j),
            |mut region| {
                let mut offset = 0;

                let mut out_val = self.limbs[j].value().map(|a| *a);
                let mut out_limb = self.limbs[j].copy_advice(
                    || format!("limbs_{}", j),
                    &mut region,
                    gate.value,
                    offset,
                )?;

                for i in k..self.limbs.len() {
                    gate.q_enable.enable(&mut region, offset)?;

                    let r_val = &r_limbs[(i - k) * m + j];
                    let r_cell = region.assign_advice_from_constant(
                        || format!("r[{}][{}]", i, j),
                        gate.value,
                        offset + 1,
                        *r_val,
                    )?;
                    region.constrain_constant(r_cell.cell(), *r_val)?;

                    self.limbs[i].copy_advice(
                        || format!("limbs_{}", i),
                        &mut region,
                        gate.value,
                        offset + 2,
                    )?;

                    out_val = out_val
                        .zip(self.limbs[i].value())
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
        &self.max_limb_size
            + big_uint::from(self.limbs.len() - k) * &self.max_limb_size * &limb_base,
        self.limb_bits,
    ))
}
