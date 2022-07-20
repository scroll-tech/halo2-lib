use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use std::cmp;

use super::{CRTInteger, OverflowInteger};
use crate::gates::qap_gate;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k = cmp::min(a.limbs.len(), b.limbs.len());
    let k_max = cmp::max(a.limbs.len(), b.limbs.len());
    let mut out_limbs = Vec::with_capacity(k_max);

    for (a_limb, b_limb) in a.limbs[..k].iter().zip(b.limbs[..k].iter()) {
        let out_limb = gate.add(layouter, a_limb, b_limb)?;
        out_limbs.push(out_limb);
    }
    if a.limbs.len() > k {
        for a_limb in &a.limbs[k..] {
            out_limbs.push(a_limb.clone());
        }
    } else {
        for b_limb in &b.limbs[k..] {
            out_limbs.push(b_limb.clone());
        }
    }

    Ok(OverflowInteger::construct(
        out_limbs,
        a.max_limb_size.clone() + b.max_limb_size.clone(),
        a.limb_bits,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<CRTInteger<F>, Error> {
    assert_eq!(a.truncation.limbs.len(), b.truncation.limbs.len());
    let out_trunc = assign(gate, layouter, &a.truncation, &b.truncation)?;
    let out_native = gate.add(layouter, &a.native, &b.native)?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a + b);
    Ok(CRTInteger::construct(
        out_trunc,
        out_native,
        out_val,
        &a.max_size + &b.max_size,
    ))
}
