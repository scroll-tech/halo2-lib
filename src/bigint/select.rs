use std::cmp;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};

use super::OverflowInteger;
use crate::gates::qap_gate;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
    sel: &AssignedCell<F, F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k = cmp::min(a.limbs.len(), b.limbs.len());
    let mut out_limbs = Vec::with_capacity(k);

    for (a_limb, b_limb) in a.limbs.iter().zip(b.limbs.iter()) {
        let out_limb = gate.select(layouter, a_limb, b_limb, sel)?;
        out_limbs.push(out_limb);
    }
    
    Ok(OverflowInteger::construct(
        out_limbs,
        cmp::max(a.max_limb_size.clone(), b.max_limb_size.clone()),
        a.limb_bits,
    ))
}
