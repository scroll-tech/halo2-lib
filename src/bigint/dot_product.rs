use std::cmp;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};

use super::OverflowInteger;
use crate::gates::qap_gate;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    ints: &Vec<OverflowInteger<F>>,
    coeffs: &Vec<AssignedCell<F, F>>
) -> Result<OverflowInteger<F>, Error> {
    let length = coeffs.len();
    assert_eq!(length, ints.len());

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
