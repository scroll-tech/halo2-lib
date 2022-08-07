use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use std::cmp;

use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell::Existing;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    let k = a.limbs.len();

    let mut out_limbs = Vec::with_capacity(k);
    for limb in &a.limbs {
        let out_limb = gate.neg(layouter, &Existing(&limb))?;
        out_limbs.push(out_limb);
    }

    Ok(OverflowInteger::construct(
        out_limbs,
        a.max_limb_size.clone(),
        a.limb_bits,
    ))
}
