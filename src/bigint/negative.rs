use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use std::cmp;

use super::OverflowInteger;
use crate::gates::{Context, GateInstructions, QuantumCell::Existing};

pub fn assign<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    let k = a.limbs.len();

    let mut out_limbs = Vec::with_capacity(k);
    for limb in &a.limbs {
        let out_limb = gate.neg(ctx, &Existing(&limb))?;
        out_limbs.push(out_limb);
    }

    Ok(OverflowInteger::construct(
        out_limbs,
        a.max_limb_size.clone(),
        a.limb_bits,
        a.max_size.clone(),
    ))
}
