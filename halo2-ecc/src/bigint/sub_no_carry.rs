use super::{CRTInteger, OverflowInteger};
use halo2_base::{gates::GateInstructions, utils::ScalarField, Context};
use std::cmp::max;

pub fn assign<F: ScalarField>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> OverflowInteger<F> {
    debug_assert_eq!(a.limbs.len(), b.limbs.len());
    let out_limbs = a
        .limbs
        .iter()
        .zip(b.limbs.iter())
        .map(|(&a_limb, &b_limb)| gate.sub(ctx, a_limb, b_limb))
        .collect();

    OverflowInteger::construct(out_limbs, max(a.max_limb_bits, b.max_limb_bits) + 1)
}

pub fn crt<F: ScalarField>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> CRTInteger<F> {
    let out_trunc = assign::<F>(gate, ctx, &a.truncation, &b.truncation);
    let out_native = gate.sub(ctx, a.native, b.native);
    let out_val = &a.value - &b.value;
    CRTInteger::construct(out_trunc, out_native, out_val)
}
