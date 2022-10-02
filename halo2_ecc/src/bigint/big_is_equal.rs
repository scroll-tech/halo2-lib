use super::{CRTInteger, OverflowInteger};
use halo2_base::gates::{
    AssignedValue, Context, GateInstructions, QuantumCell::Existing, RangeInstructions,
};
use halo2_proofs::{arithmetic::FieldExt, plonk::Error};

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a == b`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<AssignedValue<F>, Error> {
    let k_a = a.limbs.len();
    let k_b = b.limbs.len();
    let limb_bits_a = a.limb_bits;
    let limb_bits_b = b.limb_bits;
    assert_eq!(k_a, k_b);
    assert_eq!(limb_bits_a, limb_bits_b);
    let k = k_a;

    let mut eq = Vec::with_capacity(k);
    for idx in 0..k {
        let eq_limb = range.is_equal(ctx, &Existing(&a.limbs[idx]), &Existing(&b.limbs[idx]))?;
        eq.push(eq_limb);
    }

    let mut partials = Vec::with_capacity(k);
    partials.push(eq[0].clone());
    for idx in 0..(k - 1) {
        let new = range.gate().and(ctx, &Existing(&eq[idx + 1]), &Existing(&partials[idx]))?;
        partials.push(new);
    }
    Ok(partials[k - 1].clone())
}

pub fn crt<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<AssignedValue<F>, Error> {
    let out_trunc = assign(range, ctx, &a.truncation, &b.truncation)?;
    let out_native = range.is_equal(ctx, &Existing(&a.native), &Existing(&b.native))?;
    let out = range.gate().and(ctx, &Existing(&out_trunc), &Existing(&out_native))?;
    Ok(out)
}
