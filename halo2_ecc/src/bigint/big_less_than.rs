use super::OverflowInteger;
use halo2_base::gates::{AssignedValue, Context, RangeInstructions};
use halo2_proofs::{arithmetic::FieldExt, plonk::Error};

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a < b`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<AssignedValue<F>, Error> {
    // a < b iff a - b has underflow
    let (_, underflow) = super::sub::assign(range, ctx, a, b)?;
    Ok(underflow)
}
