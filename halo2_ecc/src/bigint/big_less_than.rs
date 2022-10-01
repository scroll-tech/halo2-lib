use super::{CRTInteger, OverflowInteger};
use halo2_base::gates::{Context, GateInstructions, QuantumCell::Existing, RangeInstructions};
use halo2_proofs::arithmetic::{Field, FieldExt};
use num_bigint::BigUint as big_uint;
use num_traits::One;

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a < b`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    // a < b iff a - b has underflow
    let (_, underflow) = super::sub::assign(range, ctx, a, b)?;
    Ok(underflow)
}
