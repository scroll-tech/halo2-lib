use super::OverflowInteger;
use crate::gates::{GateInstructions, QuantumCell::Existing, RangeInstructions};
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::*,
};

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a == b`
pub fn assign<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;

    let mut partial = None;
    for idx in 0..k {
        let limb_is_zero = range.is_zero(layouter, &a.limbs[idx])?;
        if let Some(prev) = partial {
            let new = range.gate().and(layouter, &Existing(&limb_is_zero), &Existing(&prev))?;
            partial = Some(new);
        } else {
            partial = Some(limb_is_zero);
        }
    }

    Ok(partial.unwrap())
}
