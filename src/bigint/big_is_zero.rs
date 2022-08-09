use super::{CRTInteger, OverflowInteger};
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell::Existing;
use crate::gates::range;
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::*,
};

// given OverflowInteger<F> `a`, returns whether `a == 0`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;

    let mut partial = None;
    for idx in 0..k {
        let limb_is_zero = range.is_zero(layouter, &a.limbs[idx])?;
        if let Some(prev) = partial {
            let new = range
                .qap_config
                .and(layouter, &Existing(&limb_is_zero), &Existing(&prev))?;
            partial = Some(new);
        } else {
            partial = Some(limb_is_zero);
        }
    }

    Ok(partial.unwrap())
}

pub fn crt<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    let out_trunc = assign(range, layouter, &a.truncation)?;
    let out_native = range.is_zero(layouter, &a.native)?;
    let out = range.qap_config.and(layouter, &Existing(&out_trunc), &Existing(&out_native))?;
    Ok(out)
}
