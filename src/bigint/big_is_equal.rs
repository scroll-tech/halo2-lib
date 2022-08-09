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

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a == b`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    let k_a = a.limbs.len();
    let k_b = b.limbs.len();
    let limb_bits_a = a.limb_bits;
    let limb_bits_b = b.limb_bits;
    assert_eq!(k_a, k_b);
    assert_eq!(limb_bits_a, limb_bits_b);
    let k = k_a;
    let limb_bits = limb_bits_a;

    let mut eq = Vec::with_capacity(k);
    for idx in 0..k {
        let eq_limb = range.is_equal(layouter, &a.limbs[idx], &b.limbs[idx])?;
        eq.push(eq_limb);
    }

    let mut partials = Vec::with_capacity(k);
    partials.push(eq[0].clone());
    for idx in 0..(k - 1) {
        let new =
            range
                .qap_config
                .and(layouter, &Existing(&eq[idx + 1]), &Existing(&partials[idx]))?;
        partials.push(new);
    }
    Ok(partials[k - 1].clone())
}

pub fn crt<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<AssignedCell<F, F>, Error> {
    let out_trunc = assign(range, layouter, &a.truncation, &b.truncation)?;
    let out_native = range.is_equal(layouter, &a.native, &b.native)?;
    let out = range.qap_config.and(layouter, &Existing(&out_trunc), &Existing(&out_native))?;
    Ok(out)
}
