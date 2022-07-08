use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::*,
};
use num_bigint::BigUint as big_uint;
use num_traits::One;

// given OverflowInteger<F>'s `a` and `b` of the same shape,
// returns whether `a < b`
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

    let mut lt = Vec::with_capacity(k);
    let mut eq = Vec::with_capacity(k);
    for idx in 0..k {
	let lt_limb = range.is_less_than(
	    layouter,
	    &a.limbs[idx],
	    &b.limbs[idx],
	    limb_bits)?;
	lt.push(lt_limb);

	let eq_limb = range.is_equal(
	    layouter,
	    &a.limbs[idx],
	    &b.limbs[idx])?;
	eq.push(eq_limb);
    }

    let mut partials = Vec::with_capacity(k);
    partials.push(lt[0].clone());
    for idx in 0..(k - 1) {
	let new = range.qap_config.or_and(
	    layouter,
	    &lt[idx + 1],
	    &eq[idx + 1],
	    &partials[idx])?;
	partials.push(new);
    }
    Ok(partials[k - 1].clone())
}
