use std::cmp;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &Vec<OverflowInteger<F>>,
    coeffs: &Vec<AssignedCell<F, F>>
) -> Result<OverflowInteger<F>, Error> {
    let length = coeffs.len();
    let k = a[0].limbs.len();
    assert_eq!(length, a.len());

    let coeffs_quantum = coeffs.iter().map(|x| Existing(&x)).collect();
    let mut out_limbs = Vec::with_capacity(k);
    for idx in 0..k {
	let mut int_limbs = Vec::with_capacity(length);
	for int_idx in 0..length {
	    int_limbs.push(Existing(&a[int_idx].limbs[idx]));
	}
	let limb_res = gate.inner_product(layouter, &int_limbs, &coeffs_quantum)?;
	out_limbs.push(limb_res.2.clone());
    }

    let max_limb_size = a.iter().fold(BigUint::from(0u64), |acc, x| cmp::max(acc, x.max_limb_size.clone()));
    
    Ok(OverflowInteger::construct(
        out_limbs,
	max_limb_size,
        a[0].limb_bits,
    ))
}
