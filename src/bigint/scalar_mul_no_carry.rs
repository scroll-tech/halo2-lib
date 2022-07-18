use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::utils::modulus as native_modulus;
use crate::utils::*;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: F,
) -> Result<OverflowInteger<F>, Error> {
    let k = a.limbs.len();
    assert!(k > 0);
    let mut out_limbs = Vec::with_capacity(k);

    for i in 0..k {
	let out_cell = gate.mul_constant(layouter, &&a.limbs[i], b)?;
        out_limbs.push(out_cell);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size * fe_to_biguint(&b),
        a.limb_bits,
    ))
}
