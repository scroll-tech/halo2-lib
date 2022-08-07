use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;
use num_traits::Signed;

use super::{CRTInteger, OverflowInteger};
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
        let out_cell = gate.mul(layouter, &Existing(&a.limbs[i]), &Constant(b))?;
        out_limbs.push(out_cell);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size * fe_to_biguint(&b),
        a.limb_bits,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: F,
) -> Result<CRTInteger<F>, Error> {
    let k = a.truncation.limbs.len();
    assert!(k > 0);
    let mut out_limbs = Vec::with_capacity(k);

    for i in 0..k {
        let out_cell = gate.mul(layouter, &Existing(&a.truncation.limbs[i]), &Constant(b))?;
        out_limbs.push(out_cell);
    }

    let out_native = gate.mul(layouter, &Existing(&a.native), &Constant(b))?;
    let b_val = fe_to_bigint(&b);
    let b_abs = b_val.abs().to_biguint().unwrap();
    let out_val = a.value.as_ref().map(|a| a * &b_val);

    Ok(CRTInteger::construct(
        OverflowInteger::construct(
            out_limbs,
            &a.truncation.max_limb_size * &b_abs,
            a.truncation.limb_bits,
        ),
        out_native,
        out_val,
        &a.max_size * &b_abs,
    ))
}
