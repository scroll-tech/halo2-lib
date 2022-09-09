use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;
use num_traits::Signed;

use super::{CRTInteger, OverflowInteger};
use crate::gates::{
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::utils::modulus as native_modulus;
use crate::utils::*;

pub fn assign<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
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
    let b_abs = fe_to_bigint(&b).abs().to_biguint().unwrap();
    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size * &b_abs,
        a.limb_bits,
        &a.max_size * &b_abs,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
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
            &a.truncation.max_size * &b_abs,
        ),
        out_native,
        out_val,
    ))
}
