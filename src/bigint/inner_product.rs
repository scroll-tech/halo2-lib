use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::{BigInt, BigUint};
use std::cmp;

use super::{CRTInteger, OverflowInteger};
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::utils::fe_to_bigint;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &Vec<OverflowInteger<F>>,
    coeffs: &Vec<AssignedCell<F, F>>,
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

    let max_limb_size = a.iter().fold(BigUint::from(0u64), |acc, x| {
        cmp::max(acc, x.max_limb_size.clone())
    });

    Ok(OverflowInteger::construct(
        out_limbs,
        max_limb_size,
        a[0].limb_bits,
    ))
}

// only use case is when coeffs has only a single 1, rest are 0
pub fn crt<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &Vec<CRTInteger<F>>,
    coeffs: &Vec<AssignedCell<F, F>>,
) -> Result<CRTInteger<F>, Error> {
    let length = coeffs.len();
    let k = a[0].truncation.limbs.len();
    assert_eq!(length, a.len());

    let coeffs_quantum = coeffs.iter().map(|x| Existing(&x)).collect();
    let mut out_limbs = Vec::with_capacity(k);
    for idx in 0..k {
        let mut int_limbs = Vec::with_capacity(length);
        for int_idx in 0..length {
            int_limbs.push(Existing(&a[int_idx].truncation.limbs[idx]));
        }
        let (_, _, limb_res) = gate.inner_product(layouter, &int_limbs, &coeffs_quantum)?;
        out_limbs.push(limb_res);
    }

    let max_limb_size = a.iter().fold(BigUint::from(0u64), |acc, x| {
        cmp::max(acc, x.truncation.max_limb_size.clone())
    });

    let out_trunc = OverflowInteger::construct(out_limbs, max_limb_size, a[0].truncation.limb_bits);
    let a_native = a.iter().map(|x| Existing(&x.native)).collect();
    let (_, _, out_native) = gate.inner_product(layouter, &a_native, &coeffs_quantum)?;
    let out_val = a
        .iter()
        .zip(coeffs.iter())
        .fold(Some(BigInt::from(0)), |acc, (x, y)| {
            acc.zip(x.value.as_ref())
                .zip(y.value())
                .map(|((a, x), y)| a + x * fe_to_bigint(y))
        });

    let max_size = a.iter().fold(BigUint::from(0u64), |acc, x| {
        cmp::max(acc, x.max_size.clone())
    });

    Ok(CRTInteger::construct(
        out_trunc, out_native, out_val, max_size,
    ))
}
