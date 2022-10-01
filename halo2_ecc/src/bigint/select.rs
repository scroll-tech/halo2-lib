use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt;
use std::cmp;

use super::{CRTInteger, OverflowInteger};
use crate::gates::{Context, GateInstructions, QuantumCell::Existing};
use crate::utils::{fe_to_bigint, value_to_option};

pub fn assign<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
    sel: &AssignedCell<F, F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k = cmp::min(a.limbs.len(), b.limbs.len());
    let mut out_limbs = Vec::with_capacity(k);

    for (a_limb, b_limb) in a.limbs.iter().zip(b.limbs.iter()) {
        let out_limb = gate.select(ctx, &Existing(&a_limb), &Existing(&b_limb), &Existing(&sel))?;
        out_limbs.push(out_limb);
    }

    Ok(OverflowInteger::construct(
        out_limbs,
        cmp::max(a.max_limb_size.clone(), b.max_limb_size.clone()),
        a.limb_bits,
        cmp::max(a.max_size.clone(), b.max_size.clone()),
    ))
}

pub fn crt<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
    sel: &AssignedCell<F, F>,
) -> Result<CRTInteger<F>, Error> {
    assert_eq!(a.truncation.limb_bits, b.truncation.limb_bits);
    let k = cmp::min(a.truncation.limbs.len(), b.truncation.limbs.len());
    let mut out_limbs = Vec::with_capacity(k);

    for (a_limb, b_limb) in a.truncation.limbs.iter().zip(b.truncation.limbs.iter()) {
        let out_limb = gate.select(ctx, &Existing(a_limb), &Existing(b_limb), &Existing(sel))?;
        out_limbs.push(out_limb);
    }

    let out_trunc = OverflowInteger::construct(
        out_limbs,
        cmp::max(a.truncation.max_limb_size.clone(), b.truncation.max_limb_size.clone()),
        a.truncation.limb_bits,
        cmp::max(a.truncation.max_size.clone(), b.truncation.max_size.clone()),
    );

    let out_native =
        gate.select(ctx, &Existing(&a.native), &Existing(&b.native), &Existing(&sel))?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).zip(sel.value()).map(|((a, b), s)| {
        let s = fe_to_bigint(s);
        (a * &s) + ((BigInt::from(1) - &s) * b)
    });
    Ok(CRTInteger::construct(out_trunc, out_native, out_val))
}
