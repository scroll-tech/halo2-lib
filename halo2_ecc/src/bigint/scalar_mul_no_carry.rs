use super::{CRTInteger, OverflowInteger};
use halo2_base::{
    gates::{
        Context, GateInstructions,
        QuantumCell::{Constant, Existing},
    },
    utils::fe_to_bigint,
};
use halo2_proofs::{arithmetic::FieldExt, plonk::Error};
use num_traits::Signed;

pub fn assign<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: F,
) -> Result<OverflowInteger<F>, Error> {
    let k = a.limbs.len();
    assert!(k > 0);
    let mut out_limbs = Vec::with_capacity(k);

    for i in 0..k {
        let out_cell = gate.mul(ctx, &Existing(&a.limbs[i]), &Constant(b))?;
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
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    b: F,
) -> Result<CRTInteger<F>, Error> {
    let k = a.truncation.limbs.len();
    assert!(k > 0);
    let mut out_limbs = Vec::with_capacity(k);

    for i in 0..k {
        let out_cell = gate.mul(ctx, &Existing(&a.truncation.limbs[i]), &Constant(b))?;
        out_limbs.push(out_cell);
    }

    let out_native = gate.mul(ctx, &Existing(&a.native), &Constant(b))?;
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
