use super::{CRTInteger, OverflowInteger};
use halo2_base::utils::bigint_to_fe;
use halo2_base::{
    gates::{GateInstructions, RangeInstructions},
    AssignedValue, Context,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_proofs::{arithmetic::FieldExt, plonk::Error};
use num_bigint::BigInt;

/// Should only be called on integers a, b in proper representation with all limbs having at most `a.limb_bits` number of bits
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<(OverflowInteger<F>, AssignedValue<F>), Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    assert_eq!(a.limbs.len(), b.limbs.len());
    let k = a.limbs.len();
    let mut out_limbs = Vec::with_capacity(k);

    let mut borrow: Option<AssignedValue<F>> = None;
    let limb_base = bigint_to_fe::<F>(&(BigInt::from(1) << a.limb_bits));
    for i in 0..k {
        let (bottom, lt) = match borrow {
            None => {
                let lt = range.is_less_than(
                    ctx,
                    &Existing(&a.limbs[i]),
                    &Existing(&b.limbs[i]),
                    a.limb_bits,
                )?;
                (b.limbs[i].clone(), lt)
            }
            Some(borrow) => {
                let b_plus_borrow =
                    range.gate().add(ctx, &Existing(&b.limbs[i]), &Existing(&borrow))?;
                let lt = range.is_less_than(
                    ctx,
                    &Existing(&a.limbs[i]),
                    &Existing(&b_plus_borrow),
                    a.limb_bits + 1,
                )?;
                (b_plus_borrow, lt)
            }
        };
        let out_limb = {
            // | a | lt | 2^n | a + lt * 2^n | -1 | bottom | a + lt * 2^n - bottom
            let a_with_borrow_val =
                a.limbs[i].value().zip(lt.value()).map(|(&a, &lt)| a + lt * limb_base);
            let out_val = a_with_borrow_val.zip(bottom.value()).map(|(ac, &b)| ac - b);
            let assignments = range.gate().assign_region_smart(
                ctx,
                vec![
                    Existing(&a.limbs[i]),
                    Existing(&lt),
                    Constant(limb_base.clone()),
                    Witness(a_with_borrow_val),
                    Constant(-F::from(1)),
                    Existing(&bottom),
                    Witness(out_val),
                ],
                vec![0, 3],
                vec![],
                vec![],
            )?;
            assignments.last().unwrap().clone()
        };
        out_limbs.push(out_limb);
        borrow = Some(lt);
    }
    Ok((
        OverflowInteger::construct(
            out_limbs,
            a.max_limb_size.clone(),
            a.limb_bits,
            a.max_size.clone(),
        ),
        borrow.unwrap(),
    ))
}

// returns (a-b, underflow), where underflow is nonzero iff a < b
pub fn crt<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<(CRTInteger<F>, AssignedValue<F>), Error> {
    assert_eq!(a.truncation.limbs.len(), b.truncation.limbs.len());
    let (out_trunc, underflow) = assign(range, ctx, &a.truncation, &b.truncation)?;
    let out_native = range.gate().sub(ctx, &Existing(&a.native), &Existing(&b.native))?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a - b);
    Ok((CRTInteger::construct(out_trunc, out_native, out_val), underflow))
}
