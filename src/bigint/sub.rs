use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt;

use super::{CRTInteger, OverflowInteger};
use crate::gates::{
    GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::bigint_to_fe;

pub fn assign<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<(OverflowInteger<F>, AssignedCell<F, F>), Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    assert_eq!(a.limbs.len(), b.limbs.len());
    let k = a.limbs.len();
    let mut out_limbs = Vec::with_capacity(k);

    let mut borrow: Option<AssignedCell<F, F>> = None;
    let limb_base = bigint_to_fe::<F>(&(BigInt::from(1) << a.limb_bits));
    for i in 0..k {
        let (bottom, lt) = match borrow {
            None => {
                let lt = range.is_less_than(layouter, &a.limbs[i], &b.limbs[i], a.limb_bits)?;
                (b.limbs[i].clone(), lt)
            }
            Some(borrow) => {
                let b_plus_borrow =
                    range.gate().add(layouter, &Existing(&b.limbs[i]), &Existing(&borrow))?;
                let lt =
                    range.is_less_than(layouter, &a.limbs[i], &b_plus_borrow, a.limb_bits + 1)?;
                (b_plus_borrow, lt)
            }
        };
        let out_limb = layouter.assign_region(
            || format!("sub_{}", i),
            |mut region| {
                // | a | lt | 2^n | a + lt * 2^n | -1 | bottom | a + lt * 2^n - bottom
                let a_with_borrow_val =
                    a.limbs[i].value().zip(lt.value()).map(|(&a, &lt)| a + lt * limb_base);
                let out_val = a_with_borrow_val.zip(bottom.value()).map(|(ac, &b)| ac - b);
                let (assignments, column_index) = range.gate().assign_region_smart(
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
                    0,
                    &mut region,
                )?;
                Ok(assignments.last().unwrap().clone())
            },
        )?;
        out_limbs.push(out_limb);
        borrow = Some(lt);
    }
    Ok((
        OverflowInteger::construct(out_limbs, a.max_limb_size.clone(), a.limb_bits),
        borrow.unwrap(),
    ))
}

// returns (a-b, underflow), where underflow is nonzero iff a < b
pub fn crt<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<(CRTInteger<F>, AssignedCell<F, F>), Error> {
    assert_eq!(a.truncation.limbs.len(), b.truncation.limbs.len());
    let (out_trunc, underflow) = assign(range, layouter, &a.truncation, &b.truncation)?;
    let out_native = range.gate().sub(layouter, &Existing(&a.native), &Existing(&b.native))?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a - b);
    Ok((CRTInteger::construct(out_trunc, out_native, out_val, a.max_size.clone()), underflow))
}
