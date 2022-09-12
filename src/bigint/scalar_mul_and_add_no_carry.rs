use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_traits::Signed;
use std::cmp;

use super::{CRTInteger, OverflowInteger};
use crate::{
    gates::{
        GateInstructions,
        QuantumCell::{Constant, Existing, Witness},
    },
    utils::fe_to_bigint,
};

/// compute a * c + b = b + a * c
// this is uniquely suited for our simple gate
pub fn assign<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
    c: F,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k_max = cmp::max(a.limbs.len(), b.limbs.len());
    let mut out_limbs = Vec::with_capacity(k_max);

    for i in 0..k_max {
        let out_limb = {
            if i < a.limbs.len() && i < b.limbs.len() {
                layouter.assign_region(
                    || format!("scalar_mult_and_add_{}", i),
                    |mut region| {
                        let out_val =
                            b.limbs[i].value().zip(a.limbs[i].value()).map(|(&b, &a)| b + a * c);
                        let assigned_cells = gate.assign_region_smart(
                            vec![
                                Existing(&b.limbs[i]),
                                Existing(&a.limbs[i]),
                                Constant(c),
                                Witness(out_val),
                            ],
                            vec![0],
                            vec![],
                            vec![],
                            0,
                            &mut region,
                        )?;
                        Ok(assigned_cells.last().unwrap().clone())
                    },
                )?
            } else if i < a.limbs.len() {
                gate.mul(layouter, &Existing(&a.limbs[i]), &Constant(c))?
            } else {
                b.limbs[i].clone()
            }
        };
        out_limbs.push(out_limb);
    }
    let c_abs = fe_to_bigint(&c).abs().to_biguint().unwrap();

    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size * &c_abs + &b.max_limb_size,
        a.limb_bits,
        &a.max_size * &c_abs + &b.max_size,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
    c: F,
) -> Result<CRTInteger<F>, Error> {
    assert_eq!(a.truncation.limbs.len(), b.truncation.limbs.len());
    let out_trunc = assign(gate, layouter, &a.truncation, &b.truncation, c)?;
    let out_native = layouter.assign_region(
        || "native scalar_mult_and_add",
        |mut region| {
            let out_val = b.native.value().zip(a.native.value()).map(|(&b, &a)| b + a * c);
            let assigned_cells = gate.assign_region_smart(
                vec![Existing(&b.native), Existing(&a.native), Constant(c), Witness(out_val)],
                vec![0],
                vec![],
                vec![],
                0,
                &mut region,
            )?;
            Ok(assigned_cells.last().unwrap().clone())
        },
    )?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a * fe_to_bigint(&c) + b);
    Ok(CRTInteger::construct(out_trunc, out_native, out_val))
}
