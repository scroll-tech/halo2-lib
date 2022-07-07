use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::fe_to_big;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::*,
};
use num_bigint::BigUint;

// given an AssignedCell `a`, creates an OverflowInteger<F> containing a base
// `limb_base` decomposition of the value of `a`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &AssignedCell<F, F>,
    limb_bits: usize,
    num_limbs: usize,
) -> Result<OverflowInteger<F>, Error> {
    assert!(limb_bits <= 64);
    assert!(limb_bits % range.lookup_bits == 0);
    let k = num_limbs;

    let a_val_temp = a.value().ok_or(Error::Synthesis)?;
    let mut a_val = fe_to_big(a_val_temp);

    let mut limb_val = F::from(0);
    if limb_bits < 64 {
        limb_val = F::from(u64::pow(2, limb_bits as u32));
    } else if limb_bits == 64 {
        limb_val = F::from(u64::pow(2, 63)) * F::from(2);
    } else {
        assert!(false);
    }
    let big_2 = BigUint::from(2 as u32);
    let limb_val_big = big_2.pow(limb_bits as u32);

    let mut out_limbs = Vec::with_capacity(k);
    for idx in 0..k {
        let limb = u64::try_from(&a_val % &limb_val_big).unwrap();
        out_limbs.push(limb);
        a_val = &a_val / &limb_val_big;
    }

    let mut out_assignments = Vec::with_capacity(k);
    layouter.assign_region(
        || "decompose",
        |mut region| {
            region.assign_advice_from_constant(
                || "limb 0",
                range.qap_config.value,
                0,
                F::from(out_limbs[0]),
            )?;

            let mut offset = 1;
            let mut running_sum = F::from(out_limbs[0]);
            let mut running_pow = F::from(1);
            for idx in 1..k {
                running_pow = running_pow * limb_val;
                running_sum = running_sum + F::from(out_limbs[idx]) * &running_pow;

                let const_cell = region.assign_advice_from_constant(
                    || format!("base^{}", idx),
                    range.qap_config.value,
                    offset,
                    running_pow,
                )?;
                let limb_cell = region.assign_advice_from_constant(
                    || format!("limb {}", idx),
                    range.qap_config.value,
                    offset + 1,
                    F::from(out_limbs[idx]),
                )?;
                let out_cell = region.assign_advice_from_constant(
                    || format!("running sum {}", idx),
                    range.qap_config.value,
                    offset + 2,
                    running_sum.clone(),
                )?;

                region.constrain_constant(const_cell.cell(), running_pow.clone())?;
                range.qap_config.q_enable.enable(&mut region, offset - 1)?;

                offset = offset + 3;
                out_assignments.push(limb_cell);
                if idx == k - 1 {
                    region.constrain_equal(a.cell(), out_cell.cell())?;
                }
            }
            Ok(())
        },
    )?;

    for limb_cell in out_assignments.iter() {
        range.range_check(layouter, limb_cell, limb_bits)?;
    }

    Ok(OverflowInteger::construct(
        out_assignments,
        limb_val_big,
        limb_bits,
    ))
}
