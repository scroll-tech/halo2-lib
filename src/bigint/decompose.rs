use super::OverflowInteger;
use crate::gates::range;
use crate::utils::*;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;
use num_traits::One;

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

    let a_val = a.value().map(|fe| *fe);
    let out_limbs = decompose_option(&a_val, k, limb_bits);
    let limb_base: F = biguint_to_fe(&(big_uint::one() << limb_bits));

    let mut out_assignments = Vec::with_capacity(k);
    layouter.assign_region(
        || "decompose",
        |mut region| {
            let mut limb_cell = region.assign_advice(
                || "limb 0",
                range.qap_config.value,
                0,
                || out_limbs[0].ok_or(Error::Synthesis),
            )?;
            out_assignments.push(limb_cell);

            let mut offset = 1;
            let mut running_sum = out_limbs[0];
            let mut running_pow = F::from(1);
            for idx in 1..k {
                running_pow = running_pow * limb_base;
                running_sum = running_sum
                    .zip(out_limbs[idx])
                    .map(|(sum, x)| sum + x * running_pow);

                let const_cell = region.assign_advice_from_constant(
                    || format!("base^{}", idx),
                    range.qap_config.value,
                    offset,
                    running_pow,
                )?;
                region.constrain_constant(const_cell.cell(), running_pow)?;

                limb_cell = region.assign_advice(
                    || format!("limb {}", idx),
                    range.qap_config.value,
                    offset + 1,
                    || out_limbs[idx].ok_or(Error::Synthesis),
                )?;
                let out_cell = region.assign_advice(
                    || format!("running sum {}", idx),
                    range.qap_config.value,
                    offset + 2,
                    || running_sum.ok_or(Error::Synthesis),
                )?;

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
        big_uint::one() << limb_bits,
        limb_bits,
    ))
}
