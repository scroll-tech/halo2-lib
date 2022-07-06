use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::{big_to_fe, modulus};

// checks there exist d_i = -c_i so that
// a0 = c0 * 2^n
// a_{i + 1} + c_i = c_{i + 1} * 2^n for i = 0.. k - 2
// a_{k - 1} + c_{k - 2} = 0
// and c_i \in [-2^{m - n}, 2^{m - n}]
//
// translated to d_i, this becomes:
// a0 + d0 * 2^n = 0
// a_{i + 1} + d_{i + 1} * 2^n = d_i for i = 0.. k - 2
// a_{k - 1} = d_{k - 2}
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<(), Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;
    let max_limb_bits = a.max_limb_size.bits();

    let mut carries = Vec::with_capacity(k);
    let limb_val = BigUint::from(1u32) << limb_bits;
    for idx in 0..k {
        let a_val_temp = a.limbs[idx].value().ok_or(Error::Synthesis)?;
        let a_val = BigUint::from_bytes_le(a_val_temp.to_repr().as_ref().try_into().unwrap());

        if idx == 0 {
            carries.push(a_val / &limb_val);
        } else {
            let carry_val = &carries[idx - 1];
            carries.push((a_val + carry_val) / &limb_val);
        }
    }

    let mut carry_assignments = Vec::with_capacity(k);
    layouter.assign_region(
        || "carry consistency",
        |mut region| {
            let mut offset = 0;
            for idx in 0..k {
                range.qap_config.q_enable.enable(&mut region, offset)?;

                a.limbs[idx].copy_advice(
                    || format!("a_{}", idx),
                    &mut region,
                    range.qap_config.value,
                    offset,
                )?;
                let last_carry = region.assign_advice(
                    || "negative carry",
                    range.qap_config.value,
                    offset + 1,
                    || Ok(big_to_fe::<F>(&(modulus::<F>() - &carries[idx]))),
                )?;
                carry_assignments.push(last_carry);
                let limb = region.assign_advice_from_constant(
                    || "base",
                    range.qap_config.value,
                    offset + 2,
                    big_to_fe::<F>(&limb_val),
                )?;
                region.constrain_constant(limb.cell(), big_to_fe::<F>(&limb_val))?;

                if idx == 0 {
                    let zero = region.assign_advice_from_constant(
                        || "zero",
                        range.qap_config.value,
                        offset + 3,
                        F::from(0),
                    )?;
                    region.constrain_constant(zero.cell(), F::from(0))?;
                } else {
                    carry_assignments[idx - 1].copy_advice(
                        || "prev negative carry",
                        &mut region,
                        range.qap_config.value,
                        offset + 3,
                    )?;
                }
                offset = offset + 4;
            }
            region.constrain_equal(a.limbs[k - 1].cell(), carry_assignments[k - 2].cell());
            Ok(())
        },
    );

    let range_bits = (((max_limb_bits - (limb_bits as u64) + 1 + (range.lookup_bits as u64) - 1)
        / (range.lookup_bits as u64))
        * (range.lookup_bits as u64)) as usize;
    let shift_val = big_to_fe::<F>(&(BigUint::one() << (range_bits - 1)));
    let mut shifted_carry_assignments = Vec::with_capacity(k);
    for carry_cell in carry_assignments.iter() {
        layouter.assign_region(
            || "shift carries",
            |mut region| {
                range.qap_config.q_enable.enable(&mut region, 0)?;
                carry_cell.copy_advice(
                    || "copy for range",
                    &mut region,
                    range.qap_config.value,
                    0,
                )?;

                let one = region.assign_advice_from_constant(
                    || "one",
                    range.qap_config.value,
                    1,
                    F::from(1),
                )?;
                region.constrain_constant(one.cell(), F::from(1))?;

                let shift = region.assign_advice_from_constant(
                    || "shift",
                    range.qap_config.value,
                    2,
                    shift_val,
                )?;
                region.constrain_constant(shift.cell(), shift_val)?;

                let carry_val = carry_cell.value().ok_or(Error::Synthesis)?;
                let shifted_carry = region.assign_advice(
                    || "shifted carry",
                    range.qap_config.value,
                    3,
                    || Ok(*carry_val + shift_val),
                )?;
                shifted_carry_assignments.push(shifted_carry);
                Ok(())
            },
        )?;
    }

    for shifted_carry in shifted_carry_assignments.iter() {
        range.range_check(layouter, shifted_carry, range_bits)?;
    }
    Ok(())
}
