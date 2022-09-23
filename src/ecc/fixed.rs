#![allow(non_snake_case)]
use std::marker::PhantomData;

use ff::PrimeField;
use group::Group;
use halo2_proofs::{
    arithmetic::{BaseExt, CurveAffine, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};
use rand_core::OsRng;

use crate::gates::QuantumCell::{self, Constant, Existing, Witness};
use crate::utils::{
    bigint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint, fe_to_biguint, modulus,
};
use crate::{
    bigint::{
        add_no_carry, inner_product, mul_no_carry, scalar_mul_no_carry, sub_no_carry, CRTInteger,
        FixedCRTInteger, OverflowInteger,
    },
    fields::PrimeFieldChip,
};
use crate::{fields::FieldChip, gates::RangeInstructions};
use crate::{
    fields::{fp::FpConfig, Selectable},
    gates::{Context, GateInstructions},
};

use super::{ecc_add_unequal, select, select_from_bits, EccPoint};

// this only works for curves GA with base field of prime order
#[derive(Clone, Debug)]
pub struct FixedEccPoint<F: FieldExt, GA: CurveAffine> {
    pub x: FixedCRTInteger<F>,
    pub y: FixedCRTInteger<F>,
    _marker: PhantomData<GA>,
}

impl<'a, F: FieldExt, GA: CurveAffine> FixedEccPoint<F, GA>
where
    GA::Base: PrimeField,
{
    pub fn construct(x: FixedCRTInteger<F>, y: FixedCRTInteger<F>) -> Self {
        Self { x, y, _marker: PhantomData }
    }

    pub fn from_g1(P: &GA, num_limbs: usize, limb_bits: usize) -> Self {
        let x_pt = FixedCRTInteger::from_native(
            fe_to_biguint(P.coordinates().unwrap().x()).into(),
            num_limbs,
            limb_bits,
        );
        let y_pt = FixedCRTInteger::from_native(
            fe_to_biguint(P.coordinates().unwrap().y()).into(),
            num_limbs,
            limb_bits,
        );
        Self::construct(x_pt, y_pt)
    }

    pub fn assign<FC>(
        &self,
        chip: &FC,
        ctx: &mut Context<'_, F>,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error>
    where
        FC: PrimeFieldChip<F, FieldType = GA::Base, FieldPoint = CRTInteger<F>>,
    {
        let assigned_x = self.x.assign(chip.range().gate(), ctx)?;
        let assigned_y = self.y.assign(chip.range().gate(), ctx)?;
        let point = EccPoint::construct(assigned_x, assigned_y);
        Ok(point)
    }
}

// computes `[scalar] * P` on y^2 = x^3 + b where `P` is fixed (constant)
// - `scalar` is represented as a reference array of `AssignedCell`s
// - `scalar = sum_i scalar_i * 2^{max_bits * i}`
// - an array of length > 1 is needed when `scalar` exceeds the modulus of scalar field `F`
// assumes:
// - `scalar_i < 2^{max_bits} for all i` (constrained by num_to_bits)
// - `max_bits <= modulus::<F>.bits()`

pub fn fixed_base_scalar_multiply<'a, F, FC, GA>(
    chip: &FC,
    ctx: &mut Context<'_, F>,
    P: &FixedEccPoint<F, GA>,
    scalar: &Vec<AssignedCell<F, F>>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    F: FieldExt,
    GA: CurveAffine,
    GA::Base: PrimeField,
    FC: PrimeFieldChip<F, FieldType = GA::Base, FieldPoint = CRTInteger<F>>
        + Selectable<F, Point = FC::FieldPoint>,
{
    assert!(scalar.len() > 0);
    assert!((max_bits as u64) <= modulus::<F>().bits());

    let total_bits = max_bits * scalar.len();
    let num_windows = (total_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    // cached_points[i][j] holds j * 2^(i * w) for j in {0, ..., 2^w - 1}
    let mut cached_points = Vec::with_capacity(num_windows);
    let base_pt = GA::from_xy(bigint_to_fe(&P.x.value), bigint_to_fe(&P.y.value)).unwrap();
    let base_pt_assigned = P.assign(chip, ctx)?;

    let mut increment = base_pt;
    for i in 0..num_windows {
        let mut cache_vec = Vec::with_capacity(1usize << window_bits);
        let mut curr = increment;

        let increment_fixed = FixedEccPoint::from_g1(
            &increment,
            P.x.truncation.limbs.len(),
            P.x.truncation.limb_bits,
        );
        let increment_assigned = increment_fixed.assign(chip, ctx)?;
        cache_vec.push(increment_assigned.clone());
        cache_vec.push(increment_assigned.clone());
        for j in 2..(1usize << window_bits) {
            curr = GA::from(curr + increment);
            let curr_fixed =
                FixedEccPoint::from_g1(&curr, P.x.truncation.limbs.len(), P.x.truncation.limb_bits);
            let curr_assigned = curr_fixed.assign(chip, ctx)?;
            cache_vec.push(curr_assigned);
        }
        increment = GA::from(curr + increment);
        cached_points.push(cache_vec);
    }

    let mut bits = Vec::with_capacity(rounded_bitlen);
    for x in scalar {
        let mut new_bits = chip.range().num_to_bits(ctx, x, max_bits)?;
        bits.append(&mut new_bits);
    }
    let mut rounded_bits = bits;
    let zero_cell = chip.range().gate().load_zero(ctx)?;
    for idx in 0..(rounded_bitlen - total_bits) {
        rounded_bits.push(zero_cell.clone());
    }

    // is_started[idx] holds whether there is a 1 in bits with index at least (rounded_bitlen - idx)
    let mut is_started = Vec::with_capacity(rounded_bitlen);
    is_started.push(zero_cell.clone());
    for idx in 1..rounded_bitlen {
        let or = chip.range().gate().or(
            ctx,
            &Existing(&is_started[idx - 1]),
            &Existing(&rounded_bits[rounded_bitlen - idx]),
        )?;
        is_started.push(or.clone());
    }

    // is_zero_window[idx] is 0/1 depending on whether bits [rounded_bitlen - window_bits * (idx + 1), rounded_bitlen - window_bits * idx) are all 0
    let mut is_zero_window = Vec::with_capacity(num_windows);
    let mut ones_vec = Vec::with_capacity(window_bits);
    for idx in 0..window_bits {
        ones_vec.push(Constant(F::from(1)));
    }
    for idx in 0..num_windows {
        let temp_bits = rounded_bits
            [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
            .iter()
            .map(|x| Existing(&x))
            .collect();
        let bit_sum = chip.range().gate().inner_product(ctx, &ones_vec, &temp_bits)?;
        let is_zero = chip.range().is_zero(ctx, &bit_sum.2)?;
        is_zero_window.push(is_zero.clone());
    }

    // if all the starting window bits are 0, get start_point = P
    let mut curr_point = select_from_bits(
        chip,
        ctx,
        &cached_points[num_windows - 1],
        &rounded_bits[rounded_bitlen - window_bits..rounded_bitlen].to_vec(),
    )?;
    for idx in 1..num_windows {
        let add_point = select_from_bits(
            chip,
            ctx,
            &cached_points[num_windows - idx - 1],
            &rounded_bits
                [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                .to_vec(),
        )?;
        let sum = ecc_add_unequal(chip, ctx, &curr_point, &add_point, false)?;
        let zero_sum = select(chip, ctx, &curr_point, &sum, &is_zero_window[idx])?;
        curr_point = select(chip, ctx, &zero_sum, &add_point, &is_started[window_bits * idx])?;
    }
    Ok(curr_point.clone())
}
