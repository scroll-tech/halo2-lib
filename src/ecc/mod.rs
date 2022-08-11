#![allow(non_snake_case)]
use std::marker::PhantomData;

use ff::PrimeField;
use group::{Curve, Group};
use halo2_proofs::{
    arithmetic::{BaseExt, CurveAffine, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    pairing::bn256::{G1Affine, G1},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};
use rand_core::OsRng;

use crate::bigint::{
    add_no_carry, inner_product, mul_no_carry, scalar_mul_no_carry, select, sub_no_carry,
    CRTInteger, FixedCRTInteger, OverflowInteger, big_less_than,
};
use crate::fields::{
    fp::{FpChip, FpConfig},
    fp_overflow::FpOverflowChip,
    Selectable,
};
use crate::fields::{FieldChip, PrimeFieldChip};
use crate::gates::{
    GateInstructions,
    RangeInstructions,
    QuantumCell::{self, Constant, Existing, Witness}
};
use crate::utils::{
    bigint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint, fe_to_biguint, modulus,
};

pub mod fixed;
use fixed::{fixed_base_scalar_multiply, FixedEccPoint};

// EccPoint and EccChip take in a generic `FieldChip` to implement generic elliptic curve operations on arbitrary field extensions (provided chip exists) for short Weierstrass curves (currently further assuming a4 = 0 for optimization purposes)
#[derive(Debug)]
pub struct EccPoint<F: FieldExt, FieldPoint: Clone> {
    pub x: FieldPoint,
    pub y: FieldPoint,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, FieldPoint: Clone> Clone for EccPoint<F, FieldPoint> {
    fn clone(&self) -> Self {
        Self { x: self.x.clone(), y: self.y.clone(), _marker: PhantomData }
    }
}

impl<F: FieldExt, FieldPoint: Clone> EccPoint<F, FieldPoint> {
    pub fn construct(x: FieldPoint, y: FieldPoint) -> Self {
        Self { x, y, _marker: PhantomData }
    }
}

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the field F_p
//      assume x_1 != x_2
//  Find ecc addition P + Q = (x_3, y_3)
// By solving:
//  lambda = (y_2-y_1)/(x_2-x_1) using constraint
//  lambda * (x_2 - x_1) = y_2 - y_1
//  x_3 = lambda^2 - x_1 - x_2 (mod p)
//  y_3 = lambda (x_1 - x_3) - y_1 mod p
pub fn ecc_add_unequal<F: FieldExt, FC: FieldChip<F>>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, FC::FieldPoint>,
    Q: &EccPoint<F, FC::FieldPoint>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
    let dx = chip.sub_no_carry(layouter, &Q.x, &P.x)?;
    let dy = chip.sub_no_carry(layouter, &Q.y, &P.y)?;
    let lambda = chip.divide(layouter, &dy, &dx)?;

    //  x_3 = lambda^2 - x_1 - x_2 (mod p)
    let lambda_sq = chip.mul_no_carry(layouter, &lambda, &lambda)?;
    let lambda_sq_minus_px = chip.sub_no_carry(layouter, &lambda_sq, &P.x)?;
    let x_3_no_carry = chip.sub_no_carry(layouter, &lambda_sq_minus_px, &Q.x)?;
    let x_3 = chip.carry_mod(layouter, &x_3_no_carry)?;

    //  y_3 = lambda (x_1 - x_3) - y_1 mod p
    let dx_13 = chip.sub_no_carry(layouter, &P.x, &x_3)?;
    let lambda_dx_13 = chip.mul_no_carry(layouter, &lambda, &dx_13)?;
    let y_3_no_carry = chip.sub_no_carry(layouter, &lambda_dx_13, &P.y)?;
    let y_3 = chip.carry_mod(layouter, &y_3_no_carry)?;

    Ok(EccPoint::construct(x_3, y_3))
}

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the field F_p
//  Find ecc subtraction P - Q = (x_3, y_3)
//  Assumes that P !=Q and Q != (P - Q)
pub fn ecc_sub_unequal<F: FieldExt, FC: FieldChip<F>>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, FC::FieldPoint>,
    Q: &EccPoint<F, FC::FieldPoint>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
    let dx = chip.sub_no_carry(layouter, &Q.x, &P.x)?;
    let dy = chip.add_no_carry(layouter, &Q.y, &P.y)?;

    let lambda = chip.neg_divide(layouter, &dy, &dx)?;

    // (x_2 - x_1) * lambda + y_2 + y_1 = 0 (mod p)
    let lambda_dx = chip.mul_no_carry(layouter, &lambda, &dx)?;
    let lambda_dx_plus_dy = chip.add_no_carry(layouter, &lambda_dx, &dy)?;
    chip.check_carry_mod_to_zero(layouter, &lambda_dx_plus_dy)?;

    //  x_3 = lambda^2 - x_1 - x_2 (mod p)
    let lambda_sq = chip.mul_no_carry(layouter, &lambda, &lambda)?;
    let lambda_sq_minus_px = chip.sub_no_carry(layouter, &lambda_sq, &P.x)?;
    let x_3_no_carry = chip.sub_no_carry(layouter, &lambda_sq_minus_px, &Q.x)?;
    let x_3 = chip.carry_mod(layouter, &x_3_no_carry)?;

    //  y_3 = lambda (x_1 - x_3) - y_1 mod p
    let dx_13 = chip.sub_no_carry(layouter, &P.x, &x_3)?;
    let lambda_dx_13 = chip.mul_no_carry(layouter, &lambda, &dx_13)?;
    let y_3_no_carry = chip.sub_no_carry(layouter, &lambda_dx_13, &P.y)?;
    let y_3 = chip.carry_mod(layouter, &y_3_no_carry)?;

    Ok(EccPoint::construct(x_3, y_3))
}

// Implements:
// computing 2P on elliptic curve E for P = (x, y)
// formula from https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
// assume y != 0 (otherwise 2P = O)

// lamb =  3x^2 / (2 y) % p
// x_3 = out[0] = lambda^2 - 2 x % p
// y_3 = out[1] = lambda (x - x_3) - y % p

// we precompute lambda and constrain (2y) * lambda = 3 x^2 (mod p)
// then we compute x_3 = lambda^2 - 2 x (mod p)
//                 y_3 = lambda (x - x_3) - y (mod p)
pub fn ecc_double<F: FieldExt, FC: FieldChip<F>>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, FC::FieldPoint>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
    // removed optimization that computes `2 * lambda` while assigning witness to `lambda` simultaneously, in favor of readability. The difference is just copying `lambda` once
    let two_y = chip.scalar_mul_no_carry(layouter, &P.y, F::from(2))?;
    let three_x = chip.scalar_mul_no_carry(layouter, &P.x, F::from(3))?;
    let three_x_sq = chip.mul_no_carry(layouter, &three_x, &P.x)?;
    let lambda = chip.divide(layouter, &three_x_sq, &two_y)?;

    // x_3 = lambda^2 - 2 x % p
    let lambda_sq = chip.mul_no_carry(layouter, &lambda, &lambda)?;
    let two_x = chip.scalar_mul_no_carry(layouter, &P.x, F::from(2))?;
    let x_3_no_carry = chip.sub_no_carry(layouter, &lambda_sq, &two_x)?;
    let x_3 = chip.carry_mod(layouter, &x_3_no_carry)?;

    // y_3 = lambda (x - x_3) - y % p
    let dx = chip.sub_no_carry(layouter, &P.x, &x_3)?;
    let lambda_dx = chip.mul_no_carry(layouter, &lambda, &dx)?;
    let y_3_no_carry = chip.sub_no_carry(layouter, &lambda_dx, &P.y)?;
    let y_3 = chip.carry_mod(layouter, &y_3_no_carry)?;

    Ok(EccPoint::construct(x_3, y_3))
}

pub fn select<F: FieldExt, FC>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, FC::FieldPoint>,
    Q: &EccPoint<F, FC::FieldPoint>,
    sel: &AssignedCell<F, F>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let Rx = chip.select(layouter, &P.x, &Q.x, sel)?;
    let Ry = chip.select(layouter, &P.y, &Q.y, sel)?;
    Ok(EccPoint::construct(Rx, Ry))
}

// takes the dot product of points with sel, where each is intepreted as
// a _vector_
pub fn inner_product<F: FieldExt, FC>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    points: &Vec<EccPoint<F, FC::FieldPoint>>,
    coeffs: &Vec<AssignedCell<F, F>>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let length = coeffs.len();
    assert_eq!(length, points.len());

    let x_coords = points.iter().map(|P| P.x.clone()).collect();
    let y_coords = points.iter().map(|P| P.y.clone()).collect();
    let Rx = chip.inner_product(layouter, &x_coords, coeffs)?;
    let Ry = chip.inner_product(layouter, &y_coords, coeffs)?;
    Ok(EccPoint::construct(Rx, Ry))
}

// sel is little-endian binary
pub fn select_from_bits<F: FieldExt, FC>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    points: &Vec<EccPoint<F, FC::FieldPoint>>,
    sel: &Vec<AssignedCell<F, F>>,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    let w = sel.len();
    let num_points = points.len();
    assert_eq!(1 << w, num_points);
    let sel_quantum = sel.iter().map(|x| Existing(x)).collect();
    let coeffs = chip.range().gate().bits_to_indicator(layouter, &sel_quantum)?;
    inner_product(chip, layouter, points, &coeffs)
}

// computes [scalar] * P on y^2 = x^3 + b
// - `scalar` is represented as a reference array of `AssignedCell`s
// - `scalar = sum_i scalar_i * 2^{max_bits * i}`
// - an array of length > 1 is needed when `scalar` exceeds the modulus of scalar field `F`
// assumes:
// - `scalar_i < 2^{max_bits} for all i` (constrained by num_to_bits)
// - `max_bits <= modulus::<F>.bits()`
//   * P has order given by the scalar field modulus
pub fn scalar_multiply<F: FieldExt, FC>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, FC::FieldPoint>,
    scalar: &Vec<AssignedCell<F, F>>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
{
    assert!(scalar.len() > 0);
    assert!((max_bits as u64) <= modulus::<F>().bits());

    let total_bits = max_bits * scalar.len();
    let num_windows = (total_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    let mut bits = Vec::with_capacity(rounded_bitlen);
    for x in scalar {
        let mut new_bits = chip.range().num_to_bits(layouter, x, max_bits)?;
        bits.append(&mut new_bits);
    }
    let mut rounded_bits = bits;
    let zero_cell = layouter.assign_region(
        || "constant 0",
        |mut region| {
            let zero_cells = vec![Constant(F::from(0))];
            let (zero_cells_assigned, _) =
                chip.range().gate().assign_region(zero_cells, 0, &mut region)?;
            Ok(zero_cells_assigned[0].clone())
        },
    )?;
    for idx in 0..(rounded_bitlen - total_bits) {
        rounded_bits.push(zero_cell.clone());
    }

    // is_started[idx] holds whether there is a 1 in bits with index at least (rounded_bitlen - idx)
    let mut is_started = Vec::with_capacity(rounded_bitlen);
    for idx in 0..(rounded_bitlen - total_bits) {
        is_started.push(zero_cell.clone());
    }
    is_started.push(zero_cell.clone());
    for idx in 1..total_bits {
        let or = chip.range().gate().or(
            layouter,
            &Existing(&is_started[rounded_bitlen - total_bits + idx - 1]),
            &Existing(&rounded_bits[total_bits - idx]),
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
        let bit_sum = chip.range().gate().inner_product(layouter, &ones_vec, &temp_bits)?;
        let is_zero = chip.range().is_zero(layouter, &bit_sum.2)?;
        is_zero_window.push(is_zero.clone());
    }

    // cached_points[idx] stores idx * P, with cached_points[0] = P
    let cache_size = 1usize << window_bits;
    let mut cached_points = Vec::with_capacity(cache_size);
    cached_points.push(P.clone());
    cached_points.push(P.clone());
    for idx in 2..cache_size {
        if idx == 2 {
            let double = ecc_double(chip, layouter, P /*, b*/)?;
            cached_points.push(double.clone());
        } else {
            let new_point = ecc_add_unequal(chip, layouter, &cached_points[idx - 1], &P)?;
            cached_points.push(new_point.clone());
        }
    }

    // if all the starting window bits are 0, get start_point = P
    let mut curr_point = select_from_bits(
        chip,
        layouter,
        &cached_points,
        &rounded_bits[rounded_bitlen - window_bits..rounded_bitlen].to_vec(),
    )?;

    for idx in 1..num_windows {
        let mut mult_point = curr_point.clone();
        for double_idx in 0..window_bits {
            mult_point = ecc_double(chip, layouter, &mult_point)?;
        }
        let add_point = select_from_bits(
            chip,
            layouter,
            &cached_points,
            &rounded_bits
                [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                .to_vec(),
        )?;
        let mult_and_add = ecc_add_unequal(chip, layouter, &mult_point, &add_point)?;
        let is_started_point =
            select(chip, layouter, &mult_point, &mult_and_add, &is_zero_window[idx])?;

        curr_point =
            select(chip, layouter, &is_started_point, &add_point, &is_started[window_bits * idx])?;
    }
    Ok(curr_point.clone())
}

// need to supply an extra generic `GA` implementing `CurveAffine` trait in order to generate random witness points on the curve in question
// Input:
// - `scalars` is vector of same length as `P`
// - each `scalar` in `scalars` satisfies same assumptions as in `scalar_multiply` above
pub fn multi_scalar_multiply<F: FieldExt, FC, GA>(
    chip: &mut FC,
    layouter: &mut impl Layouter<F>,
    P: &Vec<EccPoint<F, FC::FieldPoint>>,
    scalars: &Vec<Vec<AssignedCell<F, F>>>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
    GA: CurveAffine<Base = FC::FieldType>,
{
    let k = P.len();
    assert_eq!(k, scalars.len());
    assert!(k > 0);
    assert!(scalars[0].len() > 0);
    assert!((max_bits as u64) <= modulus::<F>().bits());

    let total_bits = max_bits * scalars[0].len();
    let num_windows = (total_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    let zero_cell = layouter.assign_region(
        || "constant 0",
        |mut region| {
            let zero_cells = vec![Constant(F::from(0))];
            let (zero_cells_assigned, _) =
                chip.range().gate().assign_region(zero_cells, 0, &mut region)?;
            Ok(zero_cells_assigned[0].clone())
        },
    )?;
    let mut rounded_bits_vec = Vec::with_capacity(k);
    for scalar in scalars {
        let mut bits = Vec::with_capacity(rounded_bitlen);
        for x in scalar {
            let mut new_bits = chip.range().num_to_bits(layouter, x, max_bits)?;
            bits.append(&mut new_bits);
        }
        let mut rounded_bits = bits;
        for _i in 0..(rounded_bitlen - total_bits) {
            rounded_bits.push(zero_cell.clone());
        }
        rounded_bits_vec.push(rounded_bits);
    }

    let mut is_zero_window_vec = Vec::with_capacity(k);
    let mut ones_vec = Vec::with_capacity(window_bits);
    for idx in 0..window_bits {
        ones_vec.push(Constant(F::from(1)));
    }
    for idx in 0..k {
        let mut is_zero_window = Vec::with_capacity(num_windows);
        for window_idx in 0..num_windows {
            let temp_bits = rounded_bits_vec[idx][rounded_bitlen - window_bits * (window_idx + 1)
                ..rounded_bitlen - window_bits * window_idx]
                .iter()
                .map(|x| Existing(&x))
                .collect();
            let bit_sum = chip.range().gate().inner_product(layouter, &ones_vec, &temp_bits)?;
            let is_zero = chip.range().is_zero(layouter, &bit_sum.2)?;
            is_zero_window.push(is_zero.clone());
        }
        is_zero_window_vec.push(is_zero_window);
    }
    let mut rng = rand::thread_rng();
    let base_point: GA = GA::CurveExt::random(&mut rng).to_affine();
    let base_point_coord = base_point.coordinates().unwrap();
    let pt_x = FC::fe_to_witness(&Some(*base_point_coord.x()));
    let pt_y = FC::fe_to_witness(&Some(*base_point_coord.y()));
    let base = {
        let x_overflow = chip.load_private(layouter, pt_x)?;
        let y_overflow = chip.load_private(layouter, pt_y)?;
        EccPoint::construct(x_overflow, y_overflow)
    };

    // contains random base points [A, ..., 2^{w + k - 1} * A]
    let mut rand_start_vec = Vec::with_capacity(k);
    rand_start_vec.push(base.clone());
    for idx in 1..(k + window_bits) {
        let base_mult = ecc_double(chip, layouter, &rand_start_vec[idx - 1])?;
        rand_start_vec.push(base_mult.clone());
    }

    // contains (1 - 2^w) * [A, ..., 2^(k - 1) * A]
    let mut neg_mult_rand_start_vec = Vec::with_capacity(k);
    for idx in 0..k {
        let diff = ecc_sub_unequal(
            chip,
            layouter,
            &rand_start_vec[idx],
            &rand_start_vec[idx + window_bits],
        )?;
        neg_mult_rand_start_vec.push(diff.clone());
    }

    let cache_size = 1usize << window_bits;
    let mut cached_points_vec = Vec::with_capacity(k);
    for idx in 0..k {
        let mut cached_points = Vec::with_capacity(cache_size);
        cached_points.push(neg_mult_rand_start_vec[idx].clone());
        for cache_idx in 0..(cache_size - 1) {
            let new_point = ecc_add_unequal(chip, layouter, &cached_points[cache_idx], &P[idx])?;
            cached_points.push(new_point.clone());
        }
        cached_points_vec.push(cached_points);
    }

    // initialize at (2^{k + 1} - 1) * A
    let start_point = ecc_sub_unequal(chip, layouter, &rand_start_vec[k], &rand_start_vec[0])?;
    let mut curr_point = start_point.clone();

    // compute \sum_i x_i P_i + (2^{k + 1} - 1) * A
    for idx in 0..num_windows {
        for double_idx in 0..window_bits {
            curr_point = ecc_double(chip, layouter, &curr_point)?;
        }
        for base_idx in 0..k {
            let add_point = select_from_bits(
                chip,
                layouter,
                &cached_points_vec[base_idx],
                &rounded_bits_vec[base_idx]
                    [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                    .to_vec(),
            )?;
            curr_point = ecc_add_unequal(chip, layouter, &curr_point, &add_point)?;
        }
    }
    curr_point = ecc_sub_unequal(chip, layouter, &curr_point, &start_point)?;

    Ok(curr_point.clone())
}

// CF is the coordinate field of GA
// SF is the scalar field of GA
pub fn ecdsa_verify_no_pubkey_check<F: FieldExt, CF: PrimeField, SF: PrimeField, GA, const NUM_ADVICE: usize, const NUM_FIXED: usize>(
    base_chip: &mut FpChip<F, NUM_ADVICE, NUM_FIXED, CF>,
    scalar_chip: &mut FpOverflowChip<F, NUM_ADVICE, NUM_FIXED, SF>,
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    pubkey: &EccPoint<F, <FpChip<F, NUM_ADVICE, NUM_FIXED, CF> as FieldChip<F>>::FieldPoint>,
    r: &OverflowInteger<F>,
    s: &OverflowInteger<F>,
    msghash: &OverflowInteger<F>,
    b: F,
    var_window_bits: usize,
    fixed_window_bits: usize,
) -> Result<AssignedCell<F, F>, Error>
where
    GA: CurveAffine<Base = CF, ScalarExt = SF>,
{
    let G = FixedEccPoint::from_g1(
	&GA::generator(),
	pubkey.x.truncation.limbs.len(),
	pubkey.x.truncation.limb_bits
    );
    let n = scalar_chip.load_constant(
	layouter,
	BigInt::from(scalar_chip.p.clone())
    )?;

    println!("0");
    
    // check r,s are in [1, n - 1]
    let r_is_zero = scalar_chip.is_zero(layouter, &r)?;
    let s_is_zero = scalar_chip.is_zero(layouter, &s)?;

    println!("1");
    let r_valid = range.gate().not(layouter, &Existing(&r_is_zero))?;
    let s_valid = range.gate().not(layouter, &Existing(&s_is_zero))?;

    println!("a");
    
    // compute u1 = m s^{-1} mod n and u2 = r s^{-1} mod n
    // TODO: maybe the big_less_than is optional?
    let u1 = scalar_chip.divide(layouter, &msghash, &s)?;
    let u2 = scalar_chip.divide(layouter, &r, &s)?;
    let u1_small = big_less_than::assign(range, layouter, &u1, &n)?;
    let u2_small = big_less_than::assign(range, layouter, &u2, &n)?;

    println!("b");
    
    // compute u1 * G and u2 * pubkey
    let u1_mul = fixed_base_scalar_multiply(base_chip, layouter, &G, &u1.limbs, b, u1.limb_bits, fixed_window_bits)?;
    let u2_mul = scalar_multiply(base_chip, layouter, pubkey, &u2.limbs, b, u2.limb_bits, var_window_bits)?;

    println!("c");
    
    // check u1 * G and u2 * pubkey are not negatives and not equal
    //     TODO: Technically they could be equal for a valid signature, but this happens with vanishing probability
    //           for an ECDSA signature constructed in a standard way
    // coordinates of u1_mul and u2_mul are in proper bigint form, but are not constrained to [0, n)
    let u1_u2_x_eq = base_chip.is_equal(layouter, &u1_mul.x, &u2_mul.x)?;
    let u1_u2_not_neg = range.gate().not(layouter, &Existing(&u1_u2_x_eq))?;

    println!("d");
    
    // compute (x1, y1) = u1 * G + u2 * pubkey and check r == x1 mod n
    let sum = ecc_add_unequal(base_chip, layouter, &u1_mul, &u2_mul)?;
    let r_crt = scalar_chip.to_crt(layouter, r)?;
    let equal_check = base_chip.is_equal(layouter, &sum.x, &r_crt)?;

    println!("e");
    
    // check (r in [1, n - 1]) and (s in [1, n - 1]) and (u1_mul != - u2_mul) and (r == x1 mod n)
    let res1 = range.gate().and(layouter, &Existing(&r_valid), &Existing(&s_valid))?;
    let res2 = range.gate().and(layouter, &Existing(&res1), &Existing(&u1_small))?;
    let res3 = range.gate().and(layouter, &Existing(&res2), &Existing(&u2_small))?;
    let res4 = range.gate().and(layouter, &Existing(&res3), &Existing(&u1_u2_not_neg))?;
    let res5 = range.gate().and(layouter, &Existing(&res4), &Existing(&equal_check))?;
    Ok(res5)
}

pub struct EccChip<'a, F: FieldExt, FC: FieldChip<F>> {
    pub field_chip: &'a mut FC,
    _marker: PhantomData<F>,
}

impl<'a, F: FieldExt, FC: FieldChip<F>> EccChip<'a, F, FC> {
    pub fn construct(field_chip: &'a mut FC) -> Self {
        Self { field_chip, _marker: PhantomData }
    }

    pub fn load_private(
        &mut self,
        layouter: &mut impl Layouter<F>,
        point: (Option<FC::FieldType>, Option<FC::FieldType>),
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
        let (x, y) = (FC::fe_to_witness(&point.0), FC::fe_to_witness(&point.1));

        let x_assigned = self.field_chip.load_private(layouter, x)?;
        let y_assigned = self.field_chip.load_private(layouter, y)?;

        Ok(EccPoint::construct(x_assigned, y_assigned))
    }

    pub fn negate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F, FC::FieldPoint>,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
        Ok(EccPoint::construct(
            P.x.clone(),
            self.field_chip.negate(layouter, &P.y).expect("negating field point should not fail"),
        ))
    }

    pub fn add_unequal(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F, FC::FieldPoint>,
        Q: &EccPoint<F, FC::FieldPoint>,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
        ecc_add_unequal(self.field_chip, layouter, P, Q)
    }

    pub fn double(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F, FC::FieldPoint>,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
        ecc_double(self.field_chip, layouter, P)
    }
}

impl<F: FieldExt, FC: FieldChip<F>> EccChip<'_, F, FC>
where
    FC: Selectable<F, Point = FC::FieldPoint>,
{
    pub fn scalar_mult(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F, FC::FieldPoint>,
        scalar: &Vec<AssignedCell<F, F>>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error> {
        scalar_multiply(
	    self.field_chip,
	    layouter,
	    P,
	    scalar,
	    b,
	    max_bits,
	    window_bits
	)
    }

    pub fn multi_scalar_mult<GA>(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &Vec<EccPoint<F, FC::FieldPoint>>,
        scalars: &Vec<Vec<AssignedCell<F, F>>>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error>
    where
        GA: CurveAffine<Base = FC::FieldType>,
    {
        multi_scalar_multiply::<F, FC, GA>(
            self.field_chip,
            layouter,
            P,
            scalars,
            b,
            max_bits,
            window_bits,
        )
    }
}

impl<F: FieldExt, FC: PrimeFieldChip<F>> EccChip<'_, F, FC> {
    pub fn fixed_base_scalar_mult<GA>(
        &mut self,
        layouter: &mut impl Layouter<F>,
        P: &FixedEccPoint<F, GA>,
        scalar: &Vec<AssignedCell<F, F>>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F, FC::FieldPoint>, Error>
    where
        GA: CurveAffine,
        GA::Base: PrimeField,
        FC: PrimeFieldChip<F, FieldType = GA::Base, FieldPoint = CRTInteger<F>>
            + Selectable<F, Point = FC::FieldPoint>,
    {
        fixed_base_scalar_multiply(self.field_chip, layouter, P, scalar, b, max_bits, window_bits)
    }
}

#[cfg(test)]
pub mod tests;
