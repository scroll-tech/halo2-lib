#![allow(non_snake_case)]
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    pairing::bn256::{Fq as Fp, Fr, G1Affine},
    pairing::group::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use rand_core::OsRng;

use crate::fields::fp_crt::{FpChip, FpConfig};
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::gates::{qap_gate, range};
use crate::utils::{
    bigint_to_fe, bigint_to_fp, decompose_bigint_option, decompose_biguint, fe_to_bigint,
    fp_to_bigint, modulus as native_modulus,
};
use crate::{
    bigint::{
        add_no_carry, inner_product, mul_no_carry, scalar_mul_no_carry, select, sub_no_carry,
        CRTInteger, FixedCRTInteger, OverflowInteger,
    },
    utils::fe_to_biguint,
};

// committing to prime field F_p with
// p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
//   = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
use lazy_static::lazy_static;
lazy_static! {
    static ref FP_MODULUS: BigUint = native_modulus::<Fp>();
}

#[derive(Clone, Debug)]
pub struct EccPoint<F: FieldExt> {
    pub x: CRTInteger<F>,
    pub y: CRTInteger<F>,
}

impl<F: FieldExt> EccPoint<F> {
    pub fn construct(x: CRTInteger<F>, y: CRTInteger<F>) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Debug)]
pub struct FixedEccPoint<F: FieldExt> {
    x: FixedCRTInteger<F>,
    y: FixedCRTInteger<F>,
}

impl<F: FieldExt> FixedEccPoint<F> {
    pub fn construct(x: FixedCRTInteger<F>, y: FixedCRTInteger<F>) -> Self {
        Self { x, y }
    }

    pub fn from_g1(P: &G1Affine, num_limbs: usize, limb_bits: usize) -> Self {
        let x_pt = FixedCRTInteger::from_native(fp_to_bigint(&P.x), num_limbs, limb_bits);
        let y_pt = FixedCRTInteger::from_native(fp_to_bigint(&P.y), num_limbs, limb_bits);
        Self { x: x_pt, y: y_pt }
    }

    pub fn assign(
        &self,
        chip: &FpChip<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<EccPoint<F>, Error> {
        let assigned_x = self.x.assign(&chip.config.range.qap_config, layouter)?;
        let assigned_y = self.y.assign(&chip.config.range.qap_config, layouter)?;
        let point = EccPoint::construct(assigned_x, assigned_y);
        Ok(point)
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
pub fn point_add_unequal<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.truncation.limbs.len();
    let n = P.x.truncation.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.truncation.limbs.len());
    assert_eq!(k, Q.x.truncation.limbs.len());
    assert_eq!(k, Q.y.truncation.limbs.len());
    assert_eq!(n, P.y.truncation.limb_bits);
    assert_eq!(n, Q.x.truncation.limb_bits);
    assert_eq!(n, Q.y.truncation.limb_bits);

    let x_1 = P.x.value.clone();
    let y_1 = P.y.value.clone();
    let x_2 = Q.x.value.clone();
    let y_2 = Q.y.value.clone();

    let lambda = if let (Some(x_1), Some(y_1), Some(x_2), Some(y_2)) = (x_1, y_1, x_2, y_2) {
        let x_1 = bigint_to_fp(x_1);
        let y_1 = bigint_to_fp(y_1);
        let x_2 = bigint_to_fp(x_2);
        let y_2 = bigint_to_fp(y_2);

        assert_ne!(x_1, x_2);
        let lambda = (y_2 - y_1) * ((x_2 - x_1).invert().unwrap());
        Some(fp_to_bigint(&lambda))
    } else {
        None
    };

    let dx = chip.sub_no_carry(layouter, &Q.x, &P.x)?;
    let dy = chip.sub_no_carry(layouter, &Q.y, &P.y)?;

    let lambda = chip.load_private(layouter.namespace(|| "load lambda"), lambda, k)?;
    chip.range_check(layouter, &lambda)?;

    // constrain lambda * dx - dy
    let lambda_dx = chip.mul_no_carry(layouter, &lambda, &dx)?;
    let lambda_constraint = chip.sub_no_carry(layouter, &lambda_dx, &dy)?;
    chip.check_carry_mod_to_zero(layouter, &lambda_constraint)?;

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
//  Find ecc addition P - Q = (x_3, y_3)
//  Assumes that P !=Q and Q != (P - Q)
pub fn point_sub_unequal<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.truncation.limbs.len();
    let n = P.x.truncation.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.truncation.limbs.len());
    assert_eq!(k, Q.x.truncation.limbs.len());
    assert_eq!(k, Q.y.truncation.limbs.len());
    assert_eq!(n, P.y.truncation.limb_bits);
    assert_eq!(n, Q.x.truncation.limb_bits);
    assert_eq!(n, Q.y.truncation.limb_bits);

    let x_1 = P.x.value.clone();
    let y_1 = P.y.value.clone();
    let x_2 = Q.x.value.clone();
    let y_2 = Q.y.value.clone();

    let lambda = if let (Some(x_1), Some(y_1), Some(x_2), Some(y_2)) = (x_1, y_1, x_2, y_2) {
        let x_1 = bigint_to_fp(x_1);
        let y_1 = bigint_to_fp(y_1);
        let x_2 = bigint_to_fp(x_2);
        let y_2 = bigint_to_fp(y_2);

        assert_ne!(x_1, x_2);
        let lambda = (-y_2 - y_1) * (x_2 - x_1).invert().unwrap();
        Some(fp_to_bigint(&lambda))
    } else {
        None
    };

    let dx = chip.sub_no_carry(layouter, &Q.x, &P.x)?;
    let dy = chip.add_no_carry(layouter, &Q.y, &P.y)?;

    let lambda = chip.load_private(layouter.namespace(|| "load lambda"), lambda, k)?;
    chip.range_check(layouter, &lambda)?;

    // (x_2 - x_1) * lambda + y_2 + y_1 (mod p)
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
pub fn point_double<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.truncation.limbs.len();
    let n = P.x.truncation.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.truncation.limbs.len());
    assert_eq!(n, P.y.truncation.limb_bits);

    let x = P.x.value.clone();
    let y = P.y.value.clone();
    let lambda = if let (Some(x), Some(y)) = (x, y) {
        assert_ne!(y, BigInt::zero());
        let x = bigint_to_fp(x);
        let y = bigint_to_fp(y);
        let lambda = Fp::from(3) * x * x * (Fp::from(2) * y).invert().unwrap();
        Some(fp_to_bigint(&lambda))
    } else {
        None
    };

    let lambda_limbs = decompose_bigint_option::<F>(&lambda, k, n);
    // assign lambda and compute 2 * lambda simultaneously
    let (lambda_trunc, two_lambda_trunc) = layouter.assign_region(
        || "2 * lambda",
        |mut region| {
            let mut offset = 0;
            let mut lambda_cells = Vec::with_capacity(k);
            let mut two_lambda_limbs = Vec::with_capacity(k);
            for limb in lambda_limbs.iter() {
                let cells = chip.config.range.qap_config.assign_region(
                    vec![
                        Constant(F::from(0)),
                        Constant(F::from(2)),
                        Witness(limb.clone()),
                        Witness(limb.map(|a| F::from(2) * a)),
                    ],
                    offset,
                    &mut region,
                )?;
                lambda_cells.push(cells[2].clone());
                two_lambda_limbs.push(cells[3].clone());
                offset = offset + 4;
            }
            Ok((
                OverflowInteger::construct(lambda_cells, BigUint::from(1u64) << n, n),
                OverflowInteger::construct(two_lambda_limbs, BigUint::from(1u64) << (n + 1), n),
            ))
        },
    )?;
    let lambda_native = OverflowInteger::evaluate(
        &chip.config.range.qap_config,
        layouter,
        &lambda_trunc.limbs,
        n,
    )?;
    let lambda = CRTInteger::construct(
        lambda_trunc,
        lambda_native,
        lambda.clone(),
        BigUint::from(1u64) << chip.config.p.bits(),
    );
    let two_lambda_native =
        chip.config
            .range
            .qap_config
            .mul_constant(layouter, &lambda.native, F::from(2))?;
    let two_lambda = CRTInteger::construct(
        two_lambda_trunc,
        two_lambda_native,
        lambda.value.as_ref().map(|a| BigInt::from(2u64) * a),
        BigUint::from(2u64) << chip.config.p.bits(),
    );

    // range check lambda
    chip.range_check(layouter, &lambda)?;

    // constrain lambda by 2 y * lambda - 3 x^2 = 0 mod p
    let two_y_lambda = chip.mul_no_carry(layouter, &two_lambda, &P.y)?;
    let three_x = chip.scalar_mul_no_carry(layouter, &P.x, F::from(3))?;
    let three_x_sq = chip.mul_no_carry(layouter, &three_x, &P.x)?;

    // 2 y * lambda - 3 x^2
    let lambda_constraint = chip.sub_no_carry(layouter, &two_y_lambda, &three_x_sq)?;
    chip.check_carry_mod_to_zero(layouter, &lambda_constraint)?;

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

pub fn select<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
    sel: &AssignedCell<F, F>,
) -> Result<EccPoint<F>, Error> {
    let Rx = select::crt(&range.qap_config, layouter, &P.x, &Q.x, sel)?;
    let Ry = select::crt(&range.qap_config, layouter, &P.y, &Q.y, sel)?;
    Ok(EccPoint::<F>::construct(Rx, Ry))
}

// takes the dot product of points with sel, where each is intepreted as
// a _vector_
pub fn inner_product<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    points: &Vec<EccPoint<F>>,
    coeffs: &Vec<AssignedCell<F, F>>,
) -> Result<EccPoint<F>, Error> {
    let length = coeffs.len();
    assert_eq!(length, points.len());

    let x_coords = points.iter().map(|P| P.x.clone()).collect();
    let y_coords = points.iter().map(|P| P.y.clone()).collect();
    let Rx = inner_product::crt(&range.qap_config, layouter, &x_coords, coeffs)?;
    let Ry = inner_product::crt(&range.qap_config, layouter, &y_coords, coeffs)?;
    Ok(EccPoint::<F>::construct(Rx, Ry))
}

// sel is little-endian binary
pub fn select_from_bits<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    points: &Vec<EccPoint<F>>,
    sel: &Vec<AssignedCell<F, F>>,
) -> Result<EccPoint<F>, Error> {
    let w = sel.len();
    let num_points = points.len();
    assert_eq!(1 << w, num_points);
    let coeffs = range.qap_config.bits_to_indicator(layouter, sel)?;
    inner_product(range, layouter, points, &coeffs)
}

// computes x * P on y^2 = x^3 + b
// assumes:
//   * 0 < x < scalar field modulus
//   * P has order given by the scalar field modulus
pub fn scalar_multiply<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    x: &AssignedCell<F, F>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F>, Error> {
    let num_windows = (max_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    let mut rounded_bits = Vec::with_capacity(rounded_bitlen);
    let bits = chip.config.range.num_to_bits(layouter, x, max_bits)?;
    for cell in bits.iter() {
        rounded_bits.push(cell.clone());
    }
    let zero_cell = layouter.assign_region(
        || "constant 0",
        |mut region| {
            let zero_cells = vec![Constant(F::from(0))];
            let zero_cells_assigned =
                chip.config
                    .range
                    .qap_config
                    .assign_region(zero_cells, 0, &mut region)?;
            Ok(zero_cells_assigned[0].clone())
        },
    )?;
    for idx in 0..(rounded_bitlen - max_bits) {
        rounded_bits.push(zero_cell.clone());
    }

    // is_started[idx] holds whether there is a 1 in bits with index at least (rounded_bitlen - idx)
    let mut is_started = Vec::with_capacity(rounded_bitlen);
    for idx in 0..(rounded_bitlen - max_bits) {
        is_started.push(zero_cell.clone());
    }
    is_started.push(zero_cell.clone());
    for idx in 1..max_bits {
        let or = chip.config.range.qap_config.or(
            layouter,
            &is_started[rounded_bitlen - max_bits + idx - 1],
            &bits[max_bits - idx],
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
        let bit_sum = chip
            .config
            .range
            .qap_config
            .inner_product(layouter, &ones_vec, &temp_bits)?;
        let is_zero = chip.config.range.is_zero(layouter, &bit_sum.2)?;
        is_zero_window.push(is_zero.clone());
    }

    // cached_points[idx] stores idx * P, with cached_points[0] = P
    let cache_size = 1usize << window_bits;
    let mut cached_points = Vec::with_capacity(cache_size);
    cached_points.push(P.clone());
    cached_points.push(P.clone());
    for idx in 2..cache_size {
        if idx == 2 {
            let double = point_double(chip, layouter, &P /*, b*/)?;
            cached_points.push(double.clone());
        } else {
            let new_point = point_add_unequal(chip, layouter, &cached_points[idx - 1], &P)?;
            cached_points.push(new_point.clone());
        }
    }

    // if all the starting window bits are 0, get start_point = P
    let mut curr_point = select_from_bits(
        &chip.config.range,
        layouter,
        &cached_points,
        &rounded_bits[rounded_bitlen - window_bits..rounded_bitlen].to_vec(),
    )?;

    for idx in 1..num_windows {
        let mut mult_point = curr_point.clone();
        for double_idx in 0..window_bits {
            mult_point = point_double(chip, layouter, &mult_point)?;
        }
        let add_point = select_from_bits(
            &chip.config.range,
            layouter,
            &cached_points,
            &rounded_bits
                [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                .to_vec(),
        )?;
        let mult_and_add = point_add_unequal(chip, layouter, &mult_point, &add_point)?;
        let is_started_point = select(
            &chip.config.range,
            layouter,
            &mult_point,
            &mult_and_add,
            &is_zero_window[idx],
        )?;

        curr_point = select(
            &chip.config.range,
            layouter,
            &is_started_point,
            &add_point,
            &is_started[window_bits * idx],
        )?;
    }
    Ok(curr_point.clone())
}

// computes x * P on y^2 = x^3 + b
// assumes:
//   * 0 < x < scalar field modulus
//   * P has order given by the scalar field modulus
pub fn fixed_base_scalar_multiply<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &FixedEccPoint<F>,
    x: &AssignedCell<F, F>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F>, Error> {
    let num_windows = (max_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    // cached_points[i][j] holds j * 2^(i * w) for j in {0, ..., 2^w - 1}
    let mut cached_points = Vec::with_capacity(num_windows);
    let mut base_pt = G1Affine::default();
    base_pt.x = bigint_to_fp(P.x.value.clone());
    base_pt.y = bigint_to_fp(P.y.value.clone());
    let base_pt_assigned = P.assign(&chip, layouter)?;
    let mut increment = base_pt;
    for i in 0..num_windows {
        let mut cache_vec = Vec::with_capacity(1usize << window_bits);
        let mut curr = increment;

        let increment_fixed = FixedEccPoint::from_g1(
            &increment,
            P.x.truncation.limbs.len(),
            P.x.truncation.limb_bits,
        );
        let increment_assigned = increment_fixed.assign(&chip, layouter)?;
        cache_vec.push(increment_assigned.clone());
        cache_vec.push(increment_assigned.clone());
        for j in 2..(1usize << window_bits) {
            curr = G1Affine::from(curr + increment);
            let curr_fixed =
                FixedEccPoint::from_g1(&curr, P.x.truncation.limbs.len(), P.x.truncation.limb_bits);
            let curr_assigned = curr_fixed.assign(&chip, layouter)?;
            cache_vec.push(curr_assigned);
        }
        increment = G1Affine::from(curr + increment);
        cached_points.push(cache_vec);
    }

    let mut rounded_bits = Vec::with_capacity(rounded_bitlen);
    let bits = chip.config.range.num_to_bits(layouter, x, max_bits)?;
    for cell in bits.iter() {
        rounded_bits.push(cell.clone());
    }
    let zero_cell = layouter.assign_region(
        || "constant 0",
        |mut region| {
            let zero_cells = vec![Constant(F::from(0))];
            let zero_cells_assigned =
                chip.config
                    .range
                    .qap_config
                    .assign_region(zero_cells, 0, &mut region)?;
            Ok(zero_cells_assigned[0].clone())
        },
    )?;
    for idx in 0..(rounded_bitlen - max_bits) {
        rounded_bits.push(zero_cell.clone());
    }

    // is_started[idx] holds whether there is a 1 in bits with index at least (rounded_bitlen - idx)
    let mut is_started = Vec::with_capacity(rounded_bitlen);
    is_started.push(zero_cell.clone());
    for idx in 1..rounded_bitlen {
        let or = chip.config.range.qap_config.or(
            layouter,
            &is_started[idx - 1],
            &rounded_bits[rounded_bitlen - idx],
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
        let bit_sum = chip
            .config
            .range
            .qap_config
            .inner_product(layouter, &ones_vec, &temp_bits)?;
        let is_zero = chip.config.range.is_zero(layouter, &bit_sum.2)?;
        is_zero_window.push(is_zero.clone());
    }

    // if all the starting window bits are 0, get start_point = P
    let mut curr_point = select_from_bits(
        &chip.config.range,
        layouter,
        &cached_points[num_windows - 1],
        &rounded_bits[rounded_bitlen - window_bits..rounded_bitlen].to_vec(),
    )?;
    for idx in 1..num_windows {
        let add_point = select_from_bits(
            &chip.config.range,
            layouter,
            &cached_points[num_windows - idx - 1],
            &rounded_bits
                [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                .to_vec(),
        )?;
        let sum = point_add_unequal(chip, layouter, &curr_point, &add_point)?;
        let zero_sum = select(
            &chip.config.range,
            layouter,
            &curr_point,
            &sum,
            &is_zero_window[idx],
        )?;
        curr_point = select(
            &chip.config.range,
            layouter,
            &zero_sum,
            &add_point,
            &is_started[window_bits * idx],
        )?;
    }
    Ok(curr_point.clone())
}

pub fn multi_scalar_multiply<F: FieldExt>(
    chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    P: &Vec<EccPoint<F>>,
    x: &Vec<AssignedCell<F, F>>,
    b: F,
    max_bits: usize,
    window_bits: usize,
) -> Result<EccPoint<F>, Error> {
    let k = P.len();
    assert_eq!(k, x.len());
    let num_windows = (max_bits + window_bits - 1) / window_bits;
    let rounded_bitlen = num_windows * window_bits;

    let zero_cell = layouter.assign_region(
        || "constant 0",
        |mut region| {
            let zero_cells = vec![Constant(F::from(0))];
            let zero_cells_assigned =
                chip.config
                    .range
                    .qap_config
                    .assign_region(zero_cells, 0, &mut region)?;
            Ok(zero_cells_assigned[0].clone())
        },
    )?;
    let mut rounded_bits_vec = Vec::with_capacity(k);
    for idx in 0..k {
        let mut rounded_bits = Vec::with_capacity(rounded_bitlen);
        let bits = chip.config.range.num_to_bits(layouter, &x[idx], max_bits)?;
        for cell in bits.iter() {
            rounded_bits.push(cell.clone());
        }
        for idx in 0..(rounded_bitlen - max_bits) {
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
            let bit_sum = chip
                .config
                .range
                .qap_config
                .inner_product(layouter, &ones_vec, &temp_bits)?;
            let is_zero = chip.config.range.is_zero(layouter, &bit_sum.2)?;
            is_zero_window.push(is_zero.clone());
        }
        is_zero_window_vec.push(is_zero_window);
    }

    let base_point = G1Affine::random(OsRng);
    let pt_x = fe_to_bigint(&base_point.x);
    let pt_y = fe_to_bigint(&base_point.y);
    let base = {
        let num_limbs = P[0].x.truncation.limbs.len();
        let x_overflow = chip.load_private(
            layouter.namespace(|| "random point x"),
            Some(pt_x),
            num_limbs,
        )?;
        let y_overflow = chip.load_private(
            layouter.namespace(|| "random point y"),
            Some(pt_y),
            num_limbs,
        )?;

        EccPoint::construct(x_overflow, y_overflow)
    };

    // contains random base points [A, ..., 2^{w + k - 1} * A]
    let mut rand_start_vec = Vec::with_capacity(k);
    rand_start_vec.push(base.clone());
    for idx in 1..(k + window_bits) {
        let base_mult = point_double(chip, layouter, &rand_start_vec[idx - 1])?;
        rand_start_vec.push(base_mult.clone());
    }

    // contains (1 - 2^w) * [A, ..., 2^(k - 1) * A]
    let mut neg_mult_rand_start_vec = Vec::with_capacity(k);
    for idx in 0..k {
        let diff = point_sub_unequal(
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
            let new_point = point_add_unequal(chip, layouter, &cached_points[cache_idx], &P[idx])?;
            cached_points.push(new_point.clone());
        }
        cached_points_vec.push(cached_points);
    }

    // initialize at (2^{k + 1} - 1) * A
    let start_point = point_sub_unequal(chip, layouter, &rand_start_vec[k], &rand_start_vec[0])?;
    let mut curr_point = start_point.clone();

    // compute \sum_i x_i P_i + (2^{k + 1} - 1) * A
    for idx in 0..num_windows {
        for double_idx in 0..window_bits {
            curr_point = point_double(chip, layouter, &curr_point)?;
        }
        for base_idx in 0..k {
            let add_point = select_from_bits(
                &chip.config.range,
                layouter,
                &cached_points_vec[base_idx],
                &rounded_bits_vec[base_idx]
                    [rounded_bitlen - window_bits * (idx + 1)..rounded_bitlen - window_bits * idx]
                    .to_vec(),
            )?;
            curr_point = point_add_unequal(chip, layouter, &curr_point, &add_point)?;
        }
    }
    curr_point = point_sub_unequal(chip, layouter, &curr_point, &start_point)?;

    Ok(curr_point.clone())
}

pub struct EccChip<F: FieldExt> {
    fp_chip: FpChip<F>,
}

impl<F: FieldExt> EccChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self {
            fp_chip: FpChip::construct(config),
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
    ) -> FpConfig<F> {
        FpChip::configure(
            meta,
            value,
            constant,
            lookup_bits,
            limb_bits,
            num_limbs,
            FP_MODULUS.clone(),
        )
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.fp_chip.load_lookup_table(layouter)
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        point: Option<(Fp, Fp)>,
    ) -> Result<EccPoint<F>, Error> {
        let (x, y) = if let Some((x, y)) = point {
            (Some(fp_to_bigint(&x)), Some(fp_to_bigint(&y)))
        } else {
            (None, None)
        };

        let x_assigned = self.fp_chip.load_private(
            layouter.namespace(|| "x"),
            x,
            self.fp_chip.config.num_limbs,
        )?;
        let y_assigned = self.fp_chip.load_private(
            layouter.namespace(|| "y"),
            y,
            self.fp_chip.config.num_limbs,
        )?;

        Ok(EccPoint::construct(x_assigned, y_assigned))
    }

    pub fn add_unequal(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
        Q: &EccPoint<F>,
    ) -> Result<EccPoint<F>, Error> {
        point_add_unequal(&self.fp_chip, layouter, P, Q)
    }

    pub fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
    ) -> Result<EccPoint<F>, Error> {
        point_double(&self.fp_chip, layouter, P)
    }

    pub fn scalar_mult(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
        x: &AssignedCell<F, F>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F>, Error> {
        scalar_multiply(&self.fp_chip, layouter, P, x, b, max_bits, window_bits)
    }

    pub fn multi_scalar_mult(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &Vec<EccPoint<F>>,
        x: &Vec<AssignedCell<F, F>>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F>, Error> {
        multi_scalar_multiply(&self.fp_chip, layouter, P, x, b, max_bits, window_bits)
    }

    pub fn fixed_base_scalar_mult(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &FixedEccPoint<F>,
        x: &AssignedCell<F, F>,
        b: F,
        max_bits: usize,
        window_bits: usize,
    ) -> Result<EccPoint<F>, Error> {
        fixed_base_scalar_multiply(&self.fp_chip, layouter, P, x, b, max_bits, window_bits)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::arithmetic::BaseExt;
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::circuit::floor_planner::*;
    use halo2_proofs::pairing::group::ff::PrimeField;
    use halo2_proofs::pairing::group::Group;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq as Fp,
        pairing::bn256::Fr as Fn, plonk::*,
    };
    use num_bigint::{BigInt, RandBigInt};

    #[derive(Default)]
    struct MyCircuit<F> {
        P: Option<G1Affine>,
        Q: Option<G1Affine>,
        P_batch: Vec<Option<G1Affine>>,
        x: Option<F>,
        x_batch: Vec<Option<F>>,
        batch_size: usize,
        _marker: PhantomData<F>,
    }

    const BATCH_SIZE: usize = 4;

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            let batch_size = BATCH_SIZE;
            Self {
                P: None,
                Q: None,
                P_batch: vec![None; batch_size],
                x: Some(F::from(23232)),
                x_batch: vec![None; batch_size],
                batch_size,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            let constant = meta.fixed_column();
            EccChip::configure(meta, value, constant, 22, 88, 3)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EccChip::construct(config.clone());
            chip.load_lookup_table(&mut layouter)?;

            let P_assigned = chip.load_private(
                layouter.namespace(|| "input point P"),
                self.P.map(|P| (P.x, P.y)),
            )?;
            let Q_assigned = chip.load_private(
                layouter.namespace(|| "input point Q"),
                self.Q.map(|P| (P.x, P.y)),
            )?;

            let mut pt = G1Affine::default();
            let mut P_fixed = FixedEccPoint::<F>::from_g1(&pt, 3, 88);
            if let Some(P_point) = &self.P {
                pt = P_point.clone();
                P_fixed = FixedEccPoint::from_g1(&P_point, 3, 88);
            }
            let x_assigned = layouter.assign_region(
                || "input scalar x",
                |mut region| {
                    region.assign_advice(
                        || "assign x",
                        config.value,
                        0,
                        || self.x.ok_or(Error::Synthesis),
                    )
                },
            )?;
            let mut P_batch_assigned = Vec::with_capacity(self.batch_size);
            let mut x_batch_assigned = Vec::with_capacity(self.batch_size);
            for i in 0..self.batch_size {
                let assigned = chip.load_private(
                    layouter.namespace(|| format!("input point P_{}", i)),
                    self.P_batch[i].map(|P| (P.x, P.y)),
                )?;
                P_batch_assigned.push(assigned);

                let xb_assigned = layouter.assign_region(
                    || "input scalar x",
                    |mut region| {
                        region.assign_advice(
                            || format!("assign x_{}", i),
                            config.value,
                            0,
                            || self.x_batch[i].clone().ok_or(Error::Synthesis),
                        )
                    },
                )?;
                x_batch_assigned.push(xb_assigned);
            }

            /*
            // test fp mul
            {
                let prod = chip
                    .fp_chip
                    .mul(&mut layouter, &P_assigned.x, &P_assigned.y)?;
                assert_eq!(prod.value, prod.truncation.to_bigint());
                if self.P != None {
                    let actual_prod = self.P.unwrap().x * self.P.unwrap().y;
                    assert_eq!(fp_to_bigint(&actual_prod), prod.value.unwrap());
                }
            }
            */

            // test add_unequal
            {
                let sum = chip.add_unequal(
                    &mut layouter.namespace(|| "add_unequal"),
                    &P_assigned,
                    &Q_assigned,
                )?;
                assert_eq!(sum.x.truncation.to_bigint(), sum.x.value);
                assert_eq!(sum.y.truncation.to_bigint(), sum.y.value);
                if self.P != None {
                    let actual_sum = G1Affine::from(self.P.unwrap() + self.Q.unwrap());
                    assert_eq!(sum.x.value.unwrap(), fp_to_bigint(&actual_sum.x));
                    assert_eq!(sum.y.value.unwrap(), fp_to_bigint(&actual_sum.y));
                }
            }

            // test double
            {
                let doub = chip.double(&mut layouter.namespace(|| "double"), &P_assigned)?;
                if self.P != None {
                    let actual_doub = G1Affine::from(self.P.unwrap() * Fn::from(2));
                    assert_eq!(doub.x.value.unwrap(), fp_to_bigint(&actual_doub.x));
                    assert_eq!(doub.y.value.unwrap(), fp_to_bigint(&actual_doub.y));
                }
            }

            /*
            // test scalar mult
            {
                let scalar_mult = chip.scalar_mult(
                    &mut layouter.namespace(|| "scalar_mult"),
                    &P_assigned,
                    &x_assigned,
                    F::from(3),
                    254,
                    4,
                )?;
                assert_eq!(scalar_mult.x.truncation.to_bigint(), scalar_mult.x.value);
                assert_eq!(scalar_mult.y.truncation.to_bigint(), scalar_mult.y.value);
                if self.P != None {
                    let actual = G1Affine::from(
                        &self.P.unwrap()
                            * Fn::from_repr_vartime(
                                self.x.unwrap().to_repr().as_ref()[..32].try_into().unwrap(),
                            )
                            .unwrap(),
                    );
                    assert_eq!(fp_to_bigint(&actual.x), scalar_mult.x.value.unwrap());
                    assert_eq!(fp_to_bigint(&actual.y), scalar_mult.y.value.unwrap());
                    println!("OK");
                }
            }
            */

            /*
            // test multi scalar mult
            {
                let multi_scalar_mult = chip.multi_scalar_mult(
                    &mut layouter.namespace(|| "multi_scalar_mult"),
                    &P_batch_assigned,
                    &x_batch_assigned,
                    F::from(3),
                    254,
                    4,
                )?;
                assert_eq!(
                    multi_scalar_mult.x.truncation.to_bigint(),
                    multi_scalar_mult.x.value
                );
                assert_eq!(
                    multi_scalar_mult.y.truncation.to_bigint(),
                    multi_scalar_mult.y.value
                );
                if self.P_batch[0] != None {
                    let mut msm = G1::identity();
                    for (P, x) in self.P_batch.iter().zip(self.x_batch.iter()) {
                        msm = msm
                            + P.as_ref().unwrap()
                                * Fn::from_repr(
                                    x.as_ref().unwrap().to_repr().as_ref()[..32]
                                        .try_into()
                                        .unwrap(),
                                )
                                .unwrap();
                    }
                    let actual = G1Affine::from(msm);
                    assert_eq!(fp_to_bigint(&actual.x), multi_scalar_mult.x.value.unwrap());
                    assert_eq!(fp_to_bigint(&actual.y), multi_scalar_mult.y.value.unwrap());
                }
            }
            */

            Ok(())
        }
    }

    use halo2_proofs::pairing::bn256::{G1Affine, G1};
    #[test]
    fn test_ecc_crt() {
        let k = 23;
        let mut rng = rand::thread_rng();

        let batch_size = BATCH_SIZE;

        let P = Some(G1Affine::random(&mut rng));
        let Q = Some(G1Affine::random(&mut rng));
        let x = Some(Fn::random(&mut rng));
        let mut P_batch = Vec::with_capacity(batch_size);
        let mut x_batch = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            P_batch.push(Some(G1Affine::random(&mut rng)));
            x_batch.push(Some(Fn::random(&mut rng)));
        }

        let circuit = MyCircuit::<Fn> {
            P,
            Q,
            P_batch,
            x,
            x_batch,
            batch_size,
            _marker: PhantomData,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_ecc_crt() {
        let k = 12;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

        let batch_size = BATCH_SIZE;
        let circuit = MyCircuit::<Fn> {
            P: None,
            Q: None,
            P_batch: vec![None; batch_size],
            x: None,
            x_batch: vec![None; batch_size],
            batch_size,
            _marker: PhantomData,
        };

        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
