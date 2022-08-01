#![allow(non_snake_case)]
use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{layouter, Layouter},
    pairing::bn256::Fq as Fp,
    pairing::group::ff::PrimeField,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use halo2curves::bn254::Fq;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use rand_core::OsRng;

use crate::gates::{qap_gate, range};
use crate::utils::{
    bigint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint, fe_to_biguint, modulus,
};
use crate::{
    ecc::EccChip,
    fields::{
        fp::{FpChip, FpConfig},
        fp12::Fp12Chip,
        fp2::Fp2Chip,
        FieldChip,
    },
};
use crate::{ecc::EccPoint, fields::FqPoint};

const XI_0: u64 = 9;

// Inputs:
//  P0 = (x_1, y_1) and P1 = (x_2, y_2) are points in E(Fp2)
//  Q is point (X, Y) in E(Fp)
// Assuming P0 != P1
// Output:
//  line_{Psi(P0), Psi(P1)}(Q) where Psi(x,y) = (w^2 x, w^3 y)
//  - equals w^3 (y_1 - y_2) X + w^2 (x_2 - x_1) Y + w^5 (x_1 y_2 - x_2 y_1) =: out3 * w^3 + out2 * w^2 + out5 * w^5 where out2, out3, out5 are Fp2 points
// Output is [None, None, out2, out3, None, out5] as vector of `Option<FqPoint>`s
pub fn sparse_line_function_unequal<F: FieldExt>(
    fp2_chip: Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    P: (&EccPoint<F, Fp2Chip<F>>, &EccPoint<F, Fp2Chip<F>>),
    Q: &EccPoint<F, FpChip<F>>,
) -> Result<Vec<Option<FqPoint<F>>>, Error> {
    let (x_1, y_1) = (P.0.x, P.0.y);
    let (x_2, y_2) = (P.1.x, P.1.y);
    let (X, Y) = (Q.x, Q.y);
    assert_eq!(x_1.coeffs.len(), 2);
    assert_eq!(y_1.coeffs.len(), 2);
    assert_eq!(x_2.coeffs.len(), 2);
    assert_eq!(y_2.coeffs.len(), 2);
    assert_eq!(x_1.degree, 2);
    assert_eq!(y_1.degree, 2);
    assert_eq!(x_2.degree, 2);
    assert_eq!(y_2.degree, 2);

    let y1_minus_y2 = fp2_chip.sub_no_carry(layouter, &y_1, &y_2)?;
    let x2_minus_x1 = fp2_chip.sub_no_carry(layouter, &x_2, &x_1)?;
    let x1y2 = fp2_chip.mul_no_carry(layouter, &x_1, &y_2)?;
    let x2y1 = fp2_chip.mul_no_carry(layouter, &x_2, &y_1)?;

    let out3 = fp2_chip.fp_mul_no_carry(layouter, &y1_minus_y2, &X)?;
    let out2 = fp2_chip.fp_mul_no_carry(layouter, &x2_minus_x1, &Y)?;
    let out5 = fp2_chip.sub_no_carry(layouter, &x1y2, &x2y1)?;

    Ok(vec![None, None, Some(out2), Some(out3), None, Some(out5)])
}

// multiply (a0 + a1 * u) * (XI0 + u) without carry
pub fn mul_no_carry_w6<F: FieldExt>(
    fp_chip: FpChip<F>,
    layouter: &mut impl Layouter<F>,
    a: &FqPoint<F>,
) -> Result<FqPoint<F>, Error> {
    assert_eq!(a.coeffs.len(), 2);
    let (a0, a1) = (a.coeffs[0], a.coeffs[1]);
    // (a0 + a1 u) * (XI_0 + u) = (a0 * XI_0 - a1) + (a1 * XI_0 + a0) u     with u^2 = -1
    // This should fit in the overflow representation if limb_bits is large enough
    let a0_xi0 = fp_chip.scalar_mul_no_carry(layouter, &a0, F::from(XI_0))?;
    let out0_0_nocarry = fp_chip.sub_no_carry(layouter, &a0_xi0, &a1)?;
    let a1_xi0 = fp_chip.scalar_mul_no_carry(layouter, &a1, F::from(XI_0))?;
    let out0_1_nocarry = fp_chip.add_no_carry(layouter, &a1_xi0, &a0)?;
    let out0_0 = fp_chip.carry_mod(layouter, &out0_0_nocarry)?;
    let out0_1 = fp_chip.carry_mod(layouter, &out0_1_nocarry)?;
    Ok(FqPoint::construct(vec![out0_0, out0_1], 2))
}
// Assuming curve is of form Y^2 = X^3 + b (a = 0) to save operations
// Inputs:
//  P = (x, y) is a point in E(Fp2)
//  Q = (Q.x, Q.y) in E(Fp)
// Output:
//  line_{Psi(P), Psi(P)}(Q) where Psi(x,y) = (w^2 x, w^3 y)
//  - equals (3x^3 - 2y^2)(XI_0 + u) + w^4 (-3 x^2 * Q.x) + w^3 (2 y * Q.y) =: out0 + out4 * w^4 + out3 * w^3 where out0, out3, out4 are Fp2 points
// Output is [out0, None, None, out3, out4, None] as vector of `Option<FqPoint>`s
pub fn sparse_line_function_equal<F: FieldExt>(
    fp2_chip: Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, Fp2Chip<F>>,
    Q: &EccPoint<F, FpChip<F>>,
) -> Result<Vec<Option<FqPoint<F>>>, Error> {
    let (x, y) = (P.x, P.y);
    assert_eq!(x.coeffs.len(), 2);
    assert_eq!(y.coeffs.len(), 2);
    assert_eq!(x.degree, 2);
    assert_eq!(y.degree, 2);

    let x_sq = fp2_chip.mul(layouter, &x, &x)?;

    let x_cube = fp2_chip.mul_no_carry(layouter, &x_sq, &x)?;
    let three_x_cu = fp2_chip.scalar_mul_no_carry(layouter, &x_cube, F::from(3))?;
    let y_sq = fp2_chip.mul_no_carry(layouter, &y, &y)?;
    let two_y_sq = fp2_chip.scalar_mul_no_carry(layouter, &y_sq, F::from(2))?;
    let out0_left = fp2_chip.sub_no_carry(layouter, &three_x_cu, &two_y_sq)?;
    let out0 = mul_no_carry_w6(fp2_chip.fp_chip, layouter, &out0_left)?;

    let x_sq_Qx = fp2_chip.fp_mul_no_carry(layouter, &x_sq, &Q.x)?;
    let out4_nocarry = fp2_chip.scalar_mul_no_carry(layouter, &x_sq_Qx, -F::from(3))?;
    let out4 = fp2_chip.carry_mod(layouter, &out4_nocarry)?;

    let y_Qy = fp2_chip.fp_mul_no_carry(layouter, &y, &Q.y)?;
    let out3_nocarry = fp2_chip.scalar_mul_no_carry(layouter, &y_Qy, F::from(2))?;
    let out3 = fp2_chip.carry_mod(layouter, &out3_nocarry)?;

    Ok(vec![Some(out0), None, None, Some(out3), Some(out4), None])
}

// multiply Fp12 point `a` with Fp12 point `b` where `b` is len 6 vector of Fp2 points, where some are `None` to represent zero.
// Assumes `b` is not vector of all `None`s
pub fn sparse_fp12_multiply<F: FieldExt>(
    fp2_chip: Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    a: &FqPoint<F>,
    b_fp2_coeffs: &Vec<Option<FqPoint<F>>>,
) -> Result<FqPoint<F>, Error> {
    assert_eq!(a.coeffs.len(), 12);
    assert_eq!(b_fp2_coeffs.len(), 6);
    let a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs.push(FqPoint::construct(vec![a.coeffs[i], a.coeffs[i + 6]], 2));
    }
    // a * b as element of Fp2[w] without evaluating w^6 = (XI_0 + u)
    let mut prod_2d: Vec<Option<FqPoint<F>>> = vec![None; 11];
    for i in 0..6 {
        for j in 0..6 {
            prod_2d[i + j] = match (prod_2d[i + j], a_fp2_coeffs[i], b_fp2_coeffs[j]) {
                (a, _, None) => a,
                (None, a, Some(b)) => {
                    let ab = fp2_chip.mul_no_carry(layouter, &a, &b)?;
                    Some(ab)
                }
                (Some(a), b, Some(c)) => {
                    let bc = fp2_chip.mul_no_carry(layouter, &b, &c)?;
                    let out = fp2_chip.add_no_carry(layouter, &a, &bc)?;
                    Some(out)
                }
            };
        }
    }

    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        // prod_2d[i] + prod_2d[i+6] * w^6
        let eval_w6 = mul_no_carry_w6(fp2_chip.fp_chip, layouter, &prod_2d[i + 6].unwrap())?;
        let prod_nocarry = fp2_chip.add_no_carry(layouter, &prod_2d[i].unwrap(), &eval_w6)?;
        let prod = fp2_chip.carry_mod(layouter, &prod_nocarry)?;
        out_fp2.push(prod);
    }

    let mut out_coeffs = Vec::with_capacity(12);
    for fp2_coeff in out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[0]);
    }
    for fp2_coeff in out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[1]);
    }
    Ok(FqPoint::construct(out_coeffs, 12))
}

// Input:
// - g is Fp12 point
// - P = (P0, P1) with P0, P1 points in E(Fp2)
// - Q is point in E(Fp)
// Output:
// - out = g * l_{Psi(P0), Psi(P1)}(Q) as Fp12 point
pub fn fp12_multiply_with_line_unequal<F: FieldExt>(
    fp2_chip: Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    g: &FqPoint<F>,
    P: (&EccPoint<F, Fp2Chip<F>>, &EccPoint<F, Fp2Chip<F>>),
    Q: &EccPoint<F, FpChip<F>>,
) -> Result<FqPoint<F>, Error> {
    let line = sparse_line_function_unequal(fp2_chip, layouter, P, Q)?;
    sparse_fp12_multiply(fp2_chip, layouter, g, &line)
}

// Input:
// - g is Fp12 point
// - P is point in E(Fp2)
// - Q is point in E(Fp)
// Output:
// - out = g * l_{Psi(P), Psi(P)}(Q) as Fp12 point
pub fn fp12_multiply_with_line_equal<F: FieldExt>(
    fp2_chip: Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    g: &FqPoint<F>,
    P: &EccPoint<F, Fp2Chip<F>>,
    Q: &EccPoint<F, FpChip<F>>,
) -> Result<FqPoint<F>, Error> {
    let line = sparse_line_function_equal(fp2_chip, layouter, P, Q)?;
    sparse_fp12_multiply(fp2_chip, layouter, g, &line)
}

// Assuming curve is of form `y^2 = x^3 + b` for now (a = 0) for less operations
// Value of `b` is never used
// Inputs:
// - P = (x, y) is a point in E(Fp2)
// - Q is a point in E(Fp)
// - `pseudo_binary_encoding` is fixed vector consisting of {-1, 0, 1} entries such that `loop_count = sum pseudo_binary_encoding[i] * 2^i`
// Output:
//  - `(f_{loop_count}(P,Q), [loop_count]*P)`
//  - where we start with `f_1(P,Q) = 1` and use Miller's algorithm f_{i+j} = f_i * f_j * l_{i,j}(P,Q)
// Assume:
//  - P != O and the order of P in E(Fp2) is r
//  - r is prime, so [i]P != [j]P for i != j in Z/r
//  - `0 <= loop_count < r` and `loop_count < p`
//  - x^3 + b = 0 has no solution in Fp2, i.e., the y-coordinate of P cannot be 0.

pub fn miller_loop<F: FieldExt>(
    ecc_chip: EccChip<F, Fp2Chip<F>>,
    fp12_chip: Fp12Chip<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F, Fp2Chip<F>>,
    Q: &EccPoint<F, FpChip<F>>,
    pseudo_binary_encoding: &Vec<i8>,
) -> Result<(FqPoint<F>, EccPoint<F, Fp2Chip<F>>), Error> {
    let i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;

    let neg_P = ecc_chip.negate(layouter, P)?;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 {
        P.clone()
    } else {
        neg_P.clone()
    };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal(ecc_chip.field_chip, layouter, &R, Q)?;
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = ecc_chip
        .field_chip
        .fp_chip
        .load_constant(layouter, BigInt::from(0))?;
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[0]);
        } else {
            f_coeffs.push(zero_fp);
        }
    }
    for coeff in sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[1]);
        } else {
            f_coeffs.push(zero_fp);
        }
    }

    let mut f = FqPoint::construct(f_coeffs, 12);

    while i >= 0 {
        if i != last_index - 1 {
            let f_sq = fp12_chip.mul(layouter, &f, &f)?;
            f = fp12_multiply_with_line_equal(ecc_chip.field_chip, layouter, &f_sq, &R, Q)?;
        }
        R = ecc_chip.double(layouter, &R)?;

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_P = if pseudo_binary_encoding[i] == 1 {
                &P
            } else {
                &neg_P
            };
            f = fp12_multiply_with_line_unequal(
                ecc_chip.field_chip,
                layouter,
                &f,
                (&R, sign_P),
                Q,
            )?;
            R = ecc_chip.add_unequal(layouter, &R, sign_P)?;
        }
    }
    Ok((f, R))
}
