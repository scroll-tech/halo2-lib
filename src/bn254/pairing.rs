#![allow(non_snake_case)]
use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::Layouter,
    pairing::{
        bn256,
        bn256::{G1Affine, G2Affine, SIX_U_PLUS_2_NAF},
    },
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use halo2curves::bn254::{Fq, Fq2, FROBENIUS_COEFF_FQ12_C1};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use super::{Fp12Chip, Fp2Chip, FpChip};
use crate::utils::{
    bigint_to_fe, biguint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint,
    fe_to_biguint, modulus,
};
use crate::{
    ecc::{EccChip, EccPoint},
    fields::{fp::FpConfig, FieldChip, FqPoint},
    gates::{qap_gate, range},
};

const XI_0: u64 = 9;

// Inputs:
//  Q0 = (x_1, y_1) and Q1 = (x_2, y_2) are points in E(Fp2)
//  P is point (X, Y) in E(Fp)
// Assuming Q0 != Q1
// Output:
//  line_{Psi(Q0), Psi(Q1)}(P) where Psi(x,y) = (w^2 x, w^3 y)
//  - equals w^3 (y_1 - y_2) X + w^2 (x_2 - x_1) Y + w^5 (x_1 y_2 - x_2 y_1) =: out3 * w^3 + out2 * w^2 + out5 * w^5 where out2, out3, out5 are Fp2 points
// Output is [None, None, out2, out3, None, out5] as vector of `Option<FqPoint>`s
pub fn sparse_line_function_unequal<F: FieldExt>(
    fp2_chip: &Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    Q: (&EccPoint<F, Fp2Chip<F>>, &EccPoint<F, Fp2Chip<F>>),
    P: &EccPoint<F, FpChip<F>>,
) -> Result<Vec<Option<FqPoint<F>>>, Error> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (X, Y) = (&P.x, &P.y);
    assert_eq!(x_1.coeffs.len(), 2);
    assert_eq!(y_1.coeffs.len(), 2);
    assert_eq!(x_2.coeffs.len(), 2);
    assert_eq!(y_2.coeffs.len(), 2);
    assert_eq!(x_1.degree, 2);
    assert_eq!(y_1.degree, 2);
    assert_eq!(x_2.degree, 2);
    assert_eq!(y_2.degree, 2);

    let y1_minus_y2 = fp2_chip.sub_no_carry(layouter, y_1, y_2)?;
    let x2_minus_x1 = fp2_chip.sub_no_carry(layouter, x_2, x_1)?;
    let x1y2 = fp2_chip.mul_no_carry(layouter, x_1, y_2)?;
    let x2y1 = fp2_chip.mul_no_carry(layouter, x_2, y_1)?;

    let out3 = fp2_chip.fp_mul_no_carry(layouter, &y1_minus_y2, X)?;
    let out2 = fp2_chip.fp_mul_no_carry(layouter, &x2_minus_x1, Y)?;
    let out5 = fp2_chip.sub_no_carry(layouter, &x1y2, &x2y1)?;

    // so far we have not "carried mod p" for any of the outputs
    // we do this below
    Ok(vec![None, None, Some(out2), Some(out3), None, Some(out5)]
        .iter()
        .map(|option_nc| {
            option_nc.as_ref().map(|nocarry| {
                fp2_chip.carry_mod(layouter, nocarry).expect("carry mod should not fail")
            })
        })
        .collect())
}

// multiply (a0 + a1 * u) * (XI0 + u) without carry
pub fn mul_no_carry_w6<F: FieldExt>(
    fp_chip: &FpChip<F>,
    layouter: &mut impl Layouter<F>,
    a: &FqPoint<F>,
) -> Result<FqPoint<F>, Error> {
    assert_eq!(a.coeffs.len(), 2);
    let (a0, a1) = (&a.coeffs[0], &a.coeffs[1]);
    // (a0 + a1 u) * (XI_0 + u) = (a0 * XI_0 - a1) + (a1 * XI_0 + a0) u     with u^2 = -1
    // This should fit in the overflow representation if limb_bits is large enough
    let a0_xi0 = fp_chip.scalar_mul_no_carry(layouter, a0, F::from(XI_0))?;
    let out0_0_nocarry = fp_chip.sub_no_carry(layouter, &a0_xi0, a1)?;
    let a1_xi0 = fp_chip.scalar_mul_no_carry(layouter, a1, F::from(XI_0))?;
    let out0_1_nocarry = fp_chip.add_no_carry(layouter, &a1_xi0, a0)?;
    let out0_0 = fp_chip.carry_mod(layouter, &out0_0_nocarry)?;
    let out0_1 = fp_chip.carry_mod(layouter, &out0_1_nocarry)?;
    Ok(FqPoint::construct(vec![out0_0, out0_1], 2))
}
// Assuming curve is of form Y^2 = X^3 + b (a = 0) to save operations
// Inputs:
//  Q = (x, y) is a point in E(Fp2)
//  P = (P.x, P.y) in E(Fp)
// Output:
//  line_{Psi(Q), Psi(Q)}(P) where Psi(x,y) = (w^2 x, w^3 y)
//  - equals (3x^3 - 2y^2)(XI_0 + u) + w^4 (-3 x^2 * Q.x) + w^3 (2 y * Q.y) =: out0 + out4 * w^4 + out3 * w^3 where out0, out3, out4 are Fp2 points
// Output is [out0, None, None, out3, out4, None] as vector of `Option<FqPoint>`s
pub fn sparse_line_function_equal<F: FieldExt>(
    fp2_chip: &Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    Q: &EccPoint<F, Fp2Chip<F>>,
    P: &EccPoint<F, FpChip<F>>,
) -> Result<Vec<Option<FqPoint<F>>>, Error> {
    let (x, y) = (&Q.x, &Q.y);
    assert_eq!(x.coeffs.len(), 2);
    assert_eq!(y.coeffs.len(), 2);
    assert_eq!(x.degree, 2);
    assert_eq!(y.degree, 2);

    let x_sq = fp2_chip.mul(layouter, x, x)?;

    let x_cube = fp2_chip.mul_no_carry(layouter, &x_sq, x)?;
    let three_x_cu = fp2_chip.scalar_mul_no_carry(layouter, &x_cube, F::from(3))?;
    let y_sq = fp2_chip.mul_no_carry(layouter, y, y)?;
    let two_y_sq = fp2_chip.scalar_mul_no_carry(layouter, &y_sq, F::from(2))?;
    let out0_left = fp2_chip.sub_no_carry(layouter, &three_x_cu, &two_y_sq)?;
    let out0 = mul_no_carry_w6(&fp2_chip.fp_chip, layouter, &out0_left)?;

    let x_sq_Px = fp2_chip.fp_mul_no_carry(layouter, &x_sq, &P.x)?;
    let out4 = fp2_chip.scalar_mul_no_carry(layouter, &x_sq_Px, -F::from(3))?;

    let y_Py = fp2_chip.fp_mul_no_carry(layouter, y, &P.y)?;
    let out3 = fp2_chip.scalar_mul_no_carry(layouter, &y_Py, F::from(2))?;

    // so far we have not "carried mod p" for any of the outputs
    // we do this below
    Ok(vec![Some(out0), None, None, Some(out3), Some(out4), None]
        .iter()
        .map(|option_nc| {
            option_nc.as_ref().map(|nocarry| {
                fp2_chip.carry_mod(layouter, nocarry).expect("carry mod should not fail")
            })
        })
        .collect())
}

// multiply Fp12 point `a` with Fp12 point `b` where `b` is len 6 vector of Fp2 points, where some are `None` to represent zero.
// Assumes `b` is not vector of all `None`s
pub fn sparse_fp12_multiply<F: FieldExt>(
    fp2_chip: &Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    a: &FqPoint<F>,
    b_fp2_coeffs: &Vec<Option<FqPoint<F>>>,
) -> Result<FqPoint<F>, Error> {
    assert_eq!(a.coeffs.len(), 12);
    assert_eq!(b_fp2_coeffs.len(), 6);
    let mut a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs
            .push(FqPoint::construct(vec![a.coeffs[i].clone(), a.coeffs[i + 6].clone()], 2));
    }
    // a * b as element of Fp2[w] without evaluating w^6 = (XI_0 + u)
    let mut prod_2d: Vec<Option<FqPoint<F>>> = vec![None; 11];
    for i in 0..6 {
        for j in 0..6 {
            prod_2d[i + j] =
                match (prod_2d[i + j].clone(), &a_fp2_coeffs[i], b_fp2_coeffs[j].as_ref()) {
                    (a, _, None) => a,
                    (None, a, Some(b)) => {
                        let ab = fp2_chip.mul_no_carry(layouter, a, b)?;
                        Some(ab)
                    }
                    (Some(a), b, Some(c)) => {
                        let bc = fp2_chip.mul_no_carry(layouter, b, c)?;
                        let out = fp2_chip.add_no_carry(layouter, &a, &bc)?;
                        Some(out)
                    }
                };
        }
    }

    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        // prod_2d[i] + prod_2d[i+6] * w^6
        let prod_nocarry = if i != 5 {
            let eval_w6 = prod_2d[i + 6].as_ref().map(|a| {
                mul_no_carry_w6(&fp2_chip.fp_chip, layouter, a)
                    .expect("mul_no_carry_w6 should not fail")
            });
            match (prod_2d[i].as_ref(), eval_w6) {
                (None, b) => b.unwrap(), // Our current use cases of 235 and 034 sparse multiplication always result in non-None value
                (Some(a), None) => a.clone(),
                (Some(a), Some(b)) => {
                    fp2_chip.add_no_carry(layouter, a, &b).expect("add no carry should not fail")
                }
            }
        } else {
            prod_2d[i].clone().unwrap()
        };
        let prod = fp2_chip.carry_mod(layouter, &prod_nocarry)?;
        out_fp2.push(prod);
    }

    let mut out_coeffs = Vec::with_capacity(12);
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[0].clone());
    }
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[1].clone());
    }
    Ok(FqPoint::construct(out_coeffs, 12))
}

// Input:
// - g is Fp12 point
// - Q = (P0, P1) with Q0, Q1 points in E(Fp2)
// - P is point in E(Fp)
// Output:
// - out = g * l_{Psi(Q0), Psi(Q1)}(P) as Fp12 point
pub fn fp12_multiply_with_line_unequal<F: FieldExt>(
    fp2_chip: &Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    g: &FqPoint<F>,
    Q: (&EccPoint<F, Fp2Chip<F>>, &EccPoint<F, Fp2Chip<F>>),
    P: &EccPoint<F, FpChip<F>>,
) -> Result<FqPoint<F>, Error> {
    let line = sparse_line_function_unequal(fp2_chip, layouter, Q, P)?;
    sparse_fp12_multiply(fp2_chip, layouter, g, &line)
}

// Input:
// - g is Fp12 point
// - Q is point in E(Fp2)
// - P is point in E(Fp)
// Output:
// - out = g * l_{Psi(Q), Psi(Q)}(P) as Fp12 point
pub fn fp12_multiply_with_line_equal<F: FieldExt>(
    fp2_chip: &Fp2Chip<F>,
    layouter: &mut impl Layouter<F>,
    g: &FqPoint<F>,
    Q: &EccPoint<F, Fp2Chip<F>>,
    P: &EccPoint<F, FpChip<F>>,
) -> Result<FqPoint<F>, Error> {
    let line = sparse_line_function_equal(fp2_chip, layouter, Q, P)?;
    sparse_fp12_multiply(fp2_chip, layouter, g, &line)
}

// Assuming curve is of form `y^2 = x^3 + b` for now (a = 0) for less operations
// Value of `b` is never used
// Inputs:
// - Q = (x, y) is a point in E(Fp2)
// - P is a point in E(Fp)
// - `pseudo_binary_encoding` is fixed vector consisting of {-1, 0, 1} entries such that `loop_count = sum pseudo_binary_encoding[i] * 2^i`
// Output:
//  - f_{loop_count}(Q,P) * l_{[loop_count] Q', Frob_p(Q')} * l_{[loop_count] Q' + Frob_p(Q'), -Frob_p^2(Q')}(P)
//  - where we start with `f_1(Q,P) = 1` and use Miller's algorithm f_{i+j} = f_i * f_j * l_{i,j}(Q,P)
//  - Q' = Psi(Q) in E(Fp12)
//  - Frob_p(x,y) = (x^p, y^p)
//  - Above formula is specific to BN curves
// Assume:
//  - Q != O and the order of Q in E(Fp2) is r
//  - r is prime, so [i]Q != [j]Q for i != j in Z/r
//  - `0 <= loop_count < r` and `loop_count < p` (to avoid [loop_count]Q' = Frob_p(Q'))
//  - x^3 + b = 0 has no solution in Fp2, i.e., the y-coordinate of Q cannot be 0.

pub fn miller_loop_BN<F: FieldExt>(
    ecc_chip: &EccChip<F, Fp2Chip<F>>,
    fp12_chip: &Fp12Chip<F>,
    layouter: &mut impl Layouter<F>,
    Q: &EccPoint<F, Fp2Chip<F>>,
    P: &EccPoint<F, FpChip<F>>,
    pseudo_binary_encoding: &[i8],
) -> Result<FqPoint<F>, Error> {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    println!("loop len = {}", last_index);

    let neg_Q = ecc_chip.negate(layouter, Q)?;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 { Q.clone() } else { neg_Q.clone() };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal(&ecc_chip.field_chip, layouter, &R, P)?;
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = ecc_chip.field_chip.fp_chip.load_constant(layouter, BigInt::from(0))?;
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[0].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[1].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }

    let mut f = FqPoint::construct(f_coeffs, 12);

    loop {
        if i != last_index - 1 {
            let f_sq = fp12_chip.mul(layouter, &f, &f)?;
            f = fp12_multiply_with_line_equal(&ecc_chip.field_chip, layouter, &f_sq, &R, P)?;
        }
        R = ecc_chip.double(layouter, &R)?;

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = if pseudo_binary_encoding[i] == 1 { &Q } else { &neg_Q };
            f = fp12_multiply_with_line_unequal(
                &ecc_chip.field_chip,
                layouter,
                &f,
                (&R, sign_Q),
                P,
            )?;
            R = ecc_chip.add_unequal(layouter, &R, sign_Q)?;
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    println!("finished main miller loop");

    // Frobenius coefficient coeff[1][j] = ((9+u)^{(p-1)/6})^j
    // load coeff[1][2], coeff[1][3]
    let c2 = FROBENIUS_COEFF_FQ12_C1[1] * FROBENIUS_COEFF_FQ12_C1[1];
    let c3 = c2 * FROBENIUS_COEFF_FQ12_C1[1];
    let c2 = ecc_chip.field_chip.load_constant(layouter, c2)?;
    let c3 = ecc_chip.field_chip.load_constant(layouter, c3)?;

    let Q_1 = twisted_frobenius(ecc_chip, layouter, Q, &c2, &c3)?;
    let neg_Q_2 = neg_twisted_frobenius(ecc_chip, layouter, &Q_1, &c2, &c3)?;
    f = fp12_multiply_with_line_unequal(&ecc_chip.field_chip, layouter, &f, (&R, &Q_1), P)?;
    R = ecc_chip.add_unequal(layouter, &R, &Q_1)?;
    f = fp12_multiply_with_line_unequal(&ecc_chip.field_chip, layouter, &f, (&R, &neg_Q_2), P)?;

    Ok(f)
}

// Frobenius coefficient coeff[1][j] = ((9+u)^{(p-1)/6})^j
// Frob_p( twist(Q) ) = ( (w^2 x)^p, (w^3 y)^p ) = twist( coeff[1][2] * x^p, coeff[1][3] * y^p )
// Input:
// - Q = (x, y) point in E(Fp2)
// - coeff[1][2], coeff[1][3] as assigned cells: this is an optimization to avoid loading new constants
// Output:
// - (coeff[1][2] * x^p, coeff[1][3] * y^p) point in E(Fp2)
pub fn twisted_frobenius<F: FieldExt>(
    ecc_chip: &EccChip<F, Fp2Chip<F>>,
    layouter: &mut impl Layouter<F>,
    Q: &EccPoint<F, Fp2Chip<F>>,
    c2: &FqPoint<F>,
    c3: &FqPoint<F>,
) -> Result<EccPoint<F, Fp2Chip<F>>, Error> {
    assert_eq!(c2.coeffs.len(), 2);
    assert_eq!(c3.coeffs.len(), 2);

    let frob_x = ecc_chip.field_chip.conjugate(layouter, &Q.x)?;
    let frob_y = ecc_chip.field_chip.conjugate(layouter, &Q.y)?;
    let out_x = ecc_chip.field_chip.mul(layouter, &c2, &frob_x)?;
    let out_y = ecc_chip.field_chip.mul(layouter, &c3, &frob_y)?;
    Ok(EccPoint::construct(out_x, out_y))
}

// Frobenius coefficient coeff[1][j] = ((9+u)^{(p-1)/6})^j
// -Frob_p( twist(Q) ) = ( (w^2 x)^p, -(w^3 y)^p ) = twist( coeff[1][2] * x^p, coeff[1][3] * -y^p )
// Input:
// - Q = (x, y) point in E(Fp2)
// Output:
// - (coeff[1][2] * x^p, coeff[1][3] * -y^p) point in E(Fp2)
pub fn neg_twisted_frobenius<F: FieldExt>(
    ecc_chip: &EccChip<F, Fp2Chip<F>>,
    layouter: &mut impl Layouter<F>,
    Q: &EccPoint<F, Fp2Chip<F>>,
    c2: &FqPoint<F>,
    c3: &FqPoint<F>,
) -> Result<EccPoint<F, Fp2Chip<F>>, Error> {
    assert_eq!(c2.coeffs.len(), 2);
    assert_eq!(c3.coeffs.len(), 2);

    let frob_x = ecc_chip.field_chip.conjugate(layouter, &Q.x)?;
    let neg_frob_y = ecc_chip.field_chip.neg_conjugate(layouter, &Q.y)?;
    let out_x = ecc_chip.field_chip.mul(layouter, &c2, &frob_x)?;
    let out_y = ecc_chip.field_chip.mul(layouter, &c3, &neg_frob_y)?;
    Ok(EccPoint::construct(out_x, out_y))
}

pub struct PairingChip<F: FieldExt> {
    pub g1_chip: EccChip<F, FpChip<F>>,
    pub g2_chip: EccChip<F, Fp2Chip<F>>,
    pub fp12_chip: Fp12Chip<F>,
}

impl<F: FieldExt> PairingChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self {
            g1_chip: EccChip::construct(FpChip::construct(config.clone()), config.range.clone()),
            g2_chip: EccChip::construct(Fp2Chip::construct(config.clone()), config.range.clone()),
            fp12_chip: Fp12Chip::construct(config),
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
        FpConfig::configure(
            meta,
            value,
            constant,
            lookup_bits,
            limb_bits,
            num_limbs,
            BigUint::from_str_radix(&Fq::MODULUS[2..], 16).unwrap(),
        )
    }

    pub fn load_private_g1(
        &self,
        layouter: &mut impl Layouter<F>,
        point: Option<G1Affine>,
    ) -> Result<EccPoint<F, FpChip<F>>, Error> {
        // go from pse/pairing::bn256::Fq to forked Fq
        let convert_fp = |x: bn256::Fq| biguint_to_fe(&fe_to_biguint(&x));
        self.g1_chip.load_private(
            layouter,
            (point.map(|pt| convert_fp(pt.x)), point.map(|pt| convert_fp(pt.y))),
        )
    }

    pub fn load_private_g2(
        &self,
        layouter: &mut impl Layouter<F>,
        point: Option<G2Affine>,
    ) -> Result<EccPoint<F, Fp2Chip<F>>, Error> {
        // go from pse/pairing::bn256::Fq2 to forked public Fq2
        let convert_fp2 = |c0: bn256::Fq, c1: bn256::Fq| Fq2 {
            c0: biguint_to_fe(&fe_to_biguint(&c0)),
            c1: biguint_to_fe(&fe_to_biguint(&c1)),
        };
        let x = point.map(|pt| convert_fp2(pt.x.c0, pt.x.c1));
        let y = point.map(|pt| convert_fp2(pt.y.c0, pt.y.c1));

        self.g2_chip.load_private(layouter, (x, y))
    }

    pub fn miller_loop(
        &self,
        layouter: &mut impl Layouter<F>,
        Q: &EccPoint<F, Fp2Chip<F>>,
        P: &EccPoint<F, FpChip<F>>,
    ) -> Result<FqPoint<F>, Error> {
        miller_loop_BN(
            &self.g2_chip,
            &self.fp12_chip,
            layouter,
            Q,
            P,
            &SIX_U_PLUS_2_NAF, // pseudo binary encoding for BN254
        )
    }

    // optimal Ate pairing
    pub fn pairing(
        &self,
        layouter: &mut impl Layouter<F>,
        Q: &EccPoint<F, Fp2Chip<F>>,
        P: &EccPoint<F, FpChip<F>>,
    ) -> Result<FqPoint<F>, Error> {
        let f0 = self.miller_loop(layouter, Q, P)?;
        // final_exp implemented in final_exp module
        let f = self.fp12_chip.final_exp(&self.g2_chip.field_chip, layouter, &f0)?;
        Ok(f)
    }
}
