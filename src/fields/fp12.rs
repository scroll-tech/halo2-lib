use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::Error};
use num_bigint::{BigInt, BigUint};

use crate::bigint::{
    add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
    sub_no_carry, CRTInteger, OverflowInteger,
};
use crate::fields::fp2::Fp2Chip;
use crate::fields::fp_crt::{FpChip, FpConfig};
use crate::fields::FqPoint;
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::bigint_to_fe;
use crate::utils::decompose_bigint_option;

use super::FieldChip;

// Represent Fp12 point as FqPoint with degree = 12
// `Fp12 = Fp2[w] / (w^6 - u - xi)`
// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to
// be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
// This means we store an Fp12 point as `\sum_{i = 0}^6 (a_{i0} + a_{i1} * u) * w^i`
// This is encoded in an FqPoint of degree 12 as `(a_{00}, ..., a_{50}, a_{01}, ..., a_{51})`
pub struct Fp12Chip<F: FieldExt> {
    pub fp_chip: FpChip<F>,
}

impl<F: FieldExt> Fp12Chip<F> {
    pub fn construct(fp_chip: FpChip<F>) -> Self {
        Self { fp_chip }
    }

    fn fp2_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        fp2_pt: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let deg = 6;
        assert_eq!(a.degree, 12);
        assert_eq!(fp2_pt.degree, 2);

        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            let coeff1 = self
                .fp_chip
                .mul_no_carry(layouter, &a.coeffs[i], &fp2_pt.coeffs[0])?;
            let coeff2 =
                self.fp_chip
                    .mul_no_carry(layouter, &a.coeffs[i + 6], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.sub_no_carry(layouter, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        for i in 0..6 {
            let coeff1 =
                self.fp_chip
                    .mul_no_carry(layouter, &a.coeffs[i + 6], &fp2_pt.coeffs[0])?;
            let coeff2 = self
                .fp_chip
                .mul_no_carry(layouter, &a.coeffs[i], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, 12))
    }

    // for \sum_i (a_i + b_i u) w^i, returns \sum_i (-1)^i (a_i + b_i u) w^i
    fn conjugate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
    }
}

impl<F: FieldExt> FieldChip<F> for Fp12Chip<F> {
    type WitnessType = Vec<Option<BigInt>>;
    type FieldPoint = FqPoint<F>;
    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        coeffs: Vec<Option<BigInt>>,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(12);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(layouter, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 12))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .add_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .sub_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: F,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .scalar_mul_no_carry(layouter, &a.coeffs[i], b)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    // w^6 = u + xi for xi = 9
    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let deg = 6;
        let xi = 9;
        assert_eq!(a.degree, 12);
        assert_eq!(b.degree, 12);

        // a = \sum_{i = 0}^5 (a_i * w^i + a_{i + 6} * w^i * u)
        // b = \sum_{i = 0}^5 (b_i * w^i + b_{i + 6} * w^i * u)
        let mut a0b0_coeffs = Vec::with_capacity(36);
        let mut a0b1_coeffs = Vec::with_capacity(36);
        let mut a1b0_coeffs = Vec::with_capacity(36);
        let mut a1b1_coeffs = Vec::with_capacity(36);
        for i in 0..6 {
            for j in 0..6 {
                let coeff00 = self
                    .fp_chip
                    .mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j])?;
                let coeff01 =
                    self.fp_chip
                        .mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j + 6])?;
                let coeff10 =
                    self.fp_chip
                        .mul_no_carry(layouter, &a.coeffs[i + 6], &b.coeffs[j])?;
                let coeff11 =
                    self.fp_chip
                        .mul_no_carry(layouter, &a.coeffs[i + 6], &b.coeffs[j + 6])?;
                a0b0_coeffs.push(coeff00);
                a0b1_coeffs.push(coeff01);
                a1b0_coeffs.push(coeff10);
                a1b1_coeffs.push(coeff11);
            }
        }

        let a0b0_minus_a1b1 = Vec::with_capacity(11);
        let a0b1_plus_a1b0 = Vec::with_capacity(11);
        for i in 0..11 {
            let a0b0_minus_a1b1_entry =
                self.fp_chip
                    .sub_no_carry(layouter, &a0b0_coeffs[i], &a1b1_coeffs[i])?;
            let a0b1_plus_a1b0_entry =
                self.fp_chip
                    .add_no_carry(layouter, &a0b1_coeffs[i], &a1b0_coeffs[i])?;

            a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
            a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
        }

        // out_i       = a0b0_minus_a1b1_i + 9 * a0b0_minus_a1b1_{i + 6} - a0b1_plus_a1b0_{i + 6}
        // out_{i + 6} = a0b1_plus_a1b0_{i} + a0b0_minus_a1b1_{i + 6} + 9 * a0b1_plus_a1b0_{i + 6}
        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            let coeff1 =
                self.fp_chip
                    .sub_no_carry(layouter, &a0b0_minus_a1b1[i], &a0b1_plus_a1b0[i + 6])?;
            let coeff2 =
                self.fp_chip
                    .scalar_mul_no_carry(layouter, &a0b0_minus_a1b1[i + 6], F::from(9))?;
            let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
            if i < 5 {
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b0_minus_a1b1[i].clone());
            }
        }
        for i in 0..6 {
            let coeff1 =
                self.fp_chip
                    .add_no_carry(layouter, &a0b1_plus_a1b0[i], &a0b0_minus_a1b1[i + 6])?;
            let coeff2 =
                self.fp_chip
                    .scalar_mul_no_carry(layouter, &a0b1_plus_a1b0[i + 6], F::from(9))?;
            let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
            if i < 5 {
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b1_plus_a1b0[i].clone());
            }
        }
        Ok(FqPoint::construct(out_coeffs, 12))
    }

    fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<(), Error> {
        for coeff in &a.coeffs {
            self.fp_chip.check_carry_mod_to_zero(layouter, coeff)?;
        }
        Ok(())
    }

    fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.carry_mod(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn range_check(&self, layouter: &mut impl Layouter<F>, a: &FqPoint<F>) -> Result<(), Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.range_check(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(())
    }
}
