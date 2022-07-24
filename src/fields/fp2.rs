use halo2_proofs::{arithmetic::FieldExt, circuit::Layouter, plonk::Error};
use num_bigint::{BigInt, BigUint};

use crate::bigint::{
    add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
    sub_no_carry, CRTInteger, OverflowInteger,
};
use crate::fields::fp_crt::{FpChip, FpConfig};
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::{bigint_to_fe, decompose_bigint_option, fe_to_biguint};

use super::{FieldChip, FqPoint};

// Represent Fp2 point as FqPoint with degree = 2
// `Fp2 = Fp[u] / (u^2 + 1)`
// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
// This means we store an Fp2 point as `a_0 + a_1 * u` where `a_0, a_1 in Fp`
pub struct Fp2Chip<F: FieldExt> {
    pub fp_chip: FpChip<F>,
}

impl<F: FieldExt> Fp2Chip<F> {
    pub fn construct(fp_chip: FpChip<F>) -> Self {
        Self { fp_chip }
    }
}

impl<F: FieldExt> FieldChip<F> for Fp2Chip<F> {
    type WitnessType = Vec<Option<BigInt>>;
    type FieldPoint = FqPoint<F>;
    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        coeffs: Vec<Option<BigInt>>,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(2);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(layouter, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 2))
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

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        // (a_0 + a_1 * u) * (b_0 + b_1 * u) = (a_0 b_0 - a_1 b_1) + (a_0 b_1 + a_1 b_0) * u
        let mut ab_coeffs = Vec::with_capacity(a.degree * b.degree);
        for i in 0..a.degree {
            for j in 0..b.degree {
                let coeff = self
                    .fp_chip
                    .mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j])?;
                ab_coeffs.push(coeff);
            }
        }
        let a0b0_minus_a1b1 = self.fp_chip.sub_no_carry(
            layouter,
            &ab_coeffs[0 * b.degree + 0],
            &ab_coeffs[1 * b.degree + 1],
        )?;
        let a0b1_plus_a1b0 = self.fp_chip.add_no_carry(
            layouter,
            &ab_coeffs[0 * b.degree + 1],
            &ab_coeffs[1 * b.degree + 0],
        )?;

        let mut out_coeffs = Vec::with_capacity(a.degree);
        out_coeffs.push(a0b0_minus_a1b1);
        out_coeffs.push(a0b1_plus_a1b0);

        Ok(FqPoint::construct(out_coeffs, a.degree))
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
