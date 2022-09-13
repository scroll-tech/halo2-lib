use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use crate::fields::fp::{FpChip, FpConfig};
use crate::gates::{
    GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::{bigint_to_fe, decompose_bigint_option, fe_to_biguint};
use crate::{
    bigint::{
        add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
        sub_no_carry, CRTInteger, OverflowInteger,
    },
    gates::range::RangeChip,
};

use super::{FieldChip, FieldExtConstructor, FieldExtPoint, PrimeFieldChip, Selectable};

/// Represent Fp2 point as `FieldExtPoint` with degree = 2
/// `Fp2 = Fp[u] / (u^2 + 1)`
/// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
/// This means we store an Fp2 point as `a_0 + a_1 * u` where `a_0, a_1 in Fp`
pub struct Fp2Chip<'a, 'b, F: FieldExt, FpChip: PrimeFieldChip<'b, F>, Fp2: Field> {
    pub fp_chip: &'a mut FpChip,
    _f: PhantomData<&'b F>,
    _fp2: PhantomData<Fp2>,
}

impl<'a, 'b, F, FpChip, Fp2> Fp2Chip<'a, 'b, F, FpChip, Fp2>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<'b, F>,
    FpChip::FieldType: PrimeField,
    Fp2: Field + FieldExtConstructor<FpChip::FieldType, 2>,
{
    /// User must construct an `FpChip` first using a config. This is intended so everything shares a single `FlexGateChip`, which is needed for the column allocation to work.
    pub fn construct(fp_chip: &'a mut FpChip) -> Self {
        Self { fp_chip, _f: PhantomData, _fp2: PhantomData }
    }

    pub fn fp_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
        fp_point: &FpChip::FieldPoint,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error> {
        assert_eq!(a.coeffs.len(), 2);

        let mut out_coeffs = Vec::with_capacity(2);
        for c in &a.coeffs {
            let coeff = self.fp_chip.mul_no_carry(layouter, c, fp_point)?;
            out_coeffs.push(coeff);
        }
        Ok(FieldExtPoint::construct(out_coeffs))
    }

    pub fn conjugate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error> {
        assert_eq!(a.coeffs.len(), 2);

        let neg_a1 = self.fp_chip.negate(layouter, &a.coeffs[1])?;
        Ok(FieldExtPoint::construct(vec![a.coeffs[0].clone(), neg_a1]))
    }

    pub fn neg_conjugate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error> {
        assert_eq!(a.coeffs.len(), 2);

        let neg_a0 = self.fp_chip.negate(layouter, &a.coeffs[0])?;
        Ok(FieldExtPoint::construct(vec![neg_a0, a.coeffs[1].clone()]))
    }

    pub fn select(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
        b: &FieldExtPoint<FpChip::FieldPoint>,
        sel: &AssignedCell<F, F>,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error>
    where
        FpChip: Selectable<F, Point = FpChip::FieldPoint>,
    {
        let coeffs: Vec<FpChip::FieldPoint> = a
            .coeffs
            .iter()
            .zip(b.coeffs.iter())
            .map(|(a, b)| self.fp_chip.select(layouter, a, b, sel).expect("select should not fail"))
            .collect();
        Ok(FieldExtPoint::construct(coeffs))
    }
}

impl<'a, 'b, F, FpChip, Fp2> FieldChip<F> for Fp2Chip<'a, 'b, F, FpChip, Fp2>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<'b, F, WitnessType = Option<BigInt>, ConstantType = BigInt>,
    FpChip::FieldType: PrimeField,
    Fp2: Field + FieldExtConstructor<FpChip::FieldType, 2>,
{
    type ConstantType = Fp2;
    type WitnessType = Vec<Option<BigInt>>;
    type FieldPoint = FieldExtPoint<FpChip::FieldPoint>;
    type FieldType = Fp2;
    type RangeChip = FpChip::RangeChip;

    fn range(&mut self) -> &mut Self::RangeChip {
        self.fp_chip.range()
    }

    fn get_assigned_value(x: &Self::FieldPoint) -> Option<Fp2> {
        assert_eq!(x.coeffs.len(), 2);
        let c0 = FpChip::get_assigned_value(&x.coeffs[0]);
        let c1 = FpChip::get_assigned_value(&x.coeffs[1]);
        c0.zip(c1).map(|(c0, c1)| Fp2::new([c0, c1]))
    }

    fn fe_to_witness(x: &Option<Fp2>) -> Vec<Option<BigInt>> {
        match x.as_ref() {
            None => vec![None, None],
            Some(x) => {
                let coeffs = x.coeffs();
                assert_eq!(coeffs.len(), 2);
                coeffs.iter().map(|c| Some(BigInt::from(fe_to_biguint(c)))).collect()
            }
        }
    }

    fn load_private(
        &mut self,
        layouter: &mut impl Layouter<F>,
        coeffs: Vec<Option<BigInt>>,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(coeffs.len(), 2);
        let mut assigned_coeffs = Vec::with_capacity(2);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(layouter, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(Self::FieldPoint::construct(assigned_coeffs))
    }

    fn load_constant(
        &mut self,
        layouter: &mut impl Layouter<F>,
        c: Fp2,
    ) -> Result<Self::FieldPoint, Error> {
        let mut assigned_coeffs = Vec::with_capacity(2);
        for a in &c.coeffs() {
            let assigned_coeff =
                self.fp_chip.load_constant(layouter, BigInt::from(fe_to_biguint(a)))?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(Self::FieldPoint::construct(assigned_coeffs))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(a.coeffs.len(), b.coeffs.len());
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.add_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn sub_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(a.coeffs.len(), b.coeffs.len());
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.sub_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn negate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let out_coeff = self.fp_chip.negate(layouter, a_coeff)?;
            out_coeffs.push(out_coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn scalar_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: F,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.scalar_mul_no_carry(layouter, &a.coeffs[i], b)?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn scalar_mul_and_add_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
        c: F,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.scalar_mul_and_add_no_carry(
                layouter,
                &a.coeffs[i],
                &b.coeffs[i],
                c,
            )?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(a.coeffs.len(), b.coeffs.len());
        // (a_0 + a_1 * u) * (b_0 + b_1 * u) = (a_0 b_0 - a_1 b_1) + (a_0 b_1 + a_1 b_0) * u
        let mut ab_coeffs = Vec::with_capacity(a.coeffs.len() * b.coeffs.len());
        for i in 0..a.coeffs.len() {
            for j in 0..b.coeffs.len() {
                let coeff = self.fp_chip.mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j])?;
                ab_coeffs.push(coeff);
            }
        }
        let a0b0_minus_a1b1 = self.fp_chip.sub_no_carry(
            layouter,
            &ab_coeffs[0 * b.coeffs.len() + 0],
            &ab_coeffs[1 * b.coeffs.len() + 1],
        )?;
        let a0b1_plus_a1b0 = self.fp_chip.add_no_carry(
            layouter,
            &ab_coeffs[0 * b.coeffs.len() + 1],
            &ab_coeffs[1 * b.coeffs.len() + 0],
        )?;

        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        out_coeffs.push(a0b0_minus_a1b1);
        out_coeffs.push(a0b1_plus_a1b0);

        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn check_carry_mod_to_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error> {
        for coeff in &a.coeffs {
            self.fp_chip.check_carry_mod_to_zero(layouter, coeff)?;
        }
        Ok(())
    }

    fn carry_mod(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.carry_mod(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.range_check(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(())
    }

    fn is_soft_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_soft_zero(layouter, a_coeff)?;
            if let Some(p) = prev {
                let new =
                    self.fp_chip.range().gate().and(layouter, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }

    fn is_soft_nonzero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_soft_nonzero(layouter, a_coeff)?;
            if let Some(p) = prev {
                let new =
                    self.fp_chip.range().gate().or(layouter, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }

    fn is_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_zero(layouter, a_coeff)?;
            if let Some(p) = prev {
                let new =
                    self.fp_chip.range().gate().and(layouter, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }
}
