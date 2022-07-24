use crate::bigint::CRTInteger;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};

pub mod fp2;
pub mod fp12;
pub mod fp_crt;
// pub mod fp_crt_vec;

#[derive(Clone, Debug)]
pub struct FqPoint<F: FieldExt> {
    // `F_q` field extension of `F_p` where `q = p^degree`
    // An `F_q` point consists of `degree` number of `F_p` points
    // The `F_p` points are stored as possibly overflow integers in CRT format

    // We do not specify the irreducible `F_p` polynomial used to construct `F_q` here - that is implementation specific
    pub coeffs: Vec<CRTInteger<F>>,
    pub degree: usize,
}

impl<F: FieldExt> FqPoint<F> {
    pub fn construct(coeffs: Vec<CRTInteger<F>>, degree: usize) -> Self {
        Self { coeffs, degree }
    }
}

// Common functionality for finite field chips
pub trait FieldChip<F: FieldExt> {
    type WitnessType;
    type FieldPoint;
    // a type implementing `Field` trait to help with witness generation (for example with inverse)
    type FieldType: Field;

    fn get_assigned_value(x: &Self::FieldPoint) -> Option<Self::FieldType>;

    fn fe_to_witness(x: &Option<Self::FieldType>) -> Self::WitnessType;

    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        coeffs: Self::WitnessType,
    ) -> Result<Self::FieldPoint, Error>;

    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: F,
    ) -> Result<Self::FieldPoint, Error>;

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error>;

    fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn range_check(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error>;

    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let no_carry = self.mul_no_carry(layouter, a, b)?;
        self.carry_mod(layouter, &no_carry)
    }

    fn divide(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let a_val = Self::get_assigned_value(a);
        let b_val = Self::get_assigned_value(b);
        let b_inv: Option<Self::FieldType> = if let Some(bv) = b_val {
            bv.invert().into()
        } else {
            None
        };
        let quot_val = a_val.zip(b_inv).map(|(a, b)| a * b);

        let quot = self.load_private(layouter, Self::fe_to_witness(&quot_val))?;
        self.range_check(layouter, &quot)?;

        // constrain quot * b - a = 0 mod p
        let quot_b = self.mul_no_carry(layouter, &quot, b)?;
        let quot_constraint = self.sub_no_carry(layouter, &quot, a)?;
        self.check_carry_mod_to_zero(layouter, &quot_constraint)?;

        Ok(quot)
    }

    // constrain and output -a / b
    // this is usually cheaper constraint-wise than computing -a and then (-a) / b separately
    fn neg_divide<Fp: FieldExt>(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let a_val = Self::get_assigned_value(a);
        let b_val = Self::get_assigned_value(b);
        let b_inv: Option<Self::FieldType> = if let Some(bv) = b_val {
            bv.invert().into()
        } else {
            None
        };
        let quot_val = a_val.zip(b_inv).map(|(a, b)| -a * b);

        let quot = self.load_private(layouter, Self::fe_to_witness(&quot_val))?;
        self.range_check(layouter, &quot)?;

        // constrain quot * b + a = 0 mod p
        let quot_b = self.mul_no_carry(layouter, &quot, b)?;
        let quot_constraint = self.add_no_carry(layouter, &quot, a)?;
        self.check_carry_mod_to_zero(layouter, &quot_constraint)?;

        Ok(quot)
    }
}

pub trait Selectable<F: FieldExt> {
    type Point;

    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Point,
        b: &Self::Point,
        sel: &AssignedCell<F, F>,
    ) -> Result<Self::Point, Error>;

    fn inner_product(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<Self::Point>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<Self::Point, Error>;
}
