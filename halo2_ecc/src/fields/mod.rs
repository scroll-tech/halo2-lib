use ff::PrimeField;
use halo2_base::{gates::RangeInstructions, AssignedValue, Context};
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::Value,
    plonk::Error,
};
use std::fmt::Debug;

pub mod fp;
pub mod fp12;
pub mod fp2;
pub mod fp_overflow;

#[derive(Clone, Debug)]
pub struct FieldExtPoint<FieldPoint: Clone + Debug> {
    // `F_q` field extension of `F_p` where `q = p^degree`
    // An `F_q` point consists of `degree` number of `F_p` points
    // The `F_p` points are stored as `FieldPoint`s

    // We do not specify the irreducible `F_p` polynomial used to construct `F_q` here - that is implementation specific
    pub coeffs: Vec<FieldPoint>,
    // `degree = coeffs.len()`
}

impl<FieldPoint: Clone + Debug> FieldExtPoint<FieldPoint> {
    pub fn construct(coeffs: Vec<FieldPoint>) -> Self {
        Self { coeffs }
    }
}

/// Common functionality for finite field chips
pub trait FieldChip<F: FieldExt> {
    type ConstantType: Debug;
    type WitnessType: Debug;
    type FieldPoint: Clone + Debug;
    // a type implementing `Field` trait to help with witness generation (for example with inverse)
    type FieldType: Field;
    type RangeChip: RangeInstructions<F>;

    fn range(&self) -> &Self::RangeChip;

    fn get_assigned_value(x: &Self::FieldPoint) -> Value<Self::FieldType>;

    fn fe_to_witness(x: &Value<Self::FieldType>) -> Self::WitnessType;

    fn load_private(
        &self,
        ctx: &mut Context<'_, F>,
        coeffs: Self::WitnessType,
    ) -> Result<Self::FieldPoint, Error>;

    fn load_constant(
        &self,
        ctx: &mut Context<'_, F>,
        coeffs: Self::ConstantType,
    ) -> Result<Self::FieldPoint, Error>;

    fn add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    /// output: `a + c`
    fn add_native_constant_no_carry(
        &self,
        _ctx: &mut Context<'_, F>,
        _a: &Self::FieldPoint,
        _c: F,
    ) -> Result<Self::FieldPoint, Error> {
        unimplemented!()
    }

    fn sub_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn negate(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    /// a * b
    fn scalar_mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: F,
    ) -> Result<Self::FieldPoint, Error>;

    /// a * c + b
    fn scalar_mul_and_add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
        c: F,
    ) -> Result<Self::FieldPoint, Error>;

    fn mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn check_carry_mod_to_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error>;

    fn carry_mod(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;

    fn range_check(&self, ctx: &mut Context<'_, F>, a: &Self::FieldPoint) -> Result<(), Error>;

    // Assumes the witness for a is 0
    // Constrains that the underlying big integer is 0 and < p.
    // For field extensions, checks coordinate-wise.
    fn is_soft_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedValue<F>, Error>;

    // Constrains that the underlying big integer is in [1, p - 1].
    // For field extensions, checks coordinate-wise.
    fn is_soft_nonzero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedValue<F>, Error>;

    fn is_zero(
        &self,
        _ctx: &mut Context<'_, F>,
        _a: &Self::FieldPoint,
    ) -> Result<AssignedValue<F>, Error> {
        todo!()
    }

    fn is_equal(
        &self,
        _ctx: &mut Context<'_, F>,
        _a: &Self::FieldPoint,
        _b: &Self::FieldPoint,
    ) -> Result<AssignedValue<F>, Error> {
        todo!()
    }

    fn assert_equal(
        &self,
        _ctx: &mut Context<'_, F>,
        _a: &Self::FieldPoint,
        _b: &Self::FieldPoint,
    ) -> Result<(), Error> {
        todo!()
    }

    fn mul(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let no_carry = self.mul_no_carry(ctx, a, b)?;
        self.carry_mod(ctx, &no_carry)
    }

    fn divide(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let a_val = Self::get_assigned_value(a);
        let b_val = Self::get_assigned_value(b);
        let b_inv = b_val.map(|bv| bv.invert().unwrap());
        let quot_val = a_val.zip(b_inv).map(|(a, bi)| a * bi);

        let quot = self.load_private(ctx, Self::fe_to_witness(&quot_val))?;
        self.range_check(ctx, &quot)?;

        // constrain quot * b - a = 0 mod p
        let quot_b = self.mul_no_carry(ctx, &quot, b)?;
        let quot_constraint = self.sub_no_carry(ctx, &quot_b, a)?;
        self.check_carry_mod_to_zero(ctx, &quot_constraint)?;

        Ok(quot)
    }

    // constrain and output -a / b
    // this is usually cheaper constraint-wise than computing -a and then (-a) / b separately
    fn neg_divide(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let a_val = Self::get_assigned_value(a);
        let b_val = Self::get_assigned_value(b);
        let b_inv = b_val.map(|bv| bv.invert().unwrap());
        let quot_val = a_val.zip(b_inv).map(|(a, b)| -a * b);

        let quot = self.load_private(ctx, Self::fe_to_witness(&quot_val))?;
        self.range_check(ctx, &quot)?;

        // constrain quot * b + a = 0 mod p
        let quot_b = self.mul_no_carry(ctx, &quot, b)?;
        let quot_constraint = self.add_no_carry(ctx, &quot_b, a)?;
        self.check_carry_mod_to_zero(ctx, &quot_constraint)?;

        Ok(quot)
    }
}

pub trait Selectable<F: FieldExt> {
    type Point;

    fn select(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::Point,
        b: &Self::Point,
        sel: &AssignedValue<F>,
    ) -> Result<Self::Point, Error>;

    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Vec<Self::Point>,
        coeffs: &Vec<AssignedValue<F>>,
    ) -> Result<Self::Point, Error>;
}

// Common functionality for prime field chips
pub trait PrimeFieldChip<F: FieldExt>: FieldChip<F>
where
    Self::FieldType: PrimeField,
{
    // for now there is nothing here
}

// helper trait so we can actually construct and read the Fp2 struct
// needs to be implemented for Fp2 struct for use cases below
pub trait FieldExtConstructor<Fp: PrimeField, const DEGREE: usize> {
    fn new(c: [Fp; DEGREE]) -> Self;

    fn coeffs(&self) -> Vec<Fp>;
}
