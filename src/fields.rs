use crate::bigint::CRTInteger as FpPoint;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::Layouter,
    plonk::Error,
};

pub mod fp2;
pub mod fp_crt;
// pub mod fp_crt_vec;

#[derive(Clone, Debug)]
pub struct FqPoint<F: FieldExt> {
    // `F_q` field extension of `F_p` where `q = p^degree`
    // An `F_q` point consists of `degree` number of `F_p` points
    // We do not specify the irreducible `F_p` polynomial used to construct `F_q` here - that is implementation specific
    pub coeffs: Vec<FpPoint<F>>,
    pub degree: usize,
}

impl<F: FieldExt> FqPoint<F> {
    pub fn construct(coeffs: Vec<FpPoint<F>>, degree: usize) -> Self {
        Self { coeffs, degree }
    }
}

// Common functionality for finite field chips
pub trait FieldChip<F: FieldExt> {
    type WitnessType;
    type FieldPoint;

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

    // `Fq` is a helper type implementing the trait `Field` - currently only used for witness generation of inverse in the field
    // we don't check if `Fq` actually matches the intended field this chip is supposed to be constraining
    fn divide<Fq: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error>;
}
