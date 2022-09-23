use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Layouter, Value},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, Signed};

use super::{FieldChip, PrimeFieldChip, Selectable};
use crate::bigint::{
    add_no_carry, big_is_equal, big_is_zero, carry_mod, check_carry_mod_to_zero, inner_product,
    mul_no_carry, scalar_mul_and_add_no_carry, scalar_mul_no_carry, select, sub, sub_no_carry,
    BigIntConfig, CRTInteger, FixedCRTInteger, OverflowInteger,
};
use crate::fields::fp::FpConfig;
use crate::gates::range::RangeConfig;
use crate::gates::{
    Context, GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::{
    bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint, fe_to_biguint,
    modulus,
};

#[derive(Debug)]
pub struct FpOverflowChip<'a, F: FieldExt, Fp: PrimeField> {
    pub range: &'a RangeConfig<F>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
    _marker: PhantomData<Fp>,
}

impl<'a, F: FieldExt, Fp: PrimeField> FpOverflowChip<'a, F, Fp> {
    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range.load_lookup_table(layouter)
    }

    pub fn to_crt(
        &self,
        ctx: &mut Context<F>,
        a: &OverflowInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        let a_native = OverflowInteger::evaluate(
            self.range.gate(),
            &BigIntConfig::default(),
            ctx,
            &a.limbs,
            a.limb_bits,
        )?;
        let a_bigint = a.to_bigint();

        Ok(CRTInteger::construct(a.clone(), a_native, a_bigint))
    }

    pub fn construct(
        range: &'a RangeConfig<F>,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> Self {
        Self { range, limb_bits, num_limbs, p, _marker: PhantomData }
    }
}

impl<'a, F: FieldExt, Fp: PrimeField> PrimeFieldChip<F> for FpOverflowChip<'a, F, Fp> {}

impl<'a, F: FieldExt, Fp: PrimeField> FieldChip<F> for FpOverflowChip<'a, F, Fp> {
    type ConstantType = BigInt;
    type WitnessType = Value<BigInt>;
    type FieldPoint = OverflowInteger<F>;
    type FieldType = Fp;
    type RangeChip = RangeConfig<F>;

    fn range(&self) -> &Self::RangeChip {
        self.range
    }

    fn get_assigned_value(x: &OverflowInteger<F>) -> Value<Fp> {
        x.to_bigint().as_ref().map(|x| bigint_to_fe::<Fp>(x))
    }

    fn fe_to_witness(x: &Value<Fp>) -> Value<BigInt> {
        x.map(|x| BigInt::from(fe_to_biguint(&x)))
    }

    fn load_private(
        &self,
        ctx: &mut Context<'_, F>,
        a: Value<BigInt>,
    ) -> Result<OverflowInteger<F>, Error> {
        let a_vec = decompose_bigint_option(&a, self.num_limbs, self.limb_bits);
        let limbs = self.range.gate().assign_region_smart(
            ctx,
            a_vec.iter().map(|x| Witness(x.clone())).collect(),
            vec![],
            vec![],
            vec![],
        )?;

        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u64) << self.limb_bits,
            self.limb_bits,
            &self.p - 1usize,
        ))
    }

    fn load_constant(
        &self,
        ctx: &mut Context<'_, F>,
        a: BigInt,
    ) -> Result<OverflowInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.num_limbs, self.limb_bits);
        let a_limbs = self.range.gate().assign_region_smart(
            ctx,
            a_vec.iter().map(|v| Constant(v.clone())).collect(),
            vec![],
            vec![],
            vec![],
        )?;

        Ok(OverflowInteger::construct(
            a_limbs,
            BigUint::from(1u64) << self.limb_bits,
            self.limb_bits,
            a.abs().to_biguint().unwrap(),
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        add_no_carry::assign(self.range.gate(), ctx, a, b)
    }

    fn sub_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        sub_no_carry::assign(self.range.gate(), ctx, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (out_or_p, underflow) = sub::assign(self.range(), ctx, &p, &a)?;
        ctx.constants_to_assign.push((F::from(0), Some(underflow.cell())));

        let a_is_zero = big_is_zero::assign(self.range(), ctx, a)?;
        select::assign(self.range.gate(), ctx, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: F,
    ) -> Result<OverflowInteger<F>, Error> {
        scalar_mul_no_carry::assign(self.range.gate(), ctx, a, b)
    }

    fn scalar_mul_and_add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
        c: F,
    ) -> Result<OverflowInteger<F>, Error> {
        scalar_mul_and_add_no_carry::assign(self.range.gate(), ctx, a, b, c)
    }

    fn mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        mul_no_carry::assign(self.range.gate(), ctx, a, b)
    }

    fn check_carry_mod_to_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::assign(self.range, ctx, a, &self.p)
    }

    fn carry_mod(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(self.range, ctx, a, &self.p, self.num_limbs)
    }

    fn range_check(&self, ctx: &mut Context<'_, F>, a: &OverflowInteger<F>) -> Result<(), Error> {
        let n = a.limb_bits;
        let k = a.limbs.len();

        // range check limbs of `a` are in [0, 2^n)
        for cell in a.limbs.iter() {
            self.range.range_check(ctx, cell, n)?;
        }
        Ok(())
    }

    fn is_soft_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_carry_zero = big_is_zero::assign(self.range(), ctx, a)?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::assign(self.range(), ctx, a, &p)?;
        let is_underflow_zero = self.range.is_zero(ctx, &underflow)?;
        let range_check = self.range.gate().not(ctx, &Existing(&is_underflow_zero))?;

        let res = self.range.gate().and(ctx, &Existing(&is_carry_zero), &Existing(&range_check))?;
        Ok(res)
    }

    fn is_soft_nonzero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero = big_is_zero::assign(self.range(), ctx, a)?;
        let is_nonzero = self.range.gate().not(ctx, &Existing(&is_zero))?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::assign(self.range(), ctx, a, &p)?;
        let is_underflow_zero = self.range.is_zero(ctx, &underflow)?;
        let range_check = self.range.gate().not(ctx, &Existing(&is_underflow_zero))?;

        let res = self.range.gate().and(ctx, &Existing(&is_nonzero), &Existing(&range_check))?;
        Ok(res)
    }
}

impl<'a, F: FieldExt, Fp: PrimeField> Selectable<F> for FpOverflowChip<'a, F, Fp> {
    type Point = OverflowInteger<F>;

    fn select(
        &self,
        ctx: &mut Context<'_, F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        select::assign(self.range.gate(), ctx, a, b, sel)
    }

    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Vec<OverflowInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<OverflowInteger<F>, Error> {
        inner_product::assign(self.range.gate(), ctx, a, coeffs)
    }
}
