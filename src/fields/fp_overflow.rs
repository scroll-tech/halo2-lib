use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use super::{FieldChip, PrimeFieldChip, Selectable};
use crate::bigint::{
    add_no_carry, big_is_equal, big_is_zero, carry_mod, check_carry_mod_to_zero, inner_product,
    mul_no_carry, scalar_mul_no_carry, select, sub, sub_no_carry, CRTInteger, FixedCRTInteger,
    OverflowInteger,
};
use crate::fields::fp::{FpChip, FpConfig};
use crate::gates::range::{RangeChip, RangeConfig};
use crate::gates::{
    GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::{
    bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint, fe_to_biguint,
    modulus,
};

#[derive(Debug)]
pub struct FpOverflowChip<'a, F: FieldExt, Fp: PrimeField> {
    pub range: &'a mut RangeChip<F>,
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
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        let a_native =
            OverflowInteger::evaluate(self.range.gate(), layouter, &a.limbs, a.limb_bits)?;
        let a_bigint = a.to_bigint();

        Ok(CRTInteger::construct(
            a.clone(),
            a_native,
            a_bigint,
            (BigUint::from(1u64) << self.p.bits()) - 1usize,
        ))
    }

    pub fn from_fp_chip(
        range: &'a mut RangeChip<F>,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> Self {
        Self { range, limb_bits, num_limbs, p, _marker: PhantomData }
    }
}

impl<'a, F: FieldExt, Fp: PrimeField> PrimeFieldChip<'a, F> for FpOverflowChip<'a, F, Fp> {
    type Config = FpConfig<F>;
    type RangeChipType = RangeChip<F>;

    fn construct(
        config: FpConfig<F>,
        range_chip: &'a mut RangeChip<F>,
        using_simple_floor_planner: bool,
    ) -> Self {
        Self {
            range: range_chip,
            limb_bits: config.limb_bits,
            num_limbs: config.num_limbs,
            p: config.p,
            _marker: PhantomData,
        }
    }
}

impl<'a, F: FieldExt, Fp: PrimeField> FieldChip<F> for FpOverflowChip<'a, F, Fp> {
    type ConstantType = BigInt;
    type WitnessType = Option<BigInt>;
    type FieldPoint = OverflowInteger<F>;
    type FieldType = Fp;
    type RangeChip = RangeChip<F>;

    fn range(&mut self) -> &mut Self::RangeChip {
        &mut self.range
    }

    fn get_assigned_value(x: &OverflowInteger<F>) -> Option<Fp> {
        x.to_bigint().as_ref().map(|x| bigint_to_fe::<Fp>(x))
    }

    fn fe_to_witness(x: &Option<Fp>) -> Option<BigInt> {
        x.map(|x| BigInt::from(fe_to_biguint(&x)))
    }

    fn load_private(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: Option<BigInt>,
    ) -> Result<OverflowInteger<F>, Error> {
        let a_vec = decompose_bigint_option(&a, self.num_limbs, self.limb_bits);
        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let limbs = self.range.gate().assign_region_smart(
                    a_vec.iter().map(|x| Witness(x.clone())).collect(),
                    vec![],
                    vec![],
                    vec![],
                    0,
                    &mut region,
                )?;
                Ok(limbs)
            },
        )?;

        Ok(OverflowInteger::construct(limbs, BigUint::from(1u64) << self.limb_bits, self.limb_bits))
    }

    fn load_constant(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: BigInt,
    ) -> Result<OverflowInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.num_limbs, self.limb_bits);
        let a_limbs = layouter.assign_region(
            || "load constant",
            |mut region| {
                let a_limbs = self.range.gate().assign_region_smart(
                    a_vec.iter().map(|v| Constant(v.clone())).collect(),
                    vec![],
                    vec![],
                    vec![],
                    0,
                    &mut region,
                )?;
                Ok(a_limbs)
            },
        )?;

        Ok(OverflowInteger::construct(
            a_limbs,
            BigUint::from(1u64) << self.limb_bits,
            self.limb_bits,
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        add_no_carry::assign(self.range.gate(), layouter, a, b)
    }

    fn sub_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        sub_no_carry::assign(self.range.gate(), layouter, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
        let (out_or_p, underflow) = sub::assign(self.range(), layouter, &p, &a)?;
        layouter.assign_region(
            || "fp negate no underflow",
            |mut region| {
                let zero = self.range.gate().assign_region_smart(
                    vec![Constant(F::from(0))],
                    vec![],
                    vec![],
                    vec![(&underflow, 0)],
                    0,
                    &mut region,
                )?;
                Ok(())
            },
        )?;

        let a_is_zero = big_is_zero::assign(self.range(), layouter, a)?;
        select::assign(self.range.gate(), layouter, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: F,
    ) -> Result<OverflowInteger<F>, Error> {
        scalar_mul_no_carry::assign(self.range.gate(), layouter, a, b)
    }

    fn mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        mul_no_carry::assign(self.range.gate(), layouter, a, b)
    }

    fn check_carry_mod_to_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::assign(self.range, layouter, a, &self.p)
    }

    fn carry_mod(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(self.range, layouter, a, &self.p)
    }

    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        let n = a.limb_bits;
        let k = a.limbs.len();

        // range check limbs of `a` are in [0, 2^n)
        for cell in a.limbs.iter() {
            self.range.range_check(layouter, cell, n)?;
        }
        Ok(())
    }

    fn is_soft_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_carry_zero = big_is_zero::assign(self.range(), layouter, a)?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::assign(self.range(), layouter, a, &p)?;
        let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
        let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

        let res =
            self.range.gate().and(layouter, &Existing(&is_carry_zero), &Existing(&range_check))?;
        Ok(res)
    }

    fn is_soft_nonzero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero = big_is_zero::assign(self.range(), layouter, a)?;
        let is_nonzero = self.range.gate().not(layouter, &Existing(&is_zero))?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::assign(self.range(), layouter, a, &p)?;
        let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
        let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

        let res =
            self.range.gate().and(layouter, &Existing(&is_nonzero), &Existing(&range_check))?;
        Ok(res)
    }
}

impl<'a, F: FieldExt, Fp: PrimeField> Selectable<F> for FpOverflowChip<'a, F, Fp> {
    type Point = OverflowInteger<F>;

    fn select(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        select::assign(self.range.gate(), layouter, a, b, sel)
    }

    fn inner_product(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<OverflowInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<OverflowInteger<F>, Error> {
        inner_product::assign(self.range.gate(), layouter, a, coeffs)
    }
}
