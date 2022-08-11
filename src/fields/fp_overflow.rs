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
    add_no_carry, big_is_equal, big_is_zero, carry_mod, check_carry_mod_to_zero, inner_product, mul_no_carry,
    scalar_mul_no_carry, select, sub, sub_no_carry, CRTInteger, FixedCRTInteger,
    OverflowInteger,
};
use crate::fields::fp::{FpChip, FpConfig};
use crate::gates::{
    GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions
};
use crate::gates::range::{RangeChip, RangeConfig};
use crate::utils::{
    bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint, fe_to_biguint,
    modulus,
};

#[derive(Clone, Debug)]
pub struct FpOverflowChip<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> {
    pub range: RangeChip<F, NUM_ADVICE, NUM_FIXED>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
    _marker: PhantomData<Fp>,
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField>
    FpOverflowChip<F, NUM_ADVICE, NUM_FIXED, Fp>
{
    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range.load_lookup_table(layouter)
    }

    pub fn to_crt(
	&mut self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
	let a_native = OverflowInteger::evaluate(
	    self.range.gate(),
	    layouter,
	    &a.limbs,
	    a.limb_bits
	)?;
	let a_bigint = a.to_bigint();
	
	Ok(CRTInteger::construct(
	    a.clone(),
	    a_native,
	    a_bigint,
	    (BigUint::from(1u64) << self.p.bits()) - 1usize,
	))
    }
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> PrimeFieldChip<F>
    for FpOverflowChip<F, NUM_ADVICE, NUM_FIXED, Fp>
{
    type Config = FpConfig<F, NUM_ADVICE, NUM_FIXED>;

    fn construct(
        config: FpConfig<F, NUM_ADVICE, NUM_FIXED>,
        using_simple_floor_planner: bool,
    ) -> Self {
        Self {
            range: RangeChip::construct(config.range_config, using_simple_floor_planner),
            limb_bits: config.limb_bits,
            num_limbs: config.num_limbs,
            p: config.p,
            _marker: PhantomData,
        }
    }
}


impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> FieldChip<F>
    for FpOverflowChip<F, NUM_ADVICE, NUM_FIXED, Fp>
{
    type ConstantType = BigInt;
    type WitnessType = Option<BigInt>;
    type FieldPoint = OverflowInteger<F>;
    type FieldType = Fp;
    type RangeChip = RangeChip<F, NUM_ADVICE, NUM_FIXED>;

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
                let (limbs, _) = self.range.gate().assign_region(
                    a_vec.iter().map(|x| Witness(x.clone())).collect(),
                    0,
                    &mut region,
                )?;
                Ok(limbs)
            },
        )?;

        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u64) << self.limb_bits,
            self.limb_bits,
        ))
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
                let (a_limbs, _) = self.range.gate().assign_region(
                    a_vec.iter().map(|v| Constant(v.clone())).collect(),
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
                let (zero, _) =
                    self.range
                        .gate()
                        .assign_region(vec![Constant(F::from(0))], 0, &mut region)?;
                region.constrain_equal(zero[0].cell(), underflow.cell())?;
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
        check_carry_mod_to_zero::assign(&mut self.range, layouter, a, &self.p)
    }

    fn carry_mod(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(&mut self.range, layouter, a, &self.p)
    }

    fn range_check(&mut self, layouter: &mut impl Layouter<F>, a: &OverflowInteger<F>) -> Result<(), Error> {
        let n = a.limb_bits;
        let k = a.limbs.len();

        // range check limbs of `a` are in [0, 2^n)
        for cell in a.limbs.iter() {
            self.range.range_check(layouter, cell, n)?;
        }
        Ok(())
    }

    fn is_zero(
	&mut self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let carry = self.carry_mod(layouter, a)?;
	let is_carry_zero = big_is_zero::assign(self.range(), layouter, &carry)?;
	
	// underflow != 0 iff carry < p
	let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
	let (diff, underflow) = sub::assign(self.range(), layouter, &carry, &p)?;
	let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
	let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

	let res = self.range.gate().and(layouter, &Existing(&is_carry_zero), &Existing(&range_check))?;
	Ok(res)	
    }

    fn is_equal(
	&mut self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
	b: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let diff = self.sub_no_carry(layouter, a, b)?;
	let carry_res = self.carry_mod(layouter, &diff)?;
	let is_diff_zero = big_is_zero::assign(self.range(), layouter, &carry_res)?;
	
	// underflow != 0 iff res < p
	let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
	let (diff, underflow) = sub::assign(self.range(), layouter, &carry_res, &p)?;
	let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
	let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

	let res = self.range.gate().and(layouter, &Existing(&is_diff_zero), &Existing(&range_check))?;
	Ok(res)
    }
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> Selectable<F>
    for FpOverflowChip<F, NUM_ADVICE, NUM_FIXED, Fp>
{
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
