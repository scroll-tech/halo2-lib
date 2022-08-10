use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use super::{FieldChip, Selectable};
use crate::bigint::{
    add_no_carry, big_is_equal, big_is_zero, carry_mod, check_carry_mod_to_zero, inner_product, mul_no_carry,
    scalar_mul_no_carry, select, sub, sub_no_carry, CRTInteger, FixedCRTInteger,
    OverflowInteger,
};
use crate::fields::fp::{FpChip, FpConfig};
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell::{Constant, Existing};
use crate::gates::range;
use crate::utils::{
    bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint, fe_to_biguint,
    modulus,
};

pub struct FpOverflowChip<F: FieldExt, Fp: PrimeField> {
    pub config: FpConfig<F>,
    _marker: PhantomData<Fp>,
}

impl<F: FieldExt, Fp: PrimeField> FpOverflowChip<F, Fp> {
    pub fn construct(config: FpConfig<F>) -> Self {
	Self {
	    config,
	    _marker: PhantomData,
	}
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.config.range.load_lookup_table(layouter)
    }

    pub fn load_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        a: BigInt,
    ) -> Result<OverflowInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.config.num_limbs, self.config.limb_bits);
        let a_limbs = layouter.assign_region(
            || "load constant",
            |mut region| {
                let a_limbs = self.config.gate.assign_region(
                    a_vec.iter().map(|v| Constant(v.clone())).collect(),
                    0,
                    &mut region,
                )?;
                Ok(a_limbs)
            },
        )?;

        Ok(OverflowInteger::construct(
            a_limbs,
            BigUint::from(1u64) << self.config.limb_bits,
            self.config.limb_bits,
        ))
    }

    pub fn to_crt(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
	let a_native = OverflowInteger::evaluate(
	    &self.config.gate,
	    layouter,
	    &a.limbs,
	    a.limb_bits
	)?;
	let a_bigint = a.to_bigint();
	
	Ok(CRTInteger::construct(
	    a.clone(),
	    a_native,
	    a_bigint,
	    (BigUint::from(1u64) << self.config.p.bits()) - 1usize,
	))
    }
}

impl<F: FieldExt, Fp: PrimeField> FieldChip<F> for FpOverflowChip<F, Fp> {
    type WitnessType = Option<BigInt>;
    type FieldPoint = OverflowInteger<F>;
    type FieldType = Fp;

    fn get_assigned_value(x: &OverflowInteger<F>) -> Option<Fp> {
        x.to_bigint().as_ref().map(|x| bigint_to_fe::<Fp>(x))
    }

    fn fe_to_witness(x: &Option<Fp>) -> Option<BigInt> {
        x.map(|x| BigInt::from(fe_to_biguint(&x)))
    }

    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        a: Option<BigInt>,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let a_vec = decompose_bigint_option(&a, self.config.num_limbs, self.config.limb_bits);
        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let mut limbs = Vec::with_capacity(self.config.num_limbs);
                for (i, a_val) in a_vec.iter().enumerate() {
                    let limb = region.assign_advice(
                        || "private value",
                        config.value,
                        i,
                        || a_val.ok_or(Error::Synthesis),
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;

        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u64) << self.config.limb_bits,
            self.config.limb_bits,
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        add_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        sub_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(layouter, BigInt::from(self.config.p.clone()))?;
        let (out_or_p, underflow) = sub::assign(&self.config.range, layouter, &p, &a)?;
        layouter.assign_region(
            || "fp negate no underflow",
            |mut region| {
                let zero =
                    self.config
                        .gate
                        .assign_region(vec![Constant(F::from(0))], 0, &mut region)?;
                region.constrain_equal(zero[0].cell(), underflow.cell())?;
                Ok(())
            },
        )?;

        let a_is_zero = big_is_zero::assign(&self.config.range, layouter, a)?;
        select::assign(&self.config.gate, layouter, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: F,
    ) -> Result<OverflowInteger<F>, Error> {
        scalar_mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::assign(&self.config.range, layouter, a, &self.config.p)
    }

    fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(&self.config.range, layouter, a, &self.config.p)
    }

    fn range_check(&self, layouter: &mut impl Layouter<F>, a: &OverflowInteger<F>) -> Result<(), Error> {
        let n = a.limb_bits;
        let k = a.limbs.len();

        // range check limbs of `a` are in [0, 2^n)
        for cell in a.limbs.iter() {
            self.config.range.range_check(layouter, cell, n)?;
        }
        Ok(())
    }

    fn is_zero(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	println!("0.a");
	let carry = self.carry_mod(layouter, a)?;

	println!("0.ab");
	let is_carry_zero = big_is_zero::assign(&self.config.range, layouter, &carry)?;

	println!("0.b");

	// underflow != 0 iff carry < p
	let p = self.load_constant(layouter, BigInt::from(self.config.p.clone()))?;
	let (diff, underflow) = sub::assign(&self.config.range, layouter, &carry, &p)?;
	let is_underflow_zero = self.config.range.is_zero(layouter, &underflow)?;
	let range_check = self.config.gate.not(layouter, &Existing(&is_underflow_zero))?;

	println!("0.c");
	let res = self.config.gate.and(layouter, &Existing(&is_carry_zero), &Existing(&range_check))?;
	Ok(res)	
    }

    fn is_equal(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &OverflowInteger<F>,
	b: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let diff = self.sub_no_carry(layouter, a, b)?;
	let carry_res = self.carry_mod(layouter, &diff)?;
	let is_diff_zero = big_is_zero::assign(&self.config.range, layouter, &carry_res)?;
	
	// underflow != 0 iff res < p
	let p = self.load_constant(layouter, BigInt::from(self.config.p.clone()))?;
	let (diff, underflow) = sub::assign(&self.config.range, layouter, &carry_res, &p)?;
	let is_underflow_zero = self.config.range.is_zero(layouter, &underflow)?;
	let range_check = self.config.gate.not(layouter, &Existing(&is_underflow_zero))?;

	let res = self.config.gate.and(layouter, &Existing(&is_diff_zero), &Existing(&range_check))?;
	Ok(res)
    }
}

impl<F: FieldExt, Fp: PrimeField> Selectable<F> for FpOverflowChip<F, Fp> {
    type Point = OverflowInteger<F>;

    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        select::assign(&self.config.range.qap_config, layouter, a, b, sel)
    }

    fn inner_product(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<OverflowInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<OverflowInteger<F>, Error> {
        inner_product::assign(&self.config.range.qap_config, layouter, a, coeffs)
    }
}
