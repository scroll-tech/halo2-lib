use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use super::{FieldChip, PrimeFieldChip, Selectable};
use crate::{
    bigint::{
        add_no_carry, big_is_equal, big_is_zero, big_less_than, carry_mod, check_carry_mod_to_zero, inner_product, mul_no_carry,
        scalar_mul_no_carry, select, sub, sub_no_carry, CRTInteger, FixedCRTInteger,
        OverflowInteger,
    },
    gates::QuantumCell::{Constant, Existing, Witness},
    gates::{
        range::{RangeChip, RangeConfig},
        GateInstructions, QuantumCell, RangeInstructions,
    },
    utils::{
        bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint, fe_to_biguint,
        modulus,
    },
};

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize> {
    pub range_config: RangeConfig<F, NUM_ADVICE, NUM_FIXED>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize>
    FpConfig<F, NUM_ADVICE, NUM_FIXED>
{
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> Self {
        FpConfig {
            range_config: RangeConfig::<F, NUM_ADVICE, NUM_FIXED>::configure(meta, lookup_bits),
            limb_bits,
            num_limbs,
            p,
        }
    }
}

#[derive(Debug)]
pub struct FpChip<'a, F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> {
    pub range: &'a mut RangeChip<F, NUM_ADVICE, NUM_FIXED>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
    _marker: PhantomData<Fp>,
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField>
    FpChip<'_, F, NUM_ADVICE, NUM_FIXED, Fp>
{
    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range.load_lookup_table(layouter)
    }
}

impl<'a, F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> PrimeFieldChip<'a, F>
    for FpChip<'a, F, NUM_ADVICE, NUM_FIXED, Fp>
{
    type Config = FpConfig<F, NUM_ADVICE, NUM_FIXED>;
    type RangeChipType = RangeChip<F, NUM_ADVICE, NUM_FIXED>;

    fn construct(
        config: FpConfig<F, NUM_ADVICE, NUM_FIXED>,
	range_chip: &'a mut RangeChip<F, NUM_ADVICE, NUM_FIXED>,
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

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> FieldChip<F>
    for FpChip<'_, F, NUM_ADVICE, NUM_FIXED, Fp>
{
    type ConstantType = BigInt;
    type WitnessType = Option<BigInt>;
    type FieldPoint = CRTInteger<F>;
    type FieldType = Fp;
    type RangeChip = RangeChip<F, NUM_ADVICE, NUM_FIXED>;

    fn range(&mut self) -> &mut Self::RangeChip {
        &mut self.range
    }

    fn get_assigned_value(x: &CRTInteger<F>) -> Option<Fp> {
        x.value.as_ref().map(|x| bigint_to_fe::<Fp>(x))
    }

    fn fe_to_witness(x: &Option<Fp>) -> Option<BigInt> {
        x.map(|x| BigInt::from(fe_to_biguint(&x)))
    }

    fn load_private(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: Option<BigInt>,
    ) -> Result<CRTInteger<F>, Error> {
        let a_vec = decompose_bigint_option::<F>(&a, self.num_limbs, self.limb_bits);
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

        let a_native =
            OverflowInteger::evaluate(self.range.gate(), layouter, &limbs, self.limb_bits)?;

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                limbs,
                BigUint::from(1u64) << self.limb_bits,
                self.limb_bits,
            ),
            a_native,
            a,
            (BigUint::from(1u64) << self.p.bits()) - 1usize,
        ))
    }

    fn load_constant(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: BigInt,
    ) -> Result<CRTInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.num_limbs, self.limb_bits);
        let (a_limbs, a_native) = layouter.assign_region(
            || "load constant",
            |mut region| {
                let mut a_vec: Vec<QuantumCell<F>> =
                    a_vec.iter().map(|v| Constant(v.clone())).collect();
                a_vec.push(Constant(bigint_to_fe(&a)));
                let (mut a_cells, _) = self.range.gate().assign_region(a_vec, 0, &mut region)?;
                let a_native = a_cells.pop().unwrap();
                Ok((a_cells, a_native))
            },
        )?;

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                a_limbs,
                BigUint::from(1u64) << self.limb_bits,
                self.limb_bits,
            ),
            a_native,
            Some(a),
            (BigUint::from(1u64) << self.p.bits()) - 1usize,
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        add_no_carry::crt(self.range.gate(), layouter, a, b)
    }

    fn sub_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        sub_no_carry::crt(self.range.gate(), layouter, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
        let (out_or_p, underflow) = sub::crt(self.range, layouter, &p, &a)?;
        // constrain underflow to equal 0
        self.range.gate().constants_to_assign.push((F::from(0), Some(underflow.cell())));

        let a_is_zero = big_is_zero::assign(self.range, layouter, &a.truncation)?;
        select::crt(self.range.gate(), layouter, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: F,
    ) -> Result<CRTInteger<F>, Error> {
        scalar_mul_no_carry::crt(self.range.gate(), layouter, a, b)
    }

    fn mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        mul_no_carry::crt(self.range.gate(), layouter, a, b)
    }

    fn check_carry_mod_to_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::crt(self.range, layouter, a, &self.p)
    }

    fn carry_mod(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        carry_mod::crt(self.range, layouter, a, &self.p)
    }

    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<(), Error> {
        let n = a.truncation.limb_bits;
        let k = a.truncation.limbs.len();
        assert!(a.max_size.bits() as usize <= n * k);
        let last_limb_bits = a.max_size.bits() as usize - n * (k - 1);
        assert!(last_limb_bits > 0);

        if a.value != None {
            assert!(a.value.clone().unwrap().bits() <= a.max_size.bits());
        }

        // range check limbs of `a` are in [0, 2^n) except last limb should be in [0, 2^last_limb_bits)
        let mut index: usize = 0;
        for cell in a.truncation.limbs.iter() {
            let limb_bits = if index == k - 1 { last_limb_bits } else { n };
            self.range.range_check(layouter, cell, limb_bits)?;
            index = index + 1;
        }
        Ok(())
    }

    fn is_soft_zero(
	&mut self,
	layouter: &mut impl Layouter<F>,
	a: &CRTInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let is_zero = big_is_zero::crt(self.range, layouter, a)?;

	// underflow != 0 iff carry < p
	let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
	let (diff, underflow) = sub::crt(self.range, layouter, a, &p)?;
	let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
	let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

	let res = self.range.gate().and(layouter, &Existing(&is_zero), &Existing(&range_check))?;
	Ok(res)
    }

    fn is_soft_nonzero(
	&mut self,
	layouter: &mut impl Layouter<F>,
	a: &CRTInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let is_zero = big_is_zero::crt(self.range, layouter, a)?;
	let is_nonzero = self.range.gate().not(layouter, &Existing(&is_zero))?;

	// underflow != 0 iff carry < p
	let p = self.load_constant(layouter, BigInt::from(self.p.clone()))?;
	let (diff, underflow) = sub::crt(self.range, layouter, a, &p)?;
	let is_underflow_zero = self.range.is_zero(layouter, &underflow)?;
	let range_check = self.range.gate().not(layouter, &Existing(&is_underflow_zero))?;

	let res = self.range.gate().and(layouter, &Existing(&is_nonzero), &Existing(&range_check))?;
	Ok(res)
    }
}

impl<F: FieldExt, const NUM_ADVICE: usize, const NUM_FIXED: usize, Fp: PrimeField> Selectable<F>
    for FpChip<'_, F, NUM_ADVICE, NUM_FIXED, Fp>
{
    type Point = CRTInteger<F>;

    fn select(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<CRTInteger<F>, Error> {
        select::crt(self.range.gate(), layouter, a, b, sel)
    }

    fn inner_product(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<CRTInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<CRTInteger<F>, Error> {
        inner_product::crt(self.range.gate(), layouter, a, coeffs)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use halo2_proofs::arithmetic::BaseExt;
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq, pairing::bn256::Fr,
        plonk::*,
    };
    use num_traits::One;

    use crate::fields::fp::{FpChip, FpConfig};
    use crate::fields::{FieldChip, PrimeFieldChip};
    use crate::gates::RangeInstructions;
    use crate::gates::range::RangeChip;
    use crate::utils::{fe_to_bigint, modulus};
    use num_bigint::{BigInt, BigUint};

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Option<Fq>,
        b: Option<Fq>,
        _marker: PhantomData<F>,
    }

    const NUM_ADVICE: usize = 2;
    const NUM_FIXED: usize = 2;

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F, NUM_ADVICE, NUM_FIXED>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            FpConfig::configure(meta, 17, 68, 4, modulus::<Fq>())
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
	    let mut range_chip = RangeChip::<F, NUM_ADVICE, NUM_FIXED>::construct(config.range_config.clone(), true);
            let mut chip = FpChip::<F, NUM_ADVICE, NUM_FIXED, Fq>::construct(config, &mut range_chip, true);
            chip.load_lookup_table(&mut layouter)?;

            let a_assigned =
                chip.load_private(&mut layouter, self.a.as_ref().map(|x| fe_to_bigint(x)))?;
            let b_assigned =
                chip.load_private(&mut layouter, self.b.as_ref().map(|x| fe_to_bigint(x)))?;

            // test fp_multiply
            {
                chip.mul(&mut layouter.namespace(|| "fp_multiply"), &a_assigned, &b_assigned)?;
            }

            println!("Using {} advice columns and {} fixed columns", NUM_ADVICE, NUM_FIXED);
            println!(
                "maximum rows used by an advice column: {}",
                chip.range.gate().advice_rows.iter().max().unwrap()
            );
            // IMPORTANT: this assigns all constants to the fixed columns
            // This is not optional.
            let const_rows = chip.range.gate().assign_and_constrain_constants(&mut layouter)?;
            println!("maximum rows used by a fixed column: {}", const_rows);
            Ok(())
        }
    }

    #[test]
    fn test_fp() {
        let k = 18;
        let a = Fq::rand();
        let b = Fq::rand();

        let circuit = MyCircuit::<Fr> { a: Some(a), b: Some(b), _marker: PhantomData };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fp() {
        let k = 9;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fp Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fr>::default();
        halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
    }
}
