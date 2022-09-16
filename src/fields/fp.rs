use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn},
    poly::Rotation,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;
use serde::{Deserialize, Serialize};

use super::{FieldChip, PrimeFieldChip, Selectable};
use crate::{
    bigint::{
        add_no_carry, big_is_equal, big_is_zero, big_less_than, carry_mod, check_carry_mod_to_zero,
        inner_product, mul_no_carry, scalar_mul_and_add_no_carry, scalar_mul_no_carry, select, sub,
        sub_no_carry, BigIntConfig, BigIntStrategy, CRTInteger, FixedCRTInteger, OverflowInteger,
    },
    gates::QuantumCell::{Constant, Existing, Witness},
    gates::{
        range::{RangeConfig, RangeStrategy},
        Context, GateInstructions, QuantumCell, RangeInstructions,
    },
    utils::{
        bigint_to_fe, decompose_bigint, decompose_bigint_option, decompose_biguint,
        decompose_biguint_to_biguints, fe_to_biguint, modulus,
    },
};

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub enum FpStrategy {
    Simple,
    CustomVerticalShort,
}

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt, Fp: PrimeField> {
    pub range: RangeConfig<F>,
    pub bigint_chip: BigIntConfig<F>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
    _marker: PhantomData<Fp>,
}

use crate::bigint::GATE_LEN;

impl<F: FieldExt, Fp: PrimeField> FpConfig<F, Fp> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        strategy: FpStrategy,
        num_advice: usize,
        num_lookup_advice: usize,
        num_fixed: usize,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> Self {
        let range = RangeConfig::<F>::configure(
            meta,
            match strategy {
                FpStrategy::Simple => RangeStrategy::Vertical,
                FpStrategy::CustomVerticalShort => RangeStrategy::CustomVerticalShort,
            },
            num_advice,
            num_lookup_advice,
            num_fixed,
            lookup_bits,
        );
        let mut constant_vecs = Vec::new();
        if strategy == FpStrategy::CustomVerticalShort {
            let p_limbs = decompose_biguint_to_biguints(&p, num_limbs, limb_bits);
            for i in 0..num_limbs {
                if i < GATE_LEN {
                    constant_vecs.push(p_limbs[0..=i].into());
                } else {
                    let shift = (i - 1) % (GATE_LEN - 2);
                    constant_vecs
                        .push([&[BigUint::from(1u64)], &p_limbs[(i - shift)..=i]].concat());
                }
            }
            let k_chunks = (num_limbs - 1 + GATE_LEN - 3) / (GATE_LEN - 2);
            for i in 0..k_chunks {
                if i == 0 {
                    constant_vecs.push(
                        (0..std::cmp::min(num_limbs, GATE_LEN - 1))
                            .map(|j| BigUint::from(1u64) << (j * limb_bits))
                            .collect(),
                    );
                } else {
                    constant_vecs.push(
                        [
                            &[BigUint::from(1u64)],
                            &((1 + i * (GATE_LEN - 2))
                                ..std::cmp::min(1 + (i + 1) * (GATE_LEN - 2), num_limbs))
                                .map(|j| BigUint::from(1u64) << (j * limb_bits))
                                .collect::<Vec<BigUint>>()[..],
                        ]
                        .concat(),
                    );
                }
            }
        }

        let bigint_chip = BigIntConfig::<F>::configure(
            meta,
            match strategy {
                FpStrategy::Simple => BigIntStrategy::Simple,
                FpStrategy::CustomVerticalShort => BigIntStrategy::CustomVerticalShort,
            },
            limb_bits,
            num_limbs,
            &range.gate,
            constant_vecs,
        );
        FpConfig { range, bigint_chip, limb_bits, num_limbs, p, _marker: PhantomData }
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.range.load_lookup_table(layouter)
    }

    pub fn finalize(&self, ctx: &mut Context<'_, F>) -> Result<(usize, usize, usize), Error> {
        self.range.finalize(ctx)
    }
}

impl<F: FieldExt, Fp: PrimeField> PrimeFieldChip<F> for FpConfig<F, Fp> {}

impl<F: FieldExt, Fp: PrimeField> FieldChip<F> for FpConfig<F, Fp> {
    type ConstantType = BigInt;
    type WitnessType = Option<BigInt>;
    type FieldPoint = CRTInteger<F>;
    type FieldType = Fp;
    type RangeChip = RangeConfig<F>;

    fn range(&self) -> &Self::RangeChip {
        &self.range
    }

    fn get_assigned_value(x: &CRTInteger<F>) -> Option<Fp> {
        x.value.as_ref().map(|x| bigint_to_fe::<Fp>(x))
    }

    fn fe_to_witness(x: &Option<Fp>) -> Option<BigInt> {
        x.map(|x| BigInt::from(fe_to_biguint(&x)))
    }

    fn load_private(
        &self,
        ctx: &mut Context<'_, F>,
        a: Option<BigInt>,
    ) -> Result<CRTInteger<F>, Error> {
        let a_vec = decompose_bigint_option::<F>(&a, self.num_limbs, self.limb_bits);
        let limbs = self.range.gate().assign_region_smart(
            ctx,
            a_vec.iter().map(|x| Witness(x.clone())).collect(),
            vec![],
            vec![],
            vec![],
        )?;

        let a_native = OverflowInteger::evaluate(
            self.range.gate(),
            &self.bigint_chip,
            ctx,
            &limbs,
            self.limb_bits,
        )?;

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                limbs,
                BigUint::from(1u64) << self.limb_bits,
                self.limb_bits,
                &self.p - 1usize,
            ),
            a_native,
            a,
        ))
    }

    fn load_constant(&self, ctx: &mut Context<'_, F>, a: BigInt) -> Result<CRTInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.num_limbs, self.limb_bits);
        let (a_limbs, a_native) = {
            let mut a_vec: Vec<QuantumCell<F>> =
                a_vec.iter().map(|v| Constant(v.clone())).collect();
            a_vec.push(Constant(bigint_to_fe(&a)));
            let mut a_cells =
                self.range.gate().assign_region_smart(ctx, a_vec, vec![], vec![], vec![])?;
            let a_native = a_cells.pop().unwrap();
            (a_cells, a_native)
        };

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                a_limbs,
                BigUint::from(1u64) << self.limb_bits,
                self.limb_bits,
                &self.p - 1usize,
            ),
            a_native,
            Some(a),
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        add_no_carry::crt(self.range.gate(), ctx, a, b)
    }

    fn sub_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        sub_no_carry::crt(self.range.gate(), ctx, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(&self, ctx: &mut Context<'_, F>, a: &CRTInteger<F>) -> Result<CRTInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (out_or_p, underflow) = sub::crt(self.range(), ctx, &p, &a)?;
        // constrain underflow to equal 0
        ctx.constants_to_assign.push((F::from(0), Some(underflow.cell())));

        let a_is_zero = big_is_zero::assign(self.range(), ctx, &a.truncation)?;
        select::crt(self.range.gate(), ctx, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: F,
    ) -> Result<CRTInteger<F>, Error> {
        scalar_mul_no_carry::crt(self.range.gate(), ctx, a, b)
    }

    fn scalar_mul_and_add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
        c: F,
    ) -> Result<CRTInteger<F>, Error> {
        scalar_mul_and_add_no_carry::crt(self.range.gate(), ctx, a, b, c)
    }

    fn mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        mul_no_carry::crt(self.range.gate(), &self.bigint_chip, ctx, a, b)
    }

    fn check_carry_mod_to_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::crt(self.range(), &self.bigint_chip, ctx, a, &self.p)
    }

    fn carry_mod(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        carry_mod::crt(self.range(), &self.bigint_chip, ctx, a, &self.p)
    }

    fn range_check(&self, ctx: &mut Context<'_, F>, a: &CRTInteger<F>) -> Result<(), Error> {
        let n = a.truncation.limb_bits;
        let k = a.truncation.limbs.len();
        assert!(a.truncation.max_size.bits() as usize <= n * k);
        let last_limb_bits = a.truncation.max_size.bits() as usize - n * (k - 1);
        assert!(last_limb_bits > 0);

        if a.value != None {
            assert!(a.value.clone().unwrap().bits() <= a.truncation.max_size.bits());
        }

        // range check limbs of `a` are in [0, 2^n) except last limb should be in [0, 2^last_limb_bits)
        let mut index: usize = 0;
        for cell in a.truncation.limbs.iter() {
            let limb_bits = if index == k - 1 { last_limb_bits } else { n };
            self.range.range_check(ctx, cell, limb_bits)?;
            index = index + 1;
        }
        Ok(())
    }

    fn is_soft_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero = big_is_zero::crt(self.range(), ctx, a)?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::crt(self.range(), ctx, a, &p)?;
        let is_underflow_zero = self.range.is_zero(ctx, &underflow)?;
        let range_check = self.range.gate().not(ctx, &Existing(&is_underflow_zero))?;

        let res = self.range.gate().and(ctx, &Existing(&is_zero), &Existing(&range_check))?;
        Ok(res)
    }

    fn is_soft_nonzero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero = big_is_zero::crt(self.range(), ctx, a)?;
        let is_nonzero = self.range.gate().not(ctx, &Existing(&is_zero))?;

        // underflow != 0 iff carry < p
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::crt(self.range(), ctx, a, &p)?;
        let is_underflow_zero = self.range.is_zero(ctx, &underflow)?;
        let range_check = self.range.gate().not(ctx, &Existing(&is_underflow_zero))?;

        let res = self.range.gate().and(ctx, &Existing(&is_nonzero), &Existing(&range_check))?;
        Ok(res)
    }

    // constrain the witness `a` to be `< p`
    // then check if `a` is 0
    fn is_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // underflow != 0 iff carry < p
        let p = self.load_constant(ctx, BigInt::from(self.p.clone()))?;
        let (diff, underflow) = sub::crt(self.range(), ctx, a, &p)?;
        let is_underflow_zero = self.range.is_zero(ctx, &underflow)?;

        self.range.gate.assign_region_smart(
            ctx,
            vec![Constant(F::from(0))],
            vec![],
            vec![],
            vec![(&is_underflow_zero, 0)],
        )?;

        big_is_zero::crt(self.range(), ctx, a)
    }
}

impl<F: FieldExt, Fp: PrimeField> Selectable<F> for FpConfig<F, Fp> {
    type Point = CRTInteger<F>;

    fn select(
        &self,
        ctx: &mut Context<'_, F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<CRTInteger<F>, Error> {
        select::crt(self.range.gate(), ctx, a, b, sel)
    }

    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Vec<CRTInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<CRTInteger<F>, Error> {
        inner_product::crt(self.range.gate(), ctx, a, coeffs)
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

    use crate::fields::fp::FpConfig;
    use crate::fields::{FieldChip, PrimeFieldChip};
    use crate::gates::flex_gate::GateStrategy;
    use crate::gates::range::RangeConfig;
    use crate::gates::{Context, ContextParams, RangeInstructions};
    use crate::utils::{fe_to_bigint, modulus};
    use num_bigint::{BigInt, BigUint};

    use super::FpStrategy;

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Option<Fq>,
        b: Option<Fq>,
        _marker: PhantomData<F>,
    }

    const NUM_ADVICE: usize = 1;
    const NUM_FIXED: usize = 1;

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F, Fq>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            FpConfig::configure(
                meta,
                FpStrategy::Simple,
                NUM_ADVICE,
                1,
                NUM_FIXED,
                22,
                88,
                3,
                modulus::<Fq>(),
            )
        }

        fn synthesize(
            &self,
            chip: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            chip.load_lookup_table(&mut layouter)?;

            let using_simple_floor_planner = true;
            let mut first_pass = true;

            layouter.assign_region(
                || "fp",
                |region| {
                    if first_pass && using_simple_floor_planner {
                        first_pass = false;
                        return Ok(());
                    }

                    let mut aux = Context::new(
                        region,
                        ContextParams {
                            num_advice: NUM_ADVICE,
                            using_simple_floor_planner,
                            first_pass,
                        },
                    );
                    let ctx = &mut aux;

                    let a_assigned =
                        chip.load_private(ctx, self.a.as_ref().map(|x| fe_to_bigint(x)))?;
                    let b_assigned =
                        chip.load_private(ctx, self.b.as_ref().map(|x| fe_to_bigint(x)))?;

                    // test fp_multiply
                    {
                        chip.mul(ctx, &a_assigned, &b_assigned)?;
                    }

                    println!("Using {} advice columns and {} fixed columns", NUM_ADVICE, NUM_FIXED);
                    println!(
                        "maximum rows used by an advice column: {}",
                        ctx.advice_rows.iter().max().unwrap()
                    );
                    // IMPORTANT: this assigns all constants to the fixed columns
                    // This is not optional.
                    let (const_rows, _, _) = chip.finalize(ctx)?;
                    println!("maximum rows used by a fixed column: {}", const_rows);
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn test_fp() {
        let k = 23;
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
