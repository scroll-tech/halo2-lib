use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    pairing::bn256::Fq,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
};
use num_bigint::{BigInt, BigUint};

use super::{FieldChip, Selectable};
use crate::gates::range;
use crate::utils::{bigint_to_fe, decompose_bigint_option, fe_to_biguint};
use crate::{
    bigint::big_is_zero,
    gates::qap_gate::QuantumCell::{Constant, Existing, Witness},
};
use crate::{bigint::sub, gates::qap_gate::QuantumCell};
use crate::{
    bigint::{
        add_no_carry, carry_mod, check_carry_mod_to_zero, inner_product, mul_no_carry,
        scalar_mul_no_carry, select, sub_no_carry, CRTInteger, FixedCRTInteger, OverflowInteger,
    },
    utils::decompose_biguint,
};
use crate::{gates::qap_gate, utils::decompose_bigint};

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt> {
    pub value: Column<Advice>,
    pub constant: Column<Fixed>,
    pub lookup: TableColumn,
    pub lookup_bits: usize,
    pub q_lookup: Selector,
    pub gate: qap_gate::Config<F>,
    pub range: range::RangeConfig<F>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
}

pub struct FpChip<F: FieldExt> {
    pub config: FpConfig<F>,
}

impl<F: FieldExt> FpChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> FpConfig<F> {
        let lookup = meta.lookup_table_column();
        let q_lookup = meta.complex_selector();
        meta.enable_equality(value);
        meta.enable_constant(constant);

        let gate_config = qap_gate::Config::configure(meta, value);
        FpConfig {
            value,
            constant,
            lookup,
            lookup_bits,
            q_lookup,
            gate: gate_config.clone(),
            range: range::RangeConfig::configure(
                meta,
                q_lookup,
                lookup,
                lookup_bits,
                gate_config.clone(),
            ),
            limb_bits,
            num_limbs,
            p,
        }
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.config.range.load_lookup_table(layouter)
    }

    pub fn load_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        a: BigInt,
    ) -> Result<CRTInteger<F>, Error> {
        let a_vec = decompose_bigint::<F>(&a, self.config.num_limbs, self.config.limb_bits);
        let (a_limbs, a_native) = layouter.assign_region(
            || "load constant",
            |mut region| {
                let a_limbs = self.config.gate.assign_region(
                    a_vec.iter().map(|v| Constant(v.clone())).collect(),
                    0,
                    &mut region,
                )?;
                let a_native = self.config.gate.assign_region(
                    vec![Constant(bigint_to_fe(&a))],
                    a_limbs.len(),
                    &mut region,
                )?;
                Ok((a_limbs, a_native[0]))
            },
        )?;

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                a_limbs,
                BigUint::from(1u64) << self.config.limb_bits,
                self.config.limb_bits,
            ),
            a_native,
            Some(a),
            (BigUint::from(1u64) << self.config.p.bits()) - 1usize,
        ))
    }
}

impl<F: FieldExt> FieldChip<F> for FpChip<F> {
    type WitnessType = Option<BigInt>;
    type FieldPoint = CRTInteger<F>;
    type FieldType = Fq;

    fn get_assigned_value(x: &CRTInteger<F>) -> Option<Fq> {
        x.value.as_ref().map(|x| bigint_to_fe::<Fq>(x))
    }

    fn fe_to_witness(x: &Option<Fq>) -> Option<BigInt> {
        x.map(|x| BigInt::from_bytes_le(num_bigint::Sign::Plus, x.to_bytes().as_ref()))
    }

    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        a: Option<BigInt>,
    ) -> Result<CRTInteger<F>, Error> {
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

        let a_native = OverflowInteger::evaluate(
            &self.config.range.qap_config,
            layouter,
            &limbs,
            self.config.limb_bits,
        )?;

        Ok(CRTInteger::construct(
            OverflowInteger::construct(
                limbs,
                BigUint::from(1u64) << self.config.limb_bits,
                self.config.limb_bits,
            ),
            a_native,
            a,
            (BigUint::from(1u64) << self.config.p.bits()) - 1usize,
        ))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        add_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        sub_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    // Input: a
    // Output: p - a if a != 0, else a
    // Assume the actual value of `a` equals `a.truncation`
    // Constrains a.truncation <= p using subtraction with carries
    fn negate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        // Compute p - a.truncation using carries
        let p = self.load_constant(layouter, BigInt::from(self.config.p))?;
        let (out_or_p, underflow) = sub::crt(&self.config.range, layouter, &p, &a)?;
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

        let a_is_zero = big_is_zero::assign(&self.config.range, layouter, &a.truncation)?;
        select::crt(&self.config.gate, layouter, a, &out_or_p, &a_is_zero)
    }

    fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: F,
    ) -> Result<CRTInteger<F>, Error> {
        scalar_mul_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        mul_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::crt(&self.config.range, layouter, a, &self.config.p)
    }

    fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        carry_mod::crt(&self.config.range, layouter, a, &self.config.p)
    }

    fn range_check(&self, layouter: &mut impl Layouter<F>, a: &CRTInteger<F>) -> Result<(), Error> {
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
            self.config.range.range_check(layouter, cell, limb_bits)?;
            index = index + 1;
        }
        Ok(())
    }
}

impl<F: FieldExt> Selectable<F> for FpChip<F> {
    type Point = CRTInteger<F>;

    fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<CRTInteger<F>, Error> {
        select::crt(&self.config.range.qap_config, layouter, a, b, sel)
    }

    fn inner_product(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Vec<CRTInteger<F>>,
        coeffs: &Vec<AssignedCell<F, F>>,
    ) -> Result<CRTInteger<F>, Error> {
        inner_product::crt(&self.config.range.qap_config, layouter, a, coeffs)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use halo2_proofs::arithmetic::BaseExt;
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq as Fp,
        pairing::bn256::Fr as Fn, plonk::*,
    };
    use num_traits::One;

    use crate::fields::fp::{FpChip, FpConfig};
    use crate::fields::FieldChip;
    use crate::utils::{fe_to_bigint, modulus};
    use num_bigint::{BigInt, BigUint};

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Option<Fp>,
        b: Option<Fp>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            let constant = meta.fixed_column();
            FpChip::configure(meta, value, constant, 17, 68, 4, modulus::<Fp>())
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FpChip::construct(config);
            chip.load_lookup_table(&mut layouter)?;

            let a_assigned =
                chip.load_private(&mut layouter, self.a.as_ref().map(|x| fe_to_bigint(x)))?;
            let b_assigned =
                chip.load_private(&mut layouter, self.b.as_ref().map(|x| fe_to_bigint(x)))?;

            // test fp_multiply
            {
                chip.mul(
                    &mut layouter.namespace(|| "fp_multiply"),
                    &a_assigned,
                    &b_assigned,
                )?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_fp_crt() {
        let k = 18;
        let a = Fp::rand();
        let b = Fp::rand();

        let circuit = MyCircuit::<Fn> {
            a: Some(a),
            b: Some(b),
            _marker: PhantomData,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fp_crt() {
        let k = 9;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout_fp_crt_mul_68_4_lookup17_pow9.png", (1024, 1024))
            .into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fp Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn>::default();
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
