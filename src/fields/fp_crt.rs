use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::{BigInt, BigUint};

use crate::bigint::*;
use crate::gates::qap_gate;
use crate::gates::range;
use crate::utils::bigint_to_fe;
use crate::utils::decompose_bigint_option;

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

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<BigInt>,
        num_limbs: usize,
    ) -> Result<CRTInteger<F>, Error> {
        let config = &self.config;

        let a_vec = decompose_bigint_option(&a, num_limbs, self.config.limb_bits);
        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let mut limbs = Vec::with_capacity(num_limbs);
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
            &mut layouter,
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
    pub fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        add_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    pub fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        sub_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    pub fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: F,
    ) -> Result<CRTInteger<F>, Error> {
        scalar_mul_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    pub fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        mul_no_carry::crt(&self.config.gate, layouter, a, b)
    }

    pub fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<(), Error> {
        check_carry_mod_to_zero::crt(&self.config.range, layouter, a, &self.config.p)
    }

    pub fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        carry_mod::crt(&self.config.range, layouter, a, &self.config.p)
    }

    pub fn range_check(
        &self,
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
            self.config.range.range_check(layouter, cell, limb_bits)?;
            index = index + 1;
        }
        Ok(())
    }

    // F_p functions
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &CRTInteger<F>,
        b: &CRTInteger<F>,
    ) -> Result<CRTInteger<F>, Error> {
        let k_a = a.truncation.limbs.len();
        let k_b = b.truncation.limbs.len();
        assert_eq!(k_a, k_b);
        let k = k_a;

        let no_carry = self.mul_no_carry(layouter, a, b)?;
        self.carry_mod(layouter, &no_carry)
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

    use crate::fields::fp_crt::{FpChip, FpConfig};
    use crate::utils::{fp_to_bigint, modulus as native_modulus};
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
            FpChip::configure(meta, value, constant, 17, 68, 4, native_modulus::<Fp>())
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FpChip::construct(config);
            chip.load_lookup_table(&mut layouter)?;

            let a_assigned = chip.load_private(
                layouter.namespace(|| "input a"),
                self.a.as_ref().map(|x| fp_to_bigint(x)),
                chip.config.num_limbs,
            )?;
            let b_assigned = chip.load_private(
                layouter.namespace(|| "input b"),
                self.b.as_ref().map(|x| fp_to_bigint(x)),
                chip.config.num_limbs,
            )?;

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
