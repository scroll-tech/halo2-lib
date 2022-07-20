use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use crate::bigint::*;
use crate::gates::qap_gate;
use crate::gates::range;

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
        vec_a: Vec<Option<F>>,
        max_limb_size: BigUint,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice(
                        || "private value",
                        config.value,
                        i,
                        || a.ok_or(Error::Synthesis),
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            max_limb_size,
            self.config.limb_bits,
        ))
    }

    pub fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: Vec<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load constant",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice_from_constant(
                        || "constant value",
                        config.value,
                        i,
                        *a,
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u32) << 64,
            64,
        ))
    }

    // signed overflow BigInt functions
    pub fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        add_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        sub_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn mod_reduce(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        desired_num_limbs: usize,
        modulus: num_bigint::BigUint,
    ) -> Result<OverflowInteger<F>, Error> {
        mod_reduce::assign(&self.config.gate, layouter, a, desired_num_limbs, modulus)
    }

    pub fn check_carry_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        check_carry_to_zero::assign(&self.config.range, layouter, a)
    }

    pub fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(&self.config.range, layouter, a, &self.config.p)
    }

    // BigInt functions
    pub fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        decompose::assign(
            &self.config.range,
            layouter,
            a,
            self.config.limb_bits,
            self.config.num_limbs,
        )
    }

    pub fn big_less_than(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        big_less_than::assign(&self.config.range, layouter, a, b)
    }

    // F_p functions
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let k_a = a.limbs.len();
        let k_b = b.limbs.len();
        assert_eq!(k_a, k_b);
        let k = k_a;

        let no_carry = self.mul_no_carry(layouter, a, b)?;
        let prime_reduce = self.mod_reduce(layouter, &no_carry, k, self.config.p.clone())?;
        self.carry_mod(layouter, &prime_reduce)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fr as Fn, plonk::*,
    };
    use num_traits::One;

    use crate::fields::fp::{FpChip, FpConfig};
    use crate::utils::*;
    use num_bigint::BigInt as big_int;
    use num_bigint::BigUint as big_uint;

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Vec<Option<F>>,
        b: Vec<Option<F>>,
        c: Vec<Option<F>>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self {
                a: vec![None; 4],
                b: vec![None; 4],
                c: vec![None; 4],
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            let constant = meta.fixed_column();
            FpChip::configure(
                meta,
                value,
                constant,
                17,
                68,
                4,
                modulus::<halo2_proofs::pairing::bn256::Fq>(),
            )
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
                self.a.clone(),
                big_uint::one() << 64 - 1usize,
            )?;
            let b_assigned = chip.load_private(
                layouter.namespace(|| "input b"),
                self.b.clone(),
                big_uint::one() << 64 - 1usize,
            )?;
            let c_assigned = chip.load_private(
                layouter.namespace(|| "input c"),
                self.c.clone(),
                big_uint::one() << 64 - 1usize,
            )?;

            // test fp_multiply
            {
                chip.mul(
                    &mut layouter.namespace(|| "fp_multiply"),
                    &a_assigned,
                    &c_assigned,
                )?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_fp() {
        let k = 18;
        let circuit = MyCircuit::<Fn> {
            a: (vec![50, -3, 11, -(1 << 30)])
                .iter()
                .map(|a| Some(bigint_to_fe(&big_int::from(*a as i64))))
                .collect(),
            b: vec![
                Some(biguint_to_fe(&(big_uint::from(1u64) << 65))),
                Some(bigint_to_fe(&big_int::from(-2i64))),
                Some(Fn::from(0)),
                Some(Fn::from(0)),
            ],
            c: (vec![(1i64 << 31), 2i64, 0, 0])
                .iter()
                .map(|a| Some(bigint_to_fe(&big_int::from(*a as i64))))
                .collect(),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fp() {
        let k = 9;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout_fp_mul_68_4_lookup17_pow9.png", (1024, 1024))
            .into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fp Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            a: vec![None; 4],
            b: vec![None; 4],
            c: vec![None; 4],
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
