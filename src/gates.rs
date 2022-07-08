pub mod qap_gate;
pub mod range;

#[cfg(test)]
pub(crate) mod tests {
    use halo2_proofs::{
        arithmetic::FieldExt,
        circuit::floor_planner::V1,
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fn,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
        poly::Rotation,
    };

    use super::qap_gate::QuantumCell::*;
    use super::{qap_gate, range};

    #[derive(Debug, Clone)]
    struct MyConfig<F: FieldExt> {
        a: Column<Advice>,
        gate: qap_gate::Config<F>,
        c: Column<Fixed>,
    }

    #[derive(Debug, Clone)]
    struct MyChip<F: FieldExt> {
        config: MyConfig<F>,
    }

    impl<F: FieldExt> MyChip<F> {
        pub fn construct(config: MyConfig<F>) -> Self {
            Self { config }
        }

        pub fn configure(meta: &mut ConstraintSystem<F>) -> MyConfig<F> {
            let a = meta.advice_column();
            let gate = qap_gate::Config::configure(meta, a);
            let c = meta.fixed_column();
            meta.enable_constant(c);

            MyConfig { a, gate, c }
        }
    }

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Option<F>,
        b: Option<F>,
        c: Option<F>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            MyChip::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let (a_cell, b_cell, c_cell) = layouter.assign_region(
                || "inputs",
                |mut region| {
                    let a_cell = region.assign_advice(
                        || "a",
                        config.a,
                        0,
                        || self.a.ok_or(Error::Synthesis),
                    )?;
                    let b_cell = region.assign_advice(
                        || "b",
                        config.a,
                        1,
                        || self.b.ok_or(Error::Synthesis),
                    )?;
                    let c_cell = region.assign_advice(
                        || "c",
                        config.a,
                        2,
                        || self.c.ok_or(Error::Synthesis),
                    )?;

                    // test assign_region
                    {
                        config.gate.assign_region(
                            vec![
                                Existing(&a_cell),
                                Existing(&b_cell),
                                Existing(&c_cell),
                                Witness(
                                    &a_cell
                                        .value()
                                        .zip(b_cell.value())
                                        .zip(c_cell.value())
                                        .map(|((a, b), c)| *a + *b * *c),
                                ),
                            ],
                            3,
                            &mut region,
                        )?;
                    }
                    Ok((a_cell, b_cell, c_cell))
                },
            )?;

            // test add
            {
                config.gate.add(&mut layouter, &a_cell, &b_cell)?;
            }

            // test sub
            {
                config.gate.sub(&mut layouter, &a_cell, &b_cell)?;
            }

            // test multiply
            {
                config.gate.mul(&mut layouter, &c_cell, &b_cell)?;
            }

            // test linear
            {
                let signals = vec![a_cell, b_cell, c_cell];
                let constants = vec![F::from(1), F::from(2), F::from(3)];
                config.gate.linear(&mut layouter, &constants, &signals)?;
            }
            Ok(())
        }
    }

    #[test]
    fn test_gates() {
        let k = 6;
        let circuit = MyCircuit::<Fn> {
            a: Some(Fn::from(10)),
            b: Some(Fn::from(12)),
            c: Some(Fn::from(120)),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_gates() {
        let k = 6;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Gates Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            a: Some(Fn::zero()),
            b: Some(Fn::zero()),
            c: Some(Fn::zero()),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }

    #[derive(Default)]
    struct RangeTestCircuit<F> {
        range_bits: usize,
        lt_bits: usize,
        a: Option<F>,
        b: Option<F>,
    }

    impl<F: FieldExt> Circuit<F> for RangeTestCircuit<F> {
        type Config = range::RangeConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self {
                range_bits: self.range_bits,
                lt_bits: self.lt_bits,
                a: None,
                b: None,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let q_lookup = meta.complex_selector();
            let lookup = meta.lookup_table_column();
            let value = meta.advice_column();
            let fixed = meta.fixed_column();
            meta.enable_constant(fixed);

            let qap_config = qap_gate::Config::configure(meta, value);
            range::RangeConfig::configure(meta, q_lookup, lookup, 3, qap_config)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let (a, b) = layouter.assign_region(
                || "inputs",
                |mut region| {
                    let a = region.assign_advice(
                        || "input",
                        config.qap_config.value,
                        0,
                        || self.a.ok_or(Error::Synthesis),
                    )?;
                    let b = region.assign_advice(
                        || "input",
                        config.qap_config.value,
                        1,
                        || self.b.ok_or(Error::Synthesis),
                    )?;
                    Ok((a, b))
                },
            )?;

            {
                config.load_lookup_table(&mut layouter)?;
            }
            {
                config.range_check(&mut layouter, &a, self.range_bits)?;
            }
            {
                config.check_less_than(&mut layouter, &a, &b, self.lt_bits)?;
            }
            {
                config.is_less_than(&mut layouter, &a, &b, self.lt_bits)?;
            }
            {
                config.is_less_than(&mut layouter, &b, &a, self.lt_bits)?;
            }
            {
                config.is_equal(&mut layouter, &b, &a)?;
            }
            {
                config.is_zero(&mut layouter, &a)?;
            }
            Ok(())
        }
    }

    #[test]
    fn test_range() {
        let k = 11;
        let circuit = RangeTestCircuit::<Fn> {
            range_bits: 8,
            lt_bits: 8,
            a: Some(Fn::from(100)),
            b: Some(Fn::from(101)),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_range() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Gates Layout", ("sans-serif", 60)).unwrap();

        let circuit = RangeTestCircuit::<Fn> {
            range_bits: 8,
            lt_bits: 8,
            a: Some(Fn::from(100)),
            b: Some(Fn::from(101)),
        };

        halo2_proofs::dev::CircuitLayout::default()
            .render(7, &circuit, &root)
            .unwrap();
    }
}
