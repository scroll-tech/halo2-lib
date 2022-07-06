pub mod qap_gate;
pub mod range;

#[cfg(test)]
pub(crate) mod tests {
    use halo2_proofs::{
        arithmetic::FieldExt,
        circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fn,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
        poly::Rotation,
    };

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
        a: F,
        b: F,
        c: F,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

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
                    let a_cell = region.assign_advice(|| "a", config.a, 0, || Ok(self.a))?;
                    let b_cell = region.assign_advice(|| "b", config.a, 1, || Ok(self.b))?;
                    let c_cell = region.assign_advice(|| "c", config.a, 2, || Ok(self.c))?;

                    // test basic gate
                    {
                        config.gate.assign_region(
                            a_cell.value().map(|a| *a),
                            b_cell.value().map(|a| *a),
                            c_cell.value().map(|a| *a),
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
        let k = 5;
        let circuit = MyCircuit::<Fn> {
            a: Fn::from(10),
            b: Fn::from(12),
            c: Fn::from(120),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_gates() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Gates Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            a: Fn::zero(),
            b: Fn::zero(),
            c: Fn::zero(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(5, &circuit, &root)
            .unwrap();
    }

    
    #[derive(Default)]
    struct RangeTestCircuit<F> {
	range_bits: usize,
	input: F,
    }

    impl<F: FieldExt> Circuit<F> for RangeTestCircuit<F> {
        type Config = range::RangeConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
	    let q_lookup = meta.complex_selector();
	    let lookup = meta.lookup_table_column();
	    let value = meta.advice_column();
	    let fixed = meta.fixed_column();
	    meta.enable_constant(fixed);
	    
	    let qap_config = qap_gate::Config::configure(
		meta,
		value,
	    );
            range::RangeConfig::configure(
		meta,
		q_lookup,
		lookup,
		3,
		qap_config,
	    )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
	    let input = layouter.assign_region(
		|| "inputs",
		|mut region| {
		    region.assign_advice_from_constant(|| "input", config.qap_config.value, 0, self.input)
		})?;
	    {
		config.load_lookup_table(&mut layouter);
	    }
	    {
		config.range_check(
		    &mut layouter,
		    &input,
		    self.range_bits)
	    }
        }
    }
    
    #[test]
    fn test_range() {
        let k = 10;
        let circuit = RangeTestCircuit::<Fn> {
	    range_bits: 9,
	    input: Fn::from(100)
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
	    range_bits: 9,
	    input: Fn::from(100)
        };
	

        halo2_proofs::dev::CircuitLayout::default()
            .render(5, &circuit, &root)
            .unwrap();
    }    
}
