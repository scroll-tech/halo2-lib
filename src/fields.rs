pub mod fp;

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
            FpChip::configure(meta, value, constant, 16, 64, 4, modulus::<Fn>())
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
        let k = 17;
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

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
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
