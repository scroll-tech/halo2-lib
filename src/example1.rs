use std::marker::PhantomData;

use halo2_pairing::bigint::{MultChip, MultConfig};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
struct FunctionConfig<F: FieldExt> {
    selector: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    out: Column<Advice>,
    ab: MultConfig,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct FunctionChip<F: FieldExt> {
    config: FunctionConfig<F>,
}

impl<F: FieldExt> FunctionChip<F> {
    pub fn construct(config: FunctionConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FunctionConfig<F> {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let out = meta.advice_column();

        let ab = MultChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(a, Rotation::cur()),
            |meta| meta.query_advice(b, Rotation::cur()),
            out,
        );

        FunctionConfig {
            selector,
            a,
            b,
            out,
            ab,
            _marker: PhantomData,
        }
    }

    pub fn assign(&self, mut layouter: impl Layouter<F>, a: F, b: F) -> Result<(), Error> {
        let mult_chip = MultChip::construct(self.config.ab.clone());

        layouter.assign_region(
            || "wide mult",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", self.config.a, 0, || Ok(a))?;
                region.assign_advice(|| "b", self.config.b, 0, || Ok(b))?;
                mult_chip.assign(&mut region, 0, a, b)
            },
        )
    }
}

#[derive(Default)]
struct FunctionCircuit<F> {
    a: F,
    b: F,
}

impl<F: FieldExt> Circuit<F> for FunctionCircuit<F> {
    type Config = FunctionConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FunctionChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FunctionChip::construct(config);
        chip.assign(layouter, self.a, self.b)?;
        Ok(())
    }
}

mod tests {
    use super::FunctionCircuit;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fn};

    #[test]
    fn test_example1() {
        let k = 4;
        let circuit = FunctionCircuit::<Fn> {
            a: Fn::from(10),
            b: Fn::from(12),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_example1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout1.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Example Layout 1", ("sans-serif", 60)).unwrap();

        let circuit = FunctionCircuit::<Fn> {
            a: Fn::from(0),
            b: Fn::from(0),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
