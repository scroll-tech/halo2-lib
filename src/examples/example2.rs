use std::marker::PhantomData;

use crate::mult::{MultChip, MultConfig};
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
        let out = meta.advice_column();

        let ab = MultChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(a, Rotation::cur()),
            |meta| meta.query_advice(a, Rotation::next()),
            out,
        );

        FunctionConfig {
            selector,
            a,
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
                region.assign_advice(|| "b", self.config.a, 1, || Ok(b))?;
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
    fn test_example2() {
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
    fn plot_example2() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout2.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Example Layout 2", ("sans-serif", 60)).unwrap();

        let circuit = FunctionCircuit::<Fn> {
            a: Fn::from(0),
            b: Fn::from(0),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
