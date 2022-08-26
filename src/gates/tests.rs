use halo2_proofs::{
    arithmetic::FieldExt, circuit::floor_planner::V1, circuit::*, dev::MockProver,
    pairing::bn256::Fr, plonk::*, poly::Rotation,
};

use super::{
    flex_gate::{FlexGateChip, FlexGateConfig},
    range, GateInstructions, RangeInstructions,
};
use crate::gates::QuantumCell::{self, Constant, Existing, Witness};

#[derive(Default)]
struct MyCircuit<F> {
    a: Option<F>,
    b: Option<F>,
    c: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FlexGateConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FlexGateConfig::configure(meta, 2, 1)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut chip = FlexGateChip::construct(config, true);
        let (a_cell, b_cell, c_cell) = layouter.assign_region(
            || "inputs",
            |mut region| {
                let (cells, _) = chip.assign_region(
                    vec![Witness(self.a), Witness(self.b), Witness(self.c)],
                    0,
                    &mut region,
                )?;
                Ok((cells[0].clone(), cells[1].clone(), cells[2].clone()))
            },
        )?;

        // test add
        {
            chip.add(&mut layouter, &Existing(&a_cell), &Existing(&b_cell))?;
        }

        // test sub
        {
            chip.sub(&mut layouter, &Existing(&a_cell), &Existing(&b_cell))?;
        }

        // test multiply
        {
            chip.mul(&mut layouter, &Existing(&c_cell), &Existing(&b_cell))?;
        }

        println!(
            "maximum rows used by an advice column: {}",
            chip.advice_rows.iter().max().unwrap()
        );

        let const_rows = chip.assign_and_constrain_constants(&mut layouter)?;
        println!("maximum rows used by a fixed column: {}", const_rows);
        Ok(())
    }
}

#[test]
fn test_gates() {
    let k = 6;
    let circuit =
        MyCircuit::<Fr> { a: Some(Fr::from(10)), b: Some(Fr::from(12)), c: Some(Fr::from(120)) };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[test]
fn plot_gates() {
    let k = 5;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Gates Layout", ("sans-serif", 60)).unwrap();

    let circuit = MyCircuit::<Fr> { a: Some(Fr::zero()), b: Some(Fr::zero()), c: Some(Fr::zero()) };
    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
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
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { range_bits: self.range_bits, lt_bits: self.lt_bits, a: None, b: None }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        range::RangeConfig::configure(meta, 2, 1, 1, 3)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut chip = range::RangeChip::construct(config.clone(), true);
        chip.load_lookup_table(&mut layouter)?;

        let (a, b) = layouter.assign_region(
            || "inputs",
            |mut region| {
                let (cells, _) = chip.gate_chip.assign_region(
                    vec![Witness(self.a), Witness(self.b)],
                    0,
                    &mut region,
                )?;
                Ok((cells[0].clone(), cells[1].clone()))
            },
        )?;

        {
            chip.range_check(&mut layouter, &a, self.range_bits)?;
        }
        {
            chip.check_less_than(&mut layouter, &a, &b, self.lt_bits)?;
        }
        {
            chip.is_less_than(&mut layouter, &a, &b, self.lt_bits)?;
        }
        {
            chip.is_less_than(&mut layouter, &b, &a, self.lt_bits)?;
        }
        {
            chip.is_equal(&mut layouter, &b, &a)?;
        }
        {
            chip.is_zero(&mut layouter, &a)?;
        }

        println!(
            "maximum rows used by an advice column: {}",
            chip.gate_chip.advice_rows.iter().max().unwrap()
        );

        let const_rows = chip.gate_chip.assign_and_constrain_constants(&mut layouter)?;
        println!("maximum rows used by a fixed column: {}", const_rows);
        chip.copy_and_lookup_cells(&mut layouter)?;
        println!("lookup cells used: {}", chip.cells_to_lookup.len());
        Ok(())
    }
}

#[test]
fn test_range() {
    let k = 11;
    let circuit = RangeTestCircuit::<Fr> {
        range_bits: 8,
        lt_bits: 8,
        a: Some(Fr::from(100)),
        b: Some(Fr::from(101)),
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

    let circuit = RangeTestCircuit::<Fr> {
        range_bits: 8,
        lt_bits: 8,
        a: Some(Fr::from(100)),
        b: Some(Fr::from(101)),
    };

    halo2_proofs::dev::CircuitLayout::default().render(7, &circuit, &root).unwrap();
}
