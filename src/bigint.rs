use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use crate::gates::qap_gate;

pub mod mul_no_carry;
pub mod decompose;

pub trait PolynomialInstructions<F: FieldExt> {
    type Polynomial;

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Polynomial,
        b: &Self::Polynomial,
    ) -> Result<Self::Polynomial, Error>;
}

pub trait BigIntInstructions<F: FieldExt>: PolynomialInstructions<F> {
    type BigInt;
    
    fn decompose(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &AssignedCell<F, F>
    ) -> Result<Self::BigInt, Error>;
}

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    limbs: Vec<AssignedCell<F, F>>,
    max_limb_size: BigUint,
    limb_bits: usize,
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
	limbs: Vec<AssignedCell<F, F>>,
	max_limb_size: BigUint,
	limb_bits: usize
    ) -> Self {
        Self {
            limbs,
            max_limb_size,
	    limb_bits
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fr as Fn, plonk::*,
        poly::Rotation,
    };

    use super::*;
    use crate::fields::fp::{FpChip, FpConfig};
    use crate::utils::big_to_fe;
    use num_bigint::BigUint as big_uint;

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Vec<Option<F>>,
        b: Vec<Option<F>>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            let constant = meta.fixed_column();
            FpChip::configure(meta, value, constant, 16, 64, 4)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FpChip::construct(config);
            let a_assigned = chip.load_private(layouter.namespace(|| "input a"), self.a.clone())?;
            let b_assigned = chip.load_private(layouter.namespace(|| "input b"), self.b.clone())?;
            chip.mul_no_carry(
                &mut layouter.namespace(|| "mul no carry"),
                &a_assigned,
                &b_assigned,
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_bigint() {
        let k = 7;
        let circuit = MyCircuit::<Fn> {
            a: (vec![100, 200, 300, 400])
                .iter()
                .map(|&a| Some(big_to_fe(big_uint::from(a as u64))))
                .collect(),
            b: (vec![500, 600, 700, 800])
                .iter()
                .map(|&a| Some(big_to_fe(big_uint::from(a as u64))))
                .collect(),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_bigint() {
        let k = 7;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("BigInt Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            a: vec![None, None, None, None],
            b: vec![None, None, None, None],
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
