use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_traits::One;

use crate::{gates::qap_gate, utils::*};

pub mod add_no_carry;
pub mod check_carry_to_zero;
pub mod decompose;
pub mod mod_reduce;
pub mod mul_no_carry;

pub trait PolynomialInstructions<F: FieldExt> {
    type Polynomial;

    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Polynomial,
        b: &Self::Polynomial,
    ) -> Result<Self::Polynomial, Error>;

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
        a: &AssignedCell<F, F>,
    ) -> Result<Self::BigInt, Error>;
}

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    limbs: Vec<AssignedCell<F, F>>,
    max_limb_size: big_uint,
    limb_bits: usize,
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
        limbs: Vec<AssignedCell<F, F>>,
        max_limb_size: big_uint,
        limb_bits: usize,
    ) -> Self {
        Self {
            limbs,
            max_limb_size,
            limb_bits,
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
    use crate::utils::*;
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
            FpChip::configure(meta, value, constant, 16, 32, 4)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FpChip::construct(config);
            chip.load_lookup_table(&mut layouter)?;
            let a_assigned = chip.load_private(layouter.namespace(|| "input a"), self.a.clone())?;
            let b_assigned = chip.load_private(layouter.namespace(|| "input b"), self.b.clone())?;

            // test mul_no_carry
            {
                chip.mul_no_carry(
                    &mut layouter.namespace(|| "mul no carry"),
                    &a_assigned,
                    &b_assigned,
                )?;
            }

            // test add_no_carry
            {
                chip.add_no_carry(
                    &mut layouter.namespace(|| "add no carry"),
                    &a_assigned,
                    &b_assigned,
                )?;
            }

            // test mod_reduce
            {
                let modulus = big_uint::from(17u32);
                let out = chip.mod_reduce(
                    &mut layouter.namespace(|| "mod reduce"),
                    &a_assigned,
                    2,
                    modulus.clone(),
                )?;

                let mut a_big = Some(big_uint::from(0u32));
                for (i, val) in self.a.iter().enumerate() {
		    a_big = a_big.zip(*val).map(|(a, b)| a + fe_to_big(&b) << (32 * i));
                }
                a_big = a_big.map(|a| a % &modulus);

                let mut out_val = Some(big_uint::from(0u32));
		let mut is_none = false;
                for (i, cell) in out.limbs.iter().enumerate() {
		    out_val = out_val
                        .zip(cell.value())
                        .map(|(a, b)| a + fe_to_big(b) << (32 * i));                 
                    out_val = out_val.map(|a| a % &modulus);		    

		    if cell.value().is_none() {
			is_none = true;
		    }
		}
		if !is_none {		    		    
		    assert_eq!(a_big, out_val);
		}
            }

            // test decompose
            {
                let decomposition = chip.decompose(
                    &mut layouter.namespace(|| "decompose"),
                    &b_assigned.limbs[0],
                )?;
            }

            /*
            // test check_carry_to_zero
            {
                chip.check_carry_to_zero(
                    &mut layouter.namespace(|| "check carry to zero"),
                    &b_assigned,
                )?;
            }
            */
            Ok(())
        }
    }

    #[test]
    fn test_bigint() {
        let k = 17;
        let circuit = MyCircuit::<Fn> {
            a: (vec![100, 200, 300, 400])
                .iter()
                .map(|a| Some(big_to_fe(&big_uint::from(*a as u64))))
                .collect(),
            b: (vec![(1i64 << 32) + 1i64, 0, 0, 0])
                .iter()
                .map(|a| Some(signed_big_to_fe(&big_int::from(*a as i64))))
                .collect(),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_bigint() {
        let k = 17;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("BigInt Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            a: (vec![100, 200, 300, 400])
                .iter()
                .map(|a| Some(big_to_fe(&big_uint::from(*a as u64))))
                .collect(),
            b: (vec![(1i64 << 32) + 1i64, 0, 0, 0])
                .iter()
                .map(|a| Some(signed_big_to_fe(&big_int::from(*a as i64))))
                .collect(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
