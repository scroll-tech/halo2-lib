use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

pub mod add_no_carry;
pub mod big_is_equal;
pub mod big_less_than;
pub mod carry_mod;
pub mod check_carry_mod_to_zero;
pub mod check_carry_to_zero;
pub mod decompose;
pub mod mod_reduce;
pub mod mul_no_carry;
pub mod scalar_mul_no_carry;
pub mod select;
pub mod sub_no_carry;

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    pub limbs: Vec<AssignedCell<F, F>>,
    pub max_limb_size: BigUint, // max absolute value of integer value of a limb
    pub limb_bits: usize,
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
        limbs: Vec<AssignedCell<F, F>>,
        max_limb_size: BigUint,
        limb_bits: usize,
    ) -> Self {
        Self {
            limbs,
            max_limb_size,
            limb_bits,
        }
    }

    pub fn to_bigint(&self) -> Option<BigInt> {
        self.limbs
            .iter()
            .rev()
            .fold(Some(BigInt::zero()), |acc, acell| {
                acc.zip(acell.value())
                    .map(|(acc, x)| (acc << self.limb_bits) + fe_to_bigint(x))
            })
    }
}

#[derive(Clone, Debug)]
pub struct CRTInteger<F: FieldExt> {
    // keep track of an integer `a` using CRT as `a mod 2^t` and `a mod n`
    // where `t = truncation.limbs.len() * truncation.limb_bits`
    //       `n = modulus::<Fn>`
    // `value` is the actual integer value we want to keep track of

    // we allow `value` to be a signed BigInt
    // however `value` is really an element of Z/(2^t * n), so signs are only meaningful if:
    // ASSUME `abs(value) < 2^t * n / 2`

    // the IMPLICIT ASSUMPTION: `value (mod 2^t) = truncation` && `value (mod n) = native`
    // this struct should only be used if the implicit assumption above is satisfied
    pub truncation: OverflowInteger<F>,
    pub native: AssignedCell<F, F>,
    pub value: Option<BigInt>,
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> CRTInteger<F> {
    pub fn construct(
        truncation: OverflowInteger<F>,
        native: AssignedCell<F, F>,
        value: Option<BigInt>,
        max_size: BigUint,
    ) -> Self {
        Self {
            truncation,
            native,
            value,
            max_size,
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fr as Fn, plonk::*,
        poly::Rotation,
    };
    use num_traits::One;

    use super::*;
    use crate::fields::fp::{FpChip, FpConfig};
    use crate::utils::*;
    use num_bigint::BigUint;

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
                16,
                64,
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
                BigUint::one() << 64 - 1usize,
            )?;
            let b_assigned = chip.load_private(
                layouter.namespace(|| "input b"),
                self.b.clone(),
                BigUint::one() << 64 - 1usize,
            )?;
            let c_assigned = chip.load_private(
                layouter.namespace(|| "input c"),
                self.c.clone(),
                BigUint::one() << 64 - 1usize,
            )?;

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
                let modulus = BigUint::from(17u32);
                let out = chip.mod_reduce(
                    &mut layouter.namespace(|| "mod reduce"),
                    &a_assigned,
                    2,
                    modulus.clone(),
                )?;

                let mut a_big = Some(BigUint::from(0u32));
                for (i, val) in self.a.iter().enumerate() {
                    a_big = a_big
                        .zip(*val)
                        .map(|(a, b)| a + fe_to_biguint(&b) << (32 * i));
                }
                a_big = a_big.map(|a| a % &modulus);

                let mut out_val = Some(BigUint::from(0u32));
                let mut is_none = false;
                for (i, cell) in out.limbs.iter().enumerate() {
                    out_val = out_val
                        .zip(cell.value())
                        .map(|(a, b)| a + fe_to_biguint(b) << (32 * i));
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

            // test check_carry_to_zero
            {
                chip.check_carry_to_zero(
                    &mut layouter.namespace(|| "check carry to zero"),
                    &b_assigned,
                )?;
            }

            // test carry_mod
            {
                chip.carry_mod(&mut layouter.namespace(|| "carry mod"), &a_assigned)?;
            }

            // test big_less_than
            {
                chip.big_less_than(
                    &mut layouter.namespace(|| "big_less_than"),
                    &a_assigned,
                    &c_assigned,
                )?;
            }

            Ok(())
        }
    }

    #[test]
    fn test_bigint() {
        let k = 17;
        let circuit = MyCircuit::<Fn> {
            a: (vec![50, -3, 11, -(1 << 30)])
                .iter()
                .map(|a| Some(bigint_to_fe(&BigInt::from(*a as i64))))
                .collect(),
            b: vec![
                Some(biguint_to_fe(&(BigUint::from(1u64) << 65))),
                Some(bigint_to_fe(&BigInt::from(-2i64))),
                Some(Fn::from(0)),
                Some(Fn::from(0)),
            ],
            c: (vec![(1i64 << 31), 2i64, 0, 0])
                .iter()
                .map(|a| Some(bigint_to_fe(&BigInt::from(*a as i64))))
                .collect(),
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_bigint() {
        let k = 9;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("BigInt Layout", ("sans-serif", 60)).unwrap();

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
