use std::io::ErrorKind;

use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell::{Constant, Existing};
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::Error,
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
pub mod inner_product;
pub mod mod_reduce;
pub mod mul_no_carry;
pub mod negative;
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

    pub fn evaluate(
        config: &qap_gate::Config<F>,
        layouter: &mut impl Layouter<F>,
        limbs: &Vec<AssignedCell<F, F>>,
        limb_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let k = limbs.len();
        let n = limb_bits;
        let mut pows = Vec::with_capacity(k);
        let mut running_pow = F::from(1);
        let limb_base: F = biguint_to_fe(&(BigUint::from(1u32) << n));
        for i in 0..k {
            pows.push(Constant(running_pow));
            running_pow = running_pow * &limb_base;
        }
        // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
        let (_, _, native) = config.inner_product(
            layouter,
            &limbs.iter().map(|a| Existing(a)).collect(),
            &pows,
        )?;
        Ok(native)
    }
}

#[derive(Clone, Debug)]
pub struct FixedOverflowInteger<F: FieldExt> {
    pub limbs: Vec<F>,
    pub max_limb_size: BigUint, // max absolute value of integer value of a limb
    pub limb_bits: usize,
}

impl<F: FieldExt> FixedOverflowInteger<F> {
    pub fn construct(
        limbs: Vec<F>,
        max_limb_size: BigUint,	
        limb_bits: usize,
    ) -> Self {
        Self {
            limbs,
            max_limb_size,
            limb_bits,
        }
    }

    pub fn from_native(
	value: BigInt,
	num_limbs: usize,
	limb_bits: usize,
    ) -> Self {
	let limbs = decompose_bigint(&value, num_limbs, limb_bits);
	Self {
	    limbs,
	    max_limb_size: BigUint::from(1u64) << limb_bits,
	    limb_bits
	}
    }

    pub fn assign(
	&self,
	config: &qap_gate::Config<F>,
	layouter: &mut impl Layouter<F>,
    ) -> Result<OverflowInteger<F>, Error> {
	let assigned_limbs = layouter.assign_region(
	    || "assign limbs",
	    |mut region| {
		let limb_cells = self.limbs.iter().map(|x| Constant(*x)).collect();
		let limb_cells_assigned = config.assign_region(limb_cells, 0, &mut region)?;
		Ok(limb_cells_assigned)
	    }
	)?;
	let assigned = OverflowInteger::construct(
	    assigned_limbs,
	    self.max_limb_size.clone(),
	    self.limb_bits
	);
	Ok(assigned)
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

#[derive(Clone, Debug)]
pub struct FixedCRTInteger<F: FieldExt> {
    // keep track of an integer `a` using CRT as `a mod 2^t` and `a mod n`
    // where `t = truncation.limbs.len() * truncation.limb_bits`
    //       `n = modulus::<Fn>`
    // `value` is the actual integer value we want to keep track of

    // we allow `value` to be a signed BigInt
    // however `value` is really an element of Z/(2^t * n), so signs are only meaningful if:
    // ASSUME `abs(value) < 2^t * n / 2`

    // the IMPLICIT ASSUMPTION: `value (mod 2^t) = truncation` && `value (mod n) = native`
    // this struct should only be used if the implicit assumption above is satisfied
    pub truncation: FixedOverflowInteger<F>,
    pub native: F,
    pub value: BigInt,
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> FixedCRTInteger<F> {
    pub fn construct(
        truncation: FixedOverflowInteger<F>,
        native: F,
        value: BigInt,
        max_size: BigUint,
    ) -> Self {
        Self {
            truncation,
            native,
            value,
            max_size,
        }
    }

    pub fn from_native(
	value: BigInt,
	num_limbs: usize,
	limb_bits: usize
    ) -> Self {
	let truncation = FixedOverflowInteger::from_native(value.clone(), num_limbs, limb_bits);
	Self {
	    truncation,
	    native: bigint_to_fe(&value),
	    value: value,
	    max_size: BigUint::from(1u64) << limb_bits,
	}
    }
    
    pub fn assign(
	&self,
	config: &qap_gate::Config<F>,
	layouter: &mut impl Layouter<F>,
    ) -> Result<CRTInteger<F>, Error> {
	let assigned_truncation = self.truncation.assign(config, layouter)?;
	let assigned_native = layouter.assign_region(
	    || "assign native",
	    |mut region| {
		let native_cells = vec![Constant(self.native)];
		let native_cells_assigned = config.assign_region(native_cells, 0, &mut region)?;
		Ok(native_cells_assigned[0].clone())		    
	    }
	)?;
	let assigned = CRTInteger::construct(
	    assigned_truncation,
	    assigned_native,
	    Some(self.value.clone()),
	    self.max_size.clone()
	);
	Ok(assigned)
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
