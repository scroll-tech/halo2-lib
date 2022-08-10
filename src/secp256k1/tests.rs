#![allow(non_snake_case)]
#![feature(explicit_generic_args_with_impl_trait)]
use std::marker::PhantomData;

use super::{FpChip, FqOverflowChip, Secp256k1Chip, SECP_B};
use crate::{
    ecc::{fixed::FixedEccPoint, ecdsa_verify_no_pubkey_check},
    fields::{fp::FpConfig, FieldChip},
    gates::qap_gate::QuantumCell::Witness,
    utils::{bigint_to_fe, biguint_to_fe, decompose_biguint_option, fe_to_biguint, modulus},
};
use ff::{Field, PrimeField};
use halo2_proofs::circuit::floor_planner::*;
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt}, circuit::*, dev::MockProver, pairing::bn256::Fr, plonk::*,
};
use halo2curves::{
    secp256k1::{Fp, Fq, Secp256k1, Secp256k1Affine}
};
use num_bigint::{BigInt, BigUint};
use rand_core::OsRng;

#[derive(Default)]
pub struct MyCircuit<F> {
    pub P: Option<Secp256k1Affine>,
    pub scalar: Option<Fq>,
    pub _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct Secp256k1Config<F: FieldExt, CF: PrimeField, SF: PrimeField> {
    pub base_config: FpConfig<F>,
    pub scalar_config: FpConfig<F>,
    _marker: PhantomData<CF>,
    _marker2: PhantomData<SF>,
}

impl<F: FieldExt, CF: PrimeField, SF: PrimeField> Secp256k1Config<F, CF, SF> {
    pub fn configure(
	meta: &mut ConstraintSystem<F>,
	value: Column<Advice>,
	constant: Column<Fixed>,
	lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
    ) -> Secp256k1Config<F, CF, SF> {
	let base_config = FpConfig::<F>::configure(
	    meta,
	    value,
	    constant,
	    lookup_bits,
	    limb_bits,
	    num_limbs,
	    modulus::<CF>()
	);
	let scalar_config = FpConfig::<F>::configure(
	    meta,
	    value,
	    constant,
	    lookup_bits,
	    limb_bits,
	    num_limbs,
	    modulus::<CF>()
	);
	Secp256k1Config {
	    base_config,
	    scalar_config,
	    _marker: PhantomData,
	    _marker2: PhantomData
	}
    }
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = Secp256k1Config<F, Fp, Fq>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        Secp256k1Config::configure(meta, value, constant, 22, 88, 3)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let fp_chip = FpChip::construct(config.base_config.clone());
        fp_chip.load_lookup_table(&mut layouter)?;
        let range = fp_chip.config.range.clone();

	let fq_chip = FqOverflowChip::construct(config.scalar_config.clone());
	fq_chip.load_lookup_table(&mut layouter)?;
	
	let G = Secp256k1Affine::generator();
	let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
	let pk = Secp256k1Affine::from(G * sk);
	let pk_fixed = FixedEccPoint::from_g1(&pk, config.base_config.num_limbs, config.base_config.limb_bits);
	let pk_assigned = pk_fixed.assign(&fp_chip, &mut layouter)?;
	
	let msg_hash = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
	let m_assigned = fq_chip.load_private(&mut layouter, FqOverflowChip::<F>::fe_to_witness(&Some(msg_hash)))?;
	
	let k = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
	let k_inv = k.invert().unwrap();

	let r_point = Secp256k1Affine::from(G * k).coordinates().unwrap();
	let x = r_point.x();
	let x_bigint = FpChip::<F>::fe_to_witness(&Some(*x));
	let r = x_bigint.as_ref().map(|xv| bigint_to_fe::<Fq>(xv)).unwrap();
	let s = k_inv * (msg_hash + (r * sk));

	println!("{:?} {:?}", r, s);
	
	let r_assigned = fq_chip.load_private(&mut layouter, FqOverflowChip::<F>::fe_to_witness(&Some(r)))?;
	let s_assigned = fq_chip.load_private(&mut layouter, FqOverflowChip::<F>::fe_to_witness(&Some(s)))?;

	println!("r_assigned: {:?} s_assigned: {:?} m_assigned: {:?} pk_assigned x: {:?} y: {:?}",
		 r_assigned,
		 s_assigned,
		 m_assigned,
		 pk_assigned.x,
		 pk_assigned.y,
	);
	
	// test ECDSA
	{
	    let ecdsa = ecdsa_verify_no_pubkey_check::<F, Fp, Fq, Secp256k1Affine>(
		&fp_chip,
		&fq_chip,
		&range,
		&mut layouter.namespace(|| "ecdsa"),
		&pk_assigned,
		&r_assigned,
		&s_assigned,
		&m_assigned,
		F::from(7),
		4,
		10
	    )?;
	}
	println!("ecdsa done");
	
        let chip = Secp256k1Chip::construct(fp_chip, range.clone());	
        let P_assigned = chip.load_private(
            &mut layouter,
            match self.P {
                Some(P) => (Some(P.x), Some(P.y)),
                None => (None, None),
            },
        )?;

        let mut pt = Secp256k1Affine::default();
        let mut P_fixed = FixedEccPoint::from_g1(&pt, config.base_config.num_limbs, config.base_config.limb_bits);
        if let Some(P_point) = &self.P {
            pt = P_point.clone();
            P_fixed = FixedEccPoint::from_g1(&P_point, config.base_config.num_limbs, config.base_config.limb_bits);
        }

        let scalar_bigint = self.scalar.map(|x| fe_to_biguint(&x));
        let mask = (BigUint::from(1u32) << 128) - 1usize;
        let scalar0 = scalar_bigint.clone().map(|x| biguint_to_fe(&(x & mask)));
        let scalar1 = scalar_bigint.map(|x| biguint_to_fe(&(x >> 128)));
        let scalar_cells = layouter.assign_region(
            || "load scalar",
            |mut region| {
                chip.field_chip.config.gate.assign_region(
                    vec![Witness(scalar0), Witness(scalar1)],
                    0,
                    &mut region,
                )
            },
        )?;
	
        // test scalar mult
        {
            let scalar_mult = chip.scalar_mult(
                &mut layouter.namespace(|| "scalar_mult"),
                &P_assigned,
                &vec![scalar_cells[0].clone(), scalar_cells[1].clone()],
                F::from(SECP_B),
                128,
                4,
            )?;
            assert_eq!(scalar_mult.x.truncation.to_bigint(), scalar_mult.x.value);
            assert_eq!(scalar_mult.y.truncation.to_bigint(), scalar_mult.y.value);
            if self.P != None {
                let actual = Secp256k1Affine::from(&self.P.unwrap() * self.scalar.unwrap());
                assert_eq!(actual.x, bigint_to_fe(&scalar_mult.x.value.unwrap()));
                assert_eq!(actual.y, bigint_to_fe(&scalar_mult.y.value.unwrap()));
                println!("scalar mult witness OK");
            }
        }

        // test fixed base scalar mult
        {
            let fixed_base_scalar_mult = chip.fixed_base_scalar_mult(
                &mut layouter.namespace(|| "fixed_base_scalar_mult"),
                &P_fixed,
                &vec![scalar_cells[0].clone(), scalar_cells[1].clone()],
                F::from(SECP_B),
                128,
                4,
            )?;
            assert_eq!(
                fixed_base_scalar_mult.x.truncation.to_bigint(),
                fixed_base_scalar_mult.x.value
            );
            assert_eq!(
                fixed_base_scalar_mult.y.truncation.to_bigint(),
                fixed_base_scalar_mult.y.value
            );
            if self.P != None {
                let actual = Secp256k1Affine::from(pt * self.scalar.unwrap());
                assert_eq!(actual.x, bigint_to_fe(&fixed_base_scalar_mult.x.value.unwrap()));
                assert_eq!(actual.y, bigint_to_fe(&fixed_base_scalar_mult.y.value.unwrap()));
                println!("fixed base scalar mult witness OK");
            }
        }

        Ok(())
    }
}

#[cfg(test)]
#[test]
fn test_secp() {
    let k = 23;
    let mut rng = rand::thread_rng();

    let P = Some(Secp256k1Affine::random(&mut rng));
    let scalar = Some(Fq::random(&mut rng));

    let circuit = MyCircuit::<Fr> { P, scalar, _marker: PhantomData };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[cfg(test)]
#[test]
fn plot_ecc() {
    let k = 12;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Secp256k1 Layout", ("sans-serif", 60)).unwrap();

    let circuit = MyCircuit::<Fr>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
