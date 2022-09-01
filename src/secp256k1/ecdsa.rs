#![allow(non_snake_case)]
use seq_macro::seq;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use ff::{Field, PrimeField};
use halo2_proofs::circuit::floor_planner::*;
use halo2_proofs::pairing::bn256::{Bn256, G1Affine};
use halo2_proofs::pairing::group::Group;
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::*,
    dev::MockProver,
    pairing::bn256::Fr,
    plonk::*,
    transcript::{Blake2bWrite, Challenge255},
};
use halo2curves::secp256k1::{Fp, Fq, Secp256k1, Secp256k1Affine};
use num_bigint::{BigInt, BigUint};
use rand_core::OsRng;

use super::{FpChip, FqOverflowChip, Secp256k1Chip, SECP_B};
use crate::{
    ecc::{ecdsa_verify_no_pubkey_check, fixed::FixedEccPoint, EccChip},
    fields::{fp::FpConfig, FieldChip, PrimeFieldChip},
    gates::{
        flex_gate::GateStrategy,
        range::{RangeChip, RangeConfig},
        GateInstructions,
        QuantumCell::Witness,
        RangeInstructions,
    },
    utils::{bigint_to_fe, biguint_to_fe, decompose_biguint_option, fe_to_biguint, modulus},
};

#[macro_export]
macro_rules! create_ecdsa_circuit {
    ($gate_strategy:expr, $num_advice:expr, $num_lookup_advice:expr, $num_fixed:expr, $lookup_bits:expr, $limb_bits:expr, $num_limbs:expr) => {
        pub struct ECDSACircuit<F> {
            pub r: Option<Fq>,
            pub s: Option<Fq>,
            pub msghash: Option<Fq>,
            pub pk: Option<Secp256k1Affine>,
            pub G: Secp256k1Affine,
            pub _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Default for ECDSACircuit<F> {
            fn default() -> Self {
                Self {
                    r: None,
                    s: None,
                    msghash: None,
                    pk: None,
                    G: Secp256k1Affine::generator(),
                    _marker: PhantomData,
                }
            }
        }

        impl<F: FieldExt> Circuit<F> for ECDSACircuit<F> {
            type Config = RangeConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                RangeConfig::configure(meta, $gate_strategy, $num_advice, $num_lookup_advice, $num_fixed, $lookup_bits)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let mut range_chip = RangeChip::<F>::construct(config.clone(), true);
                range_chip.load_lookup_table(&mut layouter)?;

                // ECDSA verify
                {
                    let (r_assigned, s_assigned, m_assigned) = {
                        let fq_config = FpConfig {
                            range_config: config.clone(),
                            limb_bits: $limb_bits,
                            num_limbs: $num_limbs,
                            p: modulus::<Fq>(),
                        };
                        let mut fq_chip =
                            FqOverflowChip::construct(fq_config, &mut range_chip, true);

                        let m_assigned = fq_chip.load_private(
                            &mut layouter,
                            FqOverflowChip::<F>::fe_to_witness(&self.msghash),
                        )?;

                        let r_assigned = fq_chip.load_private(
                            &mut layouter,
                            FqOverflowChip::<F>::fe_to_witness(&self.r),
                        )?;
                        let s_assigned = fq_chip.load_private(
                            &mut layouter,
                            FqOverflowChip::<F>::fe_to_witness(&self.s),
                        )?;
                        (r_assigned, s_assigned, m_assigned)
                    };
                    // end of fq_chip mutably borrowing range_chip
                    // now fp_chip will mutably borrow range_chip
                    let fp_config = FpConfig {
                        range_config: config.clone(),
                        limb_bits: $limb_bits,
                        num_limbs: $num_limbs,
                        p: modulus::<Fp>(),
                    };
                    let mut fp_chip = FpChip::<F>::construct(fp_config, &mut range_chip, true);
                    let mut ecc_chip = EccChip::<F, FpChip<F>>::construct(&mut fp_chip);
                    let pk_assigned = ecc_chip.load_private(
                        &mut layouter,
                        (self.pk.map(|pt| pt.x), self.pk.map(|pt| pt.y)),
                    )?;
                    // test ECDSA
                    let ecdsa = ecdsa_verify_no_pubkey_check::<F, Fp, Fq, Secp256k1Affine>(
                        &mut fp_chip,
                        &mut layouter.namespace(|| "ecdsa"),
                        &pk_assigned,
                        &r_assigned,
                        &s_assigned,
                        &m_assigned,
                        F::from(SECP_B),
                        4,
                        4,
                    )?;

                    // IMPORTANT: this assigns all constants to the fixed columns
                    // This is not optional.
                    let const_rows =
                        range_chip.gate_chip.assign_and_constrain_constants(&mut layouter)?;
                    // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
                    // This is not optional when there is more than 1 advice column.
                    range_chip.copy_and_lookup_cells(&mut layouter)?;

                    if self.r != None {
                        println!("ECDSA res {:?}", ecdsa);

                        println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", range_chip.gate_chip.config.num_advice, $num_lookup_advice, $num_fixed, $lookup_bits, $limb_bits, $num_limbs);
                        let advice_rows = range_chip.gate_chip.advice_rows.iter();
                        let horizontal_advice_rows = range_chip.gate_chip.horizontal_advice_rows.iter();
                        println!(
                            "maximum rows used by an advice column: {}",
                            std::cmp::max(
                                advice_rows.clone().max().or(Some(&0u64)).unwrap(),
                                horizontal_advice_rows.clone().max().or(Some(&0u64)).unwrap()
                            )
                        );
                        println!(
                            "minimum rows used by an advice column: {}",
                            std::cmp::min(
                                advice_rows.clone().min().or(Some(&u64::MAX)).unwrap(),
                                horizontal_advice_rows.clone().min().or(Some(&u64::MAX)).unwrap()
                            )
                        );
                        println!(
                            "total cells used: {}",
                            advice_rows.sum::<u64>() + horizontal_advice_rows.sum::<u64>() * 4
                        );
                        println!(
                            "cells used in special lookup columns: {}",
                            range_chip.cells_to_lookup.len()
                        );
                        println!(
                            "maximum rows used by a fixed column: {}",
                            const_rows
                        );
                    }
                }
                println!("ecdsa done");
                /*
                let fp_config = FpConfig {
                    range_config: config.clone(),
                    limb_bits: limb_bits,
                    num_limbs: num_limbs,
                    p: modulus::<Fp>(),
                };
                let mut fp_chip = FpChip::<F>::construct(fp_config, &mut range_chip, true);
                let mut chip = Secp256k1Chip::construct(&mut fp_chip);
                let P_assigned = chip.load_private(
                    &mut layouter,
                    match self.P {
                        Some(P) => (Some(P.x), Some(P.y)),
                        None => (None, None),
                    },
                )?;
                */

                /*
                let mut pt = Secp256k1Affine::default();
                let mut P_fixed = FixedEccPoint::<F, Secp256k1Affine>::from_g1(&pt, config.base_config.num_limbs, config.base_config.limb_bits);
                if let Some(P_point) = &self.P {
                    pt = P_point.clone();
                    P_fixed = FixedEccPoint::from_g1(&P_point, config.base_config.num_limbs, config.base_config.limb_bits);
                }

                let scalar_bigint = self.scalar.map(|x| fe_to_biguint(&x));
                let mask = (BigUint::from(1u32) << 128) - 1usize;
                let scalar0 = scalar_bigint.clone().map(|x| biguint_to_fe(&(x & mask)));
                let scalar1 = scalar_bigint.map(|x| biguint_to_fe(&(x >> 128)));
                let (scalar_cells, _) = layouter.assign_region(
                    || "load scalar",
                    |mut region| {
                        chip.field_chip.range.gate().assign_region_smart(
                            vec![Witness(scalar0), Witness(scalar1)],
                            vec![],
                            vec![],
                            vec![],
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
                */

                Ok(())
            }
        }
    };
}

#[cfg(test)]
#[test]
fn test_secp() {
    const K: u32 = 15;
    create_ecdsa_circuit!(GateStrategy::Vertical, 17, 3, 1, 14, 88, 3);
    let mut rng = rand::thread_rng();

    // generate random pub key and sign random message
    let G = Secp256k1Affine::generator();
    let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
    let pubkey = Secp256k1Affine::from(G * sk);
    let msg_hash = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);

    let k = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
    let k_inv = k.invert().unwrap();

    let r_point = Secp256k1Affine::from(G * k).coordinates().unwrap();
    let x = r_point.x();
    let x_bigint = fe_to_biguint(x);
    let r = biguint_to_fe::<Fq>(&x_bigint);
    let s = k_inv * (msg_hash + (r * sk));

    let circuit = ECDSACircuit::<Fr> {
        r: Some(r),
        s: Some(s),
        msghash: Some(msg_hash),
        pk: Some(pubkey),
        G,
        _marker: PhantomData,
    };

    let prover = MockProver::run(K, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(test)]
#[test]
fn bench_secp() -> Result<(), Box<dyn std::error::Error>> {
    const DEGREE: [u32; 8] = [19, 17, 16, 15, 14, 13, 12, 11];
    const NUM_ADVICE: [usize; 8] =
        [1, /*4*/ 5, 9, 17, /*36*/ 41, 73, /*148*/ 149, 323];
    const NUM_LOOKUP: [usize; 8] = [0, 1, 2, 3, 6, 12, 21, 38];
    const NUM_FIXED: [usize; 8] = [1, 1, 1, 1, 1, 1, 2, 5];
    const LOOKUP_BITS: [usize; 8] = [18, 16, 15, 14, 13, 12, 11, 10];
    const LIMB_BITS: [usize; 8] = [88, 88, 90, 88, 91, 88, 88, 90];

    seq!(I in 1..7 {
        {
        println!("----------------------------------------------------");
        let mut rng = rand::thread_rng();
        let start = Instant::now();

        create_ecdsa_circuit!(GateStrategy::Horizontal, NUM_ADVICE[I], NUM_LOOKUP[I], NUM_FIXED[I], LOOKUP_BITS[I], LIMB_BITS[I], 3);
        let params = Params::<G1Affine>::unsafe_setup::<Bn256>(DEGREE[I]);

        let circuit = ECDSACircuit::<Fr>::default();
        let circuit_duration = start.elapsed();
        println!("Time elapsed in circuit & params construction: {:?}", circuit_duration);
        let vk = keygen_vk(&params, &circuit)?;
        let vk_duration = start.elapsed();
        println!("Time elapsed in generating vkey: {:?}", vk_duration - circuit_duration);
        let pk = keygen_pk(&params, vk, &circuit)?;
        let pk_duration = start.elapsed();
        println!("Time elapsed in generating pkey: {:?}", pk_duration - vk_duration);

        // generate random pub key and sign random message
        let G = Secp256k1Affine::generator();
        let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
        let pubkey = Secp256k1Affine::from(G * sk);
        let msg_hash = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);

        let k = <Secp256k1Affine as CurveAffine>::ScalarExt::random(OsRng);
        let k_inv = k.invert().unwrap();

        let r_point = Secp256k1Affine::from(G * k).coordinates().unwrap();
        let x = r_point.x();
        let x_bigint = fe_to_biguint(x);
        let r = biguint_to_fe::<Fq>(&x_bigint);
        let s = k_inv * (msg_hash + (r * sk));

        let proof_circuit = ECDSACircuit::<Fr> {
            r: Some(r),
            s: Some(s),
            msghash: Some(msg_hash),
            pk: Some(pubkey),
            G,
            _marker: PhantomData,
        };
        let fill_duration = start.elapsed();
        println!("Time elapsed in filling circuit: {:?}", fill_duration - pk_duration);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(&params, &pk, &[proof_circuit], &[&[]], rng, &mut transcript)?;
        let _proof = transcript.finalize();
        let proof_duration = start.elapsed();
        println!("Proving time: {:?}", proof_duration - fill_duration);
        println!("----------------------------------------------------");
        }
    });
    Ok(())
}

#[cfg(feature = "dev-graph")]
#[cfg(test)]
#[test]
fn plot_secp() {
    let k = 19;
    create_ecdsa_circuit!(GateStrategy::Vertical, 1, 1, 1, 19, 88, 3);
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("ECDSA Layout", ("sans-serif", 60)).unwrap();

    let circuit = ECDSACircuit::<Fr>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
