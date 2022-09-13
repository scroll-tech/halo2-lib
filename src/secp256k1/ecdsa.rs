#![allow(non_snake_case)]
use serde::{Deserialize, Serialize};
use std::io::Write;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use ff::{Field, PrimeField};
use halo2_proofs::circuit::floor_planner::*;
use halo2_proofs::pairing::bn256::{Bn256, G1Affine};
use halo2_proofs::pairing::group::Group;
use halo2_proofs::poly::commitment::{Params, ParamsVerifier};
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::*,
    dev::MockProver,
    pairing::bn256::Fr,
    plonk::*,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use halo2curves::secp256k1::{Fp, Fq, Secp256k1, Secp256k1Affine};
use num_bigint::{BigInt, BigUint};
use rand_core::OsRng;

use super::{FpChip, FqOverflowChip, Secp256k1Chip, SECP_B};
use crate::{
    ecc::{ecdsa_verify_no_pubkey_check, fixed::FixedEccPoint, EccChip},
    fields::{fp::FpConfig, fp::FpStrategy, FieldChip, PrimeFieldChip},
    gates::{
        range::{RangeChip, RangeConfig, RangeStrategy},
        GateInstructions,
        QuantumCell::Witness,
        RangeInstructions,
    },
    utils::{bigint_to_fe, biguint_to_fe, decompose_biguint_option, fe_to_biguint, modulus},
};

#[derive(Serialize, Deserialize)]
struct CircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
}

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
    type Config = FpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut folder = std::path::PathBuf::new();
        folder.push("./src/secp256k1");
        folder.push("configs/ecdsa_circuit.config");
        let params_str = std::fs::read_to_string(folder.as_path())
            .expect("src/secp256k1/configs/ecdsa_circuit.config file should exist");
        let params: CircuitParams = serde_json::from_str(params_str.as_str()).unwrap();

        FpConfig::<F>::configure(
            meta,
            params.strategy,
            params.num_advice,
            params.num_lookup_advice,
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
            modulus::<Fp>(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let fp_config = config;
        let mut range_chip = RangeChip::<F>::construct(fp_config.range_config.clone(), true);
        range_chip.load_lookup_table(&mut layouter)?;

        let limb_bits = fp_config.limb_bits;
        let num_limbs = fp_config.num_limbs;
        let num_fixed = fp_config.range_config.gate_config.constants.len();
        let lookup_bits = fp_config.range_config.lookup_bits;

        // ECDSA verify
        {
            let (r_assigned, s_assigned, m_assigned) = {
                let fq_config = FpConfig {
                    range_config: fp_config.range_config.clone(),
                    bigint_config: fp_config.bigint_config.clone(),
                    limb_bits: limb_bits,
                    num_limbs: num_limbs,
                    p: modulus::<Fq>(),
                };
                let mut fq_chip = FqOverflowChip::construct(fq_config, &mut range_chip, true);

                let m_assigned = fq_chip.load_private(
                    &mut layouter,
                    FqOverflowChip::<F>::fe_to_witness(&self.msghash),
                )?;

                let r_assigned = fq_chip
                    .load_private(&mut layouter, FqOverflowChip::<F>::fe_to_witness(&self.r))?;
                let s_assigned = fq_chip
                    .load_private(&mut layouter, FqOverflowChip::<F>::fe_to_witness(&self.s))?;
                (r_assigned, s_assigned, m_assigned)
            };
            // end of fq_chip mutably borrowing range_chip
            // now fp_chip will mutably borrow range_chip
            let mut fp_chip = FpChip::<F>::construct(fp_config, &mut range_chip, true);
            let mut ecc_chip = EccChip::<F, FpChip<F>>::construct(&mut fp_chip);
            let pk_assigned = ecc_chip
                .load_private(&mut layouter, (self.pk.map(|pt| pt.x), self.pk.map(|pt| pt.y)))?;
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
            let const_rows = range_chip.gate.assign_and_constrain_constants(&mut layouter)?;
            // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
            // This is not optional when there is more than 1 advice column.
            range_chip.copy_and_lookup_cells(&mut layouter)?;

            if self.r != None {
                println!("ECDSA res {:?}", ecdsa);

                let num_advice = range_chip.config.gate_config.num_advice;
                let num_lookup_advice = range_chip.config.lookup_advice.len();

                println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", num_advice, num_lookup_advice, num_fixed, lookup_bits, limb_bits, num_limbs);
                let advice_rows = range_chip.gate.advice_rows.iter();
                let horizontal_advice_rows = range_chip.gate.horizontal_advice_rows.iter();
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

                let total_cells =
                    advice_rows.sum::<u64>() + horizontal_advice_rows.sum::<u64>() * 4;
                println!("total cells used: {}", total_cells);
                println!(
                    "cells used in special lookup column: {}",
                    range_chip.cells_to_lookup.len()
                );
                let total_fixed = const_rows * num_fixed;
                println!("maximum rows used by a fixed column: {}", const_rows);

                println!("Suggestions:");
                let degree = lookup_bits + 1;
                println!(
                    "Have you tried using {} advice columns?",
                    (total_cells + (1 << degree) - 1) / (1 << degree)
                );
                println!(
                    "Have you tried using {} lookup columns?",
                    (range_chip.cells_to_lookup.len() + (1 << degree) - 1) / (1 << degree)
                );
                println!(
                    "Have you tried using {} fixed columns?",
                    (total_fixed + (1 << degree) - 1) / (1 << degree)
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

#[cfg(test)]
#[test]
fn test_secp() {
    let mut folder = std::path::PathBuf::new();
    folder.push("./src/secp256k1");
    folder.push("configs/ecdsa_circuit.config");
    let params_str = std::fs::read_to_string(folder.as_path())
        .expect("src/secp256k1/configs/ecdsa_circuit.config file should exist");
    let params: CircuitParams = serde_json::from_str(params_str.as_str()).unwrap();
    let K = params.degree;

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
    /*
    // Parameters for use with FpStrategy::CustomVerticalCRT
    const DEGREE: [u32; 9] = [19, 18, 17, 16, 15, 14, 13, 12, 11];
    const NUM_ADVICE: [usize; 9] = [1, 2, 3, 6, 12, 25, 49, 98, 201];
    const NUM_LOOKUP: [usize; 9] = [0, 1, 1, 2, 3, 6, 12, 24, 53];
    const NUM_FIXED: [usize; 9] = [1, 1, 1, 1, 1, 1, 1, 2, 5];
    const LOOKUP_BITS: [usize; 9] = [18, 17, 16, 15, 14, 13, 12, 11, 10];
    const LIMB_BITS: [usize; 9] = [88, 88, 88, 88, 88, 88, 88, 88, 88];
    */

    use std::io::BufRead;

    let mut folder = std::path::PathBuf::new();
    folder.push("./src/secp256k1");

    folder.push("configs/bench_ecdsa.config");
    let bench_params_file = std::fs::File::open(folder.as_path())?;
    folder.pop();
    folder.pop();

    folder.push("results/ecdsa_bench.csv");
    let mut fs_results = std::fs::File::create(folder.as_path()).unwrap();
    folder.pop();
    folder.pop();
    write!(fs_results, "degree,num_advice,num_lookup,num_fixed,lookup_bits,limb_bits,num_limbs,vk_size,proof_time,proof_size,verify_time\n")?;
    folder.push("data");
    if !folder.is_dir() {
        std::fs::create_dir(folder.as_path())?;
    }

    let mut params_folder = std::path::PathBuf::new();
    params_folder.push("./params");
    if !params_folder.is_dir() {
        std::fs::create_dir(params_folder.as_path())?;
    }

    let bench_params_reader = std::io::BufReader::new(bench_params_file);
    for line in bench_params_reader.lines() {
        let bench_params: CircuitParams = serde_json::from_str(line.unwrap().as_str()).unwrap();
        println!(
            "---------------------- degree = {} ------------------------------",
            bench_params.degree
        );
        let rng = rand::thread_rng();
        let start = Instant::now();

        {
            folder.pop();
            folder.push("configs/ecdsa_circuit.config");
            let mut f = std::fs::File::create(folder.as_path())?;
            write!(f, "{}", serde_json::to_string(&bench_params).unwrap())?;
            folder.pop();
            folder.pop();
            folder.push("data");
        }
        let params = {
            params_folder.push(format!("bn254_{}.params", bench_params.degree));
            let fd = std::fs::File::open(params_folder.as_path());
            let params = if let Ok(mut f) = fd {
                println!("Found existing params file. Reading params...");
                Params::<G1Affine>::read(&mut f).unwrap()
            } else {
                println!("Creating new params file...");
                let mut f = std::fs::File::create(params_folder.as_path())?;
                let params = Params::<G1Affine>::unsafe_setup::<Bn256>(bench_params.degree);
                params.write(&mut f).unwrap();
                params
            };
            params_folder.pop();
            params
        };

        let circuit = ECDSACircuit::<Fr>::default();
        let circuit_duration = start.elapsed();
        println!("Time elapsed in circuit & params construction: {:?}", circuit_duration);

        let vk = keygen_vk(&params, &circuit)?;
        let vk_duration = start.elapsed();
        println!("Time elapsed in generating vkey: {:?}", vk_duration - circuit_duration);
        let vk_size = {
            folder.push(format!(
                "ecdsa_circuit_{}_{}_{}_{}_{}_{}_{}.vkey",
                bench_params.degree,
                bench_params.num_advice,
                bench_params.num_lookup_advice,
                bench_params.num_fixed,
                bench_params.lookup_bits,
                bench_params.limb_bits,
                bench_params.num_limbs
            ));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
            vk.write(&mut fd).unwrap();
            fd.metadata().unwrap().len()
        };
        let vk_duration = start.elapsed();
        let pk = keygen_pk(&params, vk, &circuit)?;
        let pk_duration = start.elapsed();
        println!("Time elapsed in generating pkey: {:?}", pk_duration - vk_duration);
        /*{
            folder.push(format!("ecdsa_circuit_{}_{}_{}_{}_{}_{}_{}.pkey", DEGREE[I], NUM_ADVICE[I], NUM_LOOKUP[I], NUM_FIXED[I], LOOKUP_BITS[I], LIMB_BITS[I], 3));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
        }*/
        let pk_duration = start.elapsed();

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
        let proof = transcript.finalize();
        let proof_duration = start.elapsed();
        let proof_time = proof_duration - fill_duration;
        println!("Proving time: {:?}", proof_time);

        let proof_size = {
            folder.push(format!(
                "ecdsa_circuit_proof_{}_{}_{}_{}_{}_{}_{}.data",
                bench_params.degree,
                bench_params.num_advice,
                bench_params.num_lookup_advice,
                bench_params.num_fixed,
                bench_params.lookup_bits,
                bench_params.limb_bits,
                bench_params.num_limbs
            ));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
            fd.write_all(&proof).unwrap();
            fd.metadata().unwrap().len()
        };

        let params_verifier: ParamsVerifier<Bn256> = params.verifier(0).unwrap();
        let strategy = SingleVerifier::new(&params_verifier);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(
            verify_proof(&params_verifier, pk.get_vk(), strategy, &[&[]], &mut transcript).is_ok()
        );
        let verify_duration = start.elapsed();
        let verify_time = verify_duration - proof_duration;
        println!("Verify time: {:?}", verify_time);

        write!(
            fs_results,
            "{},{},{},{},{},{},{},{},{:?},{},{:?}\n",
            bench_params.degree,
            bench_params.num_advice,
            bench_params.num_lookup_advice,
            bench_params.num_fixed,
            bench_params.lookup_bits,
            bench_params.limb_bits,
            bench_params.num_limbs,
            vk_size,
            proof_time,
            proof_size,
            verify_time
        )?;
    }
    Ok(())
}

/*
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
*/
