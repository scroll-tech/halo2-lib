#![allow(non_snake_case)]
use ark_std::{end_timer, start_timer};
use serde::{Deserialize, Serialize};
use std::io::Write;
use std::marker::PhantomData;

use ff::Field;
use halo2_proofs::poly::commitment::{Params, ParamsProver};
use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    circuit::*,
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::*,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use halo2curves::secp256k1::{Fp, Fq, Secp256k1Affine};
use rand_core::OsRng;

use super::{FpChip, FqOverflowChip};
use crate::{
    ecc::{ecdsa_verify_no_pubkey_check, EccChip},
    fields::{fp::FpStrategy, FieldChip},
};
use halo2_base::{
    utils::{biguint_to_fe, fe_to_biguint, modulus},
    Context, ContextParams,
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
    type Config = FpChip<F>;
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

        FpChip::<F>::configure(
            meta,
            params.strategy,
            &[params.num_advice],
            &[params.num_lookup_advice],
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
            modulus::<Fp>(),
            "ecdsa".to_string(),
        )
    }

    fn synthesize(
        &self,
        fp_chip: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        fp_chip.range.load_lookup_table(&mut layouter)?;

        let limb_bits = fp_chip.limb_bits;
        let num_limbs = fp_chip.num_limbs;
        let num_fixed = fp_chip.range.gate.constants.len();
        let lookup_bits = fp_chip.range.lookup_bits;
        let num_advice = fp_chip.range.gate.num_advice;

        let using_simple_floor_planner = true;
        let mut first_pass = true;
        // ECDSA verify
        layouter.assign_region(
            || "ECDSA",
            |region| {
                if first_pass && using_simple_floor_planner {
                    first_pass = false;
                    return Ok(());
                }

                let mut aux = Context::new(
                    region,
                    ContextParams {
                        num_advice: vec![("ecdsa".to_string(), num_advice)],
                    },
                );
                let ctx = &mut aux;

            let (r_assigned, s_assigned, m_assigned) = {
                let fq_chip = FqOverflowChip::construct(fp_chip.range(), limb_bits, num_limbs, modulus::<Fq>());

                let m_assigned = fq_chip.load_private(
                    ctx,
                    FqOverflowChip::<F>::fe_to_witness(&self.msghash.map_or(Value::unknown(), |v| Value::known(v))),
                )?;

                let r_assigned = fq_chip
                    .load_private(ctx, FqOverflowChip::<F>::fe_to_witness(&self.r.map_or(Value::unknown(), |v| Value::known(v))))?;
                let s_assigned = fq_chip
                    .load_private(ctx, FqOverflowChip::<F>::fe_to_witness(&self.s.map_or(Value::unknown(), |v| Value::known(v))))?;
                (r_assigned, s_assigned, m_assigned)
            };

            let ecc_chip = EccChip::<F, FpChip<F>>::construct(&fp_chip);
            let pk_assigned = ecc_chip
                .load_private(ctx, (self.pk.map_or(Value::unknown(), |pt| Value::known(pt.x)), self.pk.map_or(Value::unknown(), |pt| Value::known(pt.y))))?;
            // test ECDSA
            let ecdsa = ecdsa_verify_no_pubkey_check::<F, Fp, Fq, Secp256k1Affine>(
                &fp_chip,
                ctx,
                &pk_assigned,
                &r_assigned,
                &s_assigned,
                &m_assigned,
                4,
                4,
            )?;

            // IMPORTANT: this assigns all constants to the fixed columns
            // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
            // This is not optional.
            let (const_rows, total_fixed, _lookup_rows) = fp_chip.finalize(ctx)?;

            #[cfg(feature = "display")]
            if self.r != None {
                println!("ECDSA res {:?}", ecdsa);

                let num_lookup_advice = fp_chip.range.lookup_advice.len();

                println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", num_advice, num_lookup_advice, num_fixed, lookup_bits, limb_bits, num_limbs);
                let advice_rows = ctx.advice_rows["ecdsa"].iter();
                println!(
                    "maximum rows used by an advice column: {}",
                        advice_rows.clone().max().or(Some(&0)).unwrap(),
                );
                println!(
                    "minimum rows used by an advice column: {}",
                        advice_rows.clone().min().or(Some(&usize::MAX)).unwrap(),
                );

                let total_cells =
                    advice_rows.sum::<usize>();
                println!("total cells used: {}", total_cells);
                println!(
                    "cells used in special lookup column: {}",
                    ctx.cells_to_lookup.len()
                );
                println!("maximum rows used by a fixed column: {}", const_rows);

                println!("Suggestions:");
                let degree = lookup_bits + 1;
                println!(
                    "Have you tried using {} advice columns?",
                    (total_cells + (1 << degree) - 1) / (1 << degree)
                );
                println!(
                    "Have you tried using {} lookup columns?",
                    (ctx.cells_to_lookup.len() + (1 << degree) - 1) / (1 << degree)
                );
                println!(
                    "Have you tried using {} fixed columns?",
                    (total_fixed + (1 << degree) - 1) / (1 << degree)
                );
            }
        
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
    })
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

    use halo2_proofs::{
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
        transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
    };
    use std::io::BufRead;

    let mut rng = rand::thread_rng();

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

        {
            folder.pop();
            folder.push("configs/ecdsa_circuit.config");
            let mut f = std::fs::File::create(folder.as_path())?;
            write!(f, "{}", serde_json::to_string(&bench_params).unwrap())?;
            folder.pop();
            folder.pop();
            folder.push("data");
        }
        let params_time = start_timer!(|| "Time elapsed in circuit & params construction");
        let params = {
            params_folder.push(format!("kzg_bn254_{}.params", bench_params.degree));
            let fd = std::fs::File::open(params_folder.as_path());
            let params = if let Ok(mut f) = fd {
                println!("Found existing params file. Reading params...");
                ParamsKZG::<Bn256>::read(&mut f).unwrap()
            } else {
                println!("Creating new params file...");
                let mut f = std::fs::File::create(params_folder.as_path())?;
                let params = ParamsKZG::<Bn256>::setup(bench_params.degree, &mut rng);
                params.write(&mut f).unwrap();
                params
            };
            params_folder.pop();
            params
        };

        let circuit = ECDSACircuit::<Fr>::default();
        end_timer!(params_time);

        let vk_time = start_timer!(|| "Time elapsed in generating vkey");
        let vk = keygen_vk(&params, &circuit)?;
        end_timer!(vk_time);

        /*let vk_size = {
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
        };*/

        let pk_time = start_timer!(|| "Time elapsed in generating pkey");
        let pk = keygen_pk(&params, vk, &circuit)?;
        end_timer!(pk_time);

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
        let rng = rand::thread_rng();

        // create a proof
        let proof_time = start_timer!(|| "Proving time");
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            _,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            ECDSACircuit<Fr>,
        >(&params, &pk, &[proof_circuit], &[&[]], rng, &mut transcript)?;
        let proof = transcript.finalize();
        end_timer!(proof_time);

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

        let verify_time = start_timer!(|| "Verify time");
        let verifier_params = params.verifier_params();
        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(verifier_params, pk.get_vk(), strategy, &[&[]], &mut transcript)
        .is_ok());
        end_timer!(verify_time);

        write!(
            fs_results,
            "{},{},{},{},{},{},{},{:?},{},{:?}\n",
            bench_params.degree,
            bench_params.num_advice,
            bench_params.num_lookup_advice,
            bench_params.num_fixed,
            bench_params.lookup_bits,
            bench_params.limb_bits,
            bench_params.num_limbs,
            proof_time.time.elapsed(),
            proof_size,
            verify_time.time.elapsed()
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
