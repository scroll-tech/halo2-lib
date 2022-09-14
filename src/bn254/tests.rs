#![allow(non_snake_case)]
use serde::{Deserialize, Serialize};
use std::io::Write;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use super::pairing::PairingChip;
use super::*;
use crate::bigint::FixedOverflowInteger;
use crate::ecc::EccChip;
use crate::fields::{fp::FpStrategy, PrimeFieldChip};
use crate::gates::QuantumCell::Witness;
use crate::gates::{GateInstructions, RangeInstructions};
use crate::gates::range::{RangeChip, RangeStrategy};
use crate::utils::{decompose_bigint_option, fe_to_bigint};
use ff::{Field, PrimeField};
use group::Curve;
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::{
        multi_miller_loop, pairing, Bn256, Fr, G1Affine, G2Affine, G2Prepared, Gt, G1, G2,
    },
    plonk::*,
    poly::commitment::{Params, ParamsVerifier},
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use halo2curves::bn254::Fq12;
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_traits::Num;

#[derive(Serialize, Deserialize)]
struct PairingCircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
}

struct PairingCircuit<F: FieldExt> {
    P: Option<G1Affine>,
    Q: Option<G2Affine>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Default for PairingCircuit<F> {
    fn default() -> Self {
        Self { P: None, Q: None, _marker: PhantomData }
    }
}

impl<F: FieldExt> Circuit<F> for PairingCircuit<F> {
    type Config = FpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner; // V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut folder = std::path::PathBuf::new();
        folder.push("./src/bn254");
        folder.push("configs/pairing_circuit.config");
        let params_str = std::fs::read_to_string(folder.as_path())
            .expect("src/bn254/configs/pairing_circuit.config file should exist");
        let params: PairingCircuitParams = serde_json::from_str(params_str.as_str()).unwrap();

        PairingChip::configure(
            meta,
            params.strategy,
            params.num_advice,
            params.num_lookup_advice,
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut range_chip = RangeChip::construct(config.range_config.clone(), true);
        let mut chip = PairingChip::construct(config, &mut range_chip, true);
        chip.fp_chip.load_lookup_table(&mut layouter)?;

        let P_assigned = chip.load_private_g1(&mut layouter, self.P.clone())?;
        let Q_assigned = chip.load_private_g2(&mut layouter, self.Q.clone())?;

        /*
        // test miller loop without final exp
        {
            let f = chip.miller_loop(&mut layouter, &Q_assigned, &P_assigned)?;
            for fc in &f.coeffs {
                assert_eq!(fc.value, fc.truncation.to_bigint());
            }
            if self.P != None {
                let actual_f = multi_miller_loop(&[(
                    &self.P.unwrap(),
                    &G2Prepared::from_affine(self.Q.unwrap()),
                )]);
                let f_val: Vec<String> =
                    f.coeffs.iter().map(|x| x.value.clone().unwrap().to_str_radix(16)).collect();
                println!("single miller loop:");
                println!("actual f: {:#?}", actual_f);
                println!("circuit f: {:#?}", f_val);
            }
        }
        */

        // test optimal ate pairing
        {
            let f = chip.pairing(&mut layouter, &Q_assigned, &P_assigned)?;
            for fc in &f.coeffs {
                assert_eq!(fc.value, fc.truncation.to_bigint());
            }
            if self.P != None {
                let actual_f = pairing(&self.P.unwrap(), &self.Q.unwrap());
                let f_val: Vec<String> = f
                    .coeffs
                    .iter()
                    .map(|x| x.value.clone().unwrap().to_str_radix(16))
                    //.map(|x| x.to_bigint().clone().unwrap().to_str_radix(16))
                    .collect();
                println!("optimal ate pairing:");
                println!("actual f: {:#?}", actual_f);
                println!("circuit f: {:#?}", f_val);
            }
        }

        // IMPORTANT: this assigns all constants to the fixed columns
        // This is not optional.
        let const_rows = chip.fp_chip.range.gate.assign_and_constrain_constants(&mut layouter)?;

        // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
        // This is not optional when there is more than 1 advice column.
        chip.fp_chip.range.copy_and_lookup_cells(&mut layouter)?;

        if self.P != None {
            let num_advice = chip.fp_chip.range.gate.config.num_advice;
            let num_lookup_advice = chip.fp_chip.range.config.lookup_advice.len();
            let num_fixed = chip.fp_chip.range.gate.config.constants.len();
            let lookup_bits = chip.fp_chip.range.config.lookup_bits;
            let limb_bits = chip.fp_chip.limb_bits;
            let num_limbs = chip.fp_chip.num_limbs;

            println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", num_advice, num_lookup_advice, num_fixed, lookup_bits, limb_bits, num_limbs);
            let advice_rows = chip.fp_chip.range.gate.advice_rows.iter();
            let horizontal_advice_rows = chip.fp_chip.range.gate.horizontal_advice_rows.iter();
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
            let total_cells = advice_rows.sum::<u64>() + horizontal_advice_rows.sum::<u64>() * 4;
            println!("total cells used: {}", total_cells);
            println!("cells used in special lookup column: {}", range_chip.cells_to_lookup.len());
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
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Debug)]
struct MSMCircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
    batch_size: usize,
    window_bits: usize,
}

#[derive(Clone, Debug)]
struct MSMConfig<F: FieldExt> {
    fp_config: FpConfig<F>,
    batch_size: usize,
    window_bits: usize,
}

impl<F: FieldExt> MSMConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        strategy: FpStrategy,
        num_advice: usize,
        num_lookup_advice: usize,
        num_fixed: usize,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
        batch_size: usize,
        window_bits: usize,
    ) -> Self {
        let fp_config = FpConfig::<F>::configure(
            meta,
            strategy,
            num_advice,
            num_lookup_advice,
            num_fixed,
            lookup_bits,
            limb_bits,
            num_limbs,
            p,
        );
        MSMConfig { fp_config, batch_size, window_bits }
    }
}

struct MSMCircuit<F: FieldExt> {
    bases: Vec<Option<G1Affine>>,
    scalars: Vec<Option<Fr>>,
    batch_size: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Default for MSMCircuit<F> {
    fn default() -> Self {
        Self { bases: vec![None; 10], scalars: vec![None; 10], batch_size: 10, _marker: PhantomData }
    }
}

impl<F: FieldExt> Circuit<F> for MSMCircuit<F> {
    type Config = MSMConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
	Self {
	    bases: vec![None; self.batch_size],
	    scalars: vec![None; self.batch_size],
	    batch_size: self.batch_size,
	    _marker: PhantomData,
	}
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut folder = std::path::PathBuf::new();
        folder.push("./src/bn254");
        folder.push("configs/msm_circuit.config");
        let params_str = std::fs::read_to_string(folder.as_path())
            .expect("src/bn254/configs/msm_circuit.config file should exist");
        let params: MSMCircuitParams = serde_json::from_str(params_str.as_str()).unwrap();

        MSMConfig::configure(
            meta,
            params.strategy,
            params.num_advice,
            params.num_lookup_advice,
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
            BigUint::from_str_radix(&Fq::MODULUS[2..], 16).unwrap(),
            params.batch_size,
            params.window_bits,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        assert_eq!(config.batch_size, self.scalars.len());
        assert_eq!(config.batch_size, self.bases.len());

        let mut range_chip = RangeChip::construct(config.fp_config.range_config.clone(), true);
        let mut scalars_assigned = Vec::new();
        for scalar in &self.scalars {
	    let decomposed = decompose_bigint_option(
		&scalar.map(|x| fe_to_biguint(&x).to_bigint().unwrap()),
		config.fp_config.num_limbs,
                config.fp_config.limb_bits
	    );
	    let limbs = layouter.assign_region(
		|| "load scalar",
		|mut region| {
		    let limbs = range_chip.gate().assign_region_smart(
			decomposed.iter().map(|x| Witness(x.clone())).collect(),
			vec![],
			vec![],
			vec![],
			0,
			&mut region,
		    )?;
		    Ok(limbs)
		},
	    )?;
            scalars_assigned.push(limbs);
        }

	let mut fp_chip = FpChip::construct(config.fp_config.clone(), &mut range_chip, true);
        fp_chip.load_lookup_table(&mut layouter)?;


        let mut ecc_chip = EccChip::construct(&mut fp_chip);
        let mut bases_assigned = Vec::new();
        for base in &self.bases {
            let base_assigned = ecc_chip.load_private(
                &mut layouter,
                (
                    base.map(|pt| biguint_to_fe(&fe_to_biguint(&pt.x))),
                    base.map(|pt| biguint_to_fe(&fe_to_biguint(&pt.y))),
                ),
            )?;
            bases_assigned.push(base_assigned);
        }

        let msm = ecc_chip.multi_scalar_mult::<halo2curves::bn254::G1Affine>(
            &mut layouter.namespace(|| "msm"),
            &bases_assigned,
            &scalars_assigned,
            F::from(3),
            config.fp_config.limb_bits,
            config.window_bits,
        )?;
        if self.scalars[0] != None {
            let mut elts = Vec::new();
            for (base, scalar) in self.bases.iter().zip(&self.scalars) {
                elts.push(base.unwrap() * scalar.unwrap());
            }
            let msm_answer = elts.into_iter().reduce(|a, b| a + b).unwrap().to_affine();

            let msm_x = msm.x.value.clone().unwrap().to_str_radix(16);
            let msm_y = msm.y.value.clone().unwrap().to_str_radix(16);
            println!("circuit: {:?} {:?}", msm_x, msm_y);
            println!("correct: {:?}", msm_answer);
        }

        let const_rows = fp_chip.range.gate.assign_and_constrain_constants(&mut layouter)?;
        fp_chip.range.copy_and_lookup_cells(&mut layouter)?;
        if self.bases[0] != None {
            let num_advice = fp_chip.range.gate.config.num_advice;
            let num_lookup_advice = fp_chip.range.config.lookup_advice.len();
            let num_fixed = fp_chip.range.gate.config.constants.len();
            let lookup_bits = fp_chip.range.config.lookup_bits;
            let limb_bits = fp_chip.limb_bits;
            let num_limbs = fp_chip.num_limbs;

            println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", num_advice, num_lookup_advice, num_fixed, lookup_bits, limb_bits, num_limbs);
            let advice_rows = fp_chip.range.gate.advice_rows.iter();
            let horizontal_advice_rows = fp_chip.range.gate.horizontal_advice_rows.iter();
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
            let total_cells = advice_rows.sum::<u64>() + horizontal_advice_rows.sum::<u64>() * 4;
            println!("total cells used: {}", total_cells);
            println!("cells used in special lookup column: {}", range_chip.cells_to_lookup.len());
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
        Ok(())
    }
}

#[cfg(test)]
#[test]
fn test_msm() {
    let mut folder = std::path::PathBuf::new();
    folder.push("./src/bn254");
    folder.push("configs/msm_circuit.config");
    let params_str = std::fs::read_to_string(folder.as_path())
        .expect("src/bn254/configs/msm_circuit.config file should exist");
    let params: MSMCircuitParams = serde_json::from_str(params_str.as_str()).unwrap();
    let k = params.degree;

    let mut rng = rand::thread_rng();

    let mut bases = Vec::new();
    let mut scalars = Vec::new();
    for idx in 0..params.batch_size {
        let new_pt = Some(G1Affine::random(&mut rng));
        bases.push(new_pt);

        let new_scalar = Some(Fr::random(&mut rng));
        scalars.push(new_scalar);
    }

    println!("bases {:?}", bases);
    println!("scalars {:?}", scalars);
    let circuit = MSMCircuit::<Fr> {
	bases,
	scalars,
	batch_size: params.batch_size,
	_marker: PhantomData
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
//    prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(test)]
#[test]
fn bench_msm() -> Result<(), Box<dyn std::error::Error>> {
    use std::io::BufRead;
    let mut folder = std::path::PathBuf::new();
    folder.push("./src/bn254");

    folder.push("configs/bench_msm.config");
    let bench_params_file = std::fs::File::open(folder.as_path())?;
    folder.pop();
    folder.pop();

    folder.push("results/msm_bench.csv");
    let mut fs_results = std::fs::File::create(folder.as_path()).unwrap();
    folder.pop();
    folder.pop();
    write!(fs_results, "degree,num_advice,num_lookup,num_fixed,lookup_bits,limb_bits,num_limbs,batch_size,window_bits,vk_size,proof_time,proof_size,verify_time\n")?;
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
        let bench_params: MSMCircuitParams = serde_json::from_str(line.unwrap().as_str()).unwrap();
        println!(
            "---------------------- degree = {} ------------------------------",
            bench_params.degree
        );
        let mut rng = rand::thread_rng();
        let start = Instant::now();

        {
            folder.pop();
            folder.push("configs/msm_circuit.config");
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

        let circuit = MSMCircuit::<Fr> {
            bases: vec![None; bench_params.batch_size],
            scalars: vec![None; bench_params.batch_size],
	    batch_size: bench_params.batch_size,
            _marker: PhantomData,
        };
        let circuit_duration = start.elapsed();
        println!("Time elapsed in circuit & params construction: {:?}", circuit_duration);

        let vk = keygen_vk(&params, &circuit)?;
        let vk_duration = start.elapsed();
        println!("Time elapsed in generating vkey: {:?}", vk_duration - circuit_duration);
        let vk_size = {
            folder.push(format!(
                "msm_circuit_{}_{}_{}_{}_{}_{}_{}_{}_{}.vkey",
                bench_params.degree,
                bench_params.num_advice,
                bench_params.num_lookup_advice,
                bench_params.num_fixed,
                bench_params.lookup_bits,
                bench_params.limb_bits,
                bench_params.num_limbs,
                bench_params.batch_size,
                bench_params.window_bits,
            ));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
            vk.write(&mut fd).unwrap();
            fd.metadata().unwrap().len()
        };
        let pk = keygen_pk(&params, vk, &circuit)?;
        let pk_duration = start.elapsed();
        println!("Time elapsed in generating pkey: {:?}", pk_duration - vk_duration);

	let mut bases = Vec::new();
	let mut scalars = Vec::new();
	for idx in 0..bench_params.batch_size {
            let new_pt = Some(G1Affine::random(&mut rng));
            bases.push(new_pt);
	    
            let new_scalar = Some(Fr::random(&mut rng));
            scalars.push(new_scalar);
	}

	println!("{:?}", bench_params);
        let proof_circuit = MSMCircuit::<Fr> {
	    bases,
	    scalars,
	    batch_size: bench_params.batch_size,
	    _marker: PhantomData
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
                "msm_circuit_proof_{}_{}_{}_{}_{}_{}_{}_{}_{}.data",
                bench_params.degree,
                bench_params.num_advice,
                bench_params.num_lookup_advice,
                bench_params.num_fixed,
                bench_params.lookup_bits,
                bench_params.limb_bits,
                bench_params.num_limbs,
		bench_params.batch_size,
		bench_params.window_bits
            ));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
            fd.write_all(&proof).unwrap();
            fd.metadata().unwrap().len()
        };

        let verify_start = start.elapsed();
        let params_verifier: ParamsVerifier<Bn256> = params.verifier(0).unwrap();
        let strategy = SingleVerifier::new(&params_verifier);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(
            verify_proof(&params_verifier, pk.get_vk(), strategy, &[&[]], &mut transcript).is_ok()
        );
        let verify_duration = start.elapsed();
        let verify_time = verify_duration - verify_start;
        println!("Verify time: {:?}", verify_time);

        write!(
            fs_results,
            "{},{},{},{},{},{},{},{},{},{},{:?},{},{:?}\n",
            bench_params.degree,
            bench_params.num_advice,
            bench_params.num_lookup_advice,
            bench_params.num_fixed,
            bench_params.lookup_bits,
            bench_params.limb_bits,
            bench_params.num_limbs,
	    bench_params.batch_size,
	    bench_params.window_bits,
            vk_size,
            proof_time,
            proof_size,
            verify_time
        )?;
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn test_pairing() {
    let mut folder = std::path::PathBuf::new();
    folder.push("./src/bn254");
    folder.push("configs/pairing_circuit.config");
    let params_str = std::fs::read_to_string(folder.as_path())
        .expect("src/bn254/configs/pairing_circuit.config file should exist");
    let params: PairingCircuitParams = serde_json::from_str(params_str.as_str()).unwrap();
    let k = params.degree;

    let mut rng = rand::thread_rng();

    let P = Some(G1Affine::random(&mut rng));
    let Q = Some(G2Affine::random(&mut rng));

    let circuit = PairingCircuit::<Fr> { P, Q, _marker: PhantomData };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(test)]
#[test]
fn bench_pairing() -> Result<(), Box<dyn std::error::Error>> {
    /*
    // Parameters for FpStrategy::CustomVerticalCRT
    const DEGREE: [u32; 10] = [22, 21, 20, 19, 18, 17, 16, 15, 14, 13];
    const NUM_ADVICE: [usize; 10] = [1, 2, 3, 5, 10, 19, 37, 75, 149, 307];
    const NUM_LOOKUP: [usize; 10] = [0, 1, 1, 1, 2, 4, 7, 16, 32, 74];
    const NUM_FIXED: [usize; 10] = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    const LOOKUP_BITS: [usize; 10] = [21, 20, 19, 18, 17, 16, 15, 14, 13, 12];
    const LIMB_BITS: [usize; 10] = [88, 88, 88, 88, 88, 88, 88, 88, 88, 88];
    */

    use std::io::BufRead;
    let mut folder = std::path::PathBuf::new();
    folder.push("./src/bn254");

    folder.push("configs/bench_pairing.config");
    let bench_params_file = std::fs::File::open(folder.as_path())?;
    folder.pop();
    folder.pop();

    folder.push("results/pairing_bench.csv");
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
        let bench_params: PairingCircuitParams =
            serde_json::from_str(line.unwrap().as_str()).unwrap();
        println!(
            "---------------------- degree = {} ------------------------------",
            bench_params.degree
        );
        let mut rng = rand::thread_rng();
        let start = Instant::now();

        {
            folder.pop();
            folder.push("configs/pairing_circuit.config");
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

        let circuit = PairingCircuit::<Fr>::default();
        let circuit_duration = start.elapsed();
        println!("Time elapsed in circuit & params construction: {:?}", circuit_duration);

        let vk = keygen_vk(&params, &circuit)?;
        let vk_duration = start.elapsed();
        println!("Time elapsed in generating vkey: {:?}", vk_duration - circuit_duration);
        let vk_size = {
            folder.push(format!(
                "pairing_circuit_{}_{}_{}_{}_{}_{}_{}.vkey",
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
        let pk = keygen_pk(&params, vk, &circuit)?;
        let pk_duration = start.elapsed();
        println!("Time elapsed in generating pkey: {:?}", pk_duration - vk_duration);
        /*{
            folder.push(format!("pairing_circuit_{}_{}_{}_{}_{}_{}_{}.pkey", DEGREE[I], NUM_ADVICE[I], NUM_LOOKUP[I], NUM_FIXED[I], LOOKUP_BITS[I], LIMB_BITS[I], 3));
            let mut fd = std::fs::File::create(folder.as_path()).unwrap();
            folder.pop();
        }*/

        let P = Some(G1Affine::random(&mut rng));
        let Q = Some(G2Affine::random(&mut rng));
        let proof_circuit = PairingCircuit::<Fr> { P, Q, _marker: PhantomData };
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
                "pairing_circuit_proof_{}_{}_{}_{}_{}_{}_{}.data",
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

        let verify_start = start.elapsed();
        let params_verifier: ParamsVerifier<Bn256> = params.verifier(0).unwrap();
        let strategy = SingleVerifier::new(&params_verifier);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        assert!(
            verify_proof(&params_verifier, pk.get_vk(), strategy, &[&[]], &mut transcript).is_ok()
        );
        let verify_duration = start.elapsed();
        let verify_time = verify_duration - verify_start;
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
#[test]
fn plot_pairing() {
    let k = 23;
    use plotters::prelude::*;
    create_pairing_circuit!(GateStrategy::Vertical, 1, 1, 1, 22, 88, 3);

    let root = BitMapBackend::new("layout.png", (512, 40384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Pairing Layout", ("sans-serif", 60)).unwrap();

    let circuit = PairingCircuit::<Fr>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
*/
