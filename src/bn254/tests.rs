#![allow(non_snake_case)]
use seq_macro::seq;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use super::pairing::PairingChip;
use super::*;
use crate::ecc::EccChip;
use crate::fields::PrimeFieldChip;
use crate::gates::range::RangeChip;
use ff::PrimeField;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::pairing::bn256::{
    multi_miller_loop, pairing, Bn256, G1Affine, G2Affine, G2Prepared, Gt, G1, G2,
};
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr,
    plonk::*,
    poly::commitment::Params,
    transcript::{Blake2bWrite, Challenge255},
};
use halo2curves::bn254::Fq12;
use num_bigint::BigInt;

#[macro_export]
macro_rules! create_pairing_circuit {
    ( $num_advice:expr, $num_lookup_advice:expr, $num_fixed:expr, $lookup_bits:expr, $limb_bits:expr, $num_limbs:expr) => {
        struct PairingCircuit<F: FieldExt> {
            P: Option<G1Affine>,
            Q: Option<G2Affine>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt> Default for PairingCircuit<F> {
            fn default() -> Self {
                Self{
                    P: None,
                    Q: None,
                    _marker: PhantomData
                }
            }
        }

        impl<F: FieldExt> Circuit<F> for PairingCircuit<F> {
            type Config = FpConfig<F>;
            type FloorPlanner = SimpleFloorPlanner; // V1;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                PairingChip::configure(
                    meta,
                    $num_advice,
                    $num_lookup_advice,
                    $num_fixed,
                    $lookup_bits,
                    $limb_bits,
                    $num_limbs,
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
                    /*if self.P != None {
                        let actual_f = pairing(&self.P.unwrap(), &self.Q.unwrap());
                        let f_val: Vec<String> = f
                            .coeffs
                            .iter()
                            .map(|x| x.value.clone().unwrap().to_str_radix(16))
                            .collect();
                        println!("optimal ate pairing:");
                        println!("actual f: {:#?}", actual_f);
                        println!("circuit f: {:#?}", f_val);
                    }*/
                }

                // IMPORTANT: this assigns all constants to the fixed columns
                // This is not optional.
                let const_rows =
                    chip.fp_chip.range.gate_chip.assign_and_constrain_constants(&mut layouter)?;

                // IMPORTANT: this copies cells to the lookup advice column to perform range check lookups
                // This is not optional when there is more than 1 advice column.
                chip.fp_chip.range.copy_and_lookup_cells(&mut layouter)?;

                if self.P != None {
                    println!("Using:\nadvice columns: {}\nspecial lookup advice columns: {}\nfixed columns: {}\nlookup bits: {}\nlimb bits: {}\nnum limbs: {}", $num_advice, $num_lookup_advice, $num_fixed, $lookup_bits, $limb_bits, $num_limbs);
                    let advice_rows = chip.fp_chip.range.gate_chip.advice_rows.iter();
                    println!(
                        "maximum rows used by an advice column: {}",
                        advice_rows.clone().max().unwrap()
                    );
                    println!(
                        "minimum rows used by an advice column: {}",
                        advice_rows.clone().min().unwrap()
                    );
                    println!(
                        "total cells use: {}",
                        advice_rows.sum::<u64>()
                    );
                    println!(
                        "cells used in special lookup column: {}",
                        range_chip.cells_to_lookup.len()
                    );
                    println!(
                        "maximum rows used by a fixed column: {}",
                        const_rows
                    );
                }
                Ok(())
            }
        }
    };
}

#[cfg(test)]
#[test]
fn test_pairing() {
    let k = 23;
    create_pairing_circuit!(1, 0, 1, 22, 88, 3);
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
    const DEGREE: [u32; 5] = [23, 19, 16, 13, 12];
    const NUM_ADVICE: [usize; 5] = [1, 9, 71, 615, 1248];
    const NUM_LOOKUP: [usize; 5] = [1, 1, 1, 1, 1];
    const NUM_FIXED: [usize; 5] = [1, 1, 1, 1, 1];
    const LOOKUP_BITS: [usize; 5] = [22, 18, 15, 12, 11];
    const LIMB_BITS: [usize; 5] = [88, 90, 90, 88, 88];

    seq!(I in 0..5 {
        {
        println!("----------------------------------------------------");
        let mut rng = rand::thread_rng();
        let start = Instant::now();

        create_pairing_circuit!(NUM_ADVICE[I], NUM_LOOKUP[I], NUM_FIXED[I], LOOKUP_BITS[I], LIMB_BITS[I], 3);
        let params = Params::<G1Affine>::unsafe_setup::<Bn256>(DEGREE[I]);

        let circuit = PairingCircuit::<Fr>::default();
        let circuit_duration = start.elapsed();
        println!("Time elapsed in circuit & params construction: {:?}", circuit_duration);
        let vk = keygen_vk(&params, &circuit)?;
        let vk_duration = start.elapsed();
        println!("Time elapsed in generating vkey: {:?}", vk_duration - circuit_duration);
        let pk = keygen_pk(&params, vk, &circuit)?;
        let pk_duration = start.elapsed();
        println!("Time elapsed in generating pkey: {:?}", pk_duration - vk_duration);

        let P = Some(G1Affine::random(&mut rng));
        let Q = Some(G2Affine::random(&mut rng));
        let circuit = PairingCircuit::<Fr> { P, Q, _marker: PhantomData };
        let fill_duration = start.elapsed();
        println!("Time elapsed in filling circuit: {:?}", fill_duration - pk_duration);

        // create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof(&params, &pk, &[circuit], &[&[]], rng, &mut transcript)?;
        let _proof = transcript.finalize();
        let proof_duration = start.elapsed();
        println!("Proving time: {:?}", proof_duration - fill_duration);
        }
    });
    Ok(())
}

#[cfg(feature = "dev-graph")]
#[test]
fn plot_pairing() {
    let k = 23;
    use plotters::prelude::*;
    create_pairing_circuit!(1, 1, 22, 88, 3);

    let root = BitMapBackend::new("layout.png", (512, 40384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Pairing Layout", ("sans-serif", 60)).unwrap();

    let circuit = PairingCircuit::<Fr>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
