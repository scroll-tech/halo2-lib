#![allow(non_snake_case)]
#![feature(explicit_generic_args_with_impl_trait)]
use std::marker::PhantomData;

use halo2_pairing::ecc::*;
use halo2_pairing::fields::fp::{FpChip, FpConfig};
use halo2_pairing::utils::modulus;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::pairing::bn256::{Bn256, G1Affine};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    pairing::bn256::Fq as Fp,
    pairing::bn256::Fr as Fn,
    plonk::*,
    transcript::{Blake2bWrite, Challenge255},
};
use std::time::{Duration, Instant};

use halo2_pairing::ecc::tests::MyCircuit;
use halo2_pairing::ecc::tests::BATCH_SIZE;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("At top of run function");
    const K: u32 = 21;
    let params = Params::<G1Affine>::unsafe_setup::<Bn256>(K);

    let mut rng = rand::thread_rng();

    let P = G1Affine::random(&mut rng);
    let Q = G1Affine::random(&mut rng);

    let start = Instant::now();
    let batch_size = BATCH_SIZE;
    let circuit = MyCircuit::<Fn> {
        P: None,
        Q: None,
        P_batch: vec![None; batch_size],
        x: None,
        x_batch: vec![None; batch_size],
        batch_size,
        _marker: PhantomData,
    };

    let vk = keygen_vk(&params, &circuit)?;
    let pk = keygen_pk(&params, vk, &circuit)?;
    let duration = start.elapsed();
    println!("Time elapsed in generating vkey and pkey: {:?}", duration);

    let batch_size = BATCH_SIZE;

    let P = Some(G1Affine::random(&mut rng));
    let Q = Some(G1Affine::random(&mut rng));
    let x = Some(Fn::random(&mut rng));
    let mut P_batch = Vec::with_capacity(batch_size);
    let mut x_batch = Vec::with_capacity(batch_size);
    for _ in 0..batch_size {
        P_batch.push(Some(G1Affine::random(&mut rng)));
        x_batch.push(Some(Fn::random(&mut rng)));
    }

    let circuit = MyCircuit::<Fn> { P, Q, P_batch, x, x_batch, batch_size, _marker: PhantomData };

    let duration = start.elapsed();
    println!("Time elapsed in filling circuit: {:?}", duration);

    // create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[], rng, &mut transcript)?;
    let _proof = transcript.finalize();

    println!("Done generating proof");
    let proof_duration = start.elapsed();
    let proof_time = proof_duration - duration;
    println!("Proving time: {:?}", proof_time);

    Ok(())
}
