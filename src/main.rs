#![allow(non_snake_case)]
use std::marker::PhantomData;

use halo2_pairing::ecc_crt::*;
use halo2_pairing::fields::fp_crt::FpConfig;
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

#[derive(Default)]
struct MyCircuit<F> {
    P: Option<(Fp, Fp)>,
    Q: Option<(Fp, Fp)>,
    x: Option<F>,
    batch_size: usize,
    _marker: PhantomData<F>,
}

#[allow(non_snake_case)]
impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FpConfig<F>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            P: None,
            Q: None,
            x: None,
            batch_size: 4,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        // EccChip::configure(meta, value, constant, 22, 88, 3)
        EccChip::configure(meta, value, constant, 17, 86, 3)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = EccChip::construct(config.clone());
        chip.load_lookup_table(&mut layouter)?;

        let P_assigned = chip.load_private(layouter.namespace(|| "input point P"), self.P)?;
        let Q_assigned = chip.load_private(layouter.namespace(|| "input point Q"), self.Q)?;
        let x_assigned = layouter.assign_region(
            || "input scalar x",
            |mut region| {
                region.assign_advice(
                    || "assign x",
                    config.value,
                    0,
                    || self.x.ok_or(Error::Synthesis),
                )
            },
        )?;

        let mut P_batch_assigned = Vec::with_capacity(self.batch_size);
        let mut x_batch_assigned = Vec::with_capacity(self.batch_size);
        for _ in 0..self.batch_size {
            let assigned = chip.load_private(layouter.namespace(|| "input point P"), self.P)?;
            P_batch_assigned.push(assigned);

            let xb_assigned = layouter.assign_region(
                || "input scalar x",
                |mut region| {
                    region.assign_advice(
                        || "assign x",
                        config.value,
                        0,
                        || self.x.ok_or(Error::Synthesis),
                    )
                },
            )?;
            x_batch_assigned.push(xb_assigned);
        }

        /*
        // test add_unequal
        {
            let sum = chip.add_unequal(
                &mut layouter.namespace(|| "add_unequal"),
                &P_assigned,
                &Q_assigned,
            )?;
        }
        */

        /*
        // test double
        {
            let doub = chip.double(&mut layouter.namespace(|| "double"), &P_assigned)?;
        }
        */

        /*
        // test scalar mult
        {
            let scalar_mult = chip.scalar_mult(
                &mut layouter.namespace(|| "scalar_mult"),
                &P_assigned,
                &x_assigned,
                F::from(3),
                254,
                4,
            )?;
        }
        */

        // test multi scalar mult
        {
            let multi_scalar_mult = chip.multi_scalar_mult(
                &mut layouter.namespace(|| "multi_scalar_mult"),
                &P_batch_assigned,
                &x_batch_assigned,
                F::from(3),
                254,
                4,
            )?;
        }

        Ok(())
    }
}

#[allow(non_snake_case)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("At top of run function");
    const K: u32 = 21;
    let params = Params::<G1Affine>::unsafe_setup::<Bn256>(K);

    let mut rng = rand::thread_rng();

    let P = G1Affine::random(&mut rng);
    let Q = G1Affine::random(&mut rng);

    let start = Instant::now();

    let circuit = MyCircuit::<Fn> {
        P: None,
        Q: None,
        x: None,
        batch_size: 4,
        _marker: PhantomData,
    };

    let vk = keygen_vk(&params, &circuit)?;
    let pk = keygen_pk(&params, vk, &circuit)?;
    let duration = start.elapsed();
    println!("Time elapsed in generating vkey and pkey: {:?}", duration);

    let circuit = MyCircuit::<Fn> {
        P: Some((P.x, P.y)),
        Q: Some((Q.x, Q.y)),
        x: Some(Fn::from(11)),
        batch_size: 4,
        _marker: PhantomData,
    };
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
