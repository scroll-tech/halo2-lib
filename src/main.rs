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

#[derive(Default)]
struct MyCircuit<F> {
    P: Option<G1Affine>,
    Q: Option<G1Affine>,
    P_batch: Vec<Option<G1Affine>>,
    x: Option<F>,
    x_batch: Vec<Option<F>>,
    batch_size: usize,
    _marker: PhantomData<F>,
}

const BATCH_SIZE: usize = 4;

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        let batch_size = BATCH_SIZE;
        Self {
            P: None,
            Q: None,
            P_batch: vec![None; batch_size],
            x: None,
            x_batch: vec![None; batch_size],
            batch_size,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        FpConfig::configure(meta, value, constant, 22, 88, 3, modulus::<Fp>())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let fp_chip = FpChip::construct(config.clone());
        fp_chip.load_lookup_table(&mut layouter)?;
        let range = fp_chip.config.range.clone();
        let chip = EccChip::construct(fp_chip, range);

        let P_assigned = chip.load_private(
            &mut layouter,
            match self.P {
                Some(P) => (Some(P.x), Some(P.y)),
                None => (None, None),
            },
        )?;
        let Q_assigned = chip.load_private(
            &mut layouter,
            match self.Q {
                Some(Q) => (Some(Q.x), Some(Q.y)),
                None => (None, None),
            },
        )?;
        let mut pt = G1Affine::default();

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
        for i in 0..self.batch_size {
            let assigned = chip.load_private(
                &mut layouter,
                match self.P_batch[i] {
                    Some(P) => (Some(P.x), Some(P.y)),
                    None => (None, None),
                },
            )?;
            P_batch_assigned.push(assigned);

            let xb_assigned = layouter.assign_region(
                || "input scalar x",
                |mut region| {
                    region.assign_advice(
                        || format!("assign x_{}", i),
                        config.value,
                        0,
                        || self.x_batch[i].clone().ok_or(Error::Synthesis),
                    )
                },
            )?;
            x_batch_assigned.push(xb_assigned);
        }
        /*
        // test fp mul
        {
            let prod = chip
                .fp_chip
                .mul(&mut layouter, &P_assigned.x, &P_assigned.y)?;
            assert_eq!(prod.value, prod.truncation.to_bigint());
            if self.P != None {
                let actual_prod = self.P.unwrap().x * self.P.unwrap().y;
                assert_eq!(fp_to_bigint(&actual_prod), prod.value.unwrap());
            }
        }
        */

        /*
        // test add_unequal
        {
            let sum = chip.add_unequal(
                &mut layouter.namespace(|| "add_unequal"),
                &P_assigned,
                &Q_assigned,
            )?;
            assert_eq!(sum.x.truncation.to_bigint(), sum.x.value);
            assert_eq!(sum.y.truncation.to_bigint(), sum.y.value);
            if self.P != None {
                let actual_sum = G1Affine::from(self.P.unwrap() + self.Q.unwrap());
                assert_eq!(sum.x.value.unwrap(), fp_to_bigint(&actual_sum.x));
                assert_eq!(sum.y.value.unwrap(), fp_to_bigint(&actual_sum.y));
            }
        }
        */

        /*
        // test double
        {
            let doub = chip.double(&mut layouter.namespace(|| "double"), &P_assigned)?;
            if self.P != None {
                let actual_doub = G1Affine::from(self.P.unwrap() * Fn::from(2));
                assert_eq!(doub.x.value.unwrap(), fp_to_bigint(&actual_doub.x));
                assert_eq!(doub.y.value.unwrap(), fp_to_bigint(&actual_doub.y));
            }
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
            assert_eq!(scalar_mult.x.truncation.to_bigint(), scalar_mult.x.value);
            assert_eq!(scalar_mult.y.truncation.to_bigint(), scalar_mult.y.value);
            if self.P != None {
                let actual = G1Affine::from(
                    &self.P.unwrap()
                        * Fn::from_repr_vartime(
                            self.x.unwrap().to_repr().as_ref()[..32].try_into().unwrap(),
                        )
                        .unwrap(),
                );
                assert_eq!(fp_to_bigint(&actual.x), scalar_mult.x.value.unwrap());
                assert_eq!(fp_to_bigint(&actual.y), scalar_mult.y.value.unwrap());
                println!("OK");
            }
        }
        */

        // test multi scalar mult
        {
            let multi_scalar_mult = chip.multi_scalar_mult::<G1Affine>(
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

    let circuit = MyCircuit::<Fn> {
        P,
        Q,
        P_batch,
        x,
        x_batch,
        batch_size,
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
