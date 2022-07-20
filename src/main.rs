use std::marker::PhantomData;

use halo2_pairing::ecc::*;
use halo2_pairing::fields::fp::FpConfig;
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
#[allow(non_snake_case)]
struct MyCircuit<F> {
    P: Option<(Fp, Fp)>,
    Q: Option<(Fp, Fp)>,
    x: Option<F>,
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
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        EccChip::configure(meta, value, constant, 22, 66, 4)
        // EccChip::configure(meta, value, constant, 16, 64, 4)
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

        let _scalar_mult = chip.scalar_mult(
            &mut layouter.namespace(|| "scalar_mult"),
            &P_assigned,
            &x_assigned,
            F::from(3),
            254,
        )?;

        Ok(())
    }
}

#[allow(non_snake_case)]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("At top of run function");
    const K: u32 = 23;
    let params = Params::<G1Affine>::unsafe_setup::<Bn256>(K);

    let mut rng = rand::thread_rng();

    let P = G1Affine::random(&mut rng);
    let Q = G1Affine::random(&mut rng);

    let start = Instant::now();

    let circuit = MyCircuit::<Fn> {
        P: None,
        Q: None,
        x: None,
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
        _marker: PhantomData,
    };
    let duration = start.elapsed();
    println!("Time elapsed in filling circuit: {:?}", duration);

    // create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[], rng, &mut transcript)?;
    let _proof = transcript.finalize();

    println!("Done generating proof");
    let duration = start.elapsed();
    println!("Time elapsed in finalizing proof: {:?}", duration);

    Ok(())
}
