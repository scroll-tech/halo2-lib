#![cfg(test)]
#![allow(non_snake_case)]
use std::marker::PhantomData;

use super::pairing::PairingChip;
use super::*;
use crate::fields::fp::FpConfig;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::pairing::bn256::{
    multi_miller_loop, pairing, G1Affine, G2Affine, G2Prepared, Gt, G1, G2,
};
use halo2_proofs::pairing::group::ff::PrimeField;
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr,
    plonk::*,
};
use halo2curves::bn254::Fq12;
use num_bigint::{BigInt, RandBigInt};

#[derive(Default)]
struct PairingCircuit<F> {
    P: Option<G1Affine>,
    Q: Option<G2Affine>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for PairingCircuit<F> {
    type Config = FpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        PairingChip::configure(meta, value, constant, 22, 88, 3)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = PairingChip::construct(config);
        chip.fp12_chip.fp_chip.load_lookup_table(&mut layouter)?;

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
                let f_val: Vec<String> = f
                    .coeffs
                    .iter()
                    .map(|x| x.value.clone().unwrap().to_str_radix(16))
                    .collect();
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
                let f_val: Vec<String> =
                    f.coeffs.iter().map(|x| x.value.clone().unwrap().to_str_radix(16)).collect();
                println!("optimal ate pairing:");
                println!("actual f: {:#?}", actual_f);
                println!("circuit f: {:#?}", f_val);
            }
        }

        Ok(())
    }
}

#[test]
fn test_pairing() {
    let k = 23;
    let mut rng = rand::thread_rng();

    let P = Some(G1Affine::random(&mut rng));
    let Q = Some(G2Affine::random(&mut rng));

    let circuit = PairingCircuit::<Fr> { P, Q, _marker: PhantomData };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[test]
fn plot_pairing() {
    let k = 12;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Pairing Layout", ("sans-serif", 60)).unwrap();

    let circuit = PairingCircuit::<Fn>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
