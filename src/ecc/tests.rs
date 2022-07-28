#![cfg(test)]
use std::marker::PhantomData;

use crate::fields::fp2::Fp2Chip;

use super::*;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::circuit::floor_planner::*;
use halo2_proofs::pairing::bn256::{G1Affine, G2Affine, G1, G2};
use halo2_proofs::pairing::group::ff::PrimeField;
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq as Fp,
    pairing::bn256::Fr as Fn, plonk::*,
};
use halo2curves::bn254::Fq2;
use num_bigint::{BigInt, RandBigInt};

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
        EccChip::<F, FpChip<F>>::configure(meta, value, constant, 22, 88, 3)
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
        let mut P_fixed = FixedEccPoint::from_g1(&pt, 3, 88);
        if let Some(P_point) = &self.P {
            pt = P_point.clone();
            P_fixed = FixedEccPoint::<F>::from_g1(&P_point, 3, 88);
        }

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
                .mul(&mut layouter, &Existing(&P_assigned.x), &Existing(&P_assigned.y))?;
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
                assert_eq!(bigint_to_fe::<Fp>(&sum.x.value.unwrap()), actual_sum.x);
                assert_eq!(bigint_to_fe::<Fp>(&sum.y.value.unwrap()), actual_sum.y);
            }
            println!("add unequal witness OK");
        }

        // test double
        {
            let doub = chip.double(&mut layouter.namespace(|| "double"), &P_assigned)?;
            if self.P != None {
                let actual_doub = G1Affine::from(self.P.unwrap() * Fn::from(2));
                assert_eq!(bigint_to_fe::<Fp>(&doub.x.value.unwrap()), actual_doub.x);
                assert_eq!(bigint_to_fe::<Fp>(&doub.y.value.unwrap()), actual_doub.y);
            }
            println!("double witness OK");
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
                assert_eq!(actual.x, bigint_to_fe(&scalar_mult.x.value.unwrap()));
                assert_eq!(actual.y, bigint_to_fe(&scalar_mult.y.value.unwrap()));
                println!("scalar mult witness OK");
            }
        }
        */

        /*
            // test fixed base scalar mult
            {
                let fixed_base_scalar_mult = chip.fixed_base_scalar_mult(
                    &mut layouter.namespace(|| "fixed_base_scalar_mult"),
                    &P_fixed,
                    &x_assigned,
                    F::from(3),
                    254,
                    4,
                )?;
        if let Some(xv) = &self.x {
            println!("answer {:?}", G1Affine::from(pt * Fr::from_repr(
            (*xv).to_repr().as_ref()[..32].try_into().unwrap()).unwrap()));
            let xx = fixed_base_scalar_mult.x.value;
            let yy = fixed_base_scalar_mult.y.value;
            if let Some(xxx) = &xx {
            if let Some(yyy) = &yy {
                println!("result {:#01x} {:#01x}", xxx, yyy);
            }
            }
        }
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
            assert_eq!(
                multi_scalar_mult.x.truncation.to_bigint(),
                multi_scalar_mult.x.value
            );
            assert_eq!(
                multi_scalar_mult.y.truncation.to_bigint(),
                multi_scalar_mult.y.value
            );
            if self.P_batch[0] != None {
                let mut msm = G1::identity();
                for (P, x) in self.P_batch.iter().zip(self.x_batch.iter()) {
                    msm = msm
                        + P.as_ref().unwrap()
                            * Fn::from_repr(
                                x.as_ref().unwrap().to_repr().as_ref()[..32]
                                    .try_into()
                                    .unwrap(),
                            )
                            .unwrap();
                }
                let actual = G1Affine::from(msm);
                assert_eq!(actual.x, bigint_to_fe(&multi_scalar_mult.x.value.unwrap()));
                assert_eq!(actual.y, bigint_to_fe(&multi_scalar_mult.y.value.unwrap()));
            }
        }
        Ok(())
    }
}

#[test]
fn test_ecc() {
    let k = 23;
    let mut rng = rand::thread_rng();

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

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[test]
fn plot_ecc() {
    let k = 12;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

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

    halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
}

#[derive(Default)]
struct G2Circuit<F> {
    P: Option<G2Affine>,
    Q: Option<G2Affine>,
    //P_batch: Vec<Option<G2Affine>>,
    //x: Option<F>,
    //x_batch: Vec<Option<F>>,
    //batch_size: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for G2Circuit<F> {
    type Config = FpConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        //let batch_size = BATCH_SIZE;
        Self {
            P: None,
            Q: None,
            //P_batch: vec![None; batch_size],
            //x: None,
            //x_batch: vec![None; batch_size],
            //batch_size,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let value = meta.advice_column();
        let constant = meta.fixed_column();
        EccChip::<F, Fp2Chip<F>>::configure(meta, value, constant, 22, 88, 3)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let fp2_chip = Fp2Chip::construct(config.clone());
        config.range.load_lookup_table(&mut layouter)?;
        let range = config.range.clone();
        let chip = EccChip::construct(fp2_chip, range);

        let g2_to_fq2 = |P: G2Affine| -> (Option<Fq2>, Option<Fq2>) {
            let x = Fq2 {
                // converting from Fq in pairing to Fq in my fork of pairing...
                c0: bigint_to_fe(&fe_to_bigint(&P.x.c0)),
                c1: bigint_to_fe(&fe_to_bigint(&P.x.c1)),
            };
            let y = Fq2 {
                c0: bigint_to_fe(&fe_to_bigint(&P.y.c0)),
                c1: bigint_to_fe(&fe_to_bigint(&P.y.c1)),
            };
            (Some(x), Some(y))
        };
        let P_assigned = chip.load_private(
            &mut layouter,
            match self.P {
                Some(P) => g2_to_fq2(P),
                None => (None, None),
            },
        )?;
        let Q_assigned = chip.load_private(
            &mut layouter,
            match self.Q {
                Some(Q) => g2_to_fq2(Q),
                None => (None, None),
            },
        )?;

        // test add_unequal
        {
            let sum = chip.add_unequal(
                &mut layouter.namespace(|| "add_unequal"),
                &P_assigned,
                &Q_assigned,
            )?;
            if self.P != None {
                let actual_sum = G2Affine::from(self.P.unwrap() + self.Q.unwrap());
                assert_eq!(
                    sum.x.coeffs[0].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_sum.x.c0))
                );
                assert_eq!(
                    sum.x.coeffs[1].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_sum.x.c1))
                );
                assert_eq!(
                    sum.y.coeffs[0].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_sum.y.c0))
                );
                assert_eq!(
                    sum.y.coeffs[1].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_sum.y.c1))
                );
            }
            println!("add unequal witness OK");
        }

        // test double
        {
            let doub = chip.double(&mut layouter.namespace(|| "double"), &P_assigned)?;
            if self.P != None {
                let actual_doub = G2Affine::from(self.P.unwrap() * Fn::from(2));
                assert_eq!(
                    doub.x.coeffs[0].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_doub.x.c0))
                );
                assert_eq!(
                    doub.x.coeffs[1].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_doub.x.c1))
                );
                assert_eq!(
                    doub.y.coeffs[0].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_doub.y.c0))
                );
                assert_eq!(
                    doub.y.coeffs[1].value.clone().unwrap(),
                    BigInt::from(fe_to_biguint(&actual_doub.y.c1))
                );
            }
            println!("double witness OK");
        }

        Ok(())
    }
}

#[test]
fn test_ecc_g2() {
    let k = 23;
    let mut rng = rand::thread_rng();

    let batch_size = BATCH_SIZE;

    let P = Some(G2Affine::random(&mut rng));
    let Q = Some(G2Affine::random(&mut rng));

    let circuit = G2Circuit::<Fn> {
        P,
        Q,
        _marker: PhantomData,
    };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[test]
fn plot_ecc_g2() {
    let k = 12;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

    let batch_size = BATCH_SIZE;
    let circuit = G2Circuit::<Fn> {
        P: None,
        Q: None,
        _marker: PhantomData,
    };

    halo2_proofs::dev::CircuitLayout::default()
        .render(k, &circuit, &root)
        .unwrap();
}
