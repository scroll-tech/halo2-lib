#![allow(unused_assignments, unused_imports, unused_variables)]
use std::marker::PhantomData;

use crate::fields::fp::{FpConfig, FpStrategy};
use crate::fields::fp2::Fp2Chip;
use crate::gates::range::RangeStrategy;
use crate::gates::ContextParams;

use super::*;
use halo2_proofs::arithmetic::BaseExt;
use halo2_proofs::circuit::floor_planner::*;
use halo2_proofs::pairing::bn256::{G1Affine, G2Affine, G1, G2};
use halo2_proofs::pairing::group::ff::PrimeField;
use halo2_proofs::pairing::group::Group;
use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq, pairing::bn256::Fr,
    plonk::*,
};
use num_bigint::{BigInt, RandBigInt};

#[derive(Default)]
pub struct MyCircuit<F> {
    pub P: Option<G1Affine>,
    pub Q: Option<G1Affine>,
    pub _marker: PhantomData<F>,
}

const NUM_ADVICE: usize = 2;
const NUM_FIXED: usize = 2;

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FpConfig<F, Fq>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self { P: None, Q: None, _marker: PhantomData }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FpConfig::configure(
            meta,
            FpStrategy::Simple,
            NUM_ADVICE,
            1,
            NUM_FIXED,
            22,
            88,
            3,
            modulus::<Fq>(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load_lookup_table(&mut layouter)?;
        let chip = EccChip::construct(&config);

        let using_simple_floor_planner = true;
        let mut first_pass = true;

        layouter.assign_region(
            || "ecc",
            |region| {
                if first_pass && using_simple_floor_planner {
                    first_pass = false;
                    return Ok(());
                }

                let mut aux = Context::new(
                    region,
                    ContextParams {
                        num_advice: NUM_ADVICE,
                        using_simple_floor_planner,
                        first_pass,
                    },
                );
                let ctx = &mut aux;

                let P_assigned = chip.load_private(
                    ctx,
                    match self.P {
                        Some(P) => (Some(P.x), Some(P.y)),
                        None => (None, None),
                    },
                )?;
                let Q_assigned = chip.load_private(
                    ctx,
                    match self.Q {
                        Some(Q) => (Some(Q.x), Some(Q.y)),
                        None => (None, None),
                    },
                )?;

                // test add_unequal
                {
                    let sum = chip.add_unequal(ctx, &P_assigned, &Q_assigned)?;
                    assert_eq!(sum.x.truncation.to_bigint(), sum.x.value);
                    assert_eq!(sum.y.truncation.to_bigint(), sum.y.value);
                    if self.P != None {
                        let actual_sum = G1Affine::from(self.P.unwrap() + self.Q.unwrap());
                        assert_eq!(bigint_to_fe::<Fq>(&sum.x.value.unwrap()), actual_sum.x);
                        assert_eq!(bigint_to_fe::<Fq>(&sum.y.value.unwrap()), actual_sum.y);
                    }
                    println!("add unequal witness OK");
                }

                // test double
                {
                    let doub = chip.double(ctx, &P_assigned)?;
                    if self.P != None {
                        let actual_doub = G1Affine::from(self.P.unwrap() * Fr::from(2));
                        assert_eq!(bigint_to_fe::<Fq>(&doub.x.value.unwrap()), actual_doub.x);
                        assert_eq!(bigint_to_fe::<Fq>(&doub.y.value.unwrap()), actual_doub.y);
                    }
                    println!("double witness OK");
                }

                println!("Using {} advice columns and {} fixed columns", NUM_ADVICE, NUM_FIXED);
                println!(
                    "maximum rows used by an advice column: {}",
                    ctx.advice_rows.iter().max().unwrap()
                );
                let (const_rows, _, _) = chip.field_chip.finalize(ctx)?;
                println!("maximum rows used by a fixed column: {}", const_rows);

                Ok(())
            },
        )
    }
}

#[cfg(test)]
#[test]
fn test_ecc() {
    let k = 23;
    let mut rng = rand::thread_rng();

    let P = Some(G1Affine::random(&mut rng));
    let Q = Some(G1Affine::random(&mut rng));

    let circuit = MyCircuit::<Fr> { P, Q, _marker: PhantomData };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[cfg(test)]
#[test]
fn plot_ecc() {
    let k = 10;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

    let circuit = MyCircuit::<Fr>::default();

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}

/*
#[derive(Default)]
pub struct G2Circuit<F> {
    P: Option<G2Affine>,
    Q: Option<G2Affine>,
    //P_batch: Vec<Option<G2Affine>>,
    //x: Option<F>,
    //x_batch: Vec<Option<F>>,
    //batch_size: usize,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for G2Circuit<F> {
    type Config = FpConfig<F, NUM_ADVICE, NUM_FIXED>;
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
        FpConfig::configure(meta, 22, 88, 3, modulus::<Fq>())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let fp2_chip = Fp2Chip::construct(config, true);
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
                println!("add unequal witness OK");
            }
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
                println!("double witness OK");
            }
        }

        Ok(())
    }
}

#[cfg(test)]
#[test]
fn test_ecc_g2() {
    let k = 23;
    let mut rng = rand::thread_rng();

    let batch_size = BATCH_SIZE;

    let P = Some(G2Affine::random(&mut rng));
    let Q = Some(G2Affine::random(&mut rng));

    let circuit = G2Circuit::<Fn> { P, Q, _marker: PhantomData };

    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.assert_satisfied();
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
#[cfg(test)]
#[test]
fn plot_ecc_g2() {
    let k = 13;
    use plotters::prelude::*;

    let root = BitMapBackend::new("layout.png", (512, 16384)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

    let batch_size = BATCH_SIZE;
    let circuit = G2Circuit::<Fn> { P: None, Q: None, _marker: PhantomData };

    halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
}
*/
