use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::Layouter,
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use crate::fields::fp2::Fp2Chip;
use crate::fields::FqPoint;
use crate::utils::decompose_bigint_option;
use crate::utils::{bigint_to_fe, fe_to_biguint};
use crate::{
    bigint::{
        add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
        sub_no_carry, CRTInteger, OverflowInteger,
    },
    utils::modulus,
};

use super::{FieldChip, FieldExtConstructor, PrimeFieldChip};

const XI_0: u64 = 9;
/// Represent Fp12 point as FqPoint with degree = 12
/// `Fp12 = Fp2[w] / (w^6 - u - xi)`
/// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to
/// be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
/// This means we store an Fp12 point as `\sum_{i = 0}^6 (a_{i0} + a_{i1} * u) * w^i`
/// This is encoded in an FqPoint of degree 12 as `(a_{00}, ..., a_{50}, a_{01}, ..., a_{51})`
pub struct Fp12Chip<'a, F: FieldExt, FpChip: PrimeFieldChip<F>, Fp12: Field> {
    pub fp_chip: &'a mut FpChip,
    _f: PhantomData<F>,
    _fp12: PhantomData<Fp12>,
}

impl<'a, F, FpChip, Fp12> Fp12Chip<'a, F, FpChip, Fp12>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<F, FieldPoint = CRTInteger<F>>,
    FpChip::FieldType: PrimeField,
    Fp12: Field + FieldExtConstructor<FpChip::FieldType, 12>,
{
    /// User must construct an `FpChip` first using a config. This is intended so everything shares a single `FlexGateChip`, which is needed for the column allocation to work.
    pub fn construct(fp_chip: &'a mut FpChip) -> Self {
        Self { fp_chip, _f: PhantomData, _fp12: PhantomData }
    }

    pub fn fp2_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        fp2_pt: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let deg = 6;
        assert_eq!(a.degree, 12);
        assert_eq!(fp2_pt.degree, 2);

        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            let coeff1 = self.fp_chip.mul_no_carry(layouter, &a.coeffs[i], &fp2_pt.coeffs[0])?;
            let coeff2 =
                self.fp_chip.mul_no_carry(layouter, &a.coeffs[i + 6], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.sub_no_carry(layouter, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        for i in 0..6 {
            let coeff1 =
                self.fp_chip.mul_no_carry(layouter, &a.coeffs[i + 6], &fp2_pt.coeffs[0])?;
            let coeff2 = self.fp_chip.mul_no_carry(layouter, &a.coeffs[i], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, 12))
    }

    // for \sum_i (a_i + b_i u) w^i, returns \sum_i (-1)^i (a_i + b_i u) w^i
    pub fn conjugate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, 12);

        let coeffs = a
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if i % 2 == 0 {
                    c.clone()
                } else {
                    self.fp_chip.negate(layouter, c).expect("fp negate should not fail")
                }
            })
            .collect();
        Ok(FqPoint::construct(coeffs, 12))
    }
}

impl<F, FpChip, Fp12> FieldChip<F> for Fp12Chip<'_, F, FpChip, Fp12>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<
        F,
        FieldPoint = CRTInteger<F>,
        WitnessType = Option<BigInt>,
        ConstantType = BigInt,
    >,
    FpChip::FieldType: PrimeField,
    Fp12: Field + FieldExtConstructor<FpChip::FieldType, 12>,
{
    type ConstantType = Fp12;
    type WitnessType = Vec<Option<BigInt>>;
    type FieldPoint = FqPoint<F>;
    type FieldType = Fp12;
    type RangeChip = FpChip::RangeChip;

    fn range(&mut self) -> &mut Self::RangeChip {
        self.fp_chip.range()
    }

    fn get_assigned_value(x: &FqPoint<F>) -> Option<Fp12> {
        assert_eq!(x.coeffs.len(), 12);
        let values: Vec<Option<BigInt>> = x.coeffs.iter().map(|v| v.value.clone()).collect();
        let values_collected: Option<Vec<BigInt>> = values.into_iter().collect();
        match values_collected {
            Some(c_bigint) => {
                let mut c = [FpChip::FieldType::zero(); 12];
                for i in 0..12 {
                    c[i] = bigint_to_fe(&c_bigint[i])
                }
                Some(Fp12::new(c))
            }
            None => None,
        }
    }

    fn fe_to_witness(x: &Option<Fp12>) -> Vec<Option<BigInt>> {
        match x.as_ref() {
            Some(x) => x.coeffs().iter().map(|c| Some(BigInt::from(fe_to_biguint(c)))).collect(),
            None => vec![None; 12],
        }
    }

    fn load_private(
        &mut self,
        layouter: &mut impl Layouter<F>,
        coeffs: Vec<Option<BigInt>>,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(12);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(layouter, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 12))
    }

    fn load_constant(
        &mut self,
        layouter: &mut impl Layouter<F>,
        c: Fp12,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(12);
        for a in &c.coeffs() {
            let assigned_coeff =
                self.fp_chip.load_constant(layouter, BigInt::from(fe_to_biguint(a)))?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 12))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self.fp_chip.add_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn sub_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self.fp_chip.sub_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn negate(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let out_coeff = self.fp_chip.negate(layouter, a_coeff)?;
            out_coeffs.push(out_coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn scalar_mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: F,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self.fp_chip.scalar_mul_no_carry(layouter, &a.coeffs[i], b)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    // w^6 = u + xi for xi = 9
    fn mul_no_carry(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let deg = 6;
        let xi = XI_0;
        assert_eq!(a.degree, 12);
        assert_eq!(b.degree, 12);

        // a = \sum_{i = 0}^5 (a_i * w^i + a_{i + 6} * w^i * u)
        // b = \sum_{i = 0}^5 (b_i * w^i + b_{i + 6} * w^i * u)
        let mut a0b0_coeffs = Vec::with_capacity(11);
        let mut a0b1_coeffs = Vec::with_capacity(11);
        let mut a1b0_coeffs = Vec::with_capacity(11);
        let mut a1b1_coeffs = Vec::with_capacity(11);
        for i in 0..6 {
            for j in 0..6 {
                let coeff00 = self.fp_chip.mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j])?;
                let coeff01 =
                    self.fp_chip.mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j + 6])?;
                let coeff10 =
                    self.fp_chip.mul_no_carry(layouter, &a.coeffs[i + 6], &b.coeffs[j])?;
                let coeff11 =
                    self.fp_chip.mul_no_carry(layouter, &a.coeffs[i + 6], &b.coeffs[j + 6])?;
                if i + j < a0b0_coeffs.len() {
                    a0b0_coeffs[i + j] =
                        self.fp_chip.add_no_carry(layouter, &a0b0_coeffs[i + j], &coeff00)?;
                    a0b1_coeffs[i + j] =
                        self.fp_chip.add_no_carry(layouter, &a0b1_coeffs[i + j], &coeff01)?;
                    a1b0_coeffs[i + j] =
                        self.fp_chip.add_no_carry(layouter, &a1b0_coeffs[i + j], &coeff10)?;
                    a1b1_coeffs[i + j] =
                        self.fp_chip.add_no_carry(layouter, &a1b1_coeffs[i + j], &coeff11)?;
                } else {
                    a0b0_coeffs.push(coeff00);
                    a0b1_coeffs.push(coeff01);
                    a1b0_coeffs.push(coeff10);
                    a1b1_coeffs.push(coeff11);
                }
            }
        }

        let mut a0b0_minus_a1b1 = Vec::with_capacity(11);
        let mut a0b1_plus_a1b0 = Vec::with_capacity(11);
        for i in 0..11 {
            let a0b0_minus_a1b1_entry =
                self.fp_chip.sub_no_carry(layouter, &a0b0_coeffs[i], &a1b1_coeffs[i])?;
            let a0b1_plus_a1b0_entry =
                self.fp_chip.add_no_carry(layouter, &a0b1_coeffs[i], &a1b0_coeffs[i])?;

            a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
            a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
        }

        // out_i       = a0b0_minus_a1b1_i + XI_0 * a0b0_minus_a1b1_{i + 6} - a0b1_plus_a1b0_{i + 6}
        // out_{i + 6} = a0b1_plus_a1b0_{i} + a0b0_minus_a1b1_{i + 6} + XI_0 * a0b1_plus_a1b0_{i + 6}
        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            if i < 5 {
                let coeff1 = self.fp_chip.sub_no_carry(
                    layouter,
                    &a0b0_minus_a1b1[i],
                    &a0b1_plus_a1b0[i + 6],
                )?;
                let coeff2 = self.fp_chip.scalar_mul_no_carry(
                    layouter,
                    &a0b0_minus_a1b1[i + 6],
                    F::from(XI_0),
                )?;
                let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b0_minus_a1b1[i].clone());
            }
        }
        for i in 0..6 {
            if i < 5 {
                let coeff1 = self.fp_chip.add_no_carry(
                    layouter,
                    &a0b1_plus_a1b0[i],
                    &a0b0_minus_a1b1[i + 6],
                )?;
                let coeff2 = self.fp_chip.scalar_mul_no_carry(
                    layouter,
                    &a0b1_plus_a1b0[i + 6],
                    F::from(XI_0),
                )?;
                let coeff = self.fp_chip.add_no_carry(layouter, &coeff1, &coeff2)?;
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b1_plus_a1b0[i].clone());
            }
        }
        Ok(FqPoint::construct(out_coeffs, 12))
    }

    fn check_carry_mod_to_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<(), Error> {
        for coeff in &a.coeffs {
            self.fp_chip.check_carry_mod_to_zero(layouter, coeff)?;
        }
        Ok(())
    }

    fn carry_mod(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.carry_mod(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<(), Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.range_check(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use halo2_proofs::arithmetic::BaseExt;
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fr, plonk::*,
    };
    use halo2curves::bn254::{Fq, Fq12};
    use num_traits::One;
    use rand::Rng;

    use super::*;
    use crate::fields::fp::{FpChip, FpConfig};
    use crate::fields::{FieldChip, PrimeFieldChip};
    use crate::gates::RangeInstructions;
    use crate::utils::{fe_to_bigint, modulus};
    use num_bigint::{BigInt, BigUint};

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Option<Fq12>,
        b: Option<Fq12>,
        _marker: PhantomData<F>,
    }

    const NUM_ADVICE: usize = 2;
    const NUM_FIXED: usize = 2;

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F, NUM_ADVICE, NUM_FIXED>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            FpConfig::configure(meta, 17, 68, 4, modulus::<Fq>())
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut fp_chip = FpChip::<F, NUM_ADVICE, NUM_FIXED, Fq>::construct(config, true);
            fp_chip.load_lookup_table(&mut layouter)?;
            let mut chip =
                Fp12Chip::<F, FpChip<F, NUM_ADVICE, NUM_FIXED, Fq>, Fq12>::construct(&mut fp_chip);

            let a_assigned = chip.load_private(
                &mut layouter,
                Fp12Chip::<F, FpChip<F, NUM_ADVICE, NUM_FIXED, Fq>, Fq12>::fe_to_witness(&self.a),
            )?;
            let b_assigned = chip.load_private(
                &mut layouter,
                Fp12Chip::<F, FpChip<F, NUM_ADVICE, NUM_FIXED, Fq>, Fq12>::fe_to_witness(&self.b),
            )?;

            // test fp_multiply
            {
                chip.mul(&mut layouter.namespace(|| "fp12 multiply"), &a_assigned, &b_assigned)?;
            }

            println!("Using {} advice columns and {} fixed columns", NUM_ADVICE, NUM_FIXED);
            println!(
                "maximum rows used by an advice column: {}",
                chip.fp_chip.range.gate().advice_rows.iter().max().unwrap()
            );
            // IMPORTANT: this assigns all constants to the fixed columns
            // This is not optional.
            let const_rows =
                chip.fp_chip.range.gate().assign_and_constrain_constants(&mut layouter)?;
            println!("maximum rows used by a fixed column: {}", const_rows);
            Ok(())
        }
    }

    #[test]
    fn test_fp12() {
        let k = 18;
        let mut rng = rand::thread_rng();
        let a = Fq12::random(&mut rng);
        let b = Fq12::random(&mut rng);

        let circuit = MyCircuit::<Fr> { a: Some(a), b: Some(b), _marker: PhantomData };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fp() {
        let k = 9;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fp Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fr>::default();
        halo2_proofs::dev::CircuitLayout::default().render(k, &circuit, &root).unwrap();
    }
}
