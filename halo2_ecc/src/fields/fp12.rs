use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Layouter, Value},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use crate::gates::{
    Context, GateInstructions,
    QuantumCell::{Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::decompose_bigint_option;
use crate::utils::{bigint_to_fe, fe_to_biguint};
use crate::{
    bigint::{
        add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
        sub_no_carry, CRTInteger, OverflowInteger,
    },
    utils::modulus,
};
use crate::{fields::fp2::Fp2Chip, utils::value_to_option};

use super::{FieldChip, FieldExtConstructor, FieldExtPoint, PrimeFieldChip};

/// Represent Fp12 point as FqPoint with degree = 12
/// `Fp12 = Fp2[w] / (w^6 - u - xi)`
/// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to
/// be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
/// This means we store an Fp12 point as `\sum_{i = 0}^6 (a_{i0} + a_{i1} * u) * w^i`
/// This is encoded in an FqPoint of degree 12 as `(a_{00}, ..., a_{50}, a_{01}, ..., a_{51})`
pub struct Fp12Chip<'a, F: FieldExt, FpChip: PrimeFieldChip<F>, Fp12: Field, const XI_0: u64>
where
    FpChip::FieldType: PrimeField,
{
    // for historical reasons, leaving this as a reference
    // for the current implementation we could also just use the de-referenced version: `fp_chip: FpChip`
    pub fp_chip: &'a FpChip,
    _f: PhantomData<F>,
    _fp12: PhantomData<Fp12>,
}

impl<'a, F, FpChip, Fp12, const XI_0: u64> Fp12Chip<'a, F, FpChip, Fp12, XI_0>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<F>,
    FpChip::FieldType: PrimeField,
    Fp12: Field + FieldExtConstructor<FpChip::FieldType, 12>,
{
    /// User must construct an `FpChip` first using a config. This is intended so everything shares a single `FlexGateChip`, which is needed for the column allocation to work.
    pub fn construct(fp_chip: &'a FpChip) -> Self {
        Self { fp_chip, _f: PhantomData, _fp12: PhantomData }
    }

    pub fn fp2_mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
        fp2_pt: &FieldExtPoint<FpChip::FieldPoint>,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error> {
        let deg = 6;
        assert_eq!(a.coeffs.len(), 12);
        assert_eq!(fp2_pt.coeffs.len(), 2);

        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            let coeff1 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i], &fp2_pt.coeffs[0])?;
            let coeff2 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i + 6], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.sub_no_carry(ctx, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        for i in 0..6 {
            let coeff1 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i + 6], &fp2_pt.coeffs[0])?;
            let coeff2 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i], &fp2_pt.coeffs[1])?;
            let coeff = self.fp_chip.add_no_carry(ctx, &coeff1, &coeff2)?;
            out_coeffs.push(coeff);
        }
        Ok(FieldExtPoint::construct(out_coeffs))
    }

    // for \sum_i (a_i + b_i u) w^i, returns \sum_i (-1)^i (a_i + b_i u) w^i
    pub fn conjugate(
        &self,
        ctx: &mut Context<'_, F>,
        a: &FieldExtPoint<FpChip::FieldPoint>,
    ) -> Result<FieldExtPoint<FpChip::FieldPoint>, Error> {
        assert_eq!(a.coeffs.len(), 12);

        let coeffs = a
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if i % 2 == 0 {
                    c.clone()
                } else {
                    self.fp_chip.negate(ctx, c).expect("fp negate should not fail")
                }
            })
            .collect();
        Ok(FieldExtPoint::construct(coeffs))
    }
}

/// multiply (a0 + a1 * u) * (XI0 + u) without carry
pub fn mul_no_carry_w6<F: FieldExt, FC: FieldChip<F>, const XI_0: u64>(
    fp_chip: &FC,
    ctx: &mut Context<'_, F>,
    a: &FieldExtPoint<FC::FieldPoint>,
) -> Result<FieldExtPoint<FC::FieldPoint>, Error> {
    assert_eq!(a.coeffs.len(), 2);
    let (a0, a1) = (&a.coeffs[0], &a.coeffs[1]);
    // (a0 + a1 u) * (XI_0 + u) = (a0 * XI_0 - a1) + (a1 * XI_0 + a0) u     with u^2 = -1
    // This should fit in the overflow representation if limb_bits is large enough
    let a0_xi0 = fp_chip.scalar_mul_no_carry(ctx, a0, F::from(XI_0))?;
    let out0_0_nocarry = fp_chip.sub_no_carry(ctx, &a0_xi0, a1)?;
    let out0_1_nocarry = fp_chip.scalar_mul_and_add_no_carry(ctx, a1, a0, F::from(XI_0))?;
    Ok(FieldExtPoint::construct(vec![out0_0_nocarry, out0_1_nocarry]))
}

impl<'a, F, FpChip, Fp12, const XI_0: u64> FieldChip<F> for Fp12Chip<'a, F, FpChip, Fp12, XI_0>
where
    F: FieldExt,
    FpChip: PrimeFieldChip<F, WitnessType = Value<BigInt>, ConstantType = BigInt>,
    FpChip::FieldType: PrimeField,
    Fp12: Field + FieldExtConstructor<FpChip::FieldType, 12>,
{
    type ConstantType = Fp12;
    type WitnessType = Vec<Value<BigInt>>;
    type FieldPoint = FieldExtPoint<FpChip::FieldPoint>;
    type FieldType = Fp12;
    type RangeChip = FpChip::RangeChip;

    fn range(&self) -> &Self::RangeChip {
        self.fp_chip.range()
    }

    fn get_assigned_value(x: &Self::FieldPoint) -> Value<Fp12> {
        assert_eq!(x.coeffs.len(), 12);
        let values: Vec<Value<FpChip::FieldType>> =
            x.coeffs.iter().map(|v| FpChip::get_assigned_value(v)).collect();
        let values_collected: Value<Vec<FpChip::FieldType>> = values.into_iter().collect();
        values_collected.map(|c| Fp12::new(c.try_into().unwrap()))
    }

    fn fe_to_witness(x: &Value<Fp12>) -> Vec<Value<BigInt>> {
        match value_to_option(x.clone()) {
            Some(x) => {
                x.coeffs().iter().map(|c| Value::known(BigInt::from(fe_to_biguint(c)))).collect()
            }
            None => vec![Value::unknown(); 12],
        }
    }

    fn load_private(
        &self,
        ctx: &mut Context<'_, F>,
        coeffs: Vec<Value<BigInt>>,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(coeffs.len(), 12);
        let mut assigned_coeffs = Vec::with_capacity(12);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(ctx, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(Self::FieldPoint::construct(assigned_coeffs))
    }

    fn load_constant(&self, ctx: &mut Context<'_, F>, c: Fp12) -> Result<Self::FieldPoint, Error> {
        let mut assigned_coeffs = Vec::with_capacity(12);
        for a in &c.coeffs() {
            let assigned_coeff = self.fp_chip.load_constant(ctx, BigInt::from(fe_to_biguint(a)))?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(Self::FieldPoint::construct(assigned_coeffs))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(a.coeffs.len(), b.coeffs.len());
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.add_no_carry(ctx, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn sub_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        assert_eq!(a.coeffs.len(), b.coeffs.len());
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.sub_no_carry(ctx, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn negate(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let out_coeff = self.fp_chip.negate(ctx, a_coeff)?;
            out_coeffs.push(out_coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn scalar_mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: F,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff = self.fp_chip.scalar_mul_no_carry(ctx, &a.coeffs[i], b)?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn scalar_mul_and_add_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
        c: F,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for i in 0..a.coeffs.len() {
            let coeff =
                self.fp_chip.scalar_mul_and_add_no_carry(ctx, &a.coeffs[i], &b.coeffs[i], c)?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    // w^6 = u + xi for xi = 9
    fn mul_no_carry(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let deg = 6;
        let xi = XI_0;
        assert_eq!(a.coeffs.len(), 12);
        assert_eq!(b.coeffs.len(), 12);

        // a = \sum_{i = 0}^5 (a_i * w^i + a_{i + 6} * w^i * u)
        // b = \sum_{i = 0}^5 (b_i * w^i + b_{i + 6} * w^i * u)
        let mut a0b0_coeffs = Vec::with_capacity(11);
        let mut a0b1_coeffs = Vec::with_capacity(11);
        let mut a1b0_coeffs = Vec::with_capacity(11);
        let mut a1b1_coeffs = Vec::with_capacity(11);
        for i in 0..6 {
            for j in 0..6 {
                let coeff00 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i], &b.coeffs[j])?;
                let coeff01 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i], &b.coeffs[j + 6])?;
                let coeff10 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i + 6], &b.coeffs[j])?;
                let coeff11 = self.fp_chip.mul_no_carry(ctx, &a.coeffs[i + 6], &b.coeffs[j + 6])?;
                if i + j < a0b0_coeffs.len() {
                    a0b0_coeffs[i + j] =
                        self.fp_chip.add_no_carry(ctx, &a0b0_coeffs[i + j], &coeff00)?;
                    a0b1_coeffs[i + j] =
                        self.fp_chip.add_no_carry(ctx, &a0b1_coeffs[i + j], &coeff01)?;
                    a1b0_coeffs[i + j] =
                        self.fp_chip.add_no_carry(ctx, &a1b0_coeffs[i + j], &coeff10)?;
                    a1b1_coeffs[i + j] =
                        self.fp_chip.add_no_carry(ctx, &a1b1_coeffs[i + j], &coeff11)?;
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
                self.fp_chip.sub_no_carry(ctx, &a0b0_coeffs[i], &a1b1_coeffs[i])?;
            let a0b1_plus_a1b0_entry =
                self.fp_chip.add_no_carry(ctx, &a0b1_coeffs[i], &a1b0_coeffs[i])?;

            a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
            a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
        }

        // out_i       = a0b0_minus_a1b1_i + XI_0 * a0b0_minus_a1b1_{i + 6} - a0b1_plus_a1b0_{i + 6}
        // out_{i + 6} = a0b1_plus_a1b0_{i} + a0b0_minus_a1b1_{i + 6} + XI_0 * a0b1_plus_a1b0_{i + 6}
        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..6 {
            if i < 5 {
                let mut coeff = self.fp_chip.scalar_mul_and_add_no_carry(
                    ctx,
                    &a0b0_minus_a1b1[i + 6],
                    &a0b0_minus_a1b1[i],
                    F::from(XI_0),
                )?;
                coeff = self.fp_chip.sub_no_carry(ctx, &coeff, &a0b1_plus_a1b0[i + 6])?;
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b0_minus_a1b1[i].clone());
            }
        }
        for i in 0..6 {
            if i < 5 {
                let mut coeff =
                    self.fp_chip.add_no_carry(ctx, &a0b1_plus_a1b0[i], &a0b0_minus_a1b1[i + 6])?;
                coeff = self.fp_chip.scalar_mul_and_add_no_carry(
                    ctx,
                    &a0b1_plus_a1b0[i + 6],
                    &coeff,
                    F::from(XI_0),
                )?;
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b1_plus_a1b0[i].clone());
            }
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn check_carry_mod_to_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<(), Error> {
        for coeff in &a.coeffs {
            self.fp_chip.check_carry_mod_to_zero(ctx, coeff)?;
        }
        Ok(())
    }

    fn carry_mod(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<Self::FieldPoint, Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.carry_mod(ctx, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(Self::FieldPoint::construct(out_coeffs))
    }

    fn range_check(&self, ctx: &mut Context<'_, F>, a: &Self::FieldPoint) -> Result<(), Error> {
        let mut out_coeffs = Vec::with_capacity(a.coeffs.len());
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.range_check(ctx, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(())
    }

    fn is_soft_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_soft_zero(ctx, a_coeff)?;
            if let Some(p) = prev {
                let new = self.fp_chip.range().gate().and(ctx, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }

    fn is_soft_nonzero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_soft_nonzero(ctx, a_coeff)?;
            if let Some(p) = prev {
                let new = self.fp_chip.range().gate().or(ctx, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }

    fn is_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut prev = None;
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.is_zero(ctx, a_coeff)?;
            if let Some(p) = prev {
                let new = self.fp_chip.range().gate().and(ctx, &Existing(&coeff), &Existing(&p))?;
                prev = Some(new);
            } else {
                prev = Some(coeff);
            }
        }
        Ok(prev.unwrap())
    }

    fn is_equal(
        &self,
        ctx: &mut Context<'_, F>,
        a: &Self::FieldPoint,
        b: &Self::FieldPoint,
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut acc = None;
        for (a_coeff, b_coeff) in a.coeffs.iter().zip(b.coeffs.iter()) {
            let coeff = self.fp_chip.is_equal(ctx, a_coeff, b_coeff)?;
            if let Some(c) = acc {
                acc =
                    Some(self.fp_chip.range().gate().and(ctx, &Existing(&coeff), &Existing(&c))?);
            } else {
                acc = Some(coeff);
            }
        }
        Ok(acc.unwrap())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, halo2curves::bn256::Fr, plonk::*,
    };
    use halo2curves::bn254::{Fq, Fq12};
    use num_traits::One;
    use rand::Rng;

    use super::*;
    use crate::fields::fp::{FpConfig, FpStrategy};
    use crate::fields::{FieldChip, PrimeFieldChip};
    use crate::gates::flex_gate::GateStrategy;
    use crate::gates::range::RangeStrategy;
    use crate::gates::{ContextParams, RangeInstructions};
    use crate::utils::{fe_to_bigint, modulus};
    use num_bigint::{BigInt, BigUint};

    #[derive(Default)]
    struct MyCircuit<F> {
        a: Value<Fq12>,
        b: Value<Fq12>,
        _marker: PhantomData<F>,
    }

    const NUM_ADVICE: usize = 1;
    const NUM_FIXED: usize = 1;
    const XI_0: u64 = 9;

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F, Fq>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
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
            let chip = Fp12Chip::<F, FpConfig<F, Fq>, Fq12, XI_0>::construct(&config);

            let using_simple_floor_planner = true;
            let mut first_pass = true;

            layouter.assign_region(
                || "fp12",
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

                    let a_assigned = chip.load_private(
                        ctx,
                        Fp12Chip::<F, FpConfig<F, Fq>, Fq12, XI_0>::fe_to_witness(&self.a),
                    )?;
                    let b_assigned = chip.load_private(
                        ctx,
                        Fp12Chip::<F, FpConfig<F, Fq>, Fq12, XI_0>::fe_to_witness(&self.b),
                    )?;

                    // test fp_multiply
                    {
                        chip.mul(ctx, &a_assigned, &b_assigned)?;
                    }

                    println!("Using {} advice columns and {} fixed columns", NUM_ADVICE, NUM_FIXED);
                    println!(
                        "maximum rows used by an advice column: {}",
                        ctx.advice_rows.iter().max().unwrap()
                    );
                    // IMPORTANT: this assigns all constants to the fixed columns
                    // This is not optional.
                    let (const_rows, _, _) = chip.fp_chip.finalize(ctx)?;
                    println!("maximum rows used by a fixed column: {}", const_rows);
                    Ok(())
                },
            )
        }
    }

    #[test]
    fn test_fp12() {
        let k = 23;
        let mut rng = rand::thread_rng();
        let a = Fq12::random(&mut rng);
        let b = Fq12::random(&mut rng);

        let circuit =
            MyCircuit::<Fr> { a: Value::known(a), b: Value::known(b), _marker: PhantomData };

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
