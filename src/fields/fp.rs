use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use crate::bigint::*;
use crate::gates::qap_gate;
use crate::gates::range;

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt> {
    value: Column<Advice>,
    constant: Column<Fixed>,
    lookup: TableColumn,
    lookup_bits: usize,
    q_lookup: Selector,
    gate: qap_gate::Config<F>,
    range: range::RangeConfig<F>,
    limb_bits: usize,
    num_limbs: usize,
}

pub struct FpChip<F: FieldExt> {
    config: FpConfig<F>,
}

impl<F: FieldExt> FpChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
    ) -> FpConfig<F> {
        let lookup = meta.lookup_table_column();
        let q_lookup = meta.complex_selector();
        meta.enable_equality(value);
        meta.enable_constant(constant);

        let gate_config = qap_gate::Config::configure(meta, value);
        FpConfig {
            value,
            constant,
            lookup,
            lookup_bits,
            q_lookup,
            gate: gate_config.clone(),
            range: range::RangeConfig::configure(
                meta,
                q_lookup,
                lookup,
                lookup_bits,
                gate_config.clone(),
            ),
            limb_bits,
            num_limbs,
        }
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: Vec<Option<F>>,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice(
                        || "private value",
                        config.value,
                        i,
                        || a.ok_or(Error::Synthesis),
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u32) << 64,
            self.config.limb_bits,
        ))
    }

    pub fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: Vec<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load constant",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice_from_constant(
                        || "constant value",
                        config.value,
                        i,
                        *a,
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u32) << 64,
            64,
        ))
    }

    pub fn mod_reduce(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        desired_num_limbs: usize,
        modulus: num_bigint::BigUint,
    ) -> Result<OverflowInteger<F>, Error> {
        mod_reduce::assign(&self.config.gate, layouter, a, desired_num_limbs, modulus)
    }
}

impl<F: FieldExt> PolynomialInstructions<F> for FpChip<F> {
    type Polynomial = OverflowInteger<F>;

    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Polynomial,
        b: &Self::Polynomial,
    ) -> Result<Self::Polynomial, Error> {
        add_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Polynomial,
        b: &Self::Polynomial,
    ) -> Result<Self::Polynomial, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }
}

impl<F: FieldExt> BigIntInstructions<F> for FpChip<F> {
    type BigInt = OverflowInteger<F>;
    fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<Self::BigInt, Error> {
        decompose::assign(
            &self.config.range,
            layouter,
            a,
            self.config.limb_bits,
            self.config.num_limbs,
        )
    }
}
