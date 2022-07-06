use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;

use crate::bigint::*;
use crate::gates::qap_gate;

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt> {
    value: Column<Advice>,
    constant: Column<Fixed>,
    gate: qap_gate::Config<F>,
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
    ) -> FpConfig<F> {
        meta.enable_equality(value);
        meta.enable_constant(constant);

        FpConfig {
            value,
            constant,
            gate: qap_gate::Config::configure(meta, value),
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
            big_uint::from(1u32) << 64,
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
            big_uint::from(1u32) << 64,
        ))
    }
}

impl<F: FieldExt> PolynomialInstructions<F> for FpChip<F> {
    type Polynomial = OverflowInteger<F>;
    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::Polynomial,
        b: &Self::Polynomial,
    ) -> Result<Self::Polynomial, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }
}
