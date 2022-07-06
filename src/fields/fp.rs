use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};

use crate::bigint::{mul_no_carry, BigIntInstructions, OverflowInteger};
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
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
    ) -> Self {
        meta.enable_equality(value);
        meta.enable_constant(constant);

        let config = FpConfig {
            value,
            constant,
            gate: qap_gate::Config::configure(meta, value),
        };
        Self { config }
    }
}

impl<F: FieldExt> BigIntInstructions<F> for FpChip<F> {
    type BigInt = OverflowInteger<F>;
    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::BigInt,
        b: &Self::BigInt,
    ) -> Result<Self::BigInt, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }
}
