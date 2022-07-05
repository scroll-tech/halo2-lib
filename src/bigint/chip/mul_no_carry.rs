use super::OverflowInteger;
use crate::gates::qap_gate;

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};

#[derive(Clone, Debug)]
pub struct Config<F: FieldExt> {
    value: Column<Advice>,
    constant: Column<Fixed>,
    gate: qap_gate::Config<F>,
}

impl<F: FieldExt> Config<F> {
    // value, constant, gate are all shared among different chips, so they none of them should be configured here
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        gate: qap_gate::Config<F>,
    ) -> Self {
        meta.enable_equality(value);
        meta.enable_constant(constant);

        Self {
            value,
            constant,
            gate,
        }
    }
}
