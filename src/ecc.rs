use crate::bigint::OverflowInteger;
use crate::utils::*;
use halo2_proofs::{arithmetic::FieldExt, circuit::*};

pub mod add_unequal;

#[derive(Clone, Debug)]
pub struct EccPoint<F: FieldExt> {
    x: OverflowInteger<F>,
    y: OverflowInteger<F>,
}

impl<F: FieldExt> EccPoint<F> {
    pub fn construct(x: OverflowInteger<F>, y: OverflowInteger<F>) -> Self {
        Self { x, y }
    }
}
