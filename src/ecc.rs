use std::str::FromStr;

use crate::bigint::OverflowInteger;
use crate::utils::*;
use halo2_proofs::{arithmetic::FieldExt, circuit::*};
use num_bigint::BigUint;

pub mod add_unequal;

use lazy_static::lazy_static;
lazy_static! {
    static ref FP_MODULUS: BigUint = BigUint::from_str(
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
    )
    .unwrap();
}

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
