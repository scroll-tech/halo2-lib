use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;
pub mod mul_no_carry;

pub trait BigIntInstructions<F: FieldExt> {
    type BigInt;

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &Self::BigInt,
        b: &Self::BigInt,
    ) -> Result<Self::BigInt, Error>;
}

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    limbs: Vec<AssignedCell<F, F>>,
    max_limb_size: BigUint,
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(limbs: Vec<AssignedCell<F, F>>, max_limb_size: BigUint) -> Self {
        Self {
            limbs,
            max_limb_size,
        }
    }
}
