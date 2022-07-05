use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};

pub(super) mod mul_no_carry;

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt, const N_LIMBS: usize> {
    limbs: [AssignedCell<F, F>; N_LIMBS],
    max_bits_per_limb: u32,
}
