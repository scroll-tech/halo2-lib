use halo2_proofs::arithmetic::FieldExt;
use halo2curves::secp256k1::Fp;

use crate::ecc;
use crate::fields::fp;

type FpChip<F> = fp::FpChip<F, Fp>;
type Secp256k1Chip<F> = ecc::EccChip<F, FpChip<F>>;

const SECP_B: u64 = 7;

#[cfg(test)]
pub mod tests;
