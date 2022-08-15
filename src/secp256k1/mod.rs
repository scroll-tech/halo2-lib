use halo2_proofs::arithmetic::FieldExt;
use halo2curves::secp256k1::{Fp, Fq};

use crate::ecc;
use crate::fields::{fp, fp_overflow, PrimeFieldChip};

const NUM_ADVICE: usize = 1;
const NUM_FIXED: usize = 1;

type FqOverflowChip<'a, F> = fp_overflow::FpOverflowChip<'a, F, NUM_ADVICE, NUM_FIXED, Fq>;
type FpChip<'a, F> = fp::FpChip<'a, F, NUM_ADVICE, NUM_FIXED, Fp>;
type Secp256k1Chip<'a, F> = ecc::EccChip<'a, F, FpChip<'a, F>>;

const SECP_B: u64 = 7;

// #[cfg(test)]
pub mod tests;
