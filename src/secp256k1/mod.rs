use halo2_proofs::arithmetic::FieldExt;
use halo2curves::secp256k1::{Fp, Fq};

use crate::ecc;
use crate::fields::{fp, fp_overflow, PrimeFieldChip};

#[allow(dead_code)]
type FqOverflowChip<'a, F> = fp_overflow::FpOverflowChip<'a, F, Fq>;
#[allow(dead_code)]
type FpChip<F> = fp::FpConfig<F, Fp>;
#[allow(dead_code)]
type Secp256k1Chip<'a, F> = ecc::EccChip<'a, F, FpChip<F>>;
#[allow(dead_code)]
const SECP_B: u64 = 7;

#[cfg(test)]
pub mod ecdsa;
