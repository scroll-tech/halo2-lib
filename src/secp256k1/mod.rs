use halo2_proofs::arithmetic::FieldExt;
use halo2curves::secp256k1::{Fp, Fq};

use crate::ecc;
use crate::fields::{fp, fp_overflow, PrimeFieldChip};

type FqOverflowChip<'a, F> = fp_overflow::FpOverflowChip<'a, F, Fq>;
type FpChip<'a, F> = fp::FpChip<'a, F, Fp>;
type Secp256k1Chip<'a, F> = ecc::EccChip<'a, F, FpChip<'a, F>>;

const SECP_B: u64 = 7;

pub mod ecdsa;
