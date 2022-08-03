use halo2_proofs::arithmetic::FieldExt;
use halo2curves::bn254::{Fq, Fq2};

use crate::{
    fields::{
        fp, fp12,
        fp2::{self, FieldExtConstructor},
    },
    utils::{biguint_to_fe, fe_to_biguint},
};

pub mod pairing;

type FpChip<F> = fp::FpChip<F, Fq>;
type Fp2Chip<F> = fp2::Fp2Chip<F, Fq, Fq2>;
type Fp12Chip<F> = fp12::Fp12Chip<F>;

impl FieldExtConstructor<Fq, 2> for Fq2 {
    fn new(c: [Fq; 2]) -> Self {
        Fq2 {
            c0: c[0].clone(),
            c1: c[1].clone(),
        }
    }

    fn coeffs(&self) -> Vec<Fq> {
        vec![self.c0.clone(), self.c1.clone()]
    }
}

pub(crate) mod tests;