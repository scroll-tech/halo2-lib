use halo2_proofs::arithmetic::FieldExt;
use halo2curves::bn254::{Fq, Fq12, Fq2, Fq6};

use crate::{
    bigint::{CRTInteger, OverflowInteger},
    fields::{fp, fp12, fp2, fp_overflow, FieldExtConstructor, FieldExtPoint},
    utils::{biguint_to_fe, fe_to_biguint},
};

pub mod final_exp;
pub mod pairing;

type FpChip<F> = fp::FpConfig<F, Fq>;
type FpPoint<F> = CRTInteger<F>;
// type FpChip<'a, F> = fp_overflow::FpOverflowChip<'a, F, Fq>;
// type FpPoint<F> = OverflowInteger<F>;
type FqPoint<F> = FieldExtPoint<FpPoint<F>>;
type Fp2Chip<'a, F> = fp2::Fp2Chip<'a, F, FpChip<F>, Fq2>;
type Fp12Chip<'a, F> = fp12::Fp12Chip<'a, F, FpChip<F>, Fq12, 9>;

impl FieldExtConstructor<Fq, 2> for Fq2 {
    fn new(c: [Fq; 2]) -> Self {
        Fq2 { c0: c[0], c1: c[1] }
    }

    fn coeffs(&self) -> Vec<Fq> {
        vec![self.c0, self.c1]
    }
}

// This means we store an Fp12 point as `\sum_{i = 0}^6 (a_{i0} + a_{i1} * u) * w^i`
// This is encoded in an FqPoint of degree 12 as `(a_{00}, ..., a_{50}, a_{01}, ..., a_{51})`
impl FieldExtConstructor<Fq, 12> for Fq12 {
    fn new(c: [Fq; 12]) -> Self {
        Fq12 {
            c0: Fq6 {
                c0: Fq2 { c0: c[0], c1: c[6] },
                c1: Fq2 { c0: c[2], c1: c[8] },
                c2: Fq2 { c0: c[4], c1: c[10] },
            },
            c1: Fq6 {
                c0: Fq2 { c0: c[1], c1: c[7] },
                c1: Fq2 { c0: c[3], c1: c[9] },
                c2: Fq2 { c0: c[5], c1: c[11] },
            },
        }
    }

    fn coeffs(&self) -> Vec<Fq> {
        let x = self;
        vec![
            x.c0.c0.c0, x.c1.c0.c0, x.c0.c1.c0, x.c1.c1.c0, x.c0.c2.c0, x.c1.c2.c0, x.c0.c0.c1,
            x.c1.c0.c1, x.c0.c1.c1, x.c1.c1.c1, x.c0.c2.c1, x.c1.c2.c1,
        ]
    }
}

#[cfg(test)]
pub(crate) mod tests;
