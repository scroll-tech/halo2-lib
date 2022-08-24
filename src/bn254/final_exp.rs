use ff::{Field, PrimeField};
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::Layouter,
    pairing::{
        bn256,
        bn256::{G1Affine, G2Affine, BN_X, SIX_U_PLUS_2_NAF},
    },
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use halo2curves::bn254::{Fq, Fq2, FROBENIUS_COEFF_FQ12_C1};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use super::{Fp12Chip, Fp2Chip, FpChip};
use crate::utils::{
    bigint_to_fe, biguint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint,
    fe_to_biguint, modulus,
};
use crate::{
    ecc::{EccChip, EccPoint},
    fields::{fp::FpConfig, FieldChip, FqPoint},
};

impl<'a, 'b, F: FieldExt> Fp12Chip<'a, 'b, F> {
    // computes a ** (p ** power)
    // only works for p = 3 (mod 4) and p = 1 (mod 6)
    pub fn frobenius_map(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        power: usize,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(modulus::<Fq>() % 4u64, BigUint::from(3u64));
        assert_eq!(modulus::<Fq>() % 6u64, BigUint::from(1u64));
        assert_eq!(a.coeffs.len(), 12);
        let pow = power % 12;
        let mut out_fp2 = Vec::with_capacity(6);

        let mut fp2_chip = Fp2Chip::construct(self.fp_chip);
        for i in 0..6 {
            let frob_coeff = FROBENIUS_COEFF_FQ12_C1[pow].pow_vartime(&[i as u64]);
            // possible optimization (not implemented): load `frob_coeff` as we multiply instead of loading first
            // frobenius map is used infrequently so this is a small optimization

            let mut a_fp2 =
                FqPoint::construct(vec![a.coeffs[i].clone(), a.coeffs[i + 6].clone()], 2);
            if pow % 2 != 0 {
                a_fp2 = fp2_chip.conjugate(layouter, &a_fp2)?;
            }
            // if `frob_coeff` is in `Fp` and not just `Fp2`, then we can be more efficient in multiplication
            if frob_coeff == Fq2::one() {
                out_fp2.push(a_fp2);
            } else if frob_coeff.c1 == Fq::zero() {
                let frob_fixed = fp2_chip
                    .fp_chip
                    .load_constant(layouter, BigInt::from(fe_to_biguint(&frob_coeff.c0)))?;
                {
                    let out_nocarry = fp2_chip.fp_mul_no_carry(layouter, &a_fp2, &frob_fixed)?;
                    out_fp2.push(
                        fp2_chip
                            .carry_mod(layouter, &out_nocarry)
                            .expect("carry mod should not fail"),
                    );
                }
            } else {
                let frob_fixed = fp2_chip.load_constant(layouter, frob_coeff)?;
                out_fp2.push(
                    fp2_chip.mul(layouter, &a_fp2, &frob_fixed).expect("fp2 mul should not fail"),
                );
            }
        }

        let out_coeffs = out_fp2
            .iter()
            .map(|x| x.coeffs[0].clone())
            .chain(out_fp2.iter().map(|x| x.coeffs[1].clone()))
            .collect();

        Ok(FqPoint::construct(out_coeffs, 12))
    }

    // exp is in little-endian
    pub fn pow<S: AsRef<[u64]>>(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        exp: S,
    ) -> Result<FqPoint<F>, Error> {
        let mut res = a.clone();
        let mut is_started = false;
        for e in exp.as_ref().iter().rev() {
            for i in (0..64).rev() {
                if is_started {
                    res = self.mul(layouter, &res, &res)?;
                }

                if ((*e >> i) & 1) == 1 {
                    if is_started {
                        res = self.mul(layouter, &res, a)?;
                    } else {
                        is_started = true;
                    }
                }
            }
        }
        Ok(res)
    }

    #[allow(non_snake_case)]
    // use equation for (p^4 - p^2 + 1)/r in Section 5 of https://eprint.iacr.org/2008/490.pdf for BN curves
    pub fn hard_part_BN(
        &mut self,
        layouter: &mut impl Layouter<F>,
        m: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        // x = BN_X

        // m^x
        let mx = self.pow(layouter, m, &[BN_X])?;
        // m^{x^2}
        let mx2 = self.pow(layouter, &mx, &[BN_X])?;
        // m^{x^3}
        let mx3 = self.pow(layouter, &mx2, &[BN_X])?;

        // m^p
        let mp = self.frobenius_map(layouter, m, 1)?;
        // m^{p^2}
        let mp2 = self.frobenius_map(layouter, m, 2)?;
        // m^{p^3}
        let mp3 = self.frobenius_map(layouter, m, 3)?;
        // (m^x)^p
        let mxp = self.frobenius_map(layouter, &mx, 1)?;
        // (m^{x^2})^p
        let mx2p = self.frobenius_map(layouter, &mx2, 1)?;
        // (m^{x^3})^p
        let mx3p = self.frobenius_map(layouter, &mx3, 1)?;

        // y0 = m^p * m^{p^2} * m^{p^3}
        let mp2_mp3 = self.mul(layouter, &mp2, &mp3)?;
        let y0 = self.mul(layouter, &mp, &mp2_mp3)?;
        // y1 = 1/m,  inverse = frob(6) = conjugation in cyclotomic subgroup
        let y1 = self.conjugate(layouter, m)?;
        // y2 = (m^{x^2})^{p^2}
        let y2 = self.frobenius_map(layouter, &mx2, 2)?;
        // y3 = 1/mxp
        let y3 = self.conjugate(layouter, &mxp)?;
        // y4 = 1/(mx * mx2p)
        let mx_mx2p = self.mul(layouter, &mx, &mx2p)?;
        let y4 = self.conjugate(layouter, &mx_mx2p)?;
        // y5 = 1/mx2
        let y5 = self.conjugate(layouter, &mx2)?;
        // y6 = 1/(mx3 * mx3p)
        let mx3_mx3p = self.mul(layouter, &mx3, &mx3p)?;
        let y6 = self.conjugate(layouter, &mx3_mx3p)?;

        // out = y0 * y1^2 * y2^6 * y3^12 * y4^18 * y5^30 * y6^36
        // we compute this using the vectorial addition chain from p. 6 of https://eprint.iacr.org/2008/490.pdf
        let mut T0 = self.mul(layouter, &y6, &y6)?;
        T0 = self.mul(layouter, &T0, &y4)?;
        T0 = self.mul(layouter, &T0, &y5)?;
        let mut T1 = self.mul(layouter, &y3, &y5)?;
        T1 = self.mul(layouter, &T1, &T0)?;
        T0 = self.mul(layouter, &T0, &y2)?;
        T1 = self.mul(layouter, &T1, &T1)?;
        T1 = self.mul(layouter, &T1, &T0)?;
        T1 = self.mul(layouter, &T1, &T1)?;
        T0 = self.mul(layouter, &T1, &y1)?;
        T1 = self.mul(layouter, &T1, &y0)?;
        T0 = self.mul(layouter, &T0, &T0)?;
        T0 = self.mul(layouter, &T0, &T1)?;

        Ok(T0)
    }

    // out = in^{ (q^6 - 1)*(q^2 + 1) }
    pub fn easy_part(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        // a^{q^6} = conjugate of a
        let f1 = self.conjugate(layouter, a)?;
        let f2 = self.divide(layouter, &f1, a)?;
        let f3 = self.frobenius_map(layouter, &f2, 2)?;
        let f = self.mul(layouter, &f3, &f2)?;
        Ok(f)
    }

    // out = in^{(q^12 - 1)/r}
    pub fn final_exp(
        & mut self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let f0 = self.easy_part(layouter, a)?;
        let f = self.hard_part_BN(layouter, &f0)?;
        Ok(f)
    }
}
