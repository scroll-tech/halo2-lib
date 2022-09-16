use ff::{Field, PrimeField};
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    pairing::{
        bn256,
        bn256::{G1Affine, G2Affine, BN_X, SIX_U_PLUS_2_NAF},
    },
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use halo2curves::bn254::{Fq, Fq2, FROBENIUS_COEFF_FQ12_C1};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use super::{Fp12Chip, Fp2Chip, FpChip, FpPoint};
use crate::{
    ecc::{EccChip, EccPoint},
    fields::{fp12::mul_no_carry_w6, fp2, FieldChip, FieldExtPoint},
    gates::{Context, GateInstructions, QuantumCell::*},
    utils::{
        bigint_to_fe, biguint_to_fe, decompose_bigint_option, decompose_biguint, fe_to_bigint,
        fe_to_biguint, modulus,
    },
};

const XI_0: u64 = 9;

pub fn get_naf(mut exp: Vec<u64>) -> Vec<i8> {
    // https://en.wikipedia.org/wiki/Non-adjacent_form
    // NAF for exp:
    let mut naf: Vec<i8> = Vec::with_capacity(64 * exp.len());
    let len = exp.len();

    // generate the NAF for exp
    for idx in 0..len {
        let mut e: u64 = exp[idx];
        for i in 0..64 {
            if e & 1 == 1 {
                let z = 2i8 - (e % 4) as i8;
                e = e / 2;
                if z == -1 {
                    e += 1;
                }
                naf.push(z);
            } else {
                naf.push(0);
                e = e / 2;
            }
        }
        if e != 0 {
            assert_eq!(e, 1);
            let mut j = idx + 1;
            while j < exp.len() && exp[j] == u64::MAX {
                exp[j] = 0;
                j += 1;
            }
            if j < exp.len() {
                exp[j] += 1;
            } else {
                exp.push(1);
            }
        }
    }
    if exp.len() != len {
        assert_eq!(len, exp.len() + 1);
        assert!(exp[len] == 1);
        naf.push(1);
    }
    naf
}

impl<'a, F: FieldExt> Fp12Chip<'a, F> {
    // computes a ** (p ** power)
    // only works for p = 3 (mod 4) and p = 1 (mod 6)
    pub fn frobenius_map(
        &self,
        ctx: &mut Context<'_, F>,
        a: &<Self as FieldChip<F>>::FieldPoint,
        power: usize,
    ) -> Result<<Self as FieldChip<F>>::FieldPoint, Error> {
        assert_eq!(modulus::<Fq>() % 4u64, BigUint::from(3u64));
        assert_eq!(modulus::<Fq>() % 6u64, BigUint::from(1u64));
        assert_eq!(a.coeffs.len(), 12);
        let pow = power % 12;
        let mut out_fp2 = Vec::with_capacity(6);

        let fp2_chip = Fp2Chip::construct(self.fp_chip);
        for i in 0..6 {
            let frob_coeff = FROBENIUS_COEFF_FQ12_C1[pow].pow_vartime(&[i as u64]);
            // possible optimization (not implemented): load `frob_coeff` as we multiply instead of loading first
            // frobenius map is used infrequently so this is a small optimization

            let mut a_fp2 =
                FieldExtPoint::construct(vec![a.coeffs[i].clone(), a.coeffs[i + 6].clone()]);
            if pow % 2 != 0 {
                a_fp2 = fp2_chip.conjugate(ctx, &a_fp2)?;
            }
            // if `frob_coeff` is in `Fp` and not just `Fp2`, then we can be more efficient in multiplication
            if frob_coeff == Fq2::one() {
                out_fp2.push(a_fp2);
            } else if frob_coeff.c1 == Fq::zero() {
                let frob_fixed = fp2_chip
                    .fp_chip
                    .load_constant(ctx, BigInt::from(fe_to_biguint(&frob_coeff.c0)))?;
                {
                    let out_nocarry = fp2_chip.fp_mul_no_carry(ctx, &a_fp2, &frob_fixed)?;
                    out_fp2.push(
                        fp2_chip.carry_mod(ctx, &out_nocarry).expect("carry mod should not fail"),
                    );
                }
            } else {
                let frob_fixed = fp2_chip.load_constant(ctx, frob_coeff)?;
                out_fp2
                    .push(fp2_chip.mul(ctx, &a_fp2, &frob_fixed).expect("fp2 mul should not fail"));
            }
        }

        let out_coeffs = out_fp2
            .iter()
            .map(|x| x.coeffs[0].clone())
            .chain(out_fp2.iter().map(|x| x.coeffs[1].clone()))
            .collect();

        Ok(FieldExtPoint::construct(out_coeffs))
    }

    // exp is in little-endian
    pub fn pow(
        &self,
        ctx: &mut Context<'_, F>,
        a: &<Self as FieldChip<F>>::FieldPoint,
        exp: Vec<u64>,
    ) -> Result<<Self as FieldChip<F>>::FieldPoint, Error> {
        let mut res = a.clone();
        let mut is_started = false;
        let naf = get_naf(exp);

        for &z in naf.iter().rev() {
            if is_started {
                res = self.mul(ctx, &res, &res)?;
            }

            if z != 0 {
                assert!(z == 1 || z == -1);
                if is_started {
                    res = if z == 1 { self.mul(ctx, &res, a)? } else { self.divide(ctx, &res, a)? };
                } else {
                    assert_eq!(z, 1);
                    is_started = true;
                }
            }
        }

        Ok(res)
    }

    // assume input is an element of Fp12 in the cyclotomic subgroup GΦ₁₂
    // A cyclotomic group is a subgroup of Fp^n defined by
    //   GΦₙ(p) = {α ∈ Fpⁿ : α^{Φₙ(p)} = 1}

    // below we implement compression and decompression for an element  GΦ₁₂ following Theorem 3.1 of https://eprint.iacr.org/2010/542.pdf
    // Fp4 = Fp2(w^3) where (w^3)^2 = XI_0 +u
    // Fp12 = Fp4(w) where w^3 = w^3

    /// in = g0 + g2 w + g4 w^2 + g1 w^3 + g3 w^4 + g5 w^5 where g_i = g_i0 + g_i1 * u are elements of Fp2
    /// out = Compress(in) = [ g2, g3, g4, g5 ]
    pub fn cyclotomic_compress(
        &self,
        a: &FieldExtPoint<FpPoint<F>>,
    ) -> Vec<FieldExtPoint<FpPoint<F>>> {
        let g2 = FieldExtPoint::construct(vec![a.coeffs[1].clone(), a.coeffs[1 + 6].clone()]);
        let g3 = FieldExtPoint::construct(vec![a.coeffs[4].clone(), a.coeffs[4 + 6].clone()]);
        let g4 = FieldExtPoint::construct(vec![a.coeffs[2].clone(), a.coeffs[2 + 6].clone()]);
        let g5 = FieldExtPoint::construct(vec![a.coeffs[5].clone(), a.coeffs[5 + 6].clone()]);
        vec![g2, g3, g4, g5]
    }

    /// Input:
    /// * `compression = [g2, g3, g4, g5]` where g_i are proper elements of Fp2
    /// Output:
    /// * `Decompress(compression) = g0 + g2 w + g4 w^2 + g1 w^3 + g3 w^4 + g5 w^5` where
    /// * All elements of output are proper elements of Fp2 and:
    ///     c = XI0 + u
    ///     if g2 != 0:
    ///         g1 = (g5^2 * c + 3 g4^2 - 2 g3)/(4g2)
    ///         g0 = (2 g1^2 + g2 * g5 - 3 g3*g4) * c + 1
    ///     if g2 = 0:
    ///         g1 = (2 g4 * g5)/g3
    ///         g0 = (2 g1^2 - 3 g3 * g4) * c + 1    
    pub fn cyclotomic_decompress(
        &self,
        ctx: &mut Context<'_, F>,
        compression: &Vec<FieldExtPoint<FpPoint<F>>>,
    ) -> Result<FieldExtPoint<FpPoint<F>>, Error> {
        assert_eq!(compression.len(), 4);
        let g2 = &compression[0];
        let g3 = &compression[1];
        let g4 = &compression[2];
        let g5 = &compression[3];

        let fp2_chip = Fp2Chip::construct(&self.fp_chip);
        let g5_sq = fp2_chip.mul_no_carry(ctx, &g5, &g5)?;
        let g5_sq_c = mul_no_carry_w6::<F, FpChip<F>, XI_0>(fp2_chip.fp_chip, ctx, &g5_sq)?;

        let g4_sq = fp2_chip.mul_no_carry(ctx, &g4, &g4)?;
        let g4_sq_3 = fp2_chip.scalar_mul_no_carry(ctx, &g4_sq, F::from(3))?;
        let g3_2 = fp2_chip.scalar_mul_no_carry(ctx, &g3, F::from(2))?;

        let mut g1_num = fp2_chip.add_no_carry(ctx, &g5_sq_c, &g4_sq_3)?;
        g1_num = fp2_chip.sub_no_carry(ctx, &g1_num, &g3_2)?;
        // can divide without carrying g1_num or g1_denom (I think)
        let g2_4 = fp2_chip.scalar_mul_no_carry(ctx, &g2, F::from(4))?;
        let g1_1 = fp2_chip.divide(ctx, &g1_num, &g2_4)?;

        let g4_g5 = fp2_chip.mul_no_carry(ctx, &g4, &g5)?;
        let g1_num = fp2_chip.scalar_mul_no_carry(ctx, &g4_g5, F::from(2))?;
        let g1_0 = fp2_chip.divide(ctx, &g1_num, &g3)?;

        let g2_is_zero = fp2_chip.is_zero(ctx, &g2)?;
        // resulting `g1` is already in "carried" format (witness is in `[0, p)`)
        let g1 = fp2_chip.select(ctx, &g1_0, &g1_1, &g2_is_zero)?;

        // share the computation of 2 g1^2 between the two cases
        let g1_sq = fp2_chip.mul_no_carry(ctx, &g1, &g1)?;
        let g1_sq_2 = fp2_chip.scalar_mul_no_carry(ctx, &g1_sq, F::from(2))?;

        let g2_g5 = fp2_chip.mul_no_carry(ctx, &g2, &g5)?;
        let g3_g4 = fp2_chip.mul_no_carry(ctx, &g3, &g4)?;
        let g3_g4_3 = fp2_chip.scalar_mul_no_carry(ctx, &g3_g4, F::from(3))?;
        let temp = fp2_chip.add_no_carry(ctx, &g1_sq_2, &g2_g5)?;
        let temp = fp2_chip.select(ctx, &g1_sq_2, &temp, &g2_is_zero)?;
        let temp = fp2_chip.sub_no_carry(ctx, &temp, &g3_g4_3)?;
        let mut g0 = mul_no_carry_w6::<F, FpChip<F>, XI_0>(fp2_chip.fp_chip, ctx, &temp)?;

        // compute `g0 + 1`
        g0.coeffs[0].truncation.limbs[0] = fp2_chip.range().gate.add(
            ctx,
            &Existing(&g0.coeffs[0].truncation.limbs[0]),
            &Constant(F::from(1)),
        )?;
        g0.coeffs[0].native = fp2_chip.range().gate.add(
            ctx,
            &Existing(&g0.coeffs[0].native),
            &Constant(F::from(1)),
        )?;
        g0.coeffs[0].truncation.max_limb_size += 1usize;
        g0.coeffs[0].truncation.max_size += 1usize;
        g0.coeffs[0].value = g0.coeffs[0].clone().value.map(|v| v + 1usize);

        // finally, carry g0
        g0 = fp2_chip.carry_mod(ctx, &g0)?;

        let mut out_coeffs = Vec::with_capacity(12);
        for i in 0..2 {
            out_coeffs.append(&mut vec![
                g0.coeffs[i].clone(),
                g2.coeffs[i].clone(),
                g4.coeffs[i].clone(),
                g1.coeffs[i].clone(),
                g3.coeffs[i].clone(),
                g5.coeffs[i].clone(),
            ]);
        }
        Ok(FieldExtPoint::construct(out_coeffs))
    }

    // input is [g2, g3, g4, g5] = C(g) in compressed format of `cyclotomic_compress`
    // assume all inputs are proper Fp2 elements
    // output is C(g^2) = [h2, h3, h4, h5] computed using Theorem 3.2 of https://eprint.iacr.org/2010/542.pdf
    // all output elements are proper Fp2 elements (with carry)
    //  c = XI_0 + u
    //  h2 = 2(g2 + 3*c*B_45)
    //  h3 = 3(A_45 - (c+1)B_45) - 2g3
    //  h4 = 3(A_23 - (c+1)B_23) - 2g4
    //  h5 = 2(g5 + 3B_23)
    //  A_ij = (g_i + g_j)(g_i + c g_j)
    //  B_ij = g_i g_j

    pub fn cyclotomic_square(
        &self,
        ctx: &mut Context<'_, F>,
        compression: &Vec<FieldExtPoint<FpPoint<F>>>,
    ) -> Result<Vec<FieldExtPoint<FpPoint<F>>>, Error> {
        assert_eq!(compression.len(), 4);
        let g2 = &compression[0];
        let g3 = &compression[1];
        let g4 = &compression[2];
        let g5 = &compression[3];

        let fp2_chip = Fp2Chip::construct(&self.fp_chip);

        let g2_plus_g3 = fp2_chip.add_no_carry(ctx, g2, g3)?;
        let cg3 = mul_no_carry_w6::<F, FpChip<F>, XI_0>(fp2_chip.fp_chip, ctx, g3)?;
        let g2_plus_cg3 = fp2_chip.add_no_carry(ctx, &g2, &cg3)?;
        let a23 = fp2_chip.mul_no_carry(ctx, &g2_plus_g3, &g2_plus_cg3)?;

        let g4_plus_g5 = fp2_chip.add_no_carry(ctx, g4, g5)?;
        let cg5 = mul_no_carry_w6::<F, FpChip<F>, XI_0>(fp2_chip.fp_chip, ctx, g5)?;
        let g4_plus_cg5 = fp2_chip.add_no_carry(ctx, &g4, &cg5)?;
        let a45 = fp2_chip.mul_no_carry(ctx, &g4_plus_g5, &g4_plus_cg5)?;

        let b23 = fp2_chip.mul_no_carry(ctx, &g2, &g3)?;
        let b45 = fp2_chip.mul_no_carry(ctx, &g4, &g5)?;
        let b45_c = mul_no_carry_w6::<F, FpChip<F>, XI_0>(fp2_chip.fp_chip, ctx, &b45)?;

        let mut temp = fp2_chip.scalar_mul_and_add_no_carry(ctx, &b45_c, g2, F::from(3))?;
        let h2 = fp2_chip.scalar_mul_no_carry(ctx, &temp, F::from(2))?;

        temp = fp2_chip.add_no_carry(ctx, &b45_c, &b45)?;
        temp = fp2_chip.sub_no_carry(ctx, &a45, &temp)?;
        temp = fp2_chip.scalar_mul_no_carry(ctx, &temp, F::from(3))?;
        let h3 = fp2_chip.scalar_mul_and_add_no_carry(ctx, &g3, &temp, -F::from(2))?;

        const XI0_PLUS_1: u64 = XI_0 + 1;
        // (c + 1) = (XI_0 + 1) + u
        temp = mul_no_carry_w6::<F, FpChip<F>, XI0_PLUS_1>(fp2_chip.fp_chip, ctx, &b23)?;
        temp = fp2_chip.sub_no_carry(ctx, &a23, &temp)?;
        temp = fp2_chip.scalar_mul_no_carry(ctx, &temp, F::from(3))?;
        let h4 = fp2_chip.scalar_mul_and_add_no_carry(ctx, &g4, &temp, -F::from(2))?;

        temp = fp2_chip.scalar_mul_and_add_no_carry(ctx, &b23, g5, F::from(3))?;
        let h5 = fp2_chip.scalar_mul_no_carry(ctx, &temp, F::from(2))?;

        Ok([h2, h3, h4, h5]
            .iter()
            .map(|h| fp2_chip.carry_mod(ctx, h).expect("carry mod should not fail"))
            .collect())
    }

    // exp is in little-endian
    pub fn cyclotomic_pow(
        &self,
        ctx: &mut Context<'_, F>,
        a: &FieldExtPoint<FpPoint<F>>,
        exp: Vec<u64>,
    ) -> Result<FieldExtPoint<FpPoint<F>>, Error> {
        let mut compression = self.cyclotomic_compress(a);
        let mut res = a.clone();
        let mut is_started = false;
        let naf = get_naf(exp);

        for &z in naf.iter().rev() {
            if is_started {
                compression = self.cyclotomic_square(ctx, &compression)?;
            }
            if z != 0 {
                assert!(z == 1 || z == -1);
                if is_started {
                    res = self.cyclotomic_decompress(ctx, &compression)?;
                    res = if z == 1 { self.mul(ctx, &res, a)? } else { self.divide(ctx, &res, a)? };
                    // compression is free, so it doesn't hurt (except possibly witness generation runtime) to do it
                    // TODO: alternatively we go from small bits to large to avoid this compression
                    compression = self.cyclotomic_compress(&res);
                } else {
                    assert_eq!(z, 1);
                    is_started = true;
                }
            }
        }
        if naf[0] == 0 {
            res = self.cyclotomic_decompress(ctx, &compression)?;
        }
        Ok(res)
    }

    #[allow(non_snake_case)]
    // use equation for (p^4 - p^2 + 1)/r in Section 5 of https://eprint.iacr.org/2008/490.pdf for BN curves
    pub fn hard_part_BN(
        &self,
        ctx: &mut Context<'_, F>,
        m: &<Self as FieldChip<F>>::FieldPoint,
    ) -> Result<<Self as FieldChip<F>>::FieldPoint, Error> {
        // x = BN_X

        // m^x
        let mx = self.cyclotomic_pow(ctx, m, vec![BN_X])?;
        // m^{x^2}
        let mx2 = self.cyclotomic_pow(ctx, &mx, vec![BN_X])?;
        // m^{x^3}
        let mx3 = self.cyclotomic_pow(ctx, &mx2, vec![BN_X])?;

        // m^p
        let mp = self.frobenius_map(ctx, m, 1)?;
        // m^{p^2}
        let mp2 = self.frobenius_map(ctx, m, 2)?;
        // m^{p^3}
        let mp3 = self.frobenius_map(ctx, m, 3)?;
        // (m^x)^p
        let mxp = self.frobenius_map(ctx, &mx, 1)?;
        // (m^{x^2})^p
        let mx2p = self.frobenius_map(ctx, &mx2, 1)?;
        // (m^{x^3})^p
        let mx3p = self.frobenius_map(ctx, &mx3, 1)?;

        // y0 = m^p * m^{p^2} * m^{p^3}
        let mp2_mp3 = self.mul(ctx, &mp2, &mp3)?;
        let y0 = self.mul(ctx, &mp, &mp2_mp3)?;
        // y1 = 1/m,  inverse = frob(6) = conjugation in cyclotomic subgroup
        let y1 = self.conjugate(ctx, m)?;
        // y2 = (m^{x^2})^{p^2}
        let y2 = self.frobenius_map(ctx, &mx2, 2)?;
        // y3 = 1/mxp
        let y3 = self.conjugate(ctx, &mxp)?;
        // y4 = 1/(mx * mx2p)
        let mx_mx2p = self.mul(ctx, &mx, &mx2p)?;
        let y4 = self.conjugate(ctx, &mx_mx2p)?;
        // y5 = 1/mx2
        let y5 = self.conjugate(ctx, &mx2)?;
        // y6 = 1/(mx3 * mx3p)
        let mx3_mx3p = self.mul(ctx, &mx3, &mx3p)?;
        let y6 = self.conjugate(ctx, &mx3_mx3p)?;

        // out = y0 * y1^2 * y2^6 * y3^12 * y4^18 * y5^30 * y6^36
        // we compute this using the vectorial addition chain from p. 6 of https://eprint.iacr.org/2008/490.pdf
        let mut T0 = self.mul(ctx, &y6, &y6)?;
        T0 = self.mul(ctx, &T0, &y4)?;
        T0 = self.mul(ctx, &T0, &y5)?;
        let mut T1 = self.mul(ctx, &y3, &y5)?;
        T1 = self.mul(ctx, &T1, &T0)?;
        T0 = self.mul(ctx, &T0, &y2)?;
        T1 = self.mul(ctx, &T1, &T1)?;
        T1 = self.mul(ctx, &T1, &T0)?;
        T1 = self.mul(ctx, &T1, &T1)?;
        T0 = self.mul(ctx, &T1, &y1)?;
        T1 = self.mul(ctx, &T1, &y0)?;
        T0 = self.mul(ctx, &T0, &T0)?;
        T0 = self.mul(ctx, &T0, &T1)?;

        Ok(T0)
    }

    // out = in^{ (q^6 - 1)*(q^2 + 1) }
    pub fn easy_part(
        &self,
        ctx: &mut Context<'_, F>,
        a: &<Self as FieldChip<F>>::FieldPoint,
    ) -> Result<<Self as FieldChip<F>>::FieldPoint, Error> {
        // a^{q^6} = conjugate of a
        let f1 = self.conjugate(ctx, a)?;
        let f2 = self.divide(ctx, &f1, a)?;
        let f3 = self.frobenius_map(ctx, &f2, 2)?;
        let f = self.mul(ctx, &f3, &f2)?;
        Ok(f)
    }

    // out = in^{(q^12 - 1)/r}
    pub fn final_exp(
        &self,
        ctx: &mut Context<'_, F>,
        a: &<Self as FieldChip<F>>::FieldPoint,
    ) -> Result<<Self as FieldChip<F>>::FieldPoint, Error> {
        let f0 = self.easy_part(ctx, a)?;
        let f = self.hard_part_BN(ctx, &f0)?;
        Ok(f)
    }
}
