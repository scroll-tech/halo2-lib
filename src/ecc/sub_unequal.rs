use std::str::FromStr;

use halo2_proofs::arithmetic::Field;
use halo2_proofs::pairing::bn256::Fq as Fp;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::{One, Zero};

use super::*;
use crate::bigint::*;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::{gates::*, utils::*};

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the field F_p
//  Find ecc addition P - Q = (x_3, y_3)
//  Assumes that P !=Q and Q != (P - Q) 
#[allow(non_snake_case)]
pub fn assign_2<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(k, Q.x.limbs.len());
    assert_eq!(k, Q.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);
    assert_eq!(n, Q.x.limb_bits);
    assert_eq!(n, Q.y.limb_bits);

    let x_1 = P.x.to_bigint();
    let y_1 = P.y.to_bigint();
    let x_2 = Q.x.to_bigint();
    let y_2 = Q.y.to_bigint();

    let lambda = if let (Some(x_1), Some(y_1), Some(x_2), Some(y_2)) = (x_1, y_1, x_2, y_2) {
        let x_1 = bigint_to_fp(x_1);
        let y_1 = bigint_to_fp(y_1);
        let x_2 = bigint_to_fp(x_2);
        let y_2 = bigint_to_fp(y_2);

        assert_ne!(x_1, x_2);
        let lambda = (-y_2 - y_1) * (x_2 - x_1).invert().unwrap();
        Some(fp_to_bigint(&lambda))
    } else {
        None
    };

    let dx = sub_no_carry::assign(&range.qap_config, layouter, &Q.x, &P.x)?;
    let dy = add_no_carry::assign(&range.qap_config, layouter, &Q.y, &P.y)?;

    let lambda_limbs = decompose_bigint_option(&lambda, k, n);
    let lambda = layouter.assign_region(
        || "point double",
        |mut region| {
            let lambda_cells = lambda_limbs.iter().map(|x| Witness(*x)).collect();
            let lambda_bigint_limbs =
                range
                    .qap_config
                    .assign_region(lambda_cells, 0, &mut region)?;
            Ok(OverflowInteger::construct(
                lambda_bigint_limbs,
                BigUint::from(1u64) << n,
                n,
            ))
        },
    )?;
    for limb in &lambda.limbs {
        range.range_check(layouter, limb, n)?;
    }
    // (x_2 - x_1) * lambda + y_2 + y_1 (mod p)
    let lambda_dx = mul_no_carry::assign(&range.qap_config, layouter, &lambda, &dx)?;
    let lambda_dx_plus_dy = add_no_carry::assign(&range.qap_config, layouter, &lambda_dx, &dy)?;
    let lambda_dx_plus_dy_red = mod_reduce::assign(
	&range.qap_config,
	layouter,
	&lambda_dx_plus_dy,
	k,
	FP_MODULUS.clone(),
    )?;
    check_carry_mod_to_zero::assign(&range, layouter, &lambda_dx_plus_dy_red, &*FP_MODULUS)?;

    //  x_3 = lambda^2 - x_1 - x_2 (mod p)
    let lambda_sq = mul_no_carry::assign(&range.qap_config, layouter, &lambda, &lambda)?;
    let lambda_sq_minus_px = sub_no_carry::assign(&range.qap_config, layouter, &lambda_sq, &P.x)?;
    let x_3_no_carry =
        sub_no_carry::assign(&range.qap_config, layouter, &lambda_sq_minus_px, &Q.x)?;
    let x_3_red = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &x_3_no_carry,
        k,
        FP_MODULUS.clone(),
    )?;
    let x_3 = carry_mod::assign(range, layouter, &x_3_red, &*FP_MODULUS)?;

    //  y_3 = lambda (x_1 - x_3) - y_1 mod p
    let dx_13 = sub_no_carry::assign(&range.qap_config, layouter, &P.x, &x_3)?;
    let lambda_dx_13 = mul_no_carry::assign(&range.qap_config, layouter, &lambda, &dx_13)?;
    let y_3_no_carry = sub_no_carry::assign(&range.qap_config, layouter, &lambda_dx_13, &P.y)?;
    let y_3_red = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &y_3_no_carry,
        k,
        FP_MODULUS.clone(),
    )?;
    let y_3 = carry_mod::assign(range, layouter, &y_3_red, &*FP_MODULUS)?;

    Ok(EccPoint::construct(x_3, y_3))
}
