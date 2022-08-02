use halo2_proofs::arithmetic::Field;
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_bigint::Sign;
use num_traits::Signed;
use num_traits::{Num, One, Zero};
use std::cmp::Ordering;
use std::ops::Neg;
use std::ops::Shl;

use halo2_proofs::pairing::bn256::Fq as Fp;
use halo2_proofs::pairing::bn256::Fr;

// utils modified from halo2wrong

pub fn modulus<F: FieldExt>() -> BigUint {
    BigUint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

pub fn power_of_two<F: FieldExt>(n: usize) -> F {
    biguint_to_fe(&(BigUint::one() << n))
}

pub fn biguint_to_fe<F: FieldExt>(e: &BigUint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn bigint_to_fe<F: FieldExt>(e: &BigInt) -> F {
    let modulus = BigInt::from_biguint(Sign::Plus, modulus::<F>());
    let e: BigInt = if e < &BigInt::zero() {
        let mut a: BigInt = e % &modulus;
        while a < BigInt::zero() {
            a += &modulus;
        }
        a
    } else {
        e % &modulus
    };
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn fe_to_biguint<F: FieldExt>(fe: &F) -> BigUint {
    BigUint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn fe_to_bigint<F: FieldExt>(fe: &F) -> BigInt {
    let modulus = modulus::<F>();
    let e = fe_to_biguint(fe);
    if e <= &modulus / 2u32 {
        BigInt::from_biguint(Sign::Plus, e)
    } else {
        BigInt::from_biguint(Sign::Minus, modulus - e)
    }
}

pub fn decompose<F: FieldExt>(e: &F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    decompose_bigint(&fe_to_bigint(e), number_of_limbs, bit_len)
}

pub fn decompose_biguint<F: FieldExt>(
    e: &BigUint,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<F> {
    let mut e = e.clone();
    let mask = BigUint::from(1usize).shl(bit_len) - 1usize;
    let limbs: Vec<F> = (0..number_of_limbs)
        .map(|_| {
            let limb = &mask & &e;
            e = &e >> bit_len;
            biguint_to_fe(&limb)
        })
        .collect();
    // assert_eq!(e, BigUint::zero());
    limbs
}

pub fn decompose_bigint<F: FieldExt>(e: &BigInt, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    let sgn = e.sign();
    let mut e: BigUint = if e.is_negative() {
        e.neg().to_biguint().unwrap()
    } else {
        e.to_biguint().unwrap()
    };
    let mask = (BigUint::one() << bit_len) - 1usize;
    let limbs: Vec<F> = (0..number_of_limbs)
        .map(|_| {
            let limb = &mask & &e;
            let limb_fe: F = biguint_to_fe(&limb);
            e = &e >> bit_len;
            match sgn {
                Sign::Minus => -limb_fe,
                _ => limb_fe,
            }
        })
        .collect();
    // assert_eq!(e, BigUint::zero());
    limbs
}

pub fn decompose_option<F: FieldExt>(
    value: &Option<F>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<Option<F>> {
    decompose_bigint_option(&value.map(|fe| fe_to_bigint(&fe)), number_of_limbs, bit_len)
}

pub fn decompose_bigint_option<F: FieldExt>(
    value: &Option<BigInt>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<Option<F>> {
    match value {
        Some(e) => {
            let sgn = e.sign();
            let mut e: BigUint = if e.is_negative() {
                e.neg().to_biguint().unwrap()
            } else {
                e.to_biguint().unwrap()
            };
            let mask = (BigUint::one() << bit_len) - 1usize;
            let limbs: Vec<Option<F>> = (0..number_of_limbs)
                .map(|_| {
                    let limb = &mask & &e;
                    let limb_fe: F = biguint_to_fe(&limb);
                    e = &e >> bit_len;
                    Some(match sgn {
                        Sign::Minus => -limb_fe,
                        _ => limb_fe,
                    })
                })
                .collect();
            // assert_eq!(e, BigUint::zero());
            limbs
        }
        None => vec![None; number_of_limbs],
    }
}

pub fn decompose_biguint_option<F: FieldExt>(
    value: &Option<F>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<Option<F>> {
    match value.as_ref() {
        Some(v) => decompose_biguint(&fe_to_biguint(v), number_of_limbs, bit_len)
            .iter()
            .map(|&x| Some(x))
            .collect(),
        None => vec![None; number_of_limbs],
    }
}

/// Compute the represented value by a vector of values and a bit length.
///
/// This function is used to compute the value of an integer
/// passing as input its limb values and the bit length used.
/// Returns the sum of all limbs scaled by 2^(bit_len * i)
pub fn compose(input: Vec<BigUint>, bit_len: usize) -> BigUint {
    input
        .iter()
        .rev()
        .fold(BigUint::zero(), |acc, val| (acc << bit_len) + val)
}

#[cfg(test)]
#[test]
fn test_signed_roundtrip() {
    use halo2_proofs::pairing::bn256::Fr as F;
    assert_eq!(
        fe_to_bigint(&bigint_to_fe::<F>(&-BigInt::one())),
        -BigInt::one()
    );
}
