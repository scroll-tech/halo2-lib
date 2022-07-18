use halo2_proofs::arithmetic::Field;
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::Signed;
use num_traits::{Num, One, Zero};
use std::cmp::Ordering;
use std::ops::Neg;
use std::ops::Shl;

use halo2_proofs::pairing::bn256::Fq as Fp;

// utils modified from halo2wrong

pub fn modulus<F: FieldExt>() -> big_uint {
    big_uint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

pub fn power_of_two<F: FieldExt>(n: usize) -> F {
    biguint_to_fe(&(big_uint::one() << n))
}

pub fn biguint_to_fe<F: FieldExt>(e: &big_uint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn bigint_to_fe<F: FieldExt>(e: &big_int) -> F {
    let modulus = big_int::from_biguint(Sign::Plus, modulus::<F>());
    let e: big_int = if e < &big_int::zero() {
        let mut a: big_int = e + &modulus;
        while a < big_int::zero() {
            a += &modulus;
        }
        a
    } else {
        e % &modulus
    };
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn fe_to_biguint<F: FieldExt>(fe: &F) -> big_uint {
    big_uint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn fe_to_bigint<F: FieldExt>(fe: &F) -> big_int {
    let modulus = modulus::<F>();
    let e = fe_to_biguint(fe);
    if e <= &modulus / 2u32 {
        big_int::from_biguint(Sign::Plus, e)
    } else {
        big_int::from_biguint(Sign::Minus, modulus - e)
    }
}

pub fn decompose<F: FieldExt>(e: &F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    decompose_bigint(&fe_to_bigint(e), number_of_limbs, bit_len)
}

pub fn decompose_biguint<F: FieldExt>(
    e: &big_uint,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<F> {
    let mut e = e.clone();
    let mask = big_uint::from(1usize).shl(bit_len) - 1usize;
    let limbs: Vec<F> = (0..number_of_limbs)
        .map(|_| {
            let limb = &mask & &e;
            e = &e >> bit_len;
            biguint_to_fe(&limb)
        })
        .collect();
    assert_eq!(e, big_uint::zero());
    limbs
}

pub fn decompose_bigint<F: FieldExt>(
    e: &big_int,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<F> {
    let sgn = e.sign();
    let mut e: big_uint = if e.is_negative() {
        e.neg().to_biguint().unwrap()
    } else {
        e.to_biguint().unwrap()
    };
    let mask = (big_uint::one() << bit_len) - 1usize;
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
    assert_eq!(e, big_uint::zero());
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
    value: &Option<big_int>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<Option<F>> {
    match value {
        Some(e) => {
            let sgn = e.sign();
            let mut e: big_uint = if e.is_negative() {
                e.neg().to_biguint().unwrap()
            } else {
                e.to_biguint().unwrap()
            };
            let mask = (big_uint::one() << bit_len) - 1usize;
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
            assert_eq!(e, big_uint::zero());
            limbs
        }
        None => vec![None; number_of_limbs],
    }
}

/// Compute the represented value by a vector of values and a bit length.
///
/// This function is used to compute the value of an integer
/// passing as input its limb values and the bit length used.
/// Returns the sum of all limbs scaled by 2^(bit_len * i)
pub fn compose(input: Vec<big_uint>, bit_len: usize) -> big_uint {
    input
        .iter()
        .rev()
        .fold(big_uint::zero(), |acc, val| (acc << bit_len) + val)
}

pub fn bigint_to_fp(x: big_int) -> Fp {
    let p: big_int = big_int::from_str_radix(
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
        10,
    )
    .unwrap();
    let mut x = x % &p;
    if x < big_int::zero() {
        x += &p;
    }
    let x_bytes: &[u8; 32] = &x.to_bytes_le().1[0..32].try_into().unwrap();
    Fp::from_bytes(x_bytes).unwrap()
}

#[cfg(test)]
#[test]
fn test_signed_roundtrip() {
    use halo2_proofs::pairing::bn256::Fr as F;
    assert_eq!(
        fe_to_bigint(&bigint_to_fe::<F>(&-big_int::one())),
        -big_int::one()
    );
}

#[cfg(test)]
#[test]
fn test_fp() {
    use super::*;
    let x = big_int::from_str_radix(
        "21888242871839275222246405745257275088696311157297823662689037894645226208582",
        10,
    )
    .unwrap();
    println!("{:?}", bigint_to_fp(x));
}
