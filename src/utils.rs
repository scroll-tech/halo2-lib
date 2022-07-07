// utils from halo2wrong
use halo2_proofs::arithmetic::FieldExt;
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_traits::{Num, One, Zero};
use std::ops::Shl;

pub fn modulus<F: FieldExt>() -> big_uint {
    big_uint::from_str_radix(&F::MODULUS[2..], 16).unwrap()
}

pub fn power_of_two<F: FieldExt>(n: usize) -> F {
    big_to_fe(&(big_uint::one() << n))
}

pub fn big_to_fe<F: FieldExt>(e: &big_uint) -> F {
    let modulus = modulus::<F>();
    let e = e % modulus;
    F::from_str_vartime(&e.to_str_radix(10)[..]).unwrap()
}

pub fn fe_to_big<F: FieldExt>(fe: &F) -> big_uint {
    big_uint::from_bytes_le(fe.to_repr().as_ref())
}

pub fn decompose<F: FieldExt>(e: &F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    decompose_big(&fe_to_big(e), number_of_limbs, bit_len)
}

pub fn decompose_big<F: FieldExt>(e: &big_uint, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    let mut e = e.clone();
    let mask = big_uint::from(1usize).shl(bit_len) - 1usize;
    let limbs: Vec<F> = (0..number_of_limbs)
        .map(|_| {
            let limb = &mask & &e;
            e = &e >> bit_len;
            big_to_fe(&limb)
        })
        .collect();

    limbs
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
