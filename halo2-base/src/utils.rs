use core::hash::Hash;

#[cfg(not(feature = "halo2-axiom"))]
use crate::halo2_proofs::arithmetic::CurveAffine;
use crate::halo2_proofs::circuit::Value;
#[cfg(feature = "halo2-axiom")]
pub use crate::halo2_proofs::halo2curves::CurveAffineExt;
use halo2_proofs::halo2curves::ff::{FromUniformBytes, PrimeField};

use num_bigint::BigInt;
use num_bigint::BigUint;
use num_bigint::Sign;
use num_traits::Signed;
use num_traits::{One, Zero};

#[cfg(feature = "halo2-axiom")]
pub trait BigPrimeField: ScalarField {
    fn from_u64_digits(val: &[u64]) -> Self;
}
#[cfg(feature = "halo2-axiom")]
impl<F> BigPrimeField for F
where
    F: FieldExt + Hash + Into<[u64; 4]> + From<[u64; 4]>,
{
    #[inline(always)]
    fn from_u64_digits(val: &[u64]) -> Self {
        debug_assert!(val.len() <= 4);
        let mut raw = [0u64; 4];
        raw[..val.len()].copy_from_slice(val);
        Self::from(raw)
    }
}

#[cfg(feature = "halo2-axiom")]
pub trait ScalarField: FieldExt + Hash {
    /// Returns the base `2^bit_len` little endian representation of the prime field element
    /// up to `num_limbs` number of limbs (truncates any extra limbs)
    ///
    /// Basically same as `to_repr` but does not go further into bytes
    ///
    /// Undefined behavior if `bit_len > 64`
    fn to_u64_limbs(self, num_limbs: usize, bit_len: usize) -> Vec<u64>;
}
#[cfg(feature = "halo2-axiom")]
impl<F> ScalarField for F
where
    F: FieldExt + Hash + Into<[u64; 4]>,
{
    #[inline(always)]
    fn to_u64_limbs(self, num_limbs: usize, bit_len: usize) -> Vec<u64> {
        let tmp: [u64; 4] = self.into();
        decompose_u64_digits_to_limbs(tmp, num_limbs, bit_len)
    }
}

/// Helper trait to represent a field element that can be converted into [u64] limbs.
///
/// Note: Since the number of bits necessary to represent a field element is larger than the number of bits in a u64, we decompose the integer representation of the field element into multiple [u64] values e.g. `limbs`.
pub trait ScalarField: PrimeField + FromUniformBytes<64> + From<bool> + Hash + Ord {
    /// Returns the base `2<sup>bit_len</sup>` little endian representation of the [ScalarField] element up to `num_limbs` number of limbs (truncates any extra limbs).
    ///
    /// Assumes `bit_len < 64`.
    /// * `num_limbs`: number of limbs to return
    /// * `bit_len`: number of bits in each limb
    fn to_u64_limbs(self, num_limbs: usize, bit_len: usize) -> Vec<u64>;

    /// Returns the little endian byte representation of the element.
    fn to_bytes_le(&self) -> Vec<u8>;

    /// Creates a field element from a little endian byte representation.
    ///
    /// The default implementation assumes that `PrimeField::from_repr` is implemented for little-endian.
    /// It should be overriden if this is not the case.
    fn from_bytes_le(bytes: &[u8]) -> Self {
        let mut repr = Self::Repr::default();
        repr.as_mut()[..bytes.len()].copy_from_slice(bytes);
        Self::from_repr(repr).unwrap()
    }

    /// Gets the least significant 32 bits of the field element.
    fn get_lower_32(&self) -> u32 {
        let bytes = self.to_bytes_le();
        let mut lower_32 = 0u32;
        for (i, byte) in bytes.into_iter().enumerate().take(4) {
            lower_32 |= (byte as u32) << (i * 8);
        }
        lower_32
    }

    /// Gets the least significant 64 bits of the field element.
    fn get_lower_64(&self) -> u64 {
        let bytes = self.to_bytes_le();
        let mut lower_64 = 0u64;
        for (i, byte) in bytes.into_iter().enumerate().take(8) {
            lower_64 |= (byte as u64) << (i * 8);
        }
        lower_64
    }

    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn one() -> Self {
        Self::ONE
    }
}

/// [ScalarField] that is ~256 bits long
#[cfg(feature = "halo2-pse")]
pub trait BigPrimeField = PrimeField<Repr = [u8; 32]> + ScalarField;

#[inline(always)]
pub(crate) fn decompose_u64_digits_to_limbs(
    e: impl IntoIterator<Item = u64>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<u64> {
    debug_assert!(bit_len < 64);

    let mut e = e.into_iter();
    let mask: u64 = (1u64 << bit_len) - 1u64;
    let mut u64_digit = e.next().unwrap_or(0);
    let mut rem = 64;
    (0..number_of_limbs)
        .map(|_| match rem.cmp(&bit_len) {
            core::cmp::Ordering::Greater => {
                let limb = u64_digit & mask;
                u64_digit >>= bit_len;
                rem -= bit_len;
                limb
            }
            core::cmp::Ordering::Equal => {
                let limb = u64_digit & mask;
                u64_digit = e.next().unwrap_or(0);
                rem = 64;
                limb
            }
            core::cmp::Ordering::Less => {
                let mut limb = u64_digit;
                u64_digit = e.next().unwrap_or(0);
                limb |= (u64_digit & ((1u64 << (bit_len - rem)) - 1u64)) << rem;
                u64_digit >>= bit_len - rem;
                rem += 64 - bit_len;
                limb
            }
        })
        .collect()
}

pub const fn bit_length(x: u64) -> usize {
    (u64::BITS - x.leading_zeros()) as usize
}

pub fn log2_ceil(x: u64) -> usize {
    (u64::BITS - x.leading_zeros()) as usize - usize::from(x.is_power_of_two())
}

pub fn modulus<F: BigPrimeField>() -> BigUint {
    fe_to_biguint(&-F::ONE) + 1u64
}

pub fn power_of_two<F: BigPrimeField>(n: usize) -> F {
    biguint_to_fe(&(BigUint::one() << n))
}

/// assume `e` less than modulus of F
pub fn biguint_to_fe<F: BigPrimeField>(e: &BigUint) -> F {
    #[cfg(feature = "halo2-axiom")]
    {
        F::from_u64_digits(&e.to_u64_digits())
    }

    #[cfg(feature = "halo2-pse")]
    {
        let bytes = e.to_bytes_le();
        F::from_bytes_le(&bytes)
    }
}

/// assume `|e|` less than modulus of F
pub fn bigint_to_fe<F: BigPrimeField>(e: &BigInt) -> F {
    #[cfg(feature = "halo2-axiom")]
    {
        let (sign, digits) = e.to_u64_digits();
        if sign == Sign::Minus {
            -F::from_u64_digits(&digits)
        } else {
            F::from_u64_digits(&digits)
        }
    }
    #[cfg(feature = "halo2-pse")]
    {
        let (sign, bytes) = e.to_bytes_le();
        let f_abs = F::from_bytes_le(&bytes);
        if sign == Sign::Minus {
            -f_abs
        } else {
            f_abs
        }
    }
}

pub fn fe_to_biguint<F: ScalarField>(fe: &F) -> BigUint {
    BigUint::from_bytes_le(fe.to_bytes_le().as_ref())
}

pub fn fe_to_bigint<F: BigPrimeField>(fe: &F) -> BigInt {
    // TODO: `F` should just have modulus as lazy_static or something
    let modulus = modulus::<F>();
    let e = fe_to_biguint(fe);
    if e <= &modulus / 2u32 {
        BigInt::from_biguint(Sign::Plus, e)
    } else {
        BigInt::from_biguint(Sign::Minus, modulus - e)
    }
}

pub fn decompose<F: BigPrimeField>(e: &F, number_of_limbs: usize, bit_len: usize) -> Vec<F> {
    if bit_len > 64 {
        decompose_biguint(&fe_to_biguint(e), number_of_limbs, bit_len)
    } else {
        decompose_fe_to_u64_limbs(e, number_of_limbs, bit_len).into_iter().map(F::from).collect()
    }
}

/// Assumes `bit_len` <= 64
pub fn decompose_fe_to_u64_limbs<F: ScalarField>(
    e: &F,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<u64> {
    #[cfg(feature = "halo2-axiom")]
    {
        e.to_u64_limbs(number_of_limbs, bit_len)
    }

    #[cfg(feature = "halo2-pse")]
    {
        decompose_u64_digits_to_limbs(fe_to_biguint(e).iter_u64_digits(), number_of_limbs, bit_len)
    }
}

pub fn decompose_biguint<F: BigPrimeField>(
    e: &BigUint,
    num_limbs: usize,
    bit_len: usize,
) -> Vec<F> {
    debug_assert!((64..128).contains(&bit_len));
    let mut e = e.iter_u64_digits();

    let mut limb0 = e.next().unwrap_or(0) as u128;
    let mut rem = bit_len - 64;
    let mut u64_digit = e.next().unwrap_or(0);
    limb0 |= ((u64_digit & ((1u64 << rem) - 1u64)) as u128) << 64u32;
    u64_digit >>= rem;
    rem = 64 - rem;

    core::iter::once(F::from_u128(limb0))
        .chain((1..num_limbs).map(|_| {
            let mut limb = u64_digit as u128;
            let mut bits = rem;
            u64_digit = e.next().unwrap_or(0);
            if bit_len >= 64 + bits {
                limb |= (u64_digit as u128) << bits;
                u64_digit = e.next().unwrap_or(0);
                bits += 64;
            }
            rem = bit_len - bits;
            limb |= ((u64_digit & ((1u64 << rem) - 1u64)) as u128) << bits;
            u64_digit >>= rem;
            rem = 64 - rem;
            F::from_u128(limb)
        }))
        .collect()
}

pub fn decompose_bigint<F: BigPrimeField>(e: &BigInt, num_limbs: usize, bit_len: usize) -> Vec<F> {
    if e.is_negative() {
        decompose_biguint::<F>(e.magnitude(), num_limbs, bit_len).into_iter().map(|x| -x).collect()
    } else {
        decompose_biguint(e.magnitude(), num_limbs, bit_len)
    }
}

pub fn decompose_bigint_option<F: BigPrimeField>(
    value: Value<&BigInt>,
    number_of_limbs: usize,
    bit_len: usize,
) -> Vec<Value<F>> {
    value.map(|e| decompose_bigint(e, number_of_limbs, bit_len)).transpose_vec(number_of_limbs)
}

pub fn value_to_option<V>(value: Value<V>) -> Option<V> {
    let mut v = None;
    value.map(|val| {
        v = Some(val);
    });
    v
}

/// Compute the represented value by a vector of values and a bit length.
///
/// This function is used to compute the value of an integer
/// passing as input its limb values and the bit length used.
/// Returns the sum of all limbs scaled by 2^(bit_len * i)
pub fn compose(input: Vec<BigUint>, bit_len: usize) -> BigUint {
    input.iter().rev().fold(BigUint::zero(), |acc, val| (acc << bit_len) + val)
}

#[cfg(test)]
#[test]
fn test_signed_roundtrip() {
    use crate::halo2_proofs::halo2curves::bn256::Fr;
    assert_eq!(fe_to_bigint(&bigint_to_fe::<Fr>(&-BigInt::one())), -BigInt::one());
}

#[cfg(feature = "halo2-axiom")]
pub use halo2_proofs_axiom::halo2curves::CurveAffineExt;

#[cfg(feature = "halo2-pse")]
pub trait CurveAffineExt: CurveAffine {
    /// Unlike the `Coordinates` trait, this just returns the raw affine coordinantes without checking `is_on_curve`
    fn into_coordinates(self) -> (Self::Base, Self::Base) {
        let coordinates = self.coordinates().unwrap();
        (*coordinates.x(), *coordinates.y())
    }
}
#[cfg(feature = "halo2-pse")]
impl<C: CurveAffine> CurveAffineExt for C {}

mod scalar_field_impls {
    use super::{decompose_u64_digits_to_limbs, ScalarField};
    #[cfg(feature = "halo2-pse")]
    use crate::halo2_proofs::halo2curves::{
        bn256::{Fq as bn254Fq, Fr as bn254Fr},
        ff::PrimeField,
        secp256k1::{Fp as secpFp, Fq as secpFq},
    };

    /// To ensure `ScalarField` is only implemented for `ff:Field` where `Repr` is little endian, we use the following macro
    /// to implement the trait for each field.
    #[cfg(feature = "halo2-axiom")]
    #[macro_export]
    macro_rules! impl_scalar_field {
        ($field:ident) => {
            impl ScalarField for $field {
                #[inline(always)]
                fn to_u64_limbs(self, num_limbs: usize, bit_len: usize) -> Vec<u64> {
                    // Basically same as `to_repr` but does not go further into bytes
                    let tmp: [u64; 4] = self.into();
                    decompose_u64_digits_to_limbs(tmp, num_limbs, bit_len)
                }

                #[inline(always)]
                fn to_bytes_le(&self) -> Vec<u8> {
                    let tmp: [u64; 4] = (*self).into();
                    tmp.iter().flat_map(|x| x.to_le_bytes()).collect()
                }

                #[inline(always)]
                fn get_lower_32(&self) -> u32 {
                    let tmp: [u64; 4] = (*self).into();
                    tmp[0] as u32
                }

                #[inline(always)]
                fn get_lower_64(&self) -> u64 {
                    let tmp: [u64; 4] = (*self).into();
                    tmp[0]
                }
            }
        };
    }

    /// To ensure `ScalarField` is only implemented for `ff:Field` where `Repr` is little endian, we use the following macro
    /// to implement the trait for each field.
    #[cfg(feature = "halo2-pse")]
    #[macro_export]
    macro_rules! impl_scalar_field {
        ($field:ident) => {
            impl ScalarField for $field {
                #[inline(always)]
                fn to_u64_limbs(self, num_limbs: usize, bit_len: usize) -> Vec<u64> {
                    let bytes = self.to_repr();
                    let digits = (0..4)
                        .map(|i| u64::from_le_bytes(bytes[i * 8..(i + 1) * 8].try_into().unwrap()));
                    decompose_u64_digits_to_limbs(digits, num_limbs, bit_len)
                }

                #[inline(always)]
                fn to_bytes_le(&self) -> Vec<u8> {
                    self.to_repr().to_vec()
                }
            }
        };
    }

    impl_scalar_field!(bn254Fr);
    impl_scalar_field!(bn254Fq);
    impl_scalar_field!(secpFp);
    impl_scalar_field!(secpFq);
}

pub mod fs {
    use std::{
        env::var,
        fs::{self, File},
        io::{BufReader, BufWriter},
    };

    use crate::halo2_proofs::{
        halo2curves::{
            bn256::{Bn256, G1Affine},
            CurveAffine,
        },
        poly::{
            commitment::{Params, ParamsProver},
            kzg::commitment::ParamsKZG,
        },
    };
    use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

    pub fn read_params(k: u32) -> ParamsKZG<Bn256> {
        let dir = var("PARAMS_DIR").unwrap_or_else(|_| "./params".to_string());
        ParamsKZG::<Bn256>::read(&mut BufReader::new(
            File::open(format!("{dir}/kzg_bn254_{k}.srs").as_str())
                .expect("Params file does not exist"),
        ))
        .unwrap()
    }

    pub fn read_or_create_srs<'a, C: CurveAffine, P: ParamsProver<'a, C>>(
        k: u32,
        setup: impl Fn(u32) -> P,
    ) -> P {
        let dir = var("PARAMS_DIR").unwrap_or_else(|_| "./params".to_string());
        let path = format!("{dir}/kzg_bn254_{k}.srs");
        match File::open(path.as_str()) {
            Ok(f) => {
                #[cfg(feature = "display")]
                println!("read params from {path}");
                let mut reader = BufReader::new(f);
                P::read(&mut reader).unwrap()
            }
            Err(_) => {
                #[cfg(feature = "display")]
                println!("creating params for {k}");
                fs::create_dir_all(dir).unwrap();
                let params = setup(k);
                params.write(&mut BufWriter::new(File::create(path).unwrap())).unwrap();
                params
            }
        }
    }

    pub fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
        read_or_create_srs::<G1Affine, _>(k, |k| {
            ParamsKZG::<Bn256>::setup(k, ChaCha20Rng::from_seed(Default::default()))
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::halo2_proofs::halo2curves::bn256::Fr;
    use num_bigint::RandomBits;
    use rand::{
        rngs::{OsRng, StdRng},
        Rng, SeedableRng,
    };
    use std::ops::Shl;

    use super::*;

    #[test]
    fn test_signed_roundtrip() {
        use crate::halo2_proofs::halo2curves::bn256::Fr;
        assert_eq!(fe_to_bigint(&bigint_to_fe::<Fr>(&-BigInt::one())), -BigInt::one());
    }

    #[test]
    fn test_decompose_biguint() {
        let mut rng = OsRng;
        const MAX_LIMBS: u64 = 5;
        for bit_len in 64..128usize {
            for num_limbs in 1..=MAX_LIMBS {
                for _ in 0..10_000usize {
                    let mut e: BigUint = rng.sample(RandomBits::new(num_limbs * bit_len as u64));
                    let limbs = decompose_biguint::<Fr>(&e, num_limbs as usize, bit_len);

                    let limbs2 = {
                        let mut limbs = vec![];
                        let mask = BigUint::one().shl(bit_len) - 1usize;
                        for _ in 0..num_limbs {
                            let limb = &e & &mask;
                            let mut bytes_le = limb.to_bytes_le();
                            bytes_le.resize(32, 0u8);
                            limbs.push(Fr::from_bytes(&bytes_le.try_into().unwrap()).unwrap());
                            e >>= bit_len;
                        }
                        limbs
                    };
                    assert_eq!(limbs, limbs2);
                }
            }
        }
    }

    #[test]
    fn test_decompose_u64_digits_to_limbs() {
        let mut rng = OsRng;
        const MAX_LIMBS: u64 = 5;
        for bit_len in 0..64usize {
            for num_limbs in 1..=MAX_LIMBS {
                for _ in 0..10_000usize {
                    let mut e: BigUint = rng.sample(RandomBits::new(num_limbs * bit_len as u64));
                    let limbs = decompose_u64_digits_to_limbs(
                        e.to_u64_digits(),
                        num_limbs as usize,
                        bit_len,
                    );
                    let limbs2 = {
                        let mut limbs = vec![];
                        let mask = BigUint::one().shl(bit_len) - 1usize;
                        for _ in 0..num_limbs {
                            let limb = &e & &mask;
                            limbs.push(u64::try_from(limb).unwrap());
                            e >>= bit_len;
                        }
                        limbs
                    };
                    assert_eq!(limbs, limbs2);
                }
            }
        }
    }

    #[test]
    fn test_log2_ceil_zero() {
        assert_eq!(log2_ceil(0), 0);
    }

    #[test]
    fn test_get_lower_32() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..10_000usize {
            let e: u32 = rng.gen_range(0..u32::MAX);
            assert_eq!(Fr::from(e as u64).get_lower_32(), e);
        }
        assert_eq!(Fr::from((1u64 << 32_i32) + 1).get_lower_32(), 1);
    }

    #[test]
    fn test_get_lower_64() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..10_000usize {
            let e: u64 = rng.gen_range(0..u64::MAX);
            assert_eq!(Fr::from(e).get_lower_64(), e);
        }
    }
}
