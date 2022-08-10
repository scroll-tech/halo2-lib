use std::io::ErrorKind;

use crate::gates::{
    GateInstructions,
    QuantumCell::{self, Constant, Existing},
};
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

pub mod add_no_carry;
pub mod big_is_equal;
pub mod big_is_zero;
pub mod big_less_than;
pub mod carry_mod;
pub mod check_carry_mod_to_zero;
pub mod check_carry_to_zero;
pub mod decompose;
pub mod inner_product;
// pub mod mod_reduce;
pub mod mul_no_carry;
pub mod negative;
pub mod scalar_mul_no_carry;
pub mod select;
pub mod sub;
pub mod sub_no_carry;

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    pub limbs: Vec<AssignedCell<F, F>>,
    pub max_limb_size: BigUint, // max absolute value of integer value of a limb
    pub limb_bits: usize,
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
        limbs: Vec<AssignedCell<F, F>>,
        max_limb_size: BigUint,
        limb_bits: usize,
    ) -> Self {
        Self { limbs, max_limb_size, limb_bits }
    }

    pub fn to_bigint(&self) -> Option<BigInt> {
        self.limbs.iter().rev().fold(Some(BigInt::zero()), |acc, acell| {
            acc.zip(acell.value()).map(|(acc, x)| (acc << self.limb_bits) + fe_to_bigint(x))
        })
    }

    pub fn evaluate(
        gate: &mut impl GateInstructions<F>,
        layouter: &mut impl Layouter<F>,
        limbs: &Vec<AssignedCell<F, F>>,
        limb_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let k = limbs.len();
        let n = limb_bits;
        let mut pows = Vec::with_capacity(k);
        let mut running_pow = F::from(1);
        let limb_base: F = biguint_to_fe(&(BigUint::from(1u32) << n));
        for i in 0..k {
            pows.push(Constant(running_pow));
            running_pow = running_pow * &limb_base;
        }
        // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
        let (_, _, native) =
            gate.inner_product(layouter, &limbs.iter().map(|a| Existing(a)).collect(), &pows)?;
        Ok(native)
    }
}

#[derive(Clone, Debug)]
pub struct FixedOverflowInteger<F: FieldExt> {
    pub limbs: Vec<F>,
    pub max_limb_size: BigUint, // max absolute value of integer value of a limb
    pub limb_bits: usize,
}

impl<F: FieldExt> FixedOverflowInteger<F> {
    pub fn construct(limbs: Vec<F>, max_limb_size: BigUint, limb_bits: usize) -> Self {
        Self { limbs, max_limb_size, limb_bits }
    }

    pub fn from_native(value: BigInt, num_limbs: usize, limb_bits: usize) -> Self {
        let limbs = decompose_bigint(&value, num_limbs, limb_bits);
        Self { limbs, max_limb_size: BigUint::from(1u64) << limb_bits, limb_bits }
    }

    pub fn assign(
        &self,
        gate: &mut impl GateInstructions<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let (assigned_limbs, _) = layouter.assign_region(
            || "assign limbs",
            |mut region| {
                let limb_cells = self.limbs.iter().map(|x| Constant(*x)).collect();
                let limb_cells_assigned = gate.assign_region(limb_cells, 0, &mut region)?;
                Ok(limb_cells_assigned)
            },
        )?;
        let assigned =
            OverflowInteger::construct(assigned_limbs, self.max_limb_size.clone(), self.limb_bits);
        Ok(assigned)
    }
}

#[derive(Clone, Debug)]
pub struct CRTInteger<F: FieldExt> {
    // keep track of an integer `a` using CRT as `a mod 2^t` and `a mod n`
    // where `t = truncation.limbs.len() * truncation.limb_bits`
    //       `n = modulus::<Fn>`
    // `value` is the actual integer value we want to keep track of

    // we allow `value` to be a signed BigInt
    // however `value` is really an element of Z/(2^t * n), so signs are only meaningful if:
    // ASSUME `abs(value) < 2^t * n / 2`

    // the IMPLICIT ASSUMPTION: `value (mod 2^t) = truncation` && `value (mod n) = native`
    // this struct should only be used if the implicit assumption above is satisfied
    pub truncation: OverflowInteger<F>,
    pub native: AssignedCell<F, F>,
    pub value: Option<BigInt>,
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> CRTInteger<F> {
    pub fn construct(
        truncation: OverflowInteger<F>,
        native: AssignedCell<F, F>,
        value: Option<BigInt>,
        max_size: BigUint,
    ) -> Self {
        Self { truncation, native, value, max_size }
    }
}

#[derive(Clone, Debug)]
pub struct FixedCRTInteger<F: FieldExt> {
    // keep track of an integer `a` using CRT as `a mod 2^t` and `a mod n`
    // where `t = truncation.limbs.len() * truncation.limb_bits`
    //       `n = modulus::<Fn>`
    // `value` is the actual integer value we want to keep track of

    // we allow `value` to be a signed BigInt
    // however `value` is really an element of Z/(2^t * n), so signs are only meaningful if:
    // ASSUME `abs(value) < 2^t * n / 2`

    // the IMPLICIT ASSUMPTION: `value (mod 2^t) = truncation` && `value (mod n) = native`
    // this struct should only be used if the implicit assumption above is satisfied
    pub truncation: FixedOverflowInteger<F>,
    pub native: F,
    pub value: BigInt,
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> FixedCRTInteger<F> {
    pub fn construct(
        truncation: FixedOverflowInteger<F>,
        native: F,
        value: BigInt,
        max_size: BigUint,
    ) -> Self {
        Self { truncation, native, value, max_size }
    }

    pub fn from_native(value: BigInt, num_limbs: usize, limb_bits: usize) -> Self {
        let truncation = FixedOverflowInteger::from_native(value.clone(), num_limbs, limb_bits);
        Self {
            truncation,
            native: bigint_to_fe(&value),
            value: value,
            max_size: BigUint::from(1u64) << limb_bits,
        }
    }

    pub fn assign(
        &self,
        gate: &mut impl GateInstructions<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<CRTInteger<F>, Error> {
        let assigned_truncation = self.truncation.assign(gate, layouter)?;
        let assigned_native = layouter.assign_region(
            || "assign native",
            |mut region| {
                let native_cells = vec![Constant(self.native)];
                let (native_cells_assigned, _) =
                    gate.assign_region(native_cells, 0, &mut region)?;
                Ok(native_cells_assigned[0].clone())
            },
        )?;
        let assigned = CRTInteger::construct(
            assigned_truncation,
            assigned_native,
            Some(self.value.clone()),
            self.max_size.clone(),
        );
        Ok(assigned)
    }
}
