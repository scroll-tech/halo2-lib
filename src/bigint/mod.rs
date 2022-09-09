use std::{collections::HashMap, io::ErrorKind, marker::PhantomData};

use crate::gates::{
    flex_gate::FlexGateConfig,
    GateInstructions,
    QuantumCell::{self, Constant, Existing},
};
use crate::utils::*;
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::*,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
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
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
        limbs: Vec<AssignedCell<F, F>>,
        max_limb_size: BigUint,
        limb_bits: usize,
        max_size: BigUint,
    ) -> Self {
        Self { limbs, max_limb_size, limb_bits, max_size }
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

    pub fn to_bigint(&self) -> BigUint {
        self.limbs
            .iter()
            .rev()
            .fold(BigUint::zero(), |acc, x| (acc << self.limb_bits) + fe_to_biguint(x))
    }

    pub fn assign(
        &self,
        gate: &mut impl GateInstructions<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let assigned_limbs = layouter.assign_region(
            || "assign limbs",
            |mut region| {
                let limb_cells = self.limbs.iter().map(|x| Constant(*x)).collect();
                let limb_cells_assigned =
                    gate.assign_region_smart(limb_cells, vec![], vec![], vec![], 0, &mut region)?;
                Ok(limb_cells_assigned)
            },
        )?;
        let assigned = OverflowInteger::construct(
            assigned_limbs,
            self.max_limb_size.clone(),
            self.limb_bits,
            self.to_bigint(),
        );
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
}

impl<F: FieldExt> CRTInteger<F> {
    pub fn construct(
        truncation: OverflowInteger<F>,
        native: AssignedCell<F, F>,
        value: Option<BigInt>,
    ) -> Self {
        Self { truncation, native, value }
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
                let native_cells_assigned =
                    gate.assign_region_smart(native_cells, vec![], vec![], vec![], 0, &mut region)?;
                Ok(native_cells_assigned[0].clone())
            },
        )?;
        let assigned =
            CRTInteger::construct(assigned_truncation, assigned_native, Some(self.value.clone()));
        Ok(assigned)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum BigIntStrategy {
    Simple,              // use existing gates
    CustomVerticalTrunc, // vertical custom gates for truncative polynomial operations
}

#[derive(Clone, Debug)]
pub struct BigIntConfig<F: FieldExt> {
    // everything is empty if strategy is `Simple`

    // selector for custom gate for `mul_no_carry`
    // `q_mul_no_carry[k][i]` stores the selector for a custom gate to multiply two degree `k - 1` polynomials using index `i` vertical gate
    // gate implementation depends on the strategy
    pub q_mul_no_carry: HashMap<usize, Vec<Selector>>,
    // selector for custom gate that multiplies bigint with `num_limbs` limbs with a constant bigint with `num_limbs` limbs
    // `q_mul_no_carry_constant[p][i]` stores the selector for gate to multiply by constant `p` using index `i` vertical gate
    pub q_mul_no_carry_constant: HashMap<BigUint, Vec<Selector>>,
    strategy: BigIntStrategy,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BigIntConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        strategy: BigIntStrategy,
        limb_bits: usize,
        num_limbs: usize,
        gate_config: &FlexGateConfig<F>,
        constants: Vec<BigUint>,
    ) -> Self {
        let mut q_mul_no_carry = HashMap::new();
        let mut q_mul_no_carry_constant = HashMap::new();
        match strategy {
            BigIntStrategy::CustomVerticalTrunc => {
                q_mul_no_carry.insert(
                    num_limbs,
                    gate_config
                        .gates
                        .iter()
                        .map(|gate| {
                            let q = meta.selector();
                            create_vertical_mul_no_carry_gate(
                                meta,
                                &strategy,
                                num_limbs,
                                gate.value.clone(),
                                q,
                            );
                            q
                        })
                        .collect(),
                );
                for constant in &constants {
                    q_mul_no_carry_constant.insert(
                        constant.clone(),
                        gate_config
                            .gates
                            .iter()
                            .map(|gate| {
                                let q = meta.selector();
                                create_vertical_mul_no_carry_constant_gate(
                                    meta,
                                    &strategy,
                                    limb_bits,
                                    num_limbs,
                                    constant,
                                    gate.value.clone(),
                                    q,
                                );
                                q
                            })
                            .collect(),
                    );
                }
            }
            _ => {}
        }
        Self { q_mul_no_carry, q_mul_no_carry_constant, strategy, _marker: PhantomData }
    }
}

fn create_vertical_mul_no_carry_gate<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    strategy: &BigIntStrategy,
    k: usize,
    value: Column<Advice>,
    selector: Selector,
) {
    if *strategy == BigIntStrategy::CustomVerticalTrunc {
        meta.create_gate("custom vertical mul_no_carry gate", |meta| {
            let q = meta.query_selector(selector);
            let a: Vec<Expression<F>> =
                (0..k).map(|i| meta.query_advice(value.clone(), Rotation(i as i32))).collect();
            let b: Vec<Expression<F>> = (0..k)
                .map(|i| meta.query_advice(value.clone(), Rotation((k + i) as i32)))
                .collect();
            let out: Vec<Expression<F>> =
                (0..k).map(|i| meta.query_advice(value, Rotation((k + k + i) as i32))).collect();
            let ab: Vec<Expression<F>> = (0..k)
                .map(|i| {
                    (0..=i).fold(Expression::Constant(F::from(0)), |sum, j| {
                        sum + a[j].clone() * b[i - j].clone()
                    })
                })
                .collect();
            out.iter()
                .zip(ab.iter())
                .map(|(out, ab)| q.clone() * (ab.clone() - out.clone()))
                .collect::<Vec<Expression<F>>>()
        })
    }
}

fn create_vertical_mul_no_carry_constant_gate<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    strategy: &BigIntStrategy,
    limb_bits: usize,
    num_limbs: usize,
    constant: &BigUint,
    value: Column<Advice>,
    selector: Selector,
) {
    if *strategy == BigIntStrategy::CustomVerticalTrunc {
        meta.create_gate("custom vertical mul_no_carry_with_p gate", |meta| {
            let q = meta.query_selector(selector);
            let a: Vec<Expression<F>> = (0..num_limbs)
                .map(|i| meta.query_advice(value.clone(), Rotation(i as i32)))
                .collect();
            let b: Vec<Expression<F>> = decompose_biguint(constant, num_limbs, limb_bits)
                .iter()
                .map(|x| Expression::Constant(*x))
                .collect();
            let out: Vec<Expression<F>> = (0..num_limbs)
                .map(|i| meta.query_advice(value, Rotation((num_limbs + i) as i32)))
                .collect();
            let ab: Vec<Expression<F>> = (0..num_limbs)
                .map(|i| {
                    (0..=i).fold(Expression::Constant(F::from(0)), |sum, j| {
                        sum + a[j].clone() * b[i - j].clone()
                    })
                })
                .collect();
            out.iter()
                .zip(ab.iter())
                .map(|(out, ab)| q.clone() * (ab.clone() - out.clone()))
                .collect::<Vec<Expression<F>>>()
        })
    }
}
