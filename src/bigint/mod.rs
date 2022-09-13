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
pub mod scalar_mul_and_add_no_carry;
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
        chip: &BigIntConfig<F>,
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
        match chip.strategy {
            BigIntStrategy::Simple => {
                // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
                let (_, _, native) = gate.inner_product(
                    layouter,
                    &limbs.iter().map(|a| Existing(a)).collect(),
                    &pows,
                )?;
                Ok(native)
            }
            BigIntStrategy::CustomVerticalShort => layouter.assign_region(
                || "",
                |mut region| {
                    let (cells, enable_sel) = mul_no_carry::witness_dot_constant(
                        gate,
                        chip,
                        &limbs.iter().map(|a| Existing(a)).collect(),
                        &pows.iter().map(|qc| qc.value().unwrap().clone()).collect(),
                    )?;
                    let (assignments, gate_index) =
                        gate.assign_region(cells, vec![], 0, &mut region)?;
                    for (c, row) in &enable_sel {
                        chip.q_dot_constant.get(c).expect("should have constant for custom gate")
                            [gate_index]
                            .enable(&mut region, *row)?;
                    }
                    Ok(assignments.last().unwrap().clone())
                },
            ),
        }
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

    /// Input: a BigInteger `value`, Output: the `FixedOverflowInteger` that represents the same value
    /// Can handle signs
    /// Note the representation of the integer will be in proper (no overflow) format, if signs are interpretted correctly
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

    /// Input: a BigInteger `value`, Output: the `FixedCRTInteger` that represents the same value
    /// Can handle signs
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
    // use existing gates
    Simple,
    // vertical custom gates of length 4 for dot product between an unknown vector and a constant vector, both of length 3
    // we restrict to gate of length 4 since this uses the same set of evaluation points Rotation(0..=3) as our simple gate
    CustomVerticalShort,
}

impl Default for BigIntStrategy {
    fn default() -> Self {
        BigIntStrategy::Simple
    }
}

pub const GATE_LEN: usize = 4;

#[derive(Clone, Debug, Default)]
pub struct BigIntConfig<F: FieldExt> {
    // everything is empty if strategy is `Simple`

    // selector for custom gate
    // | a0 | a1 | a2 | a3 |
    // that constraints a3 = <[a0, a1, a2], [c0, c1, c2]> (dot product) = a0 * c0 + a1 * c1 + a2 * c2
    // for a constant vector `c = [c0, c1, c2]`
    // `q_dot_constant[c][i]` stores the selector for gate to dot product with `c` using index `i` vertical gate
    // Using BigUint for max flexibility (FieldExt does not impl Hashable); TODO: can be optimized if speed is a concern
    pub q_dot_constant: HashMap<Vec<BigUint>, Vec<Selector>>,
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
        constants: Vec<Vec<BigUint>>, // collection of the constant vectors we want custom dot product gates for
    ) -> Self {
        let mut q_dot_constant = HashMap::new();
        match strategy {
            BigIntStrategy::CustomVerticalShort => {
                for constant in &constants {
                    assert!(constant.len() < GATE_LEN);
                    q_dot_constant.insert(
                        constant.clone(),
                        gate_config
                            .gates
                            .iter()
                            .map(|gate| {
                                let q = meta.selector();
                                create_vertical_dot_constant_gate(
                                    meta,
                                    constant.iter().map(|c| biguint_to_fe::<F>(c)).collect(),
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
        Self { q_dot_constant, strategy, _marker: PhantomData }
    }
}

/// Takes transpose of | a0 | a1 | .. | a_{k-1} | a_k |
/// and constrains a0 * c0 + ... + a_{k-1} * c_{k-1} = a_k
/// where c is constant vector of length k
fn create_vertical_dot_constant_gate<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    mut constant: Vec<F>,
    value: Column<Advice>,
    selector: Selector,
) {
    constant.extend((constant.len()..(GATE_LEN - 1)).map(|_| F::from(0)));
    assert_eq!(constant.len(), GATE_LEN - 1);
    meta.create_gate("custom vertical dot constant gate", |meta| {
        let q = meta.query_selector(selector);
        let a: Vec<Expression<F>> = (0..constant.len())
            .map(|i| meta.query_advice(value.clone(), Rotation(i as i32)))
            .collect();
        let out = meta.query_advice(value, Rotation(constant.len() as i32));
        let a_dot_c = (0..constant.len()).fold(Expression::Constant(F::from(0)), |sum, j| {
            sum + a[j].clone() * Expression::Constant(constant[j])
        });

        vec![q * (a_dot_c - out)]
    })
}
