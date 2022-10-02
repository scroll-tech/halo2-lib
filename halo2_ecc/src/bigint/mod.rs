use halo2_base::{
    gates::{flex_gate::FlexGateConfig, GateInstructions},
    utils::{bigint_to_fe, biguint_to_fe, decompose_bigint, fe_to_bigint, fe_to_biguint},
    AssignedValue, Context,
    QuantumCell::{Constant, Existing},
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Value,
    plonk::{ConstraintSystem, Error},
};
use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use std::{marker::PhantomData, rc::Rc};

pub mod add_no_carry;
pub mod big_is_equal;
pub mod big_is_zero;
pub mod big_less_than;
pub mod carry_mod;
pub mod check_carry_mod_to_zero;
pub mod check_carry_to_zero;
pub mod inner_product;
pub mod mul_no_carry;
pub mod negative;
pub mod scalar_mul_and_add_no_carry;
pub mod scalar_mul_no_carry;
pub mod select;
pub mod sub;
pub mod sub_no_carry;

#[derive(Clone, Debug, PartialEq)]
pub enum BigIntStrategy {
    // use existing gates
    Simple,
    // vertical custom gates of length 4 for dot product between an unknown vector and a constant vector, both of length 3
    // we restrict to gate of length 4 since this uses the same set of evaluation points Rotation(0..=3) as our simple gate
    // CustomVerticalShort,
}

impl Default for BigIntStrategy {
    fn default() -> Self {
        BigIntStrategy::Simple
    }
}

#[derive(Clone, Debug)]
pub struct OverflowInteger<F: FieldExt> {
    pub limbs: Vec<AssignedValue<F>>,
    pub max_limb_size: BigUint, // max absolute value of integer value of a limb
    pub limb_bits: usize,
    pub max_size: BigUint, // theoretical max absolute value of `value` allowed. This needs to be < 2^t * n / 2
}

impl<F: FieldExt> OverflowInteger<F> {
    pub fn construct(
        limbs: Vec<AssignedValue<F>>,
        max_limb_size: BigUint,
        limb_bits: usize,
        max_size: BigUint,
    ) -> Self {
        Self { limbs, max_limb_size, limb_bits, max_size }
    }

    pub fn to_bigint(&self) -> Value<BigInt> {
        self.limbs.iter().rev().fold(Value::known(BigInt::zero()), |acc, acell| {
            acc.zip(acell.value()).map(|(acc, x)| (acc << self.limb_bits) + fe_to_bigint(x))
        })
    }

    pub fn evaluate(
        gate: &impl GateInstructions<F>,
        chip: &BigIntConfig<F>,
        ctx: &mut Context<'_, F>,
        limbs: &Vec<AssignedValue<F>>,
        limb_bits: usize,
    ) -> Result<AssignedValue<F>, Error> {
        let k = limbs.len();
        let n = limb_bits;
        let mut pows = Vec::with_capacity(k);
        let mut running_pow = F::from(1);
        let limb_base: F = biguint_to_fe(&(BigUint::from(1u32) << n));
        for _ in 0..k {
            pows.push(Constant(running_pow));
            running_pow = running_pow * &limb_base;
        }
        match chip.strategy {
            BigIntStrategy::Simple => {
                // Constrain `out_native = sum_i out_assigned[i] * 2^{n*i}` in `F`
                let (_, _, native) =
                    gate.inner_product(ctx, &limbs.iter().map(|a| Existing(a)).collect(), &pows)?;
                Ok(native)
            }
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
        gate: &impl GateInstructions<F>,
        ctx: &mut Context<'_, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let assigned_limbs = {
            let limb_cells = self.limbs.iter().map(|x| Constant(*x)).collect();
            gate.assign_region_smart(ctx, limb_cells, vec![], vec![], vec![])?
        };
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
    pub native: AssignedValue<F>,
    pub value: Value<BigInt>,
}

impl<F: FieldExt> CRTInteger<F> {
    pub fn construct(
        truncation: OverflowInteger<F>,
        native: AssignedValue<F>,
        value: Value<BigInt>,
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
        gate: &impl GateInstructions<F>,
        ctx: &mut Context<'_, F>,
    ) -> Result<CRTInteger<F>, Error> {
        let assigned_truncation = self.truncation.assign(gate, ctx)?;
        let assigned_native = {
            let native_cells = vec![Constant(self.native)];
            let native_cells_assigned =
                gate.assign_region_smart(ctx, native_cells, vec![], vec![], vec![])?;
            native_cells_assigned[0].clone()
        };
        let assigned = CRTInteger::construct(
            assigned_truncation,
            assigned_native,
            Value::known(self.value.clone()),
        );
        Ok(assigned)
    }
}

#[derive(Clone, Debug, Default)]
#[allow(dead_code)]
pub struct BigIntConfig<F: FieldExt> {
    // everything is empty if strategy is `Simple` or `SimplePlus`
    strategy: BigIntStrategy,
    context_id: Rc<String>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BigIntConfig<F> {
    pub fn configure(
        _meta: &mut ConstraintSystem<F>,
        strategy: BigIntStrategy,
        _limb_bits: usize,
        _num_limbs: usize,
        _gate: &FlexGateConfig<F>,
        context_id: String,
    ) -> Self {
        // let mut q_dot_constant = HashMap::new();
        match strategy {
            _ => {}
        }
        Self { strategy, _marker: PhantomData, context_id: Rc::new(context_id) }
    }
}
