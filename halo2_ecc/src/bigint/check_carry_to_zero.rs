use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::One;
use serde::de::value;

use super::OverflowInteger;
use crate::gates::{
    Context, GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::biguint_to_fe;
use crate::utils::fe_to_bigint;
use crate::utils::value_to_option;
use crate::utils::{bigint_to_fe, modulus as native_modulus};

// checks there exist d_i = -c_i so that
// a_0 = c_0 * 2^n
// a_i + c_{i - 1} = c_i * 2^n for i = 1..=k - 2
// a_{k - 1} + c_{k - 2} = 0
// and c_i \in [-2^{m - n + EPSILON}, 2^{m - n + EPSILON}], with EPSILON >= 1 for i = 0..<k - 2
// where m = a.max_limb_size.bits() and we choose EPSILON to round up to the next multiple of the range check table size
//
// translated to d_i, this becomes:
// a_0 + d_0 * 2^n = 0
// a_i + d_i * 2^n = d_{i - 1} for i = 1..=k - 2
// a_{k - 1} = d_{k - 2}

// aztec optimization:
// note that a_i + c_{i - 1} = c_i * 2^n can be expanded to
// a_i * 2^{n*w} + a_{i - 1} * 2^{n*(w-1)} + ... + a_{i - w} + c_{i - w - 1} = c_i * 2^{n*(w+1)}
// which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
// so we only need to range check `c_i` every `w + 1` steps, starting with `i = w`
pub fn assign<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
) -> Result<(), Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;
    let max_limb_bits = a.max_limb_size.bits();

    let mut carries: Vec<Value<BigInt>> = Vec::with_capacity(k);
    let limb_val = BigInt::from(1) << limb_bits;
    let limb_base = bigint_to_fe(&limb_val);

    for idx in 0..k - 1 {
        let a_val = a.limbs[idx].value();
        let carry = a_val.map(|a_fe| {
            let a_val_big = fe_to_bigint(a_fe);
            if idx == 0 {
                a_val_big / &limb_val
            } else {
                let carry_val = value_to_option(carries[idx - 1].clone()).unwrap();
                (a_val_big + carry_val) / &limb_val
            }
        });
        carries.push(carry);
    }

    let neg_carry_assignments = {
        let mut neg_carry_assignments = Vec::with_capacity(k - 1);
        let mut cells = Vec::with_capacity(4 * k);
        let mut enable_gates = Vec::with_capacity(k - 1);
        for idx in 0..k - 1 {
            enable_gates.push(4 * idx);

            cells.push(Existing(&a.limbs[idx]));
            cells.push(Witness(carries[idx].as_ref().map(|c| bigint_to_fe::<F>(&-c))));
            cells.push(Constant(limb_base));
            if idx == 0 {
                cells.push(Constant(F::from(0)));
            } else {
                cells.push(cells[4 * idx - 3].clone());
            }
        }
        let assigned_cells = range.gate().assign_region_smart(
            ctx,
            cells,
            enable_gates,
            vec![],
            vec![(&a.limbs[k - 1], 4 * (k - 2) + 1)],
        )?;

        for idx in 0..k - 1 {
            neg_carry_assignments.push(assigned_cells[4 * idx + 1].clone());
        }
        ctx.region.constrain_equal(a.limbs[k - 1].cell(), neg_carry_assignments[k - 2].cell())?;
        neg_carry_assignments
    };

    // round `max_limb_bits - limb_bits + EPSILON + 1` up to the next multiple of range.lookup_bits
    const EPSILON: usize = 1;
    let range_bits = (max_limb_bits as usize) - limb_bits + EPSILON;
    let range_bits =
        ((range_bits + range.lookup_bits()) / range.lookup_bits()) * range.lookup_bits() - 1;
    // `window = w + 1` valid as long as `range_bits + n * (w+1) < native_modulus::<F>().bits() - 1`
    let window = (native_modulus::<F>().bits() as usize - 2 - range_bits) / limb_bits;
    assert!(window > 0);

    let shift_val = biguint_to_fe::<F>(&(BigUint::one() << range_bits));
    let mut idx = window - 1;
    let mut shifted_carry_assignments = Vec::new();
    while idx < k - 2 {
        let shifted_carry_cell = {
            let carry_cell = &neg_carry_assignments[idx];
            let shift_carry_val = Value::known(shift_val) + carry_cell.value();
            let cells = vec![
                Existing(&carry_cell),
                Constant(F::from(1)),
                Constant(shift_val),
                Witness(shift_carry_val),
            ];
            let assigned_cells =
                range.gate().assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
            assigned_cells.last().unwrap().clone()
        };
        shifted_carry_assignments.push(shifted_carry_cell);
        idx += window;
    }
    for shifted_carry in shifted_carry_assignments.iter() {
        range.range_check(ctx, shifted_carry, range_bits + 1)?;
    }
    Ok(())
}

// check that `a` carries to `0 mod 2^{a.limb_bits * a.limbs.len()}`
// same as `assign` above except we need to provide `c_{k - 1}` witness as well
// checks there exist d_i = -c_i so that
// a_0 = c_0 * 2^n
// a_i + c_{i - 1} = c_i * 2^n for i = 1..=k - 1
// and c_i \in [-2^{m - n + EPSILON}, 2^{m - n + EPSILON}], with EPSILON >= 1 for i = 0..=k-1
// where m = a.max_limb_size.bits() and we choose EPSILON to round up to the next multiple of the range check table size
//
// translated to d_i, this becomes:
// a_0 + d_0 * 2^n = 0
// a_i + d_i * 2^n = d_{i - 1} for i = 1.. k - 1

// aztec optimization:
// note that a_i + c_{i - 1} = c_i * 2^n can be expanded to
// a_i * 2^{n*w} + a_{i - 1} * 2^{n*(w-1)} + ... + a_{i - w} + c_{i - w - 1} = c_i * 2^{n*(w+1)}
// which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
// so we only need to range check `c_i` every `w + 1` steps, starting with `i = w`
pub fn truncate<F: FieldExt>(
    range: &impl RangeInstructions<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
) -> Result<(), Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;
    let max_limb_bits = a.max_limb_size.bits();

    #[cfg(feature = "display")]
    {
        let key = format!("check_carry_to_zero(trunc) length {}", k);
        let count = ctx.op_count.entry(key).or_insert(0);
        *count += 1;
    }

    let mut carries: Vec<Value<BigInt>> = Vec::with_capacity(k);
    let limb_val = BigInt::from(1) << limb_bits;
    let limb_base = bigint_to_fe(&limb_val);

    for idx in 0..k {
        let a_val = a.limbs[idx].value();
        let carry = a_val.map(|a_fe| {
            let a_val_big = fe_to_bigint(a_fe);
            if idx == 0 {
                a_val_big / &limb_val
            } else {
                let carry_val = value_to_option(carries[idx - 1].clone()).unwrap();
                (a_val_big + carry_val) / &limb_val
            }
        });
        carries.push(carry);
    }

    let neg_carry_assignments = {
        let mut neg_carry_assignments = Vec::with_capacity(k);
        let mut cells = Vec::with_capacity(4 * k);
        let mut enable_gates = Vec::with_capacity(k);
        for idx in 0..k {
            enable_gates.push(4 * idx);

            cells.push(Existing(&a.limbs[idx]));
            cells.push(Witness(carries[idx].as_ref().map(|c| bigint_to_fe::<F>(&-c))));
            cells.push(Constant(limb_base));
            if idx == 0 {
                cells.push(Constant(F::from(0)));
            } else {
                cells.push(cells[4 * idx - 3].clone());
            }
        }
        let assigned_cells =
            range.gate().assign_region_smart(ctx, cells, enable_gates, vec![], vec![])?;

        for idx in 0..k {
            neg_carry_assignments.push(assigned_cells[4 * idx + 1].clone());
        }
        neg_carry_assignments
    };

    // round `max_limb_bits - limb_bits + EPSILON + 1` up to the next multiple of range.lookup_bits
    const EPSILON: usize = 1;
    let range_bits = (max_limb_bits as usize) - limb_bits + EPSILON;
    let range_bits =
        ((range_bits + range.lookup_bits()) / range.lookup_bits()) * range.lookup_bits() - 1;
    // `window = w + 1` valid as long as `range_bits + n * (w+1) < native_modulus::<F>().bits() - 1`
    let window = (native_modulus::<F>().bits() as usize - 2 - range_bits) / limb_bits;
    assert!(window > 0);

    let shift_val = biguint_to_fe::<F>(&(BigUint::one() << range_bits));
    let num_windows = (k - 1) / window + 1; // = ((k - 1) - (window - 1) + window - 1) / window + 1;
    let mut shifted_carry_assignments = Vec::with_capacity(num_windows);
    for i in 0..num_windows {
        let idx = std::cmp::min(window * i + window - 1, k - 1);
        let carry_cell = &neg_carry_assignments[idx];
        let shift_cell = {
            let shift_carry_val = Value::known(shift_val) + carry_cell.value();
            let cells = vec![
                Existing(&carry_cell),
                Constant(F::from(1)),
                Constant(shift_val),
                Witness(shift_carry_val),
            ];
            let assigned_cells =
                range.gate().assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
            assigned_cells.last().unwrap().clone()
        };
        shifted_carry_assignments.push(shift_cell);
    }

    for shifted_carry in shifted_carry_assignments.iter() {
        range.range_check(ctx, shifted_carry, range_bits + 1)?;
    }

    Ok(())
}
