use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_traits::One;

use super::OverflowInteger;
use crate::gates::{
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
    RangeInstructions,
};
use crate::utils::biguint_to_fe;
use crate::utils::fe_to_bigint;
use crate::utils::{bigint_to_fe, modulus as native_modulus};

// checks there exist d_i = -c_i so that
// a0 = c0 * 2^n
// a_{i + 1} + c_i = c_{i + 1} * 2^n for i = 0.. k - 2
// a_{k - 1} + c_{k - 2} = 0
// and c_i \in [-2^{m - n + EPSILON}, 2^{m - n + EPSILON}], with EPSILON >= 1
// where m = a.max_limb_size.bits() and we choose EPSILON to round up to the next multiple of the range check table size
//
// translated to d_i, this becomes:
// a0 + d0 * 2^n = 0
// a_{i + 1} + d_{i + 1} * 2^n = d_i for i = 0.. k - 2
// a_{k - 1} = d_{k - 2}

// aztec optimization:
// note that a_{i+1} + c_i = c_{i+1} * 2^n can be expanded to
// a_{i+1} * 2^{n*w} + a_i * 2^{n*(w-1)} + ... + a_{i+1-w} = c_{i+1} * 2^{n*(w+1)}
// which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
// so we only need to range check `c_i` every `w + 1` steps
pub fn assign<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<(), Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;
    let max_limb_bits = a.max_limb_size.bits();

    let mut carries: Vec<Option<BigInt>> = Vec::with_capacity(k);
    let limb_val = BigInt::from(1) << limb_bits;
    let limb_base = bigint_to_fe(&limb_val);

    for idx in 0..k {
        let a_val = a.limbs[idx].value();
        let carry = match a_val {
            Some(a_fe) => {
                let a_val_big = fe_to_bigint(a_fe);
                if idx == 0 {
                    Some(a_val_big / &limb_val)
                } else {
                    let carry_val = carries[idx - 1].as_ref().unwrap();
                    Some((a_val_big + carry_val) / &limb_val)
                }
            }
            None => None,
        };
        carries.push(carry);
    }

    let neg_carry_assignments = layouter.assign_region(
        || "carry consistency",
        |mut region| {
	    let mut neg_carry_assignments = Vec::new();
            let mut cells = Vec::with_capacity(4 * k);
            let mut enable_gates = Vec::new();
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
            let (assigned_cells, column_index) =
                range.gate().assign_region_smart(cells, enable_gates, 0, &mut region)?;
            region
                .constrain_equal(a.limbs[k - 1].cell(), assigned_cells[4 * (k - 2) + 1].cell())?;

            for idx in 0..k {
                neg_carry_assignments.push(assigned_cells[4 * idx + 1].clone());
            }
            Ok(neg_carry_assignments)
        },
    )?;
    // which is valid as long as `range_bits + n * w < native_modulus::<F>().bits() - 1`
    // round `max_limb_bits - limb_bits` up to the next multiple of range.lookup_bits
    const EPSILON: usize = 1;

    let range_bits = (max_limb_bits as usize) - limb_bits + EPSILON;
    // which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
    let window = (native_modulus::<F>().bits() as usize - 2 - range_bits) / limb_bits;
    assert!(window > 0);

    let shift_val = biguint_to_fe::<F>(&(BigUint::one() << range_bits));
    let num_windows = (k + window - 1) / window;
    let mut shifted_carry_assignments = Vec::new();
    for i in 0..num_windows {
	let shifted_carry_cell = layouter.assign_region(
            || "shift carries",
            |mut region| {
		let idx = std::cmp::min(window * i + window - 1, k - 1);
		let carry_cell = &neg_carry_assignments[idx];
                let shift_carry_val = Some(shift_val).zip(carry_cell.value()).map(|(s, c)| s + c);
                let cells = vec![
                    Existing(&carry_cell),
                    Constant(F::from(1)),
                    Constant(shift_val),
                    Witness(shift_carry_val),
                ];
                let (assigned_cells, column_index) =
                    range.gate().assign_region_smart(cells, vec![0], 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            }
	)?;
	shifted_carry_assignments.push(shifted_carry_cell);
    }
    for shifted_carry in shifted_carry_assignments.iter() {
        range.range_check(layouter, shifted_carry, range_bits + 1)?;
    }
    Ok(())
}

// check that `a` carries to `0 mod 2^{a.limb_bits * a.limbs.len()}`
// does same thing as check_carry_to_zero::assign except skips the last check that a_{k - 1} = d_{k - 2}
pub fn truncate<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
) -> Result<(), Error> {
    let k = a.limbs.len();
    let limb_bits = a.limb_bits;
    let max_limb_bits = a.max_limb_size.bits();

    let mut carries: Vec<Option<BigInt>> = Vec::with_capacity(k);
    let limb_val = BigInt::from(1) << limb_bits;
    let limb_base = bigint_to_fe(&limb_val);

    for idx in 0..k {
        let a_val = a.limbs[idx].value();
        let carry = match a_val {
            Some(a_fe) => {
                let a_val_big = fe_to_bigint(a_fe);
                if idx == 0 {
                    Some(a_val_big / &limb_val)
                } else {
                    let carry_val = carries[idx - 1].as_ref().unwrap();
                    Some((a_val_big + carry_val) / &limb_val)
                }
            }
            None => None,
        };
        carries.push(carry);
    }

    let neg_carry_assignments = layouter.assign_region(
        || "carry consistency",
        |mut region| {
            let mut neg_carry_assignments = Vec::with_capacity(k);
            let mut cells = Vec::with_capacity(4 * k);
            let mut enable_gates = Vec::new();
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
            let (assigned_cells, column_index) =
                range.gate().assign_region_smart(cells, enable_gates, 0, &mut region)?;

            for idx in 0..k {
                neg_carry_assignments.push(assigned_cells[4 * idx + 1].clone());
            }
            Ok(neg_carry_assignments)
        },
    )?;

    // which is valid as long as `range_bits + n * w < native_modulus::<F>().bits() - 1`
    // round `max_limb_bits - limb_bits` up to the next multiple of range.lookup_bits
    const EPSILON: usize = 1;

    let range_bits = (max_limb_bits as usize) - limb_bits + EPSILON;
    // which is valid as long as `(m - n + EPSILON) + n * (w+1) < native_modulus::<F>().bits() - 1`
    let window = (native_modulus::<F>().bits() as usize - 2 - range_bits) / limb_bits;
    assert!(window > 0);

    let shift_val = biguint_to_fe::<F>(&(BigUint::one() << range_bits));
    let num_windows = (k + window - 1) / window;
    let mut shifted_carry_assignments = Vec::with_capacity(num_windows);
    for i in 0..num_windows {
        let idx = std::cmp::min(window * i + window - 1, k - 1);
        let carry_cell = &neg_carry_assignments[idx];
        let shift_cell = layouter.assign_region(
            || "shift carries",
            |mut region| {
                let shift_carry_val = Some(shift_val).zip(carry_cell.value()).map(|(s, c)| s + c);
                let cells = vec![
                    Existing(&carry_cell),
                    Constant(F::from(1)),
                    Constant(shift_val),
                    Witness(shift_carry_val),
                ];
                let (assigned_cells, column_index) =
                    range.gate().assign_region_smart(cells, vec![0], 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )?;
        shifted_carry_assignments.push(shift_cell);
    }

    for shifted_carry in shifted_carry_assignments.iter() {
        range.range_check(layouter, shifted_carry, range_bits + 1)?;
    }

    Ok(())
}
