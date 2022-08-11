use super::OverflowInteger;
use crate::gates::{range, GateInstructions, RangeInstructions};
use crate::utils::*;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;
use num_traits::One;

use crate::gates::QuantumCell::{self, Constant, Existing, Witness};

// given an AssignedCell `a`, creates an OverflowInteger<F> containing a base
// `limb_base` decomposition of the value of `a`
pub fn assign<F: FieldExt>(
    range: &mut impl RangeInstructions<F>,
    layouter: &mut impl Layouter<F>,
    a: &AssignedCell<F, F>,
    limb_bits: usize,
    num_limbs: usize,
) -> Result<OverflowInteger<F>, Error> {
    assert!(limb_bits <= 64);
    assert!(limb_bits % range.lookup_bits() == 0);
    let k = num_limbs;

    let a_val = a.value().map(|fe| *fe);
    let out_limbs = decompose_option(&a_val, k, limb_bits);
    let limb_base: F = biguint_to_fe(&(big_uint::one() << limb_bits));

    let assigned_cells = layouter.assign_region(
        || "decompose",
        |mut region| {
            let mut cells: Vec<QuantumCell<F>> = Vec::with_capacity(3 * k - 2);
            cells.push(Witness(out_limbs[0]));

            let mut offset = 1;
            let mut running_sum = out_limbs[0];
            let mut running_pow = F::from(1);
            let mut enable_gates = Vec::new();
            for idx in 1..k {
                running_pow = running_pow * limb_base;
                running_sum = running_sum.zip(out_limbs[idx]).map(|(sum, x)| sum + x * running_pow);
                cells.push(Constant(running_pow));
                cells.push(Witness(out_limbs[idx]));
                cells.push(Witness(running_sum));

                enable_gates.push(offset - 1);
                offset = offset + 3;
            }
            let (assigned_cells, column_index) =
                range.gate().assign_region(cells, 0, &mut region)?;
            for row in enable_gates {
                range.gate().enable(&mut region, column_index, row)?;
            }
            region.constrain_equal(a.cell(), assigned_cells.last().unwrap().clone().cell())?;
            Ok(assigned_cells)
        },
    )?;

    let mut limbs = Vec::with_capacity(k);
    limbs.push(assigned_cells[0].clone());
    for idx in 1..k {
        limbs.push(assigned_cells[3 * idx - 1].clone());
    }

    for limb_cell in &limbs {
        range.range_check(layouter, &limb_cell, limb_bits)?;
    }

    Ok(OverflowInteger::construct(limbs, big_uint::one() << limb_bits, limb_bits))
}
