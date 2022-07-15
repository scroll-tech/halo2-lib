use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::OverflowInteger;
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::utils::modulus as native_modulus;

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k_a = a.limbs.len();
    let k_b = b.limbs.len();
    assert!(k_a > 0);
    assert!(k_b > 0);
    let k_out = k_a + k_b - 1;
    assert!(
        BigUint::from(std::cmp::min(k_a, k_b)) * &a.max_limb_size * &b.max_limb_size
            <= native_modulus::<F>() / 2u32
    );
    let mut out_limbs = Vec::with_capacity(k_out);

    for i in 0..k_out {
        let out_cell = layouter.assign_region(
            || format!("mul_no_carry_{}", i),
            |mut region| {
                let startj = if i >= k_b { i - k_b + 1 } else { 0 };
                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, k_a) - startj);
                prod_computation.push(Constant(F::zero()));

                let mut offset = 0;
                let mut prod_val = Some(F::zero());
                for j in startj..=i {
                    if j >= k_a {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

                    let a_cell = &a.limbs[j];
                    let b_cell = &b.limbs[i - j];
                    prod_val = prod_val
                        .zip(a_cell.value())
                        .zip(b_cell.value())
                        .map(|((sum, &a), &b)| sum + a * b);

                    prod_computation.push(Existing(a_cell));
                    prod_computation.push(Existing(b_cell));
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }
                let prod_computation_assignments =
                    gate.assign_region(prod_computation, 0, &mut region)?;
                Ok(prod_computation_assignments.last().unwrap().clone())
            },
        )?;
        out_limbs.push(out_cell);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        BigUint::from(std::cmp::min(k_a, k_b)) * &a.max_limb_size * &b.max_limb_size,
        a.limb_bits,
    ))
}
