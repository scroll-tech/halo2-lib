use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::OverflowInteger;
use crate::gates::qap_gate;

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
    let mut out_limbs = Vec::with_capacity(k_out);

    for i in 0..k_out {
        let out_cell = layouter.assign_region(
            || format!("mul_no_carry_{}", i),
            |mut region| {
                let mut offset = 0;

                let mut out_val = Some(F::zero());
                let mut out_cell =
                    region.assign_advice_from_constant(|| "0", gate.value, 0, F::zero())?;
                region.constrain_constant(out_cell.cell(), F::zero())?;

                let startj = if i >= k_b { i - k_b + 1 } else { 0 };
                for j in startj..=i {
                    if j >= k_a {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

                    let a_cell = &a.limbs[j];
                    let b_cell = &b.limbs[i - j];
                    a_cell.copy_advice(
                        || format!("a_{}", j),
                        &mut region,
                        gate.value,
                        offset + 1,
                    )?;
                    b_cell.copy_advice(
                        || format!("b_{}", i - j),
                        &mut region,
                        gate.value,
                        offset + 2,
                    )?;

                    out_val = out_val
                        .zip(a_cell.value())
                        .zip(b_cell.value())
                        .map(|((sum, a), b)| sum + *a * *b);
                    out_cell = region.assign_advice(
                        || "partial sum out",
                        gate.value,
                        offset + 3,
                        || out_val.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                Ok(out_cell)
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

// does same thing as assign except that the inputs `a` and `b` are unassigned:
// we assign the inputs as we go
// output is (a_assigned, b_assigned, out_assigned)
pub fn with_unassigned_inputs<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &Vec<Option<F>>,
    b: &Vec<Option<F>>,
    limb_bits: usize,
    max_limb_size_a: BigUint,
    max_limb_size_b: BigUint,
) -> Result<(OverflowInteger<F>, OverflowInteger<F>, OverflowInteger<F>), Error> {
    let k_a = a.len();
    let k_b = b.len();
    assert!(k_a > 0);
    assert!(k_b > 0);
    let k_out = k_a + k_b - 1;

    let mut a_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_a);
    let mut b_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_b);
    let mut out_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_out);

    for i in 0..k_out {
        let out_cell = layouter.assign_region(
            || format!("mul_no_carry_{}", i),
            |mut region| {
                let mut offset = 0;

                let mut out_val = Some(F::zero());
                let mut out_cell =
                    region.assign_advice_from_constant(|| "0", gate.value, 0, F::zero())?;
                region.constrain_constant(out_cell.cell(), F::zero())?;

                let startj = if i >= k_b { i - k_b + 1 } else { 0 };
                for j in startj..=i {
                    if j >= k_a {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

                    if j < a_assigned.len() {
                        a_assigned[j].copy_advice(
                            || format!("a_{}", j),
                            &mut region,
                            gate.value,
                            offset + 1,
                        )?;
                    } else {
                        assert_eq!(a_assigned.len(), j);
                        // assign advice for a[j]
                        let cell = region.assign_advice(
                            || format!("a_{}", j),
                            gate.value,
                            offset + 1,
                            || a[j].ok_or(Error::Synthesis),
                        )?;
                        a_assigned.push(cell);
                    };
                    if i - j < b_assigned.len() {
                        b_assigned[i - j].copy_advice(
                            || format!("b_{}", i - j),
                            &mut region,
                            gate.value,
                            offset + 2,
                        )?;
                    } else {
                        assert_eq!(b_assigned.len(), i - j);
                        let cell = region.assign_advice(
                            || format!("b_{}", i - j),
                            gate.value,
                            offset + 2,
                            || b[i - j].ok_or(Error::Synthesis),
                        )?;
                        b_assigned.push(cell);
                    };

                    out_val = out_val
                        .zip(a[j])
                        .zip(b[i - j])
                        .map(|((sum, a), b)| sum + a * b);
                    out_cell = region.assign_advice(
                        || "partial sum out",
                        gate.value,
                        offset + 3,
                        || out_val.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                Ok(out_cell)
            },
        )?;
        out_assigned.push(out_cell);
    }
    assert_eq!(a_assigned.len(), k_a);
    assert_eq!(b_assigned.len(), k_b);
    assert_eq!(out_assigned.len(), k_out);

    let max_limb_size_out =
        BigUint::from(std::cmp::min(k_a, k_b)) * &max_limb_size_a * &max_limb_size_b;
    Ok((
        OverflowInteger::construct(a_assigned, max_limb_size_a, limb_bits),
        OverflowInteger::construct(b_assigned, max_limb_size_b, limb_bits),
        OverflowInteger::construct(out_assigned, max_limb_size_out, limb_bits),
    ))
}
