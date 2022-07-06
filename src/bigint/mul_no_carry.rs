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
        BigUint::from(std::cmp::min(k_a, k_b)) * a.max_limb_size.clone() * b.max_limb_size.clone(),
	a.limb_bits
    ))
}
