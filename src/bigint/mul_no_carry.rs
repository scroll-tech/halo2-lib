use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::{BigIntConfig, CRTInteger, OverflowInteger};
use crate::gates::Context;
use crate::utils::{fe_to_biguint, modulus as native_modulus};
use crate::{
    bigint::BigIntStrategy,
    gates::{
        GateInstructions,
        QuantumCell::{self, Constant, Existing, Witness},
    },
};

pub fn assign<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    ctx: &mut Context<'_, F>,
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
        let out_cell = {
            let startj = if i >= k_b { i - k_b + 1 } else { 0 };
            let mut prod_computation: Vec<QuantumCell<F>> = Vec::new();
            prod_computation.push(Constant(F::zero()));
            let mut enable_gates = Vec::new();

            let mut offset = 0;
            let mut prod_val = Some(F::zero());
            for j in startj..=i {
                if j >= k_a {
                    break;
                }
                enable_gates.push(offset);

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
                gate.assign_region_smart(ctx, prod_computation, enable_gates, vec![], vec![])?;
            prod_computation_assignments.last().unwrap().clone()
        };
        out_limbs.push(out_cell);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        BigUint::from(std::cmp::min(k_a, k_b)) * &a.max_limb_size * &b.max_limb_size,
        a.limb_bits,
        &a.max_size * &b.max_size,
    ))
}

pub fn truncate<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    chip: &BigIntConfig<F>,
    ctx: &mut Context<'_, F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k = a.limbs.len();
    assert!(k > 0);
    assert_eq!(k, b.limbs.len());

    #[cfg(feature = "display")]
    {
        let key = format!("mul_no_carry(truncate) length {}", k);
        let count = ctx.op_count.entry(key).or_insert(0);
        *count += 1;
    }

    assert!(BigUint::from(k) * &a.max_limb_size * &b.max_limb_size <= native_modulus::<F>() / 2u32);
    let mut out_limbs = Vec::with_capacity(k);

    for i in 0..k {
        let out_cell = {
            let mut prod_computation: Vec<QuantumCell<F>> =
                Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, k));
            prod_computation.push(Constant(F::zero()));
            let mut enable_gates = Vec::new();

            let mut offset = 0;
            let mut prod_val = Some(F::zero());
            for j in 0..std::cmp::min(i + 1, k) {
                enable_gates.push(offset);

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
                gate.assign_region_smart(ctx, prod_computation, enable_gates, vec![], vec![])?;
            prod_computation_assignments.last().unwrap().clone()
        };
        out_limbs.push(out_cell);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        BigUint::from(k) * &a.max_limb_size * &b.max_limb_size,
        a.limb_bits,
        &a.max_size * &b.max_size,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &impl GateInstructions<F>,
    chip: &BigIntConfig<F>,
    ctx: &mut Context<'_, F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<CRTInteger<F>, Error> {
    let out_trunc = truncate(gate, chip, ctx, &a.truncation, &b.truncation)?;
    let out_native = gate.mul(ctx, &Existing(&a.native), &Existing(&b.native))?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a * b);

    Ok(CRTInteger::construct(out_trunc, out_native, out_val))
}
