use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use super::{BigIntConfig, CRTInteger, OverflowInteger};
use crate::utils::modulus as native_modulus;
use crate::{
    bigint::BigIntStrategy,
    gates::{
        GateInstructions,
        QuantumCell::{self, Constant, Existing, Witness},
    },
};

pub fn assign<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
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
            || format!("mul_no_carry_assign i: {} k_out: {} k_a: {} k_b: {}", i, k_out, k_a, k_b),
            |mut region| {
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
                let prod_computation_assignments = gate.assign_region_smart(
                    prod_computation,
                    enable_gates,
                    vec![],
                    vec![],
                    0,
                    &mut region,
                )?;
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

pub fn truncate<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
    chip: &BigIntConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    b: &OverflowInteger<F>,
) -> Result<OverflowInteger<F>, Error> {
    assert_eq!(a.limb_bits, b.limb_bits);
    let k = a.limbs.len();
    assert!(k > 0);
    assert_eq!(k, b.limbs.len());

    assert!(BigUint::from(k) * &a.max_limb_size * &b.max_limb_size <= native_modulus::<F>() / 2u32);
    let mut out_limbs = Vec::with_capacity(k);

    match chip.strategy {
        BigIntStrategy::Simple => {
            for i in 0..k {
                let out_cell = layouter.assign_region(
                    || format!("mul_no_carry_{}/{}", i, k),
                    |mut region| {
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
                        let prod_computation_assignments = gate.assign_region_smart(
                            prod_computation,
                            enable_gates,
                            vec![],
                            vec![],
                            0,
                            &mut region,
                        )?;
                        Ok(prod_computation_assignments.last().unwrap().clone())
                    },
                )?;
                out_limbs.push(out_cell);
            }
        }
        BigIntStrategy::CustomVerticalTrunc => {
            let out_val: Vec<Option<F>> = (0..k)
                .map(|i| {
                    (0..=i).fold(Some(F::from(0)), |sum, j| {
                        sum.zip(a.limbs[j].value().zip(b.limbs[i - j].value()))
                            .map(|(sum, (&a, &b))| sum + a * b)
                    })
                })
                .collect();
            out_limbs = layouter.assign_region(
                || format!("mul_no_carry_{}", k),
                |mut region| {
                    let computation: Vec<QuantumCell<F>> = a
                        .limbs
                        .iter()
                        .map(|x| Existing(x))
                        .chain(b.limbs.iter().map(|x| Existing(x)))
                        .chain(out_val.iter().map(|x| Witness(*x)))
                        .collect();
                    let (mut assignments, gate_index) =
                        gate.assign_region(computation, vec![], 0, &mut region)?;
                    // enable custom gate
                    chip.q_mul_no_carry.get(&k).unwrap()[gate_index].enable(&mut region, 0)?;
                    Ok(assignments.drain((k + k)..).collect())
                },
            )?;
            assert_eq!(out_limbs.len(), k);
        }
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        BigUint::from(k) * &a.max_limb_size * &b.max_limb_size,
        a.limb_bits,
    ))
}

pub fn crt<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
    chip: &BigIntConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &CRTInteger<F>,
    b: &CRTInteger<F>,
) -> Result<CRTInteger<F>, Error> {
    let out_trunc = truncate(gate, chip, layouter, &a.truncation, &b.truncation)?;
    let out_native = gate.mul(layouter, &Existing(&a.native), &Existing(&b.native))?;
    let out_val = a.value.as_ref().zip(b.value.as_ref()).map(|(a, b)| a * b);

    Ok(CRTInteger::construct(out_trunc, out_native, out_val, &a.max_size * &b.max_size))
}

pub fn witness_by_constant<F: FieldExt>(
    gate: &mut impl GateInstructions<F>,
    chip: &BigIntConfig<F>,
    layouter: &mut impl Layouter<F>,
    quot_vec: &Vec<Option<F>>,
    mod_vec: &Vec<F>,
    modulus: &BigUint,
) -> Result<(Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>), Error> {
    assert_eq!(quot_vec.len(), mod_vec.len());
    let k = quot_vec.len();
    let prod_val: Vec<Option<F>> = (0..k)
        .map(|i| {
            (0..=i).fold(Some(F::from(0)), |sum, j| {
                sum.zip(quot_vec[j]).map(|(sum, a)| sum + a * mod_vec[i - j])
            })
        })
        .collect();

    layouter.assign_region(
        || format!("quot_times_mod_{}", k),
        |mut region| {
            let computation: Vec<QuantumCell<F>> = quot_vec
                .iter()
                .map(|x| Witness(*x))
                .chain(prod_val.iter().map(|x| Witness(*x)))
                .collect();
            let (mut assignments, gate_index) =
                gate.assign_region(computation, vec![], 0, &mut region)?;
            // enable custom gate
            chip.q_mul_no_carry_constant.get(&modulus).unwrap()[gate_index]
                .enable(&mut region, 0)?;
            let out = assignments.drain(k..).collect();
            Ok((assignments, out))
        },
    )
}
