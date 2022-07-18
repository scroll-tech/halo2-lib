use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::{One, Zero};

use super::*;
use crate::bigint::carry_mod::get_carry_witness;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::{gates::*, utils::*};

// Input `a` is `OverflowInteger` of length `k` with "signed" limbs
// Check that `a = 0 (mod modulus)`
// We constrain `a = modulus * quotient` and range check `quotient`
pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    modulus: &big_uint,
) -> Result<(), Error> {
    let n = a.limb_bits;
    let k = a.limbs.len();
    assert!(k > 0);

    // overflow := a.max_limb_size.bits()
    // quot <= ceil(2^overflow * 2^{n * k} / modulus) < 2^{overflow + n * k - modulus.bits() + 1}
    // therefore quot will need ceil( (overflow + n * k - modulus.bits() + 1 ) / n ) limbs
    let overflow = a.max_limb_size.bits() as usize;
    let m = (overflow + n * k - modulus.bits() as usize + n) / n;
    assert!(m > 0);

    let a_val = a.to_bigint();
    // these are witness vectors:
    let quotient_vec = if let Some(a_big) = a_val {
        let (out, quotient) = get_carry_witness(&a_big, modulus);
        assert_eq!(out, big_uint::zero());
        decompose_bigint_option::<F>(&Some(quotient), m, n)
    } else {
        vec![None; k]
    };

    // this is a constant vector:
    // to decrease mod_vec.len(), we can store `modulus` with some overflow:
    // say `mod_vec` has limbs with at most `mod_overflow` bits
    // we just need `log_2(min(mod_limb_len,m)) + mod_overflow + n < overflow`
    let mut mod_overflow = ((&a.max_limb_size >> n) / m).bits() as usize;
    mod_overflow = std::cmp::max(mod_overflow, n);

    let mask = (big_uint::from(1u64) << mod_overflow) - 1usize;
    let mut mod_vec = Vec::with_capacity(k);
    let mut temp_mod = modulus.clone();
    while temp_mod != big_uint::zero() {
        let limb = &temp_mod & &mask;
        temp_mod = (temp_mod - &limb) >> n;
        mod_vec.push(biguint_to_fe(&limb));
    }

    // Goal: assign cells to `- a + modulus * quotient`
    // 1. we do mul_no_carry(modulus, quotient) while assigning `modulus` and `quotient` as we go
    //    call the output `prod`
    // 2. for prod[i], i < k we can compute out - a + prod by using the transpose of
    //    | prod | -1 | a | prod - a |

    let k_prod = mod_vec.len() + m - 1;
    assert!(k_prod >= k);
    let mut mod_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(mod_vec.len());
    let mut quot_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(m);
    let mut check_assigned: Vec<AssignedCell<F, F>> = Vec::with_capacity(k_prod);

    let gate = &range.qap_config;
    for i in 0..k_prod {
        layouter.assign_region(
            || format!("carry_mod_{}", i),
            |mut region| {
                let mut offset = 0;

                let startj = if i >= m { i - m + 1 } else { 0 };
                let mut prod_computation: Vec<QuantumCell<F>> =
                    Vec::with_capacity(1 + 3 * std::cmp::min(i + 1, mod_vec.len()) - startj);
                let mut prod_val = Some(F::zero());
                prod_computation.push(Constant(F::zero()));

                for j in startj..=i {
                    if j >= mod_vec.len() {
                        break;
                    }
                    gate.q_enable.enable(&mut region, offset)?;

                    if j < mod_assigned.len() {
                        // does it matter whether we are enabling equality from advice column or fixed column for constants?
                        prod_computation.push(Existing(&mod_assigned[j]));
                    } else {
                        // Implies j == i && i < mod_vec.len()
                        prod_computation.push(Constant(mod_vec[j]));
                    }

                    if i - j < quot_assigned.len() {
                        prod_computation.push(Existing(&quot_assigned[i - j]));
                    } else {
                        // Implies j == 0 && i < m
                        prod_computation.push(Witness(quotient_vec[i - j]));
                    };

                    prod_val = prod_val
                        .zip(quotient_vec[i - j])
                        .map(|(sum, b)| sum + mod_vec[j] * b);
                    prod_computation.push(Witness(prod_val));

                    offset += 3;
                }
                // assign all the cells above
                let prod_computation_assignments =
                    gate.assign_region(prod_computation, 0, &mut region)?;

                // get new assigned cells and store them
                if i < mod_vec.len() {
                    // offset at j = i
                    mod_assigned.push(prod_computation_assignments[3 * (i - startj) + 1].clone());
                }
                if i < m {
                    // offset at j = 0
                    quot_assigned.push(prod_computation_assignments[2].clone());
                }

                if i < k {
                    // perform step 2: compute prod - a
                    // transpose of:
                    // | prod | -1 | a | prod - a
                    // where prod is at relative row `offset`
                    gate.q_enable.enable(&mut region, offset)?;

                    let check_val = prod_val.zip(a.limbs[i].value()).map(|(prod, &a)| prod - a);

                    let acells = gate.assign_region(
                        vec![
                            Constant(-F::from(1)),
                            Existing(&a.limbs[i]),
                            Witness(check_val),
                        ],
                        offset + 1,
                        &mut region,
                    )?;

                    check_assigned.push(acells[2].clone());
                } else {
                    check_assigned.push(prod_computation_assignments.last().unwrap().clone());
                }

                Ok(())
            },
        )?;
    }
    assert_eq!(mod_assigned.len(), mod_vec.len());
    assert_eq!(quot_assigned.len(), m);

    let limb_base: F = biguint_to_fe(&(big_uint::one() << n));
    // range check that quot_cell in quot_assigned is in [-2^n, 2^n)
    for quot_cell in quot_assigned.iter() {
        // compute quot_cell + 2^n and range check with n + 1 bits
        let quot_shift = layouter.assign_region(
            || format!("quot + 2^{}", n),
            |mut region| {
                gate.q_enable.enable(&mut region, 0)?;

                let out_val = quot_cell.value().map(|&a| a + limb_base);
                // | quot_cell | 2^n | 1 | quot_cell + 2^n |
                let shift_computation = gate.assign_region(
                    vec![
                        Existing(quot_cell),
                        Constant(limb_base),
                        Constant(F::one()),
                        Witness(out_val),
                    ],
                    0,
                    &mut region,
                )?;
                Ok(shift_computation[3].clone())
            },
        )?;

        range.range_check(layouter, &quot_shift, n + 1)?;
    }

    let check_overflow_int = &OverflowInteger::construct(
        check_assigned,
        &a.max_limb_size + (big_uint::from(std::cmp::min(mod_vec.len(), m)) << (mod_overflow + n)),
        n,
    );
    // check that `- a + modulus * quotient == 0` after carry
    check_carry_to_zero::assign(range, layouter, check_overflow_int)?;

    Ok(())
}
