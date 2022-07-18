use std::str::FromStr;

use halo2_proofs::arithmetic::Field;
use halo2_proofs::pairing::bn256::Fq as Fp;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigInt as big_int;
use num_bigint::BigUint as big_uint;
use num_bigint::Sign;
use num_traits::{One, Zero};

use super::*;
use crate::bigint::*;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::{gates::*, utils::*};

// committing to prime field F_p with
// p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
//   = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

// Implements:
//  Given P = (x_1, y_1) and Q = (x_2, y_2), ecc points over the field F_p
//      assume x_1 != x_2
//  Find ecc addition P + Q = (x_3, y_3)
// By solving:
//  x_1 + x_2 + x_3 - lambda^2 = 0 mod p
//  y_3 = lambda (x_1 - x_3) - y_1 mod p
//  where lambda = (y_2-y_1)/(x_2-x_1) is the slope of the line between (x_1, y_1) and (x_2, y_2)
// these equations are equivalent to:
//  (x_1 + x_2 + x_3)*(x_2 - x_1)^2 = (y_2 - y_1)^2 mod p
//  (y_1 + y_3)*(x_2 - x_1) = (y_2 - y_1)*(x_1 - x_3) mod p

pub fn assign<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(k, Q.x.limbs.len());
    assert_eq!(k, Q.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);
    assert_eq!(n, Q.x.limb_bits);
    assert_eq!(n, Q.y.limb_bits);

    let x_1 = P.x.to_bigint();
    let y_1 = P.y.to_bigint();
    let x_2 = Q.x.to_bigint();
    let y_2 = Q.y.to_bigint();

    let (x_3, y_3) = if let (Some(x_1), Some(y_1), Some(x_2), Some(y_2)) = (x_1, y_1, x_2, y_2) {
        let x_1 = bigint_to_fp(x_1);
        let y_1 = bigint_to_fp(y_1);
        let x_2 = bigint_to_fp(x_2);
        let y_2 = bigint_to_fp(y_2);

        assert_ne!(x_1, x_2);
        let lambda = (y_2 - y_1) * (x_2 - x_1).invert().unwrap();
        let x_3 = lambda * lambda - x_1 - x_2;
        let y_3 = lambda * (x_1 - x_3) - y_1;
        (
            Some(big_int::from_bytes_le(Sign::Plus, &x_3.to_bytes())),
            Some(big_int::from_bytes_le(Sign::Plus, &y_3.to_bytes())),
        )
    } else {
        (None, None)
    };

    let x_3_limbs = decompose_bigint_option::<F>(&x_3, k, n);
    let y_3_limbs = decompose_bigint_option::<F>(&y_3, k, n);

    let gate = &range.qap_config;

    let dx = sub_no_carry::assign(gate, layouter, &Q.x, &P.x)?;
    let dy = sub_no_carry::assign(gate, layouter, &Q.y, &P.y)?;

    // constrain x_3 by CUBIC (x_1 + x_2 + x_3) * (x_2 - x_1)^2 - (y_2 - y_1)^2 = 0 mod p
    let dx_sq = mul_no_carry::assign(gate, layouter, &dx, &dx)?;
    let dy_sq = mul_no_carry::assign(gate, layouter, &dy, &dy)?;

    // x_1 + x_2 + x_3 cells
    let mut sum_cells: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    let mut x_3_cells: Vec<AssignedCell<F, F>> = Vec::with_capacity(k);
    for i in 0..k {
        let (x_3_cell, sum_cell) = layouter.assign_region(
            || format!("(x_1 + x_2 + x_3)[{}]", i),
            |mut region| {
                let x_1_val = P.x.limbs[i].value();
                let x_2_val = Q.x.limbs[i].value();
                let x1_plus_x2_val = x_1_val.zip(x_2_val).map(|(&a, &b)| a + b);
                let sum_val = x1_plus_x2_val.zip(x_3_limbs[i]).map(|(a, b)| a + b);
                // | x_1[i] | 1 | x_2[i] | x_1[i] + x_2[i] | 1 | x_3[i] | x_1[i] + x_2[i] + x_3[i] |
                let add_assignments = gate.assign_region(
                    vec![
                        Existing(&P.x.limbs[i]),
                        Constant(F::from(1u64)),
                        Existing(&Q.x.limbs[i]),
                        Witness(x1_plus_x2_val),
                        Constant(F::from(1u64)),
                        Witness(x_3_limbs[i]),
                        Witness(sum_val),
                    ],
                    0,
                    &mut region,
                )?;
                Ok((add_assignments[5].clone(), add_assignments[6].clone()))
            },
        )?;
        sum_cells.push(sum_cell);
        x_3_cells.push(x_3_cell);
    }

    let sum = OverflowInteger::construct(sum_cells, 3u32 * &P.x.max_limb_size, n);
    // (x_1 + x_2 + x_3) * (x_2 - x_1)^2
    let cubic_lhs = mul_no_carry::assign(gate, layouter, &sum, &dx_sq)?;
    // (x_1 + x_2 + x_3) * (x_2 - x_1)^2 - (y_2 - y_1)^2
    let cubic_vanish = sub_no_carry::assign(gate, layouter, &cubic_lhs, &dy_sq)?;

    // check (x_1 + x_2 + x_3) * (x_2 - x_1)^2 - (y_2 - y_1)^2 == 0 (mod p)
    let cubic_red = mod_reduce::assign(gate, layouter, &cubic_vanish, k, FP_MODULUS.clone())?;
    check_carry_mod_to_zero::assign(range, layouter, &cubic_red, &*FP_MODULUS)?;

    let out_x = OverflowInteger::construct(x_3_cells, P.x.max_limb_size.clone(), n);
    // Implements constraint: (y_1 + y_3) * (x_2 - x_1) - (y_2 - y_1)*(x_1 - x_3) = 0 mod p
    // used to show (x1, y1), (x2, y2), (x3, -y3) are co-linear
    let mut point_on_line = || -> Result<Vec<AssignedCell<F, F>>, Error> {
        // y_1 + y_3
        let mut sum_y_cells = Vec::with_capacity(k);
        let mut y_3_cells = Vec::with_capacity(k);

        for i in 0..k {
            let (y_3_cell, sum_cell) = layouter.assign_region(
                || format!("(y_1 + y_3)[{}]", i),
                |mut region| {
                    let sum_val = P.y.limbs[i].value().zip(y_3_limbs[i]).map(|(&a, b)| a + b);
                    // | y_1[i] | 1 | y_3[i] | y_1[i] + y_3[i]
                    let add_assignments = gate.assign_region(
                        vec![
                            Existing(&P.y.limbs[i]),
                            Constant(F::from(1u64)),
                            Witness(y_3_limbs[i]),
                            Witness(sum_val),
                        ],
                        0,
                        &mut region,
                    )?;
                    Ok((add_assignments[2].clone(), add_assignments[3].clone()))
                },
            )?;
            sum_y_cells.push(sum_cell);
            y_3_cells.push(y_3_cell);
        }
        let sum_y = OverflowInteger::construct(sum_y_cells, 2u32 * &P.x.max_limb_size, n);
        let dx1_3 = sub_no_carry::assign(gate, layouter, &P.x, &out_x)?;

        // (y_1 + y_3) * (x_2 - x_1)
        let lhs = mul_no_carry::assign(gate, layouter, &sum_y, &dx)?;
        // (y_2 - y_1) * (x_1 - x_3)
        let rhs = mul_no_carry::assign(gate, layouter, &dy, &dx1_3)?;
        // (y_1 + y_3) * (x_2 - x_1) - (y_2 - y_1)*(x_1 - x_3) = 0 mod p
        let should_vanish = sub_no_carry::assign(gate, layouter, &lhs, &rhs)?;
        let should_vanish_red =
            mod_reduce::assign(gate, layouter, &should_vanish, k, FP_MODULUS.clone())?;
        check_carry_mod_to_zero::assign(range, layouter, &should_vanish_red, &*FP_MODULUS)?;

        Ok(y_3_cells)
    };

    let y_3_cells = point_on_line()?;
    let out_y = OverflowInteger::construct(y_3_cells, P.y.max_limb_size.clone(), n);

    Ok(EccPoint::construct(out_x, out_y))
}
