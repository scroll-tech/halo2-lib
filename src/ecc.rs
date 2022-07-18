use std::str::FromStr;

use num_bigint::BigUint;
use num_bigint::BigInt;

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use halo2_proofs::pairing::bn256::Fq as Fp;

use crate::bigint::*;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::gates::*;
use crate::utils::*;

pub mod add_unequal;

use lazy_static::lazy_static;
lazy_static! {
    static ref FP_MODULUS: BigUint = BigUint::from_str(
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
    )
    .unwrap();
}

#[derive(Clone, Debug)]
pub struct EccPoint<F: FieldExt> {
    x: OverflowInteger<F>,
    y: OverflowInteger<F>,
}

impl<F: FieldExt> EccPoint<F> {
    pub fn construct(x: OverflowInteger<F>, y: OverflowInteger<F>) -> Self {
        Self { x, y }
    }
}

// Implements:
//   Check that x^3 + b - y^2 = 0 mod p
// Assume: b in [0, 2^n) 
// committing to prime field F_p with
// p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
//   = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
pub fn point_on_curve<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    b: F,
) -> Result<(), Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);

    let x_sq = mul_no_carry::assign(&range.qap_config, layouter, &P.x, &P.x)?;
    let x_cu = mul_no_carry::assign(&range.qap_config, layouter, &P.x, &x_sq)?;
    let y_sq = mul_no_carry::assign(&range.qap_config, layouter, &P.y, &P.y)?;
    let x_cu_minus_y_sq = sub_no_carry::assign(&range.qap_config, layouter, &x_cu, &y_sq)?;

    let mut carry_limbs = x_cu_minus_y_sq.limbs.clone();
    layouter.assign_region(
	|| "limb 0 add",
	|mut region| {
	    let cells = vec![
		Existing(&x_cu_minus_y_sq.limbs[0]),
		Constant(b),
		Constant(F::from(1)),
		Witness(x_cu_minus_y_sq.limbs[0].clone().value().map(|x| *x + F::from(1)))];	   
	    let assigned_cells = range.qap_config.assign_region(cells, 0, &mut region)?;
	    carry_limbs[0] = assigned_cells.last().unwrap().clone();
	    Ok(())
	}
    )?;

    let carry_int = OverflowInteger::construct(
	carry_limbs,
	x_cu_minus_y_sq.max_limb_size + fe_to_biguint(&b),
	n
    );

    let carry_int_mod = mod_reduce::assign(&range.qap_config, layouter, &carry_int, k, FP_MODULUS.clone())?;
    let check_zero = check_carry_mod_to_zero::assign(range, layouter, &carry_int_mod, &*FP_MODULUS)?;
    
    Ok(())
}

// Checks that the line between P and (Q.x, - Q.y) is the tangent line to the
// elliptic curve at P (for y^2 = x^3 + b)
// Checks:
// 2 * P.y (P.y + Q.y) = 3 * P.x^2 * (P.x - Q.x)
pub fn point_on_tangent<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
) -> Result<(), Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(k, Q.x.limbs.len());
    assert_eq!(k, Q.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);
    assert_eq!(n, Q.x.limb_bits);
    assert_eq!(n, Q.y.limb_bits);

    let three_px = scalar_mul_no_carry::assign(&range.qap_config, layouter, &P.x, F::from(3))?;
    let three_px_sq = mul_no_carry::assign(&range.qap_config, layouter, &P.x, &three_px)?;
    let px_minus_qx = sub_no_carry::assign(&range.qap_config, layouter, &P.x, &Q.x)?;
    let rhs = mul_no_carry::assign(&range.qap_config, layouter, &three_px_sq, &px_minus_qx)?;

    let two_py = scalar_mul_no_carry::assign(&range.qap_config, layouter, &P.y, F::from(2))?;
    let py_plus_qy = add_no_carry::assign(&range.qap_config, layouter, &P.y, &Q.y)?;
    let lhs = mul_no_carry::assign(&range.qap_config, layouter, &two_py, &py_plus_qy)?;

    let carry_int = sub_no_carry::assign(&range.qap_config, layouter, &lhs, &rhs)?;
    let carry_int_mod = mod_reduce::assign(&range.qap_config, layouter, &carry_int, k, FP_MODULUS.clone())?;
    let check_zero = check_carry_mod_to_zero::assign(range, layouter, &carry_int_mod, &*FP_MODULUS)?;
    
    Ok(())
}    

// Implements:
// computing 2P on elliptic curve E for P = (x, y)
// formula from https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
// assume y != 0 (otherwise 2P = O)

// lamb =  (3x^2 + a) / (2 y) % p
// x_3 = out[0] = lambda^2 - 2 x % p
// y_3 = out[1] = lambda (x - x_3) - y % p

// We precompute (x_3, y_3) and then constrain by showing that:
// * (x_3, y_3) is a valid point on the curve 
// * (x_3, y_3) is on the tangent line to E at (x, y) 
// * x != x_3
pub fn point_double<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    b: F,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);

    let x = P.x.to_bigint();
    let y = P.y.to_bigint();
    let (x_3, y_3) = if let (Some(x), Some(y)) = (x, y) {
	let x = bigint_to_fp(x);
	let y = bigint_to_fp(y);
	let lambda = bigint_to_fp(BigInt::from(3)) * x * x;
	let x_3 = lambda * lambda - bigint_to_fp(BigInt::from(2)) * x;
	let y_3 = lambda * (x - x_3) - y;
	(Some(fp_to_bigint(&x_3)), Some(fp_to_bigint(&y_3)))
    } else {
	(None, None)
    };

    let x_3_limbs = decompose_bigint_option::<F>(&x_3, k, n);
    let y_3_limbs = decompose_bigint_option::<F>(&y_3, k, n);
    
    let Q = layouter.assign_region(
	|| "point double",
	|mut region| {
	    let x_3_cells = x_3_limbs.iter().map(|x| Witness(*x)).collect();
	    let y_3_cells = y_3_limbs.iter().map(|x| Witness(*x)).collect();
            let x_3_bigint_limbs = range.qap_config.assign_region(x_3_cells, 0, &mut region)?;
	    let y_3_bigint_limbs = range.qap_config.assign_region(y_3_cells, 0, &mut region)?;
	    Ok(EccPoint::construct(OverflowInteger::construct(x_3_bigint_limbs, BigUint::from(1u64) << n, n),
				   OverflowInteger::construct(y_3_bigint_limbs, BigUint::from(1u64) << n, n)))	     
	}
    )?;

    for limb in &Q.x.limbs {
	range.range_check(layouter, &limb, n)?;
    }
    for limb in &Q.y.limbs {
	range.range_check(layouter, &limb, n)?;
    }
    point_on_curve(range, layouter, &Q, b)?;
    point_on_tangent(range, layouter, &P, &Q)?;

    let mod_limbs = decompose_biguint::<F>(&*FP_MODULUS, k, n);
    let fp_mod = layouter.assign_region(
	|| "const modulus",
	|mut region| {
	    let mod_cells = mod_limbs.iter().map(|x| Constant(*x)).collect();
	    let mod_bigint_limbs = range.qap_config.assign_region(mod_cells, 0, &mut region)?;
	    Ok(OverflowInteger::construct(mod_bigint_limbs, BigUint::from(1u64) << n, n))
	}
    )?;

    let px_less_than = big_less_than::assign(range, layouter, &P.x, &fp_mod)?;
    let qx_less_than = big_less_than::assign(range, layouter, &Q.x, &fp_mod)?;
    let px_equals_qx = big_is_equal::assign(range, layouter, &P.x, &Q.x)?;
    let check_answer = layouter.assign_region(
	|| "fp inequality check",
	|mut region| {
	    region.constrain_constant(px_less_than.cell(), F::from(1))?;
	    region.constrain_constant(qx_less_than.cell(), F::from(1))?;
	    region.constrain_constant(px_equals_qx.cell(), F::from(0))?;
	    Ok(())
	}
    )?;

    Ok(Q)
}
