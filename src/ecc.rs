use crate::bigint::OverflowInteger;
use crate::fields::fp::{FpChip, FpConfig};
use crate::utils::{
    bigint_to_fp, decompose_bigint_option, fp_to_bigint, modulus as native_modulus,
};
use halo2_proofs::arithmetic::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    pairing::bn256::Fq as Fp,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::bigint::*;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::gates::*;
use crate::utils::*;

pub mod add_unequal;

// committing to prime field F_p with
// p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
//   = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
use lazy_static::lazy_static;
lazy_static! {
    static ref FP_MODULUS: BigUint = native_modulus::<Fp>();
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
#[allow(non_snake_case)]
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
    // x^3 - y^2 + b
    layouter.assign_region(
        || "limb 0 add",
        |mut region| {
            let cells = vec![
                Existing(&x_cu_minus_y_sq.limbs[0]),
                Constant(b),
                Constant(F::from(1)),
                Witness(
                    x_cu_minus_y_sq.limbs[0]
                        .clone()
                        .value()
                        .map(|x| *x + F::from(b)),
                ),
            ];
            let assigned_cells = range.qap_config.assign_region(cells, 0, &mut region)?;
            carry_limbs[0] = assigned_cells.last().unwrap().clone();
            Ok(())
        },
    )?;

    let carry_int = OverflowInteger::construct(
        carry_limbs,
        x_cu_minus_y_sq.max_limb_size + fe_to_biguint(&b),
        n,
    );

    let carry_int_mod = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &carry_int,
        k,
        FP_MODULUS.clone(),
    )?;
    let check_zero =
        check_carry_mod_to_zero::assign(range, layouter, &carry_int_mod, &*FP_MODULUS)?;

    Ok(())
}

// Checks that the line between P and (Q.x, - Q.y) is the tangent line to the
// elliptic curve at P (for y^2 = x^3 + b)
// Checks:
// 2 * P.y (P.y + Q.y) = 3 * P.x^2 * (P.x - Q.x)
#[allow(non_snake_case)]
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

    let carry_int = sub_no_carry::assign(&range.qap_config, layouter, &rhs, &lhs)?;
    let carry_int_mod = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &carry_int,
        k,
        FP_MODULUS.clone(),
    )?;
    let check_zero =
        check_carry_mod_to_zero::assign(range, layouter, &carry_int_mod, &*FP_MODULUS)?;

    Ok(())
}

// Implements:
// computing 2P on elliptic curve E for P = (x, y)
// formula from https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
// assume y != 0 (otherwise 2P = O)

// lamb =  3x^2 / (2 y) % p
// x_3 = out[0] = lambda^2 - 2 x % p
// y_3 = out[1] = lambda (x - x_3) - y % p

// We precompute (x_3, y_3) and then constrain by showing that:
// * (x_3, y_3) is a valid point on the curve
// * (x_3, y_3) is on the tangent line to E at (x, y)
// * x != x_3
#[allow(non_snake_case)]
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
        assert_ne!(y, BigInt::zero());
        let x = bigint_to_fp(x);
        let y = bigint_to_fp(y);
        let lambda = Fp::from(3) * x * x * (Fp::from(2) * y).invert().unwrap();
        let x_3 = lambda * lambda - Fp::from(2) * x;
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
            let y_3_bigint_limbs = range.qap_config.assign_region(y_3_cells, k, &mut region)?;
            Ok(EccPoint::construct(
                OverflowInteger::construct(x_3_bigint_limbs, BigUint::from(1u64) << n, n),
                OverflowInteger::construct(y_3_bigint_limbs, BigUint::from(1u64) << n, n),
            ))
        },
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
            Ok(OverflowInteger::construct(
                mod_bigint_limbs,
                BigUint::from(1u64) << n,
                n,
            ))
        },
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
        },
    )?;

    Ok(Q)
}

// Implements:
// computing 2P on elliptic curve E for P = (x, y)
// formula from https://crypto.stanford.edu/pbc/notes/elliptic/explicit.html
// assume y != 0 (otherwise 2P = O)

// lamb =  3x^2 / (2 y) % p
// x_3 = out[0] = lambda^2 - 2 x % p
// y_3 = out[1] = lambda (x - x_3) - y % p

// we precompute lambda and constrain (2y) * lambda = 3 x^2 (mod p)
// then we compute x_3 = lambda^2 - 2 x (mod p)
//                 y_3 = lambda (x - x_3) - y (mod p)
#[allow(non_snake_case)]
pub fn point_double_2<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
) -> Result<EccPoint<F>, Error> {
    let k = P.x.limbs.len();
    let n = P.x.limb_bits;
    assert!(k > 0);
    assert_eq!(k, P.y.limbs.len());
    assert_eq!(n, P.y.limb_bits);

    let x = P.x.to_bigint();
    let y = P.y.to_bigint();
    let lambda = if let (Some(x), Some(y)) = (x, y) {
        assert_ne!(y, BigInt::zero());
        let x = bigint_to_fp(x);
        let y = bigint_to_fp(y);
        let lambda = Fp::from(3) * x * x * (Fp::from(2) * y).invert().unwrap();
        Some(fp_to_bigint(&lambda))
    } else {
        None
    };

    let lambda_limbs = decompose_bigint_option::<F>(&lambda, k, n);
    // assign lambda and compute 2 * lambda simultaneously
    let (lambda, two_lambda) = layouter.assign_region(
        || "2 * lambda",
        |mut region| {
            let mut offset = 0;
            let mut lambda_cells = Vec::with_capacity(k);
            let mut two_lambda = Vec::with_capacity(k);
            for limb in lambda_limbs.iter() {
                let cells = range.qap_config.assign_region(
                    vec![
                        Constant(F::from(0)),
                        Constant(F::from(2)),
                        Witness(limb.clone()),
                        Witness(limb.map(|a| F::from(2) * a)),
                    ],
                    offset,
                    &mut region,
                )?;
                lambda_cells.push(cells[2].clone());
                two_lambda.push(cells[3].clone());
                offset = offset + 4;
            }
            Ok((
                OverflowInteger::construct(lambda_cells, BigUint::from(1u64) << n, n),
                OverflowInteger::construct(two_lambda, BigUint::from(1u64) << (n + 1), n),
            ))
        },
    )?;
    for limb in &lambda.limbs {
        range.range_check(layouter, limb, n)?;
    }

    let two_y_lambda = mul_no_carry::assign(&range.qap_config, layouter, &two_lambda, &P.y)?;
    let three_x = scalar_mul_no_carry::assign(&range.qap_config, layouter, &P.x, F::from(3))?;
    let three_x_sq = mul_no_carry::assign(&range.qap_config, layouter, &three_x, &P.x)?;

    // 2 y * lambda - 3 x^2
    let lambda_constraint =
        sub_no_carry::assign(&range.qap_config, layouter, &two_y_lambda, &three_x_sq)?;
    let lambda_constraint_red = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &lambda_constraint,
        k,
        FP_MODULUS.clone(),
    )?;
    check_carry_mod_to_zero::assign(range, layouter, &lambda_constraint_red, &*FP_MODULUS)?;
    check_carry_mod_to_zero::assign(range, layouter, &lambda_constraint, &*FP_MODULUS)?;

    // x_3 = lambda^2 - 2 x % p
    let lambda_sq = mul_no_carry::assign(&range.qap_config, layouter, &lambda, &lambda)?;
    let two_x = scalar_mul_no_carry::assign(&range.qap_config, layouter, &P.x, F::from(2))?;
    let x_3_no_carry = sub_no_carry::assign(&range.qap_config, layouter, &lambda_sq, &two_x)?;
    let x_3_red = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &x_3_no_carry,
        k,
        FP_MODULUS.clone(),
    )?;
    let x_3 = carry_mod::assign(range, layouter, &x_3_red, &*FP_MODULUS)?;
    //let x_3 = carry_mod::assign(range, layouter, &x_3_no_carry, &*FP_MODULUS)?;

    // y_3 = lambda (x - x_3) - y % p
    let dx = sub_no_carry::assign(&range.qap_config, layouter, &P.x, &x_3)?;
    let lambda_dx = mul_no_carry::assign(&range.qap_config, layouter, &lambda, &dx)?;
    let y_3_no_carry = sub_no_carry::assign(&range.qap_config, layouter, &lambda_dx, &P.y)?;
    let y_3_red = mod_reduce::assign(
        &range.qap_config,
        layouter,
        &y_3_no_carry,
        k,
        FP_MODULUS.clone(),
    )?;
    let y_3 = carry_mod::assign(range, layouter, &y_3_red, &*FP_MODULUS)?;
    //let y_3 = carry_mod::assign(range, layouter, &y_3_no_carry, &*FP_MODULUS)?;

    Ok(EccPoint::construct(x_3, y_3))
}

#[allow(non_snake_case)]
pub fn select<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    Q: &EccPoint<F>,
    sel: &AssignedCell<F, F>,
) -> Result<EccPoint<F>, Error> {
    let Rx = select::assign(&range.qap_config, layouter, &P.x, &Q.x, sel)?;
    let Ry = select::assign(&range.qap_config, layouter, &P.y, &Q.y, sel)?;
    Ok(EccPoint::<F>::construct(Rx, Ry))
}

// computes x * P on y^2 = x^3 + b
// assumes:
//   * 0 < x < scalar field modulus
//   * P has order given by the scalar field modulus
#[allow(non_snake_case)]
pub fn scalar_multiply<F: FieldExt>(
    range: &range::RangeConfig<F>,
    layouter: &mut impl Layouter<F>,
    P: &EccPoint<F>,
    x: &AssignedCell<F, F>,
    b: F,
    max_bits: usize,
) -> Result<EccPoint<F>, Error> {
    let bits = range.num_to_bits(layouter, x, max_bits)?;

    // is_started[idx] holds whether there is a 1 in bits with index at least (max_bits - idx)
    let mut is_started = Vec::with_capacity(max_bits);
    is_started.push(bits[max_bits - 1].clone());
    for idx in 1..max_bits {
        let or = range
            .qap_config
            .or(layouter, &is_started[idx - 1], &bits[max_bits - 1 - idx])?;
        is_started.push(or.clone());
    }

    let mut curr_point = P.clone();
    for idx in 1..max_bits {
        let double = point_double_2(range, layouter, &curr_point /*, b*/)?;
        let double_and_add = add_unequal::assign_2(range, layouter, &double, &P)?;

        let is_started_point = select(
            range,
            layouter,
            &double_and_add,
            &double,
            &bits[max_bits - 1 - idx],
        )?;
        curr_point = select(range, layouter, &is_started_point, &P, &is_started[idx - 1])?;
    }
    Ok(curr_point.clone())
}

pub struct EccChip<F: FieldExt> {
    fp_chip: FpChip<F>,
}

#[allow(non_snake_case)]
impl<F: FieldExt> EccChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self {
            fp_chip: FpChip::construct(config),
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
    ) -> FpConfig<F> {
        FpChip::configure(
            meta,
            value,
            constant,
            lookup_bits,
            limb_bits,
            num_limbs,
            FP_MODULUS.clone(),
        )
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.fp_chip.load_lookup_table(layouter)
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        point: Option<(Fp, Fp)>,
    ) -> Result<EccPoint<F>, Error> {
        let (x, y) = if let Some((x, y)) = point {
            (Some(fp_to_bigint(&x)), Some(fp_to_bigint(&y)))
        } else {
            (None, None)
        };
        let x_vec = decompose_bigint_option::<F>(
            &x,
            self.fp_chip.config.num_limbs,
            self.fp_chip.config.limb_bits,
        );
        let y_vec = decompose_bigint_option::<F>(
            &y,
            self.fp_chip.config.num_limbs,
            self.fp_chip.config.limb_bits,
        );

        let x_assigned = self.fp_chip.load_private(
            layouter.namespace(|| "x"),
            x_vec,
            BigUint::one() << self.fp_chip.config.limb_bits,
        )?;
        let y_assigned = self.fp_chip.load_private(
            layouter.namespace(|| "y"),
            y_vec,
            BigUint::one() << self.fp_chip.config.limb_bits,
        )?;

        Ok(EccPoint::construct(x_assigned, y_assigned))
    }

    pub fn add_unequal(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
        Q: &EccPoint<F>,
    ) -> Result<EccPoint<F>, Error> {
        add_unequal::assign_2(&self.fp_chip.config.range, layouter, P, Q)
    }

    pub fn double(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
        b: F,
    ) -> Result<EccPoint<F>, Error> {
        // point_double(&self.fp_chip.config.range, layouter, P, b)
        point_double_2(&self.fp_chip.config.range, layouter, P)
    }

    pub fn scalar_mult(
        &self,
        layouter: &mut impl Layouter<F>,
        P: &EccPoint<F>,
        x: &AssignedCell<F, F>,
        b: F,
        max_bits: usize,
    ) -> Result<EccPoint<F>, Error> {
        scalar_multiply(&&self.fp_chip.config.range, layouter, P, x, b, max_bits)
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
pub(crate) mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::circuit::floor_planner::V1;
    use halo2_proofs::pairing::group::Group;
    use halo2_proofs::{
        arithmetic::FieldExt, circuit::*, dev::MockProver, pairing::bn256::Fq as Fp,
        pairing::bn256::Fr as Fn, plonk::*,
    };
    use num_bigint::{BigInt, RandBigInt};

    #[derive(Default)]
    struct MyCircuit<F> {
        P: Option<(Fp, Fp)>,
        Q: Option<(Fp, Fp)>,
        x: Option<F>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = FpConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self {
                P: None,
                Q: None,
                x: None,
                _marker: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            let constant = meta.fixed_column();
            EccChip::configure(meta, value, constant, 22, 66, 4)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EccChip::construct(config.clone());
            chip.load_lookup_table(&mut layouter)?;

            let P_assigned = chip.load_private(layouter.namespace(|| "input point P"), self.P)?;
            let Q_assigned = chip.load_private(layouter.namespace(|| "input point Q"), self.Q)?;
            let x_assigned = layouter.assign_region(
                || "input scalar x",
                |mut region| {
                    region.assign_advice(
                        || "assign x",
                        config.value,
                        0,
                        || self.x.ok_or(Error::Synthesis),
                    )
                },
            )?;

            // test add_unequal
            {
                let sum = chip.add_unequal(
                    &mut layouter.namespace(|| "add_unequal"),
                    &P_assigned,
                    &Q_assigned,
                )?;
            }

            /*
            // test point on curve
            {
                point_on_curve(
                    &chip.fp_chip.config.range,
                    &mut layouter,
                    &P_assigned,
                    F::from(3),
                )?;
            }
            */

            // test double
            {
                let doub = chip.double(
                    &mut layouter.namespace(|| "double"),
                    &P_assigned,
                    F::from(3),
                )?;
            }

            /*
            // test scalar mult
            {
                let scalar_mult = chip.scalar_mult(
                    &mut layouter.namespace(|| "scalar_mult"),
                    &P_assigned,
                    &x_assigned,
                    F::from(3),
                    12,
                )?;
            }
            */

            Ok(())
        }
    }

    use halo2_proofs::pairing::bn256::G1Affine;
    #[test]
    fn test_ecc() {
        let k = 22;
        let mut rng = rand::thread_rng();

        let P = G1Affine::random(&mut rng);
        let Q = G1Affine::random(&mut rng);

        let circuit = MyCircuit::<Fn> {
            P: Some((P.x, P.y)),
            Q: Some((Q.x, Q.y)),
            x: Some(Fn::from(11)),
            _marker: PhantomData,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_ecc() {
        let k = 11;
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (512, 8192)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Ecc Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fn> {
            P: None,
            Q: None,
            x: None,
            _marker: PhantomData,
        };

        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
