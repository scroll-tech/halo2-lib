use group::{Curve, Group};
use halo2_proofs::{
    arithmetic::{CurveAffine, Field, FieldExt},
    circuit::{AssignedCell, Value},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{Num, One, Zero};

use super::{
    ecc_add_unequal, ecc_double, ecc_sub_unequal, get_naf, is_on_curve, select, select_from_bits,
    EccPoint,
};
use crate::{
    fields::FieldChip,
    gates::{Context, GateInstructions, RangeInstructions},
};
use crate::{fields::Selectable, utils::modulus};

// Reference: https://jbootle.github.io/Misc/pippenger.pdf

// Reduction to multi-products
// Output:
// * new_points: length `points.len() * radix`
// * new_bool_scalars: 2d array `ceil(scalar_bits / radix)` by `points.len() * radix`
pub fn decompose<F, FC>(
    chip: &FC,
    ctx: &mut Context<'_, F>,
    points: &Vec<EccPoint<F, FC::FieldPoint>>,
    scalars: &Vec<Vec<AssignedCell<F, F>>>,
    max_scalar_bits_per_cell: usize,
    radix: usize,
) -> Result<(Vec<EccPoint<F, FC::FieldPoint>>, Vec<Vec<AssignedCell<F, F>>>), Error>
where
    F: FieldExt,
    FC: FieldChip<F>,
{
    assert_eq!(points.len(), scalars.len());
    let scalar_bits = max_scalar_bits_per_cell * scalars[0].len();
    let t = (scalar_bits + radix - 1) / radix;

    let mut new_points = Vec::with_capacity(radix * points.len());
    let mut new_bool_scalars = vec![Vec::with_capacity(radix * points.len()); t];

    let zero_cell = chip.range().gate().load_zero(ctx)?;

    for (point, scalar) in points.iter().zip(scalars.iter()) {
        assert_eq!(scalars[0].len(), scalar.len());
        let mut g = point.clone();
        new_points.push(g);
        for j in 1..radix {
            g = ecc_double(chip, ctx, &new_points.last().unwrap())?;
            new_points.push(g);
        }
        let mut bits = Vec::with_capacity(scalar_bits);
        for x in scalar {
            let mut new_bits = chip.range().num_to_bits(ctx, x, max_scalar_bits_per_cell)?;
            bits.append(&mut new_bits);
        }
        for k in 0..t {
            new_bool_scalars[k]
                .extend_from_slice(&bits[(radix * k)..std::cmp::min(radix * (k + 1), scalar_bits)]);
        }
        new_bool_scalars[t - 1].extend(vec![zero_cell.clone(); radix * t - scalar_bits]);
    }

    Ok((new_points, new_bool_scalars))
}

// Given points[i] and bool_scalars[j][i],
// compute G'[j] = sum_{i=0..points.len()} points[i] * bool_scalars[j][i]
// output is [ G'[j] + rand_point ]_{j=0..bool_scalars.len()}, rand_point
pub fn multi_product<F: FieldExt, FC, GA>(
    chip: &FC,
    ctx: &mut Context<'_, F>,
    points: &Vec<EccPoint<F, FC::FieldPoint>>,
    bool_scalars: &Vec<Vec<AssignedCell<F, F>>>,
    curve_b: F,
    clumping_factor: usize,
) -> Result<(Vec<EccPoint<F, FC::FieldPoint>>, EccPoint<F, FC::FieldPoint>), Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
    GA: CurveAffine<Base = FC::FieldType>,
{
    let c = clumping_factor; // this is `b` in Section 3 of Bootle
    let num_rounds = (points.len() + c - 1) / c;

    // we allow for points[i] to be the point at infinity, represented by (0, 0) in affine coordinates
    // this can be checked by points[i].y == 0 iff points[i] == O
    let mut is_infinity = Vec::with_capacity(points.len());
    for point in points.iter() {
        let is_zero = chip.is_zero(ctx, &point.y)?;
        is_infinity.push(is_zero);
    }

    // to avoid adding two points that are equal or negative of each other,
    // we use a trick from halo2wrong where we load a random GA point as witness
    // note that while we load a random point, an adversary could load a specifically chosen point, so we must carefully handle edge cases with constraints
    let mut rng = rand::thread_rng();
    let rand_base = {
        let base_point: GA = GA::CurveExt::random(&mut rng).to_affine();
        let base_point_coord = base_point.coordinates().unwrap();
        let pt_x = FC::fe_to_witness(&Value::known(*base_point_coord.x()));
        let pt_y = FC::fe_to_witness(&Value::known(*base_point_coord.y()));
        let x_overflow = chip.load_private(ctx, pt_x)?;
        let y_overflow = chip.load_private(ctx, pt_y)?;
        EccPoint::construct(x_overflow, y_overflow)
    };
    // for above reason we still need to constrain that the witness is on the curve
    is_on_curve(chip, ctx, &rand_base, curve_b)?;

    let mut acc = Vec::with_capacity(bool_scalars.len());

    let mut bucket = Vec::with_capacity(1 << c);
    let mut rand_point = rand_base.clone();
    for round in 0..num_rounds {
        // compute all possible multi-products of elements in points[round * c .. round * (c+1)]
        let clump = (round * c)..std::cmp::min((round + 1) * c, points.len());

        // for later addition collision-prevension, we need a different random point per round
        // we take 2^round * rand_base
        if round > 0 {
            rand_point = ecc_double(chip, ctx, &rand_point)?;
        }
        // stores { rand_point, rand_point + points[0], rand_point + points[1], rand_point + points[0] + points[1] , ... }
        // since rand_point is random, we can always use add_unequal (with strict constraint checking that the points are indeed unequal and not negative of each other)
        bucket.clear();
        bucket.push(rand_point.clone());
        for i in clump.clone() {
            for j in 0..(1 << (i - round * c)) {
                let mut new_point = ecc_add_unequal(chip, ctx, &bucket[j], &points[i], true)?;
                // if points[i] is point at infinity, do nothing
                new_point = select(chip, ctx, &bucket[j], &new_point, &is_infinity[i])?;
                bucket.push(new_point);
            }
        }

        // for each j, select using clump in e[j][i=...]
        for (j, bits) in bool_scalars.iter().enumerate() {
            let multi_prod = select_from_bits(chip, ctx, &bucket, &bits[clump.clone()].to_vec())?;
            if round == 0 {
                acc.push(multi_prod);
            } else {
                acc[j] = ecc_add_unequal(chip, ctx, &acc[j], &multi_prod, true)?;
            }
        }
    }

    // we have acc[j] = G'[j] + (2^num_rounds - 1) * rand_base
    rand_point = ecc_double(chip, ctx, &rand_point)?;
    rand_point = ecc_sub_unequal(chip, ctx, &rand_point, &rand_base, false)?;

    Ok((acc, rand_point))
}

pub fn multi_exp<F: FieldExt, FC, GA>(
    chip: &FC,
    ctx: &mut Context<'_, F>,
    points: &Vec<EccPoint<F, FC::FieldPoint>>,
    scalars: &Vec<Vec<AssignedCell<F, F>>>,
    curve_b: F,
    max_scalar_bits_per_cell: usize,
    radix: usize,
    clump_factor: usize,
) -> Result<EccPoint<F, FC::FieldPoint>, Error>
where
    FC: FieldChip<F> + Selectable<F, Point = FC::FieldPoint>,
    GA: CurveAffine<Base = FC::FieldType>,
{
    println!("radix: {}", radix);

    let (points, bool_scalars) =
        decompose(chip, ctx, points, scalars, max_scalar_bits_per_cell, radix)?;
    let t = bool_scalars.len();

    /*let c = {
        let m = points.len();
        let cost = |b: usize| -> usize { (m + b - 1) / b * ((1 << b) + t) };
        let c_max: usize = f64::from(points.len() as u32).log2().ceil() as usize;
        let mut c_best = c_max;
        for b in 1..c_max {
            if cost(b) <= cost(c_best) {
                c_best = b;
            }
        }
        c_best
    };*/
    let c = clump_factor;
    println!("clumping factor: {}", c);

    let (mut agg, rand_point) =
        multi_product::<F, FC, GA>(chip, ctx, &points, &bool_scalars, curve_b, c)?;

    // compute sum_{k=0..t} agg[k] * 2^{radix * k} - (sum_k 2^{radix * k}) * rand_point
    // (sum_{k=0..t} 2^{radix * k}) * rand_point = (2^{radix * t} - 1)/(2^radix - 1)
    let mut sum = agg.pop().unwrap();
    let mut rand_sum = rand_point.clone();
    for g in agg.iter().rev() {
        for _ in 0..radix {
            sum = ecc_double(chip, ctx, &sum)?;
            rand_sum = ecc_double(chip, ctx, &rand_sum)?;
        }
        sum = ecc_add_unequal(chip, ctx, &sum, g, true)?;

        if radix != 1 {
            // Can use non-strict as long as some property of the prime is true?
            rand_sum = ecc_add_unequal(chip, ctx, &rand_sum, &rand_point, false)?;
        }
    }

    if radix == 1 {
        rand_sum = ecc_double(chip, ctx, &rand_sum)?;
        // assume 2^t != +-1 mod modulus::<F>()
        rand_sum = ecc_sub_unequal(chip, ctx, &rand_sum, &rand_point, false)?;
    }

    ecc_sub_unequal(chip, ctx, &sum, &rand_sum, true)
}
