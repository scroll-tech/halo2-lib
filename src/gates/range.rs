use core::num;
use std::collections::{HashMap, HashSet};

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::{BigInt, BigUint};

use crate::gates::{
    flex_gate::{FlexGateConfig, GateStrategy},
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::utils::{
    bigint_to_fe, biguint_to_fe, decompose_biguint_option, decompose_option, fe_to_biguint,
};

use super::{Context, RangeInstructions};

#[derive(Clone, Debug, PartialEq)]
pub enum RangeStrategy {
    Vertical, // vanilla implementation with vertical basic gate(s)
    CustomVerticalShort, // vertical basic gate(s) and vertical custom range gates of length 2,3
              // CustomHorizontal, // vertical basic gate and dedicated horizontal custom gate
}

#[derive(Clone, Debug)]
pub struct RangeConfig<F: FieldExt> {
    // `lookup_advice` are special advice columns only used for lookups
    //
    // If `strategy` is `Vertical` or `CustomVertical`:
    // * If `gate` has only 1 advice column, enable lookups for that column, in which case `lookup_advice` is empty
    // * Otherwise, add some user-specified number of `lookup_advice` columns
    //   * In this case, we don't even need a selector so `q_lookup` is empty
    // If `strategy` is `CustomHorizontal`:
    // * TODO
    pub lookup_advice: Vec<Column<Advice>>,
    pub q_lookup: Vec<Selector>,
    pub lookup: TableColumn,
    pub lookup_bits: usize,
    // selector for custom range gate
    // `q_range[k][i]` stores the selector for a custom range gate of length `k`
    pub q_range: HashMap<usize, Vec<Selector>>,
    pub gate: FlexGateConfig<F>,
    strategy: RangeStrategy,
}

/// vertical gate that constraints `a[0] == a[1] + a[2] * 2^lookup_bits + ... + a[k] * 2^{lookup_bits * (k-1)}`
fn create_vertical_range_gate<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    k: i32,
    lookup_bits: usize,
    value: Column<Advice>,
    selector: Selector,
) {
    meta.create_gate("custom vertical range gate", |meta| {
        let q = meta.query_selector(selector);
        let out = meta.query_advice(value, Rotation::cur());
        let a: Vec<Expression<F>> =
            (0..k).map(|i| meta.query_advice(value, Rotation(i + 1))).collect();
        let limb_base = F::from(1u64 << lookup_bits);
        let sum = a.iter().fold((Expression::Constant(F::from(0)), F::from(1)), |(sum, pow), a| {
            (sum + a.clone() * Expression::Constant(pow), pow * limb_base)
        });
        vec![q * (sum.0 - out)]
    })
}

impl<F: FieldExt> RangeConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        range_strategy: RangeStrategy,
        num_advice: usize,
        mut num_lookup_advice: usize,
        num_fixed: usize,
        lookup_bits: usize,
    ) -> Self {
        assert!(lookup_bits <= 28);

        let lookup = meta.lookup_table_column();
        // GateStrategy::Horizontal is strictly inferior performance-wise
        let gate = FlexGateConfig::configure(meta, GateStrategy::Vertical, num_advice, num_fixed);

        let mut q_range = HashMap::new();

        if range_strategy == RangeStrategy::CustomVerticalShort {
            // we only use range length 3 because range length `k` requires Rotation(0..=k)
            // to minimize the different polynomial evaluation SETS we only use Rotation(0..=3), since that is what is used in our basic vertical gate
            for k in 3..4 {
                let mut selectors = Vec::with_capacity(gate.basic_gates.len());
                for gate in &gate.basic_gates {
                    let q = meta.selector();
                    selectors.push(q);
                    create_vertical_range_gate(meta, k as i32, lookup_bits, gate.value, q);
                }
                q_range.insert(k, selectors);
            }
        }

        if num_advice == 1 {
            num_lookup_advice = 0;
        }
        let mut lookup_advice = Vec::with_capacity(num_lookup_advice);
        for _i in 0..num_lookup_advice {
            let a = meta.advice_column();
            meta.enable_equality(a);
            lookup_advice.push(a);
        }
        let config = if num_advice > 1 {
            Self {
                lookup_advice,
                q_lookup: Vec::new(),
                lookup,
                lookup_bits,
                q_range,
                gate,
                strategy: range_strategy,
            }
        } else {
            let q = meta.complex_selector();
            Self {
                lookup_advice: vec![],
                q_lookup: vec![q],
                lookup,
                lookup_bits,
                q_range,
                gate,
                strategy: range_strategy,
            }
        };
        config.create_lookup(meta);

        config
    }

    fn create_lookup(&self, meta: &mut ConstraintSystem<F>) -> () {
        for i in 0..self.q_lookup.len() {
            meta.lookup("lookup", |meta| {
                let q = meta.query_selector(self.q_lookup[i]);
                let a = meta.query_advice(self.gate.basic_gates[i].value, Rotation::cur());
                vec![(q * a, self.lookup)]
            });
        }
        for la in self.lookup_advice.iter() {
            meta.lookup("lookup wo selector", |meta| {
                let a = meta.query_advice(la.clone(), Rotation::cur());
                vec![(a, self.lookup)]
            });
        }
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || format!("{} bit lookup", self.lookup_bits),
            |mut table| {
                for idx in 0..(1u32 << self.lookup_bits) {
                    table.assign_cell(
                        || "lookup table",
                        self.lookup,
                        idx as usize,
                        || Ok(F::from(idx as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    /// call this at the very end of synthesize!
    /// returns (total number of constants assigned, total number of lookup cells assigned)
    pub fn finalize(&self, ctx: &mut Context<'_, F>) -> Result<(usize, usize, usize), Error> {
        let (c_rows, c_count) = self.gate.finalize(ctx)?;
        let lookup_rows = ctx.copy_and_lookup_cells(&self.lookup_advice)?;
        Ok((c_rows, c_count, lookup_rows))
    }

    /// assuming this is called when ctx.region is not in shape mode
    /// `offset` is the offset of the cell in `ctx.region`
    /// `offset` is only used if there is a single advice column
    fn enable_lookup(
        &self,
        ctx: &mut Context<'_, F>,
        acell: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<(), Error> {
        if self.q_lookup.len() > 0 {
            // currently we only use non-specialized lookup columns if there is only a single advice column
            assert_eq!(self.gate.basic_gates.len(), 1);
            self.q_lookup[0].enable(&mut ctx.region, offset)?;
        } else {
            // offset is not used in this case
            ctx.cells_to_lookup.push(acell);
        }
        Ok(())
    }

    // returns the limbs
    fn range_check_simple(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = (range_bits + self.lookup_bits - 1) / self.lookup_bits;
        // println!("range check {} bits {} len", range_bits, k);
        let rem_bits = range_bits % self.lookup_bits;

        let limbs = decompose_option(&a.value().map(|x| *x), k, self.lookup_bits);
        let limb_base = F::from(1u64 << self.lookup_bits);

        // In the case there is only 1 advice column, we need to figure out what the starting offset in the column was before this function call
        let offset_shift = if self.gate.basic_gates.len() == 1 { ctx.advice_rows[0] } else { 0 };
        // this `offset` is the relative offset with respect to the indices of `cells` below (the local computation trace)
        let mut offset = 1;
        let mut running_sum = limbs[0];
        let mut running_pow = F::from(1u64);

        let mut enable_lookups = Vec::new();
        let mut enable_gates = Vec::new();

        enable_lookups.push(0);
        let mut cells = Vec::with_capacity(3 * k + 2);
        cells.push(Witness(limbs[0]));
        for idx in 1..k {
            running_pow = running_pow * limb_base;
            running_sum = running_sum.zip(limbs[idx]).map(|(sum, x)| sum + x * running_pow);
            cells.push(Constant(running_pow));
            cells.push(Witness(limbs[idx]));
            if idx < k - 1 || rem_bits != 1 {
                enable_lookups.push(offset + 1);
            }
            cells.push(Witness(running_sum));
            enable_gates.push(offset - 1);

            offset = offset + 3;
            if idx == k - 1 {
                if rem_bits == 1 {
                    enable_gates.push(offset);
                    // we want to check x := limbs[idx] is boolean
                    // we constrain x*(x-1) = 0 + x * x - x == 0
                    // | 0 | x | x | x |
                    cells.push(Constant(F::from(0)));
                    cells.push(Witness(limbs[k - 1]));
                    cells.push(Witness(limbs[k - 1]));
                    cells.push(Witness(limbs[k - 1]));
                } else if rem_bits > 1 {
                    enable_gates.push(offset);
                    let mult_val =
                        biguint_to_fe(&(BigUint::from(1u64) << (self.lookup_bits - rem_bits)));
                    cells.push(Constant(F::from(0)));
                    cells.push(Witness(limbs[k - 1]));
                    cells.push(Constant(mult_val));
                    cells.push(Witness(Some(mult_val).zip(limbs[k - 1]).map(|(m, l)| m * l)));
                    enable_lookups.push(offset + 3);
                }
            }
        }

        let mut eq_list = vec![];
        if rem_bits != 0 {
            eq_list.push((3 * k - 1, 3 * k - 4));
            if rem_bits == 1 {
                //         | 3k - 4 | 3k - 3 | 3k - 2 | 3k - 1 | 3k    | 3k + 1 |
                // we want | x      | a.cell | 0      | x      | x     | x      |
                // with x = limbs[idx]
                eq_list.push((3 * k, 3 * k - 4));
                eq_list.push((3 * k + 1, 3 * k - 4));
            }
        }

        let assigned_cells = self.gate.assign_region_smart(
            ctx,
            cells,
            enable_gates,
            eq_list,
            vec![(a, 3 * (k - 1))],
        )?;

        for relative_row in enable_lookups {
            self.enable_lookup(
                ctx,
                assigned_cells[relative_row].clone(),
                offset_shift + relative_row,
            )?;
        }

        let mut assigned_limbs = Vec::with_capacity(k);
        assigned_limbs.push(assigned_cells[0].clone());
        for idx in 1..k {
            assigned_limbs.push(assigned_cells[3 * idx - 1].clone());
        }
        Ok(assigned_limbs)
    }

    // returns the limbs
    fn range_check_custom_vertical_short(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = (range_bits + self.lookup_bits - 1) / self.lookup_bits;
        let limbs = decompose_option(&a.value().map(|x| *x), k, self.lookup_bits);
        let rem_bits = range_bits % self.lookup_bits;

        const MAX_RANGE_POW: usize = 2;
        assert!(
            self.q_range.contains_key(&(MAX_RANGE_POW + 1)),
            "No custom range chip of length {}",
            MAX_RANGE_POW + 1
        );
        let k_chunks = (k - 1 + MAX_RANGE_POW - 1) / MAX_RANGE_POW;
        let limb_base = F::from(1 << self.lookup_bits);

        // In the case there is only 1 advice column, we need to figure out what the starting offset in the column was before this function call
        let offset_shift = if self.gate.basic_gates.len() == 1 { ctx.advice_rows[0] } else { 0 };

        // let a = a0 + a1 * X + a2 * X^2 + a3 * X^3 + a4 * X^4 + a5 * X^5 (for example)
        // with X = 2^lookup_bits
        // then take transpose of
        // | a | a0 | a1 | y | a2 | a3 | z | a4 | a5 | 0 |
        // and we enable q_range[3] on
        // | 1 | 0  | 0  | 1 | 0  | 0  | 1 | 0  | 0  | 0 |
        let mut rev_cells = Vec::with_capacity((MAX_RANGE_POW + 1) * k_chunks);
        let mut rev_limb_indices = Vec::with_capacity(k);
        let mut enable_range = Vec::with_capacity(k_chunks);
        let mut enable_gates = Vec::new();
        let mut enable_lookups = Vec::with_capacity(k);
        let mut enable_equality = Vec::new();

        let mut start = k_chunks * MAX_RANGE_POW;
        rev_cells.extend(((k - 1)..start).map(|_| Constant(F::from(0))));
        rev_limb_indices.push(rev_cells.len());
        rev_cells.push(Witness(limbs[k - 1]));
        let mut running_sum = limbs[k - 1];
        while start > 0 {
            start -= MAX_RANGE_POW;
            let window =
                [&limbs[start..std::cmp::min(start + MAX_RANGE_POW, k - 1)], &[running_sum]]
                    .concat();
            running_sum = window
                .iter()
                .rev()
                .fold(Some(F::from(0)), |acc, &val| acc.zip(val).map(|(a, v)| a * limb_base + v));
            let len = window.len() - 1;
            rev_limb_indices.extend((0..len).map(|i| rev_cells.len() + i));
            rev_cells.extend((0..len).rev().map(|i| Witness(limbs[start + i])));
            rev_cells.push(Witness(running_sum));
            enable_range.push(rev_cells.len() - 1);
        }
        if k == 1 {
            assert_eq!(rev_cells.len(), 1);
            enable_range.push(0);
        }
        rev_cells.reverse();
        let mut cells = rev_cells;
        let tmp_len = cells.len();
        for rev_row in enable_range.iter_mut() {
            *rev_row = tmp_len - 1 - *rev_row;
        }
        rev_limb_indices.reverse();
        for (id, r) in rev_limb_indices.iter_mut().enumerate() {
            *r = tmp_len - 1 - *r;
            if id != 0 || rem_bits != 1 {
                enable_lookups.push(*r);
            }
        }
        let limb_indices = rev_limb_indices;

        if rem_bits != 0 {
            if rem_bits == 1 {
                // we want to check x := assigned_limbs[k-1] is boolean
                // we constrain x*(x-1) = 0 + x * x - x == 0
                // | 0 | x | x | x |
                cells.extend([
                    Constant(F::from(0)),
                    Witness(limbs[k - 1]),
                    Witness(limbs[k - 1]),
                    Witness(limbs[k - 1]),
                ]);
                enable_gates.push(tmp_len);
                enable_equality.extend((1..4).map(|i| (limb_indices[k - 1], tmp_len + i)));
            } else {
                let mult_val =
                    biguint_to_fe(&(BigUint::from(1u64) << (self.lookup_bits - rem_bits)));
                cells.extend([
                    Constant(F::from(0)),
                    Witness(limbs[k - 1]),
                    Constant(mult_val),
                    Witness(Some(mult_val).zip(limbs[k - 1]).map(|(m, l)| m * l)),
                ]);
                enable_gates.push(tmp_len);
                enable_equality.push((limb_indices[k - 1], tmp_len + 1));
                enable_lookups.push(tmp_len + 3);
            }
        }

        let (assigned_cells, gate_index) = self.gate.assign_region(ctx, cells, enable_gates)?;
        ctx.region.constrain_equal(a.cell(), assigned_cells[0].cell())?;

        for (i, j) in enable_equality {
            ctx.region.constrain_equal(assigned_cells[i].cell(), assigned_cells[j].cell())?;
        }

        let gate_offset_shift = ctx.advice_rows[gate_index] - assigned_cells.len();
        for row in enable_range {
            self.q_range.get(&(MAX_RANGE_POW + 1)).unwrap()[gate_index]
                .enable(&mut ctx.region, gate_offset_shift + row)?;
        }

        for i in enable_lookups {
            self.enable_lookup(ctx, assigned_cells[i].clone(), offset_shift + i)?;
        }

        let assigned_limbs: Vec<AssignedCell<F, F>> =
            limb_indices.iter().map(|&i| assigned_cells[i].clone()).collect();
        assert_eq!(assigned_limbs.len(), k);

        Ok(assigned_limbs)
    }
}

impl<F: FieldExt> RangeInstructions<F> for RangeConfig<F> {
    type Gate = FlexGateConfig<F>;

    fn gate(&self) -> &Self::Gate {
        &self.gate
    }

    fn lookup_bits(&self) -> usize {
        self.lookup_bits
    }

    // returns the limbs
    fn range_check(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        assert_ne!(range_bits, 0);
        match self.strategy {
            RangeStrategy::Vertical => self.range_check_simple(ctx, a, range_bits),
            RangeStrategy::CustomVerticalShort => {
                self.range_check_custom_vertical_short(ctx, a, range_bits)
            }
        }
    }

    // Warning: This may fail silently if a or b have more than num_bits
    // | a + 2^(num_bits) - b | b | 1 | a + 2^(num_bits) | - 2^(num_bits) | 1 | a |
    fn check_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error> {
        let cells = vec![
            Witness(
                Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                    .zip(a.value())
                    .zip(b.value())
                    .map(|((x, av), bv)| *av + x - *bv),
            ),
            Existing(&b),
            Constant(F::from(1)),
            Witness(
                Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                    .zip(a.value())
                    .map(|(x, av)| *av + x),
            ),
            Constant(bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << num_bits)))),
            Constant(F::from(1)),
            Existing(&a),
        ];
        let assigned_cells =
            self.gate.assign_region_smart(ctx, cells, vec![0, 3], vec![], vec![])?;

        self.range_check(ctx, &assigned_cells[0], num_bits)?;
        Ok(())
    }

    fn is_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let k = (num_bits + self.lookup_bits - 1) / self.lookup_bits;
        let padded_bits = k * self.lookup_bits;

        let mut enable_lookups = Vec::new();
        let mut enable_gates = Vec::new();
        enable_gates.push(0);
        enable_gates.push(3);
        enable_lookups.push(8);

        let mut cells = Vec::with_capacity(9 + 3 * k + 8);
        let shifted_val = Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
            .zip(a.value())
            .zip(b.value())
            .map(|((x, av), bv)| *av + x - *bv);
        cells.push(Witness(shifted_val));
        cells.push(Existing(&b));
        cells.push(Constant(F::from(1)));
        cells.push(Witness(
            Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
                .zip(a.value())
                .map(|(x, av)| *av + x),
        ));
        cells.push(Constant(bigint_to_fe::<F>(
            &(BigInt::from(-1i64) * (BigInt::from(1u64) << padded_bits)),
        )));
        cells.push(Constant(F::from(1)));
        cells.push(Existing(&a));
        cells.push(Witness(shifted_val));

        let mut shift_val = shifted_val.as_ref().map(|fe| fe_to_biguint(fe));
        let mask = BigUint::from(1u64 << self.lookup_bits);
        let mut limb = shift_val.as_ref().map(|x| x.modpow(&BigUint::from(1u64), &mask));
        cells.push(Witness(limb.as_ref().map(|x| biguint_to_fe(x))));

        let mut offset = 9;
        let mut running_sum = limb;
        for idx in 1..(k + 1) {
            shift_val = shift_val.map(|x| x >> self.lookup_bits);
            limb = shift_val.as_ref().map(|x| x.modpow(&BigUint::from(1u64), &mask));
            running_sum = running_sum
                .zip(limb.as_ref())
                .map(|(sum, x)| sum + (x << (idx * self.lookup_bits)));
            let running_pow = biguint_to_fe(&(BigUint::from(1u64) << (idx * self.lookup_bits)));
            cells.push(Constant(running_pow));
            cells.push(Witness(limb.as_ref().map(|x| biguint_to_fe(x))));
            cells.push(Witness(running_sum.as_ref().map(|sum| biguint_to_fe(sum))));
            enable_gates.push(offset - 1);
            enable_lookups.push(offset + 1);

            offset = offset + 3;
            if idx == k {
                let is_zero = limb.clone().zip(Some(F::from(1))).map(|(x, _y)| {
                    if x == BigUint::from(0u64) {
                        F::from(1)
                    } else {
                        F::from(0)
                    }
                });
                let inv = limb.clone().zip(Some(F::from(1))).map(|(x, _y)| {
                    if x == BigUint::from(0u64) {
                        F::from(1)
                    } else {
                        biguint_to_fe::<F>(&x).invert().unwrap()
                    }
                });

                enable_gates.push(offset);
                cells.push(Witness(is_zero));
                cells.push(Witness(limb.as_ref().map(|bi| biguint_to_fe(bi))));
                cells.push(Witness(inv));
                cells.push(Constant(F::from(1)));
                cells.push(Constant(F::from(0)));
                cells.push(Witness(limb.as_ref().map(|bi| biguint_to_fe(bi))));
                cells.push(Witness(is_zero));
                cells.push(Constant(F::from(0)));
            }
        }
        let mut eq_list = vec![];
        eq_list.push((0, 7));
        // check limb equalities for idx = k
        eq_list.push((9 + 3 * k - 2, 9 + 3 * k + 1));
        eq_list.push((9 + 3 * k - 2, 9 + 3 * k + 5));
        // check is_zero equalities
        eq_list.push((9 + 3 * k, 9 + 3 * k + 6));

        // In the case there is only 1 advice column, we need to figure out what the starting offset in the column was before this function call
        let offset_shift = if self.gate.basic_gates.len() == 1 { ctx.advice_rows[0] } else { 0 };

        let assigned_cells =
            self.gate.assign_region_smart(ctx, cells, enable_gates, eq_list, vec![])?;
        for row in enable_lookups {
            self.enable_lookup(ctx, assigned_cells[row].clone(), offset_shift + row)?;
        }
        Ok(assigned_cells[9 + 3 * k].clone())
    }

    // | out | a | inv | 1 | 0 | a | out | 0
    fn is_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero =
            a.value().map(|x| if (*x).is_zero_vartime() { F::from(1) } else { F::from(0) });
        let inv =
            a.value().map(|x| if *x == F::from(0) { F::from(1) } else { (*x).invert().unwrap() });

        let cells = vec![
            Witness(is_zero),
            Existing(&a),
            Witness(inv),
            Constant(F::from(1)),
            Constant(F::from(0)),
            Existing(&a),
            Witness(is_zero),
            Constant(F::from(0)),
        ];
        let assigned_cells =
            self.gate.assign_region_smart(ctx, cells, vec![0, 4], vec![(0, 6)], vec![])?;
        Ok(assigned_cells[0].clone())
    }

    fn is_equal(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells = vec![
            Witness(a.value().zip(b.value()).map(|(av, bv)| *av - *bv)),
            Constant(F::from(1)),
            Existing(&b),
            Existing(&a),
        ];
        let assigned_cells = self.gate.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;

        self.is_zero(ctx, &assigned_cells[0])
    }

    // returns little-endian bit vectors
    fn num_to_bits(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let bits = decompose_biguint_option(&a.value().map(|x| *x), range_bits, 1usize);
        let bit_cells = {
            let mut enable_gates = Vec::new();
            let mut cells = Vec::with_capacity(3 * range_bits - 2);
            let mut running_sum = bits[0];
            let mut running_pow = F::from(1u64);
            cells.push(Witness(bits[0]));
            let mut offset = 1;
            for idx in 1..range_bits {
                running_pow = running_pow * F::from(2u64);
                running_sum = running_sum.zip(bits[idx]).map(|(x, b)| x + b * running_pow);
                cells.push(Constant(running_pow));
                cells.push(Witness(bits[idx]));
                cells.push(Witness(running_sum));

                enable_gates.push(offset - 1);
                offset = offset + 3;
            }
            let last_idx = cells.len() - 1;
            let assigned_cells = self.gate.assign_region_smart(
                ctx,
                cells,
                enable_gates,
                vec![],
                vec![(a, last_idx)],
            )?;

            let mut assigned_bits = Vec::with_capacity(range_bits);
            assigned_bits.push(assigned_cells[0].clone());
            for idx in 1..range_bits {
                assigned_bits.push(assigned_cells[3 * idx - 1].clone());
            }
            assigned_bits
        };

        for idx in 0..range_bits {
            self.gate.assign_region_smart(
                ctx,
                vec![
                    Constant(F::from(0)),
                    Existing(&bit_cells[idx]),
                    Existing(&bit_cells[idx]),
                    Existing(&bit_cells[idx]),
                ],
                vec![0],
                vec![],
                vec![],
            )?;
        }
        Ok(bit_cells)
    }
}
