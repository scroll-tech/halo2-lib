use core::num;
use std::collections::{HashMap, HashSet};

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::{BigInt, BigUint};
use num_traits::pow;

use crate::gates::{
    flex_gate::{FlexGateConfig, GateStrategy},
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::utils::{bigint_to_fe, biguint_to_fe, decompose_option, fe_to_biguint};

use super::{Context, RangeInstructions};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RangeStrategy {
    Vertical, // vanilla implementation with vertical basic gate(s)
    // CustomVerticalShort, // vertical basic gate(s) and vertical custom range gates of length 2,3
    PlonkPlus,
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
    // pub q_range: HashMap<usize, Vec<Selector>>,
    pub gate: FlexGateConfig<F>,
    strategy: RangeStrategy,
}

/*
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
*/

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

        let gate = FlexGateConfig::configure(
            meta,
            match range_strategy {
                RangeStrategy::Vertical => GateStrategy::Vertical,
                RangeStrategy::PlonkPlus => GateStrategy::PlonkPlus,
            },
            num_advice,
            num_fixed,
        );

        /*
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
        */

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
                // q_range,
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
                // q_range,
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
                        || Value::known(F::from(idx as u64)),
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

        // In the case there is only 1 advice column, we need to figure out what the starting offset in the column was before this function call
        let offset_shift = if self.gate.basic_gates.len() == 1 { ctx.advice_rows[0] } else { 0 };

        let limbs = decompose_option(&a.value().map(|x| *x), k, self.lookup_bits);
        let (limbs_assigned, _, acc, _) = self.gate.inner_product(
            ctx,
            &limbs.into_iter().map(|limb| Witness(limb)).collect(),
            &(0..k)
                .map(|i| Constant(biguint_to_fe(&(BigUint::from(1u64) << (i * self.lookup_bits)))))
                .collect(),
        )?;
        let limbs_assigned = limbs_assigned.unwrap();

        // the inner product above must equal `a`
        ctx.region.constrain_equal(a.cell(), acc.cell())?;

        // range check all the limbs
        for i in 0..k {
            self.enable_lookup(
                ctx,
                limbs_assigned[i].0.clone(),
                offset_shift + limbs_assigned[i].1,
            )?;
        }

        // additional constraints for the last limb if rem_bits != 0
        if rem_bits == 1 {
            // we want to check x := limbs[k-1] is boolean
            // we constrain x*(x-1) = 0 + x * x - x == 0
            // | 0 | x | x | x |
            self.gate.assign_region_smart(
                ctx,
                vec![
                    Constant(F::zero()),
                    Existing(&limbs_assigned[k - 1].0),
                    Existing(&limbs_assigned[k - 1].0),
                    Existing(&limbs_assigned[k - 1].0),
                ],
                vec![0],
                vec![],
                vec![],
            )?;
        } else if rem_bits > 1 {
            let mult_val = biguint_to_fe(&(BigUint::from(1u64) << (self.lookup_bits - rem_bits)));
            let offset = if self.gate.basic_gates.len() == 1 { ctx.advice_rows[0] } else { 0 };
            let (assignments, gate_index) = self.gate.assign_region(
                ctx,
                vec![
                    Constant(F::zero()),
                    Existing(&limbs_assigned[k - 1].0),
                    Constant(mult_val),
                    Witness(limbs_assigned[k - 1].0.value().map(|limb| mult_val * limb)),
                ],
                vec![(0, None)],
                None,
            )?;
            self.enable_lookup(ctx, assignments.last().unwrap().clone(), offset + 3)?;
        }

        Ok(limbs_assigned.into_iter().map(|limb| limb.0).collect())
    }

    /// assume `a` has been range checked already to `limb_bits` bits
    pub fn get_last_bit(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        limb_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let a_v = a.value();
        let bit_v = a_v.map(|a| {
            let a_big = fe_to_biguint(a);
            if a_big % 2u64 == BigUint::from(0u64) {
                F::zero()
            } else {
                F::one()
            }
        });
        let h_v = a.value().zip(bit_v).map(|(&a, b)| (a - b) * F::from(2).invert().unwrap());
        let assignments = self.gate.assign_region_smart(
            ctx,
            vec![Witness(bit_v), Witness(h_v), Constant(F::from(2)), Existing(a)],
            vec![0],
            vec![],
            vec![],
        )?;

        self.range_check(ctx, &assignments[1], limb_bits - 1)?;
        Ok(assignments[0].clone())
    }
}

impl<F: FieldExt> RangeInstructions<F> for RangeConfig<F> {
    type Gate = FlexGateConfig<F>;

    fn gate(&self) -> &Self::Gate {
        &self.gate
    }
    fn strategy(&self) -> RangeStrategy {
        self.strategy
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
        #[cfg(feature = "display")]
        {
            let key = format!(
                "range check length {}",
                (range_bits + self.lookup_bits - 1) / self.lookup_bits
            );
            let count = ctx.op_count.entry(key).or_insert(0);
            *count += 1;
        }
        match self.strategy {
            RangeStrategy::Vertical | RangeStrategy::PlonkPlus => {
                self.range_check_simple(ctx, a, range_bits)
            }
        }
    }

    /// Warning: This may fail silently if a or b have more than num_bits
    fn check_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error> {
        let pow_of_two = biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits));
        let check_cell = match self.strategy {
            RangeStrategy::Vertical => {
                // | a + 2^(num_bits) - b | b | 1 | a + 2^(num_bits) | - 2^(num_bits) | 1 | a |
                let cells = vec![
                    Witness(Value::known(pow_of_two) + a.value() - b.value()),
                    Existing(&b),
                    Constant(F::from(1)),
                    Witness(Value::known(pow_of_two) + a.value()),
                    Constant(-pow_of_two),
                    Constant(F::from(1)),
                    Existing(&a),
                ];
                let assigned_cells =
                    self.gate.assign_region_smart(ctx, cells, vec![0, 3], vec![], vec![])?;
                assigned_cells[0].clone()
            }
            RangeStrategy::PlonkPlus => {
                // | a | 1 | b | a + 2^{num_bits} - b |
                // selectors:
                // | 1 | 0 | 0 |
                // | 0 | 2^{num_bits} | -1 |
                let (assigned_cells, _) = self.gate.assign_region(
                    ctx,
                    vec![
                        Existing(&a),
                        Constant(F::from(1)),
                        Existing(&b),
                        Witness(Value::known(pow_of_two) + a.value() - b.value()),
                    ],
                    vec![(0, Some([F::zero(), pow_of_two, -F::one()]))],
                    None,
                )?;
                assigned_cells[3].clone()
            }
        };

        self.range_check(ctx, &check_cell, num_bits)?;
        Ok(())
    }

    fn is_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        // TODO: optimize this for PlonkPlus strategy
        let k = (num_bits + self.lookup_bits - 1) / self.lookup_bits;
        let padded_bits = k * self.lookup_bits;
        let pow_padded = biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits));

        let shifted_val = a.value().zip(b.value()).map(|(&av, &bv)| av + pow_padded - bv);
        let shifted_cell = match self.strategy {
            RangeStrategy::Vertical => {
                let assignments = self.gate.assign_region_smart(
                    ctx,
                    vec![
                        Witness(shifted_val),
                        Existing(&b),
                        Constant(F::one()),
                        Witness(a.value().map(|&av| av + pow_padded)),
                        Constant(-pow_padded),
                        Constant(F::one()),
                        Existing(&a),
                    ],
                    vec![0, 3],
                    vec![],
                    vec![],
                )?;
                assignments[0].clone()
            }
            RangeStrategy::PlonkPlus => {
                let (assignments, _) = self.gate.assign_region(
                    ctx,
                    vec![Existing(&a), Constant(pow_padded), Existing(&b), Witness(shifted_val)],
                    vec![(0, Some([F::zero(), F::one(), -F::one()]))],
                    None,
                )?;
                assignments.last().unwrap().clone()
            }
        };

        // check whether a - b + 2^padded_bits < 2^padded_bits ?
        // since assuming a, b < 2^padded_bits we are guaranteed a - b + 2^padded_bits < 2^{padded_bits + 1}
        let limbs = self.range_check(ctx, &shifted_cell, padded_bits + self.lookup_bits)?;
        self.is_zero(ctx, &limbs[k])
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
        let bits = decompose_option(&a.value().copied(), range_bits, 1usize);
        let bit_cells = match self.strategy {
            RangeStrategy::Vertical => {
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
            }
            RangeStrategy::PlonkPlus => {
                let (bit_cells, _, acc, _) = self.gate.inner_product(
                    ctx,
                    &bits.iter().map(|x| Witness(*x)).collect(),
                    &(0..range_bits)
                        .map(|i| Constant(biguint_to_fe(&(BigUint::from(1u64) << i))))
                        .collect(),
                )?;
                ctx.region.constrain_equal(a.cell(), acc.cell())?;
                bit_cells.unwrap().into_iter().map(|(x, _)| x).collect()
            }
        };
        for bit_cell in &bit_cells {
            self.gate.assign_region_smart(
                ctx,
                vec![
                    Constant(F::from(0)),
                    Existing(&bit_cell),
                    Existing(&bit_cell),
                    Existing(&bit_cell),
                ],
                vec![0],
                vec![],
                vec![],
            )?;
        }
        Ok(bit_cells)
    }
}
