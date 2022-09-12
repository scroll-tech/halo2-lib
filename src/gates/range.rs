use core::num;
use std::collections::{HashMap, HashSet};

use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::{BigInt, BigUint};

use crate::gates::{
    flex_gate::{FlexGateChip, FlexGateConfig, GateStrategy},
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::utils::{
    bigint_to_fe, biguint_to_fe, decompose_biguint_option, decompose_option, fe_to_biguint,
};

use super::RangeInstructions;

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
    // * If `gate_config` has only 1 advice column, enable lookups for that column, in which case `lookup_advice` is empty
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
    pub gate_config: FlexGateConfig<F>,
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
        num_lookup_advice: usize,
        num_fixed: usize,
        lookup_bits: usize,
    ) -> Self {
        assert!(lookup_bits <= 28);

        let lookup = meta.lookup_table_column();
        // GateStrategy::Horizontal is strictly inferior performance-wise
        let gate_config =
            FlexGateConfig::configure(meta, GateStrategy::Vertical, num_advice, num_fixed);

        let mut q_range = HashMap::new();

        if range_strategy == RangeStrategy::CustomVerticalShort {
            // we only use range length 2, 3 because range length `k` requires Rotation(0..=k)
            // to minimize the distinct point sets we only use up to Rotation(3), since that is what is used in our basic vertical gate
            for k in 2..4 {
                let mut selectors = Vec::with_capacity(gate_config.gates.len());
                for gate in &gate_config.gates {
                    let q = meta.selector();
                    selectors.push(q);
                    create_vertical_range_gate(meta, k as i32, lookup_bits, gate.value, q);
                }
                q_range.insert(k, selectors);
            }
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
                gate_config,
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
                gate_config,
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
                let a = meta.query_advice(self.gate_config.gates[i].value, Rotation::cur());
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
}

// See FlexGateChip for why we need distinction between Config and Chip
#[derive(Clone, Debug)]
pub struct RangeChip<F: FieldExt> {
    // there is redundancy between `config.gate_config` and `gate.config` but the dev experience is easier
    pub config: RangeConfig<F>,
    pub gate: FlexGateChip<F>,
    // `cells_to_lookup` is a vector keeping track of all cells that we want to enable lookup for. When there is more than 1 advice column we will copy_advice all of these cells to the single lookup enabled column and do lookups there
    pub cells_to_lookup: Vec<AssignedCell<F, F>>,
    pub first_pass: bool,
    pub seen: HashSet<usize>,
}

impl<F: FieldExt> RangeChip<F> {
    pub fn construct(config: RangeConfig<F>, using_simple_floor_planner: bool) -> Self {
        let gate = FlexGateChip::construct(config.clone().gate_config, using_simple_floor_planner);
        Self { config, gate, cells_to_lookup: Vec::new(), first_pass: true, seen: HashSet::new() }
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || format!("{} bit lookup", self.config.lookup_bits),
            |mut table| {
                for idx in 0..(1u32 << self.config.lookup_bits) {
                    table.assign_cell(
                        || "lookup table",
                        self.config.lookup,
                        idx as usize,
                        || Ok(F::from(idx as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    pub fn copy_and_lookup_cells(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "load lookup advice column",
            |mut region| {
                if self.gate.using_simple_floor_planner && self.first_pass {
                    self.first_pass = false;
                    return Ok(());
                }
                let mut col = 0;
                let mut offset = 0;
                for acell in &self.cells_to_lookup {
                    acell.copy_advice(
                        || "copy lookup cell",
                        &mut region,
                        self.config.lookup_advice[col],
                        offset,
                    )?;
                    col += 1;
                    if col == self.config.lookup_advice.len() {
                        col = 0;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }

    fn enable_lookup(
        &mut self,
        region: &mut Region<'_, F>,
        acell: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<(), Error> {
        if self.config.q_lookup.len() > 0 {
            self.config.q_lookup[0].enable(region, offset)?;
        } else {
            if !self.gate.using_simple_floor_planner || self.seen.remove(&offset) {
                self.cells_to_lookup.push(acell);
            } else if self.gate.using_simple_floor_planner {
                self.seen.insert(offset);
            }
        }
        Ok(())
    }

    // returns the limbs
    fn range_check_simple(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = (range_bits + self.config.lookup_bits - 1) / self.config.lookup_bits;
        // println!("range check {} bits {} len", range_bits, k);
        let rem_bits = range_bits % self.config.lookup_bits;

        let limbs = decompose_option(&a.value().map(|x| *x), k, self.config.lookup_bits);
        let limb_base = F::from(1u64 << self.config.lookup_bits);

        layouter.assign_region(
            || format!("range check {} bits", range_bits),
            |mut region| {
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
                            let mult_val = biguint_to_fe(
                                &(BigUint::from(1u64) << (self.config.lookup_bits - rem_bits)),
                            );
                            cells.push(Constant(F::from(0)));
                            cells.push(Witness(limbs[k - 1]));
                            cells.push(Constant(mult_val));
                            cells.push(Witness(
                                Some(mult_val).zip(limbs[k - 1]).map(|(m, l)| m * l),
                            ));
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
                    cells,
                    enable_gates,
                    eq_list,
                    vec![(a, 3 * (k - 1))],
                    0,
                    &mut region,
                )?;
                for row in enable_lookups {
                    self.enable_lookup(&mut region, assigned_cells[row].clone(), row)?;
                }

                let mut assigned_limbs = Vec::with_capacity(k);
                assigned_limbs.push(assigned_cells[0].clone());
                for idx in 1..k {
                    assigned_limbs.push(assigned_cells[3 * idx - 1].clone());
                }
                Ok(assigned_limbs)
            },
        )
    }

    // returns the limbs
    fn range_check_custom_vertical_short(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = (range_bits + self.config.lookup_bits - 1) / self.config.lookup_bits;
        let limbs = decompose_option(&a.value().map(|x| *x), k, self.config.lookup_bits);
        let rem_bits = range_bits % self.config.lookup_bits;

        const MAX_RANGE_POW: usize = 2;
        let k_chunks = (k - 1 + MAX_RANGE_POW - 1) / MAX_RANGE_POW;
        let limb_base = F::from(1 << self.config.lookup_bits);

        // let a = a0 + a1 * X + a2 * X^2 + a3 * X^3 + a4 * X^4 + a5 * X^5 (for example)
        // with X = 2^lookup_bits
        // then take transpose of
        // | a | a0 | x | a1 | a2 | y | a3 | a4 | a5 |
        // and we enable q_range[2,3] on
        // | 2 | 0  | 3 | 0  | 0  | 3 | 0  | 0  | 0  |
        let assigned_limbs = layouter.assign_region(
            || format!("custom range check {} bits", range_bits),
            |mut region| {
                let mut rev_cells = Vec::with_capacity((MAX_RANGE_POW + 1) * k_chunks);
                let mut rev_limb_cells = Vec::with_capacity(k);
                let mut enable_range = Vec::with_capacity(k_chunks);

                let mut start = k - 1;
                rev_cells.push(Witness(limbs[k - 1]));
                rev_limb_cells.push(0);
                let mut running_sum = limbs[k - 1];
                while start > 0 {
                    let len = std::cmp::min(start, MAX_RANGE_POW);
                    start -= len;
                    let window = [&limbs[start..(start + len)], &[running_sum]].concat();
                    running_sum = window.iter().rev().fold(Some(F::from(0)), |acc, &val| {
                        acc.zip(val).map(|(a, v)| a * limb_base + v)
                    });
                    rev_limb_cells.extend((0..len).map(|i| rev_cells.len() + i));
                    rev_cells.extend((0..len).rev().map(|i| Witness(limbs[start + i])));
                    rev_cells.push(Witness(running_sum));
                    enable_range.push((rev_cells.len() - 1, len + 1));
                }
                rev_cells.reverse();
                let cells = rev_cells;

                let (assigned_cells, gate_index) =
                    self.gate.assign_region(cells, vec![], 0, &mut region)?;
                for (rev_row, range_len) in enable_range {
                    self.config.q_range.get(&range_len).unwrap()[gate_index]
                        .enable(&mut region, assigned_cells.len() - 1 - rev_row)?;
                }
                region.constrain_equal(a.cell(), assigned_cells[0].cell())?;
                let assigned_limbs: Vec<AssignedCell<F, F>> = rev_limb_cells
                    .iter()
                    .rev()
                    .enumerate()
                    .map(|(id, &i)| {
                        let offset = assigned_cells.len() - 1 - i;
                        let limb = assigned_cells[offset].clone();
                        if id != 0 || rem_bits != 1 {
                            self.enable_lookup(&mut region, limb.clone(), offset)
                                .expect("enable lookup should not fail");
                        }
                        limb
                    })
                    .collect();
                assert_eq!(assigned_limbs.len(), k);
                Ok(assigned_limbs)
            },
        )?;
        if rem_bits != 0 {
            layouter.assign_region(
                || format!("extra range constraints {} bits", range_bits),
                |mut region| {
                    if rem_bits == 1 {
                        // we want to check x := assigned_limbs[k-1] is boolean
                        // we constrain x*(x-1) = 0 + x * x - x == 0
                        // | 0 | x | x | x |
                        self.gate.assign_region_smart(
                            vec![
                                Constant(F::from(0)),
                                Existing(&assigned_limbs[k - 1]),
                                Existing(&assigned_limbs[k - 1]),
                                Existing(&assigned_limbs[k - 1]),
                            ],
                            vec![0],
                            vec![],
                            vec![],
                            0,
                            &mut region,
                        )?;
                    } else {
                        let mult_val = biguint_to_fe(
                            &(BigUint::from(1u64) << (self.config.lookup_bits - rem_bits)),
                        );
                        let extra_cells = self.gate.assign_region_smart(
                            vec![
                                Constant(F::from(0)),
                                Existing(&assigned_limbs[k - 1]),
                                Constant(mult_val),
                                Witness(Some(mult_val).zip(limbs[k - 1]).map(|(m, l)| m * l)),
                            ],
                            vec![0],
                            vec![],
                            vec![],
                            0,
                            &mut region,
                        )?;
                        self.enable_lookup(&mut region, extra_cells.last().unwrap().clone(), 3)?;
                    }
                    Ok(())
                },
            )?;
        }

        Ok(assigned_limbs)
    }
}

impl<F: FieldExt> RangeInstructions<F> for RangeChip<F> {
    type GateChip = FlexGateChip<F>;

    fn gate(&mut self) -> &mut Self::GateChip {
        &mut self.gate
    }

    fn lookup_bits(&self) -> usize {
        self.config.lookup_bits
    }

    // returns the limbs
    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        assert_ne!(range_bits, 0);
        match self.config.strategy {
            RangeStrategy::Vertical => self.range_check_simple(layouter, a, range_bits),
            RangeStrategy::CustomVerticalShort => {
                self.range_check_custom_vertical_short(layouter, a, range_bits)
            }
        }
    }

    // Warning: This may fail silently if a or b have more than num_bits
    // | a + 2^(num_bits) - b | b | 1 | a + 2^(num_bits) | - 2^(num_bits) | 1 | a |
    fn check_less_than(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error> {
        let shifted_val = layouter.assign_region(
            || format!("check_less_than {} bits", num_bits),
            |mut region| {
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
                    Constant(bigint_to_fe::<F>(
                        &(BigInt::from(-1i64) * (BigInt::from(1u64) << num_bits)),
                    )),
                    Constant(F::from(1)),
                    Existing(&a),
                ];
                let assigned_cells = self.gate.assign_region_smart(
                    cells,
                    vec![0, 3],
                    vec![],
                    vec![],
                    0,
                    &mut region,
                )?;
                Ok(assigned_cells[0].clone())
            },
        )?;

        self.range_check(layouter, &shifted_val, num_bits)?;
        Ok(())
    }

    fn is_less_than(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let k = (num_bits + self.config.lookup_bits - 1) / self.config.lookup_bits;
        let padded_bits = k * self.config.lookup_bits;

        layouter.assign_region(
            || format!("is_less_than {} bit bound", num_bits),
            |mut region| {
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
                let mask = BigUint::from(1u64 << self.config.lookup_bits);
                let mut limb = shift_val.as_ref().map(|x| x.modpow(&BigUint::from(1u64), &mask));
                cells.push(Witness(limb.as_ref().map(|x| biguint_to_fe(x))));

                let mut offset = 9;
                let mut running_sum = limb;
                for idx in 1..(k + 1) {
                    shift_val = shift_val.map(|x| x >> self.config.lookup_bits);
                    limb = shift_val.as_ref().map(|x| x.modpow(&BigUint::from(1u64), &mask));
                    running_sum = running_sum
                        .zip(limb.as_ref())
                        .map(|(sum, x)| sum + (x << (idx * self.config.lookup_bits)));
                    let running_pow =
                        biguint_to_fe(&(BigUint::from(1u64) << (idx * self.config.lookup_bits)));
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

                let assigned_cells = self.gate.assign_region_smart(
                    cells,
                    enable_gates,
                    eq_list,
                    vec![],
                    0,
                    &mut region,
                )?;
                for row in enable_lookups {
                    self.enable_lookup(&mut region, assigned_cells[row].clone(), row)?;
                }
                Ok(assigned_cells[9 + 3 * k].clone())
            },
        )
    }

    // | out | a | inv | 1 | 0 | a | out | 0
    fn is_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero =
            a.value().map(|x| if (*x).is_zero_vartime() { F::from(1) } else { F::from(0) });
        let inv =
            a.value().map(|x| if *x == F::from(0) { F::from(1) } else { (*x).invert().unwrap() });

        layouter.assign_region(
            || "is_equal",
            |mut region| {
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
                let assigned_cells = self.gate.assign_region_smart(
                    cells,
                    vec![0, 4],
                    vec![(0, 6)],
                    vec![],
                    0,
                    &mut region,
                )?;
                Ok(assigned_cells[0].clone())
            },
        )
    }

    fn is_equal(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let diff = layouter.assign_region(
            || "is_equal",
            |mut region| {
                let cells = vec![
                    Witness(a.value().zip(b.value()).map(|(av, bv)| *av - *bv)),
                    Constant(F::from(1)),
                    Existing(&b),
                    Existing(&a),
                ];
                let assigned_cells = self.gate.assign_region_smart(
                    cells,
                    vec![0],
                    vec![],
                    vec![],
                    0,
                    &mut region,
                )?;
                Ok(assigned_cells[0].clone())
            },
        )?;
        self.is_zero(layouter, &diff)
    }

    // returns little-endian bit vectors
    fn num_to_bits(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let bits = decompose_biguint_option(&a.value().map(|x| *x), range_bits, 1usize);
        let bit_cells = layouter.assign_region(
            || "range check",
            |mut region| {
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
                    cells,
                    enable_gates,
                    vec![],
                    vec![(a, last_idx)],
                    0,
                    &mut region,
                )?;

                let mut assigned_bits = Vec::with_capacity(range_bits);
                assigned_bits.push(assigned_cells[0].clone());
                for idx in 1..range_bits {
                    assigned_bits.push(assigned_cells[3 * idx - 1].clone());
                }
                Ok(assigned_bits)
            },
        )?;

        for idx in 0..range_bits {
            layouter.assign_region(
                || "bit check",
                |mut region| {
                    let cells = vec![
                        Constant(F::from(0)),
                        Existing(&bit_cells[idx]),
                        Existing(&bit_cells[idx]),
                        Existing(&bit_cells[idx]),
                    ];
                    self.gate.assign_region_smart(
                        cells,
                        vec![0],
                        vec![],
                        vec![],
                        0,
                        &mut region,
                    )?;
                    Ok(())
                },
            )?;
        }
        Ok(bit_cells)
    }
}
