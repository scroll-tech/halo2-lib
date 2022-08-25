use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{layouter, AssignedCell, Cell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use num_bigint::BigUint;
use num_traits::Num;
use std::{
    cell,
    collections::{HashMap, HashSet},
    marker::PhantomData,
};

use crate::utils::fe_to_biguint;

use super::{
    GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};

// Gate to perform `a + b * c - out = 0`
// We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate
#[derive(Clone, Copy, Debug)]
pub struct GateConfig<F: FieldExt> {
    pub q_enable: Selector,
    // one column to store the inputs and outputs of the gate
    pub value: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> GateConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let value = meta.advice_column();
        meta.enable_equality(value);
        let config = Self { q_enable: meta.selector(), value, _marker: PhantomData };
        config.create_gate(meta);

        config
    }
    fn create_gate(&self, meta: &mut ConstraintSystem<F>) {
        meta.create_gate("1 column a * b + c = out", |meta| {
            let q = meta.query_selector(self.q_enable);
            let a = meta.query_advice(self.value, Rotation::cur());
            let b = meta.query_advice(self.value, Rotation::next());
            let c = meta.query_advice(self.value, Rotation(2));
            let out = meta.query_advice(self.value, Rotation(3));

            vec![q * (a + b * c - out)]
        })
    }
}

#[derive(Clone, Debug)]
pub struct FlexGateConfig<F: FieldExt> {
    pub gates: Vec<GateConfig<F>>,
    // `constants` is a vector of fixed columns for allocating constant values
    pub constants: Vec<Column<Fixed>>,
}

impl<F: FieldExt> FlexGateConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, num_advice: usize, num_fixed: usize) -> Self {
        let mut gates = Vec::with_capacity(num_advice);
        for _i in 0..num_advice {
            let gate = GateConfig::configure(meta);
            gates.push(gate);
        }
        let mut constants = Vec::with_capacity(num_fixed);
        for _i in 0..num_fixed {
            let c = meta.fixed_column();
            meta.enable_equality(c);
            // meta.enable_constant(c);
            constants.push(c);
        }
        Self { gates, constants }
    }
}

// The reason we have a `FlexGateChip` is that we will need to mutably borrow `advice_rows` to update row count
// The `Circuit` trait takes in `Config` as an input that is NOT mutable, so we must make the distinction between immutable Config and mutable Chip
// We will then pass the `Chip` around everywhere for function calls
#[derive(Clone, Debug)]
pub struct FlexGateChip<F: FieldExt> {
    pub config: FlexGateConfig<F>,
    // `advice_rows[i]` keeps track of the number of rows used in the advice column `config.gates[i].value`
    pub advice_rows: Vec<u64>,
    // `constants_to_assign` is a vector keeping track of all constants that we use throughout
    // we load them all in one go using fn `load_constants`
    // if we have (c, Some(cell)) in the vector then we also constrain the loaded cell for `c` to equal `cell`
    pub constants_to_assign: Vec<(F, Option<Cell>)>,

    // SimpleFloorPlanner calls the assignments in `layerouter.assign_region` twice:
    // https://github.com/privacy-scaling-explorations/halo2/blob/f586922d19c3c96ffcec4adbe1790132565ffba6/halo2_proofs/src/circuit/floor_planner/single_pass.rs#L91
    // The following is a hack to get around this for row counting purposes
    pub using_simple_floor_planner: bool,
    pub first_pass: bool,
    // first_pass is HashSet for (column_index, advice_rows[column_index])
    pub seen: HashSet<(usize, u64)>,
}

impl<F: FieldExt> FlexGateChip<F> {
    /// returns leftmost `i` where `advice_rows[i]` is minimum amongst all `advice_rows`
    fn min_gate_index(&self) -> usize {
        self.advice_rows
            .iter()
            .enumerate()
            .min_by(|(_, x), (_, y)| x.cmp(y))
            .map(|(i, _)| i)
            .unwrap()
    }

    /// call this at the very end of synthesize!
    pub fn assign_and_constrain_constants(
        &mut self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<usize, Error> {
        // load constants cyclically over NUM_FIXED columns
        let mut assigned: HashMap<BigUint, AssignedCell<F, F>> = HashMap::new();
        let mut col = 0;
        let mut offset = 0;
        layouter.assign_region(
            || "load constants",
            |mut region| {
                if self.using_simple_floor_planner && self.first_pass {
                    self.first_pass = false;
                    return Ok(0);
                }
                for (c, ocell) in &self.constants_to_assign {
                    let c_big = fe_to_biguint(c);
                    let c_cell = if let Some(c_cell) = assigned.get(&c_big) {
                        c_cell.clone()
                    } else {
                        let c_cell = region.assign_fixed(
                            || "load constant",
                            self.config.constants[col],
                            offset,
                            || Ok(c.clone()),
                        )?;
                        assigned.insert(c_big, c_cell.clone());
                        col += 1;
                        if col == self.config.constants.len() {
                            col = 0;
                            offset += 1;
                        }
                        c_cell
                    };
                    if let Some(cell) = ocell {
                        region.constrain_equal(c_cell.cell(), cell.clone())?;
                    }
                }
                Ok(offset + 1)
            },
        )
    }

    pub fn construct(config: FlexGateConfig<F>, using_simple_floor_planner: bool) -> Self {
        let num_advice = config.gates.len();
        Self {
            config,
            advice_rows: vec![0u64; num_advice],
            constants_to_assign: Vec::new(),
            using_simple_floor_planner,
            first_pass: true,
            seen: HashSet::new(),
        }
    }
}

impl<F: FieldExt> GateInstructions<F> for FlexGateChip<F> {
    // The "contract" is that in any region you should only call `self.assign_region`
    // once if using `SimpleFloorPlanner`. Otherwise the column allocation may break
    fn assign_region(
        &mut self,
        inputs: Vec<QuantumCell<F>>,
        offset: usize,
        region: &mut Region<'_, F>,
    ) -> Result<(Vec<AssignedCell<F, F>>, usize), Error> {
        let gate_index = self.min_gate_index();

        let mut assigned_cells = Vec::with_capacity(inputs.len());
        for (i, input) in inputs.iter().enumerate() {
            let assigned_cell = match *input {
                QuantumCell::Existing(acell) => acell.copy_advice(
                    || "gate: copy advice",
                    region,
                    self.config.gates[gate_index].value,
                    offset + i,
                ),
                QuantumCell::Witness(val) => region.assign_advice(
                    || "gate: assign advice",
                    self.config.gates[gate_index].value,
                    offset + i,
                    || val.ok_or(Error::Synthesis),
                ),
                QuantumCell::Constant(c) => {
                    let acell = region.assign_advice(
                        || "gate: assign const",
                        self.config.gates[gate_index].value,
                        offset + i,
                        || Ok(c),
                    )?;
                    // add to list of constants to assign at the end ONLY if this is the last pass of the layouter
                    if !self.using_simple_floor_planner
                        || self.seen.contains(&(gate_index, self.advice_rows[gate_index]))
                    {
                        self.constants_to_assign.push((c, Some(acell.cell())));
                    }
                    Ok(acell)
                }
            }?;
            assigned_cells.push(assigned_cell);
        }
        if !self.using_simple_floor_planner
            || self.seen.remove(&(gate_index, self.advice_rows[gate_index]))
        {
            self.advice_rows[gate_index] += inputs.len() as u64;
        } else if self.using_simple_floor_planner {
            self.seen.insert((gate_index, self.advice_rows[gate_index]));
        }

        Ok((assigned_cells, gate_index))
    }

    fn enable(
        &self,
        region: &mut Region<'_, F>,
        gate_index: usize,
        offset: usize,
    ) -> Result<(), Error> {
        self.config.gates[gate_index].q_enable.enable(region, offset)
    }

    // Layouter creates new region that copies a, b and constrains `a + b * 1 = out`
    // | a | b | 1 | a + b |
    fn add(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native add",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    a.clone(),
                    b.clone(),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) + (*bv))),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `a + b * (-1) = out`
    // Requires config to have a fixed column with `enable_constants` on
    // | a | b | -1 | a - b |
    fn sub(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native sub",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    a.clone(),
                    b.clone(),
                    QuantumCell::Constant(-F::from(1)),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // | 0 | a | -1 | -a |
    fn neg(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native sub",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    a.clone(),
                    QuantumCell::Constant(-F::from(1)),
                    QuantumCell::Witness(a.value().map(|av| -(*av))),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `0 + a * b = out`
    // | 0 | a | b | a * b |
    fn mul(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native mul",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    a.clone(),
                    b.clone(),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter takes two vectors of `QuantumCell` and constrains a witness output to the inner product of `<vec_a, vec_b>`
    fn inner_product(
        &mut self,
        layouter: &mut impl Layouter<F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<(Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>, AssignedCell<F, F>), Error> {
        assert_eq!(vec_a.len(), vec_b.len());
        // don't try to call this function with empty inputs!
        if vec_a.len() == 0 {
            return Err(Error::Synthesis);
        }
        layouter.assign_region(
            || "inner product",
            |mut region| {
                let mut cells: Vec<QuantumCell<F>> = Vec::with_capacity(3 * vec_a.len() + 1);
                cells.push(QuantumCell::Constant(F::from(0)));

                let mut sum = Some(F::zero());
                for (a, b) in vec_a.iter().zip(vec_b.iter()) {
                    sum = sum.zip(a.value()).zip(b.value()).map(|((sum, a), b)| sum + *a * *b);

                    cells.push(a.clone());
                    cells.push(b.clone());
                    cells.push(QuantumCell::Witness(sum));
                }
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                let mut a_assigned = Vec::with_capacity(vec_a.len());
                let mut b_assigned = Vec::with_capacity(vec_a.len());
                for i in 0..vec_a.len() {
                    self.enable(&mut region, col_index, 3 * i)?;
                    a_assigned.push(assigned_cells[3 * i + 1].clone());
                    b_assigned.push(assigned_cells[3 * i + 1].clone());
                }

                Ok((a_assigned, b_assigned, assigned_cells.last().unwrap().clone()))
            },
        )
    }

    // | 1 - b | 1 | b | 1 | b | a | 1 - b | out |
    fn or(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "or",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Witness(b.value().map(|x| F::from(1) - *x)),
                    QuantumCell::Constant(F::from(1)),
                    b.clone(),
                    QuantumCell::Constant(F::from(1)),
                    b.clone(),
                    a.clone(),
                    QuantumCell::Witness(b.value().map(|x| F::from(1) - *x)),
                    QuantumCell::Witness(
                        a.value().zip(b.value()).map(|(av, bv)| *av + *bv - (*av) * (*bv)),
                    ),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                self.enable(&mut region, col_index, 4)?;

                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[6].cell())?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // | 0 | a | b | out |
    fn and(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "and",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    a.clone(),
                    b.clone(),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // assumes sel is boolean
    // | a - b | 1 | b | a |
    // | b | sel | a - b | out |
    // returns
    //   a * sel + b * (1 - sel)
    fn select(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        sel: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "sel",
            |mut region| {
                let cells = vec![
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                    QuantumCell::Constant(F::from(1)),
                    b.clone(),
                    a.clone(),
                    b.clone(),
                    sel.clone(),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                    QuantumCell::Witness(
                        a.value()
                            .zip(b.value())
                            .zip(sel.value())
                            .map(|((av, bv), sv)| (*av) * (*sv) + (*bv) * (F::from(1) - *sv)),
                    ),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                self.enable(&mut region, col_index, 4)?;
                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[6].cell())?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // returns: a || (b && c)
    // | 1 - b c | b | c | 1 | a - 1 | 1 - b c | out | a - 1 | 1 | 1 | a |
    fn or_and(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        c: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "or_and",
            |mut region| {
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Witness(
                        b.value().zip(c.value()).map(|(bv, cv)| F::from(1) - (*bv) * (*cv)),
                    ),
                    b.clone(),
                    c.clone(),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Witness(a.value().map(|x| *x - F::from(1))),
                    QuantumCell::Witness(
                        b.value().zip(c.value()).map(|(bv, cv)| F::from(1) - (*bv) * (*cv)),
                    ),
                    QuantumCell::Witness(
                        a.value()
                            .zip(b.value())
                            .zip(c.value())
                            .map(|((av, bv), cv)| *av + (*bv) * (*cv) - (*av) * (*bv) * (*cv)),
                    ),
                    QuantumCell::Witness(a.value().map(|x| *x - F::from(1))),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Constant(F::from(1)),
                    a.clone(),
                ];
                let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                self.enable(&mut region, col_index, 0)?;
                self.enable(&mut region, col_index, 3)?;
                self.enable(&mut region, col_index, 7)?;

                region.constrain_equal(assigned_cells[4].cell(), assigned_cells[7].cell())?;
                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[5].cell())?;
                Ok(assigned_cells[6].clone())
            },
        )
    }

    // assume bits has boolean values
    // returns vec[idx] with vec[idx] = 1 if and only if bits == idx as a binary number
    fn bits_to_indicator(
        &mut self,
        layouter: &mut impl Layouter<F>,
        bits: &Vec<QuantumCell<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = bits.len();

        let mut inv_bits = Vec::with_capacity(k);
        let mut assigned_bits = Vec::with_capacity(k);
        for idx in 0..k {
            let (inv_bit, bit) = layouter.assign_region(
                || "inv_bits",
                |mut region| {
                    let cells = vec![
                        QuantumCell::Witness(bits[idx].value().map(|x| F::from(1) - x)),
                        bits[idx].clone(),
                        QuantumCell::Constant(F::from(1)),
                        QuantumCell::Constant(F::from(1)),
                    ];
                    let (assigned_cells, col_index) = self.assign_region(cells, 0, &mut region)?;
                    self.enable(&mut region, col_index, 0)?;
                    Ok((assigned_cells[0].clone(), assigned_cells[1].clone()))
                },
            )?;
            inv_bits.push(inv_bit.clone());
            assigned_bits.push(bit.clone());
        }

        let mut indicator = Vec::with_capacity(2 * (1 << k) - 2);
        let mut offset = 0;
        indicator.push(inv_bits[k - 1].clone());
        indicator.push(assigned_bits[k - 1].clone());
        for idx in 1..k {
            for old_idx in 0..(1 << idx) {
                let inv_prod = self.mul(
                    layouter,
                    &QuantumCell::Existing(&indicator[offset + old_idx]),
                    &QuantumCell::Existing(&inv_bits[k - 1 - idx]),
                )?;
                indicator.push(inv_prod);

                let prod = self.mul(
                    layouter,
                    &QuantumCell::Existing(&indicator[offset + old_idx]),
                    &QuantumCell::Existing(&assigned_bits[k - 1 - idx]),
                )?;
                indicator.push(prod);
            }
            offset = offset + (1 << idx);
        }
        Ok(indicator[2 * (1 << k) - 2 - (1 << k)..].to_vec())
    }
}
