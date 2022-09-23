use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{layouter, AssignedCell, Cell, Layouter, Region, Value},
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
    Context, GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum GateStrategy {
    Vertical,
    PlonkPlus,
}

#[derive(Clone, Debug)]
pub struct BasicGateConfig<F: FieldExt> {
    // `q_enable` will have either length 1 or 2, depending on the strategy

    // If strategy is Vertical, then this is the basic vertical gate
    // `q_0 * (a + b * c - d) = 0`
    // where
    // * a = value[0], b = value[1], c = value[2], d = value[3]
    // * q = q_enable[0]
    // * q_i is either 0 or 1 so this is just a simple selector
    // We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate

    // If strategy is PlonkPlus, then this is a slightly extended version of the vanilla plonk (vertical) gate
    // `q_io * (a + q_left * b + q_right * c + q_mul * b * c - d)`
    // where
    // * a = value[0], b = value[1], c = value[2], d = value[3]
    // * the q_{} can be any fixed values in F, placed in two fixed columns
    // * it is crucial that q_io goes in its own selector column! we need it to be 0, 1 to turn on/off the gate
    pub q_enable: Vec<Column<Fixed>>,
    // one column to store the inputs and outputs of the gate
    pub value: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BasicGateConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, strategy: GateStrategy) -> Self {
        let value = meta.advice_column();
        meta.enable_equality(value);
        let q = meta.fixed_column();

        match strategy {
            GateStrategy::Vertical => {
                let config = Self { q_enable: vec![q], value, _marker: PhantomData };
                config.create_gate(meta);
                config
            }
            GateStrategy::PlonkPlus => {
                let q_aux = meta.fixed_column();
                let config = Self { q_enable: vec![q, q_aux], value, _marker: PhantomData };
                config.create_plonk_gate(meta);
                config
            }
        }
    }

    fn create_gate(&self, meta: &mut ConstraintSystem<F>) {
        assert_eq!(self.q_enable.len(), 1);
        meta.create_gate("1 column a * b + c = out", |meta| {
            let q = meta.query_fixed(self.q_enable[0], Rotation::cur());

            let a = meta.query_advice(self.value, Rotation::cur());
            let b = meta.query_advice(self.value, Rotation::next());
            let c = meta.query_advice(self.value, Rotation(2));
            let out = meta.query_advice(self.value, Rotation(3));

            vec![q * (a + b * c - out)]
        })
    }

    fn create_plonk_gate(&self, meta: &mut ConstraintSystem<F>) {
        assert_eq!(self.q_enable.len(), 2);
        meta.create_gate("plonk plus", |meta| {
            // q_io * (a + q_left * b + q_right * c + q_mul * b * c - d)
            // the gate is turned "off" as long as q_in = q_out = 0
            let q_io = meta.query_fixed(self.q_enable[0], Rotation::cur());

            let q_mul = meta.query_fixed(self.q_enable[1], Rotation::cur());
            let q_left = meta.query_fixed(self.q_enable[1], Rotation::next());
            let q_right = meta.query_fixed(self.q_enable[1], Rotation(2));

            let a = meta.query_advice(self.value, Rotation::cur());
            let b = meta.query_advice(self.value, Rotation::next());
            let c = meta.query_advice(self.value, Rotation(2));
            let d = meta.query_advice(self.value, Rotation(3));

            vec![q_io * (a + q_left * b.clone() + q_right * c.clone() + q_mul * b * c - d)]
        })
    }
}

#[derive(Clone, Debug)]
pub struct FlexGateConfig<F: FieldExt> {
    pub basic_gates: Vec<BasicGateConfig<F>>,
    // `constants` is a vector of fixed columns for allocating constant values
    pub constants: Vec<Column<Fixed>>,
    pub num_advice: usize,
    strategy: GateStrategy,
    gate_len: usize,
}

impl<F: FieldExt> FlexGateConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        strategy: GateStrategy,
        num_advice: usize,
        num_fixed: usize,
    ) -> Self {
        let mut constants = Vec::with_capacity(num_fixed);
        for _i in 0..num_fixed {
            let c = meta.fixed_column();
            meta.enable_equality(c);
            // meta.enable_constant(c);
            constants.push(c);
        }
        match strategy {
            GateStrategy::Vertical | GateStrategy::PlonkPlus => {
                let mut basic_gates = Vec::with_capacity(num_advice);
                for _i in 0..num_advice {
                    let gate = BasicGateConfig::configure(meta, strategy);
                    basic_gates.push(gate);
                }
                Self { basic_gates, constants, num_advice, strategy, gate_len: 4 }
            }
        }
    }
}

impl<F: FieldExt> FlexGateConfig<F> {
    /// call this at the very end of synthesize!
    /// allocates constants to fixed columns
    /// returns (max rows used by a fixed column, total number of constants assigned)
    pub fn finalize(&self, ctx: &mut Context<'_, F>) -> Result<(usize, usize), Error> {
        #[cfg(feature = "display")]
        println!("{:#?}", ctx.op_count);

        ctx.assign_and_constrain_constants(&self.constants)
    }

    /// Assuming that this is only called if ctx.region is not in shape mode!
    pub fn assign_cell(
        &self,
        ctx: &mut Context<'_, F>,
        input: QuantumCell<F>,
        column: Column<Advice>,
        offset: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        match input {
            QuantumCell::Existing(acell) => {
                acell.copy_advice(|| "gate: copy advice", &mut ctx.region, column, offset)
            }
            QuantumCell::Witness(val) => {
                ctx.region.assign_advice(|| "gate: assign advice", column, offset, || val)
            }
            QuantumCell::Constant(c) => {
                let acell = ctx.region.assign_advice(
                    || "gate: assign const",
                    column,
                    offset,
                    || Value::known(c),
                )?;
                ctx.constants_to_assign.push((c, Some(acell.cell())));
                Ok(acell)
            }
        }
    }
}

impl<F: FieldExt> GateInstructions<F> for FlexGateConfig<F> {
    fn strategy(&self) -> GateStrategy {
        self.strategy
    }
    /// All indices in `gate_offsets` are with respect to `inputs` indices
    /// * `gate_offsets` specifies indices to enable selector for the gate
    /// * `gate_offsets` specifies (index, Option<[q_left, q_right, q_mul, q_const, q_out]>)
    /// * second coordinate should only be set if using strategy PlonkPlus; if not set, default to [1, 0, 0]
    /// * allow the index in `gate_offsets` to be negative in case we want to do advanced overlapping
    /// * gate_index can either be set if you know the specific column you want to assign to, or None if you want to auto-select index
    fn assign_region(
        &self,
        ctx: &mut Context<'_, F>,
        inputs: Vec<QuantumCell<F>>,
        gate_offsets: Vec<(isize, Option<[F; 3]>)>,
        gate_index: Option<usize>,
        // offset: usize, // It's useless to have an offset here since the function auto-selects what column to put stuff into
    ) -> Result<(Vec<AssignedCell<F, F>>, usize), Error> {
        let gate_index = if let Some(id) = gate_index { id } else { ctx.min_gate_index() };

        let mut assigned_cells = Vec::with_capacity(inputs.len());
        for (i, input) in inputs.iter().enumerate() {
            let assigned_cell = self.assign_cell(
                ctx,
                input.clone(),
                self.basic_gates[gate_index].value,
                ctx.advice_rows[gate_index] + i,
            )?;
            assigned_cells.push(assigned_cell);
        }
        for (i, q_coeff) in &gate_offsets {
            ctx.region.assign_fixed(
                || "",
                self.basic_gates[gate_index].q_enable[0],
                ((ctx.advice_rows[gate_index] as isize) + i) as usize,
                || Value::known(F::one()),
            )?;

            if self.strategy == GateStrategy::PlonkPlus {
                let q_coeff = q_coeff.unwrap_or([F::one(), F::zero(), F::zero()]);
                for j in 0..3 {
                    ctx.region.assign_fixed(
                        || "",
                        self.basic_gates[gate_index].q_enable[1],
                        ((ctx.advice_rows[gate_index] as isize) + i) as usize + j,
                        || Value::known(q_coeff[j]),
                    )?;
                }
            }
        }

        ctx.advice_rows[gate_index] += inputs.len();

        Ok((assigned_cells, gate_index))
    }

    /// Only call this if ctx.region is not in shape mode, i.e., if not using simple layouter or ctx.first_pass = false
    ///
    /// All indices in `gate_offsets`, `equality_offsets`, `external_equality` are with respect to `inputs` indices
    /// - `gate_offsets` specifies indices to enable selector for the gate; assume `gate_offsets` is sorted in increasing order
    /// - `equality_offsets` specifies pairs of indices to constrain equality
    /// - `external_equality` specifies an existing cell to constrain equality with the cell at a certain index
    fn assign_region_smart(
        &self,
        ctx: &mut Context<'_, F>,
        inputs: Vec<QuantumCell<F>>,
        gate_offsets: Vec<usize>,
        equality_offsets: Vec<(usize, usize)>,
        external_equality: Vec<(&AssignedCell<F, F>, usize)>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let assigned_cells = match self.strategy {
            GateStrategy::Vertical | GateStrategy::PlonkPlus => {
                self.assign_region(
                    ctx,
                    inputs,
                    gate_offsets.iter().map(|i| (*i as isize, None)).collect(),
                    None,
                )
                .expect("assign region should not fail")
                .0
            }
        };

        for (offset1, offset2) in equality_offsets {
            ctx.region.constrain_equal(
                assigned_cells[offset1].clone().cell(),
                assigned_cells[offset2].clone().cell(),
            )?;
        }
        for (assigned_cell, eq_offset) in external_equality {
            ctx.region
                .constrain_equal(assigned_cell.cell(), assigned_cells[eq_offset].clone().cell())?;
        }
        Ok(assigned_cells)
    }

    fn load_zero(&self, ctx: &mut Context<'_, F>) -> Result<AssignedCell<F, F>, Error> {
        if let Some(zcell) = &ctx.zero_cell {
            return Ok(zcell.clone());
        }
        let zero_cells =
            self.assign_region_smart(ctx, vec![Constant(F::from(0))], vec![], vec![], vec![])?;
        ctx.zero_cell = Some(zero_cells[0].clone());
        Ok(zero_cells[0].clone())
    }

    /// Copies a, b and constrains `a + b * 1 = out`
    // | a | b | 1 | a + b |
    fn add(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells: Vec<QuantumCell<F>> = vec![
            a.clone(),
            b.clone(),
            QuantumCell::Constant(F::from(1)),
            QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) + (*bv))),
        ];
        let assigned_cells = self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    /// Copies a, b and constrains `a + b * (-1) = out`
    // | a | b | -1 | a - b |
    fn sub(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells: Vec<QuantumCell<F>> = vec![
            a.clone(),
            b.clone(),
            QuantumCell::Constant(-F::from(1)),
            QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
        ];
        let assigned_cells = self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    // | 0 | a | -1 | -a |
    fn neg(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells: Vec<QuantumCell<F>> = vec![
            QuantumCell::Constant(F::from(0)),
            a.clone(),
            QuantumCell::Constant(-F::from(1)),
            QuantumCell::Witness(a.value().map(|av| -(*av))),
        ];
        let assigned_cells = self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    /// Copies a, b and constrains `0 + a * b = out`
    // | 0 | a | b | a * b |
    fn mul(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells: Vec<QuantumCell<F>> = vec![
            QuantumCell::Constant(F::from(0)),
            a.clone(),
            b.clone(),
            QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
        ];
        let assigned_cells = self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    // Takes two vectors of `QuantumCell` and constrains a witness output to the inner product of `<vec_a, vec_b>`
    // outputs are vec<(a_cell, a_relative_index)>, vec<(b_cell, b_relative_index)>, out_cell, gate_index
    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<
        (
            Option<Vec<(AssignedCell<F, F>, usize)>>,
            Option<Vec<(AssignedCell<F, F>, usize)>>,
            AssignedCell<F, F>,
            usize,
        ),
        Error,
    > {
        assert_eq!(vec_a.len(), vec_b.len());
        // don't try to call this function with empty inputs!
        if vec_a.len() == 0 {
            return Err(Error::Synthesis);
        }
        // we will do special handling of the cases where one of the vectors is all constants
        if self.strategy == GateStrategy::PlonkPlus
            && vec_b.iter().all(|b| if let Constant(c) = b { true } else { false })
        {
            let vec_b: Vec<F> = vec_b
                .iter()
                .map(|b| if let Constant(c) = b { *c } else { unreachable!() })
                .collect();
            let k = vec_a.len();
            let gate_segment = self.gate_len - 2;

            // Say a = [a0, .., a4] for example
            // Then to compute <a, b> we use transpose of
            // | 0  | a0 | a1 | x | a2 | a3 | y | a4 | 0 | <a,c> |
            // while letting q_enable equal transpose of
            // | *  |    |    | * |    |    | * |    |   |       |
            // | 0  | b0 | b1 | 0 | b2 | b3 | 0 | b4 | 0 |

            // we effect a small optimization if we know the constant b0 == 1: then instead of starting from 0 we can start from a0
            // this is a peculiarity of our plonk-plus gate
            let start_ida: usize = if vec_b[0] == F::one() { 1 } else { 0 };
            if start_ida == 1 && k == 1 {
                // this is just a0 * 1 = a0; you're doing nothing, why are you calling this function?
                let (assignment, gate_index) =
                    self.assign_region(ctx, vec![vec_a[0].clone()], vec![], None)?;
                return Ok((
                    Some(vec![(assignment[0].clone(), 0)]),
                    None,
                    assignment[0].clone(),
                    gate_index,
                ));
            }
            let k_chunks = (k - start_ida + gate_segment - 1) / gate_segment;
            let mut cells = Vec::with_capacity(1 + (gate_segment + 1) * k_chunks);
            let mut gate_offsets = Vec::with_capacity(k_chunks);
            let mut running_sum =
                if start_ida == 1 { vec_a[0].clone() } else { Constant(F::zero()) };
            cells.push(running_sum.clone());
            for i in 0..k_chunks {
                let window = (start_ida + i * gate_segment)
                    ..std::cmp::min(k, start_ida + (i + 1) * gate_segment);
                // we add a 0 at the start for q_mul = 0
                let mut c_window = [&[F::zero()], &vec_b[window.clone()]].concat();
                c_window.extend((c_window.len()..(gate_segment + 1)).map(|_| F::zero()));
                // c_window should have length gate_segment + 1
                gate_offsets.push((
                    (i * (gate_segment + 1)) as isize,
                    Some(c_window.try_into().expect("q_coeff should be correct len")),
                ));

                cells.extend(window.clone().map(|j| vec_a[j].clone()));
                cells.extend((window.len()..gate_segment).map(|_| Constant(F::from(0))));
                running_sum =
                    Witness(window.into_iter().fold(running_sum.value().copied(), |sum, j| {
                        sum + Value::known(vec_b[j]) * vec_a[j].value()
                    }));
                cells.push(running_sum.clone());
            }

            let (assignments, gate_index) = self.assign_region(ctx, cells, gate_offsets, None)?;
            let mut a_assigned = Vec::with_capacity(k);
            if start_ida == 1 {
                a_assigned.push((assignments[0].clone(), 0));
            }
            for i in start_ida..k {
                let chunk = (i - start_ida) / gate_segment;
                a_assigned.push((
                    assignments[1 + chunk * (gate_segment + 1) + ((i - start_ida) % gate_segment)]
                        .clone(),
                    1 + chunk * (gate_segment + 1) + ((i - start_ida) % gate_segment),
                ))
            }
            return Ok((Some(a_assigned), None, assignments.last().unwrap().clone(), gate_index));
        }

        if self.strategy == GateStrategy::PlonkPlus
            && vec_a.iter().all(|a| if let Constant(c) = a { true } else { false })
        {
            let (b, a, out, id) = self.inner_product(ctx, vec_b, vec_a)?;
            return Ok((a, b, out, id));
        }

        let mut cells: Vec<QuantumCell<F>> = Vec::with_capacity(3 * vec_a.len() + 1);
        cells.push(QuantumCell::Constant(F::from(0)));

        let mut sum = Value::known(F::zero());
        for (a, b) in vec_a.iter().zip(vec_b.iter()) {
            sum = sum + a.value().copied() * b.value();

            cells.push(a.clone());
            cells.push(b.clone());
            cells.push(QuantumCell::Witness(sum));
        }
        let mut gate_offsets = Vec::with_capacity(vec_a.len());
        for i in 0..vec_a.len() {
            gate_offsets.push(3 * i);
        }
        let (assigned_cells, gate_index) = self.assign_region(
            ctx,
            cells,
            gate_offsets.iter().map(|i| (*i as isize, None)).collect(),
            None,
        )?;
        let mut a_assigned = Vec::with_capacity(vec_a.len());
        let mut b_assigned = Vec::with_capacity(vec_a.len());
        for i in 0..vec_a.len() {
            a_assigned.push((assigned_cells[3 * i + 1].clone(), 3 * i + 1));
            b_assigned.push((assigned_cells[3 * i + 2].clone(), 3 * i + 2));
        }

        Ok((Some(a_assigned), Some(b_assigned), assigned_cells.last().unwrap().clone(), gate_index))
    }

    // | 1 - b | 1 | b | 1 | b | a | 1 - b | out |
    fn or(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
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
        let assigned_cells =
            self.assign_region_smart(ctx, cells, vec![0, 4], vec![(0, 6)], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    // | 0 | a | b | out |
    fn and(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let cells: Vec<QuantumCell<F>> = vec![
            QuantumCell::Constant(F::from(0)),
            a.clone(),
            b.clone(),
            QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
        ];
        let assigned_cells = self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    /// assumes sel is boolean
    // | a - b | 1 | b | a |
    // | b | sel | a - b | out |
    /// returns
    ///   a * sel + b * (1 - sel)
    fn select(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        sel: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
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
        let assigned_cells =
            self.assign_region_smart(ctx, cells, vec![0, 4], vec![(0, 6)], vec![])?;
        Ok(assigned_cells.last().unwrap().clone())
    }

    /// returns: a || (b && c)
    // | 1 - b c | b | c | 1 | a - 1 | 1 - b c | out | a - 1 | 1 | 1 | a |
    fn or_and(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        c: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
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
        let assigned_cells =
            self.assign_region_smart(ctx, cells, vec![0, 3, 7], vec![(4, 7), (0, 5)], vec![])?;
        Ok(assigned_cells[6].clone())
    }

    /// assume bits has boolean values
    /// returns vec[idx] with vec[idx] = 1 if and only if bits == idx as a binary number
    fn bits_to_indicator(
        &self,
        ctx: &mut Context<'_, F>,
        bits: &Vec<QuantumCell<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let k = bits.len();

        let mut inv_bits = Vec::with_capacity(k);
        let mut assigned_bits = Vec::with_capacity(k);
        for idx in 0..k {
            let (inv_bit, bit) = {
                let cells = vec![
                    QuantumCell::Witness(bits[idx].value().map(|x| F::from(1) - x)),
                    bits[idx].clone(),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Constant(F::from(1)),
                ];
                let assigned_cells =
                    self.assign_region_smart(ctx, cells, vec![0], vec![], vec![])?;
                (assigned_cells[0].clone(), assigned_cells[1].clone())
            };
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
                    ctx,
                    &QuantumCell::Existing(&indicator[offset + old_idx]),
                    &QuantumCell::Existing(&inv_bits[k - 1 - idx]),
                )?;
                indicator.push(inv_prod);

                let prod = self.mul(
                    ctx,
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
