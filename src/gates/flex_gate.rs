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
    Context, GateInstructions,
    QuantumCell::{self, Constant, Existing, Witness},
};

#[derive(Clone, Debug, PartialEq)]
pub enum GateStrategy {
    Vertical,
}

// Gate to perform `a + b * c - out = 0`
// We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate
#[derive(Clone, Copy, Debug)]
pub struct BasicGateConfig<F: FieldExt> {
    pub q_enable: Selector,
    // one column to store the inputs and outputs of the gate
    pub value: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BasicGateConfig<F> {
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
    pub basic_gates: Vec<BasicGateConfig<F>>,
    // `constants` is a vector of fixed columns for allocating constant values
    pub constants: Vec<Column<Fixed>>,
    pub num_advice: usize,
    strategy: GateStrategy,
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
            GateStrategy::Vertical => {
                let mut basic_gates = Vec::with_capacity(num_advice);
                for _i in 0..num_advice {
                    let gate = BasicGateConfig::configure(meta);
                    basic_gates.push(gate);
                }
                Self { basic_gates, constants, num_advice, strategy }
            }
        }
    }
}

impl<F: FieldExt> FlexGateConfig<F> {
    /// call this at the very end of synthesize!
    /// allocates constants to fixed columns
    /// returns (max rows used by a fixed column, total number of constants assigned)
    pub fn finalize(&self, ctx: &mut Context<'_, F>) -> Result<(usize, usize), Error> {
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
            QuantumCell::Witness(val) => ctx.region.assign_advice(
                || "gate: assign advice",
                column,
                offset,
                || val.ok_or(Error::Synthesis),
            ),
            QuantumCell::Constant(c) => {
                let acell =
                    ctx.region.assign_advice(|| "gate: assign const", column, offset, || Ok(c))?;
                ctx.constants_to_assign.push((c, Some(acell.cell())));
                Ok(acell)
            }
        }
    }
}

impl<F: FieldExt> GateInstructions<F> for FlexGateConfig<F> {
    /// Only call this if ctx.region is not in shape mode, i.e., if not using simple layouter or ctx.first_pass = false
    ///
    /// All indices in `gate_offsets` are with respect to `inputs` indices
    /// - `gate_offsets` specifies indices to enable selector for the gate
    fn assign_region(
        &self,
        ctx: &mut Context<'_, F>,
        inputs: Vec<QuantumCell<F>>,
        gate_offsets: Vec<usize>,
        // offset: usize, // It's useless to have an offset here since the function auto-selects what column to put stuff into
    ) -> Result<(Vec<AssignedCell<F, F>>, usize), Error> {
        assert!(self.strategy == GateStrategy::Vertical);

        let gate_index = ctx.min_gate_index();

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
        for gate_relative_offset in gate_offsets {
            self.basic_gates[gate_index]
                .q_enable
                .enable(&mut ctx.region, ctx.advice_rows[gate_index] + gate_relative_offset)?;
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
            GateStrategy::Vertical => {
                self.assign_region(ctx, inputs, gate_offsets)
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
    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<(Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>, AssignedCell<F, F>), Error> {
        assert_eq!(vec_a.len(), vec_b.len());
        // don't try to call this function with empty inputs!
        if vec_a.len() == 0 {
            return Err(Error::Synthesis);
        }
        let mut cells: Vec<QuantumCell<F>> = Vec::with_capacity(3 * vec_a.len() + 1);
        cells.push(QuantumCell::Constant(F::from(0)));

        let mut sum = Some(F::zero());
        for (a, b) in vec_a.iter().zip(vec_b.iter()) {
            sum = sum.zip(a.value()).zip(b.value()).map(|((sum, a), b)| sum + *a * *b);

            cells.push(a.clone());
            cells.push(b.clone());
            cells.push(QuantumCell::Witness(sum));
        }
        let mut gate_offsets = Vec::with_capacity(vec_a.len());
        for i in 0..vec_a.len() {
            gate_offsets.push(3 * i);
        }
        let assigned_cells = self.assign_region_smart(ctx, cells, gate_offsets, vec![], vec![])?;
        let mut a_assigned = Vec::with_capacity(vec_a.len());
        let mut b_assigned = Vec::with_capacity(vec_a.len());
        for i in 0..vec_a.len() {
            a_assigned.push(assigned_cells[3 * i + 1].clone());
            b_assigned.push(assigned_cells[3 * i + 1].clone());
        }

        Ok((a_assigned, b_assigned, assigned_cells.last().unwrap().clone()))
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
