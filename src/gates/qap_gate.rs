use crate::utils::*;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::BigUint as big_uint;
use num_traits::One;
use std::marker::PhantomData;

pub enum QuantumCell<'a, F: FieldExt> {
    Existing(&'a AssignedCell<F, F>),
    Witness(&'a Option<F>),
    Constant(&'a F),
}

// Gate to perform `a + b * c - out = 0`
// We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate
#[derive(Clone, Debug)]
pub struct Config<F: FieldExt> {
    pub q_enable: Selector,
    // one column to store the inputs and outputs of the gate
    pub value: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Config<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        meta.enable_equality(value);

        let config = Self {
            q_enable: meta.selector(),
            value,
            _marker: PhantomData,
        };

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

    pub fn assign_region(
        &self,
        inputs: Vec<QuantumCell<F>>,
        offset: usize,
        region: &mut Region<'_, F>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let mut assigned_cells = Vec::with_capacity(inputs.len());

        for (i, input) in inputs.iter().enumerate() {
            let assigned_cell = match *input {
                QuantumCell::Existing(acell) => {
                    acell.copy_advice(|| "gate: copy advice", region, self.value, offset + i)
                }
                QuantumCell::Witness(val) => region.assign_advice(
                    || "gate: assign advice",
                    self.value,
                    offset + i,
                    || val.ok_or(Error::Synthesis),
                ),
                QuantumCell::Constant(c) => {
                    let cell = region.assign_advice_from_constant(
                        || "gate: assign const",
                        self.value,
                        offset + i,
                        *c,
                    )?;
                    region.constrain_constant(cell.cell(), c)?;
                    Ok(cell)
                }
            }?;
            assigned_cells.push(assigned_cell);
        }
        Ok(assigned_cells)
    }

    // Layouter creates new region that copies a, b and constrains `a + b * 1 = out`
    // Requires config to have a fixed column with `enable_constants` on
    pub fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native add",
            |mut region| {
                // Enable `q_enable` selector
                self.q_enable.enable(&mut region, 0)?;

                // Copy `a` into `value` column at offset `0`
                a.copy_advice(|| "a", &mut region, self.value, 0)?;

                // Copy `b` into `value` column at offset `1`
                b.copy_advice(|| "b", &mut region, self.value, 1)?;

                // Assign constant `1` into `value` column at offset `2`
                let cell = region.assign_advice_from_constant(|| "1", self.value, 2, F::one())?;
                region.constrain_constant(cell.cell(), F::one())?;

                let a = a.value();
                let b = b.value();
                let out = a.zip(b).map(|(a, b)| *a + *b);
                region.assign_advice(|| "out", self.value, 3, || out.ok_or(Error::Synthesis))
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `a + b * (-1) = out`
    // Requires config to have a fixed column with `enable_constants` on
    pub fn sub(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native sub",
            |mut region| {
                // Enable `q_enable` selector
                self.q_enable.enable(&mut region, 0)?;

                // Copy `a` into `value` column at offset `0`
                a.copy_advice(|| "a", &mut region, self.value, 0)?;

                // Copy `b` into `value` column at offset `1`
                b.copy_advice(|| "b", &mut region, self.value, 1)?;

                // Assign constant `-1` into `value` column at offset `2`
                let minus_1 = -F::from(1);
                let cell = region.assign_advice_from_constant(|| "-1", self.value, 2, minus_1)?;
                region.constrain_constant(cell.cell(), minus_1)?;

                let a = a.value();
                let b = b.value();
                let out = a.zip(b).map(|(a, b)| *a - *b);
                region.assign_advice(|| "out", self.value, 3, || out.ok_or(Error::Synthesis))
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `0 + a * b = out`
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native mul",
            |mut region| {
                // Enable `q_enable` selector
                self.q_enable.enable(&mut region, 0)?;

                // Assign constant `0` into `value` column at offset `0`
                let cell = region.assign_advice_from_constant(|| "0", self.value, 0, F::zero())?;
                region.constrain_constant(cell.cell(), F::zero())?;

                // Copy `a` into `value` column at offset `1`
                a.copy_advice(|| "a", &mut region, self.value, 1)?;

                // Copy `b` into `value` column at offset `2`
                b.copy_advice(|| "b", &mut region, self.value, 2)?;

                let a = a.value();
                let b = b.value();
                let out = a.zip(b).map(|(a, b)| *a * *b);
                region.assign_advice(|| "out", self.value, 3, || out.ok_or(Error::Synthesis))
            },
        )
    }

    // Layouter takes in vector `constants` of "constant" values, and a same-length vector `signals` of `AssignedCell` and constrains a witness output to the inner product of `<constants, signals>`
    pub fn linear(
        &self,
        layouter: &mut impl Layouter<F>,
        constants: &Vec<F>,
        signals: &Vec<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        assert_eq!(constants.len(), signals.len());
        // don't try to call this function with empty inputs!
        if constants.len() == 0 {
            return Err(Error::Synthesis);
        }
        layouter.assign_region(
            || "inner product with constants",
            |mut region| {
                let mut offset = 0;

                let mut sum = Some(F::zero());

                let mut a_cell =
                    region.assign_advice_from_constant(|| "0", self.value, 0, F::zero())?;
                region.constrain_constant(a_cell.cell(), F::zero())?;

                for (constant, signal) in constants.iter().zip(signals.iter()) {
                    self.q_enable.enable(&mut region, offset)?;

                    // `a` is either 0 or the previous output

                    // `b = constant` and constrain
                    let const_cell = region.assign_advice_from_constant(
                        || "constant",
                        self.value,
                        offset + 1,
                        *constant,
                    )?;
                    region.constrain_constant(const_cell.cell(), *constant)?;

                    // `c = signal` as copy
                    signal.copy_advice(|| "signal", &mut region, self.value, offset + 2)?;

                    sum = sum.zip(signal.value()).map(|(sum, c)| sum + *constant * *c);
                    a_cell = region.assign_advice(
                        || "out",
                        self.value,
                        offset + 3,
                        || sum.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                Ok(a_cell)
            },
        )
    }

    // Layouter takes two vectors of `AssignedCell` and constrains a witness output to the inner product of `<vec_a, vec_b>`
    pub fn inner_product(
        &self,
        layouter: &mut impl Layouter<F>,
        vec_a: &Vec<AssignedCell<F, F>>,
        vec_b: &Vec<AssignedCell<F, F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        assert_eq!(vec_a.len(), vec_b.len());
        // don't try to call this function with empty inputs!
        if vec_a.len() == 0 {
            return Err(Error::Synthesis);
        }
        layouter.assign_region(
            || "inner product",
            |mut region| {
                let mut offset = 0;

                let mut sum = Some(F::zero());

                let mut a_cell =
                    region.assign_advice_from_constant(|| "0", self.value, 0, F::zero())?;
                region.constrain_constant(a_cell.cell(), F::zero())?;

                for (a, b) in vec_a.iter().zip(vec_b.iter()) {
                    self.q_enable.enable(&mut region, offset)?;

                    a.copy_advice(|| "a_i", &mut region, self.value, offset + 1)?;
                    b.copy_advice(|| "b_i", &mut region, self.value, offset + 2)?;

                    sum = sum
                        .zip(a.value())
                        .zip(b.value())
                        .map(|((sum, a), b)| sum + *a * *b);
                    a_cell = region.assign_advice(
                        || "out",
                        self.value,
                        offset + 3,
                        || sum.ok_or(Error::Synthesis),
                    )?;

                    offset += 3;
                }
                Ok(a_cell)
            },
        )
    }

    // | 1 - b | 1 | b | 1 | b | a | 1 - b | out |
    pub fn or(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "or",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let one_minus_b = region.assign_advice(
                    || "1 - b",
                    self.value,
                    0,
                    || b.value().map(|x| F::from(1) - *x).ok_or(Error::Synthesis),
                )?;
                let one =
                    region.assign_advice_from_constant(|| "one", self.value, 1, F::from(1))?;
                region.constrain_constant(one.cell(), F::from(1))?;

                b.copy_advice(|| "b copy", &mut region, self.value, 2)?;
                let one_res =
                    region.assign_advice_from_constant(|| "one", self.value, 3, F::from(1))?;
                region.constrain_constant(one_res.cell(), F::from(1))?;

                self.q_enable.enable(&mut region, 4)?;
                b.copy_advice(|| "b copy", &mut region, self.value, 4)?;
                a.copy_advice(|| "a copy", &mut region, self.value, 5)?;
                one_minus_b.copy_advice(|| "1-b copy", &mut region, self.value, 6)?;

                region.assign_advice(
                    || "or",
                    self.value,
                    7,
                    || {
                        a.value()
                            .zip(b.value())
                            .map(|(av, bv)| *av + *bv - (*av) * (*bv))
                            .ok_or(Error::Synthesis)
                    },
                )
            },
        )
    }

    // | 0 | a | b | out |
    pub fn and(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "and",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let zero =
                    region.assign_advice_from_constant(|| "zero", self.value, 0, F::from(0))?;
                region.constrain_constant(zero.cell(), F::from(0))?;
                a.copy_advice(|| "a copy", &mut region, self.value, 1)?;
                b.copy_advice(|| "b copy", &mut region, self.value, 2)?;
                region.assign_advice(
                    || "and",
                    self.value,
                    3,
                    || {
                        a.value()
                            .zip(b.value())
                            .map(|(av, bv)| (*av) * (*bv))
                            .ok_or(Error::Synthesis)
                    },
                )
            },
        )
    }

    // returns: a || (b && c)
    // | 1 - b c | b | c | 1 | a - 1 | 1 - b c | out | a - 1 | 1 | 1 | a |
    pub fn or_and(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "or_and",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let one_minus_bc = region.assign_advice(
                    || "1 - bc",
                    self.value,
                    0,
                    || {
                        b.value()
                            .zip(c.value())
                            .map(|(bv, cv)| F::from(1) - (*bv) * (*cv))
                            .ok_or(Error::Synthesis)
                    },
                )?;
                b.copy_advice(|| "b copy", &mut region, self.value, 1)?;
                c.copy_advice(|| "c copy", &mut region, self.value, 2)?;

                self.q_enable.enable(&mut region, 3)?;
                let one =
                    region.assign_advice_from_constant(|| "one", self.value, 3, F::from(1))?;
                region.constrain_constant(one.cell(), F::from(1))?;

                let a_minus_one = region.assign_advice(
                    || "a - 1",
                    self.value,
                    7,
                    || a.value().map(|x| *x - F::from(1)).ok_or(Error::Synthesis),
                )?;

                let a_minus_one_copy =
                    a_minus_one.copy_advice(|| "a - 1 copy", &mut region, self.value, 4)?;

                let one_minus_bc_copy =
                    one_minus_bc.copy_advice(|| "1 - bc copy", &mut region, self.value, 5)?;

                let out = region.assign_advice(
                    || "out",
                    self.value,
                    6,
                    || {
                        a.value()
                            .zip(b.value())
                            .zip(c.value())
                            .map(|((av, bv), cv)| *av + (*bv) * (*cv) - (*av) * (*bv) * (*cv))
                            .ok_or(Error::Synthesis)
                    },
                )?;

                self.q_enable.enable(&mut region, 7)?;
                let one2 =
                    region.assign_advice_from_constant(|| "one2", self.value, 8, F::from(1))?;
                region.constrain_constant(one2.cell(), F::from(1))?;
                let one3 =
                    region.assign_advice_from_constant(|| "one3", self.value, 9, F::from(1))?;
                region.constrain_constant(one3.cell(), F::from(1))?;

                let a_copy = a.copy_advice(|| "a copy", &mut region, self.value, 10)?;
                Ok(out)
            },
        )
    }
}
