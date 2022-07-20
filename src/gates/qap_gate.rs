use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::BigUint as big_uint;
use num_traits::One;
use std::marker::PhantomData;

use crate::utils::*;

#[derive(Clone, Debug)]
pub enum QuantumCell<'a, F: FieldExt> {
    Existing(&'a AssignedCell<F, F>),
    Witness(Option<F>),
    Constant(F),
}

impl<F: FieldExt> QuantumCell<'_, F> {
    pub fn value(&self) -> Option<&F> {
        match self {
            Self::Existing(a) => a.value(),
            Self::Witness(a) => a.as_ref(),
            Self::Constant(a) => Some(a),
        }
    }
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
                        c,
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
    // | a | b | 1 | a + b |
    pub fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native add",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Existing(&a),
                    QuantumCell::Existing(&b),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) + (*bv))),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `a + b * (-1) = out`
    // Requires config to have a fixed column with `enable_constants` on
    // | a | b | -1 | a - b |
    pub fn sub(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native sub",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Existing(&a),
                    QuantumCell::Existing(&b),
                    QuantumCell::Constant(-F::from(1)),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // | 0 | a | -1 | -a |
    pub fn neg(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native sub",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    QuantumCell::Existing(&a),
                    QuantumCell::Constant(-F::from(1)),
                    QuantumCell::Witness(a.value().map(|av| -(*av))),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `0 + a * b = out`
    // | 0 | a | b | a * b |
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native mul",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    QuantumCell::Existing(&a),
                    QuantumCell::Existing(&b),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter creates new region that copies a, b and constrains `0 + a * b = out`
    // | 0 | a | b | a * b |
    pub fn mul_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "native mul",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    QuantumCell::Existing(&a),
                    QuantumCell::Constant(b),
                    QuantumCell::Witness(a.value().map(|av| (*av) * b)),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // Layouter takes two vectors of `QuantumCell` and constrains a witness output to the inner product of `<vec_a, vec_b>`
    pub fn inner_product(
        &self,
        layouter: &mut impl Layouter<F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<
        (
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
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
                let mut offset = 0;
                for (a, b) in vec_a.iter().zip(vec_b.iter()) {
                    sum = sum
                        .zip(a.value())
                        .zip(b.value())
                        .map(|((sum, a), b)| sum + *a * *b);

                    self.q_enable.enable(&mut region, offset)?;
                    cells.push(a.clone());
                    cells.push(b.clone());
                    cells.push(QuantumCell::Witness(sum));
                    offset += 3;
                }
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                let mut a_assigned = Vec::with_capacity(vec_a.len());
                let mut b_assigned = Vec::with_capacity(vec_a.len());
                for i in 0..vec_a.len() {
                    a_assigned.push(assigned_cells[3 * i + 1].clone());
                    b_assigned.push(assigned_cells[3 * i + 1].clone());
                }

                Ok((
                    a_assigned,
                    b_assigned,
                    assigned_cells.last().unwrap().clone(),
                ))
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
                self.q_enable.enable(&mut region, 4)?;

                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Witness(b.value().map(|x| F::from(1) - *x)),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Existing(&b),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Existing(&b),
                    QuantumCell::Existing(&a),
                    QuantumCell::Witness(b.value().map(|x| F::from(1) - *x)),
                    QuantumCell::Witness(
                        a.value()
                            .zip(b.value())
                            .map(|(av, bv)| *av + *bv - (*av) * (*bv)),
                    ),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[6].cell())?;
                Ok(assigned_cells.last().unwrap().clone())
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
                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Constant(F::from(0)),
                    QuantumCell::Existing(&a),
                    QuantumCell::Existing(&b),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) * (*bv))),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                Ok(assigned_cells.last().unwrap().clone())
            },
        )
    }

    // assumes sel is boolean
    // | a - b | 1 | b | a |
    // | b | sel | a - b | out |
    // returns
    //   a * sel + b * (1 - sel)
    pub fn select(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        sel: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "sel",
            |mut region| {
                self.q_enable.enable(&mut region, 0)?;
                self.q_enable.enable(&mut region, 4)?;
                let cells = vec![
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Existing(&b),
                    QuantumCell::Existing(&a),
                    QuantumCell::Existing(&b),
                    QuantumCell::Existing(&sel),
                    QuantumCell::Witness(a.value().zip(b.value()).map(|(av, bv)| (*av) - (*bv))),
                    QuantumCell::Witness(
                        a.value()
                            .zip(b.value())
                            .zip(sel.value())
                            .map(|((av, bv), sv)| (*av) * (*sv) + (*bv) * (F::from(1) - *sv)),
                    ),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[6].cell())?;
                Ok(assigned_cells.last().unwrap().clone())
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
                self.q_enable.enable(&mut region, 3)?;
                self.q_enable.enable(&mut region, 7)?;

                let cells: Vec<QuantumCell<F>> = vec![
                    QuantumCell::Witness(
                        b.value()
                            .zip(c.value())
                            .map(|(bv, cv)| F::from(1) - (*bv) * (*cv)),
                    ),
                    QuantumCell::Existing(&b),
                    QuantumCell::Existing(&c),
                    QuantumCell::Constant(F::from(1)),
                    QuantumCell::Witness(a.value().map(|x| *x - F::from(1))),
                    QuantumCell::Witness(
                        b.value()
                            .zip(c.value())
                            .map(|(bv, cv)| F::from(1) - (*bv) * (*cv)),
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
                    QuantumCell::Existing(&a),
                ];
                let assigned_cells = self.assign_region(cells, 0, &mut region)?;
                region.constrain_equal(assigned_cells[4].cell(), assigned_cells[7].cell())?;
                region.constrain_equal(assigned_cells[0].cell(), assigned_cells[5].cell())?;
                Ok(assigned_cells[6].clone())
            },
        )
    }

    // assume bits has boolean values
    // returns vec[idx] with vec[idx] = 1 if and only if bits == idx as a binary number
    pub fn bits_to_indicator(
	&self,
	layouter: &mut impl Layouter<F>,
	bits: &Vec<AssignedCell<F, F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
	let k = bits.len();

	let mut inv_bits = Vec::with_capacity(k);
	for idx in 0..k {
	    let inv_bit = layouter.assign_region(
		|| "inv_bits",
		|mut region| {
		    self.q_enable.enable(&mut region, 0)?;
		    let cells = vec![
			QuantumCell::Witness(bits[idx].value().map(|x| F::from(1) - x)),
			QuantumCell::Existing(&bits[idx]),
			QuantumCell::Constant(F::from(1)),
			QuantumCell::Constant(F::from(1))];
		    let assigned_cells = self.assign_region(cells, 0, &mut region)?;
		    Ok(assigned_cells[0].clone())
		}
	    )?;
	    inv_bits.push(inv_bit.clone());
	}

	let mut indicator = Vec::with_capacity(2 * (1 << k) - 2);
	let mut offset = 0;
	indicator.push(inv_bits[0].clone());
	indicator.push(bits[0].clone());
	for idx in 1..k {
	    for old_idx in 0..(1 << idx) {
		let inv_prod = self.mul(layouter, &indicator[offset + old_idx], &inv_bits[idx])?;
		indicator.push(inv_prod);

		let prod = self.mul(layouter, &indicator[offset + old_idx], &bits[idx])?;
		indicator.push(prod);
	    }
	    offset = offset + (1 << idx);
	}
	Ok(indicator[2 * (1 << k) - 2 - (1 << k)..].to_vec())
    }
}
