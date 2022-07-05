use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

// Gate to perform `a + b * c - out = 0`
// We chose `a + b * c` instead of `a * b + c` to allow "chaining" of gates, i.e., the output of one gate because `a` in the next gate
#[derive(Clone, Debug)]
pub struct Config<F: FieldExt> {
    q_enable: Selector,
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
        a: Option<F>,
        b: Option<F>,
        c: Option<F>,
        offset: usize,
        region: &mut Region<'_, F>,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        // Enable `q_enable` selector
        self.q_enable.enable(region, offset)?;

        // Assign `a` into `value` column at `offset`
        let a_cell =
            region.assign_advice(|| "a", self.value, offset, || a.ok_or(Error::Synthesis))?;

        // Assign `b` into `value` column at `offset + 1`
        let b_cell =
            region.assign_advice(|| "b", self.value, offset + 1, || b.ok_or(Error::Synthesis))?;

        // Assign `c` into `value` column at `offset + 2`
        let c_cell =
            region.assign_advice(|| "c", self.value, offset + 2, || c.ok_or(Error::Synthesis))?;

        let out = a.zip(b).zip(c).map(|((a, b), c)| a + b * c);
        let out_cell = region.assign_advice(
            || "out",
            self.value,
            offset + 3,
            || out.ok_or(Error::Synthesis),
        )?;

        Ok((a_cell, b_cell, c_cell, out_cell))
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
                    region.constrain_constant(const_cell.cell(), *constant);

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
}
