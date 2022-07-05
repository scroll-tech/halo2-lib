use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region},
    plonk::{Advice, Assigned, Column, Constraint, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

// Gate to perform a * b + c - out = 0
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

            vec![q * (a * b + c - out)]
        })
    }

    // assign to a region by imposing copy constraints from some assigned cells. Assigned cells store values in Assigned<F> in case we need to do native division later
    pub fn assign_region(
        &self,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        c: &AssignedCell<F, F>,
        offset: usize,
        region: &mut Region<'_, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // Enable `q_enable` selector
        self.q_enable.enable(region, offset)?;

        // Copy `a` into `value` column at `offset`
        a.copy_advice(|| "a", region, self.value, offset)?;

        // Copy `b` into `value` column at `offset + 1`
        b.copy_advice(|| "b", region, self.value, offset + 1)?;

        // Copy `c` into `value` column at `offset + 2`
        c.copy_advice(|| "c", region, self.value, offset + 2)?;

        let a = a.value();
        let b = b.value();
        let c = c.value();
        let out = a.zip(b).zip(c).map(|((a, b), c)| *a * *b + *c);
        region.assign_advice(
            || "out",
            self.value,
            offset + 3,
            || out.ok_or(Error::Synthesis),
        )
    }
}
