use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct MultConfig {
    pub out: Column<Advice>,
}

pub struct MultChip<F: FieldExt> {
    config: MultConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MultChip<F> {
    pub fn construct(config: MultConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        a: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        b: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        out: Column<Advice>,
    ) -> MultConfig {
        meta.create_gate("a * b = c", |meta| {
            let q_enable = q_enable(meta);
            let a = a(meta);
            let b = b(meta);
            let out = meta.query_advice(out, Rotation::cur());

            vec![q_enable * (a * b - out)]
        });

        MultConfig { out }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        a: F,
        b: F,
    ) -> Result<(), Error> {
        region.assign_advice(|| "out", self.config.out, offset, || Ok(a * b))?;
        Ok(())
    }
}
