use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::BigUint;
use std::marker::PhantomData;

use crate::gates::qap_gate;
use crate::utils::*;

#[derive(Clone, Debug)]
pub struct RangeConfig<F: FieldExt> {
    pub q_lookup: Selector,
    pub lookup: TableColumn,
    pub lookup_bits: usize,
    pub qap_config: qap_gate::Config<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RangeConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        lookup: TableColumn,
        lookup_bits: usize,
        qap_config: qap_gate::Config<F>,
    ) -> Self {
        assert!(lookup_bits <= 28);
        let config = Self {
            q_lookup,
            lookup,
            lookup_bits,
            qap_config,
            _marker: PhantomData,
        };
        config.create_lookup(meta);

        config
    }

    fn create_lookup(&self, meta: &mut ConstraintSystem<F>) -> () {
        meta.lookup("lookup", |meta| {
            let q = meta.query_selector(self.q_lookup);
            let a = meta.query_advice(self.qap_config.value, Rotation::cur());
            vec![(q * a, self.lookup)]
        });
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
                        || Ok(F::from(idx as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    pub fn range_check(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<(), Error> {
        assert!(range_bits % self.lookup_bits == 0);
        let k = range_bits / self.lookup_bits;

        let a_val = a.value();
        let out_limbs = match a_val {
            Some(a_fe) => decompose(a_fe, k, self.lookup_bits)
                .into_iter()
                .map(|limb| Some(limb))
                .collect(),
            None => vec![None; k],
        };

        let limb_base = 1u64 << self.lookup_bits;

        layouter.assign_region(
            || format!("range check {} bits", self.lookup_bits),
            |mut region| {
                let mut running_sum = out_limbs[0];
                region.assign_advice(
                    || "limb 0",
                    self.qap_config.value,
                    0,
                    || running_sum.ok_or(Error::Synthesis),
                )?;
                self.q_lookup.enable(&mut region, 0)?;

                let mut offset = 1;
                let mut running_pow = F::from(1);
                for idx in 1..k {
                    running_pow = running_pow * F::from(limb_base);
                    running_sum = running_sum
                        .zip(out_limbs[idx])
                        .map(|(sum, x)| sum + x * running_pow);

                    let const_cell = region.assign_advice_from_constant(
                        || format!("base^{}", idx),
                        self.qap_config.value,
                        offset,
                        running_pow,
                    )?;
                    let limb_cell = region.assign_advice(
                        || format!("limb {}", idx),
                        self.qap_config.value,
                        offset + 1,
                        || out_limbs[idx].ok_or(Error::Synthesis),
                    )?;
                    let out_cell = region.assign_advice(
                        || format!("running sum {}", idx),
                        self.qap_config.value,
                        offset + 2,
                        || running_sum.ok_or(Error::Synthesis),
                    )?;

                    region.constrain_constant(const_cell.cell(), running_pow)?;
                    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

                    offset = offset + 3;
                    if idx == k - 1 {
                        region.constrain_equal(a.cell(), out_cell.cell())?;
                    }
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}
