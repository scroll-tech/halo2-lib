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
        let k = (range_bits + self.lookup_bits - 1) / self.lookup_bits;
	let rem_bits = range_bits % self.lookup_bits;

        let mut a_val = a
            .value()
            .map(|fe| u64::from_le_bytes(fe.to_repr().as_ref()[0..8].try_into().unwrap()));
        let mask = (1u64 << self.lookup_bits) - 1u64;
        let mut limb = a_val.map(|x| x & mask);

        layouter.assign_region(
            || format!("range check {} bits", self.lookup_bits),
            |mut region| {
                region.assign_advice(
                    || "limb 0",
                    self.qap_config.value,
                    0,
                    || limb.map(|x| F::from(x)).ok_or(Error::Synthesis),
                )?;
                self.q_lookup.enable(&mut region, 0)?;

                let mut offset = 1;
                let mut running_sum = limb;
                for idx in 1..k {
                    a_val = a_val.map(|x| x >> self.lookup_bits);
                    limb = a_val.map(|x| x & mask);
                    running_sum = running_sum
                        .zip(limb)
                        .map(|(sum, x)| sum + (x << (idx * self.lookup_bits)));

                    let running_pow = F::from(1u64 << (idx * self.lookup_bits));
                    let const_cell = region.assign_advice_from_constant(
                        || format!("base^{}", idx),
                        self.qap_config.value,
                        offset,
                        running_pow,
                    )?;
                    region.constrain_constant(const_cell.cell(), running_pow)?;

                    let limb_cell = region.assign_advice(
                        || format!("limb {}", idx),
                        self.qap_config.value,
                        offset + 1,
                        || limb.map(|x| F::from(x)).ok_or(Error::Synthesis),
                    )?;

                    let out_cell = region.assign_advice(
                        || format!("running sum {}", idx),
                        self.qap_config.value,
                        offset + 2,
                        || running_sum.map(|sum| F::from(sum)).ok_or(Error::Synthesis),
                    )?;

                    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

                    offset = offset + 3;
                    if idx == k - 1 {
                        region.constrain_equal(a.cell(), out_cell.cell())?;
			if rem_bits != 0 {
			    self.qap_config.q_enable.enable(&mut region, offset)?;
			    
			    let zero_cell = region.assign_advice_from_constant(
				|| "zero",
				self.qap_config.value,
				offset,
				F::from(0),
			    )?;
			    region.constrain_constant(zero_cell.cell(), F::from(0))?;
			    
			    let limb_copy = limb_cell.copy_advice(
				|| "shifted lookup",
				&mut region,
				self.qap_config.value,
				offset + 1
			    )?;

			    let mult_val = big_to_fe(&(BigUint::from(1u64) << (self.lookup_bits - rem_bits)));
			    let mult_cell = region.assign_advice_from_constant(
				|| "mult",
				self.qap_config.value,
				offset + 2,
				mult_val
			    )?;
			    region.constrain_constant(mult_cell.cell(), mult_val)?;

			    let prod_cell = region.assign_advice(
				|| "prod",
				self.qap_config.value,
				offset + 3,
				|| Some(mult_val)
				    .zip(limb_copy.value())
				    .map(|(m, l)| m * l)
				    .ok_or(Error::Synthesis)
			    )?;
			    self.q_lookup.enable(&mut region, offset + 3)?;				    
			}
                    }		    
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}
