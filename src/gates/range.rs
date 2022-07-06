use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::BigUint;
use std::marker::PhantomData;

use crate::gates::qap_gate;

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

    fn create_lookup(&self, meta: &mut ConstraintSystem<F>) -> Result<(), Error> {
        meta.lookup("lookup", |meta| {
            let q = meta.query_selector(self.q_lookup);
            let a = meta.query_advice(self.qap_config.value, Rotation::cur());
            vec![(q * a, self.lookup)]
        });
        Ok(())
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

	let a_val_temp = a.value().ok_or(Error::Synthesis)?;
	let mut a_val = BigUint::from_bytes_le(a_val_temp.to_repr().as_ref().try_into().unwrap());
	
	let limb_val = u64::pow(2, self.lookup_bits as u32);
	let limb_val_big = BigUint::from(limb_val);
	
	let mut out_limbs = Vec::with_capacity(k);
	for idx in 0..k {
	    let limb = u64::try_from(a_val.clone() % limb_val_big.clone()).unwrap();
	    out_limbs.push(limb);
	    a_val = a_val.clone() / limb_val_big.clone();
	}
	
	layouter.assign_region(
	    || format!("range check {} bits", self.lookup_bits),
	    |mut region| {
		region.assign_advice_from_constant(
		    || "limb 0",
		    self.qap_config.value,
		    0,
		    F::from(out_limbs[0]))?;
		self.q_lookup.enable(&mut region, 0)?;

		let mut offset = 1;
		let mut running_sum = F::from(out_limbs[0]);
		let mut running_pow = F::from(1);
		for idx in 1..k {
		    running_pow = running_pow * F::from(limb_val);
		    running_sum = running_sum + F::from(out_limbs[idx]) * running_pow.clone();
		    
		    let const_cell = region.assign_advice_from_constant(
			|| format!("base^{}", idx),
			self.qap_config.value,
			offset,
			running_pow.clone())?;
		    region.constrain_constant(const_cell.cell(), running_pow.clone())?;
		    let limb_cell = region.assign_advice(
			|| format!("limb {}", idx),
			self.qap_config.value,
			offset + 1,
			|| Ok(F::from(out_limbs[idx])))?;
		    let out_cell = region.assign_advice(
			|| format!("running sum {}", idx),
			self.qap_config.value,
			offset + 2,
			|| Ok(running_sum.clone()))?;

		    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
		    self.q_lookup.enable(&mut region, offset + 1);
		    
		    offset = offset + 3;
		    if idx == k - 1 {
			region.constrain_equal(a.cell(), out_cell.cell())?;
		    }
		}
		Ok(())
	    }
	)?;
	Ok(())
    }
}
