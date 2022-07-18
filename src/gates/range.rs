use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::{BigInt, BigUint};
use std::marker::PhantomData;

use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
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

    // returns the limbs
    pub fn range_check(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        println!("Calling range_check on {} bits.", range_bits);
        let k = (range_bits + self.lookup_bits - 1) / self.lookup_bits;
        let rem_bits = range_bits % self.lookup_bits;

        let limbs = decompose_option(&a.value().map(|x| *x), k, self.lookup_bits);
        let limb_base = F::from(1u64 << self.lookup_bits);

        layouter.assign_region(
            || format!("range check {} bits", self.lookup_bits),
            |mut region| {
                let mut offset = 1;
                let mut running_sum = limbs[0];
                let mut running_pow = F::from(1u64);

		self.q_lookup.enable(&mut region, 0)?;		
		let mut cells = Vec::with_capacity(3 * k + 2);
		cells.push(Witness(limbs[0]));		
                for idx in 1..k {
                    running_pow = running_pow * limb_base;
                    running_sum = running_sum
                        .zip(limbs[idx])
                        .map(|(sum, x)| sum + x * running_pow);
		    cells.push(Constant(running_pow));
		    cells.push(Witness(limbs[idx]));
		    cells.push(Witness(running_sum));
		    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

		    offset = offset + 3;
                    if idx == k - 1 {
                        if rem_bits != 0 {
                            self.qap_config.q_enable.enable(&mut region, offset)?;
			    cells.push(Constant(F::from(0)));
			    cells.push(Witness(limbs[k - 1]));
			    let mult_val = biguint_to_fe(
                                &(BigUint::from(1u64) << (self.lookup_bits - rem_bits)),
                            );
			    cells.push(Constant(mult_val));
			    cells.push(Witness(Some(mult_val)
                                               .zip(limbs[k - 1])
                                               .map(|(m, l)| m * l)));
                            self.q_lookup.enable(&mut region, offset + 3)?;
                        }
                    }
		}
		let assigned_cells = self.qap_config.assign_region(cells, 0, &mut region)?;
		region.constrain_equal(a.cell(), assigned_cells[3 * (k - 1)].cell())?;
		if rem_bits != 0 {
		    region.constrain_equal(assigned_cells[3 * k - 1].cell(), assigned_cells[3 * k - 4].cell())?;
		}

                let mut assigned_limbs = Vec::with_capacity(k);
		assigned_limbs.push(assigned_cells[0].clone());
		for idx in 1..k {
		    assigned_limbs.push(assigned_cells[3 * idx - 1].clone());
		}
                Ok(assigned_limbs)
            },
        )
    }

    // Warning: This may fail silently if a or b have more than num_bits
    // | a + 2^(num_bits) - b | b | 1 | a + 2^(num_bits) | - 2^(num_bits) | 1 | a |
    pub fn check_less_than(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error> {
        let shifted_val = layouter.assign_region(
            || format!("check_less_than {} bits", num_bits),
            |mut region| {
		self.qap_config.q_enable.enable(&mut region, 0)?;
		self.qap_config.q_enable.enable(&mut region, 3)?;

		let cells = vec![
		    Witness(Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                            .zip(a.value())
                            .zip(b.value())
                            .map(|((x, av), bv)| *av + x - *bv)),
		    Existing(&b),
		    Constant(F::from(1)),
		    Witness(Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                            .zip(a.value())
                            .map(|(x, av)| *av + x)),
		    Constant(bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << num_bits)))),
		    Constant(F::from(1)),
		    Existing(&a)];
		let assigned_cells = self.qap_config.assign_region(cells, 0, &mut region)?;
		Ok(assigned_cells[0].clone())
            },
        )?;

        self.range_check(layouter, &shifted_val, num_bits)?;
        Ok(())
    }

    pub fn is_less_than(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let k = (num_bits + self.lookup_bits - 1) / self.lookup_bits;
        let padded_bits = k * self.lookup_bits;

        layouter.assign_region(
            || format!("is_less_than {} bit bound", num_bits),
            |mut region| {
                self.qap_config.q_enable.enable(&mut region, 0)?;
		self.qap_config.q_enable.enable(&mut region, 3)?;
		self.q_lookup.enable(&mut region, 8)?;

		let mut cells = Vec::with_capacity(9 + 3 * k + 8);
		let shifted_val = Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
		    .zip(a.value())
		    .zip(b.value())
		    .map(|((x, av), bv)| *av + x - *bv);
		cells.push(Witness(shifted_val));
		cells.push(Existing(&b));
		cells.push(Constant(F::from(1)));
		cells.push(Witness(Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
				   .zip(a.value())
				   .map(|(x, av)| *av + x)));
		cells.push(Constant(bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << padded_bits)))));
		cells.push(Constant(F::from(1)));
		cells.push(Existing(&a));
		cells.push(Witness(shifted_val));

		let mut shift_val = shifted_val.as_ref().map(|fe| fe_to_biguint(fe));
                let mask = BigUint::from(1u64 << self.lookup_bits);
                let mut limb = shift_val
                    .as_ref()
                    .map(|x| x.modpow(&BigUint::from(1u64), &mask));
		cells.push(Witness(limb.as_ref().map(|x| biguint_to_fe(x))));

		let mut offset = 9;
                let mut running_sum = limb;
                for idx in 1..(k + 1) {
                    shift_val = shift_val.map(|x| x >> self.lookup_bits);
                    limb = shift_val
                        .as_ref()
                        .map(|x| x.modpow(&BigUint::from(1u64), &mask));
                    running_sum = running_sum
                        .zip(limb.as_ref())
                        .map(|(sum, x)| sum + (x << (idx * self.lookup_bits)));
                    let running_pow =
                        biguint_to_fe(&(BigUint::from(1u64) << (idx * self.lookup_bits)));
		    cells.push(Constant(running_pow));
		    cells.push(Witness(limb.as_ref().map(|x| biguint_to_fe(x))));
		    cells.push(Witness(running_sum.as_ref().map(|sum| biguint_to_fe(sum))));
                    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

                    offset = offset + 3;
		    if idx == k {
			let is_zero = limb.clone().zip(Some(F::from(1))).map(|(x, _y)| {
                            if x == BigUint::from(0u64) {
                                F::from(1)
                            } else {
                                F::from(0)
                            }
                        });
                        let inv = limb.clone().zip(Some(F::from(1))).map(|(x, _y)| {
                            if x == BigUint::from(0u64) {
                                F::from(1)
                            } else {
                                biguint_to_fe::<F>(&x).invert().unwrap()
                            }
                        });
			
                        self.qap_config.q_enable.enable(&mut region, offset)?;
			cells.push(Witness(is_zero));
			cells.push(Witness(limb.as_ref().map(|bi| biguint_to_fe(bi))));
			cells.push(Witness(inv));
			cells.push(Constant(F::from(1)));
			cells.push(Constant(F::from(0)));
			cells.push(Witness(limb.as_ref().map(|bi| biguint_to_fe(bi))));
			cells.push(Witness(is_zero));
			cells.push(Constant(F::from(0)));
		    }				   
		}
		let assigned_cells = self.qap_config.assign_region(cells, 0, &mut region)?;
		region.constrain_equal(assigned_cells[0].cell(), assigned_cells[7].cell())?;
		// check limb equalities for idx = k
		region.constrain_equal(assigned_cells[9 + 3 * k - 2].cell(), assigned_cells[9 + 3 * k + 1].cell())?;
		region.constrain_equal(assigned_cells[9 + 3 * k - 2].cell(), assigned_cells[9 + 3 * k + 5].cell())?;
		// check is_zero equalities
		region.constrain_equal(assigned_cells[9 + 3 * k].cell(), assigned_cells[9 + 3 * k + 6].cell())?;
		Ok(assigned_cells[9 + 3 * k].clone())
            },
        )
    }

    // | out | a | inv | 1 | 0 | a | out | 0
    pub fn is_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero = a.value().map(|x| {
            if (*x).is_zero_vartime() {
                F::from(1)
            } else {
                F::from(0)
            }
        });
        let inv = a.value().map(|x| {
            if *x == F::from(0) {
                F::from(1)
            } else {
                (*x).invert().unwrap()
            }
        });

        layouter.assign_region(
            || "is_equal",
            |mut region| {
                self.qap_config.q_enable.enable(&mut region, 0)?;
		self.qap_config.q_enable.enable(&mut region, 4)?;
		let cells = vec![
		    Witness(is_zero),
		    Existing(&a),
		    Witness(inv),
		    Constant(F::from(1)),
		    Constant(F::from(0)),
		    Existing(&a),
		    Witness(is_zero),
		    Constant(F::from(0))];
		let assigned_cells = self.qap_config.assign_region(cells, 0, &mut region)?;
		region.constrain_equal(assigned_cells[0].cell(), assigned_cells[6].cell())?;
		Ok(assigned_cells[0].clone())
            },
        )
    }

    pub fn is_equal(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let diff = layouter.assign_region(
            || "is_equal",
            |mut region| {
                self.qap_config.q_enable.enable(&mut region, 0)?;
		let cells = vec![
		    Witness(a.value()
                            .zip(b.value())
                            .map(|(av, bv)| *av - *bv)),
		    Constant(F::from(1)),
		    Existing(&b),
		    Existing(&a)];
		let assigned_cells = self.qap_config.assign_region(cells, 0, &mut region)?;
		Ok(assigned_cells[0].clone())
            },
        )?;
        self.is_zero(layouter, &diff)
    }
}
