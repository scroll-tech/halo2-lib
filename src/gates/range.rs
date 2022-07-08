use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use num_bigint::{BigInt, BigUint};
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
                let mut assigned_limbs = Vec::with_capacity(k);

                let limb_cell = region.assign_advice(
                    || "limb 0",
                    self.qap_config.value,
                    0,
                    || limbs[0].ok_or(Error::Synthesis),
                )?;
                assigned_limbs.push(limb_cell);

                self.q_lookup.enable(&mut region, 0)?;

                let mut offset = 1;
                let mut running_sum = limbs[0];
                let mut running_pow = F::from(1u64);
                for idx in 1..k {
                    running_pow = running_pow * limb_base;
                    running_sum = running_sum
                        .zip(limbs[idx])
                        .map(|(sum, x)| sum + x * running_pow);

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
                        || limbs[idx].ok_or(Error::Synthesis),
                    )?;
                    assigned_limbs.push(limb_cell);

                    let out_cell = region.assign_advice(
                        || format!("running sum {}", idx),
                        self.qap_config.value,
                        offset + 2,
                        || running_sum.ok_or(Error::Synthesis),
                    )?;

                    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

                    offset = offset + 3;
                    if idx == k - 1 {
                        assert_eq!(assigned_limbs.len(), k);
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

                            let limb_copy = assigned_limbs[k - 1].copy_advice(
                                || "shifted lookup",
                                &mut region,
                                self.qap_config.value,
                                offset + 1,
                            )?;

                            let mult_val = biguint_to_fe(
                                &(BigUint::from(1u64) << (self.lookup_bits - rem_bits)),
                            );
                            let mult_cell = region.assign_advice_from_constant(
                                || "mult",
                                self.qap_config.value,
                                offset + 2,
                                mult_val,
                            )?;
                            region.constrain_constant(mult_cell.cell(), mult_val)?;

                            let prod_cell = region.assign_advice(
                                || "prod",
                                self.qap_config.value,
                                offset + 3,
                                || {
                                    Some(mult_val)
                                        .zip(limb_copy.value())
                                        .map(|(m, l)| m * l)
                                        .ok_or(Error::Synthesis)
                                },
                            )?;
                            self.q_lookup.enable(&mut region, offset + 3)?;
                        }
                    }
                }
                Ok(assigned_limbs)
            },
        )
    }

    // Warning: This may fail silently if a or b have more than num_bits
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
                let mut offset = 0;

                self.qap_config.q_enable.enable(&mut region, offset)?;
                let shifted_val = region.assign_advice(
                    || "shifted_val",
                    self.qap_config.value,
                    offset,
                    || {
                        Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                            .zip(a.value())
                            .zip(b.value())
                            .map(|((x, av), bv)| *av + x - *bv)
                            .ok_or(Error::Synthesis)
                    },
                )?;
                b.copy_advice(|| "b copy", &mut region, self.qap_config.value, offset + 1)?;
                let one = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    offset + 2,
                    F::from(1),
                )?;
                region.constrain_constant(one.cell(), F::from(1))?;

                self.qap_config.q_enable.enable(&mut region, offset + 3)?;
                let shifted_val_partial = region.assign_advice(
                    || "shifted_val_partial",
                    self.qap_config.value,
                    offset + 3,
                    || {
                        Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << num_bits)))
                            .zip(a.value())
                            .map(|(x, av)| *av + x)
                            .ok_or(Error::Synthesis)
                    },
                )?;
                let neg_pow = region.assign_advice_from_constant(
                    || "neg_pow",
                    self.qap_config.value,
                    offset + 4,
                    bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << num_bits))),
                )?;

                region.constrain_constant(
                    neg_pow.cell(),
                    bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << num_bits))),
                )?;
                let one_rep = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    offset + 5,
                    F::from(1),
                )?;
                region.constrain_constant(one_rep.cell(), F::from(1))?;
                a.copy_advice(|| "a copy", &mut region, self.qap_config.value, offset + 6)?;
                Ok(shifted_val)
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
                let mut offset = 0;
                self.qap_config.q_enable.enable(&mut region, offset)?;
                let shifted_val = region.assign_advice(
                    || "shifted_val",
                    self.qap_config.value,
                    offset,
                    || {
                        Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
                            .zip(a.value())
                            .zip(b.value())
                            .map(|((x, av), bv)| *av + x - *bv)
                            .ok_or(Error::Synthesis)
                    },
                )?;
                b.copy_advice(|| "b copy", &mut region, self.qap_config.value, offset + 1)?;
                let one = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    offset + 2,
                    F::from(1),
                )?;
                region.constrain_constant(one.cell(), F::from(1))?;

                self.qap_config.q_enable.enable(&mut region, offset + 3)?;
                let shifted_val_partial = region.assign_advice(
                    || "shifted_val_partial",
                    self.qap_config.value,
                    offset + 3,
                    || {
                        Some(biguint_to_fe::<F>(&(BigUint::from(1u64) << padded_bits)))
                            .zip(a.value())
                            .map(|(x, av)| *av + x)
                            .ok_or(Error::Synthesis)
                    },
                )?;

                let neg_pow = region.assign_advice_from_constant(
                    || "neg_pow",
                    self.qap_config.value,
                    offset + 4,
                    bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << padded_bits))),
                )?;
                region.constrain_constant(
                    neg_pow.cell(),
                    bigint_to_fe::<F>(&(BigInt::from(-1i64) * (BigInt::from(1u64) << padded_bits))),
                )?;

                let one_rep = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    offset + 5,
                    F::from(1),
                )?;
                region.constrain_constant(one_rep.cell(), F::from(1))?;

                a.copy_advice(|| "a copy", &mut region, self.qap_config.value, offset + 6)?;

                let shift = shifted_val.copy_advice(
                    || "shifted_val copy",
                    &mut region,
                    self.qap_config.value,
                    offset + 7,
                )?;

                let mut shift_val = shift.value().map(|fe| fe_to_biguint(fe));
                let mask = BigUint::from(1u64 << self.lookup_bits);
                let mut limb = shift_val
                    .as_ref()
                    .map(|x| x.modpow(&BigUint::from(1u64), &mask));

                region.assign_advice(
                    || "limb 0",
                    self.qap_config.value,
                    offset + 8,
                    || {
                        limb.as_ref()
                            .map(|x| biguint_to_fe(x))
                            .ok_or(Error::Synthesis)
                    },
                )?;
                self.q_lookup.enable(&mut region, offset + 8)?;
                offset = offset + 9;

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
                        || {
                            limb.as_ref()
                                .map(|x| biguint_to_fe(x))
                                .ok_or(Error::Synthesis)
                        },
                    )?;

                    let out_cell = region.assign_advice(
                        || format!("running sum {}", idx),
                        self.qap_config.value,
                        offset + 2,
                        || {
                            running_sum
                                .as_ref()
                                .map(|sum| biguint_to_fe(sum))
                                .ok_or(Error::Synthesis)
                        },
                    )?;

                    self.qap_config.q_enable.enable(&mut region, offset - 1)?;
                    self.q_lookup.enable(&mut region, offset + 1)?;

                    offset = offset + 3;
                    if idx == k {
                        region.constrain_equal(shift.cell(), out_cell.cell())?;

                        let is_zero = limb_cell.value().zip(Some(F::from(1))).map(|(x, y)| {
                            if (*x).is_zero_vartime() {
                                F::from(1)
                            } else {
                                F::from(0)
                            }
                        });
                        let inv = limb_cell.value().zip(Some(F::from(1))).map(|(x, y)| {
                            if *x == F::from(0) {
                                F::from(1)
                            } else {
                                (*x).invert().unwrap()
                            }
                        });

                        self.qap_config.q_enable.enable(&mut region, offset)?;
                        let is_zero_assign = region.assign_advice(
                            || "is_zero",
                            self.qap_config.value,
                            offset,
                            || is_zero.ok_or(Error::Synthesis),
                        )?;

                        let limb_copy = limb_cell.copy_advice(
                            || "limb copy",
                            &mut region,
                            self.qap_config.value,
                            offset + 1,
                        )?;

                        let inv_assign = region.assign_advice(
                            || "inv",
                            self.qap_config.value,
                            offset + 2,
                            || inv.ok_or(Error::Synthesis),
                        )?;

                        let one = region.assign_advice_from_constant(
                            || "one",
                            self.qap_config.value,
                            offset + 3,
                            F::from(1),
                        )?;
                        region.constrain_constant(one.cell(), F::from(1))?;

                        self.qap_config.q_enable.enable(&mut region, offset + 4)?;
                        let zero = region.assign_advice_from_constant(
                            || "zero",
                            self.qap_config.value,
                            offset + 4,
                            F::from(0),
                        )?;
                        region.constrain_constant(zero.cell(), F::from(0))?;

                        let limb_copy2 = limb_cell.copy_advice(
                            || "limb copy 2",
                            &mut region,
                            self.qap_config.value,
                            offset + 5,
                        )?;

                        let is_zero_copy = is_zero_assign.copy_advice(
                            || "is_zero copy",
                            &mut region,
                            self.qap_config.value,
                            offset + 6,
                        )?;

                        let zero_temp = region.assign_advice_from_constant(
                            || "zero",
                            self.qap_config.value,
                            offset + 7,
                            F::from(0),
                        )?;
                        region.constrain_constant(zero_temp.cell(), F::from(0))?;
                        return Ok(is_zero_assign);
                    }
                }
                Err(Error::Synthesis)
            },
        )
    }

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
                let is_zero_assign = region.assign_advice(
                    || "is_zero",
                    self.qap_config.value,
                    0,
                    || is_zero.ok_or(Error::Synthesis),
                )?;

                let a_copy = a.copy_advice(|| "a copy", &mut region, self.qap_config.value, 1)?;

                let inv_assign = region.assign_advice(
                    || "inv",
                    self.qap_config.value,
                    2,
                    || inv.ok_or(Error::Synthesis),
                )?;

                let one = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    3,
                    F::from(1),
                )?;
                region.constrain_constant(one.cell(), F::from(1))?;

                self.qap_config.q_enable.enable(&mut region, 4)?;
                let zero = region.assign_advice_from_constant(
                    || "zero",
                    self.qap_config.value,
                    4,
                    F::from(0),
                )?;
                region.constrain_constant(zero.cell(), F::from(0))?;

                let a_copy2 =
                    a.copy_advice(|| "a copy 2", &mut region, self.qap_config.value, 5)?;

                let is_zero_copy = is_zero_assign.copy_advice(
                    || "is_zero copy",
                    &mut region,
                    self.qap_config.value,
                    6,
                )?;

                let zero_temp = region.assign_advice_from_constant(
                    || "zero",
                    self.qap_config.value,
                    7,
                    F::from(0),
                )?;
                region.constrain_constant(zero_temp.cell(), F::from(0))?;
                Ok(is_zero_assign)
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
                let diff = region.assign_advice(
                    || "diff",
                    self.qap_config.value,
                    0,
                    || {
                        a.value()
                            .zip(b.value())
                            .map(|(av, bv)| *av - *bv)
                            .ok_or(Error::Synthesis)
                    },
                )?;
                let one = region.assign_advice_from_constant(
                    || "one",
                    self.qap_config.value,
                    1,
                    F::from(1),
                )?;
                region.constrain_constant(one.cell(), F::from(1))?;
                b.copy_advice(|| "b copy", &mut region, self.qap_config.value, 2)?;
                a.copy_advice(|| "a copy", &mut region, self.qap_config.value, 3)?;
                Ok(diff)
            },
        )?;
        self.is_zero(layouter, &diff)
    }
}
