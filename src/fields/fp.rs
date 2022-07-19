use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint;

use crate::bigint::*;
use crate::gates::qap_gate;
use crate::gates::range;

#[derive(Clone, Debug)]
pub struct FpConfig<F: FieldExt> {
    pub value: Column<Advice>,
    pub constant: Column<Fixed>,
    pub lookup: TableColumn,
    pub lookup_bits: usize,
    pub q_lookup: Selector,
    pub gate: qap_gate::Config<F>,
    pub range: range::RangeConfig<F>,
    pub limb_bits: usize,
    pub num_limbs: usize,
    pub p: BigUint,
}

pub struct FpChip<F: FieldExt> {
    pub config: FpConfig<F>,
}

impl<F: FieldExt> FpChip<F> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value: Column<Advice>,
        constant: Column<Fixed>,
        lookup_bits: usize,
        limb_bits: usize,
        num_limbs: usize,
        p: BigUint,
    ) -> FpConfig<F> {
        let lookup = meta.lookup_table_column();
        let q_lookup = meta.complex_selector();
        meta.enable_equality(value);
        meta.enable_constant(constant);

        let gate_config = qap_gate::Config::configure(meta, value);
        FpConfig {
            value,
            constant,
            lookup,
            lookup_bits,
            q_lookup,
            gate: gate_config.clone(),
            range: range::RangeConfig::configure(
                meta,
                q_lookup,
                lookup,
                lookup_bits,
                gate_config.clone(),
            ),
            limb_bits,
            num_limbs,
            p,
        }
    }

    pub fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.config.range.load_lookup_table(layouter)
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: Vec<Option<F>>,
        max_limb_size: BigUint,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load private",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice(
                        || "private value",
                        config.value,
                        i,
                        || a.ok_or(Error::Synthesis),
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            max_limb_size,
            self.config.limb_bits,
        ))
    }

    pub fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        vec_a: Vec<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let config = &self.config;

        let limbs = layouter.assign_region(
            || "load constant",
            |mut region| {
                let mut limbs = Vec::with_capacity(vec_a.len());
                for (i, a) in vec_a.iter().enumerate() {
                    let limb = region.assign_advice_from_constant(
                        || "constant value",
                        config.value,
                        i,
                        *a,
                    )?;
                    limbs.push(limb);
                }
                Ok(limbs)
            },
        )?;
        Ok(OverflowInteger::construct(
            limbs,
            BigUint::from(1u32) << 64,
            64,
        ))
    }

    // signed overflow BigInt functions
    pub fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        add_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        sub_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        mul_no_carry::assign(&self.config.gate, layouter, a, b)
    }

    pub fn mod_reduce(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        desired_num_limbs: usize,
        modulus: num_bigint::BigUint,
    ) -> Result<OverflowInteger<F>, Error> {
        mod_reduce::assign(&self.config.gate, layouter, a, desired_num_limbs, modulus)
    }

    pub fn check_carry_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<(), Error> {
        check_carry_to_zero::assign(&self.config.range, layouter, a)
    }

    pub fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        carry_mod::assign(&self.config.range, layouter, a, &self.config.p)
    }

    // BigInt functions
    pub fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<OverflowInteger<F>, Error> {
        decompose::assign(
            &self.config.range,
            layouter,
            a,
            self.config.limb_bits,
            self.config.num_limbs,
        )
    }

    pub fn big_less_than(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        big_less_than::assign(&self.config.range, layouter, a, b)
    }

    // F_p functions
    pub fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &OverflowInteger<F>,
        b: &OverflowInteger<F>,
    ) -> Result<OverflowInteger<F>, Error> {
        let k_a = a.limbs.len();
        let k_b = b.limbs.len();
        assert_eq!(k_a, k_b);
        let k = k_a;

        let no_carry = self.mul_no_carry(layouter, a, b)?;
        let prime_reduce = self.mod_reduce(layouter, &no_carry, k, self.config.p.clone())?;
        self.carry_mod(layouter, &prime_reduce)
    }
}
