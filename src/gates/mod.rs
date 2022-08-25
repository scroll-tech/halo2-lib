use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region},
    plonk::{ConstraintSystem, Error, Selector},
};

use self::flex_gate::FlexGateChip;

pub mod flex_gate;
pub mod range;

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

pub trait GateInstructions<F: FieldExt> {
    fn assign_region(
        &mut self,
        inputs: Vec<QuantumCell<F>>,
        offset: usize,
        region: &mut Region<'_, F>,
    ) -> Result<(Vec<AssignedCell<F, F>>, usize), Error>;

    fn enable(
        &self,
        region: &mut Region<'_, F>,
        gate_index: usize,
        offset: usize,
    ) -> Result<(), Error>;

    fn add(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn sub(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn neg(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn mul(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn inner_product(
        &mut self,
        layouter: &mut impl Layouter<F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<(Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>, AssignedCell<F, F>), Error>;

    fn or(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn and(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn not(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.sub(layouter, &QuantumCell::Constant(F::from(1)), a)
    }

    fn select(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        sel: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn or_and(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        c: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn bits_to_indicator(
        &mut self,
        layouter: &mut impl Layouter<F>,
        bits: &Vec<QuantumCell<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;
}

pub trait RangeInstructions<F: FieldExt> {
    type GateChip: GateInstructions<F>;

    fn gate(&mut self) -> &mut Self::GateChip;

    fn lookup_bits(&self) -> usize;

    fn enable_lookup(
        &self,
        region: &mut Region<'_, F>,
        column_index: usize,
        offset: usize,
    ) -> Result<(), Error>;

    fn range_check(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;

    fn check_less_than(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error>;

    fn is_less_than(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn is_zero(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn is_equal(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn num_to_bits(
        &mut self,
        layouter: &mut impl Layouter<F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;
}

#[cfg(test)]
pub mod tests;
