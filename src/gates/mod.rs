use std::collections::HashMap;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Cell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
};
use num_bigint::BigUint;

use crate::utils::fe_to_biguint;

use self::{flex_gate::GateStrategy, range::RangeStrategy};

pub mod flex_gate;
pub mod range;

#[derive(Clone, Debug)]
pub enum QuantumCell<'a, F: FieldExt> {
    Existing(&'a AssignedCell<F, F>),
    Witness(Value<F>),
    Constant(F),
}

impl<F: FieldExt> QuantumCell<'_, F> {
    pub fn value(&self) -> Value<&F> {
        match self {
            Self::Existing(a) => a.value(),
            Self::Witness(a) => a.as_ref(),
            Self::Constant(a) => Value::known(a),
        }
    }
}

// The reason we have a `Context` is that we will need to mutably borrow `advice_rows` (etc.) to update row count
// The `Circuit` trait takes in `Config` as an input that is NOT mutable, so we must pass around &mut Context everywhere for function calls
// We follow halo2wrong's convention of having `Context` also include the `Region` to be passed around, instead of a `Layouter`, so that everything happens within a single `layouter.assign_region` call. This allows us to circumvent the Halo2 layouter and use our own "pseudo-layouter", which is more specialized (and hence faster) for our specific gates
#[derive(Debug)]
pub struct Context<'a, F: FieldExt> {
    pub region: Region<'a, F>, // I don't see a region to use Box<Region<'a, F>> since we will pass mutable reference of `Context` anyways

    // `advice_rows[i]` keeps track of the number of rows used in the advice column `config.gates[i].value`
    pub advice_rows: Vec<usize>,

    // `constants_to_assign` is a vector keeping track of all constants that we use throughout
    // we load them all in one go using fn `load_constants`
    // if we have (c, Some(cell)) in the vector then we also constrain the loaded cell for `c` to equal `cell`
    pub constants_to_assign: Vec<(F, Option<Cell>)>,
    pub zero_cell: Option<AssignedCell<F, F>>,

    // `cells_to_lookup` is a vector keeping track of all cells that we want to enable lookup for. When there is more than 1 advice column we will copy_advice all of these cells to the single lookup enabled column and do lookups there
    pub cells_to_lookup: Vec<AssignedCell<F, F>>,
    // SimpleFloorPlanner calls the assignments in `layouter.assign_region` twice:
    // https://github.com/privacy-scaling-explorations/halo2/blob/f586922d19c3c96ffcec4adbe1790132565ffba6/halo2_proofs/src/circuit/floor_planner/single_pass.rs#L91
    // The following is a hack to get around this for row counting purposes
    // EDIT: we now do this in the `synthesis` function to skip the get shape step completely
    pub using_simple_floor_planner: bool,
    pub first_pass: bool, // AKA `in_shape_mode`

    #[cfg(feature = "display")]
    pub op_count: HashMap<String, usize>,
}

impl<'a, F: FieldExt> std::fmt::Display for Context<'a, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#?}", self)
    }
}

// a single struct to package any configuration parameters we will need for constructing a new `Context`
#[derive(Clone, Copy, Debug)]
pub struct ContextParams {
    pub num_advice: usize,
    pub using_simple_floor_planner: bool,
    pub first_pass: bool,
}

impl<'a, F: FieldExt> Context<'a, F> {
    pub fn new(region: Region<'a, F>, params: ContextParams) -> Self {
        Self {
            region,
            advice_rows: vec![0; params.num_advice],
            constants_to_assign: Vec::new(),
            zero_cell: None,
            cells_to_lookup: Vec::new(),
            using_simple_floor_planner: params.using_simple_floor_planner,
            first_pass: params.first_pass,
            #[cfg(feature = "display")]
            op_count: HashMap::new(),
        }
    }

    /// returns leftmost `i` where `advice_rows[i]` is minimum amongst all `advice_rows`
    fn min_gate_index(&self) -> usize {
        self.advice_rows
            .iter()
            .enumerate()
            .min_by(|(_, x), (_, y)| x.cmp(y))
            .map(|(i, _)| i)
            .unwrap()
    }

    /// call this at the very end of synthesize!
    /// assumes self.region is not in shape mode
    pub fn assign_and_constrain_constants(
        &mut self,
        fixed_columns: &Vec<Column<Fixed>>,
    ) -> Result<(usize, usize), Error> {
        // load constants cyclically over `fixed_columns.len()` columns
        let mut assigned: HashMap<BigUint, AssignedCell<F, F>> = HashMap::new();
        let mut col = 0;
        let mut offset = 0;

        for (c, ocell) in &self.constants_to_assign {
            let c_big = fe_to_biguint(c);
            let c_cell = if let Some(c_cell) = assigned.get(&c_big) {
                c_cell.clone()
            } else {
                let c_cell = self.region.assign_fixed(
                    || "load constant",
                    fixed_columns[col],
                    offset,
                    || Value::known(c.clone()),
                )?;
                assigned.insert(c_big, c_cell.clone());
                col += 1;
                if col == fixed_columns.len() {
                    col = 0;
                    offset += 1;
                }
                c_cell
            };
            if let Some(cell) = ocell {
                self.region.constrain_equal(c_cell.cell(), cell.clone())?;
            }
        }
        Ok((offset, assigned.len()))
    }

    /// call this at the very end of synthesize!
    /// assumes self.region is not in shape mode
    pub fn copy_and_lookup_cells(
        &mut self,
        lookup_advice: &Vec<Column<Advice>>,
    ) -> Result<usize, Error> {
        let mut col = 0;
        let mut offset = 0;
        for acell in &self.cells_to_lookup {
            acell.copy_advice(
                || "copy lookup cell",
                &mut self.region,
                lookup_advice[col],
                offset,
            )?;
            col += 1;
            if col == lookup_advice.len() {
                col = 0;
                offset += 1;
            }
        }
        Ok(offset)
    }
}

pub trait GateInstructions<F: FieldExt> {
    fn strategy(&self) -> GateStrategy;
    fn assign_region(
        &self,
        ctx: &mut Context<'_, F>,
        inputs: Vec<QuantumCell<F>>,
        gate_offsets: Vec<(isize, Option<[F; 3]>)>,
        gate_index: Option<usize>,
    ) -> Result<(Vec<AssignedCell<F, F>>, usize), Error>;

    fn assign_region_smart(
        &self,
        ctx: &mut Context<'_, F>,
        inputs: Vec<QuantumCell<F>>,
        gate_offsets: Vec<usize>,
        equality_offsets: Vec<(usize, usize)>,
        external_equality: Vec<(&AssignedCell<F, F>, usize)>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;

    fn load_zero(&self, ctx: &mut Context<'_, F>) -> Result<AssignedCell<F, F>, Error>;

    fn add(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn sub(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn neg(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn mul(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    /// a * b + c
    fn mul_add(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        c: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn div_unsafe(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let c = a.value().zip(b.value()).map(|(&a, b)| a * b.invert().unwrap());
        let assignments = self.assign_region_smart(
            ctx,
            vec![QuantumCell::Constant(F::from(0)), QuantumCell::Witness(c), b.clone(), a.clone()],
            vec![0],
            vec![],
            vec![],
        )?;
        Ok(assignments[1].clone())
    }

    fn inner_product(
        &self,
        ctx: &mut Context<'_, F>,
        vec_a: &Vec<QuantumCell<F>>,
        vec_b: &Vec<QuantumCell<F>>,
    ) -> Result<
        (
            Option<Vec<(AssignedCell<F, F>, usize)>>,
            Option<Vec<(AssignedCell<F, F>, usize)>>,
            AssignedCell<F, F>,
            usize,
        ),
        Error,
    >;

    fn sum_products_with_coeff_and_var<'a>(
        &self,
        ctx: &mut Context<'_, F>,
        values: &[(F, QuantumCell<F>, QuantumCell<F>)],
        var: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn or(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn and(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn not(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        self.sub(ctx, &QuantumCell::Constant(F::from(1)), a)
    }

    fn select(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        sel: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn or_and(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        c: &QuantumCell<F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn bits_to_indicator(
        &self,
        ctx: &mut Context<'_, F>,
        bits: &Vec<QuantumCell<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;
}

pub trait RangeInstructions<F: FieldExt> {
    type Gate: GateInstructions<F>;

    fn gate(&self) -> &Self::Gate;
    fn strategy(&self) -> RangeStrategy;

    fn lookup_bits(&self) -> usize;

    fn range_check(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;

    fn check_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
        num_bits: usize,
    ) -> Result<(), Error>;

    fn is_less_than(
        &self,
        ctx: &mut Context<'_, F>,
        a: &QuantumCell<F>,
        b: &QuantumCell<F>,
        num_bits: usize,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn is_zero(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn is_equal(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        b: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error>;

    fn num_to_bits(
        &self,
        ctx: &mut Context<'_, F>,
        a: &AssignedCell<F, F>,
        range_bits: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>;
}

#[cfg(test)]
pub mod tests;
