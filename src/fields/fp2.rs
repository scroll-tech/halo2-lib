use std::marker::PhantomData;

use ff::PrimeField;
use halo2_proofs::{
    arithmetic::{BaseExt, Field, FieldExt},
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use num_bigint::{BigInt, BigUint};
use num_traits::Num;

use crate::bigint::{
    add_no_carry, carry_mod, check_carry_mod_to_zero, mul_no_carry, scalar_mul_no_carry,
    sub_no_carry, CRTInteger, OverflowInteger,
};
use crate::fields::fp::{FpChip, FpConfig};
use crate::gates::qap_gate;
use crate::gates::qap_gate::QuantumCell::{Constant, Existing, Witness};
use crate::gates::range;
use crate::utils::{bigint_to_fe, decompose_bigint_option, fe_to_biguint};

use super::{FieldChip, FqPoint};

// helper trait so we can actually construct and read the Fp2 struct
// needs to be implemented for Fp2 struct for use cases below
pub trait FieldExtConstructor<Fp: PrimeField, const DEGREE: usize> {
    fn new(c: [Fp; DEGREE]) -> Self;

    fn coeffs(&self) -> Vec<Fp>;
}

// Represent Fp2 point as FqPoint with degree = 2
// `Fp2 = Fp[u] / (u^2 + 1)`
// This implementation assumes p = 3 (mod 4) in order for the polynomial u^2 + 1 to be irreducible over Fp; i.e., in order for -1 to not be a square (quadratic residue) in Fp
// This means we store an Fp2 point as `a_0 + a_1 * u` where `a_0, a_1 in Fp`
pub struct Fp2Chip<F: FieldExt, Fp: PrimeField, Fp2: Field> {
    pub fp_chip: FpChip<F, Fp>,
    _marker: PhantomData<Fp2>,
}

impl<F: FieldExt, Fp: PrimeField, Fp2: Field + FieldExtConstructor<Fp, 2>> Fp2Chip<F, Fp, Fp2> {
    pub fn construct(config: FpConfig<F>) -> Self {
        Self {
            fp_chip: FpChip::construct(config),
            _marker: PhantomData,
        }
    }

    pub fn load_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        c: Fp2,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(2);
        for a in &c.coeffs() {
            let assigned_coeff = self
                .fp_chip
                .load_constant(layouter, BigInt::from(fe_to_biguint(a)))?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 2))
    }

    pub fn fp_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        fp_point: &CRTInteger<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.coeffs.len(), 2);
        assert_eq!(a.degree, 2);

        let mut out_coeffs = Vec::with_capacity(2);
        for c in &a.coeffs {
            let coeff = self.fp_chip.mul_no_carry(layouter, c, fp_point)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, 2))
    }

    pub fn conjugate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.coeffs.len(), 2);

        let neg_a1 = self.fp_chip.negate(layouter, &a.coeffs[1])?;
        Ok(FqPoint::construct(vec![a.coeffs[0].clone(), neg_a1], 2))
    }

    pub fn neg_conjugate(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.coeffs.len(), 2);

        let neg_a0 = self.fp_chip.negate(layouter, &a.coeffs[0])?;
        Ok(FqPoint::construct(vec![neg_a0, a.coeffs[1].clone()], 2))
    }
}

impl<F: FieldExt, Fp: PrimeField, Fp2: Field + FieldExtConstructor<Fp, 2>> FieldChip<F>
    for Fp2Chip<F, Fp, Fp2>
{
    type WitnessType = Vec<Option<BigInt>>;
    type FieldPoint = FqPoint<F>;
    type FieldType = Fp2;

    fn get_assigned_value(x: &FqPoint<F>) -> Option<Fp2> {
        assert_eq!(x.coeffs.len(), 2);
        let c0 = x.coeffs[0].value.clone();
        let c1 = x.coeffs[1].value.clone();
        c0.zip(c1)
            .map(|(c0, c1)| Fp2::new([bigint_to_fe(&c0), bigint_to_fe(&c1)]))
    }

    fn fe_to_witness(x: &Option<Fp2>) -> Vec<Option<BigInt>> {
        match x.as_ref() {
            None => vec![None, None],
            Some(x) => {
                let coeffs = x.coeffs();
                assert_eq!(coeffs.len(), 2);
                coeffs
                    .iter()
                    .map(|c| Some(BigInt::from(fe_to_biguint(c))))
                    .collect()
            }
        }
    }

    fn load_private(
        &self,
        layouter: &mut impl Layouter<F>,
        coeffs: Vec<Option<BigInt>>,
    ) -> Result<FqPoint<F>, Error> {
        let mut assigned_coeffs = Vec::with_capacity(2);
        for a in coeffs {
            let assigned_coeff = self.fp_chip.load_private(layouter, a.clone())?;
            assigned_coeffs.push(assigned_coeff);
        }
        Ok(FqPoint::construct(assigned_coeffs, 2))
    }

    // signed overflow BigInt functions
    fn add_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .add_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn sub_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .sub_no_carry(layouter, &a.coeffs[i], &b.coeffs[i])?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn negate(&self, layouter: &mut impl Layouter<F>, a: &FqPoint<F>) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let out_coeff = self.fp_chip.negate(layouter, a_coeff)?;
            out_coeffs.push(out_coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn scalar_mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: F,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for i in 0..a.degree {
            let coeff = self
                .fp_chip
                .scalar_mul_no_carry(layouter, &a.coeffs[i], b)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn mul_no_carry(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
        b: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        assert_eq!(a.degree, b.degree);
        // (a_0 + a_1 * u) * (b_0 + b_1 * u) = (a_0 b_0 - a_1 b_1) + (a_0 b_1 + a_1 b_0) * u
        let mut ab_coeffs = Vec::with_capacity(a.degree * b.degree);
        for i in 0..a.degree {
            for j in 0..b.degree {
                let coeff = self
                    .fp_chip
                    .mul_no_carry(layouter, &a.coeffs[i], &b.coeffs[j])?;
                ab_coeffs.push(coeff);
            }
        }
        let a0b0_minus_a1b1 = self.fp_chip.sub_no_carry(
            layouter,
            &ab_coeffs[0 * b.degree + 0],
            &ab_coeffs[1 * b.degree + 1],
        )?;
        let a0b1_plus_a1b0 = self.fp_chip.add_no_carry(
            layouter,
            &ab_coeffs[0 * b.degree + 1],
            &ab_coeffs[1 * b.degree + 0],
        )?;

        let mut out_coeffs = Vec::with_capacity(a.degree);
        out_coeffs.push(a0b0_minus_a1b1);
        out_coeffs.push(a0b1_plus_a1b0);

        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn check_carry_mod_to_zero(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<(), Error> {
        for coeff in &a.coeffs {
            self.fp_chip.check_carry_mod_to_zero(layouter, coeff)?;
        }
        Ok(())
    }

    fn carry_mod(
        &self,
        layouter: &mut impl Layouter<F>,
        a: &FqPoint<F>,
    ) -> Result<FqPoint<F>, Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.carry_mod(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(FqPoint::construct(out_coeffs, a.degree))
    }

    fn range_check(&self, layouter: &mut impl Layouter<F>, a: &FqPoint<F>) -> Result<(), Error> {
        let mut out_coeffs = Vec::with_capacity(a.degree);
        for a_coeff in &a.coeffs {
            let coeff = self.fp_chip.range_check(layouter, a_coeff)?;
            out_coeffs.push(coeff);
        }
        Ok(())
    }

    fn is_zero(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &FqPoint<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let mut prev = None;
	for a_coeff in &a.coeffs {
	    let coeff = self.fp_chip.is_zero(layouter, a_coeff)?;
	    if let Some(p) = prev {
		let new = self.fp_chip.config.range
		    .qap_config.and(layouter, &Existing(&coeff), &Existing(&p))?;
		prev = Some(new);
	    } else {
		prev = Some(coeff);
	    }
	}
	Ok(prev.unwrap())
    }

    fn is_equal(
	&self,
	layouter: &mut impl Layouter<F>,
	a: &FqPoint<F>,
	b: &FqPoint<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
	let mut prev = None;
	for (a_coeff, b_coeff) in a.coeffs.iter().zip(b.coeffs.clone()) {
	    let coeff = self.fp_chip.is_equal(layouter, a_coeff, &b_coeff)?;
	    if let Some(p) = prev {
		let new = self.fp_chip.config.range
		    .qap_config.and(layouter, &Existing(&coeff), &Existing(&p))?;
		prev = Some(new);
	    } else {
		prev = Some(coeff);
	    }
	}
	Ok(prev.unwrap())	
    }    
}
