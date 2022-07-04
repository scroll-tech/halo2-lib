use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::{FieldExt, Field},
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, },
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
struct BigIntMultNoCarryConfig<F: FieldExt, const K: usize> {
    s_mul: Selector,
    a: Column<Advice>,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct BigIntMultNoCarryChip<F: FieldExt, const K: usize> {
    config: BigIntMultNoCarryConfig<F, K>,
}

impl<F: FieldExt, const K: usize> BigIntMultNoCarryChip<F, K> {
    pub fn construct(config: BigIntMultNoCarryConfig<F, { K }>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>)
		     -> BigIntMultNoCarryConfig<F, K> {
        let s_mul = meta.selector();
        let a = meta.advice_column();
	meta.enable_equality(a);

        for x in 0..(2 * K - 1) as u32 {
	    meta.create_gate("BigInt Lagrange", |meta| {
		let select_cell = meta.query_selector(s_mul);
		let a_vec: Vec<Expression<F>> = Vec::from_iter(0..K as u32).iter().map(|&idx| {
		    meta.query_advice(a, Rotation(idx.try_into().unwrap()))
		}).collect();

		let b_vec: Vec<Expression<F>> = Vec::from_iter(0..K as u32).iter().map(|&idx| {
		    meta.query_advice(a, Rotation((idx + K as u32).try_into().unwrap()))
		}).collect();

		let c_vec: Vec<Expression<F>> = Vec::from_iter(0..(2 * K - 1) as u32).iter().map(|&idx| {
		    meta.query_advice(a, Rotation((idx + 2 * K as u32).try_into().unwrap()))
		}).collect();

		let x_vec: Vec<Expression<F>> = Vec::from_iter(0..(2 * K - 1) as u32).iter().map(|&idx| {
		    Expression::Constant(F::from(u32::pow(x, idx) as u64))
		}).collect();

		let mut a_expr: Expression<F> = x_vec[0].clone() * a_vec[0].clone();
		for &idx in Vec::from_iter(0..K).iter().skip(1) {
		    a_expr = a_expr + x_vec[idx].clone() * a_vec[idx].clone();
		}
		let mut b_expr: Expression<F> = x_vec[0].clone() * b_vec[0].clone();
		for &idx in Vec::from_iter(0..K).iter().skip(1) {
		    b_expr = b_expr + x_vec[idx].clone() * b_vec[idx].clone();
		}
		let mut c_expr: Expression<F> = x_vec[0].clone() * c_vec[0].clone();
		for &idx in Vec::from_iter(0..(2 * K - 1)).iter().skip(1) {
		    c_expr = c_expr + x_vec[idx].clone() * c_vec[idx].clone();
		}
		
		vec![select_cell * (a_expr * b_expr - c_expr)]
	    });
	}
	
        BigIntMultNoCarryConfig {
            s_mul,
            a,
            _marker: PhantomData,
        }
    }

    pub fn assign_inputs(&self, mut layouter: impl Layouter<F>, a_vals: &[F], b_vals: &[F])
			 -> Result<(Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>), Error> {
	layouter.assign_region(
	    || "inputs",
	    |mut region| {
		let indices = Vec::from_iter(0..K);
		let a_assigned = indices.iter().map(|&idx| {
		    region.assign_advice(|| "inputs", self.config.a, idx, || Ok(a_vals[idx]))
		});
		let a_temp : Result<Vec<AssignedCell<F, F>>, Error> = a_assigned.into_iter().collect();
		
		let b_assigned = indices.iter().map(|&idx| {
		    region.assign_advice(|| "inputs", self.config.a, idx + K, || Ok(b_vals[idx]))
		});
		let b_temp : Result<Vec<AssignedCell<F, F>>, Error> = b_assigned.into_iter().collect();

		a_temp.and_then(|a| Ok((a, b_temp?)))
	    }
	)
    }
    
    pub fn assign(&self,
		  mut layouter: impl Layouter<F>,
		  a: Vec<AssignedCell<F, F>>,
		  b: Vec<AssignedCell<F, F>>)
		  -> Result<(), Error> {
        layouter.assign_region(
            || "BigIntMultNoCarry",
            |mut region| {
                self.config.s_mul.enable(&mut region, 0)?;
		for idx in 0..K {
		    a[idx].copy_advice(|| "lhs", &mut region, self.config.a, idx)?;
		    b[idx].copy_advice(|| "rhs", &mut region, self.config.a, idx + K)?;
		}

		let mut c_vals = vec![F::from(0 as u64); 2 * K - 1];
		for idx in 0..(2 * K - 1) {
		    for idx2 in 0..(idx + 1) {
			if idx2 < K && idx - idx2 < K {
			    match a[idx2].value() {
				Some(&av) => match b[idx - idx2].value() {
				    Some(&bv) => c_vals[idx] = c_vals[idx] + av * bv,
				    None => ()
				},
				None => ()
			    }
			}
		    }
                    region.assign_advice(|| "lhs * rhs", self.config.a, idx + 2 * K, || Ok(c_vals[idx]))?;
		}
		Ok(())
            },
        )
    }
}

#[derive(Default)]
struct TestCircuit<F: Field, const K: usize> {
    a_vals: Vec<F>,
    b_vals: Vec<F>,
}

impl<F: FieldExt, const K: usize> Circuit<F> for TestCircuit<F, { K }> {
    type Config = BigIntMultNoCarryConfig<F, K>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        BigIntMultNoCarryChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
	let chip = BigIntMultNoCarryChip::construct(config);
	let (a_assigned, b_assigned) = chip.assign_inputs(layouter.namespace(|| "inputs"), self.a_vals.as_slice(), self.b_vals.as_slice())?;
        chip.assign(layouter.namespace(||"actual circuit"), a_assigned, b_assigned)?;
        Ok(())
    }
}

mod tests {
    use super::TestCircuit;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fn};

    #[test]
    fn test_bigintmult1() {
        let k = 6;
        let circuit = TestCircuit::<Fn, 5> {
            a_vals: vec![Fn::from(1), Fn::from(3), Fn::from(0), Fn::from(0), Fn::from(0)],
            b_vals: vec![Fn::from(1), Fn::from(4), Fn::from(0), Fn::from(0), Fn::from(0)],
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_bigintmult1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("bigintmult1.png", (1024, 1024)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("BigIntMult1", ("sans-serif", 60)).unwrap();

        let circuit = TestCircuit::<Fn, 5> {
            a_vals: vec![Fn::from(1), Fn::from(1), Fn::from(0), Fn::from(0), Fn::from(0)],
            b_vals: vec![Fn::from(1), Fn::from(2), Fn::from(0), Fn::from(0), Fn::from(0)],
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(6, &circuit, &root)
            .unwrap();
    }
}
