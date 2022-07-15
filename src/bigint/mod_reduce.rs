use super::OverflowInteger;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*};
use num_bigint::BigUint as big_uint;
use num_traits::{One, Zero};

use crate::gates::qap_gate::QuantumCell;
use crate::gates::qap_gate::QuantumCell::*;
use crate::utils::modulus as native_modulus;
use crate::{gates::qap_gate, utils::*};

pub fn assign<F: FieldExt>(
    gate: &qap_gate::Config<F>,
    layouter: &mut impl Layouter<F>,
    a: &OverflowInteger<F>,
    desired_num_limbs: usize,
    modulus: big_uint,
) -> Result<OverflowInteger<F>, Error> {
    let n = a.limb_bits;
    let k = desired_num_limbs;

    assert!(k < a.limbs.len());
    assert!(modulus.bits() <= (n * k).try_into().unwrap());

    let m = a.limbs.len() - k;
    assert!(&a.max_limb_size * (1usize + (big_uint::from(m) << n)) <= native_modulus::<F>() / 2u32);

    let limb_base = big_uint::one() << n;
    let mut r_limbs: Vec<F> = Vec::with_capacity(m * k);

    // For i >= desired_num_limbs, compute r[i] = limb_base^i % modulus
    let mut r = limb_base.pow(k.try_into().unwrap()) % &modulus;
    for _i in k..a.limbs.len() {
        if _i > k {
            r = (r * &limb_base) % &modulus;
        }
        let mut r_temp = r.clone();
        for _j in 0..k {
            r_limbs.push(biguint_to_fe(&(&r_temp % &limb_base))); // r_limbs[ (i-k) * k + j ]
            r_temp = r_temp / &limb_base;
        }
        assert_eq!(r_temp, big_uint::zero());
    }

    let mut out_limbs = Vec::with_capacity(k);
    for j in 0..k {
        let out_limb = layouter.assign_region(
            || format!("mod_reduce_{}", j),
            |mut region| {
                let mut offset = 0;

                let mut r_computation: Vec<QuantumCell<F>> = Vec::with_capacity(3 * m + 1);
                r_computation.push(Existing(&a.limbs[j]));

                let mut out_val = a.limbs[j].value().map(|a| *a);
                for i in k..a.limbs.len() {
                    gate.q_enable.enable(&mut region, offset)?;

                    let r_val = r_limbs[(i - k) * k + j];
                    out_val = out_val
                        .zip(a.limbs[i].value())
                        .map(|(sum, c)| sum + r_val * *c);

                    r_computation.push(Constant(r_val));
                    r_computation.push(Existing(&a.limbs[i]));
                    r_computation.push(Witness(out_val));

                    offset += 3;
                }
                let r_computation_assigned = gate.assign_region(r_computation, 0, &mut region)?;
                Ok(r_computation_assigned.last().unwrap().clone())
            },
        )?;
        out_limbs.push(out_limb);
    }
    Ok(OverflowInteger::construct(
        out_limbs,
        &a.max_limb_size + big_uint::from(m) * &a.max_limb_size * (&limb_base - 1usize),
        a.limb_bits,
    ))
}
