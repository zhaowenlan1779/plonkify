use crate::circuit::PlonkishCircuit;
use ark_ff::PrimeField;
use circom_compat::R1CSFile;

pub trait Plonkifier<F: PrimeField> {
    fn plonkify(r1cs: &R1CSFile<F>) -> (PlonkishCircuit<F>, Vec<F>);
}
