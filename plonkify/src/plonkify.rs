use crate::{circuit::PlonkishCircuit, custom_gate::CustomizedGates, general::ExpandedCircuit};
use ark_ff::PrimeField;
use circom_compat::R1CSFile;

pub trait Plonkifier<F: PrimeField> {
    fn plonkify(r1cs: &R1CSFile<F>) -> (PlonkishCircuit<F>, Vec<F>);
}

pub trait GeneralPlonkifer<F: PrimeField> {
    fn plonkify(circuit: &ExpandedCircuit<F>, gate: &CustomizedGates) -> (PlonkishCircuit<F>, Vec<F>);
}
