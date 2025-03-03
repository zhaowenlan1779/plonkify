use ark_bn254::Fr;
use circom_compat::{read_witness, R1CSFile};
use clap::Parser;
use plonkify::{
    general::ExpandedCircuit, vanilla::{GreedyBruteForcePlonkifier, OptimizedPlonkifier, SimplePlonkifer}, Plonkifier
};
use std::fs::File;
use std::io::BufReader;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    /// Optimization level
    #[arg(short = 'O', default_value_t = 1, value_parser = clap::value_parser!(u8).range(..3))]
    optimize: u8,

    /// R1CS circuit file (e.g. circuit.r1cs)
    circuit: String,

    /// JSON witness file (e.g. witness.json)
    witness: String,
}

fn main() {
    let cli = Cli::parse();

    let reader = BufReader::new(File::open(cli.circuit).unwrap());
    let mut file = R1CSFile::<Fr>::new(reader).unwrap();

    let witness_reader = BufReader::new(File::open(cli.witness).unwrap());
    file.witness = read_witness::<Fr>(witness_reader);

    println!("R1CS num constraints: {}", file.header.n_constraints);

    // let expanded = ExpandedCircuit::<Fr>::preprocess(&file);
    // println!("Expanded circuit constraints: {}", expanded.constraints.len());
    // return;

    let (plonkish_circuit, plonkish_witness) = match cli.optimize {
        0 => SimplePlonkifer::<Fr>::plonkify(&file),
        1 => OptimizedPlonkifier::<Fr>::plonkify(&file),
        2 => GreedyBruteForcePlonkifier::<Fr>::plonkify(&file),
        _ => panic!("Unexpected optimizization level"),
    };

    println!(
        "Plonk num constraints: {}",
        plonkish_circuit.params.num_constraints
    );
    assert!(plonkish_circuit.is_satisfied(&plonkish_witness));
}
