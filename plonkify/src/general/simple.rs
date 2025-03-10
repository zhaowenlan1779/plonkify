use std::cmp::Reverse;
use std::collections::BTreeSet;

use crate::{
    circuit::{PlonkishCircuit, PlonkishCircuitParams},
    custom_gate::{CustomizedGates, GateInfo},
    general::ExpansionConfig,
    plonkify::GeneralPlonkifer,
    selectors::SelectorColumn,
};
use ark_ff::PrimeField;
use ark_poly::multivariate::{SparsePolynomial, SparseTerm, Term};
use circom_compat::R1CSFile;

use super::ExpandedCircuit;

pub struct SimpleGeneralPlonkifier<F: PrimeField> {
    constraint_selectors: Vec<SelectorColumn<F>>,
    constraint_variables: Vec<Vec<usize>>,
    variable_assignments: Vec<F>,
}

fn get_quotient_term(term: &SparseTerm, divisor: &SparseTerm) -> Option<SparseTerm> {
    if divisor.is_empty() {
        return Some(term.clone());
    }

    let mut divisor_idx = 0;
    let mut result_terms = vec![];
    for &(var, power) in &**term {
        if divisor_idx >= divisor.len() {
            result_terms.push((var, power));
            continue;
        }

        let (divisor_var, divisor_power) = divisor[divisor_idx];
        if divisor_var < var {
            // We are missing variables
            return None;
        }
        if divisor_var > var {
            // Skip until we reach the divisor variable
            result_terms.push((var, power));
            continue;
        }

        if divisor_power > power {
            return None;
        }
        result_terms.push((var, power - divisor_power));
        divisor_idx += 1;
    }
    if divisor_idx < divisor.len() {
        return None;
    }
    Some(SparseTerm::new(result_terms))
}

impl<F: PrimeField> SimpleGeneralPlonkifier<F> {
    fn add_selectors(&mut self, values: Vec<F>) {
        for (i, selector) in values.iter().enumerate() {
            self.constraint_selectors[i].0.push(*selector);
        }
    }

    // Note that assigned_vars must be sorted
    fn match_term_to_gate(
        term: &SparseTerm,
        gate: &GateInfo,
        gate_idx: usize,
        order_idx: usize,
        mut assigned_vars: Vec<isize>,
        require_exact: bool,
    ) -> Option<(SparseTerm, usize, Vec<isize>)> {
        let order = &gate.orders[order_idx];
        let gate = &gate.gates[gate_idx];
        let mut terms = term.to_vec();
        let mut reduced_degrees = 0;
        // First, check if already assigned variables are satisfied
        for (var, power) in gate {
            let real_var = assigned_vars[*var];
            if real_var == -1 {
                continue;
            }

            let real_var = real_var as usize;
            let idx = match terms.binary_search(&(real_var, 0)) {
                Ok(val) => val,
                Err(val) => val,
            };
            if idx >= terms.len() || terms[idx].0 != real_var || terms[idx].1 < *power {
                return None;
            }
            terms[idx].1 -= *power;
            reduced_degrees += *power;
        }

        // Annoyingly there is no proper way to write a recursive closure
        // (especially since this mutates, so it's probably almost impossible)

        fn dfs(
            gate: &Vec<(usize, usize)>,
            order: &Vec<usize>,
            gate_term_idx: usize,
            reduced_degrees: usize,
            assigned_vars: &mut Vec<isize>,
            terms: &mut Vec<(usize, usize)>,
            out: &mut Option<(usize, isize, Vec<(usize, usize)>, Vec<isize>)>,
        ) {
            if gate_term_idx >= gate.len() {
                let mut should_replace = *out == None;

                let mut width = 0;
                let mut last_var = -1;
                let mut sorted_assigned_vars = assigned_vars.clone();
                sorted_assigned_vars.sort();
                for var in sorted_assigned_vars.iter() {
                    if *var != -1 && *var != last_var {
                        last_var = *var;
                        width += 1;
                    }
                }

                if let Some((cur_reduced_degrees, cur_width, _, _)) = out {
                    if reduced_degrees > *cur_reduced_degrees
                        || (reduced_degrees == *cur_reduced_degrees && width > *cur_width)
                    {
                        should_replace = true;
                    }
                }
                if should_replace {
                    *out = Some((reduced_degrees, width, terms.clone(), assigned_vars.clone()));
                }
                return;
            }

            let (idx, power) = gate[gate_term_idx];
            if assigned_vars[idx] != -1 {
                return dfs(
                    gate,
                    order,
                    gate_term_idx + 1,
                    reduced_degrees,
                    assigned_vars,
                    terms,
                    out,
                );
            }

            let lower = assigned_vars
                .iter()
                .enumerate()
                .filter_map(|(i, var)| {
                    if *var != -1 && order[i] < order[idx] {
                        Some(*var as usize)
                    } else {
                        None
                    }
                })
                .max()
                .unwrap_or(0);
            let upper = assigned_vars
                .iter()
                .enumerate()
                .filter_map(|(i, var)| {
                    if *var != -1 && order[i] > order[idx] {
                        Some(*var as usize)
                    } else {
                        None
                    }
                })
                .min()
                .unwrap_or(usize::MAX);
            for i in 0..terms.len() {
                let (var, term_power) = terms[i];
                if term_power < power || var < lower || var > upper {
                    continue;
                }
                assigned_vars[idx] = var as isize;
                terms[i].1 -= power;
                dfs(
                    gate,
                    order,
                    gate_term_idx + 1,
                    reduced_degrees + power,
                    assigned_vars,
                    terms,
                    out,
                );
                terms[i].1 += power;
                assigned_vars[idx] = -1;
            }
            if lower == 0 {
                assigned_vars[idx] = 0;
                dfs(
                    gate,
                    order,
                    gate_term_idx + 1,
                    reduced_degrees,
                    assigned_vars,
                    terms,
                    out,
                );
                assigned_vars[idx] = -1;
            }
        }

        let mut out = None;
        dfs(
            gate,
            order,
            0,
            reduced_degrees,
            &mut assigned_vars,
            &mut terms,
            &mut out,
        );
        if let Some((reduced_degrees, _, terms, assigned_vars)) = out {
            if reduced_degrees == 0 {
                return None;
            }
            let term = SparseTerm::new(terms);
            if require_exact && !term.is_empty() {
                None
            } else {
                Some((term, reduced_degrees, assigned_vars))
            }
        } else {
            None
        }
    }

    fn search_gate(
        terms: &[(F, SparseTerm)],
        divisor: &SparseTerm,
        start_term_idx: usize,
        skip_term_idx: usize,
        gate: &GateInfo,
        order_idx: usize,
        mut assigned_vars: Vec<isize>,
        mut total_reduced_degrees: usize,
        updated_terms: &mut Vec<usize>,
        selectors: &mut Vec<F>,
        out: &mut Option<(SparseTerm, Vec<usize>, Vec<F>, Vec<isize>, usize)>,
    ) {
        let divisor_degree = divisor.degree();
        for term_idx in start_term_idx..terms.len() {
            let (coeff, term) = &terms[term_idx];
            if coeff.is_zero() || term_idx == skip_term_idx {
                continue;
            }
            let is_linear = term.len() == 1 && term[0].1 == 1;
            // Only handle linear terms if the divisor itself is linear, i.e. there
            // is a chance that we can reduce the term to a constant
            // If the divisor is one, linear terms are handled separately below
            // If the divisor is higher-degree, linear terms cannot be used anyways
            if is_linear && divisor_degree != 1 {
                continue;
            }

            if let Some(quotient_term) = get_quotient_term(term, divisor) {
                if quotient_term.is_empty() {
                    updated_terms.push(term_idx);
                    *selectors.last_mut().unwrap() += coeff;
                    Self::search_gate(
                        terms,
                        divisor,
                        term_idx + 1,
                        skip_term_idx,
                        gate,
                        order_idx,
                        assigned_vars,
                        total_reduced_degrees + divisor_degree,
                        updated_terms,
                        selectors,
                        out,
                    );
                    *selectors.last_mut().unwrap() -= coeff;
                    updated_terms.pop();
                    return;
                }

                for gate_idx in 0..gate.gates.len() {
                    if gate.is_linear[gate_idx] || !selectors[gate_idx].is_zero() {
                        continue;
                    }
                    if let Some((_, reduced_degrees, assigned_vars)) = Self::match_term_to_gate(
                        &quotient_term,
                        gate,
                        gate_idx,
                        order_idx,
                        assigned_vars.clone(),
                        true,
                    ) {
                        updated_terms.push(term_idx);
                        selectors[gate_idx] = *coeff;
                        Self::search_gate(
                            terms,
                            divisor,
                            term_idx + 1,
                            skip_term_idx,
                            gate,
                            order_idx,
                            assigned_vars,
                            total_reduced_degrees + divisor_degree + reduced_degrees,
                            updated_terms,
                            selectors,
                            out,
                        );
                        selectors[gate_idx] = F::zero();
                        updated_terms.pop();
                    }
                }

                Self::search_gate(
                    terms,
                    divisor,
                    term_idx + 1,
                    skip_term_idx,
                    gate,
                    order_idx,
                    assigned_vars,
                    total_reduced_degrees,
                    updated_terms,
                    selectors,
                    out,
                );
                return;
            }
        }

        // Finished processing high-degree terms
        // Add as many linear terms as possible
        let mut selectors_backup = None;
        let mut updated_terms_backup = None;
        if divisor.is_empty() {
            selectors_backup = Some(selectors.clone());
            updated_terms_backup = Some(updated_terms.clone());
            for &(var_idx, selector_idx) in &gate.linear_terms {
                let actual_var = assigned_vars[var_idx];
                if actual_var == -1 {
                    if let Some(term_idx) =
                        terms.iter().enumerate().position(|(i, (coeff, term))| {
                            !coeff.is_zero()
                                && term.len() == 1
                                && term[0].1 == 1
                                && !updated_terms.contains(&i)
                        })
                    {
                        let (coeff, term) = &terms[term_idx];
                        assigned_vars[var_idx] = term[0].0 as isize;
                        selectors[selector_idx] = *coeff;
                        updated_terms.push(term_idx);
                        total_reduced_degrees += 1;
                    } else {
                        break;
                    }
                } else {
                    if let Some(term_idx) =
                        terms.iter().enumerate().position(|(i, (coeff, term))| {
                            !coeff.is_zero()
                                && term.len() == 1
                                && term[0] == (actual_var as usize, 1)
                                && !updated_terms.contains(&i)
                        })
                    {
                        let (coeff, _) = &terms[term_idx];
                        selectors[selector_idx] = *coeff;
                        updated_terms.push(term_idx);
                        total_reduced_degrees += 1;
                    }
                }
            }
        }

        if *out == None || out.as_ref().unwrap().4 < total_reduced_degrees {
            *out = Some((
                divisor.clone(),
                updated_terms.clone(),
                selectors.clone(),
                assigned_vars,
                total_reduced_degrees,
            ));
        }

        if selectors_backup != None {
            *selectors = selectors_backup.unwrap();
            *updated_terms = updated_terms_backup.unwrap();
        }
    }

    fn process_constraint(
        &mut self,
        constraint: &SparsePolynomial<F, SparseTerm>,
        gate: &GateInfo,
    ) {
        let mut constant = F::zero();
        let mut terms = constraint
            .terms
            .iter()
            .filter_map(|(coeff, term)| {
                if term.is_empty() {
                    constant += coeff;
                    None
                } else {
                    Some((*coeff, term.clone()))
                }
            })
            .collect::<Vec<_>>();

        let mut terms_queue = BTreeSet::new();
        for (term_idx, (_, term)) in terms.iter().enumerate() {
            terms_queue.insert((term.degree(), term_idx));
        }

        let selector_len = gate.num_selector_columns();
        while !terms_queue.is_empty() {
            let &(degree, term_idx) = terms_queue.last().unwrap();
            if degree <= 1 {
                break;
            }
            terms_queue.pop_last();

            let (coeff, term) = &terms[term_idx];

            let mut out = None;
            for order_idx in 0..gate.orders.len() {
                let mut compatible_gates = (0..gate.gates.len())
                    .filter_map(|i| {
                        Self::match_term_to_gate(
                            &term,
                            gate,
                            i,
                            order_idx,
                            vec![-1; gate.num_witness_columns() - 1],
                            false,
                        )
                        .map(|x| (i, x))
                    })
                    .collect::<Vec<_>>();
                compatible_gates
                    .sort_by_key(|(_, (_, reduced_degrees, _))| Reverse(*reduced_degrees));

                assert_ne!(compatible_gates.len(), 0);
                let best_reduced_degrees = compatible_gates.first().unwrap().1 .1;
                for (gate_idx, (remainder_term, reduced_degrees, assigned_vars)) in compatible_gates
                {
                    if reduced_degrees != best_reduced_degrees {
                        break;
                    }

                    let mut updated_terms = vec![];
                    let mut selectors = vec![F::zero(); selector_len];
                    selectors[gate_idx] = *coeff;

                    Self::search_gate(
                        &terms,
                        &remainder_term,
                        0,
                        term_idx,
                        gate,
                        order_idx,
                        assigned_vars,
                        reduced_degrees,
                        &mut updated_terms,
                        &mut selectors,
                        &mut out,
                    );
                }
            }

            let (divisor, updated_terms, mut selectors, assigned_vars, _) = out.unwrap();
            for updated_idx in updated_terms {
                // The first term is not included, so everything here should still be present in the queue
                let removed = terms_queue.remove(&(terms[updated_idx].1.degree(), updated_idx));
                assert!(removed);
                terms[updated_idx] = (F::zero(), SparseTerm::default());
            }
            terms[term_idx] = (F::zero(), SparseTerm::default());
            if divisor.is_empty() && terms_queue.is_empty() {
                // Final constraint
                // No output
                *selectors.last_mut().unwrap() += constant;
                self.add_selectors(selectors);

                let mut constraint_vars = assigned_vars
                    .into_iter()
                    .map(|x| if x == -1 { 0 } else { x as usize })
                    .collect::<Vec<_>>();
                constraint_vars.push(0); // No output
                self.constraint_variables.push(constraint_vars);

                return;
            } else {
                // Create new variable for the output
                let new_index = self.variable_assignments.len();
                let mut constraint_vars = assigned_vars
                    .into_iter()
                    .map(|x| if x == -1 { 0 } else { x as usize })
                    .collect::<Vec<_>>();
                self.variable_assignments.push(gate.evaluate_no_output(
                    &selectors,
                    &self.variable_assignments,
                    &constraint_vars,
                ));
                let new_term = SparseTerm::new(
                    divisor
                        .iter()
                        .chain([(new_index, 1)].iter())
                        .map(|x| *x)
                        .collect(),
                );
                terms_queue.insert((new_term.degree(), terms.len()));
                terms.push((F::one(), new_term));

                // Constraints
                selectors[selector_len - 2] = -F::one(); // Output
                self.add_selectors(selectors);

                constraint_vars.push(new_index); // Output
                self.constraint_variables.push(constraint_vars);
            }
        }

        // Complete linear terms
        let num_linear_terms = gate.linear_terms.len();

        let mut cur_selectors = vec![F::zero(); selector_len];
        let mut cur_vars = vec![0; gate.num_witness_columns()];
        let mut linear_term_idx = 0;
        let mut sum = F::zero();
        while !terms_queue.is_empty() {
            let (_, term_idx) = terms_queue.pop_first().unwrap();
            let (coeff, term) = &terms[term_idx];

            let (var_idx, selector_idx) = gate.linear_terms[linear_term_idx];
            cur_selectors[selector_idx] = *coeff;
            let variable = term.first().unwrap().0;
            cur_vars[var_idx] = variable;
            sum += *coeff * self.variable_assignments[variable];

            linear_term_idx += 1;
            if linear_term_idx >= num_linear_terms {
                if terms_queue.len() == 1 {
                    // One last linear term can be accomodated by the output variable
                    let (_, term_idx) = terms_queue.pop_first().unwrap();
                    let (coeff, term) = &terms[term_idx];
                    cur_selectors[selector_len - 2] = *coeff;
                    *cur_vars.last_mut().unwrap() = term.first().unwrap().0;
                    break;
                } else if terms_queue.len() == 0 {
                    break;
                }

                let new_index = self.variable_assignments.len();
                self.variable_assignments.push(sum);
                let new_term = SparseTerm::new(vec![(new_index, 1)]);
                terms_queue.insert((1, terms.len()));
                terms.push((F::one(), new_term));

                cur_selectors[selector_len - 2] = -F::one(); // Output
                self.add_selectors(cur_selectors.clone());
                *cur_vars.last_mut().unwrap() = new_index;
                self.constraint_variables.push(cur_vars.clone());

                cur_selectors.fill(F::zero());
                cur_vars.fill(0);
                sum = F::zero();

                linear_term_idx = 0;
            }
        }

        // Final constraint
        *cur_selectors.last_mut().unwrap() = constant;
        self.add_selectors(cur_selectors);
        self.constraint_variables.push(cur_vars);
    }
}

impl<F: PrimeField> GeneralPlonkifer<F> for SimpleGeneralPlonkifier<F> {
    fn plonkify(r1cs: &R1CSFile<F>, gate: &CustomizedGates) -> (PlonkishCircuit<F>, Vec<F>) {
        let circuit = ExpandedCircuit::<F>::preprocess(&r1cs, ExpansionConfig::MaxCost(50));
        println!(
            "Expanded circuit constraints: {}",
            circuit.constraints.len()
        );

        let mut data = Self {
            constraint_selectors: vec![SelectorColumn::<F>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: circuit.witness.clone(),
        };

        // Create constraints for public inputs
        for i in 0..circuit.num_public_inputs {
            data.add_selectors(vec![F::zero(); gate.num_selector_columns()]);
            let mut variables = vec![i as usize];
            variables.resize(gate.num_witness_columns(), 0);
            data.constraint_variables.push(variables);
        }

        let gate_info = GateInfo::jellyfish_turbo_plonk_gate();
        for constraint in &circuit.constraints {
            data.process_constraint(constraint, &gate_info);
        }

        let num_constraints = data.constraint_variables.len();
        let mut variable_uses = vec![vec![]; data.variable_assignments.len()];
        for (constraint_idx, variables) in data.constraint_variables.iter().enumerate() {
            for (col, variable) in variables.iter().enumerate() {
                variable_uses[*variable].push(col * num_constraints + constraint_idx);
            }
        }

        // Start from identity permutation
        let mut permutation = vec![F::zero(); gate.num_witness_columns() * num_constraints];
        for i in 1..permutation.len() {
            permutation[i] = permutation[i - 1] + F::one();
        }
        for uses in variable_uses {
            for i in 0..uses.len() {
                let next = if i == uses.len() - 1 { 0 } else { i + 1 };
                permutation[uses[i]] = F::from_u64(uses[next] as u64).unwrap();
            }
        }

        let mut witness = vec![F::zero(); gate.num_witness_columns() * num_constraints];
        for (constraint_idx, variables) in data.constraint_variables.iter().enumerate() {
            for (col, variable_idx) in variables.iter().enumerate() {
                witness[col * num_constraints + constraint_idx] =
                    data.variable_assignments[*variable_idx];
            }
        }

        (
            PlonkishCircuit {
                permutation,
                selectors: data.constraint_selectors,
                params: PlonkishCircuitParams {
                    num_constraints,
                    num_pub_input: circuit.num_public_inputs,
                    gate_func: gate.clone(),
                },
            },
            witness,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use ark_poly::DenseMVPolynomial;
    use ark_std::{One, Zero};

    #[test]
    fn test_get_quotient_term() {
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 7)]),
                &SparseTerm::new(vec![(1, 5)])
            ),
            Some(SparseTerm::new(vec![(1, 2)]))
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (2, 2)]),
                &SparseTerm::new(vec![(1, 2)])
            ),
            Some(SparseTerm::new(vec![(2, 2)]))
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (2, 2), (3, 3)]),
                &SparseTerm::new(vec![(2, 1)])
            ),
            Some(SparseTerm::new(vec![(1, 2), (2, 1), (3, 3)]))
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (2, 2)]),
                &SparseTerm::new(vec![(1, 4)])
            ),
            None
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (2, 2)]),
                &SparseTerm::new(vec![(2, 4)])
            ),
            None
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (3, 2)]),
                &SparseTerm::new(vec![(2, 2)])
            ),
            None
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(1, 2), (3, 2)]),
                &SparseTerm::new(vec![(5, 2)])
            ),
            None
        );
        assert_eq!(
            get_quotient_term(
                &SparseTerm::new(vec![(2, 2), (3, 2)]),
                &SparseTerm::new(vec![(1, 2)])
            ),
            None
        );
    }

    fn check_satisfied(gate: &GateInfo, data: &SimpleGeneralPlonkifier<Fr>) {
        for (row, variables) in data.constraint_variables.iter().enumerate() {
            let selectors = data
                .constraint_selectors
                .iter()
                .map(|column| column.0[row])
                .collect::<Vec<_>>();
            assert_eq!(
                gate.evaluate(&selectors, &data.variable_assignments, &variables,),
                Fr::zero()
            );
        }
    }

    #[test]
    fn test_single_constraint() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![
                Fr::one(),
                Fr::from_u64(2).unwrap(),
                Fr::from_u64(32).unwrap(),
            ],
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (Fr::one(), SparseTerm::new(vec![(1, 5)])),
                (Fr::from_u64(2).unwrap(), SparseTerm::new(vec![(1, 4)])),
                (Fr::from_u64(3).unwrap(), SparseTerm::new(vec![(1, 2)])),
                (Fr::from_u64(4).unwrap(), SparseTerm::new(vec![(1, 1)])),
                (-Fr::from_u64(84).unwrap(), SparseTerm::new(vec![])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 1);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_2() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![
                Fr::one(),
                Fr::from_u64(2).unwrap(),
                Fr::from_u64(3).unwrap(),
            ],
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (Fr::one(), SparseTerm::new(vec![(1, 2), (2, 1)])),
                (-Fr::from_u64(12).unwrap(), SparseTerm::new(vec![])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 1);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_3() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![
                Fr::one(),
                Fr::from_u64(2).unwrap(),
                Fr::from_u64(3).unwrap(),
            ],
        };
        let constraint = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (Fr::one(), SparseTerm::new(vec![(1, 7)])),
                (
                    Fr::from_u64(2).unwrap(),
                    SparseTerm::new(vec![(1, 2), (2, 2)]),
                ),
                (-Fr::from_u64(200).unwrap(), SparseTerm::new(vec![])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 2);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_4() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![
                Fr::one(),
                Fr::from_u64(1).unwrap(),
                Fr::from_u64(2).unwrap(),
                Fr::from_u64(3).unwrap(),
                Fr::from_u64(4).unwrap(),
                Fr::from_u64(5).unwrap(),
                Fr::from_u64(6).unwrap(),
            ],
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            7,
            vec![
                (
                    Fr::one(),
                    SparseTerm::new(vec![(1, 1), (2, 2), (3, 1), (4, 1), (5, 1), (6, 1)]),
                ),
                (-Fr::from_u64(1440).unwrap(), SparseTerm::new(vec![])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 2);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_5() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: (0..102).map(|i| Fr::from_u64(i).unwrap()).collect(),
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            102,
            (0..102)
                .map(|i| {
                    if i == 0 {
                        (-Fr::from_u64(5151).unwrap(), SparseTerm::new(vec![]))
                    } else {
                        (Fr::one(), SparseTerm::new(vec![(i as usize, 1)]))
                    }
                })
                .collect(),
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 33);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_6() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: (0..102).map(|i| Fr::from_u64(i).unwrap()).collect(),
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            102,
            (0..102)
                .map(|i| {
                    if i == 0 {
                        (-Fr::from_u64(14950).unwrap(), SparseTerm::new(vec![]))
                    } else if i == 101 {
                        (
                            Fr::one(),
                            SparseTerm::new(vec![((i - 1) as usize, 1), ((i - 2) as usize, 1)]),
                        )
                    } else {
                        (Fr::one(), SparseTerm::new(vec![(i as usize, 1)]))
                    }
                })
                .collect(),
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 33);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_7() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![
                Fr::one(),
                Fr::from_u64(2).unwrap(),
                Fr::from_u64(3).unwrap(),
            ],
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (-Fr::from_u64(272).unwrap(), SparseTerm::new(vec![])),
                (Fr::one(), SparseTerm::new(vec![(1, 8)])),
                (Fr::from_u64(2).unwrap(), SparseTerm::new(vec![(1, 3)])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 2);
        check_satisfied(&gate, &data);
    }

    #[test]
    fn test_single_constraint_8() {
        let gate = GateInfo::jellyfish_turbo_plonk_gate();
        let mut data = SimpleGeneralPlonkifier {
            constraint_selectors: vec![SelectorColumn::<Fr>(vec![]); gate.num_selector_columns()],
            constraint_variables: Vec::new(),
            variable_assignments: vec![Fr::one(), Fr::one(), Fr::zero(), Fr::one(), Fr::zero()],
        };

        let constraint = SparsePolynomial::from_coefficients_vec(
            5,
            vec![
                (Fr::one(), SparseTerm::new(vec![(4, 1)])),
                (-Fr::one(), SparseTerm::new(vec![(1, 1)])),
                (-Fr::one(), SparseTerm::new(vec![(2, 1), (3, 1)])),
                (Fr::one(), SparseTerm::new(vec![(1, 1), (3, 1)])),
            ],
        );

        data.process_constraint(&constraint, &gate);
        assert_eq!(data.constraint_variables.len(), 2);
        check_satisfied(&gate, &data);
    }
}
