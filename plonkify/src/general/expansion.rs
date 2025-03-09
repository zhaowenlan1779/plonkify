use ark_ff::{PrimeField, Zero};
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm, Term},
    DenseMVPolynomial, Polynomial,
};
use circom_compat::R1CSFile;
use rayon::prelude::*;
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::iter::zip;
use std::mem::take;

pub(super) fn term_mul_by_term(cur: &SparseTerm, other: &SparseTerm) -> SparseTerm {
    if cur.is_empty() {
        return other.clone();
    }
    if other.is_empty() {
        return cur.clone();
    }
    SparseTerm::new((**cur).iter().chain((**other).iter()).map(|x| *x).collect())
}

pub(super) fn poly_mul_by_term<F: PrimeField>(
    cur: &mut SparsePolynomial<F, SparseTerm>,
    coeff: F,
    other: &SparseTerm,
) {
    // Note: the sparse polynomial is sorted; multiplying by the same term does not affect the ordering
    cur.terms.iter_mut().for_each(|(cur_coeff, cur_term)| {
        *cur_coeff *= coeff;
        *cur_term = term_mul_by_term(cur_term, other);
    });
}

pub(super) fn naive_mul<F: PrimeField>(
    cur: &SparsePolynomial<F, SparseTerm>,
    other: &SparsePolynomial<F, SparseTerm>,
) -> SparsePolynomial<F, SparseTerm> {
    if cur.is_zero() || other.is_zero() {
        SparsePolynomial::zero()
    } else {
        let mut result_terms = Vec::new();
        for (cur_coeff, cur_term) in cur.terms.iter() {
            for (other_coeff, other_term) in other.terms.iter() {
                result_terms.push((
                    *cur_coeff * *other_coeff,
                    term_mul_by_term(cur_term, other_term),
                ));
            }
        }
        SparsePolynomial::from_coefficients_vec(cur.num_vars, result_terms)
    }
}

fn substitute<F: PrimeField>(
    cur: &SparsePolynomial<F, SparseTerm>,
    variable: usize,
    subst: &SparsePolynomial<F, SparseTerm>,
) -> Option<SparsePolynomial<F, SparseTerm>> {
    let is_zero = subst.is_zero();
    let is_single_term = subst.terms.len() <= 1;
    let mut already_used = false;

    let mut result_terms = Vec::new();
    for (coeff, term) in cur.terms.iter() {
        let item_to_subst = (**term).iter().find(|(var, _)| *var == variable);
        if let Some((_, power)) = item_to_subst {
            if is_zero {
                continue;
            }
            if is_single_term {
                let new_term = SparseTerm::new(
                    (**term)
                        .iter()
                        .filter(|(var, _)| *var != variable)
                        .map(|x| *x)
                        .chain(subst.terms[0].1.iter().map(|(x, y)| (*x, *y * *power)))
                        .collect::<Vec<_>>(),
                );
                if *power == 1 {
                    result_terms.push((*coeff * subst.terms[0].0, new_term));
                } else {
                    result_terms.push((*coeff * subst.terms[0].0.pow([*power as u64]), new_term));
                }
                continue;
            }

            if *power > 1 || already_used {
                // It's probably not worth it to inline
                return None;
            }
            already_used = true;

            let mut new_poly = subst.clone();
            let remainder_term = SparseTerm::new(
                (**term)
                    .iter()
                    .filter(|(var, _)| *var != variable)
                    .map(|x| *x)
                    .collect::<Vec<_>>(),
            );
            poly_mul_by_term(&mut new_poly, *coeff, &remainder_term);
            result_terms.append(&mut new_poly.terms);
        } else {
            result_terms.push((*coeff, term.clone()));
        }
    }
    Some(SparsePolynomial::from_coefficients_vec(
        cur.num_vars,
        result_terms,
    ))
}

pub struct ExpandedCircuit<F: PrimeField> {
    pub num_public_inputs: usize,
    pub constraints: Vec<SparsePolynomial<F, SparseTerm>>,
    pub witness: Vec<F>,
}

fn get_poly_weight<F: PrimeField>(poly: &SparsePolynomial<F, SparseTerm>) -> usize {
    poly.terms
        .iter()
        .map(|(_, term)| (**term).iter().map(|(_, deg)| *deg).sum::<usize>())
        .sum()
}

pub enum ExpansionConfig {
    None,
    MaxWidth(usize),
    MaxDegree(usize),
    MaxCost(usize),
}

impl ExpansionConfig {
    fn check_poly<F: PrimeField>(&self, poly: &SparsePolynomial<F, SparseTerm>) -> bool {
        match self {
            ExpansionConfig::None => true,
            ExpansionConfig::MaxWidth(width) => poly.terms.len() <= *width,
            ExpansionConfig::MaxDegree(degree) => poly.degree() <= *degree,
            ExpansionConfig::MaxCost(max_cost) => get_poly_weight(poly) <= *max_cost,
        }
    }
}

impl<F: PrimeField> ExpandedCircuit<F> {
    fn poly_from_lc(lc: &[(usize, F)]) -> SparsePolynomial<F, SparseTerm> {
        // num_vars don't actually matter at all.. except for being checked
        SparsePolynomial::from_coefficients_vec(
            usize::MAX,
            lc.iter()
                .map(|(var, coeff)| {
                    if *var == 0 {
                        (*coeff, SparseTerm::new(vec![]))
                    } else {
                        (*coeff, SparseTerm::new(vec![(*var, 1)]))
                    }
                })
                .collect(),
        )
    }

    fn evaluate_lc(lc: &[(usize, F)], witness: &[F]) -> F {
        lc.iter()
            .map(|(var, coeff)| *coeff * witness[*var])
            .sum::<F>()
    }

    // (linear terms, dependencies)
    fn get_constraint_dependencies(
        num_public_input: usize,
        constraint_poly: &SparsePolynomial<F, SparseTerm>,
    ) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let mut linear_terms = BTreeSet::new();
        let mut high_order_dependencies = BTreeSet::new();
        for (_, term) in &constraint_poly.terms {
            for (var, deg) in &**term {
                if *var < num_public_input {
                    continue;
                }
                if *deg > 1 || term.len() > 1 {
                    linear_terms.remove(var);
                    high_order_dependencies.insert(*var);
                } else {
                    if !high_order_dependencies.contains(var) {
                        linear_terms.insert(*var);
                    }
                }
            }
        }
        (linear_terms, high_order_dependencies)
    }

    fn solve_for_variable(
        mut poly: SparsePolynomial<F, SparseTerm>,
        variable: usize,
    ) -> SparsePolynomial<F, SparseTerm> {
        let (divisor, _) = poly
            .terms
            .iter()
            .find(|(_, term)| term.len() == 1 && term[0].0 == variable)
            .unwrap();
        let multiplier = -divisor.inverse().unwrap();

        poly.terms.retain_mut(|(coeff, term)| {
            if term.len() == 1 && term[0].0 == variable {
                false
            } else {
                *coeff *= multiplier;
                true
            }
        });
        poly
    }

    pub fn preprocess(r1cs: &R1CSFile<F>, config: ExpansionConfig) -> Self {
        let num_public_input = (r1cs.header.n_pub_in + r1cs.header.n_pub_out + 1) as usize;
        let mut witness = r1cs.witness.clone();

        let mut constraint_polys = r1cs
            .constraints
            .iter()
            .flat_map(|(a, b, c)| {
                let mut out_polys = vec![];

                // Heuristic
                let count_vars_a = a.iter().filter(|(var, _)| *var != 0).count();
                let count_vars_b = b.iter().filter(|(var, _)| *var != 0).count();
                let should_try_outline = count_vars_a >= 2 && count_vars_b >= 2;

                let should_outline_a = should_try_outline && count_vars_a >= 3;
                let should_outline_b = should_try_outline && count_vars_b >= 3;

                let mut outline_poly = |poly: &mut SparsePolynomial<F, SparseTerm>,
                                        lc: &[(usize, F)]| {
                    poly.terms
                        .push((-F::one(), SparseTerm::new(vec![(witness.len(), 1)])));
                    out_polys.push(take(poly));
                    *poly = SparsePolynomial::from_coefficients_vec(
                        usize::MAX,
                        vec![(F::one(), SparseTerm::new(vec![(witness.len(), 1)]))],
                    );
                    witness.push(Self::evaluate_lc(lc, &witness));
                };

                let mut poly_a = Self::poly_from_lc(a);
                if should_outline_a {
                    outline_poly(&mut poly_a, a);
                }
                let mut poly_b = Self::poly_from_lc(b);
                if should_outline_b {
                    outline_poly(&mut poly_b, b);
                }
                let poly_c = Self::poly_from_lc(c);
                let mut tentative_poly = naive_mul(&poly_a, &poly_b);
                if !config.check_poly(&tentative_poly) {
                    if !should_outline_a {
                        outline_poly(&mut poly_a, a);
                    }
                    if !should_outline_b {
                        outline_poly(&mut poly_b, b);
                    }
                    tentative_poly = naive_mul(&poly_a, &poly_b) ;
                }
                out_polys.push(&tentative_poly - &poly_c);
                out_polys
            })
            .collect::<Vec<_>>();
        println!("Outlined number constraints: {}", constraint_polys.len());
        println!(
            "Num terms: {}",
            constraint_polys
                .iter()
                .map(|x| x.terms.len())
                .sum::<usize>()
        );

        let mut dependencies_list = constraint_polys
            .par_iter()
            .map(|poly| Self::get_constraint_dependencies(num_public_input, poly))
            .collect::<Vec<_>>();

        let mut dependent_map: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut dependent_queue: BTreeSet<(Reverse<usize>, usize)> = BTreeSet::new();
        let mut queue: BinaryHeap<(Reverse<usize>, usize)> = BinaryHeap::new();
        for (i, (linear_terms, dependencies)) in dependencies_list.iter().enumerate() {
            for term in linear_terms.iter().chain(dependencies.iter()) {
                dependent_map
                    .entry(*term)
                    .or_insert_with(|| Vec::new())
                    .push(i);
            }
        }
        let maybe_enqueue = |queue: &mut BinaryHeap<(Reverse<usize>, usize)>,
                             dependent_map: &mut HashMap<usize, Vec<usize>>,
                             i,
                             linear_terms: &BTreeSet<usize>,
                             dependencies: &BTreeSet<usize>| {
            if dependencies.len() > 0 {
                return;
            }
            if linear_terms.len() == 0 {
                queue.push((Reverse(0), i));
            } else if linear_terms.len() == 1 {
                let var = linear_terms.first().unwrap();
                queue.push((
                    Reverse(dependent_map.get(var).map(|x| x.len()).unwrap_or(0)),
                    i,
                ));
            }
        };
        for (i, (linear_terms, dependencies)) in dependencies_list.iter().enumerate() {
            maybe_enqueue(
                &mut queue,
                &mut dependent_map,
                i,
                linear_terms,
                dependencies,
            );
        }
        for (idx, dependents) in &dependent_map {
            dependent_queue.insert((Reverse(dependents.len()), *idx));
        }

        let mut out_constraints = vec![];
        let mut processed_constraints = 0;
        let mut visited = vec![false; constraint_polys.len()];

        loop {
            while !queue.is_empty() {
                let (_, idx) = queue.pop().unwrap();
                if visited[idx] {
                    continue;
                }
                visited[idx] = true;
                processed_constraints += 1;

                if constraint_polys[idx].is_zero() {
                    continue;
                }

                let (linear_terms, _) = &mut dependencies_list[idx];
                if linear_terms.len() == 0 {
                    out_constraints.push(take(&mut constraint_polys[idx]));
                    continue;
                }

                let new_var = *linear_terms.first().unwrap();
                let dependents = dependent_map.remove(&new_var);
                let num_dependents = dependents.as_ref().map(|x| x.len()).unwrap_or(0);

                // It's generally not worth it to inline if there are more than one usage
                // (since it must be repeated at each instance)
                // Note that self always counts as a dependent
                let should_inline =
                    num_dependents <= 2 && config.check_poly(&constraint_polys[idx]);
                if !should_inline {
                    out_constraints.push(take(&mut constraint_polys[idx]));
                }

                debug_assert_eq!(linear_terms.len(), 1);
                dependents.map(|dependents| {
                    let removed = dependent_queue.remove(&(Reverse(dependents.len()), new_var));
                    debug_assert!(removed);

                    if should_inline {
                        let subst =
                            Self::solve_for_variable(constraint_polys[idx].clone(), new_var);
                        let mut new_constraint_polys =
                            vec![SparsePolynomial::zero(); dependents.len()];
                        let is_inlined = dependents
                            .iter()
                            .zip(&mut new_constraint_polys)
                            .try_for_each(|(idx, out_poly)| {
                                if !config.check_poly(&constraint_polys[*idx]) {
                                    return None;
                                }
                                let new_poly = substitute(&constraint_polys[*idx], new_var, &subst);
                                if let Some(new_poly) = new_poly {
                                    if !config.check_poly(&new_poly) {
                                        return None;
                                    }

                                    *out_poly = new_poly;
                                    Some(())
                                } else {
                                    None
                                }
                            });
                        if is_inlined == None {
                            out_constraints.push(take(&mut constraint_polys[idx]));
                        } else {
                            for (idx, new_poly) in zip(&dependents, new_constraint_polys) {
                                constraint_polys[*idx] = new_poly;
                            }
                        }
                    }

                    for idx in &dependents {
                        if visited[*idx] {
                            continue;
                        }

                        let (linear_terms, dependencies) = &mut dependencies_list[*idx];
                        linear_terms.remove(&new_var);
                        dependencies.remove(&new_var);

                        maybe_enqueue(
                            &mut queue,
                            &mut dependent_map,
                            *idx,
                            linear_terms,
                            dependencies,
                        );
                    }
                });
            }

            if processed_constraints >= constraint_polys.len() {
                break;
            }

            // No more variables can be eliminated. We will name some variables free and continue
            while queue.is_empty() {
                let (_, var) = dependent_queue.pop_first().unwrap();

                for idx in dependent_map.remove(&var).unwrap() {
                    if visited[idx] {
                        continue;
                    }

                    let (linear_terms, dependencies) = &mut dependencies_list[idx];
                    linear_terms.remove(&var);
                    dependencies.remove(&var);

                    maybe_enqueue(
                        &mut queue,
                        &mut dependent_map,
                        idx,
                        linear_terms,
                        dependencies,
                    );
                }
            }
        }

        println!(
            "Num terms: {}",
            out_constraints.iter().map(|x| x.terms.len()).sum::<usize>()
        );

        out_constraints
            .par_iter_mut()
            .for_each(|poly| poly.num_vars = witness.len());

        Self {
            num_public_inputs: num_public_input,
            constraints: out_constraints,
            witness,
        }
    }

    pub fn is_satisfied(&self, values: &Vec<F>) -> bool {
        self.constraints
            .par_iter()
            .all(|poly| poly.evaluate(values) == F::zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use circom_compat::read_witness;
    use std::fs::File;
    use std::io::BufReader;

    #[test]
    fn test_circuit() {
        let reader = BufReader::new(File::open("D:/Projects/circuit.r1cs").unwrap());
        let mut file = R1CSFile::<Fr>::new(reader).unwrap();
        println!("R1CS num constraints: {}", file.header.n_constraints);

        let witness_reader = BufReader::new(File::open("D:/Projects/witness.json").unwrap());
        file.witness = read_witness::<Fr>(witness_reader);

        let result = ExpandedCircuit::<Fr>::preprocess(&file, ExpansionConfig::MaxCost(10));
        println!(
            "Expanded circuit num constraints: {}",
            result.constraints.len()
        );
        assert!(result.is_satisfied(&result.witness));
    }
}
