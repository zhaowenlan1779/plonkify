use ark_ff::{PrimeField, Zero};
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm, Term},
    DenseMVPolynomial, Polynomial,
};
use circom_compat::R1CSFile;
use rayon::prelude::*;
use std::{cmp::Reverse, collections::HashSet};
use std::collections::{BTreeSet, BinaryHeap, HashMap};
use std::iter::zip;
use std::mem::take;

fn term_mul_by_term(cur: &SparseTerm, other: &SparseTerm) -> SparseTerm {
    SparseTerm::new((**cur).iter().chain((**other).iter()).map(|x| *x).collect())
}

fn poly_mul_by_term<F: PrimeField>(
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

fn naive_mul<F: PrimeField>(
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
) -> SparsePolynomial<F, SparseTerm> {
    let mut result_terms = Vec::new();
    for (coeff, term) in cur.terms.iter() {
        let item_to_subst = (**term).iter().find(|(var, _)| *var == variable);
        if let Some((_, power)) = item_to_subst {
            let new_term = SparseTerm::new(
                (**term)
                    .iter()
                    .filter(|(var, _)| *var != variable)
                    .map(|x| *x)
                    .collect::<Vec<_>>(),
            );

            let mut new_poly = if *power == 1 {
                subst.clone()
            } else {
                // Exponentiation by squaring
                let mut power = *power;
                let mut multiplier = subst.clone();
                let mut new_poly = SparsePolynomial::zero();
                loop {
                    if power % 2 == 1 {
                        if new_poly.is_zero() {
                            new_poly = multiplier.clone();
                        } else {
                            new_poly = naive_mul(&new_poly, &multiplier);
                        }
                    }

                    power /= 2;
                    if power > 0 {
                        multiplier = naive_mul(&multiplier, &multiplier);
                    } else {
                        break;
                    }
                }
                new_poly
            };
            poly_mul_by_term(&mut new_poly, *coeff, &new_term);
            result_terms.append(&mut new_poly.terms);
        } else {
            result_terms.push((*coeff, term.clone()));
        }
    }
    SparsePolynomial::from_coefficients_vec(cur.num_vars, result_terms)
}

pub struct ExpandedCircuit<F: PrimeField> {
    pub num_instance_variables: usize,
    pub constraints: Vec<SparsePolynomial<F, SparseTerm>>,
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

    fn check_poly_with_weight<F: PrimeField>(
        &self,
        poly: &SparsePolynomial<F, SparseTerm>,
        weight: usize,
    ) -> bool {
        match self {
            ExpansionConfig::None => true,
            ExpansionConfig::MaxWidth(width) => poly.terms.len() <= *width,
            ExpansionConfig::MaxDegree(degree) => poly.degree() <= *degree,
            ExpansionConfig::MaxCost(max_cost) => weight <= *max_cost,
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

    // (linear terms, dependencies)
    fn get_constraint_dependencies(
        num_instance_variables: usize,
        constraint_poly: &SparsePolynomial<F, SparseTerm>,
    ) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let mut linear_terms = BTreeSet::new();
        let mut high_order_dependencies = BTreeSet::new();
        for (_, term) in &constraint_poly.terms {
            for (var, deg) in &**term {
                if *var < num_instance_variables {
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

    pub fn preprocess(r1cs: &R1CSFile<F>, config: ExpansionConfig, max_lc_width: usize) -> Self {
        let num_instance_variables =
            (r1cs.header.n_pub_in + r1cs.header.n_pub_out + r1cs.header.n_prv_in + 1) as usize;
        let mut num_vars = r1cs.header.n_wires as usize;

        let mut constraint_polys = r1cs
            .constraints
            .iter()
            .flat_map(|(a, b, c)| {
                let mut out_polys = vec![];
                let mut maybe_outline_poly = |lc: &Vec<(usize, F)>| {
                    let mut poly = Self::poly_from_lc(lc);
                    if poly.terms.len() > max_lc_width {
                        poly.terms
                            .push((-F::one(), SparseTerm::new(vec![(num_vars, 1)])));
                        out_polys.push(take(&mut poly));
                        poly = SparsePolynomial::from_coefficients_vec(
                            usize::MAX,
                            vec![(F::one(), SparseTerm::new(vec![(num_vars, 1)]))],
                        );
                        num_vars += 1;
                    }
                    poly
                };

                let poly_a = maybe_outline_poly(a);
                let poly_b = maybe_outline_poly(b);
                let poly_c = Self::poly_from_lc(c);
                out_polys.push(&naive_mul(&poly_a, &poly_b) - &poly_c);
                out_polys
            })
            .collect::<Vec<_>>();
        let mut dependencies_list = constraint_polys
            .par_iter()
            .map(|poly| Self::get_constraint_dependencies(num_instance_variables, poly))
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
            if dependencies.len() > 0 {
                continue;
            }
            if linear_terms.len() == 0 {
                queue.push((Reverse(0), i));
            } else if linear_terms.len() == 1 {
                queue.push((Reverse(get_poly_weight(&constraint_polys[i])), i))
            }
        }
        for (idx, dependents) in &dependent_map {
            dependent_queue.insert((Reverse(dependents.len()), *idx));
        }

        let mut out_constraints = vec![];
        let mut processed_constraints = 0;
        let mut visited = vec![false; constraint_polys.len()];
        loop {
            while !queue.is_empty() {
                let (cost, idx) = queue.pop().unwrap();
                if visited[idx] {
                    continue;
                }
                visited[idx] = true;

                processed_constraints += 1;
                if processed_constraints % 1000 == 0 {
                    println!("Processed {} constraints", processed_constraints);
                }

                if constraint_polys[idx].is_zero() {
                    continue;
                }

                let (linear_terms, _) = &mut dependencies_list[idx];
                if linear_terms.len() == 0 {
                    out_constraints.push(take(&mut constraint_polys[idx]));
                    continue;
                }

                let should_inline = config.check_poly_with_weight(&constraint_polys[idx], cost.0);
                if !should_inline {
                    out_constraints.push(take(&mut constraint_polys[idx]));
                }

                debug_assert_eq!(linear_terms.len(), 1);

                let new_var = *linear_terms.first().unwrap();
                dependent_map.remove(&new_var).map(|dependents| {
                    let removed = dependent_queue.remove(&(Reverse(dependents.len()), new_var));
                    debug_assert!(removed);

                    if should_inline {
                        let subst =
                            Self::solve_for_variable(take(&mut constraint_polys[idx]), new_var);
                        let new_constraint_polys = dependents
                            .par_iter()
                            .map(|idx| substitute(&constraint_polys[*idx], new_var, &subst))
                            .collect::<Vec<_>>();
                        for (idx, poly) in zip(&dependents, new_constraint_polys) {
                            constraint_polys[*idx] = poly;
                        }
                    }

                    for idx in &dependents {
                        if visited[*idx] {
                            continue;
                        }

                        let (linear_terms, dependencies) = &mut dependencies_list[*idx];
                        linear_terms.remove(&new_var);
                        dependencies.remove(&new_var);

                        if dependencies.len() > 0 {
                            continue;
                        }

                        if linear_terms.len() == 0 {
                            queue.push((Reverse(0), *idx));
                        } else if linear_terms.len() == 1 {
                            queue.push((Reverse(get_poly_weight(&constraint_polys[*idx])), *idx))
                        }
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

                    if dependencies.len() > 0 {
                        continue;
                    }

                    if linear_terms.len() == 0 {
                        queue.push((Reverse(0), idx));
                    } else if linear_terms.len() == 1 {
                        queue.push((Reverse(get_poly_weight(&constraint_polys[idx])), idx))
                    }
                }
            }
        }

        Self {
            num_instance_variables,
            constraints: out_constraints,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr;
    use circom_compat::Header;
    use std::fs::File;
    use std::io::BufReader;

    #[test]
    fn test_sample() {
        let from_u64 = |x: u64| -> Fr { Fr::from_u64(x).unwrap() };

        // (4x + 8)(6x + 8) = 8a_1
        // (a_1)(a_1) = a_2
        // (a_1 + a_3)(a_2 + a_3) = a_3 + 5
        // (a_2)(3a_1) = a_3 + 2
        let r1cs = R1CSFile {
            version: 0,
            header: Header {
                n_pub_in: 1,
                n_pub_out: 0,
                n_prv_in: 0,
                field_size: 0,
                prime_size: vec![],
                n_wires: 5,
                n_constraints: 4,
                n_labels: 0,
            },
            constraints: vec![
                (
                    vec![(0, from_u64(8)), (1, from_u64(4))],
                    vec![(0, from_u64(8)), (1, from_u64(6))],
                    vec![(2, from_u64(8))],
                ),
                (
                    vec![(2, from_u64(1))],
                    vec![(2, from_u64(1))],
                    vec![(3, from_u64(1))],
                ),
                (
                    vec![(2, from_u64(1)), (4, from_u64(1))],
                    vec![(3, from_u64(1)), (4, from_u64(1))],
                    vec![(4, from_u64(1)), (0, from_u64(5))],
                ),
                (
                    vec![(3, from_u64(1))],
                    vec![(2, from_u64(3))],
                    vec![(4, from_u64(1)), (0, from_u64(2))],
                ),
            ],
            wire_mapping: vec![],
            witness: vec![],
        };
        let result = ExpandedCircuit::<Fr>::preprocess(&r1cs, ExpansionConfig::None, 5);
        assert_eq!(result.constraints.len(), 1);
        let expected_result = SparsePolynomial::from_coefficients_vec(
            2,
            vec![
                (from_u64(2462577), SparseTerm::new(vec![])),
                (from_u64(18343340), SparseTerm::new(vec![(1, 1)])),
                (from_u64(62416402), SparseTerm::new(vec![(1, 2)])),
                (from_u64(128310040), SparseTerm::new(vec![(1, 3)])),
                (from_u64(177498006), SparseTerm::new(vec![(1, 4)])),
                (from_u64(174079740), SparseTerm::new(vec![(1, 5)])),
                (from_u64(124112574), SparseTerm::new(vec![(1, 6)])),
                (from_u64(64814040), SparseTerm::new(vec![(1, 7)])),
                (from_u64(24604803), SparseTerm::new(vec![(1, 8)])),
                (from_u64(6621750), SparseTerm::new(vec![(1, 9)])),
                (from_u64(1199205), SparseTerm::new(vec![(1, 10)])),
                (from_u64(131220), SparseTerm::new(vec![(1, 11)])),
                (from_u64(6561), SparseTerm::new(vec![(1, 12)])),
            ],
        );
        assert_eq!(result.constraints[0].terms, expected_result.terms);
    }

    #[test]
    fn test_bivariate() {
        let from_u64 = |x: u64| -> Fr { Fr::from_u64(x).unwrap() };

        // (4x + 8)(6y + 8) = 8a_1
        // (a_1 + a_2)(a_2) = x + 5
        // (a_1)(3a_1) = a_2 + 2
        let r1cs = R1CSFile {
            version: 0,
            header: Header {
                n_pub_in: 1,
                n_pub_out: 1,
                n_prv_in: 0,
                field_size: 0,
                prime_size: vec![],
                n_wires: 5,
                n_constraints: 3,
                n_labels: 0,
            },
            constraints: vec![
                (
                    vec![(0, from_u64(8)), (1, from_u64(4))],
                    vec![(0, from_u64(8)), (2, from_u64(6))],
                    vec![(3, from_u64(8))],
                ),
                (
                    vec![(3, from_u64(1)), (4, from_u64(1))],
                    vec![(4, from_u64(1))],
                    vec![(1, from_u64(1)), (0, from_u64(5))],
                ),
                (
                    vec![(3, from_u64(1))],
                    vec![(3, from_u64(3))],
                    vec![(4, from_u64(1)), (0, from_u64(2))],
                ),
            ],
            wire_mapping: vec![],
            witness: vec![],
        };
        let result = ExpandedCircuit::<Fr>::preprocess(&r1cs, ExpansionConfig::None, 5);
        assert_eq!(result.constraints.len(), 1);
        let expected_result = SparsePolynomial::from_coefficients_vec(
            3,
            vec![
                (from_u64(37615), SparseTerm::new(vec![])),
                (from_u64(112884), SparseTerm::new(vec![(2, 1)])),
                (from_u64(75255), SparseTerm::new(vec![(1, 1)])),
                (from_u64(126576), SparseTerm::new(vec![(2, 2)])),
                (from_u64(225210), SparseTerm::new(vec![(1, 1), (2, 1)])),
                (from_u64(56256), SparseTerm::new(vec![(1, 2)])),
                (from_u64(62856), SparseTerm::new(vec![(2, 3)])),
                (from_u64(252288), SparseTerm::new(vec![(1, 1), (2, 2)])),
                (from_u64(168192), SparseTerm::new(vec![(1, 2), (2, 1)])),
                (from_u64(18624), SparseTerm::new(vec![(1, 3)])),
                (from_u64(11664), SparseTerm::new(vec![(2, 4)])),
                (from_u64(125388), SparseTerm::new(vec![(1, 1), (2, 3)])),
                (from_u64(188460), SparseTerm::new(vec![(1, 2), (2, 2)])),
                (from_u64(55728), SparseTerm::new(vec![(1, 3), (2, 1)])),
                (from_u64(2304), SparseTerm::new(vec![(1, 4)])),
                (from_u64(23328), SparseTerm::new(vec![(1, 1), (2, 4)])),
                (from_u64(93798), SparseTerm::new(vec![(1, 2), (2, 3)])),
                (from_u64(62532), SparseTerm::new(vec![(1, 3), (2, 2)])),
                (from_u64(6912), SparseTerm::new(vec![(1, 4), (2, 1)])),
                (from_u64(17496), SparseTerm::new(vec![(1, 2), (2, 4)])),
                (from_u64(31185), SparseTerm::new(vec![(1, 3), (2, 3)])),
                (from_u64(7776), SparseTerm::new(vec![(1, 4), (2, 2)])),
                (from_u64(5832), SparseTerm::new(vec![(1, 3), (2, 4)])),
                (from_u64(3888), SparseTerm::new(vec![(1, 4), (2, 3)])),
                (from_u64(729), SparseTerm::new(vec![(1, 4), (2, 4)])),
            ],
        );
        assert_eq!(result.constraints[0].terms, expected_result.terms);
    }

    #[test]
    fn test_circuit() {
        let reader = BufReader::new(File::open("D:/Projects/circuit.r1cs").unwrap());
        let file = R1CSFile::<Fr>::new(reader).unwrap();
        println!("R1CS num constraints: {}", file.header.n_constraints);

        let result = ExpandedCircuit::<Fr>::preprocess(&file, ExpansionConfig::MaxCost(10), 5);
        println!(
            "Expanded circuit num constraints: {}",
            result.constraints.len()
        );
    }
}
