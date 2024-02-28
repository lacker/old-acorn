use std::collections::BTreeMap;

use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Truthiness};

pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    steps: BTreeMap<usize, ProofStep>,
}

impl<'a> Proof<'a> {
    pub fn new(normalizer: &'a Normalizer) -> Proof<'a> {
        Proof {
            normalizer,
            steps: BTreeMap::new(),
        }
    }

    pub fn add_step(&mut self, id: usize, step: ProofStep) {
        self.steps.insert(id, step);
    }

    fn display(&self, clause: &'a Clause) -> DisplayClause<'a> {
        DisplayClause {
            clause,
            normalizer: self.normalizer,
        }
    }

    fn print_step(&self, preface: &str, step: &ProofStep) {
        println!(
            "\n{}{} generated:\n    {}",
            preface,
            step.rule.name(),
            self.display(&step.clause)
        );
        for (description, i) in step.descriptive_dependencies() {
            let clause = &self.steps.get(&i).unwrap().clause;
            let dc = self.display(clause);
            println!("  using {} {}:\n    {}", description, i, dc);
        }
    }

    pub fn print(&self) {
        println!("the proof uses {} steps:", self.steps.len());
        for (step_id, step) in &self.steps {
            println!("step {}: {}", step_id, step);
            let preface = if step.is_negated_goal() {
                format!("clause {} (negating goal): ", step_id)
            } else {
                format!("clause {}: ", step_id)
            };
            self.print_step(&preface, step);
        }
    }

    fn is_counterfactual(&self, id: usize) -> bool {
        self.steps.get(&id).unwrap().truthiness == Truthiness::Counterfactual
    }

    // Tries to turn this proof into a direct proof.
    // Returns the clauses in two groups: (regular, inverted).
    // The direct proof first proves each of the regular clauses, then proves
    // the negation of each of the inverted clauses.
    //
    // Some proofs cannot be converted to a direct proof, in which case we return None.
    pub fn make_direct(&self) -> Option<(Vec<&Clause>, Vec<&Clause>)> {
        let mut regular = vec![];
        let mut inverted = vec![];
        for step in self.steps.values() {
            if step.truthiness == Truthiness::Counterfactual {
                // A counterfactual step that depends on multiple counterfactual steps
                // cannot be converted to a direct proof.
                // Instead, we would need to add branching logic somewhere.
                let mut count_counterfactual = 0;
                for &i in step.dependencies() {
                    if self.is_counterfactual(i) {
                        count_counterfactual += 1;
                    }
                }
                if count_counterfactual > 1 {
                    return None;
                }

                // A counterfactual step that only depends on a single counterfactual step
                // can be converted to a direct proof by negating it and putting it at the end.
                inverted.push(&step.clause);
            } else {
                regular.push(&step.clause);
            }
        }

        // Reverse the inverted steps so that we return the order used in the direct proof.
        inverted.reverse();

        Some((regular, inverted))
    }
}
