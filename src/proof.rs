use std::collections::BTreeMap;

use crate::acorn_value::AcornValue;
use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Rule, Truthiness};

pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    steps: BTreeMap<usize, ProofStep>,

    final_step: ProofStep,
}

impl<'a> Proof<'a> {
    pub fn new(normalizer: &'a Normalizer, final_step: ProofStep) -> Proof<'a> {
        Proof {
            normalizer,
            steps: BTreeMap::new(),
            final_step,
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

    // If this proof step cannot be made direct, return a string explaining why.
    fn check_direct(&self, step: &ProofStep) -> Result<(), String> {
        let mut counterfactual_deps = 0;
        for i in step.dependencies() {
            if self.is_counterfactual(*i) {
                counterfactual_deps += 1;
            }
        }
        if counterfactual_deps > 1 {
            return Err(format!(
                "clause {} depends on {} counterfactuals, so it cannot be made direct",
                step.clause, counterfactual_deps
            ));
        }

        Ok(())
    }

    // Tries to turn this proof into a direct proof.
    //
    // A direct proof is represented as a list of true values, each of which can be proven
    // in a single step.
    // Direct proofs do not need to include statements which the prover automatically includes,
    // such as previous statements and library facts.
    //
    // If we can't convert to values, return a string explaining why.
    pub fn make_direct(&self) -> Result<Vec<AcornValue>, String> {
        self.check_direct(&self.final_step)?;

        let mut regular = vec![];
        let mut inverted = vec![];
        for step in self.steps.values() {
            if let Rule::Assumption = step.rule {
                // This is a previous statement.
                continue;
            }
            match step.truthiness {
                Truthiness::Factual => {
                    // This is a library fact.
                    continue;
                }

                Truthiness::Counterfactual => {
                    self.check_direct(step)?;

                    // A counterfactual step that only depends on a single counterfactual step
                    // can be converted to a direct proof by negating it and putting it at the end.
                    inverted.push(&step.clause);
                }

                Truthiness::Hypothetical => {
                    regular.push(&step.clause);
                }
            }
        }

        let mut answer = vec![];
        for clause in regular {
            let value = self.normalizer.denormalize(clause);
            answer.push(value);
        }

        for clause in inverted.iter().rev() {
            let value = self.normalizer.denormalize(clause).negate();
            answer.push(value);
        }

        Ok(answer)
    }
}
