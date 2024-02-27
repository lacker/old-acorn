use std::collections::BTreeMap;

use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::ProofStep;

pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    steps: BTreeMap<usize, ProofStep>,
}

impl<'a> Proof<'a> {
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
}
