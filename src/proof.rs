use std::collections::{BTreeMap, HashMap};

use crate::acorn_value::AcornValue;
use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Rule, Truthiness};

// A proof, as produced by the prover.
pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    // Maps clause id to proof step that proves it.
    // Does not include the final step, because the final step has no clause id.
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
    fn make_direct(&self) -> Result<Vec<AcornValue>, String> {
        self.check_direct(&self.final_step)?;

        let mut regular = vec![];
        let mut inverted = vec![];
        for step in self.steps.values() {
            if let Rule::Assumption(_) = step.rule {
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

    // Make a pretty version of the proof, for an environment described by the given bindings.
    // This is a list of strings, each of which is a line in the proof.
    // If we can't, return an error string explaining why.
    pub fn to_code(&self, bindings: &BindingMap) -> Result<Vec<String>, String> {
        let values = self.make_direct()?;
        let mut answer = vec![];
        for value in values {
            let code = bindings.value_to_code(&value)?;
            answer.push(code);
        }
        Ok(answer)
    }

    // Converts the proof to lines of code.
    //
    // The prover assumes the goal is false and then searches for a contradiction.
    // When we turn this sort of proof into code, it looks like one big proof by contradiction.
    // This often commingles lemma-style reasoning that seems intuitively true with
    // proof-by-contradiction-style reasoning that feels intuitively backwards.
    // Humans try to avoid mixing these different styles of reasoning.
    //
    // In a direct proof, all of the statements are true statements, so it's more intuitive.
    // Howevever, we can't always create a direct proof. So the idea is to make the proof
    // "as direct as possible".
    //
    // Specifically, we turn the proof into something of the form:
    //
    // <proposition>
    // ...
    // <proposition>
    // if <condition> {
    //   <proposition>
    //   ...
    //   <proposition>
    //   false
    // }
    // <proposition>
    // ...
    // <proposition>
    //
    // So, a direct proof, followed by a proof by contradiction, followed by a direct proof.
    // Essentially, we start with a proof by contradiction and "extract" as many statements
    // as possible into the surrounding direct proofs.
    pub fn new_to_code(&self, bindings: &BindingMap) -> Result<Vec<String>, String> {
        // Check how many times each clause is used by a subsequent clause.
        let mut use_count = HashMap::new();
        for step in self.steps.values() {
            for i in step.dependencies() {
                *use_count.entry(*i).or_insert(0) += 1;
            }
        }
        for i in self.final_step.dependencies() {
            *use_count.entry(*i).or_insert(0) += 1;
        }

        // The clauses before the if-block.
        let mut preblock = vec![];

        // The clauses that go into the if-block.
        // The first one is the assumption.
        // The block will end with a "false" that is not explicitly included.
        let mut conditional = vec![];

        // The clauses after the if-block.
        // Populated in the order the prover generated them. In the final proof they
        // will be negated and put in reverse order.
        let mut postblock = vec![];

        for (i, step) in self.steps.iter() {
            if step.truthiness != Truthiness::Counterfactual {
                // We can extract any clauses that are not counterfactual.
                // We don't want to generate code for the assumptions.
                if !step.rule.is_assumption() {
                    preblock.push(&step.clause);
                }
                continue;
            }

            if conditional.is_empty() && use_count[i] <= 1 {
                // We can extract this counterfactual.
                // We don't want to generate code for the negated goal, though.
                if !step.rule.is_assumption() {
                    postblock.push(&step.clause);
                }
                continue;
            }

            // We can't extract this counterfactual.
            // We *do* want to generate code if this is the negated goal.
            conditional.push(&step.clause);
        }

        let mut answer = vec![];
        for clause in preblock {
            let value = self.normalizer.denormalize(clause);
            let code = bindings.value_to_code(&value)?;
            answer.push(code);
        }

        if !conditional.is_empty() {
            let value = self.normalizer.denormalize(conditional[0]);
            let code = bindings.value_to_code(&value)?;
            answer.push(format!("if {} {{", code));
            for clause in conditional.iter().skip(1) {
                let value = self.normalizer.denormalize(clause);
                let code = bindings.value_to_code(&value)?;
                answer.push(code);
            }
            answer.push("false".to_string());
            answer.push("}".to_string());
        }

        for clause in postblock.iter().rev() {
            let value = self.normalizer.denormalize(clause).negate();
            let code = bindings.value_to_code(&value)?;
            answer.push(code);
        }

        Ok(answer)
    }

    // Iterates in order through the steps of the proof.
    // Includes the clause id in the tuple, til it gets to the last one which is None.
    pub fn iter_steps(&'a self) -> impl Iterator<Item = (Option<usize>, &'a ProofStep)> {
        self.steps
            .iter()
            .map(|(id, step)| (Some(*id), step))
            .chain(std::iter::once((None, &self.final_step)))
    }
}
