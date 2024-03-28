use std::collections::{BTreeMap, HashMap};

use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::code_gen_error::CodeGenError;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Truthiness};
use crate::proposition::Source;

// A proof created by the Prover. It starts with
pub struct ReductionProof<'a> {
    normalizer: &'a Normalizer,

    // Maps clause id to proof step that proves it.
    // Does not include the final step, because the final step has no clause id.
    steps: BTreeMap<usize, ProofStep>,

    // The conclusion of this step should be a contradiction.
    final_step: ProofStep,
}

// To conveniently manipulate the proof, we store it as a directed graph with its own ids.
// We need two sorts of ids because when we reverse individual steps in the reasoning, the
// condensed and non-condensed steps won't be 1-to-1 related any more.
type CondensedProofStepId = u32;

struct CondensedProofStep {
    // The clause that should be displayed to represent this node.
    // The clause itself is stored in the ReductionProof.
    // This is None if we are proving a contradiction.
    clause_id: Option<usize>,

    // Whether we are proving the clause described by clause_id, or its negation.
    clause_negated: bool,

    // Which other steps this step depends on.
    premises: Vec<CondensedProofStepId>,

    // Which other steps depend on this step.
    consequences: Vec<CondensedProofStepId>,

    // What assumptions this step depends on.
    // Assumptions have their own ProofSteps in the ReductionProof, but in the CondensedProof
    // they are always combined into other steps.
    assumptions: Vec<Source>,
}

// A condensed proof is a graph.
// Each node has a node id.
struct CondensedProof {
    // All steps, indexed by their id.
    steps: Vec<CondensedProofStep>,
}

impl<'a> ReductionProof<'a> {
    pub fn new(normalizer: &'a Normalizer, final_step: ProofStep) -> ReductionProof<'a> {
        ReductionProof {
            normalizer,
            steps: BTreeMap::new(),
            final_step,
        }
    }

    // Just to be used during construction.
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

    fn clause_to_code(
        &self,
        clause: &Clause,
        bindings: &BindingMap,
        negate: bool,
    ) -> Result<String, CodeGenError> {
        let mut value = self.normalizer.denormalize(clause);
        if negate {
            value = value.negate();
        }
        bindings.value_to_code(&value)
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
    //
    // Code is generated with *tabs* even though I hate tabs. The consuming logic should
    // appropriately turn tabs into spaces.
    pub fn to_code(&self, bindings: &BindingMap) -> Result<Vec<String>, CodeGenError> {
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
            let code = self.clause_to_code(clause, bindings, false)?;
            answer.push(code);
        }

        if !conditional.is_empty() {
            let code = self.clause_to_code(conditional[0], bindings, false)?;
            answer.push(format!("if {} {{", code));
            for clause in conditional.iter().skip(1) {
                let code = self.clause_to_code(clause, bindings, false)?;
                answer.push(format!("\t{}", code));
            }
            answer.push("\tfalse".to_string());
            answer.push("}".to_string());
        }

        for clause in postblock.iter().rev() {
            let code = self.clause_to_code(clause, bindings, true)?;
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
