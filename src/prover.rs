use std::collections::HashSet;
use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use tower_lsp::lsp_types::Url;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::ActiveSet;
use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::goal::{Goal, GoalContext};
use crate::interfaces::{ClauseInfo, InfoResult, Location, ProofStepInfo};
use crate::literal::Literal;
use crate::module::ModuleId;
use crate::normalizer::{Normalization, NormalizationError, Normalizer};
use crate::passive_set::PassiveSet;
use crate::project::Project;
use crate::proof::{Difficulty, Proof};
use crate::proof_step::{ProofStep, ProofStepId, Rule, Truthiness};
use crate::proposition::{Proposition, SourceType};
use crate::term::Term;
use crate::term_graph::TermGraphContradiction;

pub struct Prover {
    // The normalizer is used when we are turning the facts and goals from the environment into
    // clauses that we can use internally.
    normalizer: Normalizer,
    module_id: ModuleId,

    // The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    passive_set: PassiveSet,

    // A verbose prover prints out a lot of stuff.
    pub verbose: bool,

    // The result of the proof search, if there is one.
    // If we haven't found a result yet, this is None. The prover can still return an Outcome
    // that indicates a temporary outcome, like a timeout.
    result: Option<(ProofStep, Outcome)>,

    // Clauses that we never activated, but we did use to find a contradiction.
    useful_passive: Vec<ProofStep>,

    // Setting any of these flags to true externally will stop the prover.
    pub stop_flags: Vec<Arc<AtomicBool>>,

    // When this error message is set, it indicates a problem that needs to be reported upstream
    // to the user.
    // It's better to catch errors before proving, but sometimes we don't.
    pub error: Option<String>,

    // Whether we expect a contradiction in this scope.
    // Contradictions are okay if we expect one, not okay if we don't.
    expect_contradiction: bool,

    // The normalized term we are solving for, if there is one.
    solve: Option<Term>,

    // A value expressing the negation of the goal we are trying to prove, if there is one.
    negated_goal: Option<AcornValue>,

    // Number of proof steps activated, not counting Factual ones.
    non_factual_activated: usize,
}

// The outcome of a prover operation.
// "Success" means we proved it.
// "Exhausted" means we tried every possibility and couldn't prove it.
// "Inconsistent" means that we found a contradiction just in our initial assumptions.
// "Interrupted" means that the prover was explicitly stopped.
// "Timeout" means that we hit a nondeterministic timing limit.
// "Constrained" means that we hit some deterministic limit.
// "Error" means that we found a problem in the code that needs to be fixed by the user.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Timeout,
    Constrained,
    Error,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Timeout => write!(f, "Timeout"),
            Outcome::Constrained => write!(f, "Constrained"),
            Outcome::Error => write!(f, "Error"),
        }
    }
}

impl Prover {
    pub fn new<'a>(
        project: &'a Project,
        goal_context: &'a GoalContext<'a>,
        verbose: bool,
    ) -> Prover {
        let mut p = Prover {
            normalizer: Normalizer::new(),
            module_id: goal_context.module_id,
            active_set: ActiveSet::new(),
            passive_set: PassiveSet::new(),
            verbose,
            result: None,
            stop_flags: vec![project.build_stopped.clone()],
            expect_contradiction: goal_context.includes_explicit_false(),
            error: None,
            solve: None,
            useful_passive: vec![],
            negated_goal: None,
            non_factual_activated: 0,
        };

        // Find the relevant facts that should be imported into this environment
        let mut imported_facts = vec![];
        for dependency in project.all_dependencies(goal_context.module_id()) {
            let env = project.get_env(dependency).unwrap();
            imported_facts.extend(env.exported_facts());
        }

        let (global_facts, local_facts) = goal_context.monomorphize(imported_facts);

        // Load facts into the prover
        for fact in global_facts {
            p.add_assumption(fact, Truthiness::Factual);
        }
        p.normalizer.finish_global();
        for fact in local_facts {
            p.add_assumption(fact, Truthiness::Hypothetical);
        }
        match &goal_context.goal {
            Goal::Prove(prop) => {
                // Negate the goal and add it as a counterfactual assumption.
                let (hypo, counter) = prop.value.to_placeholder().negate_goal();
                if let Some(hypo) = hypo {
                    p.add_assumption(prop.with_value(hypo), Truthiness::Hypothetical);
                }
                p.negated_goal = Some(counter.clone());
                p.add_assumption(prop.with_negated_goal(counter), Truthiness::Counterfactual);
            }
            Goal::Solve(value, _) => match p.normalizer.term_from_value(value) {
                Ok(term) => {
                    p.solve = Some(term);
                }
                Err(NormalizationError(s)) => {
                    p.error = Some(s);
                }
            },
        }
        p
    }

    fn normalize_proposition(&mut self, proposition: AcornValue) -> Normalization {
        if let Err(e) = proposition.validate() {
            return Normalization::Error(format!(
                "validation error: {} while normalizing: {}",
                e, proposition
            ));
        }
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.normalizer.normalize(proposition)
    }

    fn add_assumption(&mut self, assumption: Proposition, truthiness: Truthiness) {
        let defined_atom = match &assumption.source.source_type {
            SourceType::ConstantDefinition(value) => {
                match self.normalizer.term_from_value(&value) {
                    Ok(term) => Some(term.get_head().clone()),
                    Err(NormalizationError(s)) => {
                        self.error = Some(s);
                        return;
                    }
                }
            }
            _ => None,
        };
        let clauses = match self.normalize_proposition(assumption.value) {
            Normalization::Clauses(clauses) => clauses,
            Normalization::Impossible => {
                // We have a false assumption, so we're done already.
                let final_step = ProofStep::new_assumption(
                    Clause::impossible(),
                    truthiness,
                    &assumption.source,
                    None,
                );
                self.report_contradiction(final_step);
                return;
            }
            Normalization::Error(s) => {
                self.error = Some(s);
                return;
            }
        };
        for clause in clauses {
            let step =
                ProofStep::new_assumption(clause, truthiness, &assumption.source, defined_atom);
            self.passive_set.push(step);
        }
    }
    pub fn print_stats(&self) {
        println!("{} clauses in the active set", self.active_set.len());
        println!("{} clauses in the passive set", self.passive_set.len());
    }

    // Prints out the entire active set
    pub fn print_active(&self, substr: Option<&str>) {
        let mut count = 0;
        for clause in self.active_set.iter_clauses() {
            let clause = self.display(clause);
            if let Some(substr) = substr {
                if !clause.to_string().contains(substr) {
                    continue;
                }
            }
            count += 1;
            println!("{}", clause);
        }
        if let Some(substr) = substr {
            println!("{} active clauses matched {}", count, substr);
        } else {
            println!("{} clauses total in the active set", count);
        }
    }

    pub fn print_passive(&self, substr: Option<&str>) {
        let mut count = 0;
        let steps: Vec<_> = self.passive_set.iter_steps().collect();
        // Only print the first ones
        for step in steps.iter().take(500) {
            let clause = self.display(&step.clause);
            if let Some(substr) = substr {
                if !clause.to_string().contains(substr) {
                    continue;
                }
            }
            count += 1;
            println!("{}", clause);
            println!("  {}", step);
        }
        if let Some(substr) = substr {
            println!("{} passive clauses matched {}", count, substr);
        } else {
            if steps.len() > count {
                println!("  ...omitting {} more", steps.len() - count);
            }
            println!("{} clauses total in the passive set", steps.len());
        }
    }

    // Prints out information for a specific term
    pub fn print_term_info(&self, s: &str) {
        let mut count = 0;
        for clause in self.active_set.iter_clauses() {
            let clause_str = self.display(clause).to_string();
            if clause_str.contains(s) {
                println!("{}", clause_str);
                count += 1;
            }
        }
        println!(
            "{} clause{} matched",
            count,
            if count == 1 { "" } else { "s" }
        );
    }

    // (description, id) for every clause this rule depends on.
    // Entries with an id are references to clauses we are using.
    // An entry with no id is like a comment, it won't be linked to anything.
    fn descriptive_dependencies(&self, step: &ProofStep) -> Vec<(String, ProofStepId)> {
        let mut answer = vec![];
        match &step.rule {
            Rule::Assumption(_) => {}
            Rule::Resolution(info) => {
                answer.push((
                    "long resolver".to_string(),
                    ProofStepId::Active(info.long_id),
                ));
                answer.push((
                    "short resolver".to_string(),
                    ProofStepId::Active(info.short_id),
                ));
            }
            Rule::Rewrite(info) => {
                answer.push(("target".to_string(), ProofStepId::Active(info.target_id)));
                answer.push(("pattern".to_string(), ProofStepId::Active(info.pattern_id)));
            }
            Rule::EqualityFactoring(source)
            | Rule::EqualityResolution(source)
            | Rule::FunctionElimination(source)
            | Rule::Specialization(source) => {
                answer.push(("source".to_string(), ProofStepId::Active(*source)));
            }
            Rule::MultipleRewrite(info) => {
                answer.push((
                    "inequality".to_string(),
                    ProofStepId::Active(info.inequality_id),
                ));
                for &id in &info.active_ids {
                    answer.push(("equality".to_string(), ProofStepId::Active(id)));
                }
                for &id in &info.passive_ids {
                    answer.push(("specialization".to_string(), ProofStepId::Passive(id)));
                }
            }
            Rule::PassiveContradiction(n) => {
                for id in 0..*n {
                    answer.push(("clause".to_string(), ProofStepId::Passive(id)));
                }
            }
        }

        for rule in &step.simplification_rules {
            answer.push(("simplification".to_string(), ProofStepId::Active(*rule)));
        }
        answer
    }

    fn print_proof_step(&self, preface: &str, step: &ProofStep) {
        println!(
            "\n{}{} generated (depth {}):\n    {}",
            preface,
            step.rule.name(),
            step.depth,
            self.display(&step.clause)
        );

        for (description, id) in self.descriptive_dependencies(&step) {
            match id {
                ProofStepId::Active(i) => {
                    let c = self.display(self.active_set.get_clause(i));
                    println!("  using {} {}:\n    {}", description, i, c);
                }
                ProofStepId::Passive(i) => {
                    let c = self.display(&self.useful_passive[i as usize].clause);
                    println!("  using {}:\n    {}", description, c);
                }
                ProofStepId::Final => {
                    println!("  <unexpected dependency on final proof step>");
                }
            }
        }
    }

    pub fn num_activated(&self) -> usize {
        self.active_set.len()
    }

    pub fn get_and_print_proof(&self) -> Option<Proof> {
        let proof = match self.get_proof() {
            Some(proof) => proof,
            None => {
                println!("we do not have a proof");
                return None;
            }
        };

        println!(
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );
        println!("non-factual activations: {}", self.non_factual_activated);

        println!("the proof uses {} steps:", proof.all_steps.len());
        for (id, step) in &proof.all_steps {
            let preface = match id {
                ProofStepId::Active(i) => {
                    if step.rule.is_negated_goal() {
                        format!("clause {} (negating goal): ", i)
                    } else {
                        format!("clause {}: ", i)
                    }
                }
                ProofStepId::Passive(_) => "".to_string(),
                ProofStepId::Final => "final step: ".to_string(),
            };
            self.print_proof_step(&preface, &step);
        }
        Some(proof)
    }

    // Returns a condensed proof, if we have a proof.
    pub fn get_proof(&self) -> Option<Proof> {
        let final_step = if let Some((final_step, _)) = &self.result {
            final_step
        } else {
            return None;
        };
        let mut useful_active = HashSet::new();
        self.active_set
            .find_upstream(&final_step, &mut useful_active);
        for step in &self.useful_passive {
            self.active_set.find_upstream(step, &mut useful_active);
        }
        let negated_goal = match &self.negated_goal {
            Some(negated_goal) => negated_goal,
            None => return None,
        };

        let difficulty = if !self.passive_set.verification_phase {
            // Verification mode won't find this proof, so we definitely need a shorter one
            Difficulty::Complicated
        } else if self.non_factual_activated > 500 {
            Difficulty::Intermediate
        } else {
            Difficulty::Simple
        };

        let mut proof = Proof::new(&self.normalizer, negated_goal, difficulty);
        let mut active_ids: Vec<_> = useful_active.iter().collect();
        active_ids.sort();
        for i in active_ids {
            let step = self.active_set.get_step(*i);
            proof.add_step(ProofStepId::Active(*i), step);
        }
        for (i, step) in self.useful_passive.iter().enumerate() {
            proof.add_step(ProofStepId::Passive(i as u32), step);
        }
        proof.add_step(ProofStepId::Final, final_step);
        proof.condense();
        Some(proof)
    }

    // Handle the case when we found a contradiction
    fn report_contradiction(&mut self, step: ProofStep) -> Outcome {
        assert!(self.result.is_none());
        let outcome = if step.truthiness != Truthiness::Counterfactual && !self.expect_contradiction
        {
            Outcome::Inconsistent
        } else {
            Outcome::Success
        };

        self.result = Some((step, outcome));
        outcome
    }

    fn report_term_graph_contradiction(
        &mut self,
        contradiction: TermGraphContradiction,
    ) -> Outcome {
        let mut active_ids = vec![];
        let mut passive_ids = vec![];
        let mut new_clauses = HashSet::new();
        let mut max_depth = 0;
        let inequality_step = self.active_set.get_step(contradiction.inequality_id);
        let mut truthiness = inequality_step.truthiness;
        for (left, right, rewrite_info) in contradiction.rewrite_chain {
            let rewrite_step = self.active_set.get_step(rewrite_info.pattern_id);
            truthiness = truthiness.combine(rewrite_step.truthiness);

            // Check whether we need to explicitly add a specialized clause to the proof.
            match rewrite_info.subterm_depth {
                None | Some(0) => {
                    // No extra specialized clause needed
                    active_ids.push(rewrite_info.pattern_id);
                    max_depth = max_depth.max(rewrite_step.depth);
                    continue;
                }
                Some(_) => {}
            };

            // Create a new proof step, without activating it, to express the
            // specific equality used by this rewrite.
            let literal = Literal::equals(left, right);
            let clause = Clause::new(vec![literal]);
            if new_clauses.contains(&clause) {
                // We already created a step for this equality
                // TODO: is it really okay to not insert any sort of id here?
                continue;
            }
            new_clauses.insert(clause.clone());
            let step = ProofStep::new_specialization(rewrite_info.pattern_id, rewrite_step, clause);
            max_depth = max_depth.max(step.depth);
            let passive_id = self.useful_passive.len() as u32;
            self.useful_passive.push(step);
            passive_ids.push(passive_id);
        }

        active_ids.sort();
        active_ids.dedup();

        let step = ProofStep::new_multiple_rewrite(
            contradiction.inequality_id,
            active_ids,
            passive_ids,
            truthiness,
            max_depth,
        );
        self.report_contradiction(step)
    }

    fn report_passive_contradiction(&mut self, passive_steps: Vec<ProofStep>) -> Outcome {
        assert!(self.useful_passive.is_empty());
        for mut passive_step in passive_steps {
            passive_step.printable = false;
            self.useful_passive.push(passive_step);
        }
        let final_step = ProofStep::new_passive_contradiction(&self.useful_passive);
        self.report_contradiction(final_step)
    }

    // Activates the next clause from the queue, unless we're already done.
    // Returns the outcome if the prover finished, otherwise None.
    pub fn activate_next(&mut self) -> Option<Outcome> {
        if let Some((_, outcome)) = &self.result {
            return Some(*outcome);
        }

        if let Some(passive_steps) = self.passive_set.get_contradiction() {
            return Some(self.report_passive_contradiction(passive_steps));
        }

        let step = match self.passive_set.pop() {
            Some(step) => step,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                return Some(Outcome::Exhausted);
            }
        };

        if step.truthiness != Truthiness::Factual {
            self.non_factual_activated += 1;
        }

        if step.clause.is_impossible() {
            return Some(self.report_contradiction(step));
        }

        if self.verbose {
            let prefix = match step.truthiness {
                Truthiness::Factual => " fact",
                Truthiness::Hypothetical => " hypothesis",
                Truthiness::Counterfactual => {
                    if step.rule.is_negated_goal() {
                        " negated goal"
                    } else {
                        ""
                    }
                }
            };
            println!("activating{}: {}", prefix, self.display(&step.clause));
        }
        self.activate(step)
    }

    // Generates new passive clauses, simplifying appropriately, and adds them to the passive set.
    //
    // This does two forms of simplification. It simplifies all existing passive clauses based on
    // the newly activated clause, and simplifies the new passive clauses based on all
    // existing active clauses.
    //
    // This double simplification ensures that every passive clause is always simplified with
    // respect to every active clause.
    //
    // Returns the outcome if the prover finished, otherwise None.
    fn activate(&mut self, activated_step: ProofStep) -> Option<Outcome> {
        // Use the step for simplification
        let activated_id = self.active_set.next_id();
        if activated_step.clause.literals.len() == 1 {
            self.passive_set.simplify(activated_id, &activated_step);
        }

        // Generate new clauses
        let (alt_activated_id, generated_clauses) = self.active_set.activate(activated_step);
        assert_eq!(activated_id, alt_activated_id);

        let print_limit = 30;
        let len = generated_clauses.len();
        if self.verbose && len > 0 {
            println!(
                "generated {} new clauses{}:",
                len,
                if len > print_limit { ", eg" } else { "" }
            );
        }
        for step in generated_clauses {
            if step.finishes_proof() {
                return Some(self.report_contradiction(step));
            }

            if step.automatic_reject() {
                continue;
            }

            if let Some(simple_step) = self.active_set.simplify(step) {
                if simple_step.clause.is_impossible() {
                    return Some(self.report_contradiction(simple_step));
                }
                self.passive_set.push(simple_step);
            }
        }

        // Sometimes we find a bunch of contradictions at once.
        // It doesn't really matter what we pick, so we guess which is most likely
        // to be aesthetically pleasing.
        // First regular contradictions (in the loop above), then term graph.

        if let Some(contradiction) = self.active_set.graph.get_contradiction() {
            return Some(self.report_term_graph_contradiction(contradiction));
        }

        None
    }

    // Searches with a short duration.
    // Designed to be called multiple times in succession.
    // The time-based limit is set low, so that it feels interactive.
    pub fn partial_search(&mut self) -> Outcome {
        self.search_for_contradiction(10000, 0.1, false)
    }

    // Search in verification mode to see if this goal can be easily proven.
    // The time-based limit is set high enough so that hopefully it will not apply,
    // because we don't want the result of verification to be machine-dependent.
    pub fn verification_search(&mut self) -> Outcome {
        self.search_for_contradiction(3000, 4.0, true)
    }

    // A single fast search, intended for unit testing.
    pub fn quick_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.05, false)
    }

    // A restricted verification search, intended for unit testing.
    pub fn quick_verification_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.05, true)
    }

    // When 'verification' flag is set, the prover doesn't have to do arbitrarily deeply.
    // It is allowed to finish as soon as it finishes checking all the verification steps.
    pub fn search_for_contradiction(
        &mut self,
        size: i32,
        seconds: f32,
        verification: bool,
    ) -> Outcome {
        if self.error.is_some() {
            return Outcome::Error;
        }
        let start_time = std::time::Instant::now();
        loop {
            if verification && !self.passive_set.verification_phase {
                return Outcome::Exhausted;
            }
            if let Some(outcome) = self.activate_next() {
                return outcome;
            }
            for stop_flag in &self.stop_flags {
                if stop_flag.load(std::sync::atomic::Ordering::Relaxed) {
                    return Outcome::Interrupted;
                }
            }
            if self.active_set.len() >= size as usize {
                if self.verbose {
                    println!("active set size hit the limit: {}", self.active_set.len());
                }
                return Outcome::Constrained;
            }
            let elapsed = start_time.elapsed().as_secs_f32();
            if elapsed >= seconds {
                if self.verbose {
                    println!("active set size: {}", self.active_set.len());
                    println!("prover hit time limit after {} seconds", elapsed);
                }
                return Outcome::Timeout;
            }
        }
    }

    fn display<'a>(&'a self, clause: &'a Clause) -> DisplayClause<'a> {
        DisplayClause {
            clause,
            normalizer: &self.normalizer,
        }
    }

    fn get_clause(&self, id: ProofStepId) -> &Clause {
        match id {
            ProofStepId::Active(i) => self.active_set.get_clause(i),
            ProofStepId::Passive(i) => &self.useful_passive[i as usize].clause,
            ProofStepId::Final => {
                let (final_step, _) = self.result.as_ref().unwrap();
                &final_step.clause
            }
        }
    }

    // Attempts to convert this clause to code, but shows the clause form if that's all we can.
    fn clause_to_code(&self, bindings: Option<&BindingMap>, clause: &Clause) -> String {
        if let Some(bindings) = bindings {
            let denormalized = self.normalizer.denormalize(clause);

            if let Ok(code) = bindings.value_to_code(&denormalized) {
                return code;
            }
        }
        self.display(clause).to_string()
    }

    // Convert a clause to a jsonable form
    // We only take active ids, because the others have no external meaning.
    // If we are given a binding map, use it to make a nicer-looking display.
    pub fn to_clause_info(
        &self,
        bindings: Option<&BindingMap>,
        id: Option<usize>,
        clause: &Clause,
    ) -> ClauseInfo {
        let text = if clause.is_impossible() {
            None
        } else {
            Some(self.clause_to_code(bindings, clause))
        };
        ClauseInfo { text, id }
    }

    fn to_proof_step_info(
        &self,
        project: &Project,
        active_id: Option<usize>,
        step: &ProofStep,
    ) -> ProofStepInfo {
        let bindings = project.get_env(self.module_id).map(|env| &env.bindings);
        let clause = self.to_clause_info(bindings, active_id, &step.clause);
        let mut premises = vec![];
        for (description, id) in self.descriptive_dependencies(&step) {
            let clause = self.get_clause(id);
            let clause_info = self.to_clause_info(bindings, id.active_id(), clause);
            premises.push((description, clause_info));
        }
        let (rule, location) = match &step.rule {
            Rule::Assumption(info) => {
                let location = project
                    .path_from_module(info.source.module)
                    .and_then(|path| Url::from_file_path(path).ok())
                    .map(|uri| Location {
                        uri,
                        range: info.source.range,
                    });

                (info.source.description(), location)
            }
            _ => (step.rule.name().to_lowercase(), None),
        };
        ProofStepInfo {
            clause,
            premises,
            rule,
            location,
            depth: step.depth,
        }
    }

    pub fn to_proof_info(&self, project: &Project, proof: &Proof) -> Vec<ProofStepInfo> {
        let mut result = vec![];
        for (step_id, step) in &proof.all_steps {
            result.push(self.to_proof_step_info(project, step_id.active_id(), step));
        }
        result
    }

    // Generates information about a clause in jsonable format.
    // Returns None if we don't have any information about this clause.
    pub fn info_result(&self, project: &Project, id: usize) -> Option<InfoResult> {
        // Information for the step that proved this clause
        if !self.active_set.has_step(id) {
            return None;
        }
        let step = self.to_proof_step_info(project, Some(id), self.active_set.get_step(id));
        let mut consequences = vec![];
        let mut num_consequences = 0;
        let limit = 100;

        // Check if the final step is a consequence of this clause
        if let Some((final_step, _)) = &self.result {
            if final_step.depends_on_active(id) {
                consequences.push(self.to_proof_step_info(project, None, &final_step));
                num_consequences += 1;
            }
        }

        // Check the active set for consequences
        for (i, step) in self.active_set.find_consequences(id) {
            if consequences.len() < limit {
                consequences.push(self.to_proof_step_info(project, Some(i), step));
            }
            num_consequences += 1;
        }

        // Check the passive set for consequences
        for step in self.passive_set.find_consequences(id) {
            if consequences.len() < limit {
                consequences.push(self.to_proof_step_info(project, None, step));
            }
            num_consequences += 1;
        }

        Some(InfoResult {
            step,
            consequences,
            num_consequences,
        })
    }
}
