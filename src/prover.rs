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
use crate::goal_context::{Goal, GoalContext};
use crate::interfaces::{ClauseInfo, InfoResult, Location, ProofStepInfo};
use crate::literal::Literal;
use crate::module::ModuleId;
use crate::normalizer::{Normalization, NormalizationError, Normalizer};
use crate::passive_set::PassiveSet;
use crate::project::Project;
use crate::proof::Proof;
use crate::proof_step::{ProofStep, ProofStepId, Rule, Truthiness};
use crate::proposition::Proposition;
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

    // If a trace string is set, we print out what happens with the clause matching it, regardless
    // of verbosity.
    trace: Option<String>,

    // Whether we have hit the trace
    pub hit_trace: bool,

    // The result of the proof search, if there is one.
    // If we haven't found a result yet, this is None. The prover can still return an Outcome
    // that indicates a temporary outcome, like a timeout.
    result: Option<(ProofStep, Outcome)>,

    // Clauses that we never activated, but we did use to find a contradiction.
    useful_passive: Vec<ProofStep>,

    // Setting any of these flags to true externally will stop the prover.
    pub stop_flags: Vec<Arc<AtomicBool>>,

    // Whether we should report Outcome::Inconsistent when our assumptions lead to a
    // contradiction. Otherwise we just treat it as a success.
    report_inconsistency: bool,

    // The normalized term we are solving for, if there is one.
    solve: Option<Term>,

    // When this error message is set, it indicates a problem that needs to be reported upstream
    // to the user.
    // It's better to catch errors before proving, but sometimes we don't.
    pub error: Option<String>,

    // A value expressing the negation of the goal we are trying to prove, if there is one.
    negated_goal: Option<AcornValue>,
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
            trace: None,
            hit_trace: false,
            result: None,
            stop_flags: vec![project.build_stopped.clone()],
            report_inconsistency: !goal_context.includes_explicit_false(),
            error: None,
            solve: None,
            useful_passive: vec![],
            negated_goal: None,
        };

        // Find the relevant facts that should be imported into this environment
        let mut imported_facts = vec![];
        for dependency in project.all_dependencies(goal_context.module_id()) {
            let env = project.get_env(dependency).unwrap();
            imported_facts.extend(env.get_facts());
        }

        let (global_facts, local_facts) = goal_context.monomorphize(imported_facts);

        // Load facts into the prover
        for fact in global_facts {
            p.add_assumption(fact, Truthiness::Factual);
        }
        p.normalizer.global_done = true;
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

    pub fn set_trace(&mut self, trace: &str) {
        self.trace = Some(trace.to_string());
    }

    pub fn unset_trace(&mut self) {
        self.trace = None;
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
        let clauses = match self.normalize_proposition(assumption.value) {
            Normalization::Clauses(clauses) => clauses,
            Normalization::Impossible => {
                // We have a false assumption, so we're done already.
                let final_step =
                    ProofStep::new_assumption(Clause::impossible(), truthiness, &assumption.source);
                self.report_contradiction(final_step);
                return;
            }
            Normalization::Error(s) => {
                self.error = Some(s);
                return;
            }
        };
        for clause in clauses {
            let step = ProofStep::new_assumption(clause, truthiness, &assumption.source);
            self.passive_set.push(step);
        }
    }

    fn is_tracing(&mut self, clause: &Clause) -> bool {
        if let Some(trace) = &self.trace {
            let answer = self.display(clause).to_string().starts_with(trace);
            if answer {
                self.hit_trace = true;
            }
            answer
        } else {
            false
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
                    "short resolver".to_string(),
                    ProofStepId::Active(info.short_id),
                ));
                answer.push((
                    "long resolver".to_string(),
                    ProofStepId::Active(info.long_id),
                ));
            }
            Rule::Rewrite(info) => {
                answer.push(("pattern".to_string(), ProofStepId::Active(info.pattern_id)));
                answer.push(("target".to_string(), ProofStepId::Active(info.target_id)));
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
            step.depth(),
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

    pub fn print_proof(&self) {
        let proof = match self.get_proof() {
            Some(proof) => proof,
            None => {
                println!("we do not have a proof");
                return;
            }
        };

        println!(
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );

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
        let mut proof = Proof::new(&self.normalizer, negated_goal);
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
        let outcome = if step.truthiness != Truthiness::Counterfactual && self.report_inconsistency
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

            // Check whether we need to explicitly add a specialized clause to make
            // this rewrite a basic proof.
            match rewrite_info.subterm_depth {
                None | Some(0) => {
                    // No extra specialized clause needed
                    active_ids.push(rewrite_info.pattern_id);
                    max_depth = max_depth.max(rewrite_step.depth());
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
            max_depth = max_depth.max(step.depth());
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
            passive_step.basic = true;
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

        let tracing = self.is_tracing(&step.clause);
        let verbose = self.verbose || tracing;

        if step.clause.is_impossible() {
            return Some(self.report_contradiction(step));
        }

        if verbose {
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
        self.activate(step, verbose, tracing)
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
    fn activate(
        &mut self,
        activated_step: ProofStep,
        verbose: bool,
        tracing: bool,
    ) -> Option<Outcome> {
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
        if verbose && len > 0 {
            println!(
                "generated {} new clauses{}:",
                len,
                if len > print_limit { ", eg" } else { "" }
            );
        }
        for (i, step) in generated_clauses.into_iter().enumerate() {
            if step.finishes_proof() {
                return Some(self.report_contradiction(step));
            }

            if step.automatic_reject() {
                continue;
            }

            if tracing {
                self.print_proof_step("", &step);
            } else if verbose && (i < print_limit) {
                println!("  {}", self.display(&step.clause));
            } else if self.is_tracing(&step.clause) {
                self.print_proof_step("", &step);
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

    // Search to see if this goal can be satisfied using "basic" reasoning.
    // Basic reasoning is reasoning that we consider okay to leave implicit in the code.
    // The time-based limit is set high enough so that hopefully it will not apply,
    // because we want the standard to be deterministic.
    pub fn basic_search(&mut self) -> Outcome {
        self.search_for_contradiction(3000, 4.0, true)
    }

    // A single fast search, intended for most unit testing.
    pub fn quick_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.05, false)
    }

    pub fn quick_basic_search(&mut self) -> Outcome {
        self.search_for_contradiction(500, 0.05, true)
    }

    // If basic_only is set, we only search for a basic proof.
    pub fn search_for_contradiction(
        &mut self,
        size: i32,
        seconds: f32,
        basic_only: bool,
    ) -> Outcome {
        if self.error.is_some() {
            return Outcome::Error;
        }
        let start_time = std::time::Instant::now();
        loop {
            if basic_only && !self.passive_set.has_basic() {
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
            Rule::Assumption(source) => {
                let location = project
                    .path_from_module(source.module)
                    .and_then(|path| Url::from_file_path(path).ok())
                    .map(|uri| Location {
                        uri,
                        range: source.range,
                    });

                (source.description(), location)
            }
            _ => (step.rule.name().to_lowercase(), None),
        };
        ProofStepInfo {
            clause,
            premises,
            rule,
            location,
            depth: step.depth(),
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

#[cfg(test)]
mod tests {
    use crate::code_gen_error::CodeGenError;
    use crate::project::Project;

    use super::*;

    // Tries to prove one thing from the project.
    // If the proof is successful, try to generate the code.
    fn prove(
        project: &mut Project,
        module_name: &str,
        goal_name: &str,
    ) -> (Outcome, Result<Vec<String>, CodeGenError>) {
        let module_id = project.load_module(module_name).expect("load failed");
        let env = project.get_env(module_id).unwrap();
        let goal_context = env.get_goal_context_by_name(goal_name);
        let mut prover = Prover::new(&project, &goal_context, false);
        prover.verbose = true;
        let outcome = prover.quick_search();
        if outcome == Outcome::Error {
            panic!("prover error: {}", prover.error.unwrap());
        }
        let code = match prover.get_proof() {
            Some(proof) => proof.to_code(&env.bindings),
            None => Err(CodeGenError::NoProof),
        };
        prover.print_proof();
        (outcome, code)
    }

    fn prove_as_main(text: &str, goal_name: &str) -> (Outcome, Result<Vec<String>, CodeGenError>) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        prove(&mut project, "main", goal_name)
    }

    // Does one proof on the provided text.
    fn prove_text(text: &str, goal_name: &str) -> Outcome {
        prove_as_main(text, goal_name).0
    }

    // Verifies all the goals in the provided text, returning any non-Success outcome.
    fn verify(text: &str) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        let module_id = project.load_module("main").expect("load failed");
        let env = project.get_env(module_id).expect("get_env failed");
        let paths = env.goal_paths();
        for path in paths {
            let goal_context = env.get_goal_context(&path).unwrap();
            println!("proving: {}", goal_context.name);
            let mut prover = Prover::new(&project, &goal_context, false);
            prover.verbose = true;
            let outcome = prover.quick_basic_search();
            if outcome != Outcome::Success {
                return outcome;
            }
        }
        Outcome::Success
    }

    fn verify_succeeds(text: &str) {
        assert_eq!(verify(text), Outcome::Success);
    }

    fn verify_not_basic(text: &str) {
        assert_eq!(verify(text), Outcome::Exhausted);
    }

    fn expect_proof(text: &str, goal_name: &str, expected: &[&str]) {
        let (outcome, code) = prove_as_main(text, goal_name);
        assert_eq!(outcome, Outcome::Success);
        let actual = code.expect("code generation failed");
        assert_eq!(actual, expected);
    }

    // Expects the prover to find a proof but then fail to generate code.
    // fn expect_code_gen_error(text: &str, goal_name: &str, expected: &str) {
    //     let (outcome, code) = prove_as_main(text, goal_name);
    //     assert_eq!(outcome, Outcome::Success);
    //     assert_eq!(code.unwrap_err().error_type(), expected);
    // }

    const THING: &str = r#"
    type Thing: axiom
    let t: Thing = axiom
    let t2: Thing = axiom
    let f: Thing -> Bool = axiom
    let g: (Thing, Thing) -> Thing = axiom
    let h: Thing -> Thing = axiom
    "#;

    // Does one proof in the "thing" environment.
    fn prove_thing(text: &str, goal_name: &str) -> Outcome {
        let text = format!("{}\n{}", THING, text);
        prove_text(&text, goal_name)
    }

    #[test]
    fn test_specialization() {
        let text = r#"
            axiom f_all(x: Thing) { f(x) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let text = r#"
            axiom f_one { f(t) }
            theorem goal(x: Thing) { f(x) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_axiomatic_values_distinct() {
        let text = "theorem goal { t = t2 }";
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_finds_example() {
        let text = r#"
            axiom f_one { f(t) }
            theorem goal { exists(x: Thing) { f(x) } }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let text = r#"
            axiom not_f(x: Thing) { not f(x) }
            theorem goal { not f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_equality() {
        let text = r#"
            axiom t_eq_t2 { t = t2 }
            theorem goal { f(t) = f(t2)  }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition() {
        let text = r#"
            axiom g_id(x: Thing) { g(x, x) = x }
            axiom f_t { f(t) }
            theorem goal { f(g(t, t)) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    // #[test]
    // fn test_composition_can_fail() {
    //     let text = r#"
    //         axiom f_t: f(t)
    //         axiom g_id(x: Thing): g(x, x) = x
    //         theorem goal { f(g(t, t2)) }
    //         "#;
    //     assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    // }

    #[test]
    fn test_negative_rewriting() {
        let text = r#"
            axiom not_f_t { not f(t) }
            axiom g_id(x: Thing) { g(x, x) = x }
            theorem goal { not f(g(t, t)) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_ne() {
        let text = r#"
            axiom f_t_ne_f_t2 { f(t) != f(t2) }
            theorem goal { t != t2 }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let text = r#"
            axiom foo(x: Thing) { x != t or f(t) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let text = r#"
            axiom foo(x: Thing, y: Thing) { x = t or y = t }
            theorem goal(x: Thing) { x = t2 }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_existence_of_nonequality() {
        // After normalization, this is the same problem as the equality
        // factoring test above. So if one of them works and one doesn't,
        // it's likely to be a prioritization dependency problem.
        let text = r#"
            axiom foo { exists(x: Thing) { x != t2 } }
            theorem goal { exists(x: Thing) { x != t } }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_avoids_loops() {
        let text = r#"
            axiom trivial(x: Thing) { not f(h(x)) or f(h(x)) }
            axiom arbitrary(x: Thing) { f(h(x)) or f(x) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) or f(h(t)) }
            theorem goal { f(t2) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_higher_order_unification() {
        let text = r#"
            axiom foo(x: Thing -> Bool) { x(t) }
            theorem goal { f(t) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_theorem_block() {
        let text = r#"
            type Thing: axiom
            let t: Thing = axiom
            theorem reflexivity(x: Thing) {
                x = x
            } by {
                reflexivity(t)
            }
            "#;

        expect_proof(text, "reflexivity(t)", &[]);
    }

    #[test]
    fn test_proof_inside_forall_block() {
        let text = r#"
            type Thing: axiom
            let t: Thing = axiom
            let foo: Thing -> Bool = axiom
            axiom foo_t { foo(t) }
            forall(x: Thing) {
                x = t -> foo(x)
            }
            "#;

        expect_proof(text, "x = t -> foo(x)", &[]);
    }

    #[test]
    fn test_proof_inside_if_block() {
        let text = r#"
            type Thing: axiom
            forall(x: Thing, y: Thing) {
                if x = y {
                    x = y
                }
            }
            "#;
        expect_proof(text, "x = y", &[]);
    }

    #[test]
    fn test_extracting_narrow_proof() {
        let text = r#"
            let b: Bool = axiom
            let f1: Bool -> Bool = axiom
            let f2: Bool -> Bool = axiom
            let f3: Bool -> Bool = axiom
            let f4: Bool -> Bool = axiom
            axiom a1 { f1(b) }
            axiom a12(x: Bool) { f1(x) -> f2(x) }
            axiom a23(x: Bool) { f2(x) -> f3(x) }
            axiom a34(x: Bool) { f3(x) -> f4(x) }
            theorem goal(x: Bool) { f4(b) }
        "#;
        expect_proof(text, "goal", &["f2(b)", "f3(b)"]);
    }

    #[test]
    fn test_rewriting_confluence_indirectly() {
        // The facts given by "axiom recursion_base" and "define add" are
        // each rewrite rules.
        // To prove add_zero_right, the naive way applies one backward and one
        // forward rewrite.
        // We need to be able to handle this somehow.
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
            axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
            define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }
            theorem add_zero_right(a: Nat) { add(a, zero) = a }
        "#;
        expect_proof(text, "add_zero_right", &[]);
    }

    #[test]
    fn test_second_literal_matches_goal() {
        let text = r#"
            axiom axiom1 { f(g(t, t)) or f(t2) }
            axiom axiom2 { not f(g(t, t)) or f(t2) }
            theorem goal { f(t2) }
        "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_closure_proof() {
        let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
            theorem goal(a: Nat, b: Nat) { addx(a, b) = adder(a)(b) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_boolean_equality() {
        let text = r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define ltex(a: Nat, b: Nat) -> Bool { exists(c: Nat) { addx(a, c) = b } }
            define ltx(a: Nat, b: Nat) -> Bool { ltex(a, b) and a != b }
            theorem goal(a: Nat) { not ltx(a, a) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let suc: Nat -> Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom one_neq_zero { one != zero }
            theorem goal { exists(x: Nat) { one = suc(x) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_another_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat) { a = zero or exists(b: Nat) { a = suc(b) } }
            axiom y_not_zero { y != zero }
            theorem goal { y = zero or exists(b: Nat) { y = suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_new_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(p: Pair) { p = Pair.new(Pair.first(p), Pair.second(p)) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_first_member_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(a: Bool, b: Bool) { Pair.first(Pair.new(a, b)) = a }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_structure_second_member_equation() {
        let text = r#"
            structure Pair {
                first: Bool
                second: Bool
            }
            theorem goal(a: Bool, b: Bool) { Pair.second(Pair.new(a, b)) = b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_no_confusion_property() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat) { Nat.suc(a) != Nat.zero }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_canonical_form_principle() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat) { a = Nat.zero or exists(b: Nat) { a = Nat.suc(b) } }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_inductive_constructors_injective() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            theorem goal(a: Nat, b: Nat) { Nat.suc(a) = Nat.suc(b) -> a = b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_gets_structural_induction() {
        let text = r#"
            inductive Nat {
                zero
                suc(Nat)
            }
            let f: Nat -> Bool = axiom
            axiom base {
                f(Nat.zero)
            }
            axiom step(k: Nat) {
                f(k) -> f(k.suc)
            }
            theorem goal(n: Nat) {
                f(n)
            }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T) {
                a = b and b = c -> a = c
            } by {
                if (a = b and b = c) {
                    a = c
                }
            }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem_no_block() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T) { a = b and b = c -> a = c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_citing_parametric_theorem() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            theorem foo<T>(a: T) { a = a }
            theorem goal { foo(zero) }
        "#,
        );
    }

    #[test]
    fn test_applying_parametric_function() {
        let text = r#"
            type Nat: axiom
            define foo<T>(a: T) -> Bool { (a = a) }
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parametric_definition_and_theorem() {
        let text = r#"
            define foo<T>(a: T) -> Bool { axiom }
            axiom foo_true<T>(a: T) { foo(a) }
            type Nat: axiom
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parameter_name_can_change() {
        let text = r#"
            define foo<T>(a: T) -> Bool { axiom }
            axiom foo_true<U>(a: U) { foo(a) }
            type Nat: axiom
            let zero: Nat = axiom
            theorem goal { foo(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_inconsistency() {
        let text = r#"
            type Nat: axiom
            let zero: Nat = axiom
            let foo: Nat -> Bool = axiom
            let bar: Nat -> Bool = axiom
            axiom foo_true { foo(zero) }
            axiom foo_false { not foo(zero) }
            theorem goal { bar(zero) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_using_true_and_false_in_a_proof() {
        let text = r#"
        theorem goal(b: Bool) { b = true or b = false }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_mildly_nontrivial_inconsistency() {
        let text = r#"
            axiom bad { true = false }
            let b: Bool = axiom
            theorem goal { b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_proving_explicit_false_okay() {
        verify_succeeds(
            r#"
            let b: Bool = axiom
            if b != b {
                false
            }
        "#,
        );
    }

    #[test]
    fn test_subsequent_explicit_false_ok() {
        verify_succeeds(
            r#"
            let b: Bool = axiom
            if b != b {
                b or not b
                false
            }
        "#,
        );
    }

    #[test]
    fn test_explicit_false_mandatory() {
        let text = r#"
            let b: Bool = axiom
            let c: Bool = axiom
            if b != b {
                c
            }
        "#;
        assert_eq!(verify(text), Outcome::Inconsistent);
    }

    #[test]
    fn test_verify_if_else_function() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            define sign(a: Nat) -> Nat {
                if a = zero {
                    zero
                } else {
                    one
                }
            }
            theorem goal(a: Nat) {
                sign(a) = zero or sign(a) = one
            }
        "#,
        );
    }

    #[test]
    fn test_verify_complicated_theorem_application() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let a: Nat = axiom
            let b: Nat = axiom
            let c: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom trans(x: Nat, y: Nat, z: Nat) {
                f(x, y) and f(y, z) -> f(x, z)
            }
            axiom fab { f(a, b) }
            axiom fbc { f(b, c) }
            theorem goal {
                f(a, c)
            }
            "#,
        );
    }

    #[test]
    fn test_verify_existence_theorem() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let a: Nat = axiom
            let f: Nat -> Bool = axiom
            let g: (Nat, Nat) -> Bool = axiom
            axiom foo(x: Nat) {
                f(x) -> exists(y: Nat) { g(x, y) and g(y, x) }
            }
            theorem goal {
                f(a) -> exists(y: Nat) { g(a, y) and g(y, a) }
            }
            "#,
        );
    }

    #[test]
    fn test_rewrite_consistency() {
        // In practice this caught an inconsistency that came from bad rewrite logic.
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            let mulx: (Nat, Nat) -> Nat = axiom
            axiom add_suc(a: Nat, b: Nat) { addx(suc(a), b) = suc(addx(a, b)) }
            axiom suc_ne(a: Nat) { suc(a) != a }
            axiom mul_suc(a: Nat, b: Nat) { addx(a, mulx(a, b)) = mulx(a, suc(b)) }
            theorem goal(a: Nat) { suc(a) != a }
        "#,
        );
    }

    #[test]
    fn test_normalization_failure_doesnt_crash() {
        // We can't normalize lambdas inside function calls, but we shouldn't crash on them.
        verify(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            define apply(f: Nat -> Nat, a: Nat) -> Nat { f(a) }
            theorem goal { apply(function(x: Nat) { x }, zero) = zero }
        "#,
        );
    }

    #[test]
    fn test_functional_equality_definition() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let f: Nat -> Nat = axiom
            let g: Nat -> Nat = axiom
            theorem goal { forall(x: Nat) { f(x) = g(x) } -> f = g }
        "#,
        );
    }

    // These tests involve proving functional equality. They don't work right.
    //
    // #[test]
    // fn test_verify_functional_definition() {
    //     verify_succeeds(
    //         r#"
    //         type Nat: axiom
    //         define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
    //         define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
    //         let p: Nat = axiom
    //         let f: Nat -> Bool = is_min(gcd_term(p))

    //         theorem goal { is_min(gcd_term(p)) = f }
    //     "#,
    //     );
    // }
    // #[test]
    // fn test_functional_substitution() {
    //     prove_all_succeeds(
    //         r#"
    //         type Nat: axiom
    //         define find(f: Nat -> Bool) -> Nat { axiom }
    //         define is_min(f: Nat -> Bool) -> (Nat -> Bool) { axiom }
    //         define gcd_term(p: Nat) -> (Nat -> Bool) { axiom }
    //         let p: Nat = axiom
    //         let f: Nat -> Bool = is_min(gcd_term(p))
    //         theorem goal { find(is_min(gcd_term(p))) = find(f) }
    //     "#,
    //     );
    // }
    //
    // #[test]
    // fn test_functional_equality_implication() {
    //     prove_all_succeeds(
    //         r#"
    //         type Nat: axiom
    //         let f: Nat -> Nat = axiom
    //         let g: Nat -> Nat = axiom
    //         let p: (Nat -> Nat) -> Nat = axiom
    //         theorem goal { forall(x: Nat) { f(x) = g(x) } -> p(f) = p(g) }
    //         "#,
    //     );
    // }

    #[test]
    fn test_proving_with_partial_application() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal(f: Nat -> Nat) { f = addx(zero) -> f(zero) = addx(zero, zero) }
        "#,
        );
    }

    #[test]
    fn test_using_imported_axiom() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/bar.ac",
            r#"
            type Bar: axiom
            let bar: Bar = axiom
            let morph: Bar -> Bar = axiom
            axiom meq(b: Bar) { morph(b) = morph(bar) }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import bar
            theorem goal(a: bar.Bar, b: bar.Bar) { bar.morph(a) = bar.morph(b) }
        "#,
        );
        let (outcome, _) = prove(&mut p, "main", "goal");
        assert_eq!(outcome, Outcome::Success);
    }

    #[test]
    fn test_backward_nonbranching_reasoning() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let suc: Nat -> Nat = axiom
            axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) -> x = y }
            let n: Nat = axiom
            axiom hyp { suc(n) != n }
            theorem goal { suc(suc(n)) != suc(n) }
        "#,
        )
    }

    #[test]
    fn test_basic_unification() {
        verify_succeeds(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let f: (Nat, Nat) -> Bool = axiom
            axiom f_zero_right(x: Nat) { f(x, zero) }
            theorem goal { exists(x: Nat) { f(zero, x) } }
        "#,
        );
    }

    #[test]
    fn test_indirect_proof_collapses() {
        let text = r#"
            let a: Bool = axiom
            let b: Bool = axiom
            axiom bimpa { b -> a }
            axiom bimpna { b -> not a }
            theorem goal { not b }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_generation_with_forall_goal() {
        let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg { forall(x: Nat) { f(x) -> g(x) } }
            axiom gimph { forall(x: Nat) { g(x) -> h(x) } }
            theorem goal { forall(x: Nat) { f(x) -> h(x) } }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_generation_with_intermediate_skolem() {
        let text = r#"
        type Nat: axiom
        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom forg(x: Nat) { f(x) or g(x) }
        axiom fgimpb { forall(x: Nat) { f(x) or g(x) } -> b }
        theorem goal { b }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_assuming_lhs_of_implication() {
        verify_succeeds(
            r#"
            let a: Bool = axiom
            let b: Bool = axiom
            let c: Bool = axiom
            axiom aimpb { a -> b }
            axiom bimpc { b -> c }
            theorem goal { a -> c } by {
                b
            }
        "#,
        );
    }

    #[test]
    fn test_templated_proof() {
        let text = r#"
            type Thing: axiom
            let t1: Thing = axiom
            let t2: Thing = axiom
            let t3: Thing = axiom
            
            define foo<T>(x: T) -> Bool { axiom }

            axiom a12 { foo(t1) -> foo(t2) }
            axiom a23 { foo(t2) -> foo(t3) }
            theorem goal { foo(t1) -> foo(t3) }
            "#;

        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_using_else() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        if a {
            b
        } else {
            c
        }
        theorem goal { not a -> c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_else_when_missing_if_block() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        if a {
        } else {
            b
        }
        theorem goal { not a -> b }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_with_diamond_logic() {
        // This is a tricky one to simplify because one clause has two consequences
        // that combine.
        let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        define add(a: Nat, b: Nat) -> Nat { axiom }
        theorem add_zero_left(a: Nat) { add(zero, a) = a }
        
        theorem add_to_zero(a: Nat, b: Nat) {
            add(a, b) = zero -> a = zero and b = zero
        } by {
            define f(x: Nat) -> Bool { add_to_zero(x, b) }
            f(zero)
        }
        "#;

        expect_proof(
            text,
            "f(zero)",
            &[
                "if not add_to_zero(zero, b) {",
                "\tb != zero",
                "\tfalse",
                "}",
            ],
        );
    }

    #[test]
    fn test_proof_condensing_induction() {
        let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let suc: Nat -> Nat = axiom
        axiom induction(f: Nat -> Bool) {
            f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) }
        }
        let foo: Nat -> Bool = axiom
        theorem goal { foo(zero) and forall(k: Nat) { foo(k) -> foo(suc(k)) } -> forall(n: Nat) { foo(n) } }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_condensing_false() {
        let text = r#"
        let a: Bool = axiom
        axiom a_true { a }
        if not a {
            false
        }
        "#;
        expect_proof(text, "false", &[]);
    }

    #[test]
    fn test_proof_condensing_combining_two_theorems() {
        let text = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        axiom fimpg(x: Nat) { f(x) -> g(x) }
        axiom fa { f(a) }
        theorem goal { g(a) }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_indirect_from_goal() {
        let text = r#"
            type Nat: axiom
            let f: Nat -> Bool = axiom
            let g: Nat -> Bool = axiom
            let h: Nat -> Bool = axiom
            axiom fimpg(x: Nat) { f(x) -> g(x) }
            axiom gimph(x: Nat) { g(x) -> h(x) }
            axiom fimpnh(x: Nat) { f(x) -> not h(x) }
            theorem goal(x: Nat) { not f(x) }
        "#;
        expect_proof(text, "goal", &["if f(x) {", "\tg(x)", "\tfalse", "}"]);
    }

    #[test]
    fn test_nested_if_else() {
        let text = r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        if a {
            if b {
                c
            } else {
                c
            }
        }
        theorem goal { a -> c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_infix_addition_goes_left_to_right() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.add(a, b), c) = a + b + c }
        theorem antigoal(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.add(b, c)) = a + b + c }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
        assert_eq!(prove_text(text, "antigoal"), Outcome::Exhausted);
    }

    #[test]
    fn test_infix_mul_before_plus() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define add(self, other: Nat) -> Nat { axiom }
            define mul(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat, b: Nat, c: Nat) { Nat.add(Nat.mul(a, b), c) = a * b + c }
        theorem goal2(a: Nat, b: Nat, c: Nat) { Nat.add(a, Nat.mul(b, c)) = a + b * c }
        "#;
        assert_eq!(prove_text(text, "goal1"), Outcome::Success);
        assert_eq!(prove_text(text, "goal2"), Outcome::Success);
    }

    #[test]
    fn test_ways_to_call_methods() {
        let text = r#"
        type Nat: axiom
        class Nat {
            define suc(self) -> Nat { axiom }
            define add(self, other: Nat) -> Nat { axiom }
        }
        theorem goal1(a: Nat) { a.suc.suc = Nat.suc(Nat.suc(a)) }
        theorem goal2(a: Nat) { a.suc.suc = Nat.suc(a).suc }
        theorem goal3(a: Nat, b: Nat) { (a + b).suc = Nat.suc(Nat.add(a, b)) }
        "#;
        assert_eq!(prove_text(text, "goal1"), Outcome::Success);
        assert_eq!(prove_text(text, "goal2"), Outcome::Success);
        assert_eq!(prove_text(text, "goal3"), Outcome::Success);
    }

    #[test]
    fn test_bag_of_digits() {
        let text = r#"
        type Bag: axiom
        class Bag {
            let 1: Bag = axiom
            let 2: Bag = axiom
            define read(self, other: Bag) -> Bag { axiom }
        }
        numerals Bag
        axiom comm(a: Bag, b: Bag) { a.read(b) = b.read(a) }
        theorem goal { 12 = 21 }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_verify_function_satisfy() {
        let text = r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        axiom zero_neq_one { zero != one }
        let flip(a: Nat) -> b: Nat satisfy {
            a != b
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_not_basic_boolean_soup() {
        // This goal is not provable.
        // We should be able to quickly tell there is no basic proof.
        // I'm not sure what goes wrong, it's a mess of nested boolean formulas.
        let text = r#"
        theorem goal(a: Bool, b: Bool, c: Bool) {
            a = b or a = not c
        }
        "#;
        verify_not_basic(text);
    }

    #[test]
    fn test_not_basic_resolution_trap() {
        // This is a trap for the resolution algorithm, because repeated resolution
        // against the negated goal will give longer and longer formulas.
        let text = r#"
        type Nat: axiom
        let f: Nat -> Nat = axiom
        let g: Nat -> Bool = axiom
        let a: Nat = axiom
        axiom ga { g(a) }
        theorem goal {
            not forall(x: Nat) { g(x) -> g(f(x)) }
        }
        "#;
        verify_not_basic(text);
    }

    #[test]
    fn test_verify_if_else_theorem() {
        let text = r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        axiom fgh(a: Nat) {
            if f(a) {
                g(a)
            } else {
                h(a)
            }
        }
        theorem goal(a: Nat) {
            g(a) or h(a)
        }
        "#;
        verify_succeeds(text);
    }

    #[test]
    fn test_verify_function_satisfy_with_if_else() {
        let text = r#"
        type Nat: axiom
        let suc: Nat -> Nat = axiom
        let zero: Nat = axiom
        axiom base(a: Nat) {
            a = zero or exists(b: Nat) { a = suc(b) }
        }
        let pred(a: Nat) -> b: Nat satisfy {
            if a = zero {
                b = zero
            } else {
                suc(b) = a
            }
        } by {
            if a != zero {
                exists(b: Nat) { a = suc(b) }
            }
        }
        "#;
        verify_succeeds(text);
    }
}
