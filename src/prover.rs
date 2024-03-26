use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use crossbeam::queue::SegQueue;
use tower_lsp::lsp_types::Url;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::ActiveSet;
use crate::clause::Clause;
use crate::display::DisplayClause;
use crate::goal_context::GoalContext;
use crate::interfaces::{AssumptionInfo, ClauseInfo, InfoResult, ProofStepInfo};
use crate::located_value::LocatedValue;
use crate::normalizer::{Normalization, Normalizer};
use crate::passive_set::PassiveSet;
use crate::project::Project;
use crate::proof::Proof;
use crate::proof_step::{ProofStep, Rule, Truthiness};

pub struct Prover {
    // The normalizer is used when we are turning the facts and goals from the environment into
    // clauses that we can use internally.
    normalizer: Normalizer,

    // The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    passive_set: PassiveSet,

    // A verbose prover prints out a lot of stuff.
    pub verbose: bool,

    // When print queue is set, we send print statements here, instead of to stdout.
    pub print_queue: Option<Arc<SegQueue<String>>>,

    // If a trace string is set, we print out what happens with the clause matching it, regardless
    // of verbosity.
    trace: Option<String>,

    // Whether we have hit the trace
    pub hit_trace: bool,

    // The result of the proof search, if there is one.
    result: Option<(ProofStep, Outcome)>,

    // Setting any of these flags to true externally will stop the prover.
    pub stop_flags: Vec<Arc<AtomicBool>>,

    // Whether we should report Outcome::Inconsistent or just treat it as a success.
    report_inconsistency: bool,

    // When this error message is set, it indicates a problem that needs to be reported upstream
    // to the user.
    // It's better to catch errors before proving, and maybe in the ideal world we always would,
    // but right now we don't.
    pub error: Option<String>,
}

macro_rules! cprintln {
    ($obj:expr, $($arg:tt)*) => {
        match &$obj.print_queue {
            Some(queue) => {
                queue.push(format!($($arg)*));
            }
            None => {
                println!($($arg)*);
            }
        }
    };
}

// The outcome of a prover operation.
// "Success" means we proved it.
// "Exhausted" means we tried every possibility and couldn't prove it.
// "Inconsistent" means that we found a contradiction just in our initial assumptions.
// "Interrupted" means that the prover was explicitly stopped.
// "Unknown" means that we could keep working longer at it.
// "Error" means that we found a problem in the code that needs to be fixed by the user.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Unknown,
    Error,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Unknown => write!(f, "Unknown"),
            Outcome::Error => write!(f, "Error"),
        }
    }
}

impl Prover {
    pub fn new<'a>(
        project: &'a Project,
        goal_context: &'a GoalContext<'a>,
        verbose: bool,
        print_queue: Option<Arc<SegQueue<String>>>,
    ) -> Prover {
        let mut p = Prover {
            normalizer: Normalizer::new(),
            active_set: ActiveSet::new(),
            passive_set: PassiveSet::new(),
            verbose,
            print_queue,
            trace: None,
            hit_trace: false,
            result: None,
            stop_flags: vec![project.build_stopped.clone()],
            report_inconsistency: !goal_context.includes_explicit_false(),
            error: None,
        };

        // Find the relevant facts that should be imported into this environment
        let mut imported_facts = vec![];
        for dependency in project.all_dependencies(goal_context.module_id()) {
            let env = project.get_env(dependency).unwrap();
            imported_facts.extend(env.get_facts(project));
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
        let (hypo, counter) = goal_context.goal.value.to_placeholder().negate_goal();
        if let Some(hypo) = hypo {
            p.add_assumption(goal_context.goal.with_value(hypo), Truthiness::Hypothetical);
        }
        p.add_assumption(
            goal_context.goal.with_value(counter),
            Truthiness::Counterfactual,
        );
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

    fn add_assumption(&mut self, assumption: LocatedValue, truthiness: Truthiness) {
        let rule = Rule::new_assumption(&assumption);
        let clauses = match self.normalize_proposition(assumption.value) {
            Normalization::Clauses(clauses) => clauses,
            Normalization::Impossible => {
                // We have a false assumption, so we're done already.
                let final_step = ProofStep::new_assumption(
                    Clause::impossible(),
                    Truthiness::Factual,
                    rule.clone(),
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
            let step = ProofStep::new_assumption(clause, truthiness, rule.clone());
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
        cprintln!(self, "{} clauses in the active set", self.active_set.len());
        cprintln!(
            self,
            "{} clauses in the passive set",
            self.passive_set.len()
        );
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
            cprintln!(self, "{}", clause);
        }
        if let Some(substr) = substr {
            cprintln!(self, "{} active clauses matched {}", count, substr);
        } else {
            cprintln!(self, "{} clauses total in the active set", count);
        }
    }

    pub fn print_passive(&self, substr: Option<&str>) {
        let mut count = 0;
        let steps = self.passive_set.all_steps();
        // Only print the first ones
        for step in steps.iter().take(500) {
            let clause = self.display(&step.clause);
            if let Some(substr) = substr {
                if !clause.to_string().contains(substr) {
                    continue;
                }
            }
            count += 1;
            cprintln!(self, "{}", clause);
            cprintln!(self, "  {}", step);
        }
        if let Some(substr) = substr {
            cprintln!(self, "{} passive clauses matched {}", count, substr);
        } else {
            if steps.len() > count {
                cprintln!(self, "  ...omitting {} more", steps.len() - count);
            }
            cprintln!(self, "{} clauses total in the passive set", steps.len());
        }
    }

    // Prints out information for a specific term
    pub fn print_term_info(&self, s: &str) {
        let mut count = 0;
        for clause in self.active_set.iter_clauses() {
            let clause_str = self.display(clause).to_string();
            if clause_str.contains(s) {
                cprintln!(self, "{}", clause_str);
                count += 1;
            }
        }
        cprintln!(
            self,
            "{} clause{} matched",
            count,
            if count == 1 { "" } else { "s" }
        );
    }

    fn print_proof_step(&self, preface: &str, step: &ProofStep) {
        cprintln!(
            self,
            "\n{}{} generated:\n    {}",
            preface,
            step.rule.name(),
            self.display(&step.clause)
        );

        for (description, i) in step.descriptive_dependencies() {
            let c = self.display(self.active_set.get_clause(i));
            cprintln!(self, "  using {} {}:\n    {}", description, i, c);
        }
    }

    pub fn print_proof(&self) {
        let final_step = if let Some((final_step, _)) = &self.result {
            final_step
        } else {
            cprintln!(self, "we do not have a proof");
            return;
        };
        cprintln!(
            self,
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );

        let indices = self.active_set.find_upstream(&final_step);
        cprintln!(self, "the proof uses {} steps:", indices.len());
        for i in indices {
            let step = self.active_set.get_step(i);
            let preface = if step.is_negated_goal() {
                format!("clause {} (negating goal): ", i)
            } else {
                format!("clause {}: ", i)
            };
            self.print_proof_step(&preface, step);
        }
        self.print_proof_step("final step: ", final_step);
    }

    pub fn get_proof(&self) -> Option<Proof> {
        let final_step = if let Some((final_step, _)) = &self.result {
            final_step
        } else {
            return None;
        };
        let indices = self.active_set.find_upstream(&final_step);
        let mut proof = Proof::new(&self.normalizer, final_step.clone());
        for i in indices {
            let step = self.active_set.get_step(i);
            proof.add_step(i, step.clone());
        }
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

    // Activates the next clause from the queue, unless we're already done.
    pub fn activate_next(&mut self) -> Outcome {
        if let Some((_, outcome)) = &self.result {
            return *outcome;
        }

        let step = match self.passive_set.pop() {
            Some(step) => step,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                return Outcome::Exhausted;
            }
        };

        let tracing = self.is_tracing(&step.clause);
        let verbose = self.verbose || tracing;

        let mut original_clause_string = "".to_string();
        let mut simplified_clause_string = "".to_string();
        if verbose {
            original_clause_string = self.display(&step.clause).to_string();
        }

        let step = match self.active_set.simplify(step) {
            Some(i) => i,
            None => {
                // The clause is redundant, so skip it.
                if verbose {
                    cprintln!(self, "redundant: {}", original_clause_string);
                }
                return Outcome::Unknown;
            }
        };
        let clause = &step.clause;
        if verbose {
            simplified_clause_string = self.display(clause).to_string();
            if simplified_clause_string != original_clause_string {
                cprintln!(
                    self,
                    "simplified: {} => {}",
                    original_clause_string,
                    simplified_clause_string,
                );
            }
        }

        if clause.is_impossible() {
            return self.report_contradiction(step);
        }

        if verbose {
            let prefix = match step.truthiness {
                Truthiness::Factual => " fact",
                Truthiness::Hypothetical => " hypothesis",
                Truthiness::Counterfactual => {
                    if step.is_negated_goal() {
                        " negated goal"
                    } else {
                        ""
                    }
                }
            };
            cprintln!(self, "activating{}: {}", prefix, simplified_clause_string);
        }
        self.activate(step, verbose, tracing)
    }

    // Generates clauses, then simplifies them, then adds them to the passive set.
    // Clauses will get simplified again when they are activated.
    fn activate(&mut self, activated_step: ProofStep, verbose: bool, tracing: bool) -> Outcome {
        let generated_clauses = self.active_set.generate(activated_step);

        let print_limit = 30;
        let len = generated_clauses.len();
        if verbose && len > 0 {
            cprintln!(
                self,
                "generated {} new clauses{}:",
                len,
                if len > print_limit { ", eg" } else { "" }
            );
        }
        for (i, step) in generated_clauses.into_iter().enumerate() {
            if step.finishes_proof() {
                return self.report_contradiction(step);
            }

            if step.automatic_reject() {
                continue;
            }

            if tracing {
                self.print_proof_step("", &step);
            } else if verbose && (i < print_limit) {
                cprintln!(self, "  {}", self.display(&step.clause));
            } else if self.is_tracing(&step.clause) {
                self.print_proof_step("", &step);
            }

            if let Some(simple_step) = self.active_set.simplify(step) {
                if simple_step.clause.is_impossible() {
                    return self.report_contradiction(simple_step);
                }
                self.passive_set.push(simple_step);
            }
        }
        Outcome::Unknown
    }

    // A standard set of parameters, with a balance between speed and depth.
    // Useful for CLI or IDE when the user can wait a little bit.
    pub fn medium_search(&mut self) -> Outcome {
        self.search_for_contradiction(5000, 5.0)
    }

    // A set of parameters to use when we want to find an answer very quickly.
    // Useful for unit tests.
    // TODO: make this deterministic.
    pub fn quick_search(&mut self) -> Outcome {
        self.search_for_contradiction(2000, 0.05)
    }

    pub fn search_for_contradiction(&mut self, size: i32, seconds: f32) -> Outcome {
        if self.error.is_some() {
            return Outcome::Error;
        }
        let start_time = std::time::Instant::now();
        loop {
            let outcome = self.activate_next();
            if outcome != Outcome::Unknown {
                return outcome;
            }
            for stop_flag in &self.stop_flags {
                if stop_flag.load(std::sync::atomic::Ordering::Relaxed) {
                    return Outcome::Interrupted;
                }
            }
            if self.active_set.len() >= size as usize {
                if self.verbose {
                    cprintln!(
                        self,
                        "active set size hit the limit: {}",
                        self.active_set.len()
                    );
                }
                break;
            }
            let elapsed = start_time.elapsed().as_secs_f32();
            if elapsed >= seconds {
                if self.verbose {
                    cprintln!(self, "active set size: {}", self.active_set.len());
                    cprintln!(self, "prover hit time limit after {} seconds", elapsed);
                }
                break;
            }
        }
        Outcome::Unknown
    }

    fn display<'a>(&'a self, clause: &'a Clause) -> DisplayClause<'a> {
        DisplayClause {
            clause,
            normalizer: &self.normalizer,
        }
    }

    // Convert a clause to a jsonable form
    pub fn to_clause_info(&self, id: Option<usize>, clause: &Clause) -> ClauseInfo {
        ClauseInfo {
            text: self.display(clause).to_string(),
            id,
        }
    }

    fn to_proof_step_info(
        &self,
        project: &Project,
        id: Option<usize>,
        step: &ProofStep,
    ) -> ProofStepInfo {
        let clause = self.to_clause_info(id, &step.clause);
        let mut premises = vec![];
        for (description, i) in step.descriptive_dependencies() {
            let clause = self.to_clause_info(Some(i), self.active_set.get_clause(i));
            premises.push((description, clause));
        }
        let (rule, assumption) = match &step.rule {
            Rule::Assumption(info) => {
                let uri = match project.path_from_module(info.module) {
                    Some(path) => Url::from_file_path(path).ok(),
                    None => None,
                };
                let assumption = AssumptionInfo {
                    uri,
                    range: info.range,
                };
                let rule = match step.truthiness {
                    Truthiness::Factual => match &info.theorem_name {
                        Some(name) => format!("the '{}' theorem", name),
                        None => "an anonymous theorem".to_string(),
                    },
                    Truthiness::Hypothetical => "previous proof".to_string(),
                    Truthiness::Counterfactual => "negating the goal".to_string(),
                };
                (rule, Some(assumption))
            }
            _ => (step.rule.name().to_string(), None),
        };
        ProofStepInfo {
            clause,
            premises,
            rule,
            assumption,
        }
    }

    pub fn to_proof_info(&self, project: &Project, proof: &Proof) -> Vec<ProofStepInfo> {
        let mut result = vec![];
        for (i, step) in proof.iter_steps() {
            result.push(self.to_proof_step_info(project, i, step));
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

        // Check if the final step is a consequence of this clause
        if let Some((final_step, _)) = &self.result {
            if final_step.depends_on(id) {
                consequences.push(self.to_proof_step_info(project, None, &final_step));
            }
        }

        // Check the active set for consequences
        for (i, step) in self.active_set.find_consequences(id) {
            consequences.push(self.to_proof_step_info(project, Some(i), step));
        }

        // Check the passive set for consequences
        for step in self.passive_set.find_consequences(id) {
            consequences.push(self.to_proof_step_info(project, None, step));
        }

        Some(InfoResult { step, consequences })
    }
}

#[cfg(test)]
mod tests {
    use crate::module::Module;
    use crate::project::Project;

    use super::*;

    // Tries to prove one thing from the project.
    // If the proof is successful, try to generate the code.
    fn prove(
        project: &mut Project,
        module_name: &str,
        goal_name: &str,
    ) -> (Outcome, Result<Vec<String>, String>) {
        let module_id = project.load_module(module_name).expect("load failed");
        let env = match project.get_module(module_id) {
            Module::Ok(env) => env,
            Module::Error(e) => panic!("get_module error: {}", e),
            _ => panic!("unexpected get_module result"),
        };
        let goal_context = env.get_goal_context_by_name(project, goal_name);
        let mut prover = Prover::new(&project, &goal_context, false, None);
        prover.verbose = true;
        let outcome = prover.quick_search();
        if outcome == Outcome::Error {
            panic!("prover error: {}", prover.error.unwrap());
        }
        let code = match prover.get_proof() {
            Some(proof) => proof.to_code(&env.bindings),
            None => Err("there is no proof".to_string()),
        };
        (outcome, code)
    }

    fn prove_as_main(text: &str, goal_name: &str) -> (Outcome, Result<Vec<String>, String>) {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        prove(&mut project, "main", goal_name)
    }

    // Does one proof on the provided text.
    fn prove_text(text: &str, goal_name: &str) -> Outcome {
        prove_as_main(text, goal_name).0
    }

    // Proves all the goals in the provided text, returning any non-Success outcome.
    fn prove_all_no_crash(text: &str) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        let module_id = project.load_module("main").expect("load failed");
        let env = match project.get_module(module_id) {
            Module::Ok(env) => env,
            Module::Error(e) => panic!("get_module error: {}", e),
            _ => panic!("unexpected get_module result"),
        };
        let paths = env.goal_paths();
        for path in paths {
            let prop = env.get_proposition(&path).unwrap();
            let goal_context = env.get_goal_context(&project, &path).unwrap();
            assert_eq!(prop.claim.range, goal_context.range);
            println!("proving: {}", goal_context.name);
            let mut prover = Prover::new(&project, &goal_context, false, None);
            prover.verbose = true;
            let outcome = prover.quick_search();
            if outcome != Outcome::Success {
                return outcome;
            }
        }
        Outcome::Success
    }

    fn prove_all_succeeds(text: &str) {
        assert_eq!(prove_all_no_crash(text), Outcome::Success);
    }

    fn expect_proof(text: &str, goal_name: &str, expected: &[&str]) {
        let (outcome, code) = prove_as_main(text, goal_name);
        assert_eq!(outcome, Outcome::Success);
        let actual = code.expect("code generation failed");
        assert_eq!(actual, expected);
    }

    const THING: &str = r#"
    type Thing: axiom
    let t: Thing = axiom
    let t2: Thing = axiom
    let f: Thing -> bool = axiom
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
            axiom f_all(x: Thing): f(x)
            theorem goal: f(t)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let text = r#"
            axiom f_one: f(t)
            theorem goal(x: Thing): f(x)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_axiomatic_values_distinct() {
        let text = "theorem goal: t = t2";
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_finds_example() {
        let text = r#"
            axiom f_one: f(t)
            theorem goal: exists(x: Thing) { f(x) }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let text = r#"
            axiom not_f(x: Thing): !f(x)
            theorem goal: !f(t)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_equality() {
        let text = r#"
            axiom t_eq_t2: t = t2
            theorem goal: f(t) = f(t2) 
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition() {
        let text = r#"
            axiom g_id(x: Thing): g(x, x) = x
            axiom f_t: f(t)
            theorem goal: f(g(t, t))
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    // #[test]
    // fn test_composition_can_fail() {
    //     let text = r#"
    //         axiom f_t: f(t)
    //         axiom g_id(x: Thing): g(x, x) = x
    //         theorem goal: f(g(t, t2))
    //         "#;
    //     assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    // }

    #[test]
    fn test_negative_rewriting() {
        let text = r#"
            axiom not_f_t: !f(t)
            axiom g_id(x: Thing): g(x, x) = x
            theorem goal: !f(g(t, t))
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_ne() {
        let text = r#"
            axiom f_t_ne_f_t2: f(t) != f(t2)
            theorem goal: t != t2
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let text = r#"
            axiom foo(x: Thing): x != t | f(t)
            theorem goal: f(t)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let text = r#"
            axiom foo(x: Thing, y: Thing): x = t | y = t
            theorem goal(x: Thing): x = t2
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_existence_of_nonequality() {
        // After normalization, this is the same problem as the equality
        // factoring test above. So if one of them works and one doesn't,
        // it's likely to be a prioritization dependency problem.
        let text = r#"
            axiom foo: exists(x: Thing) { x != t2 }
            theorem goal: exists(x: Thing) { x != t }
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_avoids_loops() {
        let text = r#"
            axiom trivial(x: Thing): !f(h(x)) | f(h(x))
            axiom arbitrary(x: Thing): f(h(x)) | f(x)
            theorem goal: f(t)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let text = r#"
            axiom foo(x: Thing -> bool): x(t) | f(h(t))
            theorem goal: f(t2)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_higher_order_unification() {
        let text = r#"
            axiom foo(x: Thing -> bool): x(t)
            theorem goal: f(t)
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_theorem_block() {
        let text = r#"
            type Thing: axiom
            let t: Thing = axiom
            theorem reflexivity(x: Thing): x = x by {
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
            let foo: Thing -> bool = axiom
            axiom foo_t: foo(t)
            forall(x: Thing) {
                x = t -> foo(x)
            }
            "#;

        expect_proof(text, "((x = t) -> foo(x))", &[]);
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
        expect_proof(text, "(x = y)", &[]);
    }

    #[test]
    fn test_extracting_narrow_proof() {
        let text = r#"
            let b: bool = axiom
            let f1: bool -> bool = axiom
            let f2: bool -> bool = axiom
            let f3: bool -> bool = axiom
            let f4: bool -> bool = axiom
            axiom a1: f1(b)
            axiom a12(x: bool): f1(x) -> f2(x)
            axiom a23(x: bool): f2(x) -> f3(x)
            axiom a34(x: bool): f3(x) -> f4(x)
            theorem goal(x: bool): f4(b)
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
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
            axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
            define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)
            theorem add_zero_right(a: Nat): add(a, 0) = a
        "#;
        expect_proof(text, "add_zero_right", &[]);
    }

    #[test]
    fn test_second_literal_matches_goal() {
        let text = r#"
            axiom axiom1: f(g(t, t)) | f(t2)
            axiom axiom2: !f(g(t, t)) | f(t2)
            theorem goal: f(t2)
        "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_closure_proof() {
        let text = r#"
            type Nat: axiom
            let add: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) = function(b: Nat) { add(a, b) }
            theorem goal(a: Nat, b: Nat): add(a, b) = adder(a)(b)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_boolean_equality() {
        let text = r#"
            type Nat: axiom
            let add: (Nat, Nat) -> Nat = axiom
            define lte(a: Nat, b: Nat) -> bool = exists(c: Nat) { add(a, c) = b }
            define lt(a: Nat, b: Nat) -> bool = lte(a, b) & a != b
            theorem goal(a: Nat): !lt(a, a)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            let 1: Nat = axiom
            let Suc: Nat -> Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            axiom one_neq_zero: 1 != 0
            theorem goal: exists(x: Nat) { 1 = Suc(x) }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            theorem goal: zero_or_suc(y)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_another_instance_of_conditional_existence_theorem() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            axiom y_not_zero: y != 0
            theorem goal: zero_or_suc(y)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_struct_new_equation() {
        let text = r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(p: Pair): p = Pair.new(Pair.first(p), Pair.second(p))
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_struct_first_member_equation() {
        let text = r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(a: bool, b: bool): Pair.first(Pair.new(a, b)) = a
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_struct_second_member_equation() {
        let text = r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(a: bool, b: bool): Pair.second(Pair.new(a, b)) = b
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T): a = b & b = c -> a = c by {
                if (a = b & b = c) {
                    a = c
                }
            }
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_parametric_theorem_no_block() {
        let text = r#"
            theorem goal<T>(a: T, b: T, c: T): a = b & b = c -> a = c
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_applying_parametric_theorem() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            theorem foo<T>(a: T): a = a
            theorem goal: foo(0)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_applying_parametric_function() {
        let text = r#"
            type Nat: axiom
            define foo<T>(a: T) -> bool = (a = a)
            let 0: Nat = axiom
            theorem goal: foo(0)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parametric_definition_and_theorem() {
        let text = r#"
            define foo<T>(a: T) -> bool = axiom
            axiom foo_true<T>(a: T): foo(a)
            type Nat: axiom
            let 0: Nat = axiom
            theorem goal: foo(0)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_parameter_name_can_change() {
        let text = r#"
            define foo<T>(a: T) -> bool = axiom
            axiom foo_true<U>(a: U): foo(a)
            type Nat: axiom
            let 0: Nat = axiom
            theorem goal: foo(0)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_inconsistency() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            let foo: Nat -> bool = axiom
            let bar: Nat -> bool = axiom
            axiom foo_true: foo(0)
            axiom foo_false: !foo(0)
            theorem goal: bar(0)
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_using_true_and_false_in_a_proof() {
        let text = r#"
        theorem goal(b: bool): b = true | b = false
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finding_mildly_nontrivial_inconsistency() {
        let text = r#"
            axiom bad: true = false
            let b: bool = axiom
            theorem goal: b
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Inconsistent);
    }

    #[test]
    fn test_proving_explicit_false_okay() {
        prove_all_succeeds(
            r#"
            let b: bool = axiom
            if b != b {
                false
            }
        "#,
        );
    }

    #[test]
    fn test_subsequent_explicit_false_ok() {
        prove_all_succeeds(
            r#"
            let b: bool = axiom
            if b != b {
                b | !b
                false
            }
        "#,
        );
    }

    #[test]
    fn test_explicit_false_mandatory() {
        let text = r#"
            let b: bool = axiom
            let c: bool = axiom
            if b != b {
                c
            }
        "#;
        assert_eq!(prove_all_no_crash(text), Outcome::Inconsistent);
    }

    #[test]
    fn test_if_else_expression() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let 1: Nat = axiom
            define sign(a: Nat) -> Nat = if a = 0 { 0 } else { 1 }
            theorem goal(a: Nat): sign(a) = 0 | sign(a) = 1
        "#,
        );
    }

    #[test]
    fn test_rewrite_consistency() {
        // In practice this caught an inconsistency that came from bad rewrite logic.
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            let add: (Nat, Nat) -> Nat = axiom
            let mul: (Nat, Nat) -> Nat = axiom
            axiom add_suc(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))
            axiom suc_ne(a: Nat): Suc(a) != a
            axiom mul_suc(a: Nat, b: Nat): add(a, mul(a, b)) = mul(a, Suc(b))
            theorem goal(a: Nat): Suc(a) != a
        "#,
        );
    }

    #[test]
    fn test_normalization_failure_doesnt_crash() {
        // We can't normalize lambdas inside function calls, but we shouldn't crash on them.
        prove_all_no_crash(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            define apply(f: Nat -> Nat, a: Nat) -> Nat = f(a)
            theorem goal: apply(function(x: Nat) { x }, 0) = 0
        "#,
        );
    }

    #[test]
    fn test_functional_definition() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            define is_min(f: Nat -> bool) -> (Nat -> bool) = axiom
            define gcd_term(p: Nat) -> (Nat -> bool) = axiom
            let p: Nat = axiom
            let f: Nat -> bool = is_min(gcd_term(p))

            theorem goal: is_min(gcd_term(p)) = f
        "#,
        );
    }

    #[test]
    fn test_functional_equality_definition() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let f: Nat -> Nat = axiom
            let g: Nat -> Nat = axiom
            theorem goal: forall(x: Nat) { f(x) = g(x) } -> f = g
        "#,
        );
    }

    // These tests cover some principles of functional equality that aren't implemented yet.
    //
    // #[test]
    // fn test_functional_substitution() {
    //     prove_all_succeeds(
    //         r#"
    //         type Nat: axiom
    //         define find(f: Nat -> bool) -> Nat = axiom
    //         define is_min(f: Nat -> bool) -> (Nat -> bool) = axiom
    //         define gcd_term(p: Nat) -> (Nat -> bool) = axiom
    //         let p: Nat = axiom
    //         let f: Nat -> bool = is_min(gcd_term(p))
    //         theorem goal: find(is_min(gcd_term(p))) = find(f)
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
    //         theorem goal: forall(x: Nat) { f(x) = g(x) } -> p(f) = p(g)
    //         "#,
    //     );
    // }

    #[test]
    fn test_proving_with_partial_application() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let add: (Nat, Nat) -> Nat = axiom
            theorem goal(f: Nat -> Nat): f = add(0) -> f(0) = add(0, 0)
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
            axiom meq(b: Bar): morph(b) = morph(bar)
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            import bar
            theorem goal(a: bar.Bar, b: bar.Bar): bar.morph(a) = bar.morph(b)
        "#,
        );
        let (outcome, _) = prove(&mut p, "main", "goal");
        assert_eq!(outcome, Outcome::Success);
    }

    #[test]
    fn test_backward_nonbranching_reasoning() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let Suc: Nat -> Nat = axiom
            axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y
            let n: Nat = axiom
            axiom hyp: Suc(n) != n
            theorem goal: Suc(Suc(n)) != Suc(n)
        "#,
        )
    }

    #[test]
    fn test_basic_unification() {
        prove_all_succeeds(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let f: (Nat, Nat) -> bool = axiom
            axiom f_zero_right(x: Nat): f(x, 0)
            theorem goal: exists(x: Nat) { f(0, x) }
        "#,
        );
    }

    #[test]
    fn test_indirect_proof_extraction() {
        let text = r#"
            let a: bool = axiom
            let b: bool = axiom
            axiom bimpa: b -> a
            axiom bimpna: b -> !a
            theorem goal: !b
        "#;
        expect_proof(text, "goal", &["if b {", "\ta", "\tfalse", "}"]);
    }

    #[test]
    fn test_proof_generation_with_forall_goal() {
        let text = r#"
            type Nat: axiom
            let f: Nat -> bool = axiom
            let g: Nat -> bool = axiom
            let h: Nat -> bool = axiom
            axiom fimpg: forall(x: Nat) { f(x) -> g(x) }
            axiom gimph: forall(x: Nat) { g(x) -> h(x) }
            theorem goal: forall(x: Nat) { f(x) -> h(x) }
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_proof_generation_with_intermediate_skolems() {
        let text = r#"
        type Nat: axiom
        let a: bool = axiom
        let b: bool = axiom
        let f: Nat -> bool = axiom
        let g: Nat -> bool = axiom
        axiom aimpf: a -> forall(x: Nat) { f(x) }
        axiom fimpg: forall(x: Nat) { f(x) } -> forall(x: Nat) { g(x) }
        axiom gimpb: forall(x: Nat) { f(x) } -> b
        theorem goal: a -> b
        "#;
        expect_proof(text, "goal", &[]);
    }

    #[test]
    fn test_assuming_lhs_of_implication() {
        prove_all_succeeds(
            r#"
            let a: bool = axiom
            let b: bool = axiom
            let c: bool = axiom
            axiom aimpb: a -> b
            axiom bimpc: b -> c
            theorem goal: a -> c by {
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
            
            define foo<T>(x: T) -> bool = axiom

            axiom a12: foo(t1) -> foo(t2)
            axiom a23: foo(t2) -> foo(t3)
            theorem goal: foo(t1) -> foo(t3)
            "#;

        expect_proof(text, "goal", &["foo(t2)"]);
    }

    #[test]
    fn test_proof_using_else() {
        let text = r#"
        let a: bool = axiom
        let b: bool = axiom
        let c: bool = axiom
        if a {
            b
        } else {
            c
        }
        theorem goal: !a -> c
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_else_when_missing_if_block() {
        let text = r#"
        let a: bool = axiom
        let b: bool = axiom
        if a {
        } else {
            b
        }
        theorem goal: !a -> b
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
    }
}
