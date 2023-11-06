use std::fmt;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use crossbeam::queue::SegQueue;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::ActiveSet;
use crate::atom::Atom;
use crate::clause::Clause;
use crate::clause_info::{ClauseInfo, ClauseType, ProofStep};
use crate::display::DisplayClause;
use crate::goal_context::{monomorphize_facts, GoalContext};
use crate::normalizer::Normalizer;
use crate::passive_set::PassiveSet;
use crate::project::Project;
use crate::synthesizer::Synthesizer;

pub struct Prover {
    // The normalizer is used when we are turning the facts and goals from the environment into
    // clauses that we can use internally.
    normalizer: Normalizer,

    // The synthesizer creates new functions during the proof.
    // This is probably a bad idea - it's a lot of complexity and does not really do a good job
    // of solving the problem of how to do induction.
    synthesizer: Synthesizer,

    // The facts we start out with.
    facts: Vec<AcornValue>,

    // The goal we are trying to prove.
    goal: Option<AcornValue>,

    // The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    passive: PassiveSet,

    // A verbose prover prints out a lot of stuff.
    pub verbose: bool,

    // When print queue is set, we send print statements here, instead of to stdout.
    pub print_queue: Option<Arc<SegQueue<String>>>,

    // If a trace string is set, we print out what happens with the clause matching it, regardless
    // of verbosity.
    trace: Option<String>,

    // Whether we have hit the trace
    pub hit_trace: bool,

    // The final step that proves a contradiction, if we have one.
    final_step: Option<ProofStep>,

    // How many ClauseInfo have been generated by this prover.
    num_generated: usize,

    // Setting any of these flags to true externally will stop the prover.
    pub stop_flags: Vec<Arc<AtomicBool>>,

    // Whether we should report Outcome::Inconsistent or just treat it as a success.
    report_inconsistency: bool,

    // Whether only facts have been added to the active set.
    facts_only: bool,
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
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Exhausted,
    Inconsistent,
    Interrupted,
    Unknown,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Success => write!(f, "Success"),
            Outcome::Exhausted => write!(f, "Exhausted"),
            Outcome::Inconsistent => write!(f, "Inconsistent"),
            Outcome::Interrupted => write!(f, "Interrupted"),
            Outcome::Unknown => write!(f, "Unknown"),
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
            synthesizer: Synthesizer::new(),
            facts: Vec::new(),
            goal: None,
            active_set: ActiveSet::new(),
            passive: PassiveSet::new(),
            verbose,
            print_queue,
            trace: None,
            hit_trace: false,
            final_step: None,
            num_generated: 0,
            stop_flags: Vec::new(),
            report_inconsistency: !goal_context.includes_explicit_false(),
            facts_only: true,
        };

        // Get facts both from the goal context and from the overall project
        let mut polymorphic_facts = vec![];
        for dependency in project.all_dependencies(goal_context.namespace()) {
            let env = project.get_env(dependency).unwrap();
            polymorphic_facts.extend(env.get_facts(project));
        }
        polymorphic_facts.extend(goal_context.facts.iter().cloned());
        let monomorphic_facts = monomorphize_facts(&polymorphic_facts, &goal_context.goal);

        // Load facts into the prover
        for fact in monomorphic_facts {
            p.add_fact(fact);
        }
        p.add_goal(goal_context.goal.clone());
        p
    }

    pub fn set_trace(&mut self, trace: &str) {
        self.trace = Some(trace.to_string());
    }

    pub fn unset_trace(&mut self) {
        self.trace = None;
    }

    fn normalize_proposition(&mut self, proposition: AcornValue) -> Option<Vec<Clause>> {
        proposition.validate().unwrap_or_else(|e| {
            panic!("validation error: {} while normalizing: {}", e, proposition);
        });
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.normalizer.normalize(proposition)
    }

    // Create a new ClauseInfo object.
    fn new_clause_info(
        &mut self,
        clause: Clause,
        clause_type: ClauseType,
        proof_step: ProofStep,
    ) -> ClauseInfo {
        let atom_count = clause.atom_count();
        let generation_order = self.num_generated;
        self.num_generated += 1;
        ClauseInfo {
            clause,
            clause_type,
            proof_step,
            atom_count,
            generation_order,
        }
    }

    pub fn add_fact(&mut self, proposition: AcornValue) {
        self.facts.push(proposition.clone());
        let clauses = match self.normalize_proposition(proposition) {
            Some(clauses) => clauses,
            None => {
                // We have a false assumption, so we're done already.
                self.final_step = Some(ProofStep::assumption());
                return;
            }
        };
        for clause in clauses {
            let info = self.new_clause_info(clause, ClauseType::Fact, ProofStep::assumption());
            self.passive.push(info);
        }
    }

    pub fn add_goal(&mut self, proposition: AcornValue) {
        assert!(self.goal.is_none());
        self.goal = Some(proposition.clone());
        let clauses = match self.normalize_proposition(proposition.to_placeholder().negate()) {
            Some(clauses) => clauses,
            None => {
                // Our goal is trivially true, so we're done already.
                self.final_step = Some(ProofStep::assumption());
                return;
            }
        };
        for clause in clauses {
            let info =
                self.new_clause_info(clause, ClauseType::NegatedGoal, ProofStep::assumption());
            self.passive.push(info);
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
        cprintln!(self, "{} clauses in the passive set", self.passive.len());
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
        let clause_infos = self.passive.all_clause_info();
        for clause_info in clause_infos {
            let clause = self.display(&clause_info.clause);
            if let Some(substr) = substr {
                if !clause.to_string().contains(substr) {
                    continue;
                }
            }
            count += 1;
            cprintln!(self, "{}", clause);
            cprintln!(self, "  {}", clause_info);
        }
        if let Some(substr) = substr {
            cprintln!(self, "{} passive clauses matched {}", count, substr);
        } else {
            cprintln!(self, "{} clauses total in the passive set", count);
        }
    }

    // Prints out information for a specific atom
    pub fn print_atom_info(&self, s: &str) {
        if let Some(atom) = Atom::parse(s) {
            match atom {
                Atom::Synthetic(i) => {
                    if let Some(lit) = self.synthesizer.get_definition(i) {
                        cprintln!(self, "{} := {}", atom, lit);
                    } else {
                        cprintln!(self, "no definition for {}", atom);
                    }
                }
                _ => {
                    cprintln!(self, "we have no way to print info for {}", atom);
                }
            }
        } else {
            cprintln!(self, "not an atom: {}", s);
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

    pub fn print_proof_step(&self, preface: &str, clause: &Clause, ps: &ProofStep) {
        cprintln!(
            self,
            "\n{}{:?} generated:\n    {}",
            preface,
            ps.rule,
            self.display(clause)
        );
        if let Some(i) = ps.activated {
            let c = self.display(self.active_set.get_clause(i));
            cprintln!(self, "  when activating clause {}:\n    {}", i, c);
        }
        if let Some(i) = ps.existing {
            let c = self.display(self.active_set.get_clause(i));
            cprintln!(self, "  using clause {}:\n    {}", i, c);
        }
        for i in &ps.rewrites {
            let c = self.display(self.active_set.get_clause(*i));
            cprintln!(self, "  rewriting with clause {}:\n    {}", i, c);
        }
    }

    pub fn print_env(&self) {
        cprintln!(self, "facts:");
        for fact in &self.facts {
            cprintln!(self, "  {}", fact);
        }
        cprintln!(self, "goal:");
        if let Some(goal) = &self.goal {
            cprintln!(self, "  {}", goal);
        } else {
            cprintln!(self, "  none");
        }
    }

    pub fn print_proof(&self) {
        let final_step = if let Some(final_step) = &self.final_step {
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

        let indices = self.active_set.find_upstream(final_step);
        cprintln!(self, "the proof uses {} steps:", indices.len());
        for i in indices {
            let step = self.active_set.get_proof_step(i);
            let clause = self.active_set.get_clause(i);
            let preface = format!("clause {}: ", i);
            self.print_proof_step(&preface, clause, step);
        }
        self.print_proof_step("final step: ", &Clause::impossible(), final_step);
    }

    // Handle the case when we found a contradiction
    fn report_contradiction(&mut self, ps: ProofStep) -> Outcome {
        self.final_step = Some(ps);
        if self.facts_only && self.report_inconsistency {
            Outcome::Inconsistent
        } else {
            Outcome::Success
        }
    }

    // Activates the next clause from the queue.
    pub fn activate_next(&mut self) -> Outcome {
        if let Some(ps) = self.final_step.take() {
            // We already found a contradiction, so we're done.
            return self.report_contradiction(ps);
        }

        let info = match self.passive.pop() {
            Some(info) => info,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                return Outcome::Exhausted;
            }
        };

        if info.clause_type != ClauseType::Fact {
            self.facts_only = false;
        }

        let tracing = self.is_tracing(&info.clause);
        let verbose = self.verbose || tracing;

        let mut original_clause_string = "".to_string();
        let mut simplified_clause_string = "".to_string();
        if verbose {
            original_clause_string = self.display(&info.clause).to_string();
        }

        let info = match self.active_set.simplify(info) {
            Some(i) => i,
            None => {
                // The clause is redundant, so skip it.
                if verbose {
                    cprintln!(self, "redundant: {}", original_clause_string);
                }
                return Outcome::Unknown;
            }
        };
        let clause = &info.clause;
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
            return self.report_contradiction(info.proof_step);
        }
        self.synthesizer.observe_types(clause);

        // Synthesize predicates if this is the negated goal.
        if info.clause_type == ClauseType::NegatedGoal {
            let synth_clauses = self.synthesizer.synthesize(&self.normalizer, clause);
            if !synth_clauses.is_empty() {
                for synth_clause in synth_clauses {
                    if verbose {
                        cprintln!(self, "synthesizing: {}", self.display(&synth_clause));
                    }

                    // Treat the definition of synthesized predicates like extra facts.
                    let synth_info = self.new_clause_info(
                        synth_clause,
                        ClauseType::Fact,
                        ProofStep::definition(),
                    );
                    self.activate(synth_info, verbose, tracing);
                }
            }
        }

        if verbose {
            let prefix = match info.clause_type {
                ClauseType::Fact => " fact",
                ClauseType::NegatedGoal => " negated goal",
                ClauseType::Impure => "",
            };
            cprintln!(self, "activating{}: {}", prefix, simplified_clause_string);
        }
        self.activate(info, verbose, tracing)
    }

    // Generates clauses, then simplifies them, then adds them to the passive set.
    // Clauses will get simplified again when they are activated.
    fn activate(&mut self, info: ClauseInfo, verbose: bool, tracing: bool) -> Outcome {
        let clause_type = info.clause_type;
        let generated_clauses = self.active_set.generate(info);

        let generated_type = if clause_type == ClauseType::Fact {
            ClauseType::Fact
        } else {
            ClauseType::Impure
        };

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
        for (i, (c, ps)) in generated_clauses.into_iter().enumerate() {
            if clause_type == ClauseType::Fact && ps.proof_size > 2 {
                // Limit fact-fact inference
                continue;
            }
            if c.is_impossible() {
                return self.report_contradiction(ps);
            }
            if tracing {
                self.print_proof_step("", &c, &ps);
            } else if verbose && (i < print_limit) {
                cprintln!(self, "  {}", self.display(&c));
            } else if self.is_tracing(&c) {
                self.print_proof_step("", &c, &ps);
            }
            let info = self.new_clause_info(c, generated_type, ps);
            if let Some(info) = self.active_set.simplify(info) {
                self.passive.push(info);
            }
        }
        Outcome::Unknown
    }

    pub fn search_for_contradiction(&mut self, size: i32, seconds: f32) -> Outcome {
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

    pub fn done_with_facts(&self) -> bool {
        self.passive.next_clause_type() != Some(ClauseType::Fact)
    }
}

#[cfg(test)]
mod tests {
    use crate::project::{Module, Project};

    use super::*;

    // Tries to prove one thing from the project.
    fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Outcome {
        let namespace = project.load(module_name).expect("load failed");
        let env = match project.get_module(namespace) {
            Module::Ok(env) => env,
            Module::Error(e) => panic!("get_module error: {}", e),
            _ => panic!("unexpected get_module result"),
        };
        let goal_context = env.get_goal_context_by_name(project, goal_name);
        let mut prover = Prover::new(&project, &goal_context, false, None);
        prover.verbose = true;
        prover.search_for_contradiction(2000, 2.0)
    }

    // Does one proof on the provided text.
    fn prove_text(text: &str, goal_name: &str) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        prove(&mut project, "main", goal_name)
    }

    // Proves all the goals in the provided text, returning any non-Success outcome.
    fn prove_all(text: &str) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", text);
        let namespace = project.load("main").expect("load failed");
        let env = match project.get_module(namespace) {
            Module::Ok(env) => env,
            Module::Error(e) => panic!("get_module error: {}", e),
            _ => panic!("unexpected get_module result"),
        };
        let paths = env.goal_paths();
        for path in paths {
            let goal_context = env.get_goal_context(&project, &path);
            println!("proving: {}", goal_context.name);
            let mut prover = Prover::new(&project, &goal_context, false, None);
            prover.verbose = true;
            let outcome = prover.search_for_contradiction(2000, 2.0);
            if outcome != Outcome::Success {
                return outcome;
            }
        }
        Outcome::Success
    }

    fn prove_all_ok(text: &str) {
        assert_eq!(prove_all(text), Outcome::Success);
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

    #[test]
    fn test_composition_can_fail() {
        let text = r#"
            axiom f_t: f(t)
            axiom g_id(x: Thing): g(x, x) = x
            theorem goal: f(g(t, t2))
            "#;
        assert_eq!(prove_thing(text, "goal"), Outcome::Exhausted);
    }

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
        assert_eq!(prove_text(text, "reflexivity(t)"), Outcome::Success);
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
        assert_eq!(prove_text(text, "((x = t) -> foo(x))"), Outcome::Success);
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
        assert_eq!(prove_text(text, "(x = y)"), Outcome::Success);
    }

    #[test]
    fn test_multi_hop_rewriting() {
        let text = r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
            axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
            define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)
            theorem add_zero_right(a: Nat): add(a, 0) = a
        "#;
        assert_eq!(prove_text(text, "add_zero_right"), Outcome::Success);
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
    fn test_matching_newly_synthesized_goal() {
        let text = r#"
        type Nat: axiom
        let 0: Nat = axiom
        axiom everything(x0: Nat -> bool, x1: Nat): x0(x1)
        let add: (Nat, Nat) -> Nat = axiom
        theorem goal(a: Nat): add(a, 0) = a
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Success);
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
    fn test_forall_scopes() {
        // Unprovable, since we know nothing about lt, but it shouldn't crash.

        let text = r#"
            type Nat: axiom
            let lt: (Nat, Nat) -> bool = axiom
            theorem strong_induction(f: Nat -> bool): forall(k: Nat) {
                forall(m: Nat) { lt(m, k) -> f(m) } -> f(k)
            } -> forall(n: Nat) { f(n) }
            "#;
        assert_eq!(prove_text(text, "strong_induction"), Outcome::Exhausted);
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
        prove_all_ok(
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
        prove_all_ok(
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
            if b != b {
                b
            }
        "#;
        assert_eq!(prove_all(text), Outcome::Inconsistent);
    }

    #[test]
    fn test_lt_consistent() {
        let text = r#"
            type Nat: axiom
            let lt: (Nat, Nat) -> bool = axiom
            axiom nonreflexive(a: Nat): !lt(a, a)
            axiom trichomotomy(a: Nat, b: Nat): lt(a, b) | lt(b, a) | a = b
            theorem goal(a: Nat, b: Nat): a = b
        "#;
        assert_eq!(prove_text(text, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_basic_if_then_else() {
        prove_all_ok(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let 1: Nat = axiom
            define sign(a: Nat) -> Nat = if a = 0 { 0 } else { 1 }
            theorem goal(a: Nat): sign(a) = 0 | sign(a) = 1
        "#,
        );
    }

    // These tests are like integration tests. See the files in the `tests` directory.

    fn test_mono(name: &str) {
        assert_eq!(
            prove(&mut Project::new("test"), "mono_nat", name),
            Outcome::Success
        );
    }

    #[test]
    fn test_mono_add_zero_right() {
        test_mono("add_zero_right");
    }

    #[test]
    fn test_mono_one_plus_one() {
        test_mono("one_plus_one");
    }

    #[test]
    fn test_mono_add_zero_left() {
        test_mono("add_zero_left");
    }

    #[test]
    fn test_mono_add_suc_right() {
        test_mono("add_suc_right");
    }

    #[test]
    fn test_mono_add_suc_left() {
        test_mono("add_suc_left");
    }

    #[test]
    fn test_mono_suc_ne() {
        test_mono("suc_ne");
    }

    #[test]
    fn test_mono_suc_suc_ne() {
        test_mono("suc_suc_ne");
    }

    #[test]
    fn test_mono_add_comm() {
        test_mono("add_comm");
    }

    fn test_poly(name: &str) {
        assert_eq!(
            prove(&mut Project::new("test"), "poly_nat", name),
            Outcome::Success
        );
    }

    #[test]
    fn test_poly_add_zero_right() {
        test_poly("add_zero_right");
    }

    #[test]
    fn test_poly_one_plus_one() {
        test_poly("one_plus_one");
    }

    #[test]
    fn test_poly_add_zero_left() {
        test_poly("add_zero_left");
    }

    #[test]
    fn test_poly_add_suc_right() {
        test_poly("add_suc_right");
    }

    #[test]
    fn test_poly_add_suc_left() {
        test_poly("add_suc_left");
    }

    #[test]
    fn test_poly_suc_ne() {
        test_poly("suc_ne");
    }

    #[test]
    fn test_poly_suc_suc_ne() {
        test_poly("suc_suc_ne");
    }

    #[test]
    fn test_poly_add_comm() {
        test_poly("add_comm");
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
        assert_eq!(prove(&mut p, "main", "goal"), Outcome::Success);
    }
}
