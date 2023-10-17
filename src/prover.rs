use std::collections::HashSet;
use std::ptr;
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
use crate::environment::Environment;
use crate::goal_context::GoalContext;
use crate::normalizer::Normalizer;
use crate::passive_set::PassiveSet;
use crate::synthesizer::Synthesizer;

pub struct Prover<'a> {
    // The environment in which all the AcornValues we are passed live.
    env: &'a Environment,

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
// "Interrupted" means that the prover was explicitly stopped.
// "Unknown" means that we could keep working longer at it.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Exhausted,
    Interrupted,
    Unknown,
}

impl Prover<'_> {
    pub fn new(env: &Environment) -> Prover {
        Prover {
            normalizer: Normalizer::new(),
            synthesizer: Synthesizer::new(),
            facts: Vec::new(),
            goal: None,
            active_set: ActiveSet::new(),
            passive: PassiveSet::new(),
            env,
            verbose: false,
            print_queue: None,
            trace: None,
            hit_trace: false,
            final_step: None,
            num_generated: 0,
            stop_flags: Vec::new(),
        }
    }

    pub fn set_trace(&mut self, trace: &str) {
        self.trace = Some(trace.to_string());
    }

    pub fn unset_trace(&mut self) {
        self.trace = None;
    }

    fn normalize_proposition(&mut self, proposition: AcornValue) -> Vec<Clause> {
        if let Err(e) = proposition.validate() {
            panic!(
                "error: {} while adding proposition to prover: {}",
                e,
                self.env.value_str(&proposition)
            );
        }
        assert_eq!(proposition.get_type(), AcornType::Bool);
        let answer = self.normalizer.normalize(self.env, proposition);
        answer
    }

    // Create a new ClauseInfo object.
    fn new_clause_info(
        &mut self,
        clause: Clause,
        clause_type: ClauseType,
        proof_step: ProofStep,
        generation_order: Option<usize>,
    ) -> ClauseInfo {
        let atom_count = clause.atom_count();
        let generation_order = match generation_order {
            Some(i) => i,
            None => {
                let answer = self.num_generated;
                self.num_generated += 1;
                answer
            }
        };
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
        for clause in self.normalize_proposition(proposition) {
            let info =
                self.new_clause_info(clause, ClauseType::Fact, ProofStep::assumption(), None);
            self.passive.push(info);
        }
    }

    pub fn add_goal(&mut self, proposition: AcornValue) {
        assert!(self.goal.is_none());
        self.goal = Some(proposition.clone());
        for clause in self.normalize_proposition(proposition.negate()) {
            let info = self.new_clause_info(
                clause,
                ClauseType::NegatedGoal,
                ProofStep::assumption(),
                None,
            );
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

    pub fn print_proof_step(&self, preface: &str, clause: &Clause, ps: ProofStep) {
        cprintln!(
            self,
            "{}{:?} generated:\n    {}",
            preface,
            ps.rule,
            self.display(clause)
        );
        if let Some(i) = ps.activated {
            let c = self.display(self.active_set.get_clause(i));
            cprintln!(self, "  using clause {}:\n    {}", i, c);
        }
        if let Some(i) = ps.existing {
            let c = self.display(self.active_set.get_clause(i));
            cprintln!(self, "  with clause {}:\n    {}", i, c);
        }
    }

    pub fn print_env(&self) {
        cprintln!(self, "facts:");
        for fact in &self.facts {
            cprintln!(self, "  {}", self.env.value_str(fact));
        }
        cprintln!(self, "goal:");
        if let Some(goal) = &self.goal {
            cprintln!(self, "  {}", self.env.value_str(goal));
        } else {
            cprintln!(self, "  none");
        }
    }

    pub fn print_proof(&self) {
        let final_step = if let Some(final_step) = self.final_step {
            final_step
        } else {
            cprintln!(self, "we do not have a proof");
            return;
        };

        // Figure out which clause indices were used.
        let mut todo = Vec::<usize>::new();
        let mut done = HashSet::new();
        for i in final_step.indices() {
            todo.push(*i);
        }
        while !todo.is_empty() {
            let i = todo.pop().unwrap();
            if done.contains(&i) {
                continue;
            }
            done.insert(i);
            let step = self.active_set.get_proof_step(i);
            for j in step.indices() {
                todo.push(*j);
            }
        }

        // Print out the clauses in order.
        let mut indices = done.into_iter().collect::<Vec<_>>();
        indices.sort();
        cprintln!(
            self,
            "in total, we activated {} proof steps.",
            self.active_set.len()
        );
        cprintln!(self, "the proof uses {} steps:", indices.len());
        for i in indices {
            let step = self.active_set.get_proof_step(i);
            let clause = self.active_set.get_clause(i);
            let preface = format!("clause {}: ", i);
            self.print_proof_step(&preface, clause, *step);
        }
        self.print_proof_step("final step: ", &Clause::impossible(), final_step);
    }

    // Returns None if the clause is redundant.
    fn simplify(&mut self, info: &ClauseInfo) -> Option<ClauseInfo> {
        let new_clause = self.active_set.simplify(&info.clause, info.clause_type)?;
        Some(self.new_clause_info(
            new_clause,
            info.clause_type,
            info.proof_step,
            Some(info.generation_order),
        ))
    }

    // Activates the next clause from the queue.
    pub fn activate_next(&mut self) -> Outcome {
        let info = match self.passive.pop() {
            Some(info) => info,
            None => {
                // We're out of clauses to process, so we can't make any more progress.
                return Outcome::Exhausted;
            }
        };

        let tracing = self.is_tracing(&info.clause);
        let verbose = self.verbose || tracing;

        let mut original_clause_string = "".to_string();
        let mut simplified_clause_string = "".to_string();
        if verbose {
            original_clause_string = self.display(&info.clause).to_string();
        }

        let new_info = match self.simplify(&info) {
            Some(i) => i,
            None => {
                // The clause is redundant, so skip it.
                if verbose {
                    cprintln!(self, "redundant: {}", original_clause_string);
                }
                return Outcome::Unknown;
            }
        };
        let clause = &new_info.clause;
        if verbose {
            simplified_clause_string = self.display(clause).to_string();
            if simplified_clause_string != original_clause_string {
                cprintln!(
                    self,
                    "simplified: {} => {}",
                    original_clause_string,
                    simplified_clause_string
                );
            }
        }

        if clause.is_impossible() {
            self.final_step = Some(info.proof_step);
            return Outcome::Success;
        }
        self.synthesizer.observe_types(clause);

        // Synthesize predicates if this is the negated goal.
        if info.clause_type == ClauseType::NegatedGoal {
            let synth_clauses = self.synthesizer.synthesize(clause);
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
                        None,
                    );
                    self.activate(synth_info, verbose, tracing);
                }
            }
        }

        if verbose {
            let prefix = match info.clause_type {
                ClauseType::Fact => " fact",
                ClauseType::NegatedGoal => " negated goal",
                ClauseType::Other => "",
            };
            cprintln!(self, "activating{}: {}", prefix, simplified_clause_string);
        }
        self.activate(new_info, verbose, tracing)
    }

    fn activate(&mut self, info: ClauseInfo, verbose: bool, tracing: bool) -> Outcome {
        let clause_type = info.clause_type;
        let new_clauses = self.active_set.generate(info);

        let generated_type = if clause_type == ClauseType::Fact {
            ClauseType::Fact
        } else {
            ClauseType::Other
        };

        let print_limit = 30;
        if !new_clauses.is_empty() {
            let len = new_clauses.len();
            if verbose {
                cprintln!(
                    self,
                    "generated {} new clauses{}:",
                    len,
                    if len > print_limit { ", eg" } else { "" }
                );
            }
            for (i, (c, ps)) in new_clauses.into_iter().enumerate() {
                if c.is_impossible() {
                    self.final_step = Some(ps);
                    return Outcome::Success;
                }
                if tracing {
                    self.print_proof_step("", &c, ps);
                } else if verbose && (i < print_limit) {
                    cprintln!(self, "  {}", self.display(&c));
                } else if self.is_tracing(&c) {
                    self.print_proof_step("", &c, ps);
                }
                let info = self.new_clause_info(c, generated_type, ps, None);
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
            env: self.env,
            normalizer: &self.normalizer,
        }
    }

    pub fn done_with_facts(&self) -> bool {
        self.passive.next_clause_type() != Some(ClauseType::Fact)
    }

    pub fn load_goal<'a>(&mut self, goal_context: &GoalContext<'a>) {
        assert!(ptr::eq(self.env, goal_context.env));
        for fact in goal_context.monomorphize_facts() {
            self.add_fact(fact);
        }
        self.add_goal(goal_context.goal.clone());
    }

    pub fn new_with_goal<'a>(goal_context: &GoalContext<'a>) -> Prover<'a> {
        let mut prover = Prover::new(&goal_context.env);
        prover.load_goal(goal_context);
        prover
    }

    pub fn prove_theorem(env: &Environment, theorem_name: &str) -> Outcome {
        let goal_context = env.get_theorem_context(theorem_name);
        Prover::prove_goal(&goal_context)
    }

    fn prove_goal(goal_context: &GoalContext) -> Outcome {
        let mut prover = Prover::new_with_goal(&goal_context);
        prover.verbose = true;
        prover.search_for_contradiction(2000, 2.0)
    }

    pub fn prove(env: &Environment, name: &str) -> Outcome {
        let goal_context = env.get_goal_context_by_name(name);
        Prover::prove_goal(&goal_context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn thing_env(s: &str) -> Environment {
        let mut env = Environment::new();
        env.add(
            r#"
            type Thing: axiom
            let t: Thing = axiom
            let t2: Thing = axiom
            let f: Thing -> bool = axiom
            let g: (Thing, Thing) -> Thing = axiom
            let h: Thing -> Thing = axiom
            "#,
        );
        env.add(s);
        env
    }

    #[test]
    fn test_specialization() {
        let env = thing_env(
            r#"
            axiom f_all(x: Thing): f(x)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let env = thing_env(
            r#"
            axiom f_one: f(t)
            theorem goal(x: Thing): f(x)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_finds_example() {
        let env = thing_env(
            r#"
            axiom f_one: f(t)
            theorem goal: exists(x: Thing) { f(x) }
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let env = thing_env(
            r#"
            axiom not_f(x: Thing): !f(x)
            theorem goal: !f(t)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_equality() {
        let env = thing_env(
            r#"
            axiom t_eq_t2: t = t2
            theorem goal: f(t) = f(t2) 
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition() {
        let env = thing_env(
            r#"
            axiom g_id(x: Thing): g(x, x) = x
            axiom f_t: f(t)
            theorem goal: f(g(t, t))
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition_can_fail() {
        let env = thing_env(
            r#"
            axiom f_t: f(t)
            axiom g_id(x: Thing): g(x, x) = x
            theorem goal: f(g(t, t2))
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_negative_rewriting() {
        let env = thing_env(
            r#"
            axiom not_f_t: !f(t)
            axiom g_id(x: Thing): g(x, x) = x
            theorem goal: !f(g(t, t))
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_ne() {
        let env = thing_env(
            r#"
            axiom f_t_ne_f_t2: f(t) != f(t2)
            theorem goal: t != t2
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing): x != t | f(t)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing, y: Thing): x = t | y = t
            theorem goal(x: Thing): x = t2
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_prover_avoids_loops() {
        let env = thing_env(
            r#"
            axiom trivial(x: Thing): !f(h(x)) | f(h(x))
            axiom arbitrary(x: Thing): f(h(x)) | f(x)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t) | f(h(t))
            theorem goal: f(t2)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Exhausted);
    }

    #[test]
    fn test_higher_order_unification() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_theorem_block() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Thing: axiom
            let t: Thing = axiom
            theorem reflexivity(x: Thing): x = x by {
                reflexivity(t)
            }
            "#,
        );
        assert_eq!(Prover::prove(&env, "reflexivity(t)"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_forall_block() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Thing: axiom
            let t: Thing = axiom
            let foo: Thing -> bool = axiom
            axiom foo_t: foo(t)
            forall(x: Thing) {
                x = t -> foo(x)
            }
            "#,
        );
        assert_eq!(Prover::prove(&env, "((x = t) -> foo(x))"), Outcome::Success);
    }

    #[test]
    fn test_proof_inside_if_block() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Thing: axiom
            forall(x: Thing, y: Thing) {
                if x = y {
                    x = y
                }
            }
            "#,
        );
        assert_eq!(Prover::prove(&env, "(x = y)"), Outcome::Success);
    }

    #[test]
    fn test_multi_hop_rewriting() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
            axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
            define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)
            theorem add_zero_right(a: Nat): add(a, 0) = a
        "#,
        );
        assert_eq!(Prover::prove(&env, "add_zero_right"), Outcome::Success);
    }

    #[test]
    fn test_second_literal_matches_goal() {
        let env = thing_env(
            r#"
            axiom axiom1: f(g(t, t)) | f(t2)
            axiom axiom2: !f(g(t, t)) | f(t2)
            theorem goal: f(t2)
        "#,
        );
        assert_eq!(Prover::prove_theorem(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_matching_newly_synthesized_goal() {
        let mut env = Environment::new();
        env.add(
            r#"
        type Nat: axiom
        let 0: Nat = axiom
        axiom everything(x0: Nat -> bool, x1: Nat): x0(x1)
        let add: (Nat, Nat) -> Nat = axiom
        theorem goal(a: Nat): add(a, 0) = a
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_closure_proof() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let add: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) = function(b: Nat) { add(a, b) }
            theorem goal(a: Nat, b: Nat): add(a, b) = adder(a)(b)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_boolean_equality() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let add: (Nat, Nat) -> Nat = axiom
            define lte(a: Nat, b: Nat) -> bool = exists(c: Nat) { add(a, c) = b }
            define lt(a: Nat, b: Nat) -> bool = lte(a, b) & a != b
            theorem goal(a: Nat): !lt(a, a)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_using_conditional_existence_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let 1: Nat = axiom
            let Suc: Nat -> Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            axiom one_neq_zero: 1 != 0
            theorem goal: exists(x: Nat) { 1 = Suc(x) }
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_instance_of_conditional_existence_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            theorem goal: zero_or_suc(y)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_another_instance_of_conditional_existence_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            let Suc: Nat -> Nat = axiom
            let y: Nat = axiom
            axiom zero_or_suc(a: Nat): a = 0 | exists(b: Nat) { a = Suc(b) }
            axiom y_not_zero: y != 0
            theorem goal: zero_or_suc(y)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_forall_scopes() {
        let mut env = Environment::new();
        // Unprovable, since we know nothing about lt, but it shouldn't crash.
        env.add(
            r#"
            type Nat: axiom
            let lt: (Nat, Nat) -> bool = axiom
            theorem strong_induction(f: Nat -> bool): forall(k: Nat) {
                forall(m: Nat) { lt(m, k) -> f(m) } -> f(k)
            } -> forall(n: Nat) { f(n) }
            "#,
        );
        assert_eq!(Prover::prove(&env, "strong_induction"), Outcome::Exhausted);
    }

    #[test]
    fn test_struct_new_equation() {
        let mut env = Environment::new();
        env.add(
            r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(p: Pair): p = Pair.new(Pair.first(p), Pair.second(p))
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_struct_first_member_equation() {
        let mut env = Environment::new();
        env.add(
            r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(a: bool, b: bool): Pair.first(Pair.new(a, b)) = a
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_struct_second_member_equation() {
        let mut env = Environment::new();
        env.add(
            r#"
            struct Pair {
                first: bool
                second: bool
            }
            theorem goal(a: bool, b: bool): Pair.second(Pair.new(a, b)) = b
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_proving_templated_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            theorem goal<T>(a: T, b: T, c: T): a = b & b = c -> a = c
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_applying_templated_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            theorem foo<T>(a: T): a = a
            theorem goal: foo(0)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_applying_templated_function() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define foo<T>(a: T) -> bool = (a = a)
            let 0: Nat = axiom
            theorem goal: foo(0)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_templated_definition_and_theorem() {
        let mut env = Environment::new();
        env.add(
            r#"
            define foo<T>(a: T) -> bool = axiom
            axiom foo_true<T>(a: T): foo(a)
            type Nat: axiom
            let 0: Nat = axiom
            theorem goal: foo(0)
            "#,
        );
        // assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    // An environment with theorems that we should be able to prove in testing.
    // Ideally when there's a problem with one of these theorems we can simplify it
    // to a test that doesn't use the snap environment.
    fn snap_env() -> Environment {
        let mut env = Environment::new();
        env.load_file("snapnat.ac").unwrap();
        env
    }

    #[test]
    fn test_snap_add_zero_right() {
        let env = snap_env();
        assert_eq!(
            Prover::prove_theorem(&env, "add_zero_right"),
            Outcome::Success
        );
    }

    #[test]
    fn test_snap_one_plus_one() {
        let env = snap_env();
        assert_eq!(
            Prover::prove_theorem(&env, "one_plus_one"),
            Outcome::Success
        );
    }

    #[test]
    fn test_snap_add_zero_left() {
        let env = snap_env();
        assert_eq!(
            Prover::prove_theorem(&env, "add_zero_left"),
            Outcome::Success
        );
    }

    #[test]
    fn test_snap_add_suc_right() {
        let env = snap_env();
        assert_eq!(
            Prover::prove_theorem(&env, "add_suc_right"),
            Outcome::Success
        );
    }

    #[test]
    fn test_snap_add_suc_left() {
        let env = snap_env();
        assert_eq!(
            Prover::prove_theorem(&env, "add_suc_left"),
            Outcome::Success
        );
    }

    #[test]
    fn test_snap_suc_ne() {
        let env = snap_env();
        assert_eq!(Prover::prove_theorem(&env, "suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_snap_suc_suc_ne() {
        let env = snap_env();
        assert_eq!(Prover::prove_theorem(&env, "suc_suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_snap_add_comm() {
        let env = snap_env();
        assert_eq!(Prover::prove_theorem(&env, "add_comm"), Outcome::Success);
    }
}
