use std::collections::HashSet;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::{ActiveSet, ProofStep};
use crate::atom::Atom;
use crate::display::DisplayClause;
use crate::environment::{Environment, GoalContext};
use crate::normalizer::Normalizer;
use crate::passive_set::PassiveSet;
use crate::synthesizer::Synthesizer;
use crate::term::Clause;

pub struct Prover<'a> {
    env: &'a Environment,
    normalizer: Normalizer,
    synthesizer: Synthesizer,

    // The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    passive: PassiveSet,

    // A prover is dirty when it has had false propositions added to it.
    dirty: bool,

    // A verbose prover prints out a lot of stuff.
    pub verbose: bool,

    // If a trace string is set, we print out what happens with the clause matching it, regardless
    // of verbosity.
    trace: Option<String>,

    // Whether we have hit the trace
    pub hit_trace: bool,

    // Where each clause in the active set came from.
    history: Vec<ProofStep>,

    // The final step that proves a contradiction, if we have one.
    final_step: Option<ProofStep>,
}

// The outcome of a prover operation.
// "Success" or "Failure" generally terminate the proof process.
// "Unknown" can mean either that we should continue working, or that we just
// couldn't figure out the answer.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Failure,
    Unknown,
}

impl Prover<'_> {
    pub fn new(env: &Environment) -> Prover {
        Prover {
            normalizer: Normalizer::new(),
            synthesizer: Synthesizer::new(),
            active_set: ActiveSet::new(),
            passive: PassiveSet::new(),
            env,
            dirty: false,
            verbose: false,
            trace: None,
            hit_trace: false,
            history: Vec::new(),
            final_step: None,
        }
    }

    pub fn set_trace(&mut self, trace: &str) {
        self.trace = Some(trace.to_string());
    }

    pub fn unset_trace(&mut self) {
        self.trace = None;
    }

    // Normalizes the proposition and adds it as a passive clause.
    // The explicitly imported propositions are weight zero because they should be prioritized over
    // all the autogenerated propositions.
    pub fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            self.passive
                .add_with_weight(clause, ProofStep::assumption(), 0);
        }
    }

    pub fn add_negated(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.dirty = true;
        self.add_proposition(proposition.negate());
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
        println!("{} clauses in the passive set", self.passive.len());
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
        for clause in self.passive.iter_clauses() {
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
            println!("{} passive clauses matched {}", count, substr);
        } else {
            println!("{} clauses total in the passive set", count);
        }
    }

    // Prints out information for a specific atom
    pub fn print_atom_info(&self, s: &str) {
        if let Some(atom) = Atom::parse(s) {
            match atom {
                Atom::Synthetic(i) => {
                    if let Some(lit) = self.synthesizer.get_definition(i) {
                        println!("{} := {}", atom, lit);
                    } else {
                        println!("no definition for {}", atom);
                    }
                }
                _ => {
                    println!("we have no way to print info for {}", atom);
                }
            }
        } else {
            println!("not an atom: {}", s);
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

    pub fn print_proof_step(&self, clause: &Clause, ps: ProofStep) {
        println!("{:?} generated:\n    {}", ps.rule, self.display(clause));
        if let Some(i) = ps.activated {
            let c = self.display(self.active_set.get_clause(i));
            println!("  using clause {}:\n    {}", i, c);
        }
        if let Some(i) = ps.existing {
            let c = self.display(self.active_set.get_clause(i));
            println!("  with clause {}:\n    {}", i, c);
        }
    }

    pub fn print_proof(&self) {
        let final_step = if let Some(final_step) = self.final_step {
            final_step
        } else {
            println!("we do not have a proof");
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
            let step = self.history[i];
            for j in step.indices() {
                todo.push(*j);
            }
        }

        // Print out the clauses in order.
        let mut indices = done.into_iter().collect::<Vec<_>>();
        indices.sort();
        println!("in total, we activated {} proof steps.", self.history.len());
        println!("the proof uses {} steps:", indices.len());
        for i in indices {
            let step = self.history[i];
            let clause = self.active_set.get_clause(i);
            print!("clause {}: ", i);
            self.print_proof_step(clause, step);
        }
        print!("final step: ");
        self.print_proof_step(&Clause::impossible(), final_step);
    }

    // Activates the next clause from the queue.
    pub fn activate_next(&mut self) -> Outcome {
        let (clause, proof_step) = if let Some((clause, proof_step)) = self.passive.pop() {
            (clause, proof_step)
        } else {
            // We're out of clauses to process, so we can't make any more progress.
            return Outcome::Failure;
        };

        let mut original_clause_string = "".to_string();
        if self.verbose {
            original_clause_string = self.display(&clause).to_string();
            println!("activating: {}", original_clause_string);
        }

        let clause = if let Some(clause) = self.active_set.simplify(&clause) {
            clause
        } else {
            // The clause is redundant, so skip it.
            if self.verbose {
                println!("  redundant");
            }
            return Outcome::Unknown;
        };
        if self.verbose {
            let s = self.display(&clause).to_string();
            if s != original_clause_string {
                println!("simplified: {}", s);
            }
        }

        if clause.is_impossible() {
            self.final_step = Some(proof_step);
            return Outcome::Success;
        }
        self.history.push(proof_step);

        let tracing = self.is_tracing(&clause);
        let verbose = self.verbose || tracing;

        self.synthesizer.observe(&clause);

        let gen_clauses = self.active_set.generate(&clause);
        let mut simp_clauses = vec![];
        for (generated_clause, step) in gen_clauses {
            if let Some(simp_clause) = self.active_set.simplify(&generated_clause) {
                simp_clauses.push((simp_clause, step));
            }
        }

        let print_limit = 5;
        if !simp_clauses.is_empty() {
            let len = simp_clauses.len();
            if verbose {
                println!(
                    "generated {} new clauses{}:",
                    len,
                    if len > print_limit { ", eg" } else { "" }
                );
            }
            for (i, (c, ps)) in simp_clauses.into_iter().enumerate() {
                if c.is_impossible() {
                    self.final_step = Some(ps);
                    return Outcome::Success;
                }
                if verbose && (i < print_limit || tracing) {
                    println!("  {}", self.display(&c));
                } else if self.is_tracing(&c) {
                    self.print_proof_step(&c, ps);
                }
                self.passive.add(c, ps);
            }
        }

        let synth_clauses = self.synthesizer.synthesize(&clause);
        if !synth_clauses.is_empty() {
            if verbose {
                println!("synthesized {} new clauses:", synth_clauses.len());
            }
            for clause in synth_clauses {
                if let Some(simp_clause) = self.active_set.simplify(&clause) {
                    if verbose {
                        println!("  {}", self.display(&simp_clause));
                    }
                    self.passive.add(simp_clause, ProofStep::definition());
                }
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
            if self.active_set.len() >= size as usize {
                if self.verbose {
                    println!("active set size hit the limit: {}", self.active_set.len());
                }
                break;
            }
            let elapsed = start_time.elapsed().as_secs_f32();
            if elapsed >= seconds {
                if self.verbose {
                    println!("active set size: {}", self.active_set.len());
                    println!("prover hit time limit after {} seconds", elapsed);
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
        }
    }

    pub fn load_goal<'a>(goal_context: &GoalContext<'a>) -> Prover<'a> {
        let mut prover = Prover::new(&goal_context.env);
        for fact in &goal_context.facts {
            prover.add_proposition(fact.clone());
        }
        prover.add_negated(goal_context.goal.clone());
        prover
    }

    pub fn prove(env: &Environment, theorem_name: &str) -> Outcome {
        let goal_context = env.get_theorem_context(theorem_name);
        let mut prover = Prover::load_goal(&goal_context);
        prover.search_for_contradiction(1000, 1.0)
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
        define t: Thing = axiom
        define t2: Thing = axiom
        define f: Thing -> bool = axiom
        define g: (Thing, Thing) -> Thing = axiom
        define h: Thing -> Thing = axiom
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
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let env = thing_env(
            r#"
        axiom f_one: f(t)
        theorem goal(x: Thing): f(x)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Failure);
    }

    #[test]
    fn test_finds_example() {
        let env = thing_env(
            r#"
        axiom f_one: f(t)
        theorem goal: exists(x: Thing, f(x))
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let env = thing_env(
            r#"
        axiom not_f(x: Thing): !f(x)
        theorem goal: !f(t)
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_equality() {
        let env = thing_env(
            r#"
            axiom t_eq_t2: t = t2
            theorem goal: f(t) = f(t2) 
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_composition() {
        let env = thing_env(
            r#"
        axiom f_t: f(t)
        axiom g_id(x: Thing): g(x, x) = x
        theorem goal: f(g(t, t))
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
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
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Failure);
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
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_extends_ne() {
        let env = thing_env(
            r#"
        axiom f_t_ne_f_t2: f(t) != f(t2)
        theorem goal: t != t2
        "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing): x != t | f(t)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing, y: Thing): x = t | y = t
            theorem goal(x: Thing): x = t2
            "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
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
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Failure);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t) | f(h(t))
            theorem goal: f(t2)
            "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Failure);
    }

    #[test]
    fn test_higher_order_unification() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t)
            theorem goal: f(t)
            "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    #[test]
    fn test_higher_order_synthesis() {
        let env = thing_env(
            r#"
            axiom t_implies_all(q: Thing -> bool): q(t) -> forall(x: Thing, q(x))
            theorem goal(x: Thing): x = t
            "#,
        );
        assert_eq!(Prover::prove(&env, "goal"), Outcome::Success);
    }

    fn nat_ac_env() -> Environment {
        let mut env = Environment::new();
        env.load_file("nat.ac").unwrap();
        env
    }

    #[test]
    fn test_proving_add_zero_right() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "add_zero_right"), Outcome::Success);
    }

    #[test]
    fn test_proving_one_plus_one() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "one_plus_one"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_zero_left() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "add_zero_left"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_suc_right() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "add_suc_right"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_suc_left() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "add_suc_left"), Outcome::Success);
    }

    #[test]
    fn test_suc_ne() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_suc_suc_ne() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "suc_suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_add_comm() {
        let env = nat_ac_env();
        assert_eq!(Prover::prove(&env, "add_comm"), Outcome::Success);
    }
}
