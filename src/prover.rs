use std::collections::VecDeque;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::{ActiveSet, ProofStep};
use crate::display::DisplayClause;
use crate::environment::Environment;
use crate::normalizer::Normalizer;
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
    passive: VecDeque<Clause>,

    // A prover is dirty when it has had false propositions added to it.
    dirty: bool,

    // A verbose prover prints out a lot of stuff.
    verbose: bool,

    // If a trace string is set, we print out what happens with the clause matching it.
    trace: Option<String>,
}

// The result of a prover operation.
// "Success" or "Failure" generally terminate the proof process.
// "Unknown" can mean either that we should continue working, or that we just
// couldn't figure out the answer.
#[derive(Debug, PartialEq, Eq)]
pub enum Result {
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
            passive: VecDeque::new(),
            env,
            dirty: false,
            verbose: true,
            trace: None,
        }
    }

    pub fn set_trace(&mut self, trace: &str) {
        self.verbose = false;
        self.trace = Some(trace.to_string());
    }

    fn add_passive(&mut self, clause: Clause) {
        self.passive.push_back(clause);
    }

    // Normalizes the proposition and adds it as a passive clause.
    fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        if self.verbose {
            println!("\nadding prop: {}", proposition);
        }
        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            self.add_passive(clause);
        }
    }

    fn add_negated(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.dirty = true;
        self.add_proposition(proposition.negate());
    }

    fn is_tracing(&self, clause: &Clause) -> bool {
        if let Some(trace) = &self.trace {
            self.display(clause).to_string().starts_with(trace)
        } else {
            false
        }
    }

    // Activates the next clause from the queue.
    fn activate_next(&mut self) -> Result {
        let clause = if let Some(clause) = self.passive.pop_front() {
            if self.active_set.contains(&clause) {
                // We've already seen this clause, so we can skip it.
                return Result::Unknown;
            }
            clause
        } else {
            // We're out of clauses to process, so we can't make any more progress.
            return Result::Failure;
        };
        let tracing = self.is_tracing(&clause);
        let verbose = self.verbose || tracing;
        if verbose {
            println!("activating: {}", self.display(&clause));
        }

        self.synthesizer.observe(&clause);

        let gen_clauses = self.active_set.generate(&clause);
        let print_limit = 5;
        if !gen_clauses.is_empty() {
            let len = gen_clauses.len();
            if verbose {
                println!(
                    "generated {} new clauses{}:",
                    len,
                    if len > print_limit { ", eg" } else { "" }
                );
            }
            for (i, (c, ps)) in gen_clauses.into_iter().enumerate() {
                if c.is_impossible() {
                    return Result::Success;
                }
                if verbose && (i < print_limit || tracing) {
                    println!("  {}", self.display(&c));
                } else if self.is_tracing(&c) {
                    println!("when activating:");
                    println!("  {}", self.display(&clause));
                    match ps {
                        ProofStep::ActivateParamodulator(i) => {
                            println!(
                                "used AP with:\n  {}",
                                self.display(&self.active_set.get_clause(i))
                            );
                        }
                        ProofStep::ActivateResolver(i) => {
                            println!(
                                "used AR with:\n  {}",
                                self.display(&self.active_set.get_clause(i))
                            );
                        }
                        ProofStep::EqualityFactoring => {
                            print!("used EF ");
                        }
                        ProofStep::EqualityResolution => {
                            print!("used ER ");
                        }
                    }
                    println!("to generate:");
                    println!("  {}", self.display(&c));
                }
                self.add_passive(c);
            }
        }

        let synth_clauses = self.synthesizer.synthesize(&clause);
        if !synth_clauses.is_empty() {
            if verbose {
                println!("synthesized {} new clauses:", synth_clauses.len());
            }
            for clause in synth_clauses {
                if verbose {
                    println!("  {}", self.display(&clause));
                }
                self.add_passive(clause);
            }
        }

        self.active_set.insert(clause);
        Result::Unknown
    }

    fn search_for_contradiction(&mut self, steps: i32, seconds: f32) -> Result {
        let start_time = std::time::Instant::now();
        let mut steps_taken = 0;
        loop {
            let result = self.activate_next();
            if result != Result::Unknown {
                return result;
            }
            steps_taken += 1;
            if steps_taken >= steps {
                if self.verbose {
                    println!("active set size: {}", self.active_set.len());
                    println!("prover hit step limit after {} steps", steps_taken);
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
        Result::Unknown
    }

    fn display<'a>(&'a self, clause: &'a Clause) -> DisplayClause<'a> {
        DisplayClause {
            clause,
            env: self.env,
        }
    }

    pub fn prove_limited(&mut self, theorem_name: &str, steps: i32, seconds: f32) -> Result {
        if self.dirty {
            panic!("prove called on a dirty prover");
        }
        for (name, value) in self.env.iter_theorems() {
            if name == theorem_name {
                // To prove a statement, we negate, then search for a contradiction.
                self.add_negated(value.clone());

                if self.verbose {
                    println!("\nprover initial state:");
                    for clause in &self.passive {
                        println!("  {}", self.display(clause));
                    }
                    println!();
                }

                let answer = self.search_for_contradiction(steps, seconds);
                if self.verbose {
                    println!("conclusion: {:?}\n", answer);
                }
                return answer;
            }

            self.add_proposition(value.clone());
        }
        panic!("no theorem named {}", theorem_name);
    }

    pub fn prove(&mut self, theorem_name: &str) -> Result {
        self.prove_limited(theorem_name, 1000, 0.1)
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
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_backward_specialization_fails() {
        let env = thing_env(
            r#"
        axiom f_one: f(t)
        theorem goal(x: Thing): f(x)
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Failure);
    }

    #[test]
    fn test_finds_example() {
        let env = thing_env(
            r#"
        axiom f_one: f(t)
        theorem goal: exists(x: Thing, f(x))
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_finds_negative_example() {
        let env = thing_env(
            r#"
        axiom not_f(x: Thing): !f(x)
        theorem goal: !f(t)
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_extends_equality() {
        let env = thing_env(
            r#"
            axiom t_eq_t2: t = t2
            theorem goal: f(t) = f(t2) 
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_rewriting() {
        let env = thing_env(
            r#"
        axiom f_t: f(t)
        axiom g_id(x: Thing): g(x, x) = x
        theorem goal: f(g(t, t))
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_rewrites_can_fail() {
        let env = thing_env(
            r#"
        axiom f_t: f(t)
        axiom g_id(x: Thing): g(x, x) = x
        theorem goal: f(g(t, t2))
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Failure);
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
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_extends_ne() {
        let env = thing_env(
            r#"
        axiom f_t_ne_f_t2: f(t) != f(t2)
        theorem goal: t != t2
        "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_equality_resolution() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing): x != t | f(t)
            theorem goal: f(t)
            "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_equality_factoring() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing, y: Thing): x = t | y = t
            theorem goal(x: Thing): x = t2
            "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
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
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Failure);
    }

    #[test]
    fn test_synthesis_avoids_loops() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t) | f(h(t))
            theorem goal: f(t2)
            "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Failure);
    }

    #[test]
    fn test_higher_order_unification() {
        let env = thing_env(
            r#"
            axiom foo(x: Thing -> bool): x(t)
            theorem goal: f(t)
            "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    #[test]
    fn test_higher_order_synthesis() {
        let env = thing_env(
            r#"
            axiom t_implies_all(q: Thing -> bool): q(t) -> forall(x: Thing, q(x))
            theorem goal(x: Thing): x = t
            "#,
        );
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Result::Success);
    }

    fn nat_ac_env() -> Environment {
        let mut env = Environment::new();
        env.add(
            r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

define 0: Nat = axiom

define Suc: Nat -> Nat = axiom
define 1: Nat = Suc(0)

axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y

axiom suc_neq_zero(x: Nat): Suc(x) != 0

axiom induction(f: Nat -> bool): f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> forall(n: Nat, f(n))

// Ideally a and f would be templated rather than just Nat.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat): recursion(f, a, Suc(n)) = f(recursion(f, a, n))

define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)

// Now let's have some theorems.

theorem add_zero_right(a: Nat): add(a, 0) = a

define 2: Nat = Suc(1)

theorem one_plus_one: add(1, 1) = 2

theorem add_zero_left(a: Nat): add(0, a) = a

theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))

theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))

theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))
"#,
        );
        env
    }

    #[test]
    fn test_proving_add_zero_right() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_zero_right"), Result::Success);
    }

    #[test]
    fn test_proving_one_plus_one() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("one_plus_one"), Result::Success);
    }

    // #[test]
    // fn test_proving_add_zero_left() {
    //     let env = nat_ac_env();
    //     let mut prover = Prover::new(&env);
    //     prover.set_trace("recursion(Suc, 0, Suc(x0)) = Suc(x0) | p6(x0)");
    //     assert_eq!(
    //         prover.prove_limited("add_zero_left", 1000000, 5.0),
    //         Result::Success
    //     );
    // }
}
