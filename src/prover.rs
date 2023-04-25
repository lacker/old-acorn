use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::{ActiveSet, ProofStep};
use crate::atom::Atom;
use crate::display::DisplayClause;
use crate::environment::Environment;
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
    verbose: bool,

    // If a trace string is set, we print out what happens with the clause matching it.
    trace: Option<String>,

    // Whether we have hit the trace
    pub hit_trace: bool,
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
            verbose: true,
            trace: None,
            hit_trace: false,
        }
    }

    pub fn set_trace(&mut self, trace: &str) {
        self.trace = Some(trace.to_string());
    }

    // Normalizes the proposition and adds it as a passive clause.
    // The explicitly imported propositions are weight zero because they should be prioritized over
    // all the autogenerated propositions.
    fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            self.passive.add_with_weight(clause, 0);
        }
    }

    fn add_negated(&mut self, proposition: AcornValue) {
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

    // Prints out the entire active set
    pub fn print_active(&self) {
        for clause in self.active_set.iter_clauses() {
            println!("{}", self.display(clause));
        }
    }

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

    // Activates the next clause from the queue.
    pub fn activate_next(&mut self) -> Outcome {
        let clause = if let Some(clause) = self.passive.pop() {
            clause
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
            return Outcome::Success;
        }

        let tracing = self.is_tracing(&clause);
        let verbose = self.verbose || tracing;

        self.synthesizer.observe(&clause);

        let gen_clauses = self.active_set.generate(&clause);
        self.active_set.insert(clause.clone());
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
                    return Outcome::Success;
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
                self.passive.add(c);
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
                    self.passive.add(simp_clause);
                }
            }
        }

        Outcome::Unknown
    }

    fn search_for_contradiction(&mut self, size: i32, seconds: f32) -> Outcome {
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

    pub fn assume_false(&mut self, theorem_name: &str) {
        if self.dirty {
            panic!("assume_false called on a dirty prover");
        }
        for (name, value) in self.env.iter_theorems() {
            if name == theorem_name {
                self.add_negated(value.clone());

                if self.verbose {
                    println!("\nprover initial state:");
                    self.passive.map(&mut |clause| {
                        println!("  {}", self.display(clause));
                    });
                    println!();
                }

                return;
            }

            self.add_proposition(value.clone());
        }
        panic!("no theorem named {}", theorem_name);
    }

    pub fn prove_limited(&mut self, theorem_name: &str, size: i32, seconds: f32) -> Outcome {
        self.assume_false(theorem_name);
        let answer = self.search_for_contradiction(size, seconds);
        if self.verbose {
            println!("conclusion: {:?}\n", answer);
        }
        return answer;
    }

    pub fn prove(&mut self, theorem_name: &str) -> Outcome {
        self.prove_limited(theorem_name, 1000, 1.0)
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Failure);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("goal"), Outcome::Failure);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Failure);
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
        assert_eq!(prover.prove("goal"), Outcome::Failure);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
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
        assert_eq!(prover.prove("goal"), Outcome::Success);
    }

    fn nat_ac_env() -> Environment {
        let mut env = Environment::new();
        env.load_file("nat.ac").unwrap();
        env
    }

    #[test]
    fn test_proving_add_zero_right() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_zero_right"), Outcome::Success);
    }

    #[test]
    fn test_proving_one_plus_one() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("one_plus_one"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_zero_left() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_zero_left"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_suc_right() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_suc_right"), Outcome::Success);
    }

    #[test]
    fn test_proving_add_suc_left() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_suc_left"), Outcome::Success);
    }

    #[test]
    fn test_suc_ne() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_suc_suc_ne() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("suc_suc_ne"), Outcome::Success);
    }

    #[test]
    fn test_add_comm() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.prove("add_comm"), Outcome::Success);
    }

    #[test]
    fn test_add_assoc() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(
            prover.prove_limited("add_assoc", 10000, 30.0),
            Outcome::Success
        );
    }
}
