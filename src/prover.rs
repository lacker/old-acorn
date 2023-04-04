use std::collections::VecDeque;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::active_set::ActiveSet;
use crate::atom::AtomId;
use crate::environment::Environment;
use crate::normalizer::Normalizer;
use crate::substitution::Substitution;
use crate::term::{Clause, Literal, Term};

pub struct Prover<'a> {
    env: &'a Environment,
    normalizer: Normalizer,

    // The "active" clauses are the ones we use for reasoning.
    active_set: ActiveSet,

    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    passive: VecDeque<Clause>,

    old_active: Vec<Clause>,

    // A prover is dirty when it has had false propositions added to it.
    dirty: bool,
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
            old_active: Vec::new(),
            active_set: ActiveSet::new(),
            passive: VecDeque::new(),
            env,
            dirty: false,
        }
    }

    // Normalizes the proposition and adds it as a passive clause.
    fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        println!("\nadding prop: {}", proposition);
        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            println!("adding clause: {}", clause);
            self.passive.push_back(clause);
        }
    }

    fn add_negated(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.dirty = true;
        let negated = AcornValue::Not(Box::new(proposition));
        self.add_proposition(negated);
    }

    // Checks whether (term1 = term) = equal for all values of the universally quantified variables.
    // This only does exact comparisons, so if we already know x = y,
    // this won't find that f(x) = f(y).
    //
    // Meaning of the return value:
    // Some(true): (term1 = term2) = equal always
    // Some(false): there is a counterexample where (term1 = term2) != equal
    // None: we don't know
    fn old_exact_compare(
        &self,
        term1: &Term,
        term2: &Term,
        equal: bool,
        find_counterexamples: bool,
    ) -> Option<bool> {
        for clause in &self.old_active {
            if clause.literals.len() != 1 {
                continue;
            }
            let literal = &clause.literals[0];

            if literal.positive == equal {
                // Signs match.
                // Check for a proof by specialization.
                // Check if (left, right) specializes to (term1, term2)
                let mut sub = Substitution::new();
                if sub.match_terms(&literal.left, term1) && sub.match_terms(&literal.right, term2) {
                    return Some(true);
                }

                // Check if (left, right) specializes to (term2, term1)
                sub = Substitution::new();
                if sub.match_terms(&literal.left, term2) && sub.match_terms(&literal.right, term1) {
                    return Some(true);
                }
            } else if find_counterexamples {
                // Signs don't match.
                // Check for a counterexample.
                // Check if (left, right) unifies to (term1, term2).
                // Note that "shift" is the size for left/right so we have to shift term1 and term2.
                let shift = clause.num_quantifiers() as AtomId;
                let mut sub = Substitution::new();
                if sub.unify_terms(&literal.left, term1, shift)
                    && sub.unify_terms(&literal.right, term2, shift)
                {
                    return Some(false);
                }

                // Check if (left, right) unifies to (term2, term1).
                sub = Substitution::new();
                if sub.unify_terms(&literal.left, term2, shift) {
                    if sub.unify_terms(&literal.right, term1, shift) {
                        return Some(false);
                    }
                }
            }
        }
        None
    }

    // Check whether term = valuation for all values of the universally quantified variables.
    // Meaning of the return value:
    // Some(true): term = evaluation always
    // Some(false): there is some counterexample where term != evaluation
    // None: we don't know
    fn old_evaluate_term(&self, term: &Term, evaluation: bool) -> Option<bool> {
        for clause in &self.old_active {
            if clause.literals.len() != 1 {
                continue;
            }
            let literal = &clause.literals[0];
            if !literal.right.is_true() {
                continue;
            }
            if literal.positive == evaluation {
                // Signs match.
                // If this term is a generalization of the known term, then term = evaluation.
                let mut sub = Substitution::new();
                if sub.match_terms(term, &literal.left) {
                    return Some(true);
                }
            } else {
                // Signs don't match.
                // If these terms can unify, this is a counterexample.
                // Note that this depends on the fact that every type is occupied.
                let mut sub = Substitution::new();
                if sub.unify_terms(&literal.left, term, clause.num_quantifiers() as AtomId) {
                    return Some(false);
                }
            }
        }
        None
    }

    // Meaning of the return value:
    // Some(true): literal is true over the (implicit) universal quantifiers
    // Some(false): literal is false, there is some counterexample
    // None: we don't know anything
    fn old_evaluate_literal(&self, literal: &Literal) -> Option<bool> {
        if literal.right.is_true() {
            return self.old_evaluate_term(&literal.left, literal.positive);
        }
        if literal.left == literal.right {
            return Some(literal.positive);
        }

        if let Some((subleft, subright)) = literal.left.matches_but_one(&literal.right) {
            // If a = b, then that proves f(a) = f(b).
            // TODO: Should this really work the other way?
            if self.old_exact_compare(subleft, subright, true, false) == Some(true) {
                return Some(literal.positive);
            }
        }
        self.old_exact_compare(&literal.left, &literal.right, literal.positive, true)
    }

    fn old_rewrite_term(&self, term: Term) -> Term {
        let mut answer = term;
        loop {
            for clause in &self.old_active {
                if clause.literals.len() != 1 {
                    continue;
                }
                let literal = &clause.literals[0];
                if !literal.positive {
                    continue;
                }
                match answer.rewrite(&literal.left, &literal.right) {
                    Some(new_term) => {
                        answer = new_term;
                        continue;
                    }
                    None => {}
                }
            }
            return answer;
        }
    }

    fn old_rewrite_literal(&self, literal: Literal) -> Literal {
        literal.map(&mut |term| self.old_rewrite_term(term.clone()))
    }

    // Activates the next clause from the queue.
    fn old_activate_next(&mut self) -> Result {
        let clause = if let Some(clause) = self.passive.pop_front() {
            clause
        } else {
            // We're out of clauses to process, so we can't make any more progress.
            return Result::Failure;
        };

        // Simplify the clause
        let mut literals = Vec::new();
        for literal in clause.literals {
            let literal = self.old_rewrite_literal(literal);
            match self.old_evaluate_literal(&literal) {
                Some(true) => {
                    // This clause is true, so activating it is a no-op.
                    return Result::Unknown;
                }
                Some(false) => {
                    // This literal is false, so we can leave it out of the new active clause.
                    continue;
                }
                None => {
                    // We don't know anything about this literal, so we'll keep it.
                    literals.push(literal);
                }
            }
        }
        if literals.is_empty() {
            // All the literals were false, so this clause is false.
            // That means we have successfully proven a contradiction.
            return Result::Success;
        }

        self.old_active.push(Clause::new(literals));
        Result::Unknown
    }

    // Activates the next clause from the queue.
    fn activate_next(&mut self) -> Result {
        let clause = if let Some(clause) = self.passive.pop_front() {
            clause
        } else {
            // We're out of clauses to process, so we can't make any more progress.
            return Result::Failure;
        };

        let new_clauses = self.active_set.generate(&clause);
        for clause in new_clauses {
            if clause.is_tautology() {
                continue;
            }
            if clause.is_impossible() {
                return Result::Success;
            }
            self.passive.push_back(clause);
        }
        self.active_set.insert(clause);
        Result::Unknown
    }

    fn old_search_for_contradiction(&mut self) -> Result {
        let start_time = std::time::Instant::now();
        while start_time.elapsed().as_secs() < 3 {
            let result = self.old_activate_next();
            if result != Result::Unknown {
                return result;
            }
        }
        Result::Unknown
    }

    fn search_for_contradiction(&mut self) -> Result {
        let start_time = std::time::Instant::now();
        while start_time.elapsed().as_secs() < 3 {
            let result = self.activate_next();
            if result != Result::Unknown {
                return result;
            }
        }
        Result::Unknown
    }

    pub fn old_prove(&mut self, theorem_name: &str) -> Result {
        if self.dirty {
            panic!("prove called on a dirty prover");
        }
        for (name, value) in self.env.iter_theorems() {
            if name == theorem_name {
                // To prove a statement, we negate, then search for a contradiction.
                self.add_negated(value.clone());

                return self.old_search_for_contradiction();
            }

            self.add_proposition(value.clone());
        }
        panic!("no theorem named {}", theorem_name);
    }

    pub fn prove(&mut self, theorem_name: &str) -> Result {
        if self.dirty {
            panic!("prove called on a dirty prover");
        }
        for (name, value) in self.env.iter_theorems() {
            if name == theorem_name {
                // To prove a statement, we negate, then search for a contradiction.
                self.add_negated(value.clone());

                return self.search_for_contradiction();
            }

            self.add_proposition(value.clone());
        }
        panic!("no theorem named {}", theorem_name);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn thing_env() -> Environment {
        let mut env = Environment::new();
        env.add(
            r#"
        type Thing: axiom
        define t: Thing = axiom
        define t2: Thing = axiom
        define f: Thing -> bool = axiom
        define g: (Thing, Thing) -> Thing = axiom
        "#,
        );
        env
    }

    #[test]
    fn test_specialization() {
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
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
        let mut env = thing_env();
        env.add(
            r#"
            axiom not_f_t: !f(t)
            axiom g_id(x: Thing): g(x, x) = x
            theorem goal: !f(g(t, t))
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
        assert_eq!(prover.old_prove("add_zero_right"), Result::Success);
    }

    // #[test]
    #[allow(dead_code)]
    fn test_proving_one_plus_one() {
        let env = nat_ac_env();
        let mut prover = Prover::new(&env);
        assert_eq!(prover.old_prove("one_plus_one"), Result::Success);
    }
}
