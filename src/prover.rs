use std::collections::VecDeque;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::normalizer::Normalizer;
use crate::term::{Clause, Literal, Substitution, Term};

pub struct Prover<'a> {
    env: &'a Environment,
    normalizer: Normalizer,

    // The "active" clauses are the ones we use for reasoning.
    // The "passive" clauses are a queue of pending clauses that
    // we will add to the active clauses in the future.
    active: Vec<Clause>,
    passive: VecDeque<Clause>,

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
            active: Vec::new(),
            passive: VecDeque::new(),
            env,
            dirty: false,
        }
    }

    // Normalizes the proposition and adds it as a passive clause.
    fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        println!("adding prop: {}", proposition);

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

    // Checks whether we already know how to compare these two terms.
    // This only does exact comparisons, so if we already know x = y,
    // this won't find that f(x) = f(y).
    //
    // Meaning of the return value:
    // Some(true): term1 = term2
    // Some(false): term1 != term2
    // None: we don't know anything
    fn exact_compare(&self, term1: &Term, term2: &Term) -> Option<bool> {
        for clause in &self.active {
            if clause.literals.len() != 1 {
                continue;
            }
            let (left, right, answer) = match &clause.literals[0] {
                Literal::NotEquals(left, right) => (left, right, Some(false)),
                Literal::Equals(left, right) => (left, right, Some(true)),
                _ => continue,
            };

            // Check if (left, right) specializes to (term1, term2)
            let mut sub = Substitution::new();
            if sub.identify_terms(left, term1) && sub.identify_terms(right, term2) {
                return answer;
            }

            // Check if (left, right) specializes to (term2, term1)
            sub = Substitution::new();
            if sub.identify_terms(left, term2) && sub.identify_terms(right, term1) {
                return answer;
            }
        }
        None
    }

    // Meaning of the return value:
    // Some(true): term is true
    // Some(false): !term is true
    // None: we don't know anything
    fn evaluate_term(&self, term: &Term) -> Option<bool> {
        for clause in &self.active {
            if clause.literals.len() != 1 {
                continue;
            }
            let (known_term, answer) = match &clause.literals[0] {
                Literal::Positive(t) => (t, Some(true)),
                Literal::Negative(t) => (t, Some(false)),
                _ => continue,
            };
            let mut sub = Substitution::new();
            if sub.identify_terms(known_term, term) {
                return answer;
            }
        }
        None
    }

    // Meaning of the return value:
    // Some(true): literal is true
    // Some(false): !literal is true
    // None: we don't know anything
    fn evaluate_literal(&self, literal: &Literal) -> Option<bool> {
        match literal {
            Literal::Positive(term) => self.evaluate_term(term),
            Literal::Negative(term) => self.evaluate_term(term).map(|x| !x),
            Literal::Equals(left, right) => self.exact_compare(left, right),
            Literal::NotEquals(left, right) => self.exact_compare(left, right).map(|x| !x),
        }
    }

    // Activates the next clause from the queue.
    fn activate_next(&mut self) -> Result {
        let clause = if let Some(clause) = self.passive.pop_front() {
            clause
        } else {
            // We're out of clauses to process, so we can't make any more progress.
            return Result::Failure;
        };

        // Simplify the clause
        let mut literals = Vec::new();
        for literal in clause.literals {
            match self.evaluate_literal(&literal) {
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

        self.active.push(Clause::new(&clause.universal, literals));
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
}
