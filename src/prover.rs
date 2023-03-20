use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::normalizer::Normalizer;
use crate::term::{Clause, Literal, Substitution, Term};

pub struct Prover<'a> {
    pub normalizer: Normalizer,

    pub clauses: Vec<Clause>,

    env: &'a Environment,

    // A prover is dirty when it has had false propositions added to it.
    dirty: bool,
}

pub enum Compare {
    Equal,
    NotEqual,
    Unknown,
}

impl Prover<'_> {
    pub fn new(env: &Environment) -> Prover {
        Prover {
            normalizer: Normalizer::new(),
            clauses: vec![],
            env,
            dirty: false,
        }
    }

    // Normalizes the proposition and adds it to our clause list.
    fn add_proposition(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);

        let new_clauses = self.normalizer.normalize(proposition);
        for clause in new_clauses {
            println!("adding clause: {:?}", clause);
            self.clauses.push(clause);
        }
    }

    fn add_negated(&mut self, proposition: AcornValue) {
        assert_eq!(proposition.get_type(), AcornType::Bool);
        self.dirty = true;
        let negated = AcornValue::Not(Box::new(proposition));
        self.add_proposition(negated);
    }

    // Checks whether we already know whether these two terms are equal.
    // This only does exact comparisons, so if we already know x = y,
    // this won't find that f(x) = f(y).
    pub fn exact_compare(&self, term1: &Term, term2: &Term) -> Compare {
        for clause in &self.clauses {
            if clause.literals.len() != 1 {
                continue;
            }
            let (left, right, answer) = match &clause.literals[0] {
                Literal::NotEquals(left, right) => (left, right, Compare::NotEqual),
                Literal::Equals(left, right) => (left, right, Compare::Equal),
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
        Compare::Unknown
    }

    // Returns whether we could prove this statement.
    pub fn prove(&mut self, theorem_name: &str) -> bool {
        if self.dirty {
            panic!("prove called on a dirty prover");
        }
        for (name, value) in self.env.iter_theorems() {
            if name == theorem_name {
                // To prove a statement, we negate, then search for a contradiction.
                self.add_negated(value.clone());

                // TODO: search for a contradiction
                return false;
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
        prover.prove("add_zero_right");
    }
}
