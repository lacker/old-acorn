use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::atom::{Atom, AtomId, TypedAtom};
use crate::environment::Environment;
use crate::term::Clause;
use crate::type_space::TypeSpace;

pub struct Normalizer {
    // Types of the skolem functions produced
    // Some of them are just constants, so we store an AcornType rather than a FunctionType
    skolem_types: Vec<AcornType>,

    pub typespace: TypeSpace,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            skolem_types: vec![],
            typespace: TypeSpace::new(),
        }
    }

    // The input should already have negations moved inwards.
    // The stack must be entirely universal quantifiers.
    //
    // The value does *not* need to be in prenex normal form.
    // I.e., it can still have quantifier nodes, either "exists" or "forall", inside of
    // logical nodes, like "and" and "or".
    // All negations must be moved inside quantifiers, though.
    //
    // In general I think converting to prenex seems bad. Consider:
    //   forall(x, f(x)) & exists(y, g(y))
    // If we convert to prenex, we get:
    //   forall(x, exists(y, f(x) & g(y)))
    // which skolemizes to
    //   forall(x, f(x) & g(skolem(x)))
    // But there's a redundant arg here. The simpler form is just
    //   forall(x, f(x) & g(skolem()))
    // which is what we get if we don't convert to prenex first.
    pub fn skolemize(&mut self, stack: &Vec<AcornType>, value: AcornValue) -> AcornValue {
        match value {
            AcornValue::ForAll(quants, subvalue) => {
                let mut new_stack = stack.clone();
                new_stack.extend(quants.clone());
                let new_subvalue = self.skolemize(&new_stack, *subvalue);
                AcornValue::ForAll(quants, Box::new(new_subvalue))
            }

            AcornValue::Exists(quants, subvalue) => {
                // The current stack will be the arguments for the skolem functions
                let mut args = vec![];
                for (i, univ) in stack.iter().enumerate() {
                    args.push(AcornValue::Atom(TypedAtom {
                        atom: Atom::Variable(i as AtomId),
                        acorn_type: univ.clone(),
                    }));
                }

                // Find a replacement for each of the quantifiers.
                // Each one will be a skolem function applied to the current stack.
                let mut replacements = vec![];
                for quant in quants {
                    let skolem_type = AcornType::functional(stack.clone(), quant);
                    let skolem_index = self.skolem_types.len() as AtomId;
                    self.skolem_types.push(skolem_type.clone());
                    let function = AcornValue::Atom(TypedAtom {
                        atom: Atom::Skolem(skolem_index),
                        acorn_type: skolem_type,
                    });
                    let replacement = AcornValue::apply(function, args.clone());
                    replacements.push(replacement);
                }

                // Replace references to the existential quantifiers
                self.skolemize(
                    stack,
                    subvalue.bind_values(stack.len() as AtomId, &replacements),
                )
            }

            AcornValue::And(left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::And(Box::new(left), Box::new(right))
            }

            AcornValue::Or(left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::Or(Box::new(left), Box::new(right))
            }

            // Acceptable terminal nodes for the skolemization algorithm
            AcornValue::Atom(_) => value,
            AcornValue::Application(_) => value,
            AcornValue::Not(_) => value,
            AcornValue::Equals(_, _) => value,
            AcornValue::NotEquals(_, _) => value,

            _ => panic!(
                "moving negation inwards should have eliminated this node: {:?}",
                value
            ),
        }
    }

    pub fn normalize(&mut self, value: AcornValue) -> Vec<Clause> {
        // println!("value: {}", value);
        let expanded = value.expand_lambdas(0);
        // println!("expanded: {}", expanded);
        let neg_in = expanded.move_negation_inwards(false);
        println!("negin: {}", neg_in);
        let skolemized = self.skolemize(&vec![], neg_in);
        println!("skolemized: {}", skolemized);
        let mut universal = vec![];
        let dequantified = skolemized.remove_forall(&mut universal);
        // println!("universal: {}", AcornType::vec_to_str(&universal));
        let mut literal_lists = vec![];
        self.typespace.into_cnf(dequantified, &mut literal_lists);

        let mut clauses = vec![];
        for literals in literal_lists {
            assert!(literals.len() > 0);
            clauses.push(Clause::new(literals));
        }
        clauses
    }

    pub fn check(&mut self, env: &Environment, name: &str, expected: &[&str]) {
        let val = match env.get_value(name) {
            Some(val) => val,
            None => panic!("no value named {}", name),
        };
        let actual = self.normalize(val.clone());
        if actual.len() != expected.len() {
            panic!(
                "expected {} clauses, got {}:\n{}",
                expected.len(),
                actual.len(),
                actual
                    .iter()
                    .map(|c| format!("{}", c))
                    .collect::<Vec<String>>()
                    .join("\n")
            );
        }
        for i in 0..actual.len() {
            assert_eq!(format!("{}", actual[i]), expected[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nat_normalization() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("define 0: Nat = axiom");
        env.axiomcheck(0, "0");
        env.add("define Suc: Nat -> Nat = axiom");
        env.axiomcheck(1, "Suc");
        env.add("define 1: Nat = Suc(0)");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        norm.check(&env, "suc_injective", &["a1(x0) != a1(x1) | x0 = x1"]);

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        norm.check(&env, "suc_neq_zero", &["a1(x0) != a0"]);

        env.add(
            "axiom induction(f: Nat -> bool):\
            f(0) & forall(k: Nat, f(k) -> f(Suc(k))) -> forall(n: Nat, f(n))",
        );
        norm.check(
            &env,
            "induction",
            &[
                "!x0(a0) | x0(s0(x0)) | x0(x1)",
                "!x0(a1(s0(x0))) | !x0(a0) | x0(x1)",
            ],
        );

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.axiomcheck(2, "recursion");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        norm.check(&env, "recursion_base", &["a2(x0, x1, a0) = x1"]);

        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):\
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );
        norm.check(
            &env,
            "recursion_step",
            &["a2(x0, x1, a1(x2)) = x0(a2(x0, x1, x2))"],
        );
        env.add("define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)");
        env.add("theorem add_zero_right(a: Nat): add(a, 0) = a");
        norm.check(&env, "add_zero_right", &["a2(a1, x0, a0) = x0"]);
    }

    #[test]
    fn test_bool_formulas() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("theorem one(a: bool): a -> a | (a | a)");
        norm.check(&env, "one", &["!x0 | x0"]);

        env.add("theorem two(a: bool): a -> a & (a & a)");
        norm.check(&env, "two", &["!x0 | x0", "!x0 | x0", "!x0 | x0"]);
    }

    #[test]
    fn test_tautology_elimination() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem one(n: Nat): n = n");
        norm.check(&env, "one", &[]);

        env.add("theorem two(n: Nat): n = n | n != n");
        norm.check(&env, "two", &[]);
    }

    #[test]
    fn test_nested_skolemization() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem exists_eq(x : Nat): exists(y: Nat, x = y)");
        norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
    }

    #[test]
    fn test_skolemizing_without_args() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("define 0: Nat = axiom");
        env.add("theorem exists_zero: exists(x: Nat, x = 0)");
        norm.check(&env, "exists_zero", &["s0 = a0"]);
    }
}
