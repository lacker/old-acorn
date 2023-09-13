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
                let stack_size = stack.len() as AtomId;
                self.skolemize(
                    stack,
                    subvalue.bind_values(stack_size, stack_size, &replacements),
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

    pub fn normalize(&mut self, env: &Environment, value: AcornValue) -> Vec<Clause> {
        // println!("\nnormalizing: {}", env.value_str(&value));
        let replaced = value.replace_function_equality(0);
        // println!("\nreplaced: {}", env.value_str(&replaced));
        let expanded = replaced.expand_lambdas(0);
        // println!("\nexpanded: {}\n", env.value_str(&expanded));
        let neg_in = expanded.move_negation_inwards(false);
        // println!("negin: {}", neg_in);
        let skolemized = self.skolemize(&vec![], neg_in);
        // println!("skolemized: {}", skolemized);
        let mut universal = vec![];
        let dequantified = skolemized.remove_forall(&mut universal);
        // println!("universal: {}", AcornType::vec_to_str(&universal));
        let mut literal_lists = vec![];
        if let Err(e) = self.typespace.into_cnf(&dequantified, &mut literal_lists) {
            panic!(
                "\nerror converting {} to CNF:\n{}",
                env.value_str(&dequantified),
                e
            );
        }

        let mut clauses = vec![];
        for literals in literal_lists {
            assert!(literals.len() > 0);
            let clause = Clause::new(literals);
            // println!("clause: {}", clause);
            clauses.push(clause);
        }
        clauses
    }

    fn check_value(&mut self, env: &Environment, value: AcornValue, expected: &[&str]) {
        let actual = self.normalize(env, value);
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
            if actual[i].to_string() != expected[i] {
                panic!(
                    "expected clause {} to be:\n{}\ngot:\n{}",
                    i, expected[i], actual[i]
                );
            }
        }
    }

    // Checks a theorem
    pub fn check(&mut self, env: &Environment, name: &str, expected: &[&str]) {
        let val = match env.get_theorem_claim(name) {
            Some(val) => val,
            None => panic!("no value named {}", name),
        };
        self.check_value(env, val, expected);
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
        env.constantcheck(0, "0");
        env.add("define Suc: Nat -> Nat = axiom");
        env.constantcheck(1, "Suc");
        env.add("define 1: Nat = Suc(0)");
        env.constantcheck(2, "1");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        norm.check(&env, "suc_injective", &["c1(x0) != c1(x1) | x0 = x1"]);
        env.constantcheck(3, "suc_injective");

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        norm.check(&env, "suc_neq_zero", &["c1(x0) != c0"]);
        env.constantcheck(4, "suc_neq_zero");

        env.add(
            "axiom induction(f: Nat -> bool):\
            f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> forall(n: Nat) { f(n) }",
        );
        norm.check(
            &env,
            "induction",
            &[
                "!x0(c0) | x0(s0(x0)) | x0(x1)",
                "!x0(c1(s0(x0))) | !x0(c0) | x0(x1)",
            ],
        );
        env.constantcheck(5, "induction");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.constantcheck(6, "recursion");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.constantcheck(7, "recursion_base");
        norm.check(&env, "recursion_base", &["c6(x0, x1, c0) = x1"]);

        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):\
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );
        env.constantcheck(8, "recursion_step");
        norm.check(
            &env,
            "recursion_step",
            &["c6(x0, x1, c1(x2)) = x0(c6(x0, x1, x2))"],
        );
        env.add("define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)");
        env.constantcheck(9, "add");
        env.add("theorem add_zero_right(a: Nat): add(a, 0) = a");
        norm.check(&env, "add_zero_right", &["c6(c1, x0, c0) = x0"]);
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
        env.add("theorem exists_eq(x: Nat): exists(y: Nat) { x = y }");
        norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
    }

    #[test]
    fn test_skolemizing_without_args() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("define 0: Nat = axiom");
        env.add("theorem exists_zero: exists(x: Nat) { x = 0 }");
        norm.check(&env, "exists_zero", &["s0 = c0"]);
    }

    #[test]
    fn test_second_order_binding() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define borf: (Nat, Nat, Nat) -> bool = axiom
            define also_borf(a: Nat, b: Nat, c: Nat) -> bool = borf(a, b, c)
            define bb: Nat = axiom
            define cc: Nat = axiom
            define specific_borf(x: Nat) -> bool = also_borf(x, bb, cc)
            define always_true(f: Nat -> bool) -> bool = forall(n: Nat) { f(n) }
            theorem goal: !always_true(specific_borf)
        "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["!c0(s0, c2, c3)"]);
    }

    #[test]
    fn test_boolean_equality() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define n0: Nat = axiom
            define n1: Nat = axiom
            define n2: Nat = axiom
            define n3: Nat = axiom
            theorem goal: (n0 = n1) = (n2 = n3)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["c1 != c0 | c3 = c2", "c3 != c2 | c1 = c0"]);
    }

    #[test]
    fn test_boolean_inequality() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define n0: Nat = axiom
            define n1: Nat = axiom
            define n2: Nat = axiom
            define n3: Nat = axiom
            theorem goal: (n0 = n1) != (n2 = n3)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["c3 != c2 | c1 != c0", "c3 = c2 | c1 = c0"]);
    }

    #[test]
    fn test_functions_returning_lambdas() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define add: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) = function(b: Nat) { add(a, b) }
            theorem goal(a: Nat, b: Nat): adder(a)(b) = adder(b)(a)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["c0(x0, x1) = c0(x1, x0)"]);
    }

    #[test]
    fn test_functional_equality() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define 0: Nat = axiom
            define zerof(a: Nat) -> (Nat -> Nat) = function(b: Nat) { 0 }
            theorem goal(a: Nat, b: Nat): zerof(a) = zerof(b)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &[]);
    }
}
