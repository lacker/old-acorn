use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::constant_map::ConstantMap;
use crate::display::DisplayClause;
use crate::environment::Environment;
use crate::literal::Literal;
use crate::namespace::SKOLEM;
use crate::term::Term;
use crate::type_map::TypeMap;

// A failure during normalization.
pub struct NormalizationError(pub String);

impl fmt::Display for NormalizationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NormalizationError(msg) => write!(f, "Normalization error: {}", msg),
        }
    }
}

pub type Result<T> = std::result::Result<T, NormalizationError>;

pub struct Normalizer {
    // Types of the skolem functions produced
    // Some of them are just constants, so we store an AcornType rather than a FunctionType
    skolem_types: Vec<AcornType>,

    pub type_map: TypeMap,

    constant_map: ConstantMap,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Normalizer {
            skolem_types: vec![],
            type_map: TypeMap::new(),
            constant_map: ConstantMap::new(),
        }
    }

    fn new_skolem_value(&mut self, acorn_type: AcornType) -> AcornValue {
        let skolem_index = self.skolem_types.len() as AtomId;
        self.skolem_types.push(acorn_type.clone());
        let name = format!("s{}", skolem_index);
        AcornValue::Constant(SKOLEM, name, acorn_type, vec![])
    }

    pub fn is_skolem(&self, atom: &Atom) -> bool {
        if let Atom::Constant(id) = atom {
            let (namespace, _) = self.constant_map.get_info(*id);
            namespace == SKOLEM
        } else {
            false
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
                    args.push(AcornValue::Variable(i as AtomId, univ.clone()));
                }

                // Find a replacement for each of the quantifiers.
                // Each one will be a skolem function applied to the current stack.
                let mut replacements = vec![];
                for quant in quants {
                    let skolem_type = AcornType::functional(stack.clone(), quant);
                    let skolem_fn = self.new_skolem_value(skolem_type);
                    let replacement = AcornValue::new_apply(skolem_fn, args.clone());
                    replacements.push(replacement);
                }

                // Replace references to the existential quantifiers
                let stack_size = stack.len() as AtomId;
                self.skolemize(
                    stack,
                    subvalue.bind_values(stack_size, stack_size, &replacements),
                )
            }

            AcornValue::Binary(BinaryOp::And, left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::Binary(BinaryOp::And, Box::new(left), Box::new(right))
            }

            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left = self.skolemize(stack, *left);
                let right = self.skolemize(stack, *right);
                AcornValue::Binary(BinaryOp::Or, Box::new(left), Box::new(right))
            }

            // Acceptable terminal nodes for the skolemization algorithm
            AcornValue::Application(_)
            | AcornValue::Not(_)
            | AcornValue::Binary(_, _, _)
            | AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Bool(_) => value,

            _ => panic!(
                "moving negation inwards should have eliminated this node: {:?}",
                value
            ),
        }
    }

    // Constructs a new term from a function application
    // Function applications that are nested like f(x)(y) are flattened to f(x, y)
    fn term_from_application(&mut self, application: &FunctionApplication) -> Result<Term> {
        let term_type = self.type_map.add_type(&application.return_type());
        let func_term = self.term_from_value(&application.function)?;
        let head = func_term.head;
        let head_type = func_term.head_type;
        let mut args = func_term.args;
        for arg in &application.args {
            args.push(self.term_from_value(arg)?);
        }
        Ok(Term::new(term_type, head_type, head, args))
    }

    // Constructs a new term from an AcornValue
    // Returns an error if it's inconvertible
    fn term_from_value(&mut self, value: &AcornValue) -> Result<Term> {
        match value {
            AcornValue::Variable(i, var_type) => {
                let type_id = self.type_map.add_type(var_type);
                Ok(Term {
                    term_type: type_id,
                    head_type: type_id,
                    head: Atom::Variable(*i),
                    args: vec![],
                })
            }
            AcornValue::Constant(namespace, name, t, params) => {
                assert!(params.is_empty());
                let type_id = self.type_map.add_type(t);
                let c_id = self.constant_map.add_constant(*namespace, name);
                Ok(Term {
                    term_type: type_id,
                    head_type: type_id,
                    head: Atom::Constant(c_id),
                    args: vec![],
                })
            }
            AcornValue::Application(application) => Ok(self.term_from_application(application)?),
            AcornValue::Specialized(namespace, name, _, parameters) => Ok(self
                .type_map
                .term_from_monomorph(*namespace, name, parameters, value.get_type())),
            _ => Err(NormalizationError(format!(
                "Cannot convert {} to term",
                value
            ))),
        }
    }
    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    // Normalizes literals to <larger> = <smaller>, because that's the logical direction
    // to do rewrite-type lookups, on the larger literal first.
    fn literal_from_value(&mut self, value: &AcornValue) -> Result<Literal> {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Constant(_, _, _, _) => {
                Ok(Literal::positive(self.term_from_value(value)?))
            }
            AcornValue::Application(app) => Ok(Literal::positive(self.term_from_application(app)?)),
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                let left_term = self.term_from_value(&*left)?;
                let right_term = self.term_from_value(&*right)?;
                Ok(Literal::equals(left_term, right_term))
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                let left_term = self.term_from_value(&*left)?;
                let right_term = self.term_from_value(&*right)?;
                Ok(Literal::not_equals(left_term, right_term))
            }
            AcornValue::Not(subvalue) => Ok(Literal::negative(self.term_from_value(subvalue)?)),
            _ => Err(NormalizationError(format!(
                "Cannot convert {} to literal",
                value
            ))),
        }
    }

    // Converts a value to Clausal Normal Form, output in results.
    // Each Vec<Literal> is a conjunction, an "or" node.
    // The CNF form is expressing that each of these conjunctions are true.
    // Returns Ok(Some(cnf)) if it can be turned into CNF.
    // Returns Ok(None) if it's an impossibility.
    // Returns an error if we failed in some user-reportable way.
    fn into_cnf(&mut self, value: &AcornValue) -> Result<Option<Vec<Vec<Literal>>>> {
        match value {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let mut left = match self.into_cnf(left)? {
                    Some(left) => left,
                    None => return Ok(None),
                };
                let right = match self.into_cnf(right)? {
                    Some(right) => right,
                    None => return Ok(None),
                };
                left.extend(right);
                Ok(Some(left))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left = self.into_cnf(left)?;
                let right = self.into_cnf(right)?;
                match (left, right) {
                    (None, None) => Ok(None),
                    (Some(result), None) | (None, Some(result)) => Ok(Some(result)),
                    (Some(left), Some(right)) => {
                        let mut results = vec![];
                        for left_result in &left {
                            for right_result in &right {
                                let mut combined = left_result.clone();
                                combined.extend(right_result.clone());
                                results.push(combined);
                            }
                        }
                        Ok(Some(results))
                    }
                }
            }
            AcornValue::Bool(true) => Ok(Some(vec![])),
            AcornValue::Bool(false) => Ok(None),
            _ => {
                let literal = self.literal_from_value(&value)?;
                if literal.is_tautology() {
                    Ok(Some(vec![]))
                } else {
                    Ok(Some(vec![vec![literal]]))
                }
            }
        }
    }

    // Converts a value to CNF. If value is true, then all the returned clauses are true.
    // If the value is always satisfied, like explicit "true", returns an empty list.
    // If the value is impossible to satify, like explicit "false", returns None.
    pub fn normalize(&mut self, value: AcornValue) -> Option<Vec<Clause>> {
        // println!("\nnormalizing: {}", value);
        let value = value.replace_function_equality(0);
        let value = value.expand_lambdas(0);
        let value = value.replace_if();
        let value = value.move_negation_inwards(false);
        // println!("negin'd: {}", value);
        let value = self.skolemize(&vec![], value);
        // println!("skolemized: {}", value);
        let mut universal = vec![];
        let value = value.remove_forall(&mut universal);
        let literal_lists = match self.into_cnf(&value) {
            Ok(Some(lists)) => lists,
            Ok(None) => return None,
            Err(e) => panic!("\nerror converting {} to CNF:\n{}", value, e),
        };

        let mut clauses = vec![];
        for literals in literal_lists {
            assert!(literals.len() > 0);
            let clause = Clause::new(literals);
            // println!("clause: {}", clause);
            clauses.push(clause);
        }
        Some(clauses)
    }

    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::Constant(i) => {
                let (_, name) = self.constant_map.get_info(*i);
                name.to_string()
            }
            Atom::Monomorph(i) => {
                let (_, name, params) = self.type_map.get_monomorph_info(*i);
                let param_names: Vec<_> = params.iter().map(|(name, _)| name.clone()).collect();
                format!("{}<{}>", name, param_names.join(", "))
            }
            Atom::Synthetic(i) => format!("p{}", i),
            Atom::Variable(i) => format!("x{}", i),
        }
    }

    fn check_value(&mut self, value: AcornValue, expected: &[&str]) {
        let actual = self.normalize(value).unwrap();
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
        for (i, clause) in actual.iter().enumerate() {
            let c = DisplayClause {
                clause,
                normalizer: self,
            };
            let a = c.to_string();
            if a != expected[i] {
                panic!("expected clause {} to be:\n{}\ngot:\n{}", i, expected[i], a);
            }
        }
    }

    // Checks a theorem
    pub fn check(&mut self, env: &Environment, name: &str, expected: &[&str]) {
        let val = match env.get_theorem_claim(name) {
            Some(val) => val,
            None => panic!("no value named {}", name),
        };
        self.check_value(val, expected);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nat_normalization() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.expect_type("0", "Nat");
        env.add("let Suc: Nat -> Nat = axiom");
        env.expect_type("Suc", "Nat -> Nat");
        env.add("let 1: Nat = Suc(0)");
        env.expect_type("1", "Nat");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        norm.check(&env, "suc_injective", &["Suc(x0) != Suc(x1) | x0 = x1"]);
        env.expect_type("suc_injective", "(Nat, Nat) -> bool");

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        norm.check(&env, "suc_neq_zero", &["0 != Suc(x0)"]);
        env.expect_type("suc_neq_zero", "Nat -> bool");

        env.add(
            "axiom induction(f: Nat -> bool):\
            f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> forall(n: Nat) { f(n) }",
        );
        norm.check(
            &env,
            "induction",
            &[
                "!x0(0) | x0(s0(x0)) | x0(x1)",
                "!x0(Suc(s0(x0))) | !x0(0) | x0(x1)",
            ],
        );
        env.expect_type("induction", "Nat -> bool -> bool");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.expect_type("recursion_base", "(Nat -> Nat, Nat) -> bool");
        norm.check(&env, "recursion_base", &["recursion(x0, x1, 0) = x1"]);

        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):\
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );
        env.expect_type("recursion_step", "(Nat -> Nat, Nat, Nat) -> bool");
        norm.check(
            &env,
            "recursion_step",
            &["recursion(x0, x1, Suc(x2)) = x0(recursion(x0, x1, x2))"],
        );
    }

    #[test]
    fn test_bool_formulas() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("theorem one(a: bool): a -> a | (a | a)");
        norm.check(&env, "one", &["!x0 | x0"]);

        env.add("theorem two(a: bool): a -> a & (a & a)");
        norm.check(&env, "two", &["!x0 | x0", "!x0 | x0", "!x0 | x0"]);
    }

    #[test]
    fn test_tautology_elimination() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem one(n: Nat): n = n");
        norm.check(&env, "one", &[]);

        env.add("theorem two(n: Nat): n = n | n != n");
        norm.check(&env, "two", &[]);
    }

    #[test]
    fn test_nested_skolemization() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem exists_eq(x: Nat): exists(y: Nat) { x = y }");
        norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
    }

    #[test]
    fn test_skolemizing_without_args() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("theorem exists_zero: exists(x: Nat) { x = 0 }");
        norm.check(&env, "exists_zero", &["0 = s0"]);
    }

    #[test]
    fn test_second_order_binding() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let borf: (Nat, Nat, Nat) -> bool = axiom
            define also_borf(a: Nat, b: Nat, c: Nat) -> bool = borf(a, b, c)
            let bb: Nat = axiom
            let cc: Nat = axiom
            define specific_borf(x: Nat) -> bool = also_borf(x, bb, cc)
            define always_true(f: Nat -> bool) -> bool = forall(n: Nat) { f(n) }
            theorem goal: !always_true(specific_borf)
        "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["!always_true(specific_borf)"]);
    }

    #[test]
    fn test_boolean_equality() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let n0: Nat = axiom
            let n1: Nat = axiom
            let n2: Nat = axiom
            let n3: Nat = axiom
            theorem goal: (n0 = n1) = (n2 = n3)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["n1 != n0 | n3 = n2", "n3 != n2 | n1 = n0"]);
    }

    #[test]
    fn test_boolean_inequality() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let n0: Nat = axiom
            let n1: Nat = axiom
            let n2: Nat = axiom
            let n3: Nat = axiom
            theorem goal: (n0 = n1) != (n2 = n3)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["n3 != n2 | n1 != n0", "n3 = n2 | n1 = n0"]);
    }

    #[test]
    fn test_functions_returning_lambdas() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let add: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) = function(b: Nat) { add(a, b) }
            theorem goal(a: Nat, b: Nat): adder(a)(b) = adder(b)(a)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["adder(x0, x1) = adder(x1, x0)"]);
    }

    #[test]
    fn test_functional_equality() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            define zerof(a: Nat) -> (Nat -> Nat) = function(b: Nat) { 0 }
            theorem goal(a: Nat, b: Nat): zerof(a) = zerof(b)
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["zerof(x0, x1) = zerof(x2, x1)"]);
    }
}
