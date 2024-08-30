use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::constant_map::ConstantMap;
use crate::display::DisplayClause;
use crate::environment::Environment;
use crate::literal::Literal;
use crate::module::SKOLEM;
use crate::term::Term;
use crate::type_map::{TypeId, TypeMap};

#[derive(Debug)]
pub struct NormalizationError(pub String);
type Result<T> = std::result::Result<T, NormalizationError>;

#[derive(Debug)]
pub enum Normalization {
    // A successfully normalized value turns into a bunch of clauses.
    // Logically, this is an "and of ors". Each Clause is an "or" of its literals.
    // An empty list indicates a proposition that is always trivially satisfied.
    Clauses(Vec<Clause>),

    // Sometimes as we normalize we discover a proposition that is impossible to satisfy.
    // This can't be trivially represented in CNF, so it gets its own variant.
    Impossible,

    // A user-visible error.
    Error(String),
}

impl Normalization {
    pub fn expect_clauses(self) -> Vec<Clause> {
        match self {
            Normalization::Clauses(clauses) => clauses,
            _ => panic!("expected clauses but got: {:?}", self),
        }
    }

    fn and(self, other: Normalization) -> Normalization {
        match self {
            Normalization::Clauses(mut clauses) => match other {
                Normalization::Clauses(mut other_clauses) => {
                    clauses.append(&mut other_clauses);
                    Normalization::Clauses(clauses)
                }
                Normalization::Impossible => Normalization::Impossible,
                Normalization::Error(s) => Normalization::Error(s),
            },
            Normalization::Impossible => Normalization::Impossible,
            Normalization::Error(s) => Normalization::Error(s),
        }
    }

    pub fn clauses(&self) -> Vec<&Clause> {
        match self {
            Normalization::Clauses(clauses) => clauses.iter().collect(),
            _ => vec![],
        }
    }
}

#[derive(Clone)]
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
        // Hacky. Turn the int into an s-name
        let name = format!("s{}", skolem_index);
        AcornValue::Constant(SKOLEM, name, acorn_type, vec![])
    }

    pub fn is_skolem(&self, atom: &Atom) -> bool {
        matches!(atom, Atom::Skolem(_))
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
                    let skolem_type = AcornType::new_functional(stack.clone(), quant);
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
    fn term_from_application(
        &mut self,
        application: &FunctionApplication,
        local: bool,
    ) -> Result<Term> {
        let term_type = self.type_map.add_type(&application.get_type());
        let func_term = self.term_from_value(&application.function, local)?;
        let head = func_term.head;
        let head_type = func_term.head_type;
        let mut args = func_term.args;
        for arg in &application.args {
            args.push(self.term_from_value(arg, local)?);
        }
        Ok(Term::new(term_type, head_type, head, args))
    }

    // Constructs a new term from an AcornValue
    // Returns an error if it's inconvertible.
    // The "local" flag here and elsewhere controls whether any newly discovered variables
    // are local variables.
    pub fn term_from_value(&mut self, value: &AcornValue, local: bool) -> Result<Term> {
        match value {
            AcornValue::Variable(i, var_type) => {
                let type_id = self.type_map.add_type(var_type);
                Ok(Term::new(type_id, type_id, Atom::Variable(*i), vec![]))
            }
            AcornValue::Constant(module, name, t, params) => {
                assert!(params.is_empty());
                let type_id = self.type_map.add_type(t);
                let constant_atom = if *module == SKOLEM {
                    // Hacky. Turn the s-name back to an int
                    Atom::Skolem(name[1..].parse().unwrap())
                } else {
                    self.constant_map.add_constant(*module, name, local)
                };
                Ok(Term::new(type_id, type_id, constant_atom, vec![]))
            }
            AcornValue::Application(application) => {
                Ok(self.term_from_application(application, local)?)
            }
            AcornValue::Specialized(module, name, _, parameters) => Ok(self
                .type_map
                .term_from_monomorph(*module, name, parameters, value.get_type())),
            AcornValue::Bool(true) => Ok(Term::new_true()),
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
    fn literal_from_value(&mut self, value: &AcornValue, local: bool) -> Result<Literal> {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Constant(_, _, _, _) => {
                Ok(Literal::positive(self.term_from_value(value, local)?))
            }
            AcornValue::Application(app) => {
                Ok(Literal::positive(self.term_from_application(app, local)?))
            }
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                let left_term = self.term_from_value(&*left, local)?;
                let right_term = self.term_from_value(&*right, local)?;
                Ok(Literal::equals(left_term, right_term))
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                let left_term = self.term_from_value(&*left, local)?;
                let right_term = self.term_from_value(&*right, local)?;
                Ok(Literal::not_equals(left_term, right_term))
            }
            AcornValue::Not(subvalue) => {
                Ok(Literal::negative(self.term_from_value(subvalue, local)?))
            }
            _ => Err(NormalizationError(format!(
                "Cannot convert {} to literal",
                value
            ))),
        }
    }

    // Converts a value that is already in CNF into lists of literals.
    // Each Vec<Literal> is a conjunction, an "or" node.
    // The CNF form is expressing that each of these conjunctions are true.
    // Returns Ok(Some(cnf)) if it can be turned into CNF.
    // Returns Ok(None) if it's an impossibility.
    // Returns an error if we failed in some user-reportable way.
    fn into_literal_lists(
        &mut self,
        value: &AcornValue,
        local: bool,
    ) -> Result<Option<Vec<Vec<Literal>>>> {
        match value {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let mut left = match self.into_literal_lists(left, local)? {
                    Some(left) => left,
                    None => return Ok(None),
                };
                let right = match self.into_literal_lists(right, local)? {
                    Some(right) => right,
                    None => return Ok(None),
                };
                left.extend(right);
                Ok(Some(left))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let left = self.into_literal_lists(left, local)?;
                let right = self.into_literal_lists(right, local)?;
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
                let literal = self.literal_from_value(&value, local)?;
                if literal.is_tautology() {
                    Ok(Some(vec![]))
                } else {
                    Ok(Some(vec![vec![literal]]))
                }
            }
        }
    }

    // Turns a value that is already in CNF into a Normalization
    fn normalize_cnf(&mut self, value: AcornValue, local: bool) -> Normalization {
        let mut universal = vec![];
        let value = value.remove_forall(&mut universal);
        match self.into_literal_lists(&value, local) {
            Ok(Some(lists)) => self.normalize_literal_lists(lists),
            Ok(None) => Normalization::Impossible,
            Err(NormalizationError(s)) => {
                // value is essentially a subvalue with the universal quantifiers removed,
                // so reconstruct it to display it nicely.
                let reconstructed = AcornValue::new_forall(universal, value);
                Normalization::Error(format!(
                    "\nerror converting {} to CNF:\n{}",
                    reconstructed, s
                ))
            }
        }
    }

    fn normalize_literal_lists(&self, literal_lists: Vec<Vec<Literal>>) -> Normalization {
        let mut clauses = vec![];
        for literals in literal_lists {
            assert!(literals.len() > 0);
            let clause = Clause::new(literals);
            // println!("clause: {}", clause);
            clauses.push(clause);
        }
        Normalization::Clauses(clauses)
    }

    // Converts a value to CNF, then to a Normalization.
    // Does not handle the "definition" sorts of values.
    fn convert_then_normalize(&mut self, value: &AcornValue, local: bool) -> Normalization {
        // println!("\nnormalizing: {}", value);
        let value = value.replace_function_equality(0);
        let value = value.expand_lambdas(0);
        let value = value.replace_if();
        let value = value.move_negation_inwards(true, false);
        // println!("negin'd: {}", value);
        let value = self.skolemize(&vec![], value);
        // println!("skolemized: {}", value);

        self.normalize_cnf(value, local)
    }

    // Converts a value to CNF.
    pub fn normalize(&mut self, value: &AcornValue, local: bool) -> Normalization {
        if let AcornValue::Binary(BinaryOp::Equals, left, right) = &value {
            // Check for defining one constant to equal another constant.
            if let AcornValue::Constant(left_module, left_name, _, _) = left.as_ref() {
                if let AcornValue::Constant(right_module, right_name, _, _) = right.as_ref() {
                    if self.constant_map.has_constant(*right_module, &right_name)
                        && !self.constant_map.has_constant(*left_module, &left_name)
                    {
                        // Yep, this is defining one constant to be another one.
                        // We can handle this in the constant map.
                        self.constant_map.add_alias(
                            *left_module,
                            &left_name,
                            *right_module,
                            &right_name,
                        );
                        return Normalization::Clauses(vec![]);
                    }
                }
            }

            // Check for the sort of functional equality that can be represented as a literal.
            if left.get_type().is_functional() && left.is_term() && right.is_term() {
                // We want to represent this two ways.
                // One as an equality between functions, another as an equality between
                // primitive types, after applying the functions.
                // If we handled functional types better in unification we might not need this.
                let functional = self.normalize_cnf(value.clone(), local);
                let primitive = self.convert_then_normalize(value, local);
                return functional.and(primitive);
            }
        }

        self.convert_then_normalize(value, local)
    }

    // Variables are left unbound. Their types are accumulated.
    fn denormalize_atom(
        &self,
        atom_type: TypeId,
        atom: &Atom,
        var_types: &mut Vec<AcornType>,
    ) -> AcornValue {
        let acorn_type = self.type_map.get_type(atom_type).clone();
        match atom {
            Atom::True => AcornValue::Bool(true),
            Atom::GlobalConstant(i) => {
                let (module, name) = self.constant_map.get_global_info(*i);
                AcornValue::Constant(module, name.to_string(), acorn_type, vec![])
            }
            Atom::LocalConstant(i) => {
                let (module, name) = self.constant_map.get_local_info(*i);
                AcornValue::Constant(module, name.to_string(), acorn_type, vec![])
            }
            Atom::Monomorph(i) => {
                let (module, name, params) = self.type_map.get_monomorph_info(*i);
                AcornValue::Specialized(module, name.to_string(), acorn_type, params.clone())
            }
            Atom::Variable(i) => {
                let index = *i as usize;
                if index < var_types.len() {
                    assert_eq!(var_types[index], acorn_type);
                } else if index == var_types.len() {
                    var_types.push(acorn_type.clone());
                } else {
                    panic!("variable index out of order");
                }
                AcornValue::Variable(*i, acorn_type)
            }
            Atom::Skolem(i) => {
                let acorn_type = self.skolem_types[*i as usize].clone();
                AcornValue::Constant(SKOLEM, format!("s{}", i), acorn_type, vec![])
            }
        }
    }

    fn denormalize_term(&self, term: &Term, var_types: &mut Vec<AcornType>) -> AcornValue {
        let head = self.denormalize_atom(term.head_type, &term.head, var_types);
        let args: Vec<_> = term
            .args
            .iter()
            .map(|t| self.denormalize_term(t, var_types))
            .collect();
        AcornValue::new_apply(head, args)
    }

    fn denormalize_literal(&self, literal: &Literal, var_types: &mut Vec<AcornType>) -> AcornValue {
        let left = self.denormalize_term(&literal.left, var_types);
        if literal.right.is_true() {
            if literal.positive {
                return left;
            } else {
                return AcornValue::Not(Box::new(left));
            }
        }
        let right = self.denormalize_term(&literal.right, var_types);
        if literal.positive {
            AcornValue::new_equals(left, right)
        } else {
            AcornValue::new_not_equals(left, right)
        }
    }

    // Converts backwards, from a clause to a value.
    // This will panic on a skolem.
    pub fn denormalize(&self, clause: &Clause) -> AcornValue {
        let mut var_types = vec![];
        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(literal, &mut var_types));
        }
        let mut answer = denormalized_literals.pop().unwrap();
        for subvalue in denormalized_literals.into_iter().rev() {
            answer = AcornValue::new_or(subvalue, answer);
        }
        AcornValue::new_forall(var_types, answer)
    }

    pub fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::GlobalConstant(i) => {
                let (_, name) = self.constant_map.get_global_info(*i);
                name.to_string()
            }
            Atom::LocalConstant(i) => {
                let (_, name) = self.constant_map.get_local_info(*i);
                name.to_string()
            }
            Atom::Monomorph(i) => {
                let (_, name, params) = self.type_map.get_monomorph_info(*i);
                let param_names: Vec<_> = params.iter().map(|(name, _)| name.clone()).collect();
                format!("{}<{}>", name, param_names.join(", "))
            }
            Atom::Variable(i) => format!("x{}", i),
            Atom::Skolem(i) => format!("s{}", i),
        }
    }

    // When you denormalize and renormalize a clause, you should get the same thing.
    fn check_denormalize_renormalize(&mut self, clause: &Clause) {
        let denormalized = self.denormalize(clause);
        denormalized
            .validate()
            .expect("denormalized clause should validate");
        let renormalized = self.normalize(&denormalized, true).expect_clauses();
        if renormalized.len() != 1 {
            println!("original clause: {}", clause);
            println!("denormalized: {}", denormalized);
            for (i, clause) in renormalized.iter().enumerate() {
                println!("renormalized[{}]: {}", i, clause);
            }
            panic!("expected 1 clause, got {}", renormalized.len());
        }
        assert_eq!(clause, &renormalized[0]);
    }

    fn check_value(&mut self, value: &AcornValue, expected: &[&str]) {
        let actual = self.normalize(value, true).expect_clauses();
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
            self.check_denormalize_renormalize(clause);
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
        self.check_value(&val, expected);
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
        env.add("let zero: Nat = axiom");
        env.expect_type("zero", "Nat");
        env.add("let suc: Nat -> Nat = axiom");
        env.expect_type("suc", "Nat -> Nat");
        env.add("let one: Nat = suc(zero)");
        env.expect_type("one", "Nat");

        env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) -> x = y }");
        norm.check(&env, "suc_injective", &["suc(x0) != suc(x1) or x0 = x1"]);
        env.expect_type("suc_injective", "(Nat, Nat) -> Bool");

        env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
        norm.check(&env, "suc_neq_zero", &["zero != suc(x0)"]);
        env.expect_type("suc_neq_zero", "Nat -> Bool");

        env.add(
            "axiom induction(f: Nat -> Bool) {\
            f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) } }",
        );

        norm.check(
            &env,
            "induction",
            &[
                "not x0(zero) or x0(s0(x0)) or x0(x1)",
                "not x0(suc(s0(x0))) or not x0(zero) or x0(x1)",
            ],
        );

        env.expect_type("induction", "Nat -> Bool -> Bool");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
        env.expect_type("recursion_base", "(Nat -> Nat, Nat) -> Bool");
        norm.check(&env, "recursion_base", &["recursion(x0, x1, zero) = x1"]);

        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {\
            recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
        );
        env.expect_type("recursion_step", "(Nat -> Nat, Nat, Nat) -> Bool");
        norm.check(
            &env,
            "recursion_step",
            &["recursion(x0, x1, suc(x2)) = x0(recursion(x0, x1, x2))"],
        );
    }

    #[test]
    fn test_bool_formulas() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("theorem one(a: Bool) { a -> a or (a or a) }");
        norm.check(&env, "one", &["not x0 or x0"]);

        env.add("theorem two(a: Bool) { a -> a and (a and a) }");
        norm.check(
            &env,
            "two",
            &["not x0 or x0", "not x0 or x0", "not x0 or x0"],
        );
    }

    #[test]
    fn test_tautology_elimination() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem one(n: Nat) { n = n }");
        norm.check(&env, "one", &[]);

        env.add("theorem two(n: Nat) { n = n or n != n }");
        norm.check(&env, "two", &[]);
    }

    #[test]
    fn test_nested_skolemization() {
        let mut env = Environment::new_test();
        let mut norm = Normalizer::new();
        env.add("type Nat: axiom");
        env.add("theorem exists_eq(x: Nat) { exists(y: Nat) { x = y } }");
        norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
    }

    #[test]
    fn test_second_order_binding() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let borf: (Nat, Nat, Nat) -> Bool = axiom
            define also_borf(a: Nat, b: Nat, c: Nat) -> Bool { borf(a, b, c) }
            let bb: Nat = axiom
            let cc: Nat = axiom
            define specific_borf(x: Nat) -> Bool { also_borf(x, bb, cc) }
            define always_true(f: Nat -> Bool) -> Bool { forall(n: Nat) { f(n) } }
            theorem goal { not always_true(specific_borf) }
        "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["not always_true(specific_borf)"]);
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
            theorem goal { (n0 = n1) = (n2 = n3) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &["n1 != n0 or n3 = n2", "n3 != n2 or n1 = n0"],
        );
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
            theorem goal { (n0 = n1) != (n2 = n3) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "goal",
            &["n3 != n2 or n1 != n0", "n3 = n2 or n1 = n0"],
        );
    }

    #[test]
    fn test_functions_returning_lambdas() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let addx: (Nat, Nat) -> Nat = axiom
            define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
            theorem goal(a: Nat, b: Nat) { adder(a)(b) = adder(b)(a) }
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
            let zero: Nat = axiom
            define zerof(a: Nat) -> (Nat -> Nat) { function(b: Nat) { zero } }
            theorem goal(a: Nat, b: Nat) { zerof(a) = zerof(b) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["zerof(x0, x1) = zerof(x2, x1)"]);
    }

    #[test]
    fn test_normalizing_exists() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem goal { exists(x: Nat) { addx(x, zero) = one } }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(&env, "goal", &["addx(s0, zero) = one"]);
    }

    #[test]
    fn test_denormalizing_disjunction() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            let one: Nat = axiom
            let ltx: (Nat, Nat) -> Bool = axiom
            let addx: (Nat, Nat) -> Nat = axiom
            theorem foo(x0: Nat, x1: Nat) { addx(addx(x0, zero), x1) != zero or ltx(x1, zero) }
            "#,
        );
        let mut norm = Normalizer::new();
        norm.check(
            &env,
            "foo",
            &["addx(addx(x0, zero), x1) != zero or ltx(x1, zero)"],
        );
    }
}
