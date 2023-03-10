use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

impl FunctionApplication {
    pub fn return_type(&self) -> AcornType {
        match self.function.get_type() {
            AcornType::Function(FunctionType { return_type, .. }) => *return_type,
            _ => panic!("FunctionApplication's function is not a function type"),
        }
    }
}

// An atomic value is one that we don't want to expand inline.
// We could add more things here, like defined constants.
// For now, we expand everything we can inline.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Atom {
    // Values defined like "define 0: Nat = axiom"
    Axiomatic(usize),

    // Functions created in the normalization process
    Skolem(usize),

    // A Reference is a reference to a variable on the stack.
    // We drop the variable name. Instead we track the index on the stack of the binding.
    // This does mean that you must be careful when moving values between different stack environments.
    Reference(usize),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TypedAtom {
    pub atom: Atom,
    pub acorn_type: AcornType,
}

impl fmt::Display for TypedAtom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.atom {
            Atom::Axiomatic(i) => write!(f, "a{}", i),
            Atom::Skolem(i) => write!(f, "s{}", i),
            Atom::Reference(i) => write!(f, "x{}", i),
        }
    }
}

impl TypedAtom {
    // Binds this atom if it matches one of the new stack values.
    // They start at the provided stack index.
    // Since stack references are stored by height on the stack, this will also change the
    // reference id if this is a reference to a subsequent stack value.
    pub fn bind_values(self, stack_index: usize, values: &Vec<AcornValue>) -> AcornValue {
        match self.atom {
            Atom::Reference(i) => {
                if i < stack_index {
                    // This reference is unchanged
                    return AcornValue::Atom(self);
                }
                if i < stack_index + values.len() {
                    // This reference is bound to a new value
                    return values[i - stack_index].clone();
                }
                // This reference just needs to be shifted
                AcornValue::Atom(TypedAtom {
                    atom: Atom::Reference(i - values.len()),
                    acorn_type: self.acorn_type,
                })
            }
            _ => AcornValue::Atom(self),
        }
    }

    pub fn insert_stack(self, index: usize, increment: usize) -> AcornValue {
        match self.atom {
            Atom::Reference(i) => {
                if i < index {
                    // This reference is unchanged
                    return AcornValue::Atom(self);
                }
                // This reference just needs to be shifted
                AcornValue::Atom(TypedAtom {
                    atom: Atom::Reference(i + increment),
                    acorn_type: self.acorn_type,
                })
            }
            _ => AcornValue::Atom(self),
        }
    }
}

// Two AcornValue compare to equal if they are structurally identical.
// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    // An atomic value could be an axiom.
    // It could be a defined value that we don't want to expand inline.
    // It could be a function produced by skolemization.
    // Basically anything that isn't composed of smaller parts.
    Atom(TypedAtom),

    Application(FunctionApplication),
    ArgList(Vec<AcornValue>),

    // A function definition that introduces variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    // Some functions are hardcoded because we want to treat them specially during inference.
    Implies(Box<AcornValue>, Box<AcornValue>),
    Equals(Box<AcornValue>, Box<AcornValue>),
    NotEquals(Box<AcornValue>, Box<AcornValue>),
    And(Box<AcornValue>, Box<AcornValue>),
    Or(Box<AcornValue>, Box<AcornValue>),
    Not(Box<AcornValue>),

    // Quantifiers that introduce variables onto the stack.
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),

    // The unbound macros themselves
    ForAllMacro,
    ExistsMacro,
}

impl AcornValue {
    pub fn into_vec(self) -> Vec<AcornValue> {
        match self {
            AcornValue::ArgList(t) => t,
            _ => vec![self],
        }
    }

    pub fn axiom_index(&self) -> Option<usize> {
        match self {
            AcornValue::Atom(t) => match t.atom {
                Atom::Axiomatic(i) => Some(i),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Atom(t) => t.acorn_type.clone(),
            AcornValue::Application(t) => t.return_type(),
            AcornValue::ArgList(t) => {
                AcornType::ArgList(t.into_iter().map(|x| x.get_type()).collect())
            }
            AcornValue::Lambda(args, return_value) => AcornType::Function(FunctionType {
                arg_types: args.clone(),
                return_type: Box::new(return_value.get_type()),
            }),
            AcornValue::Implies(_, _) => AcornType::Bool,
            AcornValue::Equals(_, _) => AcornType::Bool,
            AcornValue::NotEquals(_, _) => AcornType::Bool,
            AcornValue::And(_, _) => AcornType::Bool,
            AcornValue::Or(_, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::ForAllMacro => AcornType::Macro,
            AcornValue::ExistsMacro => AcornType::Macro,
        }
    }

    // Simplifies at the top level but does not recurse.
    pub fn maybe_negate(self, negate: bool) -> AcornValue {
        if !negate {
            return self;
        }
        match self {
            AcornValue::Not(x) => *x,
            AcornValue::Equals(x, y) => AcornValue::NotEquals(x, y),
            AcornValue::NotEquals(x, y) => AcornValue::Equals(x, y),
            _ => AcornValue::Not(Box::new(self)),
        }
    }

    // Normalizes a boolean expression by moving all negations inwards.
    // If 'negate' is set then we also negate this expression.
    // See https://www.csd.uwo.ca/~lkari/prenex.pdf
    // page 3, steps 1 and 2.
    pub fn move_negation_inwards(self, negate: bool) -> AcornValue {
        match self {
            AcornValue::Implies(left, right) => {
                // (left -> right) is equivalent to (!left | right)
                let equivalent = AcornValue::Or(Box::new(AcornValue::Not(left)), right);
                equivalent.move_negation_inwards(negate)
            }
            AcornValue::And(left, right) => {
                if negate {
                    // !(left & right) is equivalent to (!left | !right)
                    let equivalent = AcornValue::Or(
                        Box::new(AcornValue::Not(left)),
                        Box::new(AcornValue::Not(right)),
                    );
                    equivalent.move_negation_inwards(false)
                } else {
                    AcornValue::And(
                        Box::new(left.move_negation_inwards(false)),
                        Box::new(right.move_negation_inwards(false)),
                    )
                }
            }
            AcornValue::Or(left, right) => {
                if negate {
                    // !(left | right) is equivalent to (!left & !right)
                    let equivalent = AcornValue::And(
                        Box::new(AcornValue::Not(left)),
                        Box::new(AcornValue::Not(right)),
                    );
                    equivalent.move_negation_inwards(false)
                } else {
                    AcornValue::Or(
                        Box::new(left.move_negation_inwards(false)),
                        Box::new(right.move_negation_inwards(false)),
                    )
                }
            }
            AcornValue::Not(x) => x.move_negation_inwards(!negate),
            AcornValue::ForAll(quants, value) => {
                if negate {
                    // "not forall x, foo(x)" is equivalent to "exists x, not foo(x)"
                    AcornValue::Exists(quants, Box::new(value.move_negation_inwards(true)))
                } else {
                    AcornValue::ForAll(quants, Box::new(value.move_negation_inwards(false)))
                }
            }
            AcornValue::Exists(quants, value) => {
                if negate {
                    // "not exists x, foo(x)" is equivalent to "forall x, not foo(x)"
                    AcornValue::ForAll(quants, Box::new(value.move_negation_inwards(true)))
                } else {
                    AcornValue::Exists(quants, Box::new(value.move_negation_inwards(false)))
                }
            }
            _ => self.maybe_negate(negate),
        }
    }

    // Binds the provided values to stack variables, starting at the provided stack index.
    // Since stack references are stored by height on the stack, this will also change the
    // references for any subsequent stack variables.
    pub fn bind_values(self, stack_index: usize, values: &Vec<AcornValue>) -> AcornValue {
        match self {
            AcornValue::Atom(a) => a.bind_values(stack_index, values),
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.bind_values(stack_index, values)),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.bind_values(stack_index, values))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => AcornValue::Lambda(
                args,
                Box::new(return_value.bind_values(stack_index, values)),
            ),
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.bind_values(stack_index, values)),
                Box::new(right.bind_values(stack_index, values)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.bind_values(stack_index, values)),
                Box::new(right.bind_values(stack_index, values)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.bind_values(stack_index, values)),
                Box::new(right.bind_values(stack_index, values)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.bind_values(stack_index, values)),
                Box::new(right.bind_values(stack_index, values)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.bind_values(stack_index, values)),
                Box::new(right.bind_values(stack_index, values)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.bind_values(stack_index, values))),
            AcornValue::ForAll(quants, value) => {
                AcornValue::ForAll(quants, Box::new(value.bind_values(stack_index, values)))
            }
            AcornValue::Exists(quants, value) => {
                AcornValue::Exists(quants, Box::new(value.bind_values(stack_index, values)))
            }
            _ => panic!("unhandled case in bind_values: {:?}", self),
        }
    }

    // Inserts 'increment' stack entries, starting with the provided index, that this value
    // doesn't use.
    // Every reference at index or higher should be incremented by increment.
    pub fn insert_stack(self, index: usize, increment: usize) -> AcornValue {
        match self {
            AcornValue::Atom(a) => a.insert_stack(index, increment),
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.insert_stack(index, increment)),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.insert_stack(index, increment))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => {
                AcornValue::Lambda(args, Box::new(return_value.insert_stack(index, increment)))
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.insert_stack(index, increment)),
                Box::new(right.insert_stack(index, increment)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.insert_stack(index, increment))),
            AcornValue::ForAll(quants, value) => {
                AcornValue::ForAll(quants, Box::new(value.insert_stack(index, increment)))
            }
            AcornValue::Exists(quants, value) => {
                AcornValue::Exists(quants, Box::new(value.insert_stack(index, increment)))
            }
            _ => panic!("unhandled case in insert_stack: {:?}", self),
        }
    }

    // stack_size is the number of variables that are already on the stack.
    pub fn expand_lambdas(self, stack_size: usize) -> AcornValue {
        match self {
            AcornValue::Application(app) => {
                if let AcornValue::Lambda(_, return_value) = *app.function {
                    // Expand the lambda
                    let expanded = return_value.bind_values(stack_size, &app.args);
                    expanded.expand_lambdas(stack_size)
                } else {
                    AcornValue::Application(FunctionApplication {
                        function: app.function,
                        args: app
                            .args
                            .into_iter()
                            .map(|x| x.expand_lambdas(stack_size))
                            .collect(),
                    })
                }
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.expand_lambdas(stack_size)),
                Box::new(right.expand_lambdas(stack_size)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.expand_lambdas(stack_size))),
            AcornValue::ForAll(quants, value) => {
                let new_stack_size = stack_size + quants.len();
                AcornValue::ForAll(quants, Box::new(value.expand_lambdas(new_stack_size)))
            }
            AcornValue::Exists(quants, value) => {
                let new_stack_size = stack_size + quants.len();
                AcornValue::Exists(quants, Box::new(value.expand_lambdas(new_stack_size)))
            }
            _ => self,
        }
    }

    // Removes all "forall" nodes, collecting the quantified types into quantifiers.
    pub fn remove_forall(self, quantifiers: &mut Vec<AcornType>) -> AcornValue {
        match self {
            AcornValue::And(left, right) => {
                let original_num_quants = quantifiers.len();
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() - original_num_quants;

                let shifted_right = right.insert_stack(original_num_quants, added_quants);
                let new_right = shifted_right.remove_forall(quantifiers);
                AcornValue::And(Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Or(left, right) => {
                let original_num_quants = quantifiers.len();
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() - original_num_quants;

                let shifted_right = right.insert_stack(original_num_quants, added_quants);
                let new_right = shifted_right.remove_forall(quantifiers);
                AcornValue::Or(Box::new(new_left), Box::new(new_right))
            }
            AcornValue::ForAll(new_quants, value) => {
                quantifiers.extend(new_quants);
                value.remove_forall(quantifiers)
            }
            _ => self,
        }
    }
}

// If args is not empty, then atom should be treated as a function.
// Otherwise, the term is just the atom.
// This is more general than typical first-order logic terms, because the
// function can be quantified.
#[derive(Clone, Debug)]
pub struct Term {
    pub atom: TypedAtom,
    pub args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.atom)
        } else {
            write!(f, "{}(", self.atom)?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")
        }
    }
}

impl Term {
    pub fn from_atom(atom: TypedAtom) -> Term {
        Term {
            atom,
            args: Vec::new(),
        }
    }

    pub fn from_application(app: FunctionApplication) -> Term {
        let atom = match *app.function {
            AcornValue::Atom(atom) => atom,
            _ => panic!("cannot convert {:?} to a term", app.function),
        };
        Term {
            atom: atom,
            args: app.args.into_iter().map(|x| Term::from_value(x)).collect(),
        }
    }

    // Panics if this value cannot be converted to a term.
    pub fn from_value(value: AcornValue) -> Term {
        match value {
            AcornValue::Atom(atom) => Term::from_atom(atom),
            AcornValue::Application(app) => Term::from_application(app),
            _ => panic!("cannot convert {:?} to a term", value),
        }
    }
}

// Literals are always boolean-valued.
#[derive(Clone, Debug)]
pub enum Literal {
    Positive(Term),
    Negative(Term),
    Equals(Term, Term),
    NotEquals(Term, Term),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Positive(term) => write!(f, "{}", term),
            Literal::Negative(term) => write!(f, "!{}", term),
            Literal::Equals(left, right) => write!(f, "{} = {}", left, right),
            Literal::NotEquals(left, right) => write!(f, "{} != {}", left, right),
        }
    }
}

impl Literal {
    // Panics if this value cannot be converted to a literal.
    pub fn from_value(value: AcornValue) -> Literal {
        match value {
            AcornValue::Atom(atom) => Literal::Positive(Term::from_atom(atom)),
            AcornValue::Application(app) => Literal::Positive(Term::from_application(app)),
            AcornValue::Equals(left, right) => {
                Literal::Equals(Term::from_value(*left), Term::from_value(*right))
            }
            AcornValue::NotEquals(left, right) => {
                Literal::NotEquals(Term::from_value(*left), Term::from_value(*right))
            }
            AcornValue::Not(subvalue) => Literal::Negative(Term::from_value(*subvalue)),
            _ => panic!("cannot convert {:?} to a literal", value),
        }
    }

    // Everything below "and" and "or" nodes must be literals.
    // Appends all results found.
    pub fn into_cnf(value: AcornValue, results: &mut Vec<Vec<Literal>>) {
        match value {
            AcornValue::And(left, right) => {
                Literal::into_cnf(*left, results);
                Literal::into_cnf(*right, results);
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                Literal::into_cnf(*left, &mut left_results);
                let mut right_results = Vec::new();
                Literal::into_cnf(*right, &mut right_results);
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
            }
            _ => {
                results.push(vec![Literal::from_value(value)]);
            }
        }
    }
}

// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
#[derive(Debug)]
pub struct Clause {
    pub universal: Vec<AcornType>,
    pub literals: Vec<Literal>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.universal.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}", literal)?;
        }
        Ok(())
    }
}
