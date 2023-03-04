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

    // A function definition that introduces a certain number of variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    // Some functions are hardcoded because we want to treat them specially during inference.
    Implies(Box<AcornValue>, Box<AcornValue>),
    Equals(Box<AcornValue>, Box<AcornValue>),
    NotEquals(Box<AcornValue>, Box<AcornValue>),
    And(Box<AcornValue>, Box<AcornValue>),
    Or(Box<AcornValue>, Box<AcornValue>),
    Not(Box<AcornValue>),
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
                args: args.clone(),
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

    // The stack size tracks how many variables are on the stack already, when converting this to a term.
    // TODO: don't panic on failure
    pub fn into_term(self, stack_size: usize) -> Term {
        match self {
            AcornValue::Atom(t) => Term {
                atom: t,
                args: vec![],
            },
            AcornValue::Application(app) => match *app.function {
                AcornValue::Atom(atom) => Term {
                    atom,
                    args: app
                        .args
                        .into_iter()
                        .map(|x| x.into_term(stack_size))
                        .collect(),
                },
                AcornValue::Lambda(args, return_value) => {
                    // I'm not sure if we need to typecheck here.
                    // Let's do it anyway.
                    for (lambda_arg_type, actual_arg_type) in
                        args.iter().zip(app.args.iter().map(|x| x.get_type()))
                    {
                        if lambda_arg_type != &actual_arg_type {
                            panic!(
                                "type mismatch in function application: expected {:?}, got {:?}",
                                lambda_arg_type, actual_arg_type
                            );
                        }
                    }

                    let expanded = return_value.bind_values(stack_size, &app.args);
                    // Note the stack size has not expanded, since we aren't putting these args
                    // on the stack, we're just inlining them.
                    expanded.into_term(stack_size)
                }
                _ => panic!("unable to expand function application: {:?}", app),
            },
            _ => panic!("expected a term, got {:?}", self),
        }
    }
}

// If args is not empty, then atom should be treated as a function.
// Otherwise, the term is just the atom.
pub struct Term {
    pub atom: TypedAtom,
    pub args: Vec<Term>,
}

// Literals are always boolean-valued.
pub enum Literal {
    Positive(Term),
    Negative(Term),
    Equals(Term, Term),
    NotEquals(Term, Term),
}

// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
pub struct Clause {
    pub universal: Vec<AcornType>,
    pub literals: Vec<Literal>,
}
