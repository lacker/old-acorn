use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};
use crate::atom::{Atom, AtomId, TypedAtom};

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

    fn fmt_helper(&self, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
        self.function.fmt_helper(f, stack_size)?;
        write!(f, "(")?;
        fmt_values(&self.args, f, stack_size)?;
        write!(f, ")")
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

impl fmt::Display for AcornValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_helper(f, 0)
    }
}

fn fmt_values(v: &Vec<AcornValue>, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
    for (i, item) in v.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        item.fmt_helper(f, stack_size)?;
    }
    Ok(())
}

fn fmt_macro(
    f: &mut fmt::Formatter,
    name: &str,
    decs: &Vec<AcornType>,
    body: &AcornValue,
    stack_size: usize,
) -> fmt::Result {
    write!(f, "{}({}, ", name, AcornType::decs_to_str(decs, stack_size))?;
    body.fmt_helper(f, stack_size + decs.len())?;
    write!(f, ")")
}

fn fmt_binary(
    f: &mut fmt::Formatter,
    op: &str,
    left: &AcornValue,
    right: &AcornValue,
    stack_size: usize,
) -> fmt::Result {
    write!(f, "(")?;
    left.fmt_helper(f, stack_size)?;
    write!(f, " {} ", op)?;
    right.fmt_helper(f, stack_size)?;
    write!(f, ")")
}

// An AcornValue has an implicit stack size that determines what index new stack variables
// will have.
// The Subvalue includes this implicit stack size.
// The stack size of a "root" AcornValue is always zero.
struct Subvalue<'a> {
    value: &'a AcornValue,
    stack_size: usize,
}

impl fmt::Display for Subvalue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt_helper(f, self.stack_size)
    }
}

impl AcornValue {
    fn fmt_helper(&self, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
        match self {
            AcornValue::Atom(a) => write!(f, "{}", a),
            AcornValue::Application(a) => a.fmt_helper(f, stack_size),
            AcornValue::ArgList(args) => {
                write!(f, "(")?;
                fmt_values(args, f, stack_size)?;
                write!(f, ")")
            }
            AcornValue::Lambda(args, body) => fmt_macro(f, "lambda", args, body, stack_size),
            AcornValue::Implies(a, b) => fmt_binary(f, "=>", a, b, stack_size),
            AcornValue::Equals(a, b) => fmt_binary(f, "=", a, b, stack_size),
            AcornValue::NotEquals(a, b) => fmt_binary(f, "!=", a, b, stack_size),
            AcornValue::And(a, b) => fmt_binary(f, "&", a, b, stack_size),
            AcornValue::Or(a, b) => fmt_binary(f, "|", a, b, stack_size),
            AcornValue::Not(a) => {
                write!(f, "!")?;
                a.fmt_helper(f, stack_size)
            }
            AcornValue::ForAll(args, body) => fmt_macro(f, "forall", args, body, stack_size),
            AcornValue::Exists(args, body) => fmt_macro(f, "exists", args, body, stack_size),
            AcornValue::ForAllMacro => write!(f, "forall"),
            AcornValue::ExistsMacro => write!(f, "exists"),
        }
    }

    pub fn to_stacked_string(&self, stack_size: usize) -> String {
        format!(
            "{}",
            Subvalue {
                value: self,
                stack_size: stack_size,
            }
        )
    }

    // Creates a value of type matching AcornType::functional.
    pub fn apply(function: AcornValue, args: Vec<AcornValue>) -> AcornValue {
        if args.is_empty() {
            return function;
        }
        AcornValue::Application(FunctionApplication {
            function: Box::new(function),
            args,
        })
    }

    pub fn into_vec(self) -> Vec<AcornValue> {
        match self {
            AcornValue::ArgList(t) => t,
            _ => vec![self],
        }
    }

    pub fn is_constant(&self) -> bool {
        match self {
            AcornValue::Atom(t) => t.is_constant(),
            _ => false,
        }
    }

    pub fn axiom_index(&self) -> Option<AtomId> {
        match self {
            AcornValue::Atom(t) => match t.atom {
                Atom::Constant(i) => Some(i),
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

    pub fn negate(self) -> AcornValue {
        self.maybe_negate(true)
    }

    // Simplifies at the top level but does not recurse.
    // Does not typecheck
    fn maybe_negate(self, negate: bool) -> AcornValue {
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
    pub fn bind_values(self, stack_index: AtomId, values: &Vec<AcornValue>) -> AcornValue {
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
    pub fn insert_stack(self, index: AtomId, increment: AtomId) -> AcornValue {
        match self {
            AcornValue::Atom(a) => AcornValue::Atom(a.insert_stack(index, increment)),
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
    pub fn expand_lambdas(self, stack_size: AtomId) -> AcornValue {
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
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(quants, Box::new(value.expand_lambdas(new_stack_size)))
            }
            AcornValue::Exists(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(quants, Box::new(value.expand_lambdas(new_stack_size)))
            }
            _ => self,
        }
    }

    // Removes all "forall" nodes, collecting the quantified types into quantifiers.
    pub fn remove_forall(self, quantifiers: &mut Vec<AcornType>) -> AcornValue {
        match self {
            AcornValue::And(left, right) => {
                let original_num_quants = quantifiers.len() as AtomId;
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() as AtomId - original_num_quants;

                let shifted_right = right.insert_stack(original_num_quants, added_quants);
                let new_right = shifted_right.remove_forall(quantifiers);
                AcornValue::And(Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Or(left, right) => {
                let original_num_quants = quantifiers.len() as AtomId;
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() as AtomId - original_num_quants;

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

    // Replaces some constants in this value with other values.
    // 'replacer' tells us what value a constant should be replaced with, or None to not replace it.
    // stack_size is how many variables are already on the stack, that we should not use when
    // constructing replacements.
    pub fn replace_constants<'a>(
        &self,
        stack_size: AtomId,
        replacer: &impl Fn(AtomId) -> Option<&'a AcornValue>,
    ) -> AcornValue {
        match self {
            AcornValue::Atom(typed_atom) => {
                if let Atom::Constant(i) = typed_atom.atom {
                    if let Some(replacement) = replacer(i) {
                        // First we need to make the replacement use the correct stack variables
                        let shifted = replacement.clone().insert_stack(0, stack_size);
                        // Then we need to recursively replace constants in the replacement
                        return shifted.replace_constants(stack_size, replacer);
                    }
                }
                AcornValue::Atom(typed_atom.clone())
            }
            AcornValue::Application(fa) => {
                let new_function = fa.function.replace_constants(stack_size, replacer);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants(stack_size, replacer))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value =
                    value.replace_constants(stack_size + arg_types.len() as AtomId, replacer);
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.replace_constants(stack_size, replacer)),
                Box::new(right.replace_constants(stack_size, replacer)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.replace_constants(stack_size, replacer)),
                Box::new(right.replace_constants(stack_size, replacer)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.replace_constants(stack_size, replacer)),
                Box::new(right.replace_constants(stack_size, replacer)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.replace_constants(stack_size, replacer)),
                Box::new(right.replace_constants(stack_size, replacer)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.replace_constants(stack_size, replacer)),
                Box::new(right.replace_constants(stack_size, replacer)),
            ),
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_constants(stack_size, replacer)))
            }
            AcornValue::ForAll(quants, value) => {
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value =
                    value.replace_constants(stack_size + quants.len() as AtomId, replacer);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            _ => self.clone(),
        }
    }
}
