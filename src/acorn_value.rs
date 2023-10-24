use std::fmt;

use crate::acorn_type::{AcornType, FunctionType, NamespaceId};
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
        write!(f, "{}(", Subvalue::new(&self.function, stack_size))?;
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
    //
    // TODO: deprecate. Make it clear that:
    //   Term/Atom/TypeId is for the Prover.
    //   AcornValue/AcornType is for the Environment.
    Atom(TypedAtom),

    // A variable that is bound to a value on the stack.
    // Represented by (stack index, type).
    Variable(AtomId, AcornType),

    // A constant, defined in a particular namespace.
    // (namespace, constant id, constant name, type)
    // TODO: remove the constant id
    Constant(NamespaceId, AtomId, String, AcornType),

    Application(FunctionApplication),

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

    // The monomorphized version of a constant polymorphic function.
    // Like the Constant but also has a list of types that it has been monomorphized to.
    Monomorph(NamespaceId, AtomId, String, AcornType, Vec<AcornType>),
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
        match self.value {
            AcornValue::Atom(a) => write!(f, "{}", a),
            AcornValue::Variable(i, _) => write!(f, "x{}", i),
            AcornValue::Constant(_, _, name, _) => write!(f, "{}", name),
            AcornValue::Application(a) => a.fmt_helper(f, self.stack_size),
            AcornValue::Lambda(args, body) => fmt_macro(f, "lambda", args, body, self.stack_size),
            AcornValue::Implies(a, b) => fmt_binary(f, "=>", a, b, self.stack_size),
            AcornValue::Equals(a, b) => fmt_binary(f, "=", a, b, self.stack_size),
            AcornValue::NotEquals(a, b) => fmt_binary(f, "!=", a, b, self.stack_size),
            AcornValue::And(a, b) => fmt_binary(f, "&", a, b, self.stack_size),
            AcornValue::Or(a, b) => fmt_binary(f, "|", a, b, self.stack_size),
            AcornValue::Not(a) => {
                write!(f, "!{}", Subvalue::new(a, self.stack_size))
            }
            AcornValue::ForAll(args, body) => fmt_macro(f, "forall", args, body, self.stack_size),
            AcornValue::Exists(args, body) => fmt_macro(f, "exists", args, body, self.stack_size),
            AcornValue::Monomorph(_, _, name, _, types) => {
                write!(f, "{}<{}>", name, AcornType::vec_to_str(types))
            }
        }
    }
}

impl Subvalue<'_> {
    fn new(value: &AcornValue, stack_size: usize) -> Subvalue {
        Subvalue {
            value: value,
            stack_size: stack_size,
        }
    }

    fn root(value: &AcornValue) -> Subvalue {
        Subvalue::new(value, 0)
    }
}

fn fmt_values(v: &Vec<AcornValue>, f: &mut fmt::Formatter, stack_size: usize) -> fmt::Result {
    for (i, item) in v.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{}", Subvalue::new(item, stack_size))?;
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
    write!(
        f,
        "{}({}) {{ {} }}",
        name,
        AcornType::decs_to_str(decs, stack_size),
        Subvalue::new(body, stack_size + decs.len())
    )
}

fn fmt_binary(
    f: &mut fmt::Formatter,
    op: &str,
    left: &AcornValue,
    right: &AcornValue,
    stack_size: usize,
) -> fmt::Result {
    write!(
        f,
        "({} {} {})",
        Subvalue::new(left, stack_size),
        op,
        Subvalue::new(right, stack_size)
    )
}

impl fmt::Display for AcornValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Subvalue::root(self).fmt(f)
    }
}

impl AcornValue {
    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Atom(t) => t.acorn_type.clone(),
            AcornValue::Variable(_, t) => t.clone(),
            AcornValue::Constant(_, _, _, t) => t.clone(),
            AcornValue::Application(t) => t.return_type(),
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
            AcornValue::Monomorph(_, _, _, c_type, types) => c_type.monomorphize(types),
        }
    }

    // Construct an application if we have arguments, but omit it otherwise.
    pub fn new_apply(function: AcornValue, args: Vec<AcornValue>) -> AcornValue {
        if args.is_empty() {
            function
        } else {
            AcornValue::Application(FunctionApplication {
                function: Box::new(function),
                args,
            })
        }
    }

    // Construct a lambda if we have arguments, but omit it otherwise.
    pub fn new_lambda(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::Lambda(args, Box::new(value))
        }
    }

    // Construct a forall if we have arguments, but omit it otherwise.
    pub fn new_forall(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::ForAll(args, Box::new(value))
        }
    }

    // Construct an exists if we have arguments, but omit it otherwise.
    pub fn new_exists(args: Vec<AcornType>, value: AcornValue) -> AcornValue {
        if args.is_empty() {
            value
        } else {
            AcornValue::Exists(args, Box::new(value))
        }
    }

    // Construct a monomorph if we have generic types, but otherwise just return the atom.
    pub fn new_monomorph(
        namespace: NamespaceId,
        constant_id: AtomId,
        name: String,
        constant_type: AcornType,
        opaque_types: Vec<AcornType>,
    ) -> AcornValue {
        if opaque_types.is_empty() {
            AcornValue::Constant(namespace, constant_id, name, constant_type)
        } else {
            AcornValue::Monomorph(namespace, constant_id, name, constant_type, opaque_types)
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

    // Moves negation inward for a boolean comparison.
    // We want as close to CNF as possible.
    // So the order outside-in goes: and, or, negates.
    fn boolean_comparison(left: AcornValue, right: AcornValue, negate: bool) -> AcornValue {
        let negative_left = left.clone().move_negation_inwards(true);
        let negative_right = right.clone().move_negation_inwards(true);
        let positive_left = left.move_negation_inwards(false);
        let positive_right = right.move_negation_inwards(false);
        if negate {
            // left != right is equivalent to:
            //   (left | right) & (!left | !right)
            AcornValue::And(
                Box::new(AcornValue::Or(
                    Box::new(negative_left),
                    Box::new(negative_right),
                )),
                Box::new(AcornValue::Or(
                    Box::new(positive_left),
                    Box::new(positive_right),
                )),
            )
        } else {
            // left = right is equivalent to:
            //   (!left | right) & (left | !right)
            AcornValue::And(
                Box::new(AcornValue::Or(
                    Box::new(negative_left),
                    Box::new(positive_right),
                )),
                Box::new(AcornValue::Or(
                    Box::new(positive_left),
                    Box::new(negative_right),
                )),
            )
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
            AcornValue::Equals(left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, negate)
                } else {
                    AcornValue::Equals(left, right).maybe_negate(negate)
                }
            }
            AcornValue::NotEquals(left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, !negate)
                } else {
                    AcornValue::NotEquals(left, right).maybe_negate(negate)
                }
            }
            _ => self.maybe_negate(negate),
        }
    }

    // Binds the provided values to stack variables.
    //
    // The first_binding_index is the first index that we should bind to.
    // For example, if stack_index is 2, and the values
    // are "foo", "bar", and "baz" we should set x2 = foo, x3 = bar, x4 = baz.
    // Any subsequent variables, x5 x6 x7 etc, should be renumbered downwards.
    //
    // The stack_size is the size of the stack where this value occurs. This is relevant because any
    // variables in the bound values will be moved into this environment, so we need to renumber
    // their variables appropriately.
    pub fn bind_values(
        self,
        first_binding_index: AtomId,
        stack_size: AtomId,
        values: &Vec<AcornValue>,
    ) -> AcornValue {
        match self {
            AcornValue::Atom(a) => a.bind_values(first_binding_index, stack_size, values),
            AcornValue::Variable(i, var_type) => {
                if i < first_binding_index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type);
                }
                if i < first_binding_index + values.len() as AtomId {
                    // This reference is bound to a new value
                    let new_value = values[(i - first_binding_index) as usize].clone();

                    // We are moving this value between contexts with possibly different stack sizes
                    assert!(stack_size >= first_binding_index);
                    return new_value
                        .insert_stack(first_binding_index, stack_size - first_binding_index);
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i - values.len() as AtomId, var_type)
            }
            AcornValue::Constant(namespace, id, name, t) => {
                AcornValue::Constant(namespace, id, name, t)
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.bind_values(
                    first_binding_index,
                    stack_size,
                    values,
                )),
                args: app
                    .args
                    .into_iter()
                    .map(|x| x.bind_values(first_binding_index, stack_size, values))
                    .collect(),
            }),
            AcornValue::Lambda(args, return_value) => {
                let return_value_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(
                    args,
                    Box::new(return_value.bind_values(
                        first_binding_index,
                        return_value_stack_size,
                        values,
                    )),
                )
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.bind_values(first_binding_index, stack_size, values)),
                Box::new(right.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.bind_values(
                first_binding_index,
                stack_size,
                values,
            ))),
            AcornValue::ForAll(quants, value) => {
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(
                    quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let value_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(
                    quants,
                    Box::new(value.bind_values(first_binding_index, value_stack_size, values)),
                )
            }
            AcornValue::Monomorph(_, _, _, _, _) => self,
        }
    }

    // Inserts 'increment' stack entries, starting with the provided index, that this value
    // doesn't use.
    // This moves the value from a context that has 'index' stack entries, to one that
    // has 'index + increment' entries.
    // Every reference at index or higher should be incremented by increment.
    pub fn insert_stack(self, index: AtomId, increment: AtomId) -> AcornValue {
        if increment == 0 {
            return self;
        }
        match self {
            AcornValue::Atom(a) => AcornValue::Atom(a.insert_stack(index, increment)),
            AcornValue::Variable(i, var_type) => {
                if i < index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type);
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i + increment, var_type)
            }
            AcornValue::Constant(namespace, id, name, t) => {
                AcornValue::Constant(namespace, id, name, t)
            }
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
            AcornValue::Monomorph(_, _, _, _, _) => self,
        }
    }

    // Converts function types to a primitive type by applying them to new unbound variables.
    // Inserts these unbound variables as new stack variables starting at stack_size.
    // Returns the types of the newly created unbound variables, along with the converted value.
    fn apply_to_free_variables(self, stack_size: AtomId) -> (Vec<AcornType>, AcornValue) {
        let current_type = self.get_type();
        if let AcornType::Function(ftype) = current_type {
            let shifted = self.insert_stack(stack_size, ftype.arg_types.len() as AtomId);
            let new_value = AcornValue::Application(FunctionApplication {
                function: Box::new(shifted),
                args: ftype
                    .arg_types
                    .iter()
                    .enumerate()
                    .map(|(i, t)| AcornValue::Variable(stack_size + i as AtomId, t.clone()))
                    .collect(),
            });

            // We need to recurse in case we have functions that generate more functions.
            let (mut new_args, final_value) = new_value.apply_to_free_variables(stack_size);
            new_args.extend(ftype.arg_types);
            (new_args, final_value)
        } else {
            (vec![], self)
        }
    }

    // Replaces functional comparisons with comparisons between primitive values.
    // f = g is equivalent to forall(x) { f(x) = g(x) }
    // f != g is equivalent to exists(x) { f(x) != g(x) }
    pub fn replace_function_equality(&self, stack_size: AtomId) -> AcornValue {
        match self {
            AcornValue::Atom(_) => panic!("dead branch"),

            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.replace_function_equality(stack_size)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.replace_function_equality(stack_size))
                    .collect(),
            }),
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.replace_function_equality(stack_size)),
                Box::new(right.replace_function_equality(stack_size)),
            ),
            AcornValue::Equals(left, right) => {
                let (left_quants, left) = left
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                let (right_quants, right) = right
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                assert_eq!(left_quants, right_quants);
                let equality = AcornValue::Equals(Box::new(left), Box::new(right));
                let answer = if left_quants.is_empty() {
                    equality
                } else {
                    AcornValue::ForAll(left_quants, Box::new(equality))
                };
                answer
            }
            AcornValue::NotEquals(left, right) => {
                let (left_quants, left) = left
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                let (right_quants, right) = right
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                assert_eq!(left_quants, right_quants);
                let inequality = AcornValue::NotEquals(Box::new(left), Box::new(right));
                if left_quants.is_empty() {
                    inequality
                } else {
                    AcornValue::Exists(left_quants, Box::new(inequality))
                }
            }
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.replace_function_equality(stack_size)),
                Box::new(right.replace_function_equality(stack_size)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.replace_function_equality(stack_size)),
                Box::new(right.replace_function_equality(stack_size)),
            ),
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_function_equality(stack_size)))
            }
            AcornValue::ForAll(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::ForAll(
                    quants.clone(),
                    Box::new(value.replace_function_equality(new_stack_size)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(
                    quants.clone(),
                    Box::new(value.replace_function_equality(new_stack_size)),
                )
            }
            AcornValue::Lambda(args, value) => {
                let new_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(
                    args.clone(),
                    Box::new(value.replace_function_equality(new_stack_size)),
                )
            }
            AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Monomorph(_, _, _, _, _) => self.clone(),
        }
    }

    // Attempts to remove all lambdas from a value.
    //
    // Replaces lambda(...) { value } (args) by substituting the args into the value.
    //
    // stack_size is the number of variables that are already on the stack.
    pub fn expand_lambdas(self, stack_size: AtomId) -> AcornValue {
        match self {
            AcornValue::Application(app) => {
                let function = app.function.expand_lambdas(stack_size);
                if let AcornValue::Lambda(_, return_value) = function {
                    // Expand the lambda
                    let expanded = return_value.bind_values(stack_size, stack_size, &app.args);
                    expanded.expand_lambdas(stack_size)
                } else {
                    AcornValue::Application(FunctionApplication {
                        function: Box::new(function),
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
                AcornValue::ForAll(
                    quants.clone(),
                    Box::new(value.expand_lambdas(new_stack_size)),
                )
            }
            AcornValue::Exists(quants, value) => {
                let new_stack_size = stack_size + quants.len() as AtomId;
                AcornValue::Exists(quants, Box::new(value.expand_lambdas(new_stack_size)))
            }
            AcornValue::Lambda(args, value) => {
                let new_stack_size = stack_size + args.len() as AtomId;
                AcornValue::Lambda(args, Box::new(value.expand_lambdas(new_stack_size)))
            }
            AcornValue::Atom(_)
            | AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Monomorph(_, _, _, _, _) => self,
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
    pub fn replace_constants_with_values<'a>(
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
                        return shifted.replace_constants_with_values(stack_size, replacer);
                    }
                }
                AcornValue::Atom(typed_atom.clone())
            }
            AcornValue::Constant(_, id, _, _) => {
                if let Some(replacement) = replacer(*id) {
                    // First we need to make the replacement use the correct stack variables
                    let shifted = replacement.clone().insert_stack(0, stack_size);
                    // Then we need to recursively replace constants in the replacement
                    return shifted.replace_constants_with_values(stack_size, replacer);
                }
                self.clone()
            }
            AcornValue::Variable(_, _) => self.clone(),
            AcornValue::Application(fa) => {
                let new_function = fa
                    .function
                    .replace_constants_with_values(stack_size, replacer);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants_with_values(stack_size, replacer))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value = value.replace_constants_with_values(
                    stack_size + arg_types.len() as AtomId,
                    replacer,
                );
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.replace_constants_with_values(stack_size, replacer)),
                Box::new(right.replace_constants_with_values(stack_size, replacer)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.replace_constants_with_values(stack_size, replacer)),
                Box::new(right.replace_constants_with_values(stack_size, replacer)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.replace_constants_with_values(stack_size, replacer)),
                Box::new(right.replace_constants_with_values(stack_size, replacer)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.replace_constants_with_values(stack_size, replacer)),
                Box::new(right.replace_constants_with_values(stack_size, replacer)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.replace_constants_with_values(stack_size, replacer)),
                Box::new(right.replace_constants_with_values(stack_size, replacer)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(
                x.replace_constants_with_values(stack_size, replacer),
            )),
            AcornValue::ForAll(quants, value) => {
                let new_value = value
                    .replace_constants_with_values(stack_size + quants.len() as AtomId, replacer);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value = value
                    .replace_constants_with_values(stack_size + quants.len() as AtomId, replacer);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            AcornValue::Monomorph(_, id, _, _, types) => {
                if let Some(replacement) = replacer(*id) {
                    // We do need to replace this
                    replacement.monomorphize(types)
                } else {
                    // We don't need to replace this
                    self.clone()
                }
            }
        }
    }

    // Replace the constant(constants[i]) with a variable(i).
    // Shift all other variable indexes up to account for the new variables.
    pub fn replace_constants_with_variables(&self, constants: &Vec<AtomId>) -> AcornValue {
        match self {
            AcornValue::Atom(typed_atom) => match typed_atom.atom {
                Atom::Constant(c) => {
                    if let Some(i) = constants.iter().position(|&x| x == c) {
                        AcornValue::Variable(i as AtomId, typed_atom.acorn_type.clone())
                    } else {
                        self.clone()
                    }
                }
                Atom::Variable(i) => AcornValue::Atom(TypedAtom {
                    atom: Atom::Variable(i + constants.len() as AtomId),
                    acorn_type: typed_atom.acorn_type.clone(),
                }),
                _ => self.clone(),
            },
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(i + constants.len() as AtomId, var_type.clone())
            }
            AcornValue::Constant(_, id, _, t) => {
                if let Some(i) = constants.iter().position(|&x| x == *id) {
                    AcornValue::Variable(i as AtomId, t.clone())
                } else {
                    self.clone()
                }
            }
            AcornValue::Application(fa) => {
                let new_function = fa.function.replace_constants_with_variables(constants);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants_with_variables(constants))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value = value.replace_constants_with_variables(constants);
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.replace_constants_with_variables(constants)),
                Box::new(right.replace_constants_with_variables(constants)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.replace_constants_with_variables(constants)),
                Box::new(right.replace_constants_with_variables(constants)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.replace_constants_with_variables(constants)),
                Box::new(right.replace_constants_with_variables(constants)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.replace_constants_with_variables(constants)),
                Box::new(right.replace_constants_with_variables(constants)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.replace_constants_with_variables(constants)),
                Box::new(right.replace_constants_with_variables(constants)),
            ),
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_constants_with_variables(constants)))
            }
            AcornValue::ForAll(quants, value) => {
                let new_value = value.replace_constants_with_variables(constants);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value = value.replace_constants_with_variables(constants);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            AcornValue::Monomorph(_, _, _, _, _) => panic!("can this happen?"),
        }
    }

    // Find all constants c_i with i >= index.
    // Report tuples of (i, type).
    pub fn find_constants_gte(&self, index: AtomId, answer: &mut Vec<(AtomId, AcornType)>) {
        match self {
            AcornValue::Atom(ta) => ta.find_constants_gte(index, answer),
            AcornValue::Variable(_, _) => {}
            AcornValue::Constant(_, id, _, t) => {
                if *id >= index {
                    answer.push((*id, t.clone()));
                }
            }
            AcornValue::Application(fa) => {
                fa.function.find_constants_gte(index, answer);
                for arg in &fa.args {
                    arg.find_constants_gte(index, answer);
                }
            }
            AcornValue::Lambda(_, value) => value.find_constants_gte(index, answer),
            AcornValue::Implies(left, right) => {
                left.find_constants_gte(index, answer);
                right.find_constants_gte(index, answer);
            }
            AcornValue::Equals(left, right) => {
                left.find_constants_gte(index, answer);
                right.find_constants_gte(index, answer);
            }
            AcornValue::NotEquals(left, right) => {
                left.find_constants_gte(index, answer);
                right.find_constants_gte(index, answer);
            }
            AcornValue::And(left, right) => {
                left.find_constants_gte(index, answer);
                right.find_constants_gte(index, answer);
            }
            AcornValue::Or(left, right) => {
                left.find_constants_gte(index, answer);
                right.find_constants_gte(index, answer);
            }
            AcornValue::Not(x) => x.find_constants_gte(index, answer),
            AcornValue::ForAll(_, value) => value.find_constants_gte(index, answer),
            AcornValue::Exists(_, value) => value.find_constants_gte(index, answer),
            AcornValue::Monomorph(_, c, _, generic_type, _) => TypedAtom {
                atom: Atom::Constant(*c),
                acorn_type: generic_type.clone(),
            }
            .find_constants_gte(index, answer),
        }
    }

    // Returns an error string if this is not a valid top-level value.
    // The types of variables should match the type of the quantifier they correspond to.
    pub fn validate(&self) -> Result<(), String> {
        let mut stack: Vec<AcornType> = vec![];
        self.validate_against_stack(&mut stack)
    }

    fn validate_against_stack(&self, stack: &mut Vec<AcornType>) -> Result<(), String> {
        match self {
            AcornValue::Atom(ta) => match ta.atom {
                Atom::Variable(i) => match stack.get(i as usize) {
                    Some(t) => {
                        if ta.acorn_type == *t {
                            Ok(())
                        } else {
                            Err(format!(
                                "variable {} has type {:?} but is used as type {:?}",
                                i, t, ta.acorn_type
                            ))
                        }
                    }
                    None => Err(format!("variable {} is not in scope", i)),
                },
                _ => Ok(()),
            },
            AcornValue::Variable(i, var_type) => match stack.get(*i as usize) {
                Some(t) => {
                    if var_type == t {
                        Ok(())
                    } else {
                        Err(format!(
                            "variable {} has type {:?} but is used as type {:?}",
                            i, t, var_type
                        ))
                    }
                }
                None => Err(format!("variable {} is not in scope", i)),
            },
            AcornValue::Application(app) => {
                app.function.validate_against_stack(stack)?;
                for arg in &app.args {
                    arg.validate_against_stack(stack)?;
                }
                Ok(())
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                let original_len = stack.len();
                stack.extend(args.iter().cloned());
                let answer = value.validate_against_stack(stack);
                stack.truncate(original_len);
                answer
            }
            AcornValue::Implies(left, right)
            | AcornValue::Equals(left, right)
            | AcornValue::NotEquals(left, right)
            | AcornValue::And(left, right)
            | AcornValue::Or(left, right) => {
                left.validate_against_stack(stack)?;
                right.validate_against_stack(stack)
            }
            AcornValue::Not(x) => x.validate_against_stack(stack),
            AcornValue::Monomorph(_, _, _, _, _) | AcornValue::Constant(_, _, _, _) => Ok(()),
        }
    }

    // Replaces all the generic types with specific types
    pub fn monomorphize(&self, types: &[AcornType]) -> AcornValue {
        match self {
            AcornValue::Atom(ta) => {
                if let Atom::Constant(c) = ta.atom {
                    if ta.acorn_type.is_polymorphic() {
                        // We need to monomorphize
                        AcornValue::Monomorph(
                            0,
                            c,
                            "XXX".to_string(),
                            ta.acorn_type.clone(),
                            types.to_vec(),
                        )
                    } else {
                        // Otherwise, this constant is unchanged
                        self.clone()
                    }
                } else {
                    // Change the type appropriately
                    AcornValue::Atom(ta.monomorphize(types))
                }
            }
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.monomorphize(types))
            }
            AcornValue::Constant(namespace, id, name, t) => {
                if t.is_polymorphic() {
                    // We need to monomorphize
                    AcornValue::Monomorph(*namespace, *id, name.clone(), t.clone(), types.to_vec())
                } else {
                    // Otherwise, this constant is unchanged
                    self.clone()
                }
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.monomorphize(types)),
                args: app.args.iter().map(|x| x.monomorphize(types)).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.monomorphize(types))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(types)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.monomorphize(types))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(types)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.monomorphize(types))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(types)),
            ),
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.monomorphize(types)),
                Box::new(right.monomorphize(types)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.monomorphize(types)),
                Box::new(right.monomorphize(types)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.monomorphize(types)),
                Box::new(right.monomorphize(types)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.monomorphize(types)),
                Box::new(right.monomorphize(types)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.monomorphize(types)),
                Box::new(right.monomorphize(types)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.monomorphize(types))),
            AcornValue::Monomorph(_, _, _, _, _) => {
                // We don't alter monomorphs because they cannot themselves be polymorphic.
                // That would be something like, taking T to List<U>, or partially
                // monomorphizing Map<T, U> to Map<T, Nat>, neither of which we
                // support yet.
                self.clone()
            }
        }
    }

    // Replaces a data type with a generic type.
    pub fn genericize(
        &self,
        namespace: NamespaceId,
        name: &str,
        generic_type: usize,
    ) -> AcornValue {
        match self {
            AcornValue::Atom(ta) => AcornValue::Atom(ta.genericize(namespace, name, generic_type)),
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.genericize(namespace, name, generic_type))
            }
            AcornValue::Constant(const_namespace, id, name, t) => AcornValue::Constant(
                *const_namespace,
                *id,
                name.clone(),
                t.genericize(namespace, name, generic_type),
            ),
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.genericize(namespace, name, generic_type)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.genericize(namespace, name, generic_type))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.genericize(namespace, name, generic_type))
                    .collect(),
                Box::new(value.genericize(namespace, name, generic_type)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.genericize(namespace, name, generic_type))
                    .collect(),
                Box::new(value.genericize(namespace, name, generic_type)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.genericize(namespace, name, generic_type))
                    .collect(),
                Box::new(value.genericize(namespace, name, generic_type)),
            ),
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.genericize(namespace, name, generic_type)),
                Box::new(right.genericize(namespace, name, generic_type)),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.genericize(namespace, name, generic_type)),
                Box::new(right.genericize(namespace, name, generic_type)),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.genericize(namespace, name, generic_type)),
                Box::new(right.genericize(namespace, name, generic_type)),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.genericize(namespace, name, generic_type)),
                Box::new(right.genericize(namespace, name, generic_type)),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.genericize(namespace, name, generic_type)),
                Box::new(right.genericize(namespace, name, generic_type)),
            ),
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.genericize(namespace, name, generic_type)))
            }
            AcornValue::Monomorph(_, c, _, c_type, types) => {
                if types.len() > 1 || generic_type > 0 {
                    todo!("genericize monomorphs with multiple types");
                }

                if types[0].equals_data_type(namespace, name) {
                    return AcornValue::Atom(TypedAtom {
                        atom: Atom::Constant(*c),
                        acorn_type: c_type.clone(),
                    });
                }

                if types[0].refers_to(namespace, name) {
                    todo!("genericize monomorphs with complex types");
                }

                self.clone()
            }
        }
    }

    // Finds all polymorphic constants used in this value.
    pub fn find_polymorphic(&self, output: &mut Vec<AtomId>) {
        match self {
            AcornValue::Atom(ta) => {
                if let Atom::Constant(c) = ta.atom {
                    if ta.acorn_type.is_polymorphic() {
                        output.push(c);
                    }
                }
            }
            AcornValue::Variable(_, _) => {}
            AcornValue::Constant(_, id, _, t) => {
                if t.is_polymorphic() {
                    output.push(*id);
                }
            }
            AcornValue::Application(app) => {
                app.function.find_polymorphic(output);
                for arg in &app.args {
                    arg.find_polymorphic(output);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.find_polymorphic(output),
            AcornValue::Implies(left, right)
            | AcornValue::Equals(left, right)
            | AcornValue::NotEquals(left, right)
            | AcornValue::And(left, right)
            | AcornValue::Or(left, right) => {
                left.find_polymorphic(output);
                right.find_polymorphic(output);
            }
            AcornValue::Not(x) => x.find_polymorphic(output),
            AcornValue::Monomorph(_, _, _, _, _) => {}
        }
    }

    // Finds all monomorphizations of polymorphic constants in this value.
    // Only handles single generic types.
    pub fn find_monomorphs(&self, output: &mut Vec<(AtomId, AcornType)>) {
        match self {
            AcornValue::Atom(_) | AcornValue::Variable(_, _) | AcornValue::Constant(_, _, _, _) => {
            }
            AcornValue::Application(app) => {
                app.function.find_monomorphs(output);
                for arg in &app.args {
                    arg.find_monomorphs(output);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.find_monomorphs(output),
            AcornValue::Implies(left, right)
            | AcornValue::Equals(left, right)
            | AcornValue::NotEquals(left, right)
            | AcornValue::And(left, right)
            | AcornValue::Or(left, right) => {
                left.find_monomorphs(output);
                right.find_monomorphs(output);
            }
            AcornValue::Not(x) => x.find_monomorphs(output),
            AcornValue::Monomorph(_, id, _, _, types) => {
                assert!(types.len() == 1);
                output.push((*id, types[0].clone()));
            }
        }
    }

    // A value is polymorphic if any of its components have a polymorphic type.
    pub fn is_polymorphic(&self) -> bool {
        match self {
            AcornValue::Atom(ta) => ta.acorn_type.is_polymorphic(),
            AcornValue::Variable(_, t) | AcornValue::Constant(_, _, _, t) => t.is_polymorphic(),

            AcornValue::Application(app) => {
                app.function.is_polymorphic() || app.args.iter().any(|x| x.is_polymorphic())
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.is_polymorphic(),
            AcornValue::Implies(left, right)
            | AcornValue::Equals(left, right)
            | AcornValue::NotEquals(left, right)
            | AcornValue::And(left, right)
            | AcornValue::Or(left, right) => left.is_polymorphic() || right.is_polymorphic(),
            AcornValue::Not(x) => x.is_polymorphic(),
            AcornValue::Monomorph(_, _, _, _, _) => false,
        }
    }

    // Converts all the parametrized types to placeholder types.
    pub fn to_placeholder(&self) -> AcornValue {
        match self {
            AcornValue::Atom(ta) => AcornValue::Atom(ta.to_placeholder()),
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.to_placeholder())
            }
            AcornValue::Constant(namespace, id, name, t) => {
                AcornValue::Constant(*namespace, *id, name.clone(), t.to_placeholder())
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.to_placeholder()),
                args: app.args.iter().map(|x| x.to_placeholder()).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter().map(|x| x.to_placeholder()).collect(),
                Box::new(value.to_placeholder()),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter().map(|x| x.to_placeholder()).collect(),
                Box::new(value.to_placeholder()),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter().map(|x| x.to_placeholder()).collect(),
                Box::new(value.to_placeholder()),
            ),
            AcornValue::Implies(left, right) => AcornValue::Implies(
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::Equals(left, right) => AcornValue::Equals(
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::NotEquals(left, right) => AcornValue::NotEquals(
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::And(left, right) => AcornValue::And(
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::Or(left, right) => AcornValue::Or(
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.to_placeholder())),
            AcornValue::Monomorph(_, _, _, _, _) => self.clone(),
        }
    }
}
