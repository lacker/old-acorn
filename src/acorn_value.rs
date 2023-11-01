use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::{AcornType, FunctionType};
use crate::atom::AtomId;
use crate::constant_map::ConstantKey;
use crate::namespace::NamespaceId;

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

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum BinaryOp {
    Implies,
    Equals,
    NotEquals,
    And,
    Or,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::Implies => write!(f, "->"),
            BinaryOp::Equals => write!(f, "="),
            BinaryOp::NotEquals => write!(f, "!="),
            BinaryOp::And => write!(f, "&"),
            BinaryOp::Or => write!(f, "|"),
        }
    }
}

// Two AcornValue compare to equal if they are structurally identical.
// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    // A variable that is bound to a value on the stack.
    // Represented by (stack index, type).
    Variable(AtomId, AcornType),

    // A constant, defined in a particular namespace.
    // (namespace, constant name, type, type parameters)
    // The type parameters can be empty.
    // The type parameters must be used in the type of this constant, because
    // we need to be able to infer the monomorph whenever this constant is applied.
    // Conversely, every type parameter used in the definition of this constant must be
    // present in the parameter list.
    Constant(NamespaceId, String, AcornType, Vec<String>),

    Application(FunctionApplication),

    // A function definition that introduces variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    // The boolean binary operators are treated specially during inference
    Binary(BinaryOp, Box<AcornValue>, Box<AcornValue>),

    Not(Box<AcornValue>),

    // Quantifiers that introduce variables onto the stack.
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),

    // The monomorphized version of a polymorphic constant.
    // (namespace, constant name, type, (type parameter, type) mapping)
    // The type is the polymorphic type of the constant.
    // The vector parameter maps parameter names to types they were monomorphized to.
    // The parameters cannot be empty - that should be a Constant rather than a Monomorph.
    Monomorph(NamespaceId, String, AcornType, Vec<(String, AcornType)>),
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
            AcornValue::Variable(i, _) => write!(f, "x{}", i),
            AcornValue::Constant(_, name, _, _) => write!(f, "{}", name),
            AcornValue::Application(a) => a.fmt_helper(f, self.stack_size),
            AcornValue::Lambda(args, body) => fmt_binder(f, "lambda", args, body, self.stack_size),
            AcornValue::Binary(op, left, right) => {
                write!(
                    f,
                    "({} {} {})",
                    Subvalue::new(left, self.stack_size),
                    op,
                    Subvalue::new(right, self.stack_size)
                )
            }
            AcornValue::Not(a) => {
                write!(f, "!{}", Subvalue::new(a, self.stack_size))
            }
            AcornValue::ForAll(args, body) => fmt_binder(f, "forall", args, body, self.stack_size),
            AcornValue::Exists(args, body) => fmt_binder(f, "exists", args, body, self.stack_size),
            AcornValue::Monomorph(_, name, _, params) => {
                let param_names: Vec<_> = params.iter().map(|(name, _)| name.to_string()).collect();
                write!(f, "{}<{}>", name, param_names.join(", "))
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

fn fmt_binder(
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

impl fmt::Display for AcornValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Subvalue::root(self).fmt(f)
    }
}

impl AcornValue {
    pub fn get_type(&self) -> AcornType {
        match self {
            AcornValue::Variable(_, t) => t.clone(),
            AcornValue::Constant(_, _, t, _) => t.clone(),
            AcornValue::Application(t) => t.return_type(),
            AcornValue::Lambda(args, return_value) => AcornType::Function(FunctionType {
                arg_types: args.clone(),
                return_type: Box::new(return_value.get_type()),
            }),
            AcornValue::Binary(_, _, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::Monomorph(_, _, c_type, params) => c_type.monomorphize(&params),
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
        name: String,
        constant_type: AcornType,
        params: Vec<(String, AcornType)>,
    ) -> AcornValue {
        if params.is_empty() {
            AcornValue::Constant(namespace, name, constant_type, vec![])
        } else {
            AcornValue::Monomorph(namespace, name, constant_type, params)
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
            AcornValue::Binary(BinaryOp::Equals, x, y) => {
                AcornValue::Binary(BinaryOp::NotEquals, x, y)
            }
            AcornValue::Binary(BinaryOp::NotEquals, x, y) => {
                AcornValue::Binary(BinaryOp::Equals, x, y)
            }
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
            AcornValue::Binary(
                BinaryOp::And,
                Box::new(AcornValue::Binary(
                    BinaryOp::Or,
                    Box::new(negative_left),
                    Box::new(negative_right),
                )),
                Box::new(AcornValue::Binary(
                    BinaryOp::Or,
                    Box::new(positive_left),
                    Box::new(positive_right),
                )),
            )
        } else {
            // left = right is equivalent to:
            //   (!left | right) & (left | !right)
            AcornValue::Binary(
                BinaryOp::And,
                Box::new(AcornValue::Binary(
                    BinaryOp::Or,
                    Box::new(negative_left),
                    Box::new(positive_right),
                )),
                Box::new(AcornValue::Binary(
                    BinaryOp::Or,
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
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                // (left -> right) is equivalent to (!left | right)
                let equivalent =
                    AcornValue::Binary(BinaryOp::Or, Box::new(AcornValue::Not(left)), right);
                equivalent.move_negation_inwards(negate)
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                if negate {
                    // !(left & right) is equivalent to (!left | !right)
                    let equivalent = AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(AcornValue::Not(left)),
                        Box::new(AcornValue::Not(right)),
                    );
                    equivalent.move_negation_inwards(false)
                } else {
                    AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(left.move_negation_inwards(false)),
                        Box::new(right.move_negation_inwards(false)),
                    )
                }
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                if negate {
                    // !(left | right) is equivalent to (!left & !right)
                    let equivalent = AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(AcornValue::Not(left)),
                        Box::new(AcornValue::Not(right)),
                    );
                    equivalent.move_negation_inwards(false)
                } else {
                    AcornValue::Binary(
                        BinaryOp::Or,
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
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, negate)
                } else {
                    AcornValue::Binary(BinaryOp::Equals, left, right).maybe_negate(negate)
                }
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, !negate)
                } else {
                    AcornValue::Binary(BinaryOp::NotEquals, left, right).maybe_negate(negate)
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
            AcornValue::Constant(_, _, _, _) => self.clone(),
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
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
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
            AcornValue::Monomorph(_, _, _, _) => self,
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
            AcornValue::Variable(i, var_type) => {
                if i < index {
                    // This reference is unchanged
                    return AcornValue::Variable(i, var_type);
                }
                // This reference just needs to be shifted
                AcornValue::Variable(i + increment, var_type)
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
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
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
            AcornValue::Constant(_, _, _, _) | AcornValue::Monomorph(_, _, _, _) => self,
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
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.replace_function_equality(stack_size)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.replace_function_equality(stack_size))
                    .collect(),
            }),
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                let (left_quants, left) = left
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                let (right_quants, right) = right
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                assert_eq!(left_quants, right_quants);
                let equality =
                    AcornValue::Binary(BinaryOp::Equals, Box::new(left), Box::new(right));
                let answer = if left_quants.is_empty() {
                    equality
                } else {
                    AcornValue::ForAll(left_quants, Box::new(equality))
                };
                answer
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                let (left_quants, left) = left
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                let (right_quants, right) = right
                    .replace_function_equality(stack_size)
                    .apply_to_free_variables(stack_size);
                assert_eq!(left_quants, right_quants);
                let inequality =
                    AcornValue::Binary(BinaryOp::NotEquals, Box::new(left), Box::new(right));
                if left_quants.is_empty() {
                    inequality
                } else {
                    AcornValue::Exists(left_quants, Box::new(inequality))
                }
            }
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
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
            | AcornValue::Monomorph(_, _, _, _) => self.clone(),
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
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                op,
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
            AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Monomorph(_, _, _, _) => self,
        }
    }

    // Removes all "forall" nodes, collecting the quantified types into quantifiers.
    pub fn remove_forall(self, quantifiers: &mut Vec<AcornType>) -> AcornValue {
        match self {
            AcornValue::Binary(BinaryOp::And, left, right) => {
                let original_num_quants = quantifiers.len() as AtomId;
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() as AtomId - original_num_quants;

                let shifted_right = right.insert_stack(original_num_quants, added_quants);
                let new_right = shifted_right.remove_forall(quantifiers);
                AcornValue::Binary(BinaryOp::And, Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Binary(BinaryOp::Or, left, right) => {
                let original_num_quants = quantifiers.len() as AtomId;
                let new_left = left.remove_forall(quantifiers);
                let added_quants = quantifiers.len() as AtomId - original_num_quants;

                let shifted_right = right.insert_stack(original_num_quants, added_quants);
                let new_right = shifted_right.remove_forall(quantifiers);
                AcornValue::Binary(BinaryOp::Or, Box::new(new_left), Box::new(new_right))
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
        replacer: &impl Fn(NamespaceId, &str) -> Option<&'a AcornValue>,
    ) -> AcornValue {
        match self {
            AcornValue::Constant(namespace, name, _, params) => {
                if let Some(replacement) = replacer(*namespace, name) {
                    assert!(params.is_empty());
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
            AcornValue::Binary(op, left, right) => {
                let new_left = left.replace_constants_with_values(stack_size, replacer);
                let new_right = right.replace_constants_with_values(stack_size, replacer);
                AcornValue::Binary(*op, Box::new(new_left), Box::new(new_right))
            }
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
            AcornValue::Monomorph(namespace, name, _, params) => {
                if let Some(replacement) = replacer(*namespace, name) {
                    // We do need to replace this
                    replacement.monomorphize(params)
                } else {
                    // We don't need to replace this
                    self.clone()
                }
            }
        }
    }

    // For constants in this namespace, replace them with a variable id if they are in the constants map.
    pub fn replace_constants_with_vars(
        &self,
        namespace: NamespaceId,
        constants: &HashMap<String, AtomId>,
    ) -> AcornValue {
        match self {
            AcornValue::Variable(_, _) => self.clone(),
            AcornValue::Constant(n, name, t, params) => {
                if *n == namespace {
                    if let Some(i) = constants.get(name) {
                        assert!(params.is_empty());
                        return AcornValue::Variable(*i, t.clone());
                    }
                }
                self.clone()
            }
            AcornValue::Application(fa) => {
                let new_function = fa
                    .function
                    .replace_constants_with_vars(namespace, constants);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants_with_vars(namespace, constants))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value = value.replace_constants_with_vars(namespace, constants);
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Binary(op, left, right) => {
                let new_left = left.replace_constants_with_vars(namespace, constants);
                let new_right = right.replace_constants_with_vars(namespace, constants);
                AcornValue::Binary(*op, Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Not(x) => AcornValue::Not(Box::new(
                x.replace_constants_with_vars(namespace, constants),
            )),
            AcornValue::ForAll(quants, value) => {
                let new_value = value.replace_constants_with_vars(namespace, constants);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value = value.replace_constants_with_vars(namespace, constants);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            AcornValue::Monomorph(_, _, _, _) => panic!("can this happen?"),
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
            AcornValue::Binary(_, left, right) => {
                left.validate_against_stack(stack)?;
                right.validate_against_stack(stack)
            }
            AcornValue::Not(x) => x.validate_against_stack(stack),
            AcornValue::Monomorph(_, _, _, _) | AcornValue::Constant(_, _, _, _) => Ok(()),
        }
    }

    // A value is monomorphized by replacing *all* parametric types with concrete types.
    // For example, the definition of a polymorphic function or a theorem is stored with
    // parameters. However, in the context where it is applied, or used in the prover,
    // we should be able to figure out its monomorphization from the context.
    pub fn monomorphize(&self, params: &[(String, AcornType)]) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.monomorphize(params))
            }
            AcornValue::Constant(namespace, name, t, c_params) => {
                if c_params.is_empty() {
                    // This constant isn't polymorphic in the first place
                    return self.clone();
                }
                assert!(t.is_parametric());

                // Match up names to monomorphize
                let mut out_params = vec![];
                for name in c_params {
                    let mut found = false;
                    for (param_name, param_type) in params {
                        if name == param_name {
                            out_params.push((name.clone(), param_type.clone()));
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        panic!("could not find param {} in {:?}", name, params);
                    }
                }
                AcornValue::Monomorph(*namespace, name.clone(), t.clone(), out_params)
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.monomorphize(params)),
                args: app.args.iter().map(|x| x.monomorphize(params)).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.monomorphize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(params)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.monomorphize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(params)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.monomorphize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.monomorphize(params)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.monomorphize(params)),
                Box::new(right.monomorphize(params)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.monomorphize(params))),
            AcornValue::Monomorph(namespace, name, base_type, params) => {
                // I think we should alter the types within params.
                // I'm not entirely sure. I'm not aware of any test hitting this.
                let out_params: Vec<_> = params
                    .iter()
                    .map(|(name, t)| (name.clone(), t.monomorphize(params)))
                    .collect();
                AcornValue::Monomorph(*namespace, name.clone(), base_type.clone(), out_params)
            }
        }
    }

    // Replaces a data type with a generic type.
    pub fn genericize(&self, namespace: NamespaceId, name: &str) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.genericize(namespace, name))
            }
            AcornValue::Constant(const_namespace, name, t, params) => {
                // TODO: use params differently? seems wrong
                AcornValue::Constant(
                    *const_namespace,
                    name.clone(),
                    t.genericize(namespace, name),
                    params.clone(),
                )
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.genericize(namespace, name)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.genericize(namespace, name))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter().map(|x| x.genericize(namespace, name)).collect(),
                Box::new(value.genericize(namespace, name)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter().map(|x| x.genericize(namespace, name)).collect(),
                Box::new(value.genericize(namespace, name)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter().map(|x| x.genericize(namespace, name)).collect(),
                Box::new(value.genericize(namespace, name)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.genericize(namespace, name)),
                Box::new(right.genericize(namespace, name)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.genericize(namespace, name))),
            AcornValue::Monomorph(c_namespace, c_name, c_type, params) => {
                if params.len() > 1 {
                    todo!("genericize monomorphs with multiple types");
                }

                let (name, t) = &params[0];
                if t.equals_data_type(namespace, name) {
                    return AcornValue::Constant(
                        *c_namespace,
                        c_name.clone(),
                        c_type.clone(),
                        vec![name.clone()],
                    );
                }

                if t.refers_to(namespace, name) {
                    todo!("genericize monomorphs with complex types");
                }

                self.clone()
            }
        }
    }

    // Finds all polymorphic constants used in this value.
    pub fn find_polymorphic(&self, output: &mut Vec<ConstantKey>) {
        match self {
            AcornValue::Variable(_, _) => {}
            AcornValue::Constant(namespace, name, t, _) => {
                if t.is_parametric() {
                    output.push(ConstantKey {
                        namespace: *namespace,
                        name: name.clone(),
                    });
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
            AcornValue::Binary(_, left, right) => {
                left.find_polymorphic(output);
                right.find_polymorphic(output);
            }
            AcornValue::Not(x) => x.find_polymorphic(output),
            AcornValue::Monomorph(_, _, _, _) => {}
        }
    }

    // Finds all monomorphizations of polymorphic constants in this value.
    // Only handles single generic types.
    pub fn find_monomorphs(&self, output: &mut Vec<(ConstantKey, Vec<(String, AcornType)>)>) {
        match self {
            AcornValue::Variable(_, _) | AcornValue::Constant(_, _, _, _) => {}
            AcornValue::Application(app) => {
                app.function.find_monomorphs(output);
                for arg in &app.args {
                    arg.find_monomorphs(output);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.find_monomorphs(output),
            AcornValue::Binary(_, left, right) => {
                left.find_monomorphs(output);
                right.find_monomorphs(output);
            }
            AcornValue::Not(x) => x.find_monomorphs(output),
            AcornValue::Monomorph(namespace, name, _, params) => {
                let key = ConstantKey {
                    namespace: *namespace,
                    name: name.clone(),
                };
                output.push((key, params.clone()));
            }
        }
    }

    // A value is parametric if any of its components have a parametric type.
    pub fn is_parametric(&self) -> bool {
        match self {
            AcornValue::Variable(_, t) | AcornValue::Constant(_, _, t, _) => t.is_parametric(),

            AcornValue::Application(app) => {
                app.function.is_parametric() || app.args.iter().any(|x| x.is_parametric())
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.is_parametric(),
            AcornValue::Binary(_, left, right) => left.is_parametric() || right.is_parametric(),
            AcornValue::Not(x) => x.is_parametric(),
            AcornValue::Monomorph(_, _, _, _) => false,
        }
    }

    // Converts all the parametrized types to placeholder types.
    pub fn to_placeholder(&self) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.to_placeholder())
            }
            AcornValue::Constant(namespace, name, t, params) => {
                AcornValue::Constant(*namespace, name.clone(), t.to_placeholder(), params.clone())
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
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.to_placeholder()),
                Box::new(right.to_placeholder()),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.to_placeholder())),
            AcornValue::Monomorph(_, _, _, _) => self.clone(),
        }
    }
}
