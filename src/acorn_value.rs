use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::atom::AtomId;
use crate::constant_map::ConstantKey;
use crate::module::ModuleId;
use crate::token::TokenType;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FunctionApplication {
    pub function: Box<AcornValue>,
    pub args: Vec<AcornValue>,
}

impl FunctionApplication {
    pub fn get_type(&self) -> AcornType {
        match self.function.get_type() {
            AcornType::Function(ftype) => ftype.applied_type(self.args.len()),
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

impl BinaryOp {
    pub fn token_type(&self) -> TokenType {
        match self {
            BinaryOp::Implies => TokenType::RightArrow,
            BinaryOp::Equals => TokenType::Equals,
            BinaryOp::NotEquals => TokenType::NotEquals,
            BinaryOp::And => TokenType::And,
            BinaryOp::Or => TokenType::Or,
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.token_type().to_str())
    }
}

// Two AcornValue compare to equal if they are structurally identical.
// Comparison doesn't do any evaluations.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AcornValue {
    // A variable that is bound to a value on the stack.
    // Represented by (stack index, type).
    Variable(AtomId, AcornType),

    // A constant, defined in a particular module.
    // (module, constant name, type, type parameters)
    // The type parameters can be empty.
    //
    // The name can have a dot in it, indicating this value is <typename>.<constantname>.
    //
    // When the type parameters are not empty, this indicates a polymorphic constant
    // whose type can still be inferred.
    // This sort of pre-type-inference value should only exist during parsing.
    Constant(ModuleId, String, AcornType, Vec<String>),

    Application(FunctionApplication),

    // A function definition that introduces variables onto the stack.
    Lambda(Vec<AcornType>, Box<AcornValue>),

    // The boolean binary operators are treated specially during inference
    Binary(BinaryOp, Box<AcornValue>, Box<AcornValue>),

    Not(Box<AcornValue>),

    // Quantifiers that introduce variables onto the stack.
    ForAll(Vec<AcornType>, Box<AcornValue>),
    Exists(Vec<AcornType>, Box<AcornValue>),

    // The specialized version of a polymorphic constant.
    // (module, constant name, type, (type parameter, type) mapping)
    // The type is the polymorphic type of the constant.
    // The vector parameter maps parameter names to types they were replaced with.
    // The parameters cannot be empty - that should just be a Constant.
    Specialized(ModuleId, String, AcornType, Vec<(String, AcornType)>),

    // A plain old bool. True or false
    Bool(bool),

    // If-then-else requires all parts: condition, if-value, else-value.
    IfThenElse(Box<AcornValue>, Box<AcornValue>, Box<AcornValue>),
}

// An AcornValue has an implicit stack size that determines what index new stack variables
// will have.
// The Subvalue includes this implicit stack size.
// The stack size of a "root" AcornValue is always zero.
struct Subvalue<'a> {
    value: &'a AcornValue,
    stack_size: usize,
}

// This is a formatting helper, doing a "best effort" that should always display *something*
// but should not be used for generating usable code.
// It may reuse temporary variable names, or use constants that have not been imported.
impl fmt::Display for Subvalue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.value {
            AcornValue::Variable(i, _) => write!(f, "x{}", i),
            AcornValue::Constant(_, name, _, _) => write!(f, "{}", name),
            AcornValue::Application(a) => a.fmt_helper(f, self.stack_size),
            AcornValue::Lambda(args, body) => {
                fmt_binder(f, "function", args, body, self.stack_size)
            }
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
                write!(f, "not {}", Subvalue::new(a, self.stack_size))
            }
            AcornValue::ForAll(args, body) => fmt_binder(f, "forall", args, body, self.stack_size),
            AcornValue::Exists(args, body) => fmt_binder(f, "exists", args, body, self.stack_size),
            AcornValue::Specialized(_, name, _, params) => {
                let types: Vec<_> = params.iter().map(|(_, t)| t.to_string()).collect();
                write!(f, "{}<{}>", name, types.join(", "))
            }
            AcornValue::Bool(b) => write!(f, "{}", b),
            AcornValue::IfThenElse(cond, if_value, else_value) => write!(
                f,
                "if {} {{ {} }} else {{ {} }}",
                Subvalue::new(cond, self.stack_size),
                Subvalue::new(if_value, self.stack_size),
                Subvalue::new(else_value, self.stack_size)
            ),
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
            AcornValue::Application(t) => t.get_type(),
            AcornValue::Lambda(args, return_value) => {
                AcornType::new_functional(args.clone(), return_value.get_type())
            }
            AcornValue::Binary(_, _, _) => AcornType::Bool,
            AcornValue::Not(_) => AcornType::Bool,
            AcornValue::ForAll(_, _) => AcornType::Bool,
            AcornValue::Exists(_, _) => AcornType::Bool,
            AcornValue::Specialized(_, _, c_type, params) => c_type.specialize(&params),
            AcornValue::Bool(_) => AcornType::Bool,
            AcornValue::IfThenElse(_, if_value, _) => if_value.get_type(),
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

    pub fn new_implies(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Implies, Box::new(left), Box::new(right))
    }

    pub fn new_equals(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Equals, Box::new(left), Box::new(right))
    }

    pub fn new_not_equals(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::NotEquals, Box::new(left), Box::new(right))
    }

    pub fn new_and(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::And, Box::new(left), Box::new(right))
    }

    pub fn new_or(left: AcornValue, right: AcornValue) -> AcornValue {
        AcornValue::Binary(BinaryOp::Or, Box::new(left), Box::new(right))
    }

    // Make a Constant or a Specialized depending on whether we have params.
    pub fn new_specialized(
        module: ModuleId,
        name: String,
        constant_type: AcornType,
        params: Vec<(String, AcornType)>,
    ) -> AcornValue {
        if params.is_empty() {
            AcornValue::Constant(module, name, constant_type, vec![])
        } else {
            AcornValue::Specialized(module, name, constant_type, params)
        }
    }

    pub fn is_lambda(&self) -> bool {
        match self {
            AcornValue::Lambda(_, _) => true,
            _ => false,
        }
    }

    // Whether this value can be converted to a term, rather than requiring a literal or clause.
    // Terms can have no boolean operators, lambdas, etc.
    pub fn is_term(&self) -> bool {
        match self {
            AcornValue::Variable(_, _) => true,
            AcornValue::Constant(_, _, _, _) => true,
            AcornValue::Application(app) => {
                app.args.iter().all(|x| x.is_term()) && app.function.is_term()
            }
            AcornValue::Lambda(_, _) => false,
            AcornValue::Binary(_, _, _) => false,
            AcornValue::Not(_) => false,
            AcornValue::ForAll(_, _) => false,
            AcornValue::Exists(_, _) => false,
            AcornValue::Specialized(_, _, _, _) => true,

            // Bit of a weird case. "true" is a term but "false" is not.
            AcornValue::Bool(value) => *value,

            AcornValue::IfThenElse(_, _, _) => false,
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
            AcornValue::Bool(b) => AcornValue::Bool(!b),
            _ => AcornValue::Not(Box::new(self)),
        }
    }

    // Negates, but pushes the negation inwards when possible.
    pub fn pretty_negate(self) -> AcornValue {
        match self {
            AcornValue::Not(x) => *x,
            AcornValue::Binary(BinaryOp::Equals, x, y) => {
                AcornValue::Binary(BinaryOp::NotEquals, x, y)
            }
            AcornValue::Binary(BinaryOp::NotEquals, x, y) => {
                AcornValue::Binary(BinaryOp::Equals, x, y)
            }
            AcornValue::Binary(BinaryOp::Or, x, y) => {
                AcornValue::new_and(x.pretty_negate(), y.pretty_negate())
            }
            AcornValue::Binary(BinaryOp::And, x, y) => {
                AcornValue::new_or(x.pretty_negate(), y.pretty_negate())
            }
            AcornValue::Binary(BinaryOp::Implies, x, y) => {
                AcornValue::new_and(*x, y.pretty_negate())
            }
            AcornValue::Bool(b) => AcornValue::Bool(!b),
            AcornValue::ForAll(quants, value) => {
                AcornValue::new_exists(quants, value.pretty_negate())
            }
            AcornValue::Exists(quants, value) => {
                AcornValue::new_forall(quants, value.pretty_negate())
            }
            _ => AcornValue::Not(Box::new(self)),
        }
    }

    // If this value can be represented as just a term, with perhaps a negation, return it.
    // Removes negation if it's present.
    // The boolean is whether the term was negated.
    fn as_simple_boolean_term(&self) -> Option<(bool, AcornValue)> {
        match self {
            AcornValue::Not(x) => Some((true, *x.clone())),
            AcornValue::Binary(..) | AcornValue::ForAll(..) | AcornValue::Exists(..) => None,
            AcornValue::Bool(b) => Some((*b, AcornValue::Bool(true))),
            _ => Some((false, self.clone())),
        }
    }

    // Moves negation inward for a boolean comparison.
    // left and right should both be verified to be bools, when this is called.
    // We want as close to CNF as possible.
    // So the order outside-in goes: and, or, negates.
    fn boolean_comparison(
        left: AcornValue,
        right: AcornValue,
        allow_bool_eq: bool,
        negate: bool,
    ) -> AcornValue {
        if allow_bool_eq {
            if let Some((left_negated, left_term)) = left.as_simple_boolean_term() {
                if let Some((right_negated, right_term)) = right.as_simple_boolean_term() {
                    let final_negated = negate ^ left_negated ^ right_negated;
                    if !final_negated {
                        return AcornValue::Binary(
                            BinaryOp::Equals,
                            Box::new(left_term),
                            Box::new(right_term),
                        );
                    }
                }
            }
        }
        let negative_left = left.clone().move_negation_inwards(false, true);
        let negative_right = right.clone().move_negation_inwards(false, true);
        let positive_left = left.move_negation_inwards(false, false);
        let positive_right = right.move_negation_inwards(false, false);
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
    // If 'allow_bool_eq' is set then it's okay to return something like
    //   <bool expr> = <bool expr>
    // This is useful because it allows rewrites.
    // If 'negate' is set then we also negate this expression.
    // See https://www.csd.uwo.ca/~lkari/prenex.pdf
    // page 3, steps 1 and 2.
    pub fn move_negation_inwards(self, allow_bool_eq: bool, negate: bool) -> AcornValue {
        match self {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                // (left -> right) is equivalent to (!left | right)
                let equivalent =
                    AcornValue::Binary(BinaryOp::Or, Box::new(AcornValue::Not(left)), right);
                equivalent.move_negation_inwards(false, negate)
            }
            AcornValue::Binary(BinaryOp::And, left, right) => {
                if negate {
                    // !(left & right) is equivalent to (!left | !right)
                    let equivalent = AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(AcornValue::Not(left)),
                        Box::new(AcornValue::Not(right)),
                    );
                    equivalent.move_negation_inwards(false, false)
                } else {
                    AcornValue::Binary(
                        BinaryOp::And,
                        Box::new(left.move_negation_inwards(false, false)),
                        Box::new(right.move_negation_inwards(false, false)),
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
                    equivalent.move_negation_inwards(false, false)
                } else {
                    AcornValue::Binary(
                        BinaryOp::Or,
                        Box::new(left.move_negation_inwards(false, false)),
                        Box::new(right.move_negation_inwards(false, false)),
                    )
                }
            }
            AcornValue::Not(x) => x.move_negation_inwards(allow_bool_eq, !negate),
            AcornValue::ForAll(quants, value) => {
                if negate {
                    // "not forall x, foo(x)" is equivalent to "exists x, not foo(x)"
                    AcornValue::Exists(
                        quants,
                        Box::new(value.move_negation_inwards(allow_bool_eq, true)),
                    )
                } else {
                    AcornValue::ForAll(
                        quants,
                        Box::new(value.move_negation_inwards(allow_bool_eq, false)),
                    )
                }
            }
            AcornValue::Exists(quants, value) => {
                if negate {
                    // "not exists x, foo(x)" is equivalent to "forall x, not foo(x)"
                    AcornValue::ForAll(
                        quants,
                        Box::new(value.move_negation_inwards(allow_bool_eq, true)),
                    )
                } else {
                    AcornValue::Exists(
                        quants,
                        Box::new(value.move_negation_inwards(allow_bool_eq, false)),
                    )
                }
            }
            AcornValue::Binary(BinaryOp::Equals, left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, allow_bool_eq, negate)
                } else {
                    AcornValue::Binary(BinaryOp::Equals, left, right).maybe_negate(negate)
                }
            }
            AcornValue::Binary(BinaryOp::NotEquals, left, right) => {
                if left.get_type() == AcornType::Bool {
                    AcornValue::boolean_comparison(*left, *right, allow_bool_eq, !negate)
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
        values: &[AcornValue],
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
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.bind_values(first_binding_index, stack_size, values)),
                Box::new(if_value.bind_values(first_binding_index, stack_size, values)),
                Box::new(else_value.bind_values(first_binding_index, stack_size, values)),
            ),
            AcornValue::Constant(_, _, _, _)
            | AcornValue::Specialized(_, _, _, _)
            | AcornValue::Bool(_) => self,
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
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.insert_stack(index, increment)),
                Box::new(if_value.insert_stack(index, increment)),
                Box::new(else_value.insert_stack(index, increment)),
            ),
            AcornValue::Constant(_, _, _, _)
            | AcornValue::Specialized(_, _, _, _)
            | AcornValue::Bool(_) => self,
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
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.replace_function_equality(stack_size)),
                Box::new(if_value.replace_function_equality(stack_size)),
                Box::new(else_value.replace_function_equality(stack_size)),
            ),
            AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Specialized(_, _, _, _)
            | AcornValue::Bool(_) => self.clone(),
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
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.expand_lambdas(stack_size)),
                Box::new(if_value.expand_lambdas(stack_size)),
                Box::new(else_value.expand_lambdas(stack_size)),
            ),
            AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Specialized(_, _, _, _)
            | AcornValue::Bool(_) => self,
        }
    }

    // The general idea is that these expressions are equivalent:
    //
    //   foo(if a then b else c)
    //   if a then foo(b) else foo(c)
    //
    // extract_one_if tries to use this equivalence to extract one "if" statement, and return
    // Some((condition, if_value, else_value))
    //
    // This function is very closely tied to replace_if and only has to work with the sorts of
    // values it is called on, those at the boundary between boolean and non-boolean values.
    fn extract_one_if(&self) -> Option<(AcornValue, AcornValue, AcornValue)> {
        match self {
            AcornValue::Application(app) => {
                if let Some((a, b, c)) = app.function.extract_one_if() {
                    // We can extract the if from the function
                    Some((
                        a,
                        AcornValue::Application(FunctionApplication {
                            function: Box::new(b),
                            args: app.args.clone(),
                        }),
                        AcornValue::Application(FunctionApplication {
                            function: Box::new(c),
                            args: app.args.clone(),
                        }),
                    ))
                } else {
                    // We can't extract the if from the function, but we can extract it from the args
                    for (i, arg) in app.args.iter().enumerate() {
                        if let Some((a, b, c)) = arg.extract_one_if() {
                            // We can extract the if from this arg
                            let mut new_args = app.args.clone();
                            new_args[i] = b;
                            let b_args = new_args.clone();
                            new_args[i] = c;
                            let c_args = new_args;
                            return Some((
                                a,
                                AcornValue::Application(FunctionApplication {
                                    function: app.function.clone(),
                                    args: b_args,
                                }),
                                AcornValue::Application(FunctionApplication {
                                    function: app.function.clone(),
                                    args: c_args,
                                }),
                            ));
                        }
                    }
                    None
                }
            }

            AcornValue::IfThenElse(a, b, c) => Some((*a.clone(), *b.clone(), *c.clone())),

            AcornValue::Binary(op, left, right) => {
                if let Some((a, b, c)) = left.extract_one_if() {
                    Some((
                        a,
                        AcornValue::Binary(*op, Box::new(b), right.clone()),
                        AcornValue::Binary(*op, Box::new(c), right.clone()),
                    ))
                } else if let Some((a, b, c)) = right.extract_one_if() {
                    Some((
                        a,
                        AcornValue::Binary(*op, left.clone(), Box::new(b)),
                        AcornValue::Binary(*op, left.clone(), Box::new(c)),
                    ))
                } else {
                    None
                }
            }

            AcornValue::Not(_)
            | AcornValue::ForAll(_, _)
            | AcornValue::Exists(_, _)
            | AcornValue::Bool(_)
            | AcornValue::Lambda(_, _)
            | AcornValue::Variable(_, _)
            | AcornValue::Constant(_, _, _, _)
            | AcornValue::Specialized(_, _, _, _) => None,
        }
    }

    // For an "if" among three boolean values, replace it with an equivalent value that
    // doesn't use if-then-else nodes.
    fn new_if_replacement(a: AcornValue, b: AcornValue, c: AcornValue) -> AcornValue {
        let (a, b, c) = (a.replace_if(), b.replace_if(), c.replace_if());
        let not_a_imp_c = AcornValue::new_implies(a.clone().negate(), c);
        let a_imp_b = AcornValue::new_implies(a, b);
        AcornValue::new_and(a_imp_b, not_a_imp_c)
    }

    // Replaces all "if" nodes by extracting them into boolean values and then replacing them.
    // This should only be called on boolean values.
    pub fn replace_if(self) -> AcornValue {
        assert_eq!(self.get_type(), AcornType::Bool);

        match self {
            AcornValue::Binary(op, left, right) if (left.get_type() == AcornType::Bool) => {
                // The subvalues are still boolean, so we can recurse.
                let new_left = left.replace_if();
                let new_right = right.replace_if();
                return AcornValue::Binary(op, Box::new(new_left), Box::new(new_right));
            }

            AcornValue::Binary(_, _, _) | AcornValue::Application(_) => match self.extract_one_if()
            {
                Some((a, b, c)) => AcornValue::new_if_replacement(a, b, c),
                None => self,
            },

            AcornValue::IfThenElse(a, b, c) => AcornValue::new_if_replacement(*a, *b, *c),

            AcornValue::Not(value) => AcornValue::Not(Box::new(value.replace_if())),
            AcornValue::ForAll(quants, value) => {
                AcornValue::ForAll(quants, Box::new(value.replace_if()))
            }
            AcornValue::Exists(quants, value) => {
                AcornValue::Exists(quants, Box::new(value.replace_if()))
            }
            AcornValue::Lambda(args, value) => {
                AcornValue::Lambda(args, Box::new(value.replace_if()))
            }
            _ => self,
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
        replacer: &impl Fn(ModuleId, &str) -> Option<&'a AcornValue>,
    ) -> AcornValue {
        match self {
            AcornValue::Constant(module, name, _, params) => {
                if let Some(replacement) = replacer(*module, name) {
                    assert!(params.is_empty());
                    // First we need to make the replacement use the correct stack variables
                    let shifted = replacement.clone().insert_stack(0, stack_size);
                    // Then we need to recursively replace constants in the replacement
                    return shifted.replace_constants_with_values(stack_size, replacer);
                }
                self.clone()
            }
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => self.clone(),
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
            AcornValue::Specialized(module, name, _, params) => {
                if let Some(replacement) = replacer(*module, name) {
                    // We do need to replace this
                    replacement.specialize(params)
                } else {
                    // We don't need to replace this
                    self.clone()
                }
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.replace_constants_with_values(stack_size, replacer)),
                Box::new(if_value.replace_constants_with_values(stack_size, replacer)),
                Box::new(else_value.replace_constants_with_values(stack_size, replacer)),
            ),
        }
    }

    // For constants in this module, replace them with a variable id if they are in the constants map.
    pub fn replace_constants_with_vars(
        &self,
        module: ModuleId,
        constants: &HashMap<String, AtomId>,
    ) -> AcornValue {
        match self {
            AcornValue::Variable(_, _) => self.clone(),
            AcornValue::Constant(m, name, t, params) => {
                if *m == module {
                    if let Some(i) = constants.get(name) {
                        assert!(params.is_empty());
                        return AcornValue::Variable(*i, t.clone());
                    }
                }
                self.clone()
            }
            AcornValue::Application(fa) => {
                let new_function = fa.function.replace_constants_with_vars(module, constants);
                let new_args = fa
                    .args
                    .iter()
                    .map(|x| x.replace_constants_with_vars(module, constants))
                    .collect();
                AcornValue::Application(FunctionApplication {
                    function: Box::new(new_function),
                    args: new_args,
                })
            }
            AcornValue::Lambda(arg_types, value) => {
                let new_value = value.replace_constants_with_vars(module, constants);
                AcornValue::Lambda(arg_types.clone(), Box::new(new_value))
            }
            AcornValue::Binary(op, left, right) => {
                let new_left = left.replace_constants_with_vars(module, constants);
                let new_right = right.replace_constants_with_vars(module, constants);
                AcornValue::Binary(*op, Box::new(new_left), Box::new(new_right))
            }
            AcornValue::Not(x) => {
                AcornValue::Not(Box::new(x.replace_constants_with_vars(module, constants)))
            }
            AcornValue::ForAll(quants, value) => {
                let new_value = value.replace_constants_with_vars(module, constants);
                AcornValue::ForAll(quants.clone(), Box::new(new_value))
            }
            AcornValue::Exists(quants, value) => {
                let new_value = value.replace_constants_with_vars(module, constants);
                AcornValue::Exists(quants.clone(), Box::new(new_value))
            }
            AcornValue::Specialized(_, _, _, _) => panic!("can this happen?"),
            AcornValue::Bool(_) => self.clone(),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.replace_constants_with_vars(module, constants)),
                Box::new(if_value.replace_constants_with_vars(module, constants)),
                Box::new(else_value.replace_constants_with_vars(module, constants)),
            ),
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
            AcornValue::Constant(_, _, _, params) => {
                if !params.is_empty() {
                    Err("should be no polymorphs during validation".to_string())
                } else {
                    Ok(())
                }
            }
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
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.validate_against_stack(stack)?;
                if_value.validate_against_stack(stack)?;
                else_value.validate_against_stack(stack)
            }
            AcornValue::Not(x) => x.validate_against_stack(stack),
            AcornValue::Specialized(_, _, _, _) | AcornValue::Bool(_) => Ok(()),
        }
    }

    // Replace some parametric types with other types.
    pub fn specialize(&self, params: &[(String, AcornType)]) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.specialize(params))
            }
            AcornValue::Constant(_, _, _, c_params) => {
                assert!(c_params.is_empty());
                self.clone()
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.specialize(params)),
                args: app.args.iter().map(|x| x.specialize(params)).collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.specialize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.specialize(params)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.specialize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.specialize(params)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.specialize(params))
                    .collect::<Vec<_>>(),
                Box::new(value.specialize(params)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.specialize(params)),
                Box::new(right.specialize(params)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.specialize(params)),
                Box::new(if_value.specialize(params)),
                Box::new(else_value.specialize(params)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.specialize(params))),
            AcornValue::Specialized(module, name, base_type, in_params) => {
                let out_params: Vec<_> = in_params
                    .iter()
                    .map(|(name, t)| (name.clone(), t.specialize(params)))
                    .collect();
                AcornValue::Specialized(*module, name.clone(), base_type.clone(), out_params)
            }
            AcornValue::Bool(_) => self.clone(),
        }
    }

    // parametrize should only be called on concrete types.
    // It replaces every data type with the given module and name with a type parameter.
    pub fn parametrize(&self, module: ModuleId, type_names: &[String]) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.parametrize(module, type_names))
            }
            AcornValue::Constant(_, _, _, params) => {
                if !params.is_empty() {
                    panic!("we should only be genericizing concrete values");
                }
                self.clone()
            }
            AcornValue::Application(app) => AcornValue::Application(FunctionApplication {
                function: Box::new(app.function.parametrize(module, type_names)),
                args: app
                    .args
                    .iter()
                    .map(|x| x.parametrize(module, type_names))
                    .collect(),
            }),
            AcornValue::Lambda(args, value) => AcornValue::Lambda(
                args.iter()
                    .map(|x| x.parametrize(module, type_names))
                    .collect(),
                Box::new(value.parametrize(module, type_names)),
            ),
            AcornValue::ForAll(args, value) => AcornValue::ForAll(
                args.iter()
                    .map(|x| x.parametrize(module, type_names))
                    .collect(),
                Box::new(value.parametrize(module, type_names)),
            ),
            AcornValue::Exists(args, value) => AcornValue::Exists(
                args.iter()
                    .map(|x| x.parametrize(module, type_names))
                    .collect(),
                Box::new(value.parametrize(module, type_names)),
            ),
            AcornValue::Binary(op, left, right) => AcornValue::Binary(
                *op,
                Box::new(left.parametrize(module, type_names)),
                Box::new(right.parametrize(module, type_names)),
            ),
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.parametrize(module, type_names)),
                Box::new(if_value.parametrize(module, type_names)),
                Box::new(else_value.parametrize(module, type_names)),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.parametrize(module, type_names))),
            AcornValue::Specialized(c_module, c_name, c_type, params) => {
                // New way
                let mut out_params = vec![];
                for (param_name, t) in params {
                    out_params.push((param_name.clone(), t.parametrize(module, type_names)));
                }
                AcornValue::Specialized(*c_module, c_name.clone(), c_type.clone(), out_params)
            }
            AcornValue::Bool(_) => self.clone(),
        }
    }

    // Whether anything in this value has unbound type parameters.
    pub fn is_parametric(&self) -> bool {
        match self {
            AcornValue::Variable(_, t) => t.is_parametric(),
            AcornValue::Constant(_, _, t, _) => t.is_parametric(),
            AcornValue::Application(app) => {
                app.function.is_parametric() || app.args.iter().any(|x| x.is_parametric())
            }
            AcornValue::Lambda(args, value)
            | AcornValue::ForAll(args, value)
            | AcornValue::Exists(args, value) => {
                args.iter().any(|x| x.is_parametric()) || value.is_parametric()
            }
            AcornValue::Binary(_, left, right) => left.is_parametric() || right.is_parametric(),
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.is_parametric() || if_value.is_parametric() || else_value.is_parametric()
            }
            AcornValue::Not(x) => x.is_parametric(),
            AcornValue::Specialized(_, _, _, params) => {
                params.iter().any(|(_, t)| t.is_parametric())
            }
            AcornValue::Bool(_) => false,
        }
    }

    // Finds all specialized constants used in this value that still have parameters in them.
    pub fn find_parametric(&self, output: &mut Vec<(ConstantKey, Vec<(String, AcornType)>)>) {
        match self {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(_, _, _, params) => {
                assert!(params.is_empty());
            }
            AcornValue::Application(app) => {
                app.function.find_parametric(output);
                for arg in &app.args {
                    arg.find_parametric(output);
                }
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value) => value.find_parametric(output),
            AcornValue::Binary(_, left, right) => {
                left.find_parametric(output);
                right.find_parametric(output);
            }
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.find_parametric(output);
                if_value.find_parametric(output);
                else_value.find_parametric(output);
            }
            AcornValue::Not(x) => x.find_parametric(output),
            AcornValue::Specialized(module, name, _, params) => {
                for (_, t) in params {
                    if t.is_parametric() {
                        let key = ConstantKey {
                            module: *module,
                            name: name.clone(),
                        };
                        output.push((key, params.clone()));
                        break;
                    }
                }
            }
        }
    }

    // Finds all monomorphizations of polymorphic constants in this value.
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
            AcornValue::IfThenElse(cond, if_value, else_value) => {
                cond.find_monomorphs(output);
                if_value.find_monomorphs(output);
                else_value.find_monomorphs(output);
            }
            AcornValue::Not(x) => x.find_monomorphs(output),
            AcornValue::Specialized(module, name, _, params) => {
                for (_, t) in params {
                    if t.is_parametric() {
                        // This is not a monomorphization
                        return;
                    }
                }
                let key = ConstantKey {
                    module: *module,
                    name: name.clone(),
                };
                output.push((key, params.clone()));
            }
            AcornValue::Bool(_) => {}
        }
    }

    // Converts all the parametrized types to placeholder types.
    pub fn to_placeholder(&self) -> AcornValue {
        match self {
            AcornValue::Variable(i, var_type) => {
                AcornValue::Variable(*i, var_type.to_placeholder())
            }
            AcornValue::Constant(module, name, t, params) => {
                AcornValue::Constant(*module, name.clone(), t.to_placeholder(), params.clone())
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
            AcornValue::IfThenElse(cond, if_value, else_value) => AcornValue::IfThenElse(
                Box::new(cond.to_placeholder()),
                Box::new(if_value.to_placeholder()),
                Box::new(else_value.to_placeholder()),
            ),
            AcornValue::Not(x) => AcornValue::Not(Box::new(x.to_placeholder())),
            AcornValue::Specialized(_, _, _, _) | AcornValue::Bool(_) => self.clone(),
        }
    }

    // Negates a goal proposition and separates it into the types of its assumptions.
    // (hypothetical, counterfactual)
    // Hypotheticals are assumed to be true in a "by" block when proving something, in the
    // sense that you can write more statements that depend on the hypotheticals.
    // Counterfactuals are used by the prover to find a contradiction, but cannot be used
    // in the direct reasoning of the code.
    pub fn negate_goal(self) -> (Option<AcornValue>, AcornValue) {
        match self {
            AcornValue::Binary(BinaryOp::Implies, left, right) => (Some(*left), right.negate()),
            _ => (None, self.negate()),
        }
    }

    // Combine a bunch of values with the given binary operator.
    pub fn reduce(op: BinaryOp, args: Vec<AcornValue>) -> AcornValue {
        if args.is_empty() {
            panic!("cannot reduce with no arguments");
        }

        let mut answer = None;
        for arg in args {
            if let Some(a) = answer {
                answer = Some(AcornValue::Binary(op, Box::new(a), Box::new(arg)));
            } else {
                answer = Some(arg);
            }
        }
        answer.unwrap()
    }

    // If this value is a member function or member variable of the given type, return its name.
    pub fn is_member(&self, class: &AcornType) -> Option<String> {
        match &self {
            AcornValue::Constant(module_id, name, _, _) => {
                let parts = name.split('.').collect::<Vec<_>>();
                if parts.len() != 2 {
                    return None;
                }
                let type_name = parts[0];
                let member_name = parts[1];
                let type_id = AcornType::Data(*module_id, type_name.to_string());
                if type_id == *class {
                    Some(member_name.to_string())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn is_named_function_call(&self) -> Option<(ModuleId, &str)> {
        match self {
            AcornValue::Application(fa) => match &*fa.function {
                AcornValue::Constant(module, name, _, _) => Some((*module, name)),
                AcornValue::Specialized(module, name, _, _) => Some((*module, name)),
                _ => None,
            },
            _ => None,
        }
    }
}
