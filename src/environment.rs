use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::{fmt, io};

use tower_lsp::lsp_types::{Position, Range};

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, AtomId, TypedAtom};
use crate::expression::Expression;
use crate::statement::{Statement, StatementInfo};
use crate::token::{Error, Result, Token, TokenIter, TokenType};

// The Environment takes in a bunch of statements that make sense on their own,
// and combines them while doing typechecking and name resolution.
// It is not responsible for proving anything, but it is responsible for determining which
// things need to be proved, and which statements are usable in which proofs.
// It does not have to be efficient enough to run in the inner loop of the prover.
// It does keep track of names, with the goal of being able to show nice debug information
// for its values and types.
pub struct Environment {
    // The names of the data types that have been defined in this scope.
    // A data type is one that cannot be represented as a functional type.
    // These data types can be stored as ids that are indices into this vector.
    data_types: Vec<String>,

    // Maps the name of a type to the type object.
    type_names: HashMap<String, AcornType>,

    // Maps an identifier name to its type.
    identifier_types: HashMap<String, AcornType>,

    // Maps the name of a constant to information about it.
    // Doesn't handle variables defined on the stack, only ones that will be in scope for the
    // entirety of this environment.
    constants: HashMap<String, ConstantInfo>,

    // Reverse lookup for the information in constants.
    // constants[constant_names[i]] = (i, _)
    constant_names: Vec<String>,

    // How many constants were externally imported at creation time.
    // This includes both previously defined constants, and variables defined in
    // "forall" and "exists" statements (since those are constant inside the block).
    num_imported_constants: AtomId,

    // For variables defined on the stack, we keep track of their depth from the top.
    stack: HashMap<String, AtomId>,

    // The propositions in this environment.
    // This includes every sort of thing that we need to know is true, specific to this environment.
    // This includes theorems, anonymous propositions, and the implicit equalities of
    // definitions.
    // Does not include propositions from parent or child environments.
    // The propositions are fundamentally linear; each may depend on the previous propositions
    // but not on later ones.
    propositions: Vec<Proposition>,

    // The names of theorems in this environment.
    // Does not include the "goal" theorem that this environment is trying to prove.
    theorem_names: HashSet<String>,

    // The region in the source document where a name was defined
    definition_ranges: HashMap<String, Range>,
}

#[derive(Clone)]
struct ConstantInfo {
    // The id of this constant, used for constructing its atom or for the index in constant_names.
    id: AtomId,

    // The definition of this constant.
    // If it doesn't have a definition, this is just an atomic constant.
    value: AcornValue,
}

pub struct Proposition {
    // For a named theorem, this is the name of the theorem.
    // Otherwise, we generate a human-readable best effort.
    pub display_name: Option<String>,

    // Whether this theorem has already been proved structurally.
    // For example, this could be an axiom, or a definition.
    pub proven: bool,

    // A boolean expressing the claim of the proposition.
    // If we have a block and a subenvironment, this represents the "external claim".
    // It is the value we can assume is true, in the outer environment, when everything
    // in the inner environment has been proven.
    pub claim: AcornValue,

    // The body of the proposition, when it has an associated block.
    pub block: Option<Block>,

    // The range in the source document corresponding to this proposition.
    pub range: Range,
}

pub struct Block {
    // The "internal claim" of this block.
    // This claim is defined relative to the block's environment.
    // This claim must be proved inside the block's environment in order for the block to be valid.
    pub claim: Option<AcornValue>,

    // The environment created inside the block.
    pub env: Environment,
}

// A goal and the information used to prove it.
pub struct GoalContext<'a> {
    pub env: &'a Environment,

    // The facts that can be used to prove the goal.
    pub facts: Vec<AcornValue>,

    // A printable name for this goal.
    pub name: String,

    // The goal itself.
    pub goal: AcornValue,

    // The range in the source document corresponding to this goal.
    pub range: Range,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        for (name, acorn_type) in &self.type_names {
            write!(f, "  type {}: {}\n", name, self.type_str(acorn_type))?;
        }
        for (name, acorn_type) in &self.identifier_types {
            write!(f, "  let {}: {}\n", name, self.type_str(acorn_type))?;
        }
        write!(f, "}}")
    }
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            data_types: Vec::new(),
            constant_names: Vec::new(),
            type_names: HashMap::from([("bool".to_string(), AcornType::Bool)]),
            identifier_types: HashMap::new(),
            constants: HashMap::new(),
            num_imported_constants: 0,
            stack: HashMap::new(),
            propositions: Vec::new(),
            theorem_names: HashSet::new(),
            definition_ranges: HashMap::new(),
        }
    }

    // Creates a new environment by copying the names defined in this one.
    // Stack variables in this theorem turn into constant values in the new environment.
    //
    // unbound_claim is the claim for this block, but without any stack variables bound.
    // So if there are stack variables, unbound_claim should be a function that takes those
    // variables to a bool. Otherwise it should just be a bool.
    //
    // theorem_name is the name of the theorem this block is for.
    //
    // Performance is quadratic and therefore bad; using different data structures
    // should improve this when we need to.
    //
    // If this block is an "if" block, we add the if_condition as an available fact.
    fn new_block(
        &self,
        unbound_claim: Option<AcornValue>,
        body: &Vec<Statement>,
        theorem_name: Option<&str>,
        if_condition: Option<(&AcornValue, Range)>,
    ) -> Result<Option<Block>> {
        if body.is_empty() {
            return Ok(None);
        }
        let mut subenv = Environment {
            data_types: self.data_types.clone(),
            constant_names: self.constant_names.clone(),
            type_names: self.type_names.clone(),
            identifier_types: self.identifier_types.clone(),
            constants: self.constants.clone(),
            num_imported_constants: self.constants.len() as AtomId,
            stack: self.stack.clone(),
            propositions: Vec::new(),
            theorem_names: self.theorem_names.clone(),
            definition_ranges: self.definition_ranges.clone(),
        };
        if let Some((fact, range)) = if_condition {
            subenv.add_proposition(Proposition {
                display_name: None,
                proven: true,
                claim: fact.clone(),
                block: None,
                range,
            });
        }
        if let Some(theorem_name) = theorem_name {
            subenv.add_identity_props(theorem_name);
        }

        // Convert stack variables to constant values and bind them to the claim
        let mut names: Vec<&str> = vec![""; self.stack.len()];
        for (name, i) in &self.stack {
            names[*i as usize] = name;
        }
        for name in &names {
            subenv.move_stack_variable_to_constant(name);
        }
        let claim = match unbound_claim {
            None => None,
            Some(unbound_claim) => {
                if names.is_empty() {
                    Some(unbound_claim)
                } else {
                    let args: Vec<_> = names
                        .iter()
                        .map(|name| subenv.get_constant_atom(name).unwrap())
                        .collect();
                    Some(AcornValue::apply(unbound_claim, args))
                }
            }
        };

        for s in body {
            subenv.add_statement(s)?;
        }
        Ok(Some(Block { env: subenv, claim }))
    }

    pub fn load_file(&mut self, filename: &str) -> io::Result<()> {
        let path = if filename.starts_with('.') {
            PathBuf::from(filename)
        } else {
            let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            d.push("math/");
            d.push(filename);
            d
        };
        let contents = std::fs::read_to_string(path)?;
        self.add(&contents);
        Ok(())
    }

    // Adds a proposition.
    fn add_proposition(&mut self, prop: Proposition) {
        // Check if we're adding invalid claims.
        // println!("adding claim: {}", self.value_str(&prop.claim));

        self.propositions.push(prop);
    }

    fn add_data_type(&mut self, name: &str) -> AcornType {
        let data_type = AcornType::Data(self.data_types.len());
        self.data_types.push(name.to_string());
        self.type_names.insert(name.to_string(), data_type.clone());
        data_type
    }

    fn remove_data_type(&mut self, name: &str) {
        self.type_names.remove(name);
    }

    // This creates an atomic value for the next constant, but does not bind it to any name.
    fn next_constant_atom(&self, acorn_type: &AcornType) -> AcornValue {
        let atom = Atom::Constant(self.constant_names.len() as AtomId);
        AcornValue::Atom(TypedAtom {
            atom,
            acorn_type: acorn_type.clone(),
        })
    }

    fn push_stack_variable(&mut self, name: &str, acorn_type: AcornType) {
        self.stack
            .insert(name.to_string(), self.stack.len() as AtomId);
        self.identifier_types.insert(name.to_string(), acorn_type);
    }

    fn pop_stack_variable(&mut self, name: &str) {
        self.stack.remove(name);
        self.identifier_types.remove(name);
    }

    // Adds a proposition, or multiple propositions, to represent the definition of the provided
    // constant.
    fn add_identity_props(&mut self, name: &str) {
        // Currently we can only handle adding props for the most recently defined constant
        let pos = self.constant_names.iter().position(|n| n == name).unwrap();
        assert_eq!(pos + 1, self.constant_names.len());
        let id = pos as AtomId;
        let definition: AcornValue = self.constants[name].value.clone();
        let constant_type_clone = self.identifier_types[name].clone();
        // let definition: AcornValue = definition_clone.unwrap();
        // assert_eq!(definition, v);
        let atom = Box::new(AcornValue::Atom(TypedAtom {
            atom: Atom::Constant(id),
            acorn_type: constant_type_clone,
        }));
        let claim = if let AcornValue::Lambda(acorn_types, return_value) = definition {
            let args: Vec<_> = acorn_types
                .iter()
                .enumerate()
                .map(|(i, acorn_type)| {
                    let atom = Atom::Variable(i as AtomId);
                    AcornValue::Atom(TypedAtom {
                        atom,
                        acorn_type: acorn_type.clone(),
                    })
                })
                .collect();
            let app = AcornValue::Application(FunctionApplication {
                function: atom,
                args,
            });
            AcornValue::ForAll(
                acorn_types,
                Box::new(AcornValue::Equals(Box::new(app), return_value)),
            )
        } else {
            AcornValue::Equals(atom, Box::new(definition))
        };
        let range = self.definition_ranges.get(name).unwrap().clone();

        self.add_proposition(Proposition {
            display_name: None,
            proven: true,
            claim,
            block: None,
            range,
        });
    }

    // Adds a constant.
    // If add_identity_prop is true, this also adds a proposition that the constant is equal to
    // its definition.
    fn add_constant(
        &mut self,
        name: &str,
        constant_type: AcornType,
        definition: Option<AcornValue>,
    ) {
        if self.identifier_types.contains_key(name) {
            panic!("name {} already bound to a type", name);
        }
        if self.constants.contains_key(name) {
            panic!("name {} already bound to a value", name);
        }

        let id = self.constant_names.len() as AtomId;

        let info = ConstantInfo {
            id,
            value: match definition {
                Some(value) => value,
                None => self.next_constant_atom(&constant_type),
            },
        };

        self.identifier_types
            .insert(name.to_string(), constant_type);
        self.constants.insert(name.to_string(), info);
        self.constant_names.push(name.to_string());
    }

    fn move_stack_variable_to_constant(&mut self, name: &str) {
        self.stack.remove(name).unwrap();
        let acorn_type = self.identifier_types.remove(name).unwrap();
        self.add_constant(name, acorn_type, None);
    }

    // This gets the atomic representation of a constant, if this name refers to a constant.
    pub fn get_constant_atom(&self, name: &str) -> Option<AcornValue> {
        let info = self.constants.get(name)?;
        Some(AcornValue::Atom(TypedAtom {
            atom: Atom::Constant(info.id),
            acorn_type: self.identifier_types[name].clone(),
        }))
    }

    // i is the id of a constant
    fn get_defined_value_for_id(&self, i: AtomId) -> Option<&AcornValue> {
        let name = &self.constant_names[i as usize];
        let info = &self.constants[name];
        if let AcornValue::Atom(typed_atom) = &info.value {
            if typed_atom.atom == Atom::Constant(i) {
                // This constant has no definition
                return None;
            }
        }
        Some(&info.value)
    }

    // i is the id of a constant
    fn get_theorem_value_for_id(&self, i: AtomId) -> Option<&AcornValue> {
        let name = &self.constant_names[i as usize];
        if !self.theorem_names.contains(name) {
            return None;
        }
        let info = &self.constants[name];
        if let AcornValue::Atom(typed_atom) = &info.value {
            if typed_atom.atom == Atom::Constant(i) {
                panic!("a theorem has no definition");
            }
        }
        Some(&info.value)
    }

    pub fn get_defined_value(&self, name: &str) -> Option<&AcornValue> {
        let i = self.constant_names.iter().position(|n| n == name)?;
        self.get_defined_value_for_id(i as AtomId)
    }

    // This gets the expanded value of a constant, replacing each defined constant with its definition.
    pub fn get_expanded_value(&self, name: &str) -> Option<AcornValue> {
        let value = self.get_constant_atom(name)?;
        Some(self.expand_constants(&value))
    }

    // Replaces each defined constant with its definition, recursively.
    fn expand_constants(&self, value: &AcornValue) -> AcornValue {
        value.replace_constants_with_values(0, &|i| self.get_defined_value_for_id(i))
    }

    // Replaces each theorem with its definition.
    fn expand_theorems(&self, value: &AcornValue) -> AcornValue {
        value.replace_constants_with_values(0, &|i| self.get_theorem_value_for_id(i))
    }

    pub fn get_theorem_claim(&self, name: &str) -> Option<AcornValue> {
        for prop in &self.propositions {
            if let Some(claim_name) = &prop.display_name {
                if claim_name == name {
                    return Some(self.expand_constants(&prop.claim));
                }
            }
        }
        None
    }

    pub fn get_proposition_name(&self, prop: &Proposition) -> String {
        if let Some(name) = &prop.display_name {
            name.clone()
        } else {
            self.value_str(&prop.claim)
        }
    }

    pub fn get_proposition(&self, name: &str) -> &Proposition {
        for prop in &self.propositions {
            if let Some(claim_name) = &prop.display_name {
                if claim_name == name {
                    return prop;
                }
            }
        }
        panic!("no proposition named {}", name);
    }

    pub fn get_constant_name(&self, id: AtomId) -> &str {
        &self.constant_names[id as usize]
    }

    pub fn type_list_str(&self, types: &[AcornType]) -> String {
        let mut s = "(".to_string();
        for (i, acorn_type) in types.iter().enumerate() {
            if i > 0 {
                s.push_str(", ");
            }
            s.push_str(&self.type_str(acorn_type));
        }
        s.push_str(")");
        s
    }

    pub fn type_str(&self, acorn_type: &AcornType) -> String {
        match acorn_type {
            AcornType::Bool => "bool".to_string(),
            AcornType::Data(i) => self.data_types[*i].to_string(),
            AcornType::Generic(i) => {
                // This return value doesn't mean anything, but it's useful for debugging.
                format!("T{}", i)
            }
            AcornType::Function(function_type) => {
                let s = if function_type.arg_types.len() > 1 {
                    self.type_list_str(&function_type.arg_types)
                } else {
                    self.type_str(&function_type.arg_types[0])
                };
                format!("{} -> {}", s, self.type_str(&function_type.return_type))
            }
            AcornType::ArgList(types) => self.type_list_str(types),
            AcornType::Any => "any".to_string(),
        }
    }

    fn atom_str(&self, atom: &Atom) -> String {
        match atom {
            Atom::True => "true".to_string(),
            Atom::Constant(i) => {
                if let Some(s) = self.constant_names.get(*i as usize) {
                    s.to_string()
                } else {
                    panic!("could not find c{} in {:?}", i, self.constant_names);
                }
            }
            Atom::Skolem(i) => format!("s{}", i),
            Atom::Synthetic(i) => format!("p{}", i),
            Atom::Variable(i) => format!("x{}", i),
            Atom::Anonymous => "_".to_string(),
        }
    }

    fn macro_str_stacked(
        &self,
        macro_name: &str,
        types: &Vec<AcornType>,
        value: &AcornValue,
        stack_size: usize,
    ) -> String {
        let parts: Vec<_> = types
            .iter()
            .enumerate()
            .map(|(i, t)| format!("x{}: {}", i + stack_size, self.type_str(t)))
            .collect();
        let value_str = self.value_str_stacked(value, stack_size + types.len());
        format!("{}({}) {{ {} }}", macro_name, parts.join(", "), value_str)
    }

    fn value_str_stacked(&self, value: &AcornValue, stack_size: usize) -> String {
        match value {
            AcornValue::Atom(a) => self.atom_str(&a.atom),
            AcornValue::Application(app) => {
                let fn_name = self.value_str_stacked(&app.function, stack_size);
                let args: Vec<_> = app
                    .args
                    .iter()
                    .map(|a| self.value_str_stacked(a, stack_size))
                    .collect();
                format!("{}({})", fn_name, args.join(", "))
            }
            AcornValue::Implies(left, right) => format!(
                "({} -> {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Equals(left, right) => format!(
                "({} = {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::NotEquals(left, right) => format!(
                "({} != {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::And(left, right) => format!(
                "({} & {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::Or(left, right) => format!(
                "({} | {})",
                self.value_str_stacked(left, stack_size),
                self.value_str_stacked(right, stack_size)
            ),
            AcornValue::ForAll(types, values) => {
                self.macro_str_stacked("forall", types, values, stack_size)
            }
            AcornValue::Exists(types, values) => {
                self.macro_str_stacked("exists", types, values, stack_size)
            }
            AcornValue::Not(subvalue) => {
                format!("!{}", self.value_str_stacked(subvalue, stack_size))
            }
            AcornValue::Lambda(types, values) => {
                self.macro_str_stacked("lambda", types, values, stack_size)
            }
            _ => format!("unhandled({:?})", value),
        }
    }

    pub fn value_str(&self, value: &AcornValue) -> String {
        self.value_str_stacked(value, 0)
    }

    // actual_type should be non-generic here.
    // expected_type can be generic.
    fn check_type<'a>(
        &self,
        error_token: &Token,
        expected_type: Option<&AcornType>,
        actual_type: &AcornType,
    ) -> Result<()> {
        if let Some(e) = expected_type {
            if !actual_type.instantiates_from(e) {
                return Err(Error::new(
                    error_token,
                    &format!(
                        "expected type {}, but got {}",
                        self.type_str(e),
                        self.type_str(actual_type)
                    ),
                ));
            }
        }
        Ok(())
    }

    // Parses a list of named argument declarations and adds them to the stack.
    fn bind_args<'a, I>(&mut self, declarations: I) -> Result<(Vec<String>, Vec<AcornType>)>
    where
        I: IntoIterator<Item = &'a Expression>,
    {
        let mut names = Vec::new();
        let mut types = Vec::new();
        for declaration in declarations {
            let (name, acorn_type) = self.parse_declaration(declaration)?;
            if self.identifier_types.contains_key(&name) {
                return Err(Error::new(
                    declaration.token(),
                    "cannot redeclare a name in an argument list",
                ));
            }
            if names.contains(&name) {
                return Err(Error::new(
                    declaration.token(),
                    "cannot declare a name twice in one argument list",
                ));
            }
            names.push(name);
            types.push(acorn_type);
        }
        for (name, acorn_type) in names.iter().zip(types.iter()) {
            self.push_stack_variable(name, acorn_type.clone());
        }
        Ok((names, types))
    }

    // There should be a call to unbind_args for every call to bind_args.
    fn unbind_args(&mut self, names: Vec<String>) {
        for name in names {
            self.pop_stack_variable(&name);
        }
    }

    // Binds a possibly-empty list of generic types, along with function arguments.
    // This adds names for both types and arguments to the environment.
    // Internally to this scope, the types work like any other type.
    // Externally, these types are marked as generic.
    // Returns (generic type names, arg names, arg types).
    // Call both unbind_args and unbind_generic_types when done.
    fn bind_templated_args(
        &mut self,
        generic_type_tokens: &[Token],
        args: &[Expression],
        location: &Token,
    ) -> Result<(Vec<String>, Vec<String>, Vec<AcornType>)> {
        let mut generic_type_names: Vec<String> = vec![];
        let mut generic_types: Vec<AcornType> = vec![];
        for token in generic_type_tokens {
            if self.type_names.contains_key(token.text()) {
                return Err(Error::new(
                    token,
                    "cannot redeclare a type in a generic type list",
                ));
            }
            generic_types.push(self.add_data_type(token.text()));
            generic_type_names.push(token.text().to_string());
        }

        let (arg_names, arg_types) = self.bind_args(args)?;

        // Each type has to be used by some argument so that we know how to
        // instantiate the template
        for (i, generic_type) in generic_types.iter().enumerate() {
            if !arg_types.iter().any(|a| a.refers_to(generic_type)) {
                return Err(Error::new(
                    location,
                    &format!(
                        "generic type {} is not used in the function arguments",
                        generic_type_names[i]
                    ),
                ));
            }
        }
        Ok((generic_type_names, arg_names, arg_types))
    }

    // Remove the generic types that were added by bind_generic_types.
    fn unbind_generic_types(&mut self, generic_types: Vec<String>) {
        for name in generic_types {
            self.remove_data_type(&name);
        }
    }

    // self.generic_types contains a list of types that are internally primitive but
    // externally generic.
    // genericize does the internal-to-external conversion, replacing any types in
    // this list with AcornType::Generic values.
    // Do this before unbind_generic_types.
    fn genericize(&self, generic_types: &[String], value: AcornValue) -> AcornValue {
        let mut value = value;
        for (i, name) in generic_types.iter().enumerate() {
            let in_type = self.type_names.get(name).unwrap();
            let out_type = AcornType::Generic(i);
            value = value.replace_type(in_type, &out_type);
        }
        value
    }

    // Evaluates an expression that we expect to be indicating either a type or an arg list
    pub fn evaluate_partial_type_expression(&self, expression: &Expression) -> Result<AcornType> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return Err(Error::new(
                        token,
                        "axiomatic types can only be created at the top level",
                    ));
                }
                if let Some(acorn_type) = self.type_names.get(token.text()) {
                    Ok(acorn_type.clone())
                } else {
                    Err(Error::new(token, "expected type name"))
                }
            }
            Expression::Unary(token, _) => Err(Error::new(
                token,
                "unexpected unary operator in type expression",
            )),
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::RightArrow => {
                    let left_type = self.evaluate_partial_type_expression(left)?;
                    let right_type = self.evaluate_partial_type_expression(right)?;
                    let function_type = FunctionType {
                        arg_types: left_type.into_vec(),
                        return_type: Box::new(right_type),
                    };
                    Ok(AcornType::Function(function_type))
                }
                TokenType::Comma => {
                    // Flatten the types on either side, assumed to be arg lists
                    let mut args = self.evaluate_partial_type_expression(left)?.into_vec();
                    args.extend(self.evaluate_partial_type_expression(right)?.into_vec());
                    Ok(AcornType::ArgList(args))
                }
                _ => Err(Error::new(
                    token,
                    "unexpected binary operator in type expression",
                )),
            },
            Expression::Apply(left, _) => Err(Error::new(
                left.token(),
                "unexpected function application in type expression",
            )),
            Expression::Grouping(_, e, _) => self.evaluate_partial_type_expression(e),
            Expression::Macro(token, _, _, _) => {
                Err(Error::new(token, "unexpected macro in type expression"))
            }
        }
    }

    // Evaluates an expression that indicates a complete type, not an arg list
    pub fn evaluate_type_expression(&self, expression: &Expression) -> Result<AcornType> {
        let acorn_type = self.evaluate_partial_type_expression(expression)?;
        if let AcornType::ArgList(_) = acorn_type {
            Err(Error::new(
                expression.token(),
                "expected a complete type, not arg list",
            ))
        } else {
            Ok(acorn_type)
        }
    }

    // A value expression could be either a value or an argument list.
    // We mutate the environment to account for the stack, so self has to be mut.
    // It might be better to use some fancier data structure.
    // Returns the value along with its type.
    pub fn evaluate_value_expression(
        &mut self,
        expression: &Expression,
        expected_type: Option<&AcornType>,
    ) -> Result<AcornValue> {
        match expression {
            Expression::Identifier(token) => {
                if token.token_type == TokenType::Axiom {
                    return match expected_type {
                        Some(AcornType::ArgList(_)) => Err(Error::new(
                            token,
                            "axiomatic objects cannot be argument lists",
                        )),
                        Some(t) => Ok(self.next_constant_atom(&t)),
                        None => Err(Error::new(
                            token,
                            "axiomatic objects can only be created with known types",
                        )),
                    };
                }

                if token.token_type.is_macro() {
                    return Err(Error::new(token, "macros cannot be used as values"));
                }

                // Check the type for this identifier
                let return_type = match self.identifier_types.get(token.text()) {
                    Some(t) => {
                        self.check_type(token, expected_type, t)?;
                        t.clone()
                    }
                    None => {
                        return Err(Error::new(
                            token,
                            &format!("the name {} is unbound", token.text()),
                        ));
                    }
                };

                // Figure out the value for this identifier
                if let Some(acorn_value) = self.get_constant_atom(token.text()) {
                    Ok(acorn_value)
                } else if let Some(stack_index) = self.stack.get(token.text()) {
                    let atom = Atom::Variable(*stack_index);
                    let typed_atom = TypedAtom {
                        atom,
                        acorn_type: return_type.clone(),
                    };
                    Ok(AcornValue::Atom(typed_atom))
                } else {
                    Err(Error::new(
                        token,
                        "interpreter bug: name is bound but it has no value and is not on the stack",
                    ))
                }
            }
            Expression::Unary(token, expr) => match token.token_type {
                TokenType::Exclam => {
                    self.check_type(token, expected_type, &AcornType::Bool)?;
                    let value = self.evaluate_value_expression(expr, Some(&AcornType::Bool))?;
                    Ok(AcornValue::Not(Box::new(value)))
                }
                _ => Err(Error::new(
                    token,
                    "unexpected unary operator in value expression",
                )),
            },
            Expression::Binary(left, token, right) => {
                match token.token_type {
                    TokenType::Comma => {
                        // Flatten the values on either side, assumed to be arg lists
                        let left_args = self.evaluate_value_expression(left, None)?;
                        let right_args = self.evaluate_value_expression(right, None)?;
                        let mut args = left_args.into_vec();
                        args.extend(right_args.into_vec());
                        Ok(AcornValue::ArgList(args))
                    }
                    TokenType::RightArrow => {
                        self.check_type(token, expected_type, &AcornType::Bool)?;
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::Implies(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::Equals => {
                        self.check_type(token, expected_type, &AcornType::Bool)?;
                        let left_value = self.evaluate_value_expression(left, None)?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&left_value.get_type()))?;
                        Ok(AcornValue::Equals(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::NotEquals => {
                        self.check_type(token, expected_type, &AcornType::Bool)?;
                        let left_value = self.evaluate_value_expression(left, None)?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&left_value.get_type()))?;
                        Ok(AcornValue::NotEquals(
                            Box::new(left_value),
                            Box::new(right_value),
                        ))
                    }
                    TokenType::Ampersand => {
                        self.check_type(token, expected_type, &AcornType::Bool)?;
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::And(Box::new(left_value), Box::new(right_value)))
                    }
                    TokenType::Pipe => {
                        self.check_type(token, expected_type, &AcornType::Bool)?;
                        let left_value =
                            self.evaluate_value_expression(left, Some(&AcornType::Bool))?;
                        let right_value =
                            self.evaluate_value_expression(right, Some(&AcornType::Bool))?;
                        Ok(AcornValue::Or(Box::new(left_value), Box::new(right_value)))
                    }
                    TokenType::Dot => {
                        let name = expression.concatenate_dots()?;
                        if let Some(acorn_value) = self.get_constant_atom(&name) {
                            Ok(acorn_value)
                        } else {
                            return Err(Error::new(
                                token,
                                &format!("the name {} is unbound", name),
                            ));
                        }
                    }
                    _ => Err(Error::new(
                        token,
                        "unhandled binary operator in value expression",
                    )),
                }
            }
            Expression::Apply(function_expr, args_expr) => {
                let function = self.evaluate_value_expression(function_expr, None)?;
                let function_type = function.get_type();

                let function_type = match function_type {
                    AcornType::Function(f) => f,
                    _ => {
                        return Err(Error::new(function_expr.token(), "expected a function"));
                    }
                };
                self.check_type(
                    function_expr.token(),
                    expected_type,
                    &*function_type.return_type,
                )?;

                let arg_exprs = args_expr.flatten_grouped_list()?;

                if function_type.arg_types.len() != arg_exprs.len() {
                    return Err(Error::new(
                        args_expr.token(),
                        &format!(
                            "expected {} arguments, but got {}",
                            function_type.arg_types.len(),
                            arg_exprs.len()
                        ),
                    ));
                }

                let mut args = vec![];
                for (i, arg_expr) in arg_exprs.iter().enumerate() {
                    let arg_type = &function_type.arg_types[i];
                    let arg_value = self.evaluate_value_expression(arg_expr, Some(arg_type))?;
                    args.push(arg_value);
                }

                Ok(AcornValue::Application(FunctionApplication {
                    function: Box::new(function),
                    args,
                }))
            }
            Expression::Grouping(_, e, _) => self.evaluate_value_expression(e, expected_type),
            Expression::Macro(token, args_expr, body, _) => {
                let macro_args = args_expr.flatten_grouped_list()?;
                if macro_args.len() < 1 {
                    return Err(Error::new(
                        args_expr.token(),
                        "macros must have at least one argument",
                    ));
                }
                let (arg_names, arg_types) = self.bind_args(macro_args)?;
                let expected_type = match token.token_type {
                    TokenType::ForAll => Some(&AcornType::Bool),
                    TokenType::Exists => Some(&AcornType::Bool),
                    _ => None,
                };
                let ret_val = match self.evaluate_value_expression(body, expected_type) {
                    Ok(value) => match token.token_type {
                        TokenType::ForAll => Ok(AcornValue::ForAll(arg_types, Box::new(value))),
                        TokenType::Exists => Ok(AcornValue::Exists(arg_types, Box::new(value))),
                        TokenType::Function => Ok(AcornValue::Lambda(arg_types, Box::new(value))),
                        _ => Err(Error::new(token, "expected a macro identifier token")),
                    },
                    Err(e) => Err(e),
                };
                self.unbind_args(arg_names);
                ret_val
            }
        }
    }

    // Parses the "x: Nat" sort of declaration.
    fn parse_declaration(&self, declaration: &Expression) -> Result<(String, AcornType)> {
        match declaration {
            Expression::Binary(left, token, right) => match token.token_type {
                TokenType::Colon => {
                    if left.token().token_type != TokenType::Identifier {
                        return Err(Error::new(
                            left.token(),
                            "expected an identifier in this declaration",
                        ));
                    }
                    let name = left.token().text().to_string();
                    let acorn_type = self.evaluate_type_expression(right)?;
                    Ok((name, acorn_type))
                }
                _ => Err(Error::new(token, "expected a colon in this declaration")),
            },
            _ => Err(Error::new(declaration.token(), "expected a declaration")),
        }
    }

    // Takes a claim that is relative to this environment, and expresses it relative to
    // the parent environment.
    // The caller needs to provide the names of any "forall" variables used in the creation of
    // this block. (Perhaps the environment could just know about that?)
    fn export_claim(
        &self,
        forall_names: &Vec<String>,
        forall_types: Vec<AcornType>,
        inner_claim: &AcornValue,
    ) -> AcornValue {
        // Find the constants that were part of the "forall" that opened the block
        let mut forall_constants: Vec<AtomId> = vec![];
        for name in forall_names {
            if let Some(info) = self.constants.get(name) {
                forall_constants.push(info.id);
            } else {
                panic!("name {} not found in block constants", name);
            }
        }

        // Find any other constants that were defined in the block
        let mut all_constants: Vec<(AtomId, AcornType)> = vec![];
        inner_claim.find_constants_gte(self.num_imported_constants, &mut all_constants);

        // Separate the constants into two groups
        let mut exists_constants = vec![];
        let mut exists_types = vec![];
        for (constant, constant_type) in all_constants {
            if forall_constants.contains(&constant) {
                continue;
            }
            exists_constants.push(constant);
            exists_types.push(constant_type);
        }

        let ordered_constants = forall_constants
            .iter()
            .chain(exists_constants.iter())
            .cloned()
            .collect();

        // Replace all of the constants that only exist in the inside environment
        let replaced = inner_claim.replace_constants_with_variables(&ordered_constants);

        let with_exists = if exists_types.is_empty() {
            replaced
        } else {
            AcornValue::Exists(exists_types, Box::new(replaced))
        };
        let with_forall = if forall_types.is_empty() {
            with_exists
        } else {
            AcornValue::ForAll(forall_types, Box::new(with_exists))
        };

        with_forall
    }

    // Adds a statement to the environment.
    // If the statement has a body, this call creates a sub-environment and adds the body
    // to that sub-environment.
    pub fn add_statement(&mut self, statement: &Statement) -> Result<()> {
        match &statement.statement {
            StatementInfo::Type(ts) => {
                if self.type_names.contains_key(&ts.name) {
                    return Err(Error::new(
                        &ts.type_expr.token(),
                        "type name already defined in this scope",
                    ));
                }
                if ts.type_expr.token().token_type == TokenType::Axiom {
                    self.add_data_type(&ts.name);
                } else {
                    let acorn_type = self.evaluate_type_expression(&ts.type_expr)?;
                    self.type_names.insert(ts.name.to_string(), acorn_type);
                };
                Ok(())
            }

            StatementInfo::Let(ls) => {
                if self.identifier_types.contains_key(&ls.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("variable name '{}' already defined in this scope", ls.name),
                    ));
                }
                let acorn_type = self.evaluate_type_expression(&ls.type_expr)?;
                let acorn_value = self.evaluate_value_expression(&ls.value, Some(&acorn_type))?;
                self.add_constant(&ls.name, acorn_type, Some(acorn_value));
                self.definition_ranges
                    .insert(ls.name.clone(), statement.range());
                self.add_identity_props(&ls.name);
                Ok(())
            }

            StatementInfo::Define(ds) => {
                if self.identifier_types.contains_key(&ds.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("variable name '{}' already defined in this scope", ds.name),
                    ));
                }

                // Calculate the function value
                let (generic_types, arg_names, arg_types) =
                    self.bind_templated_args(&ds.generic_types, &ds.args, &statement.first_token)?;

                let return_type = self.evaluate_type_expression(&ds.return_type)?;
                let fn_value = if ds.return_value.token().token_type == TokenType::Axiom {
                    let new_axiom_type = AcornType::Function(FunctionType {
                        arg_types,
                        return_type: Box::new(return_type),
                    });
                    self.next_constant_atom(&new_axiom_type)
                } else {
                    let return_value =
                        self.evaluate_value_expression(&ds.return_value, Some(&return_type))?;
                    AcornValue::Lambda(arg_types, Box::new(return_value))
                };
                let fn_value = self.genericize(&generic_types, fn_value);
                self.unbind_args(arg_names);
                self.unbind_generic_types(generic_types);

                // Add the function value to the environment
                self.add_constant(&ds.name, fn_value.get_type(), Some(fn_value));
                self.definition_ranges
                    .insert(ds.name.clone(), statement.range());
                self.add_identity_props(&ds.name);
                Ok(())
            }

            StatementInfo::Theorem(ts) => {
                // A theorem has three parts:
                //   * A list of generic types
                //   * A list of arguments that are being universally quantified
                //   * A boolean expression representing a claim of things that are true.
                let (generic_types, arg_names, arg_types) =
                    self.bind_templated_args(&ts.generic_types, &ts.args, &statement.first_token)?;

                // Handle the claim
                let ret_val = match self
                    .evaluate_value_expression(&ts.claim, Some(&AcornType::Bool))
                {
                    Ok(claim_value) => {
                        // The claim of the theorem is what we need to prove
                        let claim = if arg_types.is_empty() {
                            claim_value.clone()
                        } else {
                            AcornValue::ForAll(arg_types.clone(), Box::new(claim_value.clone()))
                        };

                        // The functional value of the theorem is the lambda that
                        // is constantly "true" if the theorem is true
                        let fn_value = if arg_types.is_empty() {
                            claim_value
                        } else {
                            AcornValue::Lambda(arg_types.clone(), Box::new(claim_value))
                        };
                        let fn_value = self.genericize(&generic_types, fn_value);

                        self.add_constant(&ts.name, fn_value.get_type(), Some(fn_value.clone()));

                        // Figure out the range for this theorem definition.
                        // It's smaller than the whole theorem statement because it doesn't
                        // include the proof block.
                        let range = Range {
                            start: statement.first_token.start_pos(),
                            end: ts.claim.last_token().end_pos(),
                        };
                        self.definition_ranges.insert(ts.name.to_string(), range);

                        let unbound_claim = self.get_constant_atom(&ts.name).unwrap();
                        let block =
                            self.new_block(Some(unbound_claim), &ts.body, Some(&ts.name), None)?;
                        let prop = Proposition {
                            display_name: Some(ts.name.to_string()),
                            proven: ts.axiomatic,
                            claim,
                            block,
                            range,
                        };
                        self.add_proposition(prop);
                        self.theorem_names.insert(ts.name.to_string());
                        Ok(())
                    }
                    Err(e) => Err(e),
                };

                self.unbind_args(arg_names);
                self.unbind_generic_types(generic_types);

                ret_val
            }

            StatementInfo::Prop(ps) => {
                let claim = self.evaluate_value_expression(&ps.claim, Some(&AcornType::Bool))?;
                let prop = Proposition {
                    display_name: None,
                    proven: false,
                    claim,
                    block: None,
                    range: statement.range(),
                };
                self.add_proposition(prop);
                Ok(())
            }

            StatementInfo::ForAll(fas) => {
                if fas.body.is_empty() {
                    // ForAll statements with an empty body can just be ignored
                    return Ok(());
                }

                let (forall_names, forall_types) = self.bind_args(&fas.quantifiers)?;

                let block = self.new_block(None, &fas.body, None, None)?.unwrap();

                // The last claim in the block is exported to the outside environment.
                // It may have variables that are bound to the "forall" names, which
                // aren't available in the outside environment, so we need to unbind them.
                let inner_claim: &AcornValue = match block.env.propositions.last() {
                    Some(p) => &p.claim,
                    None => {
                        return Err(Error::new(
                            &statement.first_token,
                            "expected a claim in this block",
                        ));
                    }
                };
                let outer_claim = block
                    .env
                    .export_claim(&forall_names, forall_types, inner_claim);

                let prop = Proposition {
                    display_name: None,
                    proven: false,
                    claim: outer_claim,
                    block: Some(block),
                    range: statement.range(),
                };
                self.add_proposition(prop);
                self.unbind_args(forall_names);
                Ok(())
            }

            StatementInfo::If(is) => {
                if is.body.is_empty() {
                    // If statements with an empty body can just be ignored
                    return Ok(());
                }
                let condition = self.evaluate_value_expression(&is.condition, None)?;
                let range = is.condition.range();
                let block = self
                    .new_block(None, &is.body, None, Some((&condition, range)))?
                    .unwrap();
                let inner_claim: &AcornValue = match block.env.propositions.last() {
                    Some(p) => &p.claim,
                    None => {
                        return Err(Error::new(&is.token, "expected a claim in this block"));
                    }
                };
                let outer_claim = block.env.export_claim(&vec![], vec![], inner_claim);
                let claim = AcornValue::Implies(Box::new(condition), Box::new(outer_claim.clone()));

                let prop = Proposition {
                    display_name: None,
                    proven: false,
                    claim,
                    block: Some(block),
                    range: statement.range(),
                };
                self.add_proposition(prop);
                Ok(())
            }

            StatementInfo::Exists(es) => {
                // We need to prove the general existence claim
                let (quant_names, quant_types) = self.bind_args(&es.quantifiers)?;
                let general_claim_value =
                    self.evaluate_value_expression(&es.claim, Some(&AcornType::Bool))?;
                let general_claim =
                    AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
                self.unbind_args(quant_names.clone());
                let general_prop = Proposition {
                    display_name: None,
                    proven: false,
                    claim: general_claim,
                    block: None,
                    range: statement.range(),
                };
                self.add_proposition(general_prop);

                // Define the quantifiers as constants
                for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
                    self.add_constant(quant_name, quant_type.clone(), None);
                }

                // We can then assume the specific existence claim with the named constants
                let specific_claim =
                    self.evaluate_value_expression(&es.claim, Some(&AcornType::Bool))?;
                let specific_prop = Proposition {
                    display_name: None,
                    proven: true,
                    claim: specific_claim,
                    block: None,
                    range: statement.range(),
                };
                self.add_proposition(specific_prop);

                Ok(())
            }

            StatementInfo::Struct(ss) => {
                if self.type_names.contains_key(&ss.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        "type name already defined in this scope",
                    ));
                }
                let struct_type = self.add_data_type(&ss.name);

                // The member functions take the type itself to a particular member.
                let mut member_fn_names = vec![];
                let mut member_fns = vec![];
                let mut field_types = vec![];
                for (field_name_token, field_type_expr) in &ss.fields {
                    let field_type = self.evaluate_type_expression(&field_type_expr)?;
                    field_types.push(field_type.clone());
                    let member_fn_name = format!("{}.{}", ss.name, field_name_token.text());
                    let member_fn_type = AcornType::Function(FunctionType {
                        arg_types: vec![struct_type.clone()],
                        return_type: Box::new(field_type),
                    });
                    self.add_constant(&member_fn_name, member_fn_type, None);
                    member_fn_names.push(member_fn_name.clone());
                    member_fns.push(self.get_constant_atom(&member_fn_name).unwrap());
                }

                // A "new" function to create one of these struct types.
                let new_fn_name = format!("{}.new", ss.name);
                let new_fn_type = AcornType::Function(FunctionType {
                    arg_types: field_types.clone(),
                    return_type: Box::new(struct_type.clone()),
                });
                self.add_constant(&new_fn_name, new_fn_type, None);
                let new_fn = self.get_constant_atom(&new_fn_name).unwrap();

                // A struct can be recreated by new'ing from its members. Ie:
                // Pair.new(Pair.first(p), Pair.second(p)) = p.
                // This is the "new equation" for a struct type.
                let new_eq_var = AcornValue::Atom(TypedAtom {
                    atom: Atom::Variable(0),
                    acorn_type: struct_type.clone(),
                });
                let new_eq_args = member_fns
                    .iter()
                    .map(|f| {
                        AcornValue::Application(FunctionApplication {
                            function: Box::new(f.clone()),
                            args: vec![new_eq_var.clone()],
                        })
                    })
                    .collect::<Vec<_>>();
                let recreated = AcornValue::Application(FunctionApplication {
                    function: Box::new(new_fn.clone()),
                    args: new_eq_args,
                });
                let new_eq = AcornValue::Equals(Box::new(recreated), Box::new(new_eq_var));
                let new_claim = AcornValue::ForAll(vec![struct_type], Box::new(new_eq));
                self.add_proposition(Proposition {
                    display_name: None,
                    proven: true,
                    claim: new_claim,
                    block: None,
                    range: Range {
                        start: statement.first_token.start_pos(),
                        end: ss.name_token.end_pos(),
                    },
                });

                // There are also formulas for new followed by member functions. Ie:
                // Pair.first(Pair.new(a, b)) = a.
                // These are the "member equations".
                let var_args = (0..ss.fields.len())
                    .map(|i| {
                        AcornValue::Atom(TypedAtom {
                            atom: Atom::Variable(i as AtomId),
                            acorn_type: field_types[i].clone(),
                        })
                    })
                    .collect::<Vec<_>>();
                let new_application = AcornValue::Application(FunctionApplication {
                    function: Box::new(new_fn),
                    args: var_args,
                });
                for i in 0..ss.fields.len() {
                    let (field_name_token, field_type_expr) = &ss.fields[i];
                    let member_fn = &member_fns[i];
                    let member_eq = AcornValue::Equals(
                        Box::new(AcornValue::Application(FunctionApplication {
                            function: Box::new(member_fn.clone()),
                            args: vec![new_application.clone()],
                        })),
                        Box::new(AcornValue::Atom(TypedAtom {
                            atom: Atom::Variable(i as AtomId),
                            acorn_type: field_types[i].clone(),
                        })),
                    );
                    let member_claim = AcornValue::ForAll(field_types.clone(), Box::new(member_eq));
                    self.add_proposition(Proposition {
                        display_name: None,
                        proven: true,
                        claim: member_claim,
                        block: None,
                        range: Range {
                            start: field_name_token.start_pos(),
                            end: field_type_expr.last_token().end_pos(),
                        },
                    });
                }

                Ok(())
            }
        }
    }

    // Adds a possibly multi-line statement to the environment.
    // Panics on failure.
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input);
        if let Err(e) = self.add_tokens(tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    pub fn add_tokens(&mut self, tokens: Vec<Token>) -> Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false) {
                Ok((Some(statement), _)) => {
                    if let Err(e) = self.add_statement(&statement) {
                        return Err(e);
                    }
                }
                Ok((None, _)) => return Ok(()),
                Err(e) => return Err(e),
            }
        }
    }

    // Will return a context for a subenvironment if this theorem has a block
    pub fn get_theorem_context(&self, theorem_name: &str) -> GoalContext {
        for (i, p) in self.propositions.iter().enumerate() {
            if let Some(name) = &p.display_name {
                if name == theorem_name {
                    return self.get_goal_context(&vec![i]);
                }
            }
        }
        panic!("no top-level theorem named {}", theorem_name);
    }

    // The "path" to a proposition is a list of indices to recursively go into env.propositions.
    // This returns a path for all non-axiomatic propositions within this environment,
    // or subenvironments, recursively.
    // The order is "proving order", ie the propositions inside the block are proved before the
    // root proposition of a block.
    pub fn goal_paths(&self) -> Vec<Vec<usize>> {
        self.prepend_goal_paths(&Vec::new())
    }

    // A helper for proposition_paths that prepends 'prepend' to each path.
    fn prepend_goal_paths(&self, prepend: &Vec<usize>) -> Vec<Vec<usize>> {
        let mut paths = Vec::new();
        for (i, prop) in self.propositions.iter().enumerate() {
            if prop.proven {
                continue;
            }
            let path = {
                let mut path = prepend.clone();
                path.push(i);
                path
            };
            if let Some(block) = &prop.block {
                let mut subpaths = block.env.prepend_goal_paths(&path);
                paths.append(&mut subpaths);
                if block.claim.is_some() {
                    // This block has a claim that also needs to be proved
                    paths.push(path);
                }
            } else {
                paths.push(path);
            }
        }
        paths
    }

    // Get a list of facts that are available at a certain path, along with the proposition
    // that should be proved there.
    pub fn get_goal_context(&self, path: &Vec<usize>) -> GoalContext {
        let mut facts = Vec::new();
        let mut env = self;
        let mut it = path.iter().peekable();
        while let Some(i) = it.next() {
            for previous_prop in &env.propositions[0..*i] {
                facts.push(env.expand_theorems(&previous_prop.claim));
            }
            let prop = &env.propositions[*i];
            if let Some(block) = &prop.block {
                if it.peek().is_none() {
                    // This is the last element of the path. It has a block, so we can use the
                    // contents of the block to help prove it.
                    for p in &block.env.propositions {
                        facts.push(block.env.expand_theorems(&p.claim));
                    }
                    let claim = if let Some(claim) = &block.claim {
                        claim
                    } else {
                        panic!("expected a claim at path {:?}", path);
                    };
                    return GoalContext {
                        env: &block.env,
                        facts,
                        name: env.get_proposition_name(&prop),
                        goal: block.env.expand_theorems(claim),
                        range: prop.range,
                    };
                }
                env = &block.env;
            } else {
                // If there's no block on this prop, this must be the last element of the path
                assert!(it.peek().is_none());

                return GoalContext {
                    env: &env,
                    facts,
                    name: env.get_proposition_name(&prop),
                    goal: env.expand_theorems(&prop.claim),
                    range: prop.range,
                };
            }
        }
        panic!("control should not get here");
    }

    pub fn get_goal_context_by_name(&self, name: &str) -> GoalContext {
        let paths = self.goal_paths();
        let mut names = Vec::new();
        for path in paths {
            let context = self.get_goal_context(&path);
            if context.name == name {
                return context;
            }
            names.push(context.name);
        }

        panic!("no context found for {} in:\n{}\n", name, names.join("\n"));
    }

    // Returns the path and goal context for the given location.
    pub fn find_location(
        &self,
        start: Position,
        end: Position,
    ) -> Option<(Vec<usize>, GoalContext)> {
        let paths = self.goal_paths();
        for path in paths {
            let goal_context = self.get_goal_context(&path);
            if goal_context.range.start <= start && goal_context.range.end >= end {
                // This is the goal that contains the cursor.
                return Some((path, goal_context));
            }
        }
        None
    }

    #[cfg(test)]
    fn assert_type_ok(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expression, _) =
            Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine).unwrap();
        match self.evaluate_type_expression(&expression) {
            Ok(_) => {}
            Err(error) => panic!("Error evaluating type expression: {}", error),
        }
    }

    #[cfg(test)]
    fn assert_type_bad(&mut self, input: &str) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let expression = match Expression::parse(&mut tokens, false, |t| t == TokenType::NewLine) {
            Ok((expression, _)) => expression,
            Err(_) => {
                // We expect a bad type so this is fine
                return;
            }
        };
        assert!(self.evaluate_type_expression(&expression).is_err());
    }

    // Expects the given line to be bad
    #[cfg(test)]
    fn bad(&mut self, input: &str) {
        if let Ok(statement) = Statement::parse_str(input) {
            assert!(
                self.add_statement(&statement).is_err(),
                "expected error in: {}",
                input
            );
        }
    }

    // Check that the given name actually does have this type in the environment.
    #[cfg(test)]
    fn typecheck(&mut self, name: &str, type_string: &str) {
        let env_type = match self.identifier_types.get(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(self.type_str(env_type), type_string);
    }

    // Check that the given name has this normalized value in the environment
    #[cfg(test)]
    fn valuecheck(&mut self, name: &str, value_string: &str) {
        let env_value = match self.get_expanded_value(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(self.value_str(&env_value), value_string);
    }

    // Check the name of the given constant
    #[cfg(test)]
    pub fn constantcheck(&mut self, id: usize, name: &str) {
        let constant = match self.constant_names.get(id) {
            Some(c) => c,
            None => panic!("constant {} not found in environment", id),
        };
        assert_eq!(constant, name);
        let info = match self.constants.get(name) {
            Some(info) => info,
            None => panic!(
                "inconsistency: c{} evalutes to {}, for which we have no info",
                id, name
            ),
        };
        assert_eq!(info.id, id as AtomId);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_env_types() {
        let mut env = Environment::new();
        env.assert_type_ok("bool");
        env.assert_type_ok("bool -> bool");
        env.assert_type_ok("bool -> (bool -> bool)");
        env.assert_type_ok("(bool -> bool) -> (bool -> bool)");
        env.assert_type_ok("(bool, bool) -> bool");

        env.assert_type_bad("bool, bool -> bool");
        env.assert_type_bad("(bool, bool)");
    }

    #[test]
    fn test_fn_equality() {
        let mut env = Environment::new();
        env.add("define idb1(x: bool) -> bool = x");
        env.typecheck("idb1", "bool -> bool");
        env.add("define idb2(y: bool) -> bool = y");
        env.typecheck("idb2", "bool -> bool");
        assert_eq!(
            env.get_expanded_value("idb1"),
            env.get_expanded_value("idb2")
        );

        env.add("type Nat: axiom");
        env.add("define idn1(x: Nat) -> Nat = x");
        env.typecheck("idn1", "Nat -> Nat");
        assert_ne!(
            env.get_expanded_value("idb1"),
            env.get_expanded_value("idn1")
        );
    }

    #[test]
    fn test_forall_equality() {
        let mut env = Environment::new();
        env.add("let bsym1: bool = forall(x: bool) { x = x }");
        env.typecheck("bsym1", "bool");
        env.add("let bsym2: bool = forall(y: bool) { y = y }");
        env.typecheck("bsym2", "bool");
        assert_eq!(
            env.get_expanded_value("bsym1"),
            env.get_expanded_value("bsym2")
        );

        env.add("type Nat: axiom");
        env.add("let nsym1: bool = forall(x: Nat) { x = x }");
        env.typecheck("nsym1", "bool");
        assert_ne!(
            env.get_expanded_value("bsym1"),
            env.get_expanded_value("nsym1")
        );
    }

    #[test]
    fn test_exists_equality() {
        let mut env = Environment::new();
        env.add("let bex1: bool = exists(x: bool) { x = x }");
        env.add("let bex2: bool = exists(y: bool) { y = y }");
        assert_eq!(
            env.get_expanded_value("bex1"),
            env.get_expanded_value("bex2")
        );

        env.add("type Nat: axiom");
        env.add("let nex1: bool = exists(x: Nat) { x = x }");
        assert_ne!(
            env.get_expanded_value("bex1"),
            env.get_expanded_value("nex1")
        );
    }

    #[test]
    fn test_arg_binding() {
        let mut env = Environment::new();
        env.bad("define qux(x: bool, x: bool) -> bool = x");
        assert!(env.identifier_types.get("x").is_none());
        env.add("define qux(x: bool, y: bool) -> bool = x");
        env.typecheck("qux", "(bool, bool) -> bool");

        env.bad("theorem foo(x: bool, x: bool): x");
        assert!(env.identifier_types.get("x").is_none());
        env.add("theorem foo(x: bool, y: bool): x");
        env.typecheck("foo", "(bool, bool) -> bool");

        env.bad("let bar: bool = forall(x: bool, x: bool) { x = x }");
        assert!(env.identifier_types.get("x").is_none());
        env.add("let bar: bool = forall(x: bool, y: bool) { x = x }");

        env.bad("let baz: bool = exists(x: bool, x: bool) { x = x }");
        assert!(env.identifier_types.get("x").is_none());
        env.add("let baz: bool = exists(x: bool, y: bool) { x = x }");
    }

    #[test]
    fn test_argless_theorem() {
        let mut env = Environment::new();
        env.add("let b: bool = axiom");
        env.add("theorem foo: b | !b");
        env.valuecheck("foo", "(b | !b)");
    }

    #[test]
    fn test_nested_binding() {
        let mut env = Environment::new();
        env.add("let p: bool = forall(b: bool) { b | !b }");
        env.add("let q: bool = forall(b: bool) { p }");
        env.valuecheck("q", "forall(x0: bool) { forall(x1: bool) { (x1 | !x1) } }");
    }

    #[test]
    fn test_axiomatic_values_distinct() {
        let mut env = Environment::new();
        env.add("let x: bool = axiom");
        env.add("let y: bool = axiom");
        assert_ne!(env.get_expanded_value("x"), env.get_expanded_value("y"));
    }

    #[test]
    fn test_forall_value() {
        let mut env = Environment::new();
        env.add("let p: bool = forall(x: bool) { x | !x }");
        env.valuecheck("p", "forall(x0: bool) { (x0 | !x0) }");
    }

    #[test]
    fn test_inline_function_value() {
        let mut env = Environment::new();
        env.add("define ander(a: bool) -> (bool -> bool) = function(b: bool) { a & b }");
        env.valuecheck(
            "ander",
            "lambda(x0: bool) { lambda(x1: bool) { (x0 & x1) } }",
        );
    }

    #[test]
    fn test_empty_if_block() {
        let mut env = Environment::new();
        env.add("let b: bool = axiom");
        env.add("if b {}");
    }

    #[test]
    fn test_empty_forall_statement() {
        // Allowed as statement but not as an expression.
        let mut env = Environment::new();
        env.add("forall(b: bool) {}");
    }

    #[test]
    fn test_nat_ac_piecewise() {
        let mut env = Environment::new();
        env.add("type Nat: axiom");

        env.bad("type Borf: Gorf");
        env.bad("type Nat: axiom");

        env.add("let 0: Nat = axiom");
        env.valuecheck("0", "0");

        env.bad("let Nat: 0 = axiom");
        env.bad("let axiom: Nat = 0");
        env.bad("let foo: bool = (axiom = axiom)");
        env.bad("let foo: bool = 0");

        env.add("let Suc: Nat -> Nat = axiom");
        env.valuecheck("Suc", "Suc");
        env.add("let 1: Nat = Suc(0)");
        env.valuecheck("1", "Suc(0)");

        env.bad("let 1: Nat = Suc(1)");
        env.bad("let 1: Nat = Borf");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        env.typecheck("suc_injective", "(Nat, Nat) -> bool");
        env.valuecheck(
            "suc_injective",
            "lambda(x0: Nat, x1: Nat) { ((Suc(x0) = Suc(x1)) -> (x0 = x1)) }",
        );

        env.bad("axiom bad_types(x: Nat, y: Nat): x -> y");

        // We don't want failed typechecks to leave the environment in a bad state
        assert!(!env.identifier_types.contains_key("x"));

        env.bad("let foo: bool = Suc(0)");
        env.bad("let foo: Nat = Suc(0 = 0)");
        env.bad("let foo: Nat = Suc(0, 0)");

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        env.valuecheck("suc_neq_zero", "lambda(x0: Nat) { (Suc(x0) != 0) }");

        assert!(env.type_names.contains_key("Nat"));
        assert!(!env.identifier_types.contains_key("Nat"));

        assert!(!env.type_names.contains_key("0"));
        assert!(env.identifier_types.contains_key("0"));

        assert!(!env.type_names.contains_key("1"));
        assert!(env.identifier_types.contains_key("1"));

        assert!(!env.type_names.contains_key("Suc"));
        assert!(env.identifier_types.contains_key("Suc"));

        assert!(!env.type_names.contains_key("foo"));
        assert!(!env.identifier_types.contains_key("foo"));

        env.add(
            "axiom induction(f: Nat -> bool, n: Nat):
            f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> f(n)",
        );
        env.valuecheck("induction", "lambda(x0: Nat -> bool, x1: Nat) { ((x0(0) & forall(x2: Nat) { (x0(x2) -> x0(Suc(x2))) }) -> x0(x1)) }");

        env.bad("theorem foo(x: Nat): 0");
        env.bad("theorem foo(x: Nat): forall(0, 0) { 0 }");
        env.bad("theorem foo(x: Nat): forall(y: Nat) { 0 }");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.typecheck("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.bad("theorem foo(x: Nat): forall(0: Nat) { 0 = 0 }");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );

        env.add("define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)");
        env.typecheck("add", "(Nat, Nat) -> Nat");

        env.add("theorem add_zero_right(a: Nat): add(a, 0) = a");
        env.add("theorem add_zero_left(a: Nat): add(0, a) = a");
        env.add("theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))");
        env.add("theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))");
        env.add("theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)");
        env.add("theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))");
        env.add("theorem not_suc_eq_zero(x: Nat): !(Suc(x) = 0)");
    }

    #[test]
    fn test_nat_ac_together() {
        let mut env = Environment::new();
        env.add(
            r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

let 0: Nat = axiom

let Suc: Nat -> Nat = axiom
let 1: Nat = Suc(0)

axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y

axiom suc_neq_zero(x: Nat): Suc(x) != 0

axiom induction(f: Nat -> bool): f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> forall(n: Nat) { f(n) }

// Ideally a and f would be templated rather than just Nat.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom
axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat): recursion(f, a, Suc(n)) = f(recursion(f, a, n))

define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)

// Now let's have some theorems.

theorem add_zero_right(a: Nat): add(a, 0) = a

theorem add_zero_left(a: Nat): add(0, a) = a

theorem add_suc_right(a: Nat, b: Nat): add(a, Suc(b)) = Suc(add(a, b))

theorem add_suc_left(a: Nat, b: Nat): add(Suc(a), b) = Suc(add(a, b))

theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))
"#,
        );
    }

    #[test]
    fn test_names_in_subenvs() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            theorem foo(a: Nat, b: Nat): a = b by {
                let c: Nat = a
                define d(e: Nat) -> bool = foo(e, b)
            }
            "#,
        );
    }

    #[test]
    fn test_forall_subenv() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            forall(x: Nat) {
                x = x
            }
            "#,
        );
    }

    #[test]
    fn test_if_subenv() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            let 0: Nat = axiom
            if 0 = 0 {
                0 = 0
            }
            "#,
        )
    }

    #[test]
    fn test_exists_exports_names() {
        let mut env = Environment::new();
        env.add(
            r#"
            type Nat: axiom
            define foo(x: Nat) -> bool = axiom
            exists(z: Nat) { foo(z) }
            foo(z)
        "#,
        );
    }

    #[test]
    fn test_if_block_ending_with_exists() {
        let mut env = Environment::new();
        env.add(
            r#"
            let a: bool = axiom
            theorem goal: a by {
                if a {
                    exists(b: bool) { b = b }
                }
            }
            "#,
        );
        for path in env.goal_paths() {
            env.get_goal_context(&path);
        }
    }

    #[test]
    fn test_forall_block_ending_with_exists() {
        let mut env = Environment::new();
        env.add(
            r#"
            let a: bool = axiom
            theorem goal: a by {
                forall(b: bool) {
                    exists(c: bool) { c = c }
                }
            }
            "#,
        );
        for path in env.goal_paths() {
            env.get_goal_context(&path);
        }
    }

    #[test]
    fn test_struct_new_definition() {
        let mut env = Environment::new();
        env.add(
            r#"
        struct BoolPair {
            first: bool
            second: bool
        }
        theorem goal(p: BoolPair): p = BoolPair.new(BoolPair.first(p), BoolPair.second(p))
        "#,
        );
    }

    #[test]
    fn test_templated_types_required_in_function_args() {
        let mut env = Environment::new();
        env.bad("define foo<T>(a: bool) -> bool = a");
    }

    #[test]
    fn test_templated_types_required_in_theorem_args() {
        let mut env = Environment::new();
        env.bad("theorem foo<T>(a: bool): a | !a");
    }
}
