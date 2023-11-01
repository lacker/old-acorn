use std::collections::HashMap;

use tower_lsp::lsp_types::{Position, Range};

use crate::acorn_type::{AcornType, FunctionType};
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::AtomId;
use crate::binding_map::BindingMap;
use crate::goal_context::GoalContext;
use crate::namespace::NamespaceId;
use crate::project::{LoadError, Project};
use crate::statement::{Statement, StatementInfo};
use crate::token::{Error, Result, Token, TokenIter, TokenType};

// The Environment takes Statements as input and processes them.
// It does not prove anything directly, but it is responsible for determining which
// things need to be proved, and which statements are usable in which proofs.
// It creates subenvironments for nested blocks.
// It does not have to be efficient enough to run in the inner loop of the prover.
pub struct Environment {
    pub namespace: NamespaceId,

    // What all the names mean in this environment
    pub bindings: BindingMap,

    // The propositions in this environment.
    // This includes every sort of thing that we need to know is true, specific to this environment.
    // This includes theorems, anonymous propositions, and the implicit equalities of
    // definitions.
    // Does not include propositions from parent or child environments.
    // The propositions are fundamentally linear; each may depend on the previous propositions
    // but not on later ones.
    propositions: Vec<Proposition>,

    // The region in the source document where a name was defined
    definition_ranges: HashMap<String, Range>,
}

pub struct Proposition {
    // For a named theorem, this is the name of the theorem.
    // Otherwise, we generate a human-readable best effort.
    pub display_name: Option<String>,

    // Whether this theorem has already been proved structurally.
    // For example, this could be an axiom, or a definition.
    pub proven: bool,

    // A boolean expressing the claim of the proposition.
    // If this proposition has a block, this represents the "external claim".
    // It is the value we can assume is true, in the outer environment, when everything
    // in the inner environment has been proven.
    // Besides the claim, nothing else from the block is visible externally.
    //
    // This claim needs to be proved when proven is false, and there is no block.
    pub claim: AcornValue,

    // The body of the proposition, when it has an associated block.
    // When there is a block, proving every proposition in the block implies that the
    // claim is proven as well.
    block: Option<Block>,

    // The range in the source document corresponding to this proposition.
    pub range: Range,
}

// Proofs are structured into blocks.
// The environment specific to this block can have a bunch of propositions that need to be
// proved, along with helper statements to express those propositions, but they are not
// visible to the outside world.
struct Block {
    // The generic types that this block is polymorphic over.
    // Internally to the block, these are opaque data types.
    // Externally, these are generic data types.
    type_params: Vec<String>,

    // The arguments to this block.
    // Internally to the block, the arguments are constants.
    // Externally, these arguments are variables.
    args: Vec<(String, AcornType)>,

    // The "internal claim" of this block, defined relative to the block's environment.
    // We always need to prove the propositions in the block's environment.
    // When the block has an internal claim, we need to prove that too.
    claim: Option<AcornValue>,

    // The environment created inside the block.
    env: Environment,
}

impl Block {
    // Convert a boolean value from the block's environment to a value in the outer environment.
    fn export_bool(&self, outer_env: &Environment, inner_value: &AcornValue) -> AcornValue {
        // The constants that were block arguments will export as "forall" variables.
        let mut forall_names: Vec<String> = vec![];
        let mut forall_types: Vec<AcornType> = vec![];
        for (name, t) in &self.args {
            forall_names.push(name.clone());
            forall_types.push(t.clone());
        }

        // Find all unexportable constants
        let mut unexportable: HashMap<String, AcornType> = HashMap::new();
        outer_env
            .bindings
            .find_unknown_local_constants(inner_value, &mut unexportable);

        // Unexportable constants that are not arguments export as "exists" variables.
        let mut exists_names = vec![];
        let mut exists_types = vec![];
        for (name, t) in unexportable {
            if forall_names.contains(&name) {
                continue;
            }
            exists_names.push(name);
            exists_types.push(t);
        }

        // The forall must be outside the exists, so order stack variables appropriately
        let mut map: HashMap<String, AtomId> = HashMap::new();
        for (i, name) in forall_names
            .into_iter()
            .chain(exists_names.into_iter())
            .enumerate()
        {
            map.insert(name, i as AtomId);
        }

        // Replace all of the constants that only exist in the inside environment
        let replaced = inner_value.replace_constants_with_vars(outer_env.namespace, &map);
        let replaced = self.env.bindings.genericize(&self.type_params, replaced);
        AcornValue::new_forall(forall_types, AcornValue::new_exists(exists_types, replaced))
    }
}

// The different ways to construct a block
enum BlockParams<'a> {
    // The name of the theorem.
    // The theorem is either a bool, or a function from something -> bool.
    // The meaning of the theorem is that it is true for all args.
    Theorem(&'a str),

    // The value passed in the "if" condition, and its range in the source document
    If(&'a AcornValue, Range),

    // No special params needed
    ForAll,
}

impl Environment {
    pub fn new(namespace: NamespaceId) -> Self {
        Environment {
            namespace,
            bindings: BindingMap::new(namespace),
            propositions: Vec::new(),
            definition_ranges: HashMap::new(),
        }
    }

    // Create a test version of the environment.
    #[cfg(test)]
    pub fn new_test() -> Self {
        use crate::namespace::FIRST_NORMAL;
        Environment::new(FIRST_NORMAL)
    }

    // Creates a new block with a subenvironment by copying this environment and adding some stuff.
    //
    // Performance is quadratic because it clones a lot of the existing environment.
    // Using different data structures should improve this when we need to.
    //
    // The types in args must be generic when type params are provided.
    fn new_block(
        &self,
        project: &mut Project,
        type_params: Vec<String>,
        args: Vec<(String, AcornType)>,
        body: &Vec<Statement>,
        params: BlockParams,
    ) -> Result<Option<Block>> {
        if body.is_empty() {
            return Ok(None);
        }
        let mut subenv = Environment {
            namespace: self.namespace,
            bindings: self.bindings.clone(),
            propositions: Vec::new(),
            definition_ranges: self.definition_ranges.clone(),
        };

        // Inside the block, the type parameters are opaque data types.
        let param_pairs: Vec<(String, AcornType)> = type_params
            .iter()
            .map(|s| (s.clone(), subenv.bindings.add_data_type(&s)))
            .collect();

        // Inside the block, the arguments are constants.
        for (arg_name, generic_arg_type) in &args {
            let specific_arg_type = generic_arg_type.monomorphize(&param_pairs);
            subenv
                .bindings
                .add_constant(&arg_name, vec![], specific_arg_type, None);
        }

        let claim = match params {
            BlockParams::If(fact, range) => {
                subenv.add_proposition(Proposition {
                    display_name: None,
                    proven: true,
                    claim: fact.clone(),
                    block: None,
                    range,
                });
                None
            }
            BlockParams::Theorem(theorem_name) => {
                let theorem_type = self.bindings.get_type(theorem_name).unwrap().clone();
                let unbound_claim = AcornValue::new_monomorph(
                    self.namespace,
                    theorem_name.to_string(),
                    theorem_type,
                    param_pairs,
                );

                let arg_values = args
                    .iter()
                    .map(|(name, _)| subenv.bindings.get_constant_value(name).unwrap())
                    .collect::<Vec<_>>();

                // Within the theorem block, the theorem is treated like a function,
                // with propositions to define its identity.
                // Outside the theorem block, theorems are inlined.
                subenv.add_identity_props(theorem_name);

                Some(AcornValue::new_apply(unbound_claim, arg_values))
            }
            BlockParams::ForAll => None,
        };

        for s in body {
            // Imports are not allowed in blocks, so the subenv doesn't need the project.
            subenv.add_statement(project, s)?;
        }
        Ok(Some(Block {
            type_params,
            args,
            env: subenv,
            claim,
        }))
    }

    // Adds a proposition.
    fn add_proposition(&mut self, prop: Proposition) {
        // Check if we're adding invalid claims.
        // self.validate(&prop.claim);
        // println!("adding claim: {}", self.value_str(&prop.claim));

        self.propositions.push(prop);
    }

    // Adds a proposition, or multiple propositions, to represent the definition of the provided
    // constant.
    fn add_identity_props(&mut self, name: &str) {
        let definition = if let Some(d) = self.bindings.get_definition(name) {
            d.clone()
        } else {
            return;
        };

        let constant_type_clone = self.bindings.get_type(name).unwrap().clone();
        let atom = Box::new(AcornValue::Constant(
            self.namespace,
            name.to_string(),
            constant_type_clone,
            self.bindings.get_params(name),
        ));
        let claim = if let AcornValue::Lambda(acorn_types, return_value) = definition {
            let args: Vec<_> = acorn_types
                .iter()
                .enumerate()
                .map(|(i, acorn_type)| AcornValue::Variable(i as AtomId, acorn_type.clone()))
                .collect();
            let app = AcornValue::Application(FunctionApplication {
                function: atom,
                args,
            });
            AcornValue::ForAll(
                acorn_types,
                Box::new(AcornValue::Binary(
                    BinaryOp::Equals,
                    Box::new(app),
                    return_value,
                )),
            )
        } else {
            AcornValue::Binary(BinaryOp::Equals, atom, Box::new(definition))
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

    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    pub fn get_theorem_claim(&self, name: &str) -> Option<AcornValue> {
        for prop in &self.propositions {
            if let Some(claim_name) = &prop.display_name {
                if claim_name == name {
                    return Some(prop.claim.clone());
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

    // Panics if the value is bad, for some varieties of bad
    pub fn validate(&self, value: &AcornValue) {
        self.value_str(value);
        value.get_type();
    }

    pub fn value_str(&self, value: &AcornValue) -> String {
        self.bindings.value_str(value)
    }

    // Adds a statement to the environment.
    // If the statement has a body, this call creates a sub-environment and adds the body
    // to that sub-environment.
    // If project is not provided, we won't be able to handle import statements.
    pub fn add_statement(&mut self, project: &mut Project, statement: &Statement) -> Result<()> {
        match &statement.statement {
            StatementInfo::Type(ts) => {
                if self.bindings.name_in_use(&ts.name) {
                    return Err(Error::new(
                        &ts.type_expr.token(),
                        &format!("type name '{}' already defined in this scope", ts.name),
                    ));
                }
                if ts.type_expr.token().token_type == TokenType::Axiom {
                    self.bindings.add_data_type(&ts.name);
                } else {
                    let acorn_type = self.bindings.evaluate_type(project, &ts.type_expr)?;
                    self.bindings.add_type_alias(&ts.name, acorn_type);
                };
                Ok(())
            }

            StatementInfo::Let(ls) => {
                if self.bindings.name_in_use(&ls.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("variable name '{}' already defined in this scope", ls.name),
                    ));
                }
                let acorn_type = self.bindings.evaluate_type(project, &ls.type_expr)?;
                let value = if ls.value.token().token_type == TokenType::Axiom {
                    AcornValue::Constant(
                        self.namespace,
                        ls.name.clone(),
                        acorn_type.clone(),
                        vec![],
                    )
                } else {
                    self.bindings
                        .evaluate_value(project, &ls.value, Some(&acorn_type))?
                };
                self.bindings
                    .add_constant(&ls.name, vec![], acorn_type, Some(value));
                self.definition_ranges
                    .insert(ls.name.clone(), statement.range());
                self.add_identity_props(&ls.name);
                Ok(())
            }

            StatementInfo::Define(ds) => {
                if self.bindings.name_in_use(&ds.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("function name '{}' already defined in this scope", ds.name),
                    ));
                }

                // Calculate the function value
                let (param_names, _, arg_types, unbound_value, value_type) =
                    self.bindings.evaluate_subvalue(
                        project,
                        &ds.type_params,
                        &ds.args,
                        Some(&ds.return_type),
                        &ds.return_value,
                    )?;
                if let Some(v) = unbound_value {
                    let fn_value = AcornValue::new_lambda(arg_types, v);
                    // Add the function value to the environment
                    self.bindings.add_constant(
                        &ds.name,
                        param_names,
                        fn_value.get_type(),
                        Some(fn_value),
                    );
                } else {
                    let new_axiom_type = AcornType::Function(FunctionType {
                        arg_types,
                        return_type: Box::new(value_type),
                    });
                    self.bindings
                        .add_constant(&ds.name, param_names, new_axiom_type, None);
                };

                self.definition_ranges
                    .insert(ds.name.clone(), statement.range());
                self.add_identity_props(&ds.name);
                Ok(())
            }

            StatementInfo::Theorem(ts) => {
                if self.bindings.name_in_use(&ts.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("theorem name '{}' already defined in this scope", ts.name),
                    ));
                }

                // Figure out the range for this theorem definition.
                // It's smaller than the whole theorem statement because it doesn't
                // include the proof block.
                let range = Range {
                    start: statement.first_token.start_pos(),
                    end: ts.claim.last_token().end_pos(),
                };
                self.definition_ranges.insert(ts.name.to_string(), range);

                let (type_params, arg_names, arg_types, value, _) = self
                    .bindings
                    .evaluate_subvalue(project, &ts.type_params, &ts.args, None, &ts.claim)?;

                let unbound_claim = if let Some(v) = value {
                    v
                } else {
                    return Err(Error::new(
                        &statement.first_token,
                        "theorems must have values",
                    ));
                };

                let mut block_args = vec![];
                for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
                    block_args.push((arg_name.clone(), arg_type.clone()));
                }

                // Externally we use the theorem in "forall" form
                let forall_claim = AcornValue::new_forall(arg_types.clone(), unbound_claim.clone());

                // We define the theorem using "lambda" form
                let lambda_claim = AcornValue::new_lambda(arg_types, unbound_claim);

                let theorem_type = lambda_claim.get_type();
                self.bindings.add_constant(
                    &ts.name,
                    type_params.clone(),
                    theorem_type.clone(),
                    Some(lambda_claim.clone()),
                );

                let block = self.new_block(
                    project,
                    type_params,
                    block_args,
                    &ts.body,
                    BlockParams::Theorem(&ts.name),
                )?;

                let prop = Proposition {
                    display_name: Some(ts.name.to_string()),
                    proven: ts.axiomatic,
                    claim: forall_claim,
                    block,
                    range,
                };
                self.add_proposition(prop);
                self.bindings.mark_as_theorem(&ts.name);

                Ok(())
            }

            StatementInfo::Prop(ps) => {
                let claim =
                    self.bindings
                        .evaluate_value(project, &ps.claim, Some(&AcornType::Bool))?;
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
                let mut args = vec![];
                for quantifier in &fas.quantifiers {
                    let (arg_name, arg_type) =
                        self.bindings.parse_declaration(project, quantifier)?;
                    args.push((arg_name, arg_type));
                }

                let block = self
                    .new_block(project, vec![], args, &fas.body, BlockParams::ForAll)?
                    .unwrap();

                // The last claim in the block is exported to the outside environment.
                let inner_claim: &AcornValue = match block.env.propositions.last() {
                    Some(p) => &p.claim,
                    None => {
                        return Err(Error::new(
                            &statement.first_token,
                            "expected a claim in this block",
                        ));
                    }
                };
                let outer_claim = block.export_bool(&self, inner_claim);

                let prop = Proposition {
                    display_name: None,
                    proven: false,
                    claim: outer_claim,
                    block: Some(block),
                    range: statement.range(),
                };
                self.add_proposition(prop);
                Ok(())
            }

            StatementInfo::If(is) => {
                if is.body.is_empty() {
                    // If statements with an empty body can just be ignored
                    return Ok(());
                }
                let condition =
                    self.bindings
                        .evaluate_value(project, &is.condition, Some(&AcornType::Bool))?;
                let range = is.condition.range();
                let block = self
                    .new_block(
                        project,
                        vec![],
                        vec![],
                        &is.body,
                        BlockParams::If(&condition, range),
                    )?
                    .unwrap();
                let inner_claim: &AcornValue = match block.env.propositions.last() {
                    Some(p) => &p.claim,
                    None => {
                        return Err(Error::new(&is.token, "expected a claim in this block"));
                    }
                };

                // The last claim in the block is exported to the outside environment.
                let outer_claim = block.export_bool(&self, inner_claim);
                let claim = AcornValue::Binary(
                    BinaryOp::Implies,
                    Box::new(condition),
                    Box::new(outer_claim.clone()),
                );

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
                let (quant_names, quant_types) =
                    self.bindings.bind_args(project, &es.quantifiers)?;
                let general_claim_value =
                    self.bindings
                        .evaluate_value(project, &es.claim, Some(&AcornType::Bool))?;
                let general_claim =
                    AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
                self.bindings.unbind_args(&quant_names);
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
                    self.bindings
                        .add_constant(quant_name, vec![], quant_type.clone(), None);
                }

                // We can then assume the specific existence claim with the named constants
                let specific_claim =
                    self.bindings
                        .evaluate_value(project, &es.claim, Some(&AcornType::Bool))?;
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
                if self.bindings.has_type_name(&ss.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        "type name already defined in this scope",
                    ));
                }
                let struct_type = self.bindings.add_data_type(&ss.name);

                // The member functions take the type itself to a particular member.
                let mut member_fn_names = vec![];
                let mut member_fns = vec![];
                let mut field_types = vec![];
                for (field_name_token, field_type_expr) in &ss.fields {
                    let field_type = self.bindings.evaluate_type(project, &field_type_expr)?;
                    field_types.push(field_type.clone());
                    let member_fn_name = format!("{}.{}", ss.name, field_name_token.text());
                    let member_fn_type = AcornType::Function(FunctionType {
                        arg_types: vec![struct_type.clone()],
                        return_type: Box::new(field_type),
                    });
                    self.bindings
                        .add_constant(&member_fn_name, vec![], member_fn_type, None);
                    member_fn_names.push(member_fn_name.clone());
                    member_fns.push(self.bindings.get_constant_value(&member_fn_name).unwrap());
                }

                // A "new" function to create one of these struct types.
                let new_fn_name = format!("{}.new", ss.name);
                let new_fn_type = AcornType::Function(FunctionType {
                    arg_types: field_types.clone(),
                    return_type: Box::new(struct_type.clone()),
                });
                self.bindings
                    .add_constant(&new_fn_name, vec![], new_fn_type, None);
                let new_fn = self.bindings.get_constant_value(&new_fn_name).unwrap();

                // A struct can be recreated by new'ing from its members. Ie:
                // Pair.new(Pair.first(p), Pair.second(p)) = p.
                // This is the "new equation" for a struct type.
                let new_eq_var = AcornValue::Variable(0, struct_type.clone());
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
                let new_eq =
                    AcornValue::Binary(BinaryOp::Equals, Box::new(recreated), Box::new(new_eq_var));
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
                    .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
                    .collect::<Vec<_>>();
                let new_application = AcornValue::Application(FunctionApplication {
                    function: Box::new(new_fn),
                    args: var_args,
                });
                for i in 0..ss.fields.len() {
                    let (field_name_token, field_type_expr) = &ss.fields[i];
                    let member_fn = &member_fns[i];
                    let member_eq = AcornValue::Binary(
                        BinaryOp::Equals,
                        Box::new(AcornValue::Application(FunctionApplication {
                            function: Box::new(member_fn.clone()),
                            args: vec![new_application.clone()],
                        })),
                        Box::new(AcornValue::Variable(i as AtomId, field_types[i].clone())),
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

            StatementInfo::Import(is) => {
                let local_name = is.components.last().unwrap();
                if self.bindings.name_in_use(local_name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!(
                            "imported name '{}' already defined in this scope",
                            local_name
                        ),
                    ));
                }
                let full_name = is.components.join(".");
                let namespace = match project.load(&full_name) {
                    Ok(namespace) => namespace,
                    Err(LoadError(s)) => {
                        return Err(Error::new(
                            &statement.first_token,
                            &format!("import error: {}", s),
                        ));
                    }
                };
                self.bindings.add_module(local_name, namespace);
                Ok(())
            }
        }
    }

    // Adds a possibly multi-line statement to the environment.
    // Panics on failure.
    #[cfg(test)]
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input);
        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    // Parse these tokens and add them to the environment.
    // If project is not provided, we won't be able to handle import statements.
    pub fn add_tokens(&mut self, project: &mut Project, tokens: Vec<Token>) -> Result<()> {
        let mut tokens = TokenIter::new(tokens);
        loop {
            match Statement::parse(&mut tokens, false) {
                Ok((Some(statement), _)) => {
                    if let Err(e) = self.add_statement(project, &statement) {
                        return Err(e);
                    }
                }
                Ok((None, _)) => return Ok(()),
                Err(e) => return Err(e),
            }
        }
    }

    // Will return a context for a subenvironment if this theorem has a block
    pub fn get_theorem_context(&self, project: &Project, theorem_name: &str) -> GoalContext {
        for (i, p) in self.propositions.iter().enumerate() {
            if let Some(name) = &p.display_name {
                if name == theorem_name {
                    return self.get_goal_context(project, &vec![i]);
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

    // Uses our own binding to inline theorems when the namespace matches.
    // Falls back to project-level when the namespace doesn't match.
    fn inline_theorems(&self, project: &Project, value: &AcornValue) -> AcornValue {
        // Replaces each theorem with its definition.
        value.replace_constants_with_values(0, &|namespace, name| {
            let bindings = if self.namespace == namespace {
                &self.bindings
            } else {
                &project
                    .get_env(namespace)
                    .expect("missing namespace in inline_theorems")
                    .bindings
            };
            if bindings.is_theorem(name) {
                bindings.get_definition(name).clone()
            } else {
                None
            }
        })
    }

    // Get all facts from this environment.
    pub fn get_facts(&self, project: &Project) -> Vec<AcornValue> {
        let mut facts = Vec::new();
        for prop in &self.propositions {
            facts.push(self.inline_theorems(project, &prop.claim));
        }
        facts
    }

    // Get a list of facts that are available at a certain path, along with the proposition
    // that should be proved there.
    pub fn get_goal_context(&self, project: &Project, path: &Vec<usize>) -> GoalContext {
        let mut facts = Vec::new();
        let mut env = self;
        let mut it = path.iter().peekable();
        while let Some(i) = it.next() {
            for previous_prop in &env.propositions[0..*i] {
                facts.push(env.inline_theorems(project, &previous_prop.claim));
            }
            let prop = &env.propositions[*i];
            if let Some(block) = &prop.block {
                if it.peek().is_none() {
                    // This is the last element of the path. It has a block, so we can use the
                    // contents of the block to help prove it.
                    for p in &block.env.propositions {
                        facts.push(block.env.inline_theorems(project, &p.claim));
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
                        goal: block.env.inline_theorems(project, claim),
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
                    goal: env.inline_theorems(project, &prop.claim),
                    range: prop.range,
                };
            }
        }
        panic!("control should not get here");
    }

    pub fn get_goal_context_by_name(&self, project: &Project, name: &str) -> GoalContext {
        let paths = self.goal_paths();
        let mut names = Vec::new();
        for path in paths {
            let context = self.get_goal_context(project, &path);
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
        project: &Project,
        start: Position,
        end: Position,
    ) -> Option<(Vec<usize>, GoalContext)> {
        let paths = self.goal_paths();
        for path in paths {
            let goal_context = self.get_goal_context(project, &path);
            if goal_context.range.start <= start && goal_context.range.end >= end {
                // This is the goal that contains the cursor.
                return Some((path, goal_context));
            }
        }
        None
    }

    // Expects the given line to be bad
    #[cfg(test)]
    fn bad(&mut self, input: &str) {
        if let Ok(statement) = Statement::parse_str(input) {
            assert!(
                self.add_statement(&mut Project::new_mock(), &statement)
                    .is_err(),
                "expected error in: {}",
                input
            );
        }
    }

    // Check that the given name actually does have this type in the environment.
    #[cfg(test)]
    pub fn expect_type(&mut self, name: &str, type_string: &str) {
        self.bindings.expect_type(name, type_string)
    }

    // Check that the given name is defined to be this value
    #[cfg(test)]
    fn expect_def(&mut self, name: &str, value_string: &str) {
        let env_value = match self.bindings.get_definition(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(self.value_str(&env_value), value_string);
    }

    // Assert that these two names are defined to equal the same thing
    #[cfg(test)]
    fn assert_def_eq(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_eq!(def1, def2);
    }

    // Assert that these two names are defined to be different things
    #[cfg(test)]
    fn assert_def_ne(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_ne!(def1, def2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fn_equality() {
        let mut env = Environment::new_test();
        env.add("define idb1(x: bool) -> bool = x");
        env.expect_type("idb1", "bool -> bool");
        env.add("define idb2(y: bool) -> bool = y");
        env.expect_type("idb2", "bool -> bool");
        env.assert_def_eq("idb1", "idb2");

        env.add("type Nat: axiom");
        env.add("define idn1(x: Nat) -> Nat = x");
        env.expect_type("idn1", "Nat -> Nat");
        env.assert_def_ne("idb1", "idn1");
    }

    #[test]
    fn test_forall_equality() {
        let mut env = Environment::new_test();
        env.add("let bsym1: bool = forall(x: bool) { x = x }");
        env.expect_type("bsym1", "bool");
        env.add("let bsym2: bool = forall(y: bool) { y = y }");
        env.expect_type("bsym2", "bool");
        env.assert_def_eq("bsym1", "bsym2");

        env.add("type Nat: axiom");
        env.add("let nsym1: bool = forall(x: Nat) { x = x }");
        env.expect_type("nsym1", "bool");
        env.assert_def_ne("bsym1", "nsym1");
    }

    #[test]
    fn test_exists_equality() {
        let mut env = Environment::new_test();
        env.add("let bex1: bool = exists(x: bool) { x = x }");
        env.add("let bex2: bool = exists(y: bool) { y = y }");
        env.assert_def_eq("bex1", "bex2");

        env.add("type Nat: axiom");
        env.add("let nex1: bool = exists(x: Nat) { x = x }");
        env.assert_def_ne("bex1", "nex1");
    }

    #[test]
    fn test_arg_binding() {
        let mut env = Environment::new_test();
        env.bad("define qux(x: bool, x: bool) -> bool = x");
        assert!(!env.bindings.has_identifier("x"));
        env.add("define qux(x: bool, y: bool) -> bool = x");
        env.expect_type("qux", "(bool, bool) -> bool");

        env.bad("theorem foo(x: bool, x: bool): x");
        assert!(!env.bindings.has_identifier("x"));
        env.add("theorem foo(x: bool, y: bool): x");
        env.expect_type("foo", "(bool, bool) -> bool");

        env.bad("let bar: bool = forall(x: bool, x: bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let bar: bool = forall(x: bool, y: bool) { x = x }");

        env.bad("let baz: bool = exists(x: bool, x: bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let baz: bool = exists(x: bool, y: bool) { x = x }");
    }

    #[test]
    fn test_no_double_grouped_arg_list() {
        let mut env = Environment::new_test();
        env.add("define foo(x: bool, y: bool) -> bool = x");
        env.add("let b: bool = axiom");
        env.bad("foo((b, b))");
    }

    #[test]
    fn test_argless_theorem() {
        let mut env = Environment::new_test();
        env.add("let b: bool = axiom");
        env.add("theorem foo: b | !b");
        env.expect_def("foo", "(b | !b)");
    }

    #[test]
    fn test_forall_value() {
        let mut env = Environment::new_test();
        env.add("let p: bool = forall(x: bool) { x | !x }");
        env.expect_def("p", "forall(x0: bool) { (x0 | !x0) }");
    }

    #[test]
    fn test_inline_function_value() {
        let mut env = Environment::new_test();
        env.add("define ander(a: bool) -> (bool -> bool) = function(b: bool) { a & b }");
        env.expect_def(
            "ander",
            "function(x0: bool) { function(x1: bool) { (x0 & x1) } }",
        );
    }

    #[test]
    fn test_empty_if_block() {
        let mut env = Environment::new_test();
        env.add("let b: bool = axiom");
        env.add("if b {}");
    }

    #[test]
    fn test_empty_forall_statement() {
        // Allowed as statement but not as an expression.
        let mut env = Environment::new_test();
        env.add("forall(b: bool) {}");
    }

    #[test]
    fn test_nat_ac_piecewise() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("let Suc: Nat -> Nat = axiom");
        env.add("let 1: Nat = Suc(0)");
        env.expect_def("1", "Suc(0)");

        env.add("axiom suc_injective(x: Nat, y: Nat): Suc(x) = Suc(y) -> x = y");
        env.expect_type("suc_injective", "(Nat, Nat) -> bool");
        env.expect_def(
            "suc_injective",
            "function(x0: Nat, x1: Nat) { ((Suc(x0) = Suc(x1)) -> (x0 = x1)) }",
        );

        env.add("axiom suc_neq_zero(x: Nat): Suc(x) != 0");
        env.expect_def("suc_neq_zero", "function(x0: Nat) { (Suc(x0) != 0) }");

        assert!(env.bindings.has_type_name("Nat"));
        assert!(!env.bindings.has_identifier("Nat"));

        assert!(!env.bindings.has_type_name("0"));
        assert!(env.bindings.has_identifier("0"));

        assert!(!env.bindings.has_type_name("1"));
        assert!(env.bindings.has_identifier("1"));

        assert!(!env.bindings.has_type_name("Suc"));
        assert!(env.bindings.has_identifier("Suc"));

        assert!(!env.bindings.has_type_name("foo"));
        assert!(!env.bindings.has_identifier("foo"));

        env.add(
            "axiom induction(f: Nat -> bool, n: Nat):
            f(0) & forall(k: Nat) { f(k) -> f(Suc(k)) } -> f(n)",
        );
        env.expect_def("induction", "function(x0: Nat -> bool, x1: Nat) { ((x0(0) & forall(x2: Nat) { (x0(x2) -> x0(Suc(x2))) }) -> x0(x1)) }");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat = axiom");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):
            recursion(f, a, Suc(n)) = f(recursion(f, a, n))",
        );

        env.add("define add(a: Nat, b: Nat) -> Nat = recursion(Suc, a, b)");
        env.expect_type("add", "(Nat, Nat) -> Nat");

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
        let mut env = Environment::new_test();
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
        let mut env = Environment::new_test();
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
        let mut env = Environment::new_test();
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
        let mut env = Environment::new_test();
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
        let mut env = Environment::new_test();
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
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: bool = axiom
            theorem goal: a by {
                if a {
                    exists(b: bool) { b = b }
                }
            }
            "#,
        );
        let namespace = p.expect_ok("main");
        let env = p.get_env(namespace).unwrap();
        for path in env.goal_paths() {
            env.get_goal_context(&p, &path);
        }
    }

    #[test]
    fn test_forall_block_ending_with_exists() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: bool = axiom
            theorem goal: a by {
                forall(b: bool) {
                    exists(c: bool) { c = c }
                }
            }
            "#,
        );
        let namespace = p.expect_ok("main");
        let env = p.get_env(namespace).unwrap();
        for path in env.goal_paths() {
            env.get_goal_context(&p, &path);
        }
    }

    #[test]
    fn test_struct_new_definition() {
        let mut env = Environment::new_test();
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
        let mut env = Environment::new_test();
        env.bad("define foo<T>(a: bool) -> bool = a");
    }

    #[test]
    fn test_templated_types_required_in_theorem_args() {
        let mut env = Environment::new_test();
        env.bad("theorem foo<T>(a: bool): a | !a");
    }

    #[test]
    fn test_template_typechecking() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("define eq<T>(a: T, b: T) -> bool = a = b");
        env.add("eq(0, 0)");
        env.add("eq(0 = 0, 0 = 0)");
        env.add("eq(0 = 0, eq(0, 0))");
        env.bad("eq(0, 0 = 0)");
        env.bad("0 = eq(0, 0)");
    }

    #[test]
    fn test_type_params_cleaned_up() {
        let mut env = Environment::new_test();
        env.add("define foo<T>(a: T) -> bool = axiom");
        assert!(env.bindings.get_type_for_name("T").is_none());
    }

    #[test]
    fn test_if_condition_must_be_bool() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("let b: bool = axiom");
        env.add("if b { 0 = 0 }");
        env.bad("if 0 { 0 = 0 }");
    }

    #[test]
    fn test_reusing_type_name_as_var_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let Nat: bool = axiom");
    }

    #[test]
    fn test_reusing_var_name_as_type_name() {
        let mut env = Environment::new_test();
        env.add("let x: bool = axiom");
        env.bad("type x: axiom");
    }

    #[test]
    fn test_reusing_type_name_as_fn_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define Nat(x: bool) -> bool = x");
    }

    #[test]
    fn test_reusing_type_name_as_theorem_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("theorem Nat(x: bool): x = x");
    }

    #[test]
    fn test_reusing_type_name_as_exists_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: bool = exists(x: bool, Nat: bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_forall_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: bool = forall(x: bool, Nat: bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_lambda_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let f: (bool, bool) -> bool = function(x: bool, Nat: bool) { x = x }");
    }
}
