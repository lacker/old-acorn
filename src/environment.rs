use std::collections::HashMap;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::AtomId;
use crate::binding_map::{BindingMap, Stack};
use crate::goal_context::GoalContext;
use crate::module::ModuleId;
use crate::project::{LoadError, Project};
use crate::proposition::Proposition;
use crate::statement::{Body, DefineStatement, LetStatement, Statement, StatementInfo};
use crate::token::{self, Error, Token, TokenIter, TokenType};

// Each line has a LineType, to handle line-based user interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LineType {
    // Only used within subenvironments.
    // The line relates to the block, but is outside the opening brace for this block.
    Opening,

    // This line corresponds to a proposition inside the environment.
    // The usize is an index into the propositions array.
    // If the proposition has a block, this line should also have a type within the block.
    Proposition(usize),

    // Either only whitespace is here, or a comment.
    Empty,

    // Lines with other sorts of statements besides prop statements.
    Other,

    // Only used within subenvironments.
    // The line has the closing brace for this block.
    Closing,
}

// The Environment takes Statements as input and processes them.
// It does not prove anything directly, but it is responsible for determining which
// things need to be proved, and which statements are usable in which proofs.
// It creates subenvironments for nested blocks.
// It does not have to be efficient enough to run in the inner loop of the prover.
pub struct Environment {
    pub module_id: ModuleId,

    // What all the names mean in this environment
    pub bindings: BindingMap,

    // The propositions in this environment.
    // This includes every sort of thing that we need to know is true, specific to this environment.
    // This includes theorems, anonymous propositions, and definitions.
    // Does not include propositions from parent or child environments.
    // The propositions are fundamentally linear; each may depend on the previous propositions
    // but not on later ones.
    propositions: Vec<PropositionTree>,

    // The region in the source document where a name was defined
    definition_ranges: HashMap<String, Range>,

    // Whether a plain "false" is anywhere in this environment.
    // This indicates that the environment is supposed to have contradictory facts.
    pub includes_explicit_false: bool,

    // For the base environment, first_line is zero.
    // first_line is usually nonzero when the environment is a subenvironment.
    // line_types[0] corresponds to first_line in the source document.
    first_line: u32,
    line_types: Vec<LineType>,

    // Implicit blocks aren't written in the code; they are created for theorems that
    // the user has asserted without proof.
    pub implicit: bool,
}

// A proposition, as well as any subpropositions that need to be proved to establish this one.
struct PropositionTree {
    // Whether this proposition has already been proved structurally.
    // For example, this could be an axiom, or a definition.
    proven: bool,

    // The proposition represented by this tree.
    // If this proposition has a block, this represents the "external claim".
    // It is the value we can assume is true, in the outer environment, when everything
    // in the inner environment has been proven.
    // Besides the claim, nothing else from the block is visible externally.
    //
    // This claim needs to be proved when proven is false, and there is no block.
    claim: Proposition,

    // The body of the proposition, when it has an associated block.
    // When there is a block, proving every proposition in the block implies that the
    // claim is proven as well.
    block: Option<Block>,
}

impl PropositionTree {
    // A human-readable name for this proposition.
    pub fn name(&self) -> String {
        match &self.claim.name() {
            Some(name) => name.to_string(),
            None => self.claim.value.to_string(),
        }
    }
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
    // This only exists for theorem blocks, where we implicitly want to prove the theorem.
    // We always need to prove the propositions in the block's environment.
    // When the block has an internal claim, we need to prove that too.
    claim: Option<Proposition>,

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

        // Internal variables need to be shifted over
        let shift_amount = (forall_names.len() + exists_names.len()) as AtomId;

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
        let replaced = inner_value.clone().insert_stack(0, shift_amount);
        let replaced = replaced.replace_constants_with_vars(outer_env.module_id, &map);
        let replaced = replaced.parametrize(self.env.module_id, &self.type_params);
        AcornValue::new_forall(forall_types, AcornValue::new_exists(exists_types, replaced))
    }
}

// The different ways to construct a block
enum BlockParams<'a> {
    // (theorem name, premise, goal)
    //
    // The premise and goal are unbound, to be proved based on the args of the theorem.
    //
    // The theorem should already be defined by this name in the external environment.
    // It is either a bool, or a function from something -> bool.
    // The meaning of the theorem is that it is true for all args.
    //
    // The premise is optional.
    Theorem(&'a str, Option<(AcornValue, Range)>, AcornValue),

    // The assumption to be used by the block, and the range of this assumption.
    Conditional(&'a AcornValue, Range),

    // No special params needed
    ForAll,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            propositions: Vec::new(),
            definition_ranges: HashMap::new(),
            includes_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
        }
    }

    // Create a test version of the environment.
    #[cfg(test)]
    pub fn new_test() -> Self {
        use crate::module::FIRST_NORMAL;
        Environment::new(FIRST_NORMAL)
    }

    fn next_line(&self) -> u32 {
        self.line_types.len() as u32 + self.first_line
    }

    fn last_line(&self) -> u32 {
        self.next_line() - 1
    }

    fn theorem_range(&self, name: &str) -> Option<Range> {
        self.definition_ranges.get(name).cloned()
    }

    // Add line types for the given range, inserting empties as needed.
    // If the line already has a type, do nothing.
    fn add_line_types(&mut self, line_type: LineType, first: u32, last: u32) {
        while self.next_line() < first {
            self.line_types.push(LineType::Empty);
        }
        while self.next_line() <= last {
            self.line_types.push(line_type);
        }
    }

    fn add_other_lines(&mut self, statement: &Statement) {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            statement.last_line(),
        );
    }

    fn add_prop_lines(&mut self, index: usize, statement: &Statement) {
        self.add_line_types(
            LineType::Proposition(index),
            statement.first_line(),
            statement.last_line(),
        );
    }

    fn get_line_type(&self, line: u32) -> Option<LineType> {
        if line < self.first_line {
            return None;
        }
        let index = (line - self.first_line) as usize;
        if index < self.line_types.len() {
            Some(self.line_types[index])
        } else {
            None
        }
    }

    // Creates a new block with a subenvironment by copying this environment and adding some stuff.
    //
    // Performance is quadratic because it clones a lot of the existing environment.
    // Using different data structures should improve this when we need to.
    //
    // The types in args must be generic when type params are provided.
    // If no body is provided, the block has no statements in it.
    fn new_block(
        &self,
        project: &mut Project,
        type_params: Vec<String>,
        args: Vec<(String, AcornType)>,
        params: BlockParams,
        first_line: u32,
        last_line: u32,
        body: Option<&Body>,
    ) -> token::Result<Block> {
        let mut subenv = Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            propositions: Vec::new(),
            definition_ranges: self.definition_ranges.clone(),
            includes_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit: body.is_none(),
        };

        // Inside the block, the type parameters are opaque data types.
        let param_pairs: Vec<(String, AcornType)> = type_params
            .iter()
            .map(|s| (s.clone(), subenv.bindings.add_data_type(&s)))
            .collect();

        // Inside the block, the arguments are constants.
        for (arg_name, generic_arg_type) in &args {
            let specific_arg_type = generic_arg_type.specialize(&param_pairs);
            subenv
                .bindings
                .add_constant(&arg_name, vec![], specific_arg_type, None);
        }

        let claim = match params {
            BlockParams::Conditional(condition, range) => {
                subenv.add_proposition(PropositionTree {
                    proven: true,
                    claim: Proposition::premise(condition.clone(), self.module_id, range),
                    block: None,
                });
                None
            }
            BlockParams::Theorem(theorem_name, premise, unbound_goal) => {
                let theorem_type = self
                    .bindings
                    .get_type_for_identifier(theorem_name)
                    .unwrap()
                    .clone();

                // The theorem as a named function from args -> bool.
                let functional_theorem = AcornValue::new_specialized(
                    self.module_id,
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
                // This is a compromise initially inspired by the desire so to do induction
                // without writing a separate definition for the inductive hypothesis.
                // (Outside the theorem block, theorems are inlined.)
                subenv.add_identity_props(theorem_name);

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound = unbound_premise.bind_values(0, 0, &arg_values);

                    subenv.add_proposition(PropositionTree {
                        proven: true,
                        claim: Proposition::premise(bound, self.module_id, premise_range),
                        block: None,
                    });
                }

                // We can prove the goal either in bound or in function form
                let bound_goal = unbound_goal.bind_values(0, 0, &arg_values);
                let functional_goal = AcornValue::new_apply(functional_theorem, arg_values);
                let value = AcornValue::new_or(functional_goal, bound_goal);
                Some(Proposition::theorem(
                    false,
                    value,
                    self.module_id,
                    self.theorem_range(theorem_name).unwrap(),
                    theorem_name.to_string(),
                ))
            }
            BlockParams::ForAll => None,
        };

        match body {
            Some(body) => {
                subenv.add_line_types(
                    LineType::Opening,
                    first_line,
                    body.left_brace.line_number as u32,
                );
                for s in &body.statements {
                    subenv.add_statement(project, s)?;
                }
                subenv.add_line_types(
                    LineType::Closing,
                    body.right_brace.line_number as u32,
                    body.right_brace.line_number as u32,
                );
            }
            None => {
                // The subenv is an implicit block, so consider all the lines to be "opening".
                subenv.add_line_types(LineType::Opening, first_line, last_line);
            }
        };
        Ok(Block {
            type_params,
            args,
            env: subenv,
            claim,
        })
    }

    // Adds a proposition.
    fn add_proposition(&mut self, prop: PropositionTree) -> usize {
        // Check if we're adding invalid claims.
        prop.claim
            .value
            .validate()
            .unwrap_or_else(|e| panic!("invalid claim: {} ({})", prop.claim.value, e));

        self.propositions.push(prop);
        self.propositions.len() - 1
    }

    // Adds a proposition, or multiple propositions, to represent the definition of the provided
    // constant.
    fn add_identity_props(&mut self, name: &str) {
        let definition = if let Some(d) = self.bindings.get_definition(name) {
            d.clone()
        } else {
            return;
        };

        let constant_type_clone = self.bindings.get_type_for_identifier(name).unwrap().clone();
        let param_names = self.bindings.get_params(name);

        let constant = if param_names.is_empty() {
            AcornValue::Constant(
                self.module_id,
                name.to_string(),
                constant_type_clone,
                vec![],
            )
        } else {
            let params = param_names
                .into_iter()
                .map(|n| (n.clone(), AcornType::Parameter(n)))
                .collect();
            AcornValue::Specialized(
                self.module_id,
                name.to_string(),
                constant_type_clone,
                params,
            )
        };
        let claim = if let AcornValue::Lambda(acorn_types, return_value) = definition {
            let args: Vec<_> = acorn_types
                .iter()
                .enumerate()
                .map(|(i, acorn_type)| AcornValue::Variable(i as AtomId, acorn_type.clone()))
                .collect();
            let app = AcornValue::Application(FunctionApplication {
                function: Box::new(constant),
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
            AcornValue::Binary(BinaryOp::Equals, Box::new(constant), Box::new(definition))
        };
        let range = self.definition_ranges.get(name).unwrap().clone();

        self.add_proposition(PropositionTree {
            proven: true,
            claim: Proposition::definition(claim, self.module_id, range, name.to_string()),
            block: None,
        });
    }

    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    pub fn get_theorem_claim(&self, name: &str) -> Option<AcornValue> {
        for prop in &self.propositions {
            if let Some(claim_name) = prop.claim.name() {
                if claim_name == name {
                    return Some(prop.claim.value.clone());
                }
            }
        }
        None
    }

    // Adds a conditional block to the environment.
    // Takes the condition, the range to associate with the condition, the first line of
    // the conditional block, and finally the body itself.
    // If this is an "else" block, we pass in the claim from the "if" part of the block.
    // This way, if the claim is the same, we can simplify by combining them when exported.
    // Returns the last claim in the block, if we didn't have an if-claim to match against.
    fn add_conditional(
        &mut self,
        project: &mut Project,
        condition: AcornValue,
        range: Range,
        first_line: u32,
        last_line: u32,
        body: &Body,
        if_claim: Option<AcornValue>,
    ) -> token::Result<Option<AcornValue>> {
        if body.statements.is_empty() {
            // Conditional blocks with an empty body can just be ignored
            return Ok(None);
        }
        let block = self.new_block(
            project,
            vec![],
            vec![],
            BlockParams::Conditional(&condition, range),
            first_line,
            last_line,
            Some(body),
        )?;
        let (inner_claim, claim_range) = match block.env.propositions.last() {
            Some(p) => (&p.claim.value, p.claim.source.range),
            None => {
                return Err(Error::new(
                    &body.right_brace,
                    "expected a claim in this block",
                ));
            }
        };
        // The last claim in the block is exported to the outside environment.
        let outer_claim = block.export_bool(&self, inner_claim);
        let matching_branches = if let Some(if_claim) = if_claim {
            if outer_claim == if_claim {
                true
            } else {
                false
            }
        } else {
            false
        };
        let (external_claim, last_claim) = if matching_branches {
            (outer_claim, None)
        } else {
            (
                AcornValue::Binary(
                    BinaryOp::Implies,
                    Box::new(condition),
                    Box::new(outer_claim.clone()),
                ),
                Some(outer_claim),
            )
        };
        let prop = PropositionTree {
            proven: false,
            claim: Proposition::anonymous(external_claim, self.module_id, claim_range),
            block: Some(block),
        };
        let index = self.add_proposition(prop);
        self.add_line_types(
            LineType::Proposition(index),
            first_line,
            body.right_brace.line_number,
        );
        Ok(last_claim)
    }

    // Adds a "let" statement to the environment, that may be within a class block.
    fn add_let_statement(
        &mut self,
        project: &Project,
        class: Option<&str>,
        ls: &LetStatement,
        range: Range,
    ) -> token::Result<()> {
        let name = match class {
            Some(c) => format!("{}.{}", c, ls.name),
            None => ls.name.clone(),
        };
        if name == "self" {
            return Err(Error::new(
                &ls.name_token,
                "cannot define a constant named 'self'",
            ));
        }
        if self.bindings.name_in_use(&name) {
            return Err(Error::new(
                &ls.name_token,
                &format!("constant name '{}' already defined in this scope", name),
            ));
        }
        let acorn_type = self.bindings.evaluate_type(project, &ls.type_expr)?;
        let value = if ls.value.token().token_type == TokenType::Axiom {
            AcornValue::Constant(self.module_id, name.clone(), acorn_type.clone(), vec![])
        } else {
            self.bindings
                .evaluate_value(project, &ls.value, Some(&acorn_type))?
        };
        self.bindings
            .add_constant(&name, vec![], acorn_type, Some(value));
        self.definition_ranges.insert(name.clone(), range);
        self.add_identity_props(&name);
        Ok(())
    }

    // Adds a "define" statement to the environment, that may be within a class block.
    fn add_define_statement(
        &mut self,
        project: &Project,
        class: Option<&str>,
        ds: &DefineStatement,
        range: Range,
    ) -> token::Result<()> {
        let name = match class {
            Some(c) => format!("{}.{}", c, ds.name),
            None => ds.name.clone(),
        };
        if self.bindings.name_in_use(&name) {
            return Err(Error::new(
                &ds.name_token,
                &format!("function name '{}' already defined in this scope", name),
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
                class.is_some(),
            )?;
        if let Some(v) = unbound_value {
            let fn_value = AcornValue::new_lambda(arg_types, v);
            // Add the function value to the environment
            self.bindings
                .add_constant(&name, param_names, fn_value.get_type(), Some(fn_value));
        } else {
            let new_axiom_type = AcornType::new_functional(arg_types, value_type);
            self.bindings
                .add_constant(&name, param_names, new_axiom_type, None);
        };

        self.definition_ranges.insert(name.clone(), range);
        self.add_identity_props(&name);
        Ok(())
    }

    // Adds a statement to the environment.
    // If the statement has a body, this call creates a sub-environment and adds the body
    // to that sub-environment.
    pub fn add_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
    ) -> token::Result<()> {
        if self.includes_explicit_false {
            return Err(Error::new(
                &statement.first_token,
                "an explicit 'false' may not be followed by other statements",
            ));
        }
        match &statement.statement {
            StatementInfo::Type(ts) => {
                self.add_other_lines(statement);
                if !Token::is_valid_type_name(&ts.name) {
                    return Err(Error::new(
                        &ts.type_expr.token(),
                        &format!("invalid type name '{}'.", ts.name),
                    ));
                }

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
                self.add_other_lines(statement);
                self.add_let_statement(project, None, ls, statement.range())
            }

            StatementInfo::Define(ds) => {
                self.add_other_lines(statement);
                self.add_define_statement(project, None, ds, statement.range())
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

                let (type_params, arg_names, arg_types, value, _) =
                    self.bindings.evaluate_subvalue(
                        project,
                        &ts.type_params,
                        &ts.args,
                        None,
                        &ts.claim,
                        false,
                    )?;

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

                let (premise, goal) = match &unbound_claim {
                    AcornValue::Binary(BinaryOp::Implies, left, right) => {
                        let premise_range = match ts.claim.premise() {
                            Some(p) => p.range(),
                            None => {
                                // I don't think this should happen, but it's awkward for the
                                // compiler to enforce, so pick a not-too-wrong default.
                                ts.claim.range()
                            }
                        };
                        (Some((*left.clone(), premise_range)), *right.clone())
                    }
                    c => (None, c.clone()),
                };

                // We define the theorem using "lambda" form.
                // The definition happens here, in the outside environment, because the
                // theorem is usable by name in this environment.
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
                    BlockParams::Theorem(&ts.name, premise, goal),
                    statement.first_line(),
                    statement.last_line(),
                    ts.body.as_ref(),
                )?;

                let tree = PropositionTree {
                    proven: ts.axiomatic,
                    claim: Proposition::theorem(
                        ts.axiomatic,
                        forall_claim,
                        self.module_id,
                        range,
                        ts.name.to_string(),
                    ),
                    block: Some(block),
                };
                let index = self.add_proposition(tree);
                self.add_prop_lines(index, statement);
                self.bindings.mark_as_theorem(&ts.name);

                Ok(())
            }

            StatementInfo::Prop(ps) => {
                let claim =
                    self.bindings
                        .evaluate_value(project, &ps.claim, Some(&AcornType::Bool))?;
                if claim == AcornValue::Bool(false) {
                    self.includes_explicit_false = true;
                }
                let prop = PropositionTree {
                    proven: false,
                    claim: Proposition::anonymous(claim, self.module_id, statement.range()),
                    block: None,
                };
                let index = self.add_proposition(prop);
                self.add_prop_lines(index, statement);
                Ok(())
            }

            StatementInfo::ForAll(fas) => {
                if fas.body.statements.is_empty() {
                    // ForAll statements with an empty body can just be ignored
                    return Ok(());
                }
                let mut args = vec![];
                for quantifier in &fas.quantifiers {
                    let (arg_name, arg_type) = self
                        .bindings
                        .parse_declaration(project, quantifier, false)?;
                    args.push((arg_name, arg_type));
                }

                let block = self.new_block(
                    project,
                    vec![],
                    args,
                    BlockParams::ForAll,
                    statement.first_line(),
                    statement.last_line(),
                    Some(&fas.body),
                )?;

                // The last claim in the block is exported to the outside environment.
                let inner_claim: &AcornValue = match block.env.propositions.last() {
                    Some(p) => &p.claim.value,
                    None => {
                        return Err(Error::new(
                            &statement.first_token,
                            "expected a claim in this block",
                        ));
                    }
                };
                let outer_claim = block.export_bool(&self, inner_claim);
                let prop = PropositionTree {
                    proven: false,
                    claim: Proposition::anonymous(outer_claim, self.module_id, statement.range()),
                    block: Some(block),
                };
                let index = self.add_proposition(prop);
                self.add_prop_lines(index, statement);
                Ok(())
            }

            StatementInfo::If(is) => {
                let condition =
                    self.bindings
                        .evaluate_value(project, &is.condition, Some(&AcornType::Bool))?;
                let range = is.condition.range();
                let if_claim = self.add_conditional(
                    project,
                    condition.clone(),
                    range,
                    statement.first_line(),
                    statement.last_line(),
                    &is.body,
                    None,
                )?;
                if let Some(else_body) = &is.else_body {
                    self.add_conditional(
                        project,
                        condition.negate(),
                        range,
                        else_body.left_brace.line_number as u32,
                        else_body.right_brace.line_number as u32,
                        else_body,
                        if_claim,
                    )?;
                }
                Ok(())
            }

            StatementInfo::Exists(es) => {
                // We need to prove the general existence claim
                let mut stack = Stack::new();
                let (quant_names, quant_types) =
                    self.bindings
                        .bind_args(&mut stack, project, &es.quantifiers, false)?;
                let general_claim_value = self.bindings.evaluate_value_with_stack(
                    &mut stack,
                    project,
                    &es.claim,
                    Some(&AcornType::Bool),
                )?;
                let general_claim =
                    AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
                let general_prop = PropositionTree {
                    proven: false,
                    claim: Proposition::anonymous(general_claim, self.module_id, statement.range()),
                    block: None,
                };
                let index = self.add_proposition(general_prop);
                self.add_prop_lines(index, statement);

                // Define the quantifiers as constants
                for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
                    self.bindings
                        .add_constant(quant_name, vec![], quant_type.clone(), None);
                }

                // We can then assume the specific existence claim with the named constants
                let specific_claim =
                    self.bindings
                        .evaluate_value(project, &es.claim, Some(&AcornType::Bool))?;
                let specific_prop = PropositionTree {
                    proven: true,
                    claim: Proposition::anonymous(
                        specific_claim,
                        self.module_id,
                        statement.range(),
                    ),
                    block: None,
                };
                self.add_proposition(specific_prop);

                Ok(())
            }

            StatementInfo::Struct(ss) => {
                self.add_other_lines(statement);
                if self.bindings.has_type_name(&ss.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        "type name already defined in this scope",
                    ));
                }

                // Parse the fields before adding the struct type so that we can't have
                // self-referential structs.
                let mut member_fn_names = vec![];
                let mut field_types = vec![];
                for (field_name_token, field_type_expr) in &ss.fields {
                    let field_type = self.bindings.evaluate_type(project, &field_type_expr)?;
                    field_types.push(field_type.clone());
                    let member_fn_name = format!("{}.{}", ss.name, field_name_token.text());
                    member_fn_names.push(member_fn_name);
                }

                // The member functions take the type itself to a particular member.
                let struct_type = self.bindings.add_data_type(&ss.name);
                let mut member_fns = vec![];
                for (member_fn_name, field_type) in member_fn_names.iter().zip(&field_types) {
                    let member_fn_type =
                        AcornType::new_functional(vec![struct_type.clone()], field_type.clone());
                    self.bindings
                        .add_constant(&member_fn_name, vec![], member_fn_type, None);
                    member_fns.push(self.bindings.get_constant_value(&member_fn_name).unwrap());
                }

                // A "new" function to create one of these struct types.
                let new_fn_name = format!("{}.new", ss.name);
                let new_fn_type =
                    AcornType::new_functional(field_types.clone(), struct_type.clone());
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
                let range = Range {
                    start: statement.first_token.start_pos(),
                    end: ss.name_token.end_pos(),
                };
                self.add_proposition(PropositionTree {
                    proven: true,
                    claim: Proposition::definition(
                        new_claim,
                        self.module_id,
                        range,
                        ss.name.clone(),
                    ),
                    block: None,
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
                    let range = Range {
                        start: field_name_token.start_pos(),
                        end: field_type_expr.last_token().end_pos(),
                    };
                    self.add_proposition(PropositionTree {
                        proven: true,
                        claim: Proposition::definition(
                            member_claim,
                            self.module_id,
                            range,
                            ss.name.clone(),
                        ),
                        block: None,
                    });
                }

                Ok(())
            }

            StatementInfo::Import(is) => {
                self.add_other_lines(statement);
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
                let module_id = match project.load_module(&full_name) {
                    Ok(module_id) => module_id,
                    Err(LoadError(s)) => {
                        return Err(Error::new(
                            &statement.first_token,
                            &format!("import error: {}", s),
                        ));
                    }
                };
                self.bindings.add_module(local_name, module_id);
                Ok(())
            }

            StatementInfo::Class(cs) => {
                self.add_other_lines(statement);
                match self.bindings.get_type_for_name(&cs.name) {
                    Some(AcornType::Data(module, name)) => {
                        if module != &self.module_id {
                            return Err(Error::new(
                                &cs.name_token,
                                "we can only bind members to types in the current module",
                            ));
                        }
                        if name != &cs.name {
                            return Err(Error::new(
                                &cs.name_token,
                                "we cannot bind members to type aliases",
                            ));
                        }
                    }
                    Some(_) => {
                        return Err(Error::new(
                            &cs.name_token,
                            &format!("we can only bind members to data types"),
                        ));
                    }
                    None => {
                        return Err(Error::new(
                            &cs.name_token,
                            &format!("undefined type name '{}'", cs.name),
                        ));
                    }
                };
                for substatement in &cs.body.statements {
                    match &substatement.statement {
                        StatementInfo::Let(ls) => {
                            self.add_let_statement(
                                project,
                                Some(&cs.name),
                                ls,
                                substatement.range(),
                            )?;
                        }
                        StatementInfo::Define(ds) => {
                            self.add_define_statement(
                                project,
                                Some(&ds.name),
                                ds,
                                substatement.range(),
                            )?;
                        }
                        _ => {
                            return Err(Error::new(
                                &substatement.first_token,
                                "only let and define statements are allowed in class bodies",
                            ));
                        }
                    }
                }
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
    pub fn add_tokens(&mut self, project: &mut Project, tokens: Vec<Token>) -> token::Result<()> {
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
            if let Some(name) = p.claim.name() {
                if name == theorem_name {
                    return self.get_goal_context(project, &vec![i]).unwrap();
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
        self.get_paths(&vec![], false)
    }

    // Like goal_paths but also includes the paths to props with no goal, like
    // "if" or "define" statements.
    pub fn prop_paths(&self) -> Vec<Vec<usize>> {
        self.get_paths(&vec![], true)
    }

    // Find all paths from this environment, prepending 'prepend' to each path.
    // allow_proven controls whether we include propositions that have already been proven.
    fn get_paths(&self, prepend: &Vec<usize>, allow_proven: bool) -> Vec<Vec<usize>> {
        let mut paths = Vec::new();
        for (i, prop) in self.propositions.iter().enumerate() {
            if prop.proven && !allow_proven {
                continue;
            }
            let path = {
                let mut path = prepend.clone();
                path.push(i);
                path
            };
            if let Some(block) = &prop.block {
                let mut subpaths = block.env.get_paths(&path, allow_proven);
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

    // Uses our own binding to inline theorems when the module matches.
    // Falls back to project-level when the module doesn't match.
    fn inline_theorems(&self, project: &Project, prop: &Proposition) -> Proposition {
        // Replaces each theorem with its definition.
        let value = prop
            .value
            .replace_constants_with_values(0, &|module_id, name| {
                let bindings = if self.module_id == module_id {
                    &self.bindings
                } else {
                    &project
                        .get_env(module_id)
                        .expect("missing module in inline_theorems")
                        .bindings
                };
                if bindings.is_theorem(name) {
                    bindings.get_definition(name).clone()
                } else {
                    None
                }
            });
        prop.with_value(value)
    }

    // Get all facts from this environment.
    pub fn get_facts(&self, project: &Project) -> Vec<Proposition> {
        let mut facts = Vec::new();
        for prop in &self.propositions {
            facts.push(self.inline_theorems(project, &prop.claim));
        }
        facts
    }

    // Gets the proposition at a certain path.
    pub fn get_proposition(&self, path: &Vec<usize>) -> Option<&Proposition> {
        let mut env = self;
        let mut it = path.iter().peekable();
        while let Some(i) = it.next() {
            if it.peek().is_none() {
                return env.propositions.get(*i).map(|p| &p.claim);
            }
            let prop = env.propositions.get(*i)?;
            if let Some(block) = &prop.block {
                env = &block.env;
            } else {
                return None;
            }
        }
        None
    }

    // Get a list of facts that are available at a certain path, along with the proposition
    // that should be proved there.
    pub fn get_goal_context(
        &self,
        project: &Project,
        path: &Vec<usize>,
    ) -> Result<GoalContext, String> {
        let mut global_facts = vec![];
        let mut local_facts = vec![];
        let mut env = self;
        let mut it = path.iter().peekable();
        let mut global = true;
        while let Some(i) = it.next() {
            for previous_prop in &env.propositions[0..*i] {
                let fact = env.inline_theorems(project, &previous_prop.claim);
                if global {
                    global_facts.push(fact);
                } else {
                    local_facts.push(fact);
                }
            }
            global = false;
            let prop = &env.propositions.get(*i);
            let prop = match prop {
                Some(p) => p,
                None => return Err(format!("no prop at path {:?}", path)),
            };
            if let Some(block) = &prop.block {
                if it.peek().is_none() {
                    // This is the last element of the path. It has a block, so we can use the
                    // contents of the block to help prove it.
                    for p in &block.env.propositions {
                        local_facts.push(block.env.inline_theorems(project, &p.claim));
                    }
                    let claim = if let Some(claim) = &block.claim {
                        claim
                    } else {
                        return Err(format!("no internal claim at path {:?}", path));
                    };

                    let proof_insertion_line = if block.env.implicit {
                        // Insert the proof, along with an explicit block, after the statement
                        block.env.last_line() + 1
                    } else {
                        // Insert the proof at the end of the existing block
                        block.env.last_line()
                    };

                    return Ok(GoalContext::new(
                        &block.env,
                        global_facts,
                        local_facts,
                        prop.name(),
                        block.env.inline_theorems(project, &claim),
                        prop.claim.source.range,
                        proof_insertion_line,
                    ));
                }
                env = &block.env;
            } else {
                // If there's no block on this prop, this must be the last element of the path
                assert!(it.peek().is_none());

                return Ok(GoalContext::new(
                    &env,
                    global_facts,
                    local_facts,
                    prop.name(),
                    env.inline_theorems(project, &prop.claim),
                    prop.claim.source.range,
                    prop.claim.source.range.start.line,
                ));
            }
        }
        panic!("control should not get here");
    }

    pub fn get_goal_context_by_name(&self, project: &Project, name: &str) -> GoalContext {
        let paths = self.goal_paths();
        let mut names = Vec::new();
        for path in paths {
            let context = self.get_goal_context(project, &path).unwrap();
            if context.name == name {
                return context;
            }
            names.push(context.name);
        }

        panic!("no context found for {} in:\n{}\n", name, names.join("\n"));
    }

    // Returns the path corresponding to the goal for a given zero-based line.
    // This is a UI heuristic.
    // Either returns a path to a proposition, or an error message explaining why this line
    // is unusable. Error messages use one-based line numbers.
    pub fn get_path_for_line(&self, line: u32) -> Result<Vec<usize>, String> {
        let mut path = vec![];
        let mut block: Option<&Block> = None;
        let mut env = self;
        loop {
            match env.get_line_type(line) {
                Some(LineType::Proposition(i)) => {
                    path.push(i);
                    let prop = &env.propositions[i];
                    if prop.claim.source.is_axiom() {
                        return Err(format!("line {} is an axiom", line + 1));
                    }
                    match &prop.block {
                        Some(b) => {
                            block = Some(b);
                            env = &b.env;
                            continue;
                        }
                        None => {
                            return Ok(path);
                        }
                    }
                }
                Some(LineType::Opening) | Some(LineType::Closing) => match block {
                    Some(block) => {
                        if block.claim.is_none() {
                            return Err(format!("no claim for block at line {}", line + 1));
                        }
                        return Ok(path);
                    }
                    None => return Err(format!("brace but no block, line {}", line + 1)),
                },
                Some(LineType::Other) => return Err(format!("line {} is not a prop", line + 1)),
                None => return Err(format!("line {} is out of range", line + 1)),
                Some(LineType::Empty) => {
                    // We let the user insert a proof in an area by clicking on an empty
                    // line where the proof would go.
                    // To find the statement we're proving, we "slide" into the next prop.
                    let mut slide = line;
                    loop {
                        slide += 1;
                        match env.get_line_type(slide) {
                            Some(LineType::Proposition(i)) => {
                                let prop = &env.propositions[i];
                                if prop.claim.source.is_axiom() {
                                    return Err(format!("slide to axiom, line {}", slide + 1));
                                }
                                if prop.block.is_none() {
                                    path.push(i);
                                    return Ok(path);
                                }
                                // We can't slide into a block, because the proof would be
                                // inserted into the block, rather than here.
                                return Err(format!("blocked slide {} -> {}", line + 1, slide + 1));
                            }
                            Some(LineType::Empty) => {
                                // Keep sliding
                                continue;
                            }
                            Some(LineType::Closing) => {
                                // Sliding into the end of our block is okay
                                match block {
                                    Some(block) => {
                                        if block.claim.is_none() {
                                            return Err("slide to end but no claim".to_string());
                                        }
                                        return Ok(path);
                                    }
                                    None => {
                                        return Err(format!(
                                            "close brace but no block, line {}",
                                            slide + 1
                                        ))
                                    }
                                }
                            }
                            Some(LineType::Opening) => {
                                return Err(format!("slide to open brace, line {}", slide + 1));
                            }
                            Some(LineType::Other) => {
                                return Err(format!("slide to non-prop {}", slide + 1));
                            }
                            None => return Err(format!("slide to end, line {}", slide + 1)),
                        }
                    }
                }
            }
        }
    }

    pub fn covers_line(&self, line: u32) -> bool {
        if line < self.first_line {
            return false;
        }
        if line >= self.next_line() {
            return false;
        }
        true
    }

    // Makes sure the lines are self-consistent
    #[cfg(test)]
    fn check_lines(&self) {
        // Check that each proposition's block covers the lines it claims to cover
        for (line, line_type) in self.line_types.iter().enumerate() {
            if let LineType::Proposition(prop_index) = line_type {
                let prop = &self.propositions[*prop_index];
                if let Some(block) = &prop.block {
                    assert!(block.env.covers_line(line as u32));
                }
            }
        }

        // Recurse
        for prop in &self.propositions {
            if let Some(block) = &prop.block {
                block.env.check_lines();
            }
        }
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
        assert_eq!(env_value.to_string(), value_string);
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
        env.add("define idb1(x: Bool) -> Bool: x");
        env.expect_type("idb1", "Bool -> Bool");
        env.add("define idb2(y: Bool) -> Bool: y");
        env.expect_type("idb2", "Bool -> Bool");
        env.assert_def_eq("idb1", "idb2");

        env.add("type Nat: axiom");
        env.add("define idn1(x: Nat) -> Nat: x");
        env.expect_type("idn1", "Nat -> Nat");
        env.assert_def_ne("idb1", "idn1");
    }

    #[test]
    fn test_forall_equality() {
        let mut env = Environment::new_test();
        env.add("let bsym1: Bool = forall(x: Bool) { x = x }");
        env.expect_type("bsym1", "Bool");
        env.add("let bsym2: Bool = forall(y: Bool) { y = y }");
        env.expect_type("bsym2", "Bool");
        env.assert_def_eq("bsym1", "bsym2");

        env.add("type Nat: axiom");
        env.add("let nsym1: Bool = forall(x: Nat) { x = x }");
        env.expect_type("nsym1", "Bool");
        env.assert_def_ne("bsym1", "nsym1");
    }

    #[test]
    fn test_exists_equality() {
        let mut env = Environment::new_test();
        env.add("let bex1: Bool = exists(x: Bool) { x = x }");
        env.add("let bex2: Bool = exists(y: Bool) { y = y }");
        env.assert_def_eq("bex1", "bex2");

        env.add("type Nat: axiom");
        env.add("let nex1: Bool = exists(x: Nat) { x = x }");
        env.assert_def_ne("bex1", "nex1");
    }

    #[test]
    fn test_arg_binding() {
        let mut env = Environment::new_test();
        env.bad("define qux(x: Bool, x: Bool) -> Bool: x");
        assert!(!env.bindings.has_identifier("x"));
        env.add("define qux(x: Bool, y: Bool) -> Bool: x");
        env.expect_type("qux", "(Bool, Bool) -> Bool");

        env.bad("theorem foo(x: Bool, x: Bool): x");
        assert!(!env.bindings.has_identifier("x"));
        env.add("theorem foo(x: Bool, y: Bool): x");
        env.expect_type("foo", "(Bool, Bool) -> Bool");

        env.bad("let bar: Bool = forall(x: Bool, x: Bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let bar: Bool = forall(x: Bool, y: Bool) { x = x }");

        env.bad("let baz: Bool = exists(x: Bool, x: Bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let baz: Bool = exists(x: Bool, y: Bool) { x = x }");
    }

    #[test]
    fn test_no_double_grouped_arg_list() {
        let mut env = Environment::new_test();
        env.add("define foo(x: Bool, y: Bool) -> Bool: x");
        env.add("let b: Bool = axiom");
        env.bad("foo((b, b))");
    }

    #[test]
    fn test_argless_theorem() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.add("theorem foo: b | !b");
        env.expect_def("foo", "(b | !b)");
    }

    #[test]
    fn test_forall_value() {
        let mut env = Environment::new_test();
        env.add("let p: Bool = forall(x: Bool) { x | !x }");
        env.expect_def("p", "forall(x0: Bool) { (x0 | !x0) }");
    }

    #[test]
    fn test_inline_function_value() {
        let mut env = Environment::new_test();
        env.add("define ander(a: Bool) -> (Bool -> Bool): function(b: Bool) { a & b }");
        env.expect_def(
            "ander",
            "function(x0: Bool) { function(x1: Bool) { (x0 & x1) } }",
        );
    }

    #[test]
    fn test_empty_if_block() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.add("if b {}");
    }

    #[test]
    fn test_empty_forall_statement() {
        // Allowed as statement but not as an expression.
        let mut env = Environment::new_test();
        env.add("forall(b: Bool) {}");
    }

    #[test]
    fn test_nat_ac_piecewise() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("let suc: Nat -> Nat = axiom");
        env.add("let 1: Nat = suc(0)");
        env.expect_def("1", "suc(0)");

        env.add("axiom suc_injective(x: Nat, y: Nat): suc(x) = suc(y) -> x = y");
        env.expect_type("suc_injective", "(Nat, Nat) -> Bool");
        env.expect_def(
            "suc_injective",
            "function(x0: Nat, x1: Nat) { ((suc(x0) = suc(x1)) -> (x0 = x1)) }",
        );

        env.add("axiom suc_neq_zero(x: Nat): suc(x) != 0");
        env.expect_def("suc_neq_zero", "function(x0: Nat) { (suc(x0) != 0) }");

        assert!(env.bindings.has_type_name("Nat"));
        assert!(!env.bindings.has_identifier("Nat"));

        assert!(!env.bindings.has_type_name("0"));
        assert!(env.bindings.has_identifier("0"));

        assert!(!env.bindings.has_type_name("1"));
        assert!(env.bindings.has_identifier("1"));

        assert!(!env.bindings.has_type_name("suc"));
        assert!(env.bindings.has_identifier("suc"));

        assert!(!env.bindings.has_type_name("foo"));
        assert!(!env.bindings.has_identifier("foo"));

        env.add(
            "axiom induction(f: Nat -> Bool, n: Nat):
            f(0) & forall(k: Nat) { f(k) -> f(suc(k)) } -> f(n)",
        );
        env.expect_def("induction", "function(x0: Nat -> Bool, x1: Nat) { ((x0(0) & forall(x2: Nat) { (x0(x2) -> x0(suc(x2))) }) -> x0(x1)) }");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat: axiom");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a");
        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat):
            recursion(f, a, suc(n)) = f(recursion(f, a, n))",
        );

        env.add("define add(a: Nat, b: Nat) -> Nat: recursion(suc, a, b)");
        env.expect_type("add", "(Nat, Nat) -> Nat");

        env.add("theorem add_zero_right(a: Nat): add(a, 0) = a");
        env.add("theorem add_zero_left(a: Nat): add(0, a) = a");
        env.add("theorem add_suc_right(a: Nat, b: Nat): add(a, suc(b)) = suc(add(a, b))");
        env.add("theorem add_suc_left(a: Nat, b: Nat): add(suc(a), b) = suc(add(a, b))");
        env.add("theorem add_comm(a: Nat, b: Nat): add(a, b) = add(b, a)");
        env.add("theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c))");
        env.add("theorem not_suc_eq_zero(x: Nat): !(suc(x) = 0)");
    }

    #[test]
    fn test_nat_ac_together() {
        let mut env = Environment::new_test();
        env.add(
            r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

let 0: Nat = axiom

let suc: Nat -> Nat = axiom
let 1: Nat = suc(0)

axiom suc_injective(x: Nat, y: Nat): suc(x) = suc(y) -> x = y

axiom suc_neq_zero(x: Nat): suc(x) != 0

axiom induction(f: Nat -> Bool): f(0) & forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) }

// The old version. In the modern codebase these are parametric.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat: axiom
axiom recursion_base(f: Nat -> Nat, a: Nat): recursion(f, a, 0) = a
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat): recursion(f, a, suc(n)) = f(recursion(f, a, n))

define add(a: Nat, b: Nat) -> Nat: recursion(suc, a, b)

// Now let's have some theorems.

theorem add_zero_right(a: Nat): add(a, 0) = a

theorem add_zero_left(a: Nat): add(0, a) = a

theorem add_suc_right(a: Nat, b: Nat): add(a, suc(b)) = suc(add(a, b))

theorem add_suc_left(a: Nat, b: Nat): add(suc(a), b) = suc(add(a, b))

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
                define d(e: Nat) -> Bool: foo(e, b)
            }
            "#,
        );
        env.check_lines();
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
            define foo(x: Nat) -> Bool: axiom
            theorem goal: true by {
                exists(z: Nat) { foo(z) }
                foo(z)
            }
        "#,
        );
    }

    #[test]
    fn test_if_block_ending_with_exists() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: Bool = axiom
            theorem goal: a by {
                if a {
                    exists(b: Bool) { b = b }
                }
            }
            "#,
        );
        let module = p.expect_ok("main");
        let env = p.get_env(module).unwrap();
        for path in env.goal_paths() {
            env.get_goal_context(&p, &path).unwrap();
        }
    }

    #[test]
    fn test_forall_block_ending_with_exists() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: Bool = axiom
            theorem goal: a by {
                forall(b: Bool) {
                    exists(c: Bool) { c = c }
                }
            }
            "#,
        );
        let module = p.expect_ok("main");
        let env = p.get_env(module).unwrap();
        for path in env.goal_paths() {
            env.get_goal_context(&p, &path).unwrap();
        }
    }

    #[test]
    fn test_struct_new_definition() {
        let mut env = Environment::new_test();
        env.add(
            r#"
        struct BoolPair {
            first: Bool
            second: Bool
        }
        theorem goal(p: BoolPair): p = BoolPair.new(BoolPair.first(p), BoolPair.second(p))
        "#,
        );
    }

    #[test]
    fn test_struct_cant_contain_itself() {
        // It seems like this would be okay, but type theory says it isn't okay, and
        // there's definitely a paradox if we allow full self-reference in type construction,
        // so let's ban it.
        let mut env = Environment::new_test();
        env.bad(
            r#"
        struct InfiniteBools {
            head: Bool
            tail: InfiniteBools
        }
        "#,
        );
    }

    #[test]
    fn test_no_russell_paradox() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
        struct NaiveSet {
            set: NaiveSet -> Bool 
        }
        "#,
        );
    }

    #[test]
    fn test_parametric_types_required_in_function_args() {
        let mut env = Environment::new_test();
        env.bad("define foo<T>(a: Bool) -> Bool = a");
    }

    #[test]
    fn test_parametric_types_required_in_theorem_args() {
        let mut env = Environment::new_test();
        env.bad("theorem foo<T>(a: Bool): a | !a");
    }

    #[test]
    fn test_template_typechecking() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("define eq<T>(a: T, b: T) -> Bool: a = b");
        env.add("theorem t1: eq(0, 0)");
        env.add("theorem t2: eq(0 = 0, 0 = 0)");
        env.add("theorem t3: eq(0 = 0, eq(0, 0))");
        env.bad("theorem t4: eq(0, 0 = 0)");
        env.bad("theorem t5: 0 = eq(0, 0)");
    }

    #[test]
    fn test_type_params_cleaned_up() {
        let mut env = Environment::new_test();
        env.add("define foo<T>(a: T) -> Bool: axiom");
        assert!(env.bindings.get_type_for_name("T").is_none());
    }

    #[test]
    fn test_if_condition_must_be_bool() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("let b: Bool = axiom");
        env.add("if b { 0 = 0 }");
        env.bad("if 0 { 0 = 0 }");
    }

    #[test]
    fn test_reusing_type_name_as_var_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let Nat: Bool = axiom");
    }

    #[test]
    fn test_reusing_var_name_as_type_name() {
        let mut env = Environment::new_test();
        env.add("let x: Bool = axiom");
        env.bad("type x: axiom");
    }

    #[test]
    fn test_reusing_type_name_as_fn_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define Nat(x: Bool) -> Bool: x");
    }

    #[test]
    fn test_reusing_type_name_as_theorem_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("theorem Nat(x: Bool): x = x");
    }

    #[test]
    fn test_reusing_type_name_as_exists_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: Bool = exists(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_forall_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: Bool = forall(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_lambda_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let f: (bool, bool) -> Bool = function(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_parsing_true_false_keywords() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = true | false");
    }

    #[test]
    fn test_nothing_after_explicit_false() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.bad(
            r#"
            if b = !b {
                false
                b
            }
        "#,
        );
    }

    #[test]
    fn test_condition_must_be_valid() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
            if a {
            }
        "#,
        );
    }

    #[test]
    fn test_inline_function_in_forall_block() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("let suc: Nat -> Nat = axiom");
        env.add(
            r#"
            axiom induction(f: Nat -> Bool):
                f(0) & forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) }
            "#,
        );
        env.add(
            r#"
            forall(f: (Nat, Bool) -> Bool) {
                induction(function(x: Nat) { f(x, true) })
            }
        "#,
        );
    }

    #[test]
    fn test_structs_must_be_capitalized() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
            struct foo {
                bar: Bool
            }
        "#,
        );
    }

    #[test]
    fn test_axiomatic_types_must_be_capitalized() {
        let mut env = Environment::new_test();
        env.bad("type foo: axiom");
    }

    #[test]
    fn test_functional_definition_typechecking() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define foo(f: Nat -> Nat) -> Bool: function(x: Nat) { true }");
    }

    #[test]
    fn test_partial_application() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let 0: Nat = axiom");
        env.add("define add3(a: Nat, b: Nat, c: Nat) -> Nat: axiom");
        env.add("let add0: (Nat, Nat) -> Nat = add3(0)");
        env.add("let add00: Nat -> Nat = add3(0, 0)");
        env.add("let add00_alt: Nat -> Nat = add0(0)");
    }

    #[test]
    fn test_else_on_new_line() {
        // This is ugly but it should work.
        let mut env = Environment::new_test();
        env.add(
            r#"
        let b: Bool = axiom
        if b {
            b
        }
        else {
            !b
        }
        "#,
        );
    }

    #[test]
    fn test_arg_names_lowercased() {
        let mut env = Environment::new_test();
        env.bad("let f: Bool -> Bool = function(A: Bool) { true }");
        env.add("let f: Bool -> Bool = function(a: Bool) { true }");
        env.bad("forall(A: Bool) { true }");
        env.add("forall(a: Bool) { true }");
        env.bad("define foo(X: Bool) -> Bool: true");
        env.add("define foo(x: Bool) -> Bool: true");
        env.bad("theorem bar(X: Bool): true");
        env.add("theorem bar(x: Bool): true");
        env.bad("exists(A: Bool) { true }");
        env.add("exists(a: Bool) { true }");
    }

    #[test]
    fn test_undefined_class_name() {
        let mut env = Environment::new_test();
        env.bad("class Foo {}");
    }

    #[test]
    fn test_class_variables() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                let 0: Nat = axiom
                let 1: Nat = axiom
            }

            axiom zero_neq_one(x: Nat): Nat.0 = Nat.1
        "#,
        );

        // Class variables shouldn't get bound at module scope
        env.bad("let zero: Nat = 0");
    }

    #[test]
    fn test_instance_methods() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define add(self: Nat, other: Nat) -> Nat: axiom
            }
        "#,
        );
    }

    #[test]
    fn test_no_methods_on_type_aliases() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("type NatFn: Nat -> Nat");
        env.bad("class NatFn {}");
    }

    #[test]
    fn test_first_arg_must_be_self() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                define add(a: Nat, b: Nat) -> Nat: axiom
            }
            "#,
        );
    }

    #[test]
    fn test_no_self_variables() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let foo: Bool = exists(self: Nat) { true }");
        env.bad("let foo: Bool = forall(self: Nat) { true }");
        env.bad("let self: Nat = axiom");
    }

    #[test]
    fn test_no_self_args_outside_class() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define foo(self: Nat) -> Bool: true");
    }

    #[test]
    fn test_no_self_as_forall_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("forall(self: Nat) { true }");
    }

    #[test]
    fn test_no_self_as_exists_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("exists(self: Nat) { true }");
    }

    #[test]
    fn test_no_self_as_lambda_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let f: Nat -> Bool = lambda(self: Nat) { true }");
    }

    // #[test]
    // fn test_using_member_function() {
    //     let mut env = Environment::new_test();
    //     env.add(
    //         r#"
    //         type Nat: axiom
    //         class Nat {
    //             define add(self: Nat, other: Nat) -> Nat: axiom
    //         }
    //         theorem goal(a: Nat, b: Nat): a.add(b) = b.add(a)
    //     "#,
    //     );
    // }

    // #[test]
    // fn test_infix_add() {
    //     let mut env = Environment::new_test();
    //     env.add(
    //         r#"
    //         type Nat: axiom
    //         class Nat {
    //             define add(self: Nat, other: Nat) -> Nat: axiom
    //         }
    //         theorem goal(a: Nat, b: Nat): a + b = b + a
    //     "#,
    //     );
    // }
}
