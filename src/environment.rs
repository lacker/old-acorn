use std::collections::HashMap;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp, FunctionApplication};
use crate::atom::AtomId;
use crate::binding_map::{BindingMap, Stack};
use crate::block::{Block, BlockParams, Node, NodeCursor};
use crate::fact::Fact;
use crate::module::ModuleId;
use crate::project::{LoadError, Project};
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::statement::{Body, DefineStatement, LetStatement, Statement, StatementInfo};
use crate::token::{self, Error, Token, TokenIter, TokenType};

// Each line has a LineType, to handle line-based user interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LineType {
    // Only used within subenvironments.
    // The line relates to the block, but is outside the opening brace for this block.
    Opening,

    // This line corresponds to a node inside the environment.
    // The usize is an index into the nodes array.
    // If the node represents a block, this line should also have a line type in the
    // subenvironment within the block.
    Node(usize),

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

    // The nodes structure is fundamentally linear.
    // Each node depends only on the nodes before it.
    pub nodes: Vec<Node>,

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

    // Whether this environment is at the top level of a module.
    pub top_level: bool,
}

impl Environment {
    pub fn new(module_id: ModuleId) -> Self {
        Environment {
            module_id,
            bindings: BindingMap::new(module_id),
            nodes: Vec::new(),
            definition_ranges: HashMap::new(),
            includes_explicit_false: false,
            first_line: 0,
            line_types: Vec::new(),
            implicit: false,
            top_level: true,
        }
    }

    // Create a child environment.
    pub fn child(&self, first_line: u32, implicit: bool) -> Self {
        Environment {
            module_id: self.module_id,
            bindings: self.bindings.clone(),
            nodes: Vec::new(),
            definition_ranges: self.definition_ranges.clone(),
            includes_explicit_false: false,
            first_line,
            line_types: Vec::new(),
            implicit,
            top_level: false,
        }
    }

    fn next_line(&self) -> u32 {
        self.line_types.len() as u32 + self.first_line
    }

    pub fn last_line(&self) -> u32 {
        self.next_line() - 1
    }

    pub fn theorem_range(&self, name: &str) -> Option<Range> {
        self.definition_ranges.get(name).cloned()
    }

    // Add line types for the given range, inserting empties as needed.
    // If the line already has a type, do nothing.
    pub fn add_line_types(&mut self, line_type: LineType, first: u32, last: u32) {
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
            LineType::Node(index),
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

    // Adds a node to the environment tree.
    // This also macro-expands theorem names into their definitions.
    // Ideally, that would happen during expression parsing.
    // However, it needs to work with templated theorems, which makes it tricky/hacky to do the
    // type inference.
    pub fn add_node(
        &mut self,
        project: &Project,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> usize {
        let node = Node::new(project, self, structural, proposition, block);
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    // Adds a proposition, or multiple propositions, to represent the definition of the provided
    // constant.
    pub fn add_identity_props(&mut self, project: &Project, name: &str) {
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
            let app = AcornValue::new_apply(constant.clone(), args);
            AcornValue::ForAll(
                acorn_types,
                Box::new(AcornValue::Binary(
                    BinaryOp::Equals,
                    Box::new(app),
                    return_value,
                )),
            )
        } else {
            AcornValue::new_equals(constant.clone(), definition)
        };
        let range = self.definition_ranges.get(name).unwrap().clone();

        self.add_node(
            project,
            true,
            Proposition::constant_definition(claim, self.module_id, range, constant),
            None,
        );
    }

    pub fn get_definition(&self, name: &str) -> Option<&AcornValue> {
        self.bindings.get_definition(name)
    }

    pub fn get_theorem_claim(&self, name: &str) -> Option<AcornValue> {
        for prop in &self.nodes {
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
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
            BlockParams::Conditional(&condition, range),
            first_line,
            last_line,
            Some(body),
        )?;
        let (outer_claim, claim_range) = block.export_last_claim(self, &body.right_brace)?;

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
        let index = self.add_node(
            project,
            false,
            Proposition::anonymous(external_claim, self.module_id, claim_range),
            Some(block),
        );
        self.add_line_types(
            LineType::Node(index),
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
        if class.is_none() && ls.name_token.token_type == TokenType::Numeral {
            return Err(Error::new(
                &ls.name_token,
                "numeric literals may not be defined outside of a class",
            ));
        }
        if ls.name == "self"
            || ls.name == "new"
            || ls.name == "read"
            || (class.is_some() && TokenType::from_magic_method_name(&ls.name).is_some())
        {
            return Err(Error::new(
                &ls.name_token,
                &format!("'{}' is a reserved word. use a different name", ls.name),
            ));
        }
        let name = match class {
            Some(c) => format!("{}.{}", c, ls.name),
            None => ls.name.clone(),
        };
        if self.bindings.name_in_use(&name) {
            return Err(Error::new(
                &ls.name_token,
                &format!("constant name '{}' already defined in this scope", name),
            ));
        }
        let acorn_type = self.bindings.evaluate_type(project, &ls.type_expr)?;
        if ls.name_token.token_type == TokenType::Numeral {
            if acorn_type != AcornType::Data(self.module_id, class.unwrap().to_string()) {
                return Err(Error::new(
                    &ls.type_expr.token(),
                    "numeric class variables must be the class type",
                ));
            }
        }
        let value = if ls.value.token().token_type == TokenType::Axiom {
            None
        } else {
            Some(
                self.bindings
                    .evaluate_value(project, &ls.value, Some(&acorn_type))?,
            )
        };
        if self.bindings.add_constant(&name, vec![], acorn_type, value) {
            // This is a new constant, so we should track where it's defined
            self.definition_ranges.insert(name.clone(), range);
            self.add_identity_props(project, &name);
        }
        Ok(())
    }

    // Adds a "define" statement to the environment, that may be within a class block.
    fn add_define_statement(
        &mut self,
        project: &Project,
        class_name: Option<&str>,
        ds: &DefineStatement,
        range: Range,
    ) -> token::Result<()> {
        if ds.name == "new" || ds.name == "self" {
            return Err(Error::new(
                &ds.name_token,
                &format!("'{}' is a reserved word. use a different name", ds.name),
            ));
        }
        let name = match class_name {
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
                class_name,
            )?;

        if let Some(class_name) = class_name {
            let class_type = AcornType::Data(self.module_id, class_name.to_string());
            if arg_types[0] != class_type {
                return Err(Error::new(
                    ds.args[0].token(),
                    "self must be the class type",
                ));
            }

            if ds.name == "read" {
                if arg_types.len() != 2 || arg_types[1] != class_type || value_type != class_type {
                    return Err(Error::new(
                        &ds.name_token,
                        &format!(
                            "{}.read should be type ({}, {}) -> {}",
                            class_name, class_name, class_name, class_name
                        ),
                    ));
                }
            }
        }

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
        self.add_identity_props(project, &name);
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
                    end: ts.claim_right_brace.end_pos(),
                };
                self.definition_ranges.insert(ts.name.to_string(), range);

                let (type_params, arg_names, arg_types, value, _) = self
                    .bindings
                    .evaluate_subvalue(project, &ts.type_params, &ts.args, None, &ts.claim, None)?;

                let unbound_claim = value.ok_or_else(|| {
                    Error::new(&statement.first_token, "theorems must have values")
                })?;

                let is_citation = self.bindings.is_citation(project, &unbound_claim);
                if is_citation && ts.body.is_some() {
                    return Err(Error::new(
                        &statement.first_token,
                        "citations do not need proof blocks",
                    ));
                }

                let mut block_args = vec![];
                for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
                    block_args.push((arg_name.clone(), arg_type.clone()));
                }

                // Externally we use the theorem in unnamed, "forall" form
                let external_claim =
                    AcornValue::new_forall(arg_types.clone(), unbound_claim.clone());

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

                let already_proven = ts.axiomatic || is_citation;

                let block = if already_proven {
                    None
                } else {
                    Some(Block::new(
                        project,
                        &self,
                        type_params,
                        block_args,
                        BlockParams::Theorem(&ts.name, premise, goal),
                        statement.first_line(),
                        statement.last_line(),
                        ts.body.as_ref(),
                    )?)
                };

                let index = self.add_node(
                    project,
                    already_proven,
                    Proposition::theorem(
                        already_proven,
                        external_claim,
                        self.module_id,
                        range,
                        ts.name.to_string(),
                    ),
                    block,
                );
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

                if self.bindings.is_citation(project, &claim) {
                    // We already know this is true, so we don't need to prove it
                    self.add_node(
                        project,
                        true,
                        Proposition::anonymous(claim, self.module_id, statement.range()),
                        None,
                    );
                    self.add_other_lines(statement);
                } else {
                    let index = self.add_node(
                        project,
                        false,
                        Proposition::anonymous(claim, self.module_id, statement.range()),
                        None,
                    );
                    self.add_prop_lines(index, statement);
                }
                Ok(())
            }

            StatementInfo::ForAll(fas) => {
                if fas.body.statements.is_empty() {
                    // ForAll statements with an empty body can just be ignored
                    return Ok(());
                }
                let mut args = vec![];
                for quantifier in &fas.quantifiers {
                    let (arg_name, arg_type) =
                        self.bindings.evaluate_declaration(project, quantifier)?;
                    args.push((arg_name, arg_type));
                }

                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    args,
                    BlockParams::ForAll,
                    statement.first_line(),
                    statement.last_line(),
                    Some(&fas.body),
                )?;

                let (outer_claim, range) = block.export_last_claim(self, &fas.body.right_brace)?;

                let index = self.add_node(
                    project,
                    false,
                    Proposition::anonymous(outer_claim, self.module_id, range),
                    Some(block),
                );
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

            StatementInfo::VariableSatisfy(vss) => {
                // We need to prove the general existence claim
                let mut stack = Stack::new();
                let (quant_names, quant_types) =
                    self.bindings
                        .bind_args(&mut stack, project, &vss.declarations, None)?;
                let general_claim_value = self.bindings.evaluate_value_with_stack(
                    &mut stack,
                    project,
                    &vss.condition,
                    Some(&AcornType::Bool),
                )?;
                let general_claim =
                    AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value));
                let index = self.add_node(
                    project,
                    false,
                    Proposition::anonymous(general_claim, self.module_id, statement.range()),
                    None,
                );
                self.add_prop_lines(index, statement);

                // Define the quantifiers as constants
                for (quant_name, quant_type) in quant_names.iter().zip(quant_types.iter()) {
                    self.bindings
                        .add_constant(quant_name, vec![], quant_type.clone(), None);
                }

                // We can then assume the specific existence claim with the named constants
                let specific_claim = self.bindings.evaluate_value(
                    project,
                    &vss.condition,
                    Some(&AcornType::Bool),
                )?;
                self.add_node(
                    project,
                    true,
                    Proposition::anonymous(specific_claim, self.module_id, statement.range()),
                    None,
                );

                Ok(())
            }

            StatementInfo::FunctionSatisfy(fss) => {
                if fss.name == "new" || fss.name == "self" {
                    return Err(Error::new(
                        &fss.name_token,
                        &format!("'{}' is a reserved word. use a different name", fss.name),
                    ));
                }
                if self.bindings.name_in_use(&fss.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        &format!("function name '{}' already defined in this scope", fss.name),
                    ));
                }

                // Figure out the range for this function definition.
                // It's smaller than the whole function statement because it doesn't
                // include the proof block.
                let definition_range = Range {
                    start: statement.first_token.start_pos(),
                    end: fss.satisfy_token.end_pos(),
                };
                self.definition_ranges
                    .insert(fss.name.clone(), definition_range);

                let (_, mut arg_names, mut arg_types, condition, _) =
                    self.bindings.evaluate_subvalue(
                        project,
                        &[],
                        &fss.declarations,
                        None,
                        &fss.condition,
                        None,
                    )?;

                let unbound_condition = condition
                    .ok_or_else(|| Error::new(&statement.first_token, "missing condition"))?;
                if unbound_condition.get_type() != AcornType::Bool {
                    return Err(Error::new(
                        &fss.condition.token(),
                        "condition must be a boolean",
                    ));
                }

                // The return variable shouldn't become a block arg, because we're trying to
                // prove its existence.
                let _return_name = arg_names.pop().unwrap();
                let return_type = arg_types.pop().unwrap();
                let block_args: Vec<_> = arg_names
                    .iter()
                    .cloned()
                    .zip(arg_types.iter().cloned())
                    .collect();
                let num_args = block_args.len() as AtomId;

                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    block_args,
                    BlockParams::FunctionSatisfy(
                        unbound_condition.clone(),
                        return_type.clone(),
                        fss.condition.range(),
                    ),
                    statement.first_line(),
                    statement.last_line(),
                    fss.body.as_ref(),
                )?;

                // We define this function not with an equality, but via the condition.
                let function_type = AcornType::new_functional(arg_types.clone(), return_type);
                self.bindings
                    .add_constant(&fss.name, vec![], function_type.clone(), None);
                let function_constant =
                    AcornValue::Constant(self.module_id, fss.name.clone(), function_type, vec![]);
                let function_term = AcornValue::new_apply(
                    function_constant.clone(),
                    arg_types
                        .iter()
                        .enumerate()
                        .map(|(i, t)| AcornValue::Variable(i as AtomId, t.clone()))
                        .collect(),
                );
                let return_bound =
                    unbound_condition.bind_values(num_args, num_args, &[function_term]);
                let external_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

                let prop = Proposition::constant_definition(
                    external_condition,
                    self.module_id,
                    definition_range,
                    function_constant,
                );

                let index = self.add_node(project, false, prop, Some(block));
                self.add_prop_lines(index, statement);
                Ok(())
            }

            StatementInfo::Structure(ss) => {
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
                    if TokenType::from_magic_method_name(&field_name_token.text()).is_some() {
                        return Err(Error::new(
                            field_name_token,
                            &format!(
                                "'{}' is a reserved word. use a different name",
                                field_name_token.text()
                            ),
                        ));
                    }
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
                self.add_node(
                    project,
                    true,
                    Proposition::type_definition(new_claim, self.module_id, range, ss.name.clone()),
                    None,
                );

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
                    self.add_node(
                        project,
                        true,
                        Proposition::type_definition(
                            member_claim,
                            self.module_id,
                            range,
                            ss.name.clone(),
                        ),
                        None,
                    );
                }

                Ok(())
            }

            StatementInfo::Inductive(is) => {
                self.add_other_lines(statement);
                if self.bindings.has_type_name(&is.name) {
                    return Err(Error::new(
                        &statement.first_token,
                        "type name already defined in this scope",
                    ));
                }
                let range = Range {
                    start: statement.first_token.start_pos(),
                    end: is.name_token.end_pos(),
                };

                // Add the new type first, because we can have self-reference in the inductive type.
                let inductive_type = self.bindings.add_data_type(&is.name);

                // Parse (member name, list of arg types) for each constructor.
                let mut constructors = vec![];
                let mut has_base = false;
                for (name_token, type_list_expr) in &is.constructors {
                    let type_list = match type_list_expr {
                        Some(expr) => {
                            let mut type_list = vec![];
                            self.bindings
                                .evaluate_type_list(project, expr, &mut type_list)?;
                            type_list
                        }
                        None => vec![],
                    };
                    if !type_list.contains(&inductive_type) {
                        // This provides a base case
                        has_base = true;
                    }
                    let member_name = format!("{}.{}", is.name, name_token.text());
                    constructors.push((member_name, type_list));
                }
                if !has_base {
                    return Err(Error::new(
                        &statement.first_token,
                        "inductive type must have a base case",
                    ));
                }

                // Define the constructors.
                let mut constructor_fns = vec![];
                for (constructor_name, type_list) in &constructors {
                    let constructor_type =
                        AcornType::new_functional(type_list.clone(), inductive_type.clone());
                    self.bindings
                        .add_constant(constructor_name, vec![], constructor_type, None);
                    constructor_fns
                        .push(self.bindings.get_constant_value(constructor_name).unwrap());
                }

                // The "no confusion" property. Different constructors give different results.
                for i in 0..constructors.len() {
                    let (_, i_arg_types) = &constructors[i];
                    let i_fn = constructor_fns[i].clone();
                    let i_vars: Vec<_> = i_arg_types
                        .iter()
                        .enumerate()
                        .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                        .collect();
                    let i_app = AcornValue::new_apply(i_fn, i_vars);
                    for j in 0..i {
                        let (_, j_arg_types) = &constructors[j];
                        let j_fn = constructor_fns[j].clone();
                        let j_vars: Vec<_> = j_arg_types
                            .iter()
                            .enumerate()
                            .map(|(k, t)| {
                                AcornValue::Variable((k + i_arg_types.len()) as AtomId, t.clone())
                            })
                            .collect();
                        let j_app = AcornValue::new_apply(j_fn, j_vars);
                        let inequality = AcornValue::new_not_equals(i_app.clone(), j_app);
                        let mut quantifiers = i_arg_types.clone();
                        quantifiers.extend(j_arg_types.clone());
                        let claim = AcornValue::new_forall(quantifiers, inequality);
                        self.add_node(
                            project,
                            true,
                            Proposition::type_definition(
                                claim,
                                self.module_id,
                                range,
                                is.name.clone(),
                            ),
                            None,
                        );
                    }
                }

                // The "canonical form" principle. Any item of this type must be created by one
                // of the constructors.
                // It seems like this is implied by induction but let's just stick it in.
                // x0 is going to be the "generic item of this type".
                let mut disjunction_parts = vec![];
                for (i, constructor_fn) in constructor_fns.iter().enumerate() {
                    let (_, arg_types) = &constructors[i];
                    let args = arg_types
                        .iter()
                        .enumerate()
                        .map(|(k, t)| AcornValue::Variable((k + 1) as AtomId, t.clone()))
                        .collect();
                    let app = AcornValue::new_apply(constructor_fn.clone(), args);
                    let var = AcornValue::Variable(0, inductive_type.clone());
                    let equality = AcornValue::new_equals(var, app);
                    let exists = AcornValue::new_exists(arg_types.clone(), equality);
                    disjunction_parts.push(exists);
                }
                let disjunction = AcornValue::reduce(BinaryOp::Or, disjunction_parts);
                let claim = AcornValue::new_forall(vec![inductive_type.clone()], disjunction);
                self.add_node(
                    project,
                    true,
                    Proposition::type_definition(claim, self.module_id, range, is.name.clone()),
                    None,
                );

                // The next principle is that each constructor is injective.
                // Ie if Type.construct(x0, x1) = Type.construct(x2, x3) then x0 = x2 and x1 = x3.
                for (i, constructor_fn) in constructor_fns.iter().enumerate() {
                    let (_, arg_types) = &constructors[i];
                    if arg_types.is_empty() {
                        continue;
                    }

                    // First construct the equality.
                    // "Type.construct(x0, x1) = Type.construct(x2, x3)"
                    let left_args = arg_types
                        .iter()
                        .enumerate()
                        .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                        .collect();
                    let lhs = AcornValue::new_apply(constructor_fn.clone(), left_args);
                    let right_args = arg_types
                        .iter()
                        .enumerate()
                        .map(|(k, t)| {
                            AcornValue::Variable((k + arg_types.len()) as AtomId, t.clone())
                        })
                        .collect();
                    let rhs = AcornValue::new_apply(constructor_fn.clone(), right_args);
                    let equality = AcornValue::new_equals(lhs, rhs);

                    // Then construct the implication, that the corresponding args are equal.
                    let mut conjunction_parts = vec![];
                    for (i, arg_type) in arg_types.iter().enumerate() {
                        let left = AcornValue::Variable(i as AtomId, arg_type.clone());
                        let right =
                            AcornValue::Variable((i + arg_types.len()) as AtomId, arg_type.clone());
                        let arg_equality = AcornValue::new_equals(left, right);
                        conjunction_parts.push(arg_equality);
                    }
                    let conjunction = AcornValue::reduce(BinaryOp::And, conjunction_parts);
                    let mut forall_types = arg_types.clone();
                    forall_types.extend_from_slice(&arg_types);
                    let claim = AcornValue::new_forall(
                        forall_types,
                        AcornValue::new_implies(equality, conjunction),
                    );
                    self.add_node(
                        project,
                        true,
                        Proposition::type_definition(claim, self.module_id, range, is.name.clone()),
                        None,
                    );
                }

                // Structural induction.
                // The type for the inductive hypothesis.
                let hyp_type =
                    AcornType::new_functional(vec![inductive_type.clone()], AcornType::Bool);
                // x0 represents the inductive hypothesis.
                // Think of the inductive principle as (conjunction) -> (conclusion).
                // The conjunction is a case for each constructor.
                // The conclusion is that x0 holds for all items of the type.
                let mut conjunction_parts = vec![];
                for (i, constructor_fn) in constructor_fns.iter().enumerate() {
                    let (_, arg_types) = &constructors[i];
                    let mut args = vec![];
                    let mut conditions = vec![];
                    for (j, arg_type) in arg_types.iter().enumerate() {
                        // x0 is the inductive hypothesis so we start at 1 for the
                        // constructor arguments.
                        let id = (j + 1) as AtomId;
                        args.push(AcornValue::Variable(id, arg_type.clone()));
                        if arg_type == &inductive_type {
                            // The inductive case for this constructor includes a condition
                            // that the inductive hypothesis holds for this argument.
                            conditions.push(AcornValue::new_apply(
                                AcornValue::Variable(0, hyp_type.clone()),
                                vec![AcornValue::Variable(id, arg_type.clone())],
                            ));
                        }
                    }

                    let new_instance = AcornValue::new_apply(constructor_fn.clone(), args);
                    let instance_claim = AcornValue::new_apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![new_instance],
                    );
                    let unbound = if conditions.is_empty() {
                        // This is a base case. We just need to show that the inductive hypothesis
                        // holds for this constructor.
                        instance_claim
                    } else {
                        // This is an inductive case. Given the conditions, we show that
                        // the inductive hypothesis holds for this constructor.
                        AcornValue::new_implies(
                            AcornValue::reduce(BinaryOp::And, conditions),
                            instance_claim,
                        )
                    };
                    let conjunction_part = AcornValue::new_forall(arg_types.clone(), unbound);
                    conjunction_parts.push(conjunction_part);
                }
                let conjunction = AcornValue::reduce(BinaryOp::And, conjunction_parts);
                let conclusion = AcornValue::new_forall(
                    vec![inductive_type.clone()],
                    AcornValue::new_apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![AcornValue::Variable(1, inductive_type.clone())],
                    ),
                );
                let unbound_claim = AcornValue::new_implies(conjunction, conclusion);

                // The lambda form is the functional form, which we bind in the environment.
                let name = format!("{}.induction", is.name);
                let lambda_claim =
                    AcornValue::new_lambda(vec![hyp_type.clone()], unbound_claim.clone());
                self.bindings.add_constant(
                    &name,
                    vec![],
                    lambda_claim.get_type(),
                    Some(lambda_claim),
                );
                self.bindings.mark_as_theorem(&name);

                // The forall form is the anonymous truth of induction. We add that as a proposition.
                let forall_claim = AcornValue::new_forall(vec![hyp_type], unbound_claim);
                self.add_node(
                    project,
                    true,
                    Proposition::theorem(true, forall_claim, self.module_id, range, name),
                    None,
                );

                Ok(())
            }

            StatementInfo::Import(is) => {
                self.add_other_lines(statement);

                // Give a local name to the imported module
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
                        // The error is with the import statement itself, like a circular import.
                        return Err(Error::new(
                            &statement.first_token,
                            &format!("import error: {}", s),
                        ));
                    }
                };
                if project.get_bindings(module_id).is_none() {
                    // The fundamental error is in the other module, not this one.
                    return Err(Error::external(
                        &statement.first_token,
                        &format!("error in '{}' module", full_name),
                    ));
                }
                self.bindings.add_module(local_name, module_id);

                // Bring the imported names into this environment
                for name in &is.names {
                    self.bindings.import_name(project, module_id, name)?;
                }

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
                                Some(&cs.name),
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

            StatementInfo::Numerals(ds) => {
                self.add_other_lines(statement);
                let acorn_type = self.bindings.evaluate_type(project, &ds.type_expr)?;
                if let AcornType::Data(module, typename) = acorn_type {
                    self.bindings.set_default(module, typename);
                    Ok(())
                } else {
                    Err(Error::new(
                        &ds.type_expr.token(),
                        "numerals type must be a data type",
                    ))
                }
            }

            StatementInfo::Solve(ss) => {
                let target = self.bindings.evaluate_value(project, &ss.target, None)?;
                let solve_range = Range {
                    start: statement.first_token.start_pos(),
                    end: ss.target.last_token().end_pos(),
                };

                let mut block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Solve(target.clone(), solve_range),
                    statement.first_line(),
                    statement.last_line(),
                    Some(&ss.body),
                )?;

                let prop = match block.solves(self, &target) {
                    Some((outer_claim, claim_range)) => {
                        block.goal = None;
                        Proposition::anonymous(outer_claim, self.module_id, claim_range)
                    }
                    None => {
                        // The block doesn't contain a solution.
                        // So, it has no claim that can be exported. It doesn't really make sense
                        // to export whatever the last proposition is.
                        // A lot of code expects something, though, so put a vacuous "true" in here.
                        Proposition::anonymous(
                            AcornValue::Bool(true),
                            self.module_id,
                            statement.range(),
                        )
                    }
                };

                let index = self.add_node(project, false, prop, Some(block));
                self.add_prop_lines(index, statement);
                Ok(())
            }

            StatementInfo::Problem(body) => {
                let block = Block::new(
                    project,
                    &self,
                    vec![],
                    vec![],
                    BlockParams::Problem,
                    statement.first_line(),
                    statement.last_line(),
                    Some(body),
                )?;

                // It would be nice to not have to make a vacuous "true" proposition here.
                let vacuous_prop = Proposition::anonymous(
                    AcornValue::Bool(true),
                    self.module_id,
                    statement.range(),
                );

                let index = self.add_node(project, false, vacuous_prop, Some(block));
                self.add_prop_lines(index, statement);
                Ok(())
            }
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

    // Get all facts that this environment exports.
    pub fn exported_facts(&self) -> Vec<Fact> {
        assert!(self.top_level);
        let mut facts = vec![];
        for node in &self.nodes {
            facts.push(Fact::new(node.claim.clone(), Truthiness::Factual));
        }
        facts
    }

    // Returns a NodeCursor for all nodes that correspond to a goal within this environment,
    // or subenvironments, recursively.
    // The order is "proving order", ie the goals inside the block are listed before the
    // root goal of a block.
    pub fn iter_goals(&self) -> impl Iterator<Item = NodeCursor> {
        let mut answer = vec![];
        for i in 0..self.nodes.len() {
            let mut cursor = NodeCursor::new(self, i);
            cursor.find_goals(&mut answer);
        }
        answer.into_iter()
    }

    // Used for integration testing.
    pub fn get_node_by_name(&self, name: &str) -> NodeCursor {
        let mut names = Vec::new();
        for node in self.iter_goals() {
            let context = node.goal_context().unwrap();
            if context.name == name {
                return node;
            }
            names.push(context.name);
        }

        panic!("no context found for {} in:\n{}\n", name, names.join("\n"));
    }

    // Returns the path to a given zero-based line.
    // This is a UI heuristic.
    // Either returns a path to a proposition, or an error message explaining why this
    // line is unusable.
    // Error messages use one-based line numbers.
    pub fn path_for_line(&self, line: u32) -> Result<Vec<usize>, String> {
        let mut path = vec![];
        let mut block: Option<&Block> = None;
        let mut env = self;
        loop {
            match env.get_line_type(line) {
                Some(LineType::Node(i)) => {
                    path.push(i);
                    let prop = &env.nodes[i];
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
                        if block.goal.is_none() {
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
                            Some(LineType::Node(i)) => {
                                let prop = &env.nodes[i];
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
                                        if block.goal.is_none() {
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
}

// Methods used for integration testing.
impl Environment {
    // Create a test version of the environment.
    pub fn new_test() -> Self {
        use crate::module::FIRST_NORMAL;
        Environment::new(FIRST_NORMAL)
    }

    // Adds a possibly multi-line statement to the environment.
    // Panics on failure.
    pub fn add(&mut self, input: &str) {
        let tokens = Token::scan(input);
        if let Err(e) = self.add_tokens(&mut Project::new_mock(), tokens) {
            panic!("error in add_tokens: {}", e);
        }
    }

    // Makes sure the lines are self-consistent
    pub fn check_lines(&self) {
        // Check that each proposition's block covers the lines it claims to cover
        for (line, line_type) in self.line_types.iter().enumerate() {
            if let LineType::Node(prop_index) = line_type {
                let prop = &self.nodes[*prop_index];
                if let Some(block) = &prop.block {
                    assert!(block.env.covers_line(line as u32));
                }
            }
        }

        // Recurse
        for prop in &self.nodes {
            if let Some(block) = &prop.block {
                block.env.check_lines();
            }
        }
    }

    // Expects the given line to be bad
    pub fn bad(&mut self, input: &str) {
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
    pub fn expect_type(&mut self, name: &str, type_string: &str) {
        self.bindings.expect_type(name, type_string)
    }

    // Check that the given name is defined to be this value
    pub fn expect_def(&mut self, name: &str, value_string: &str) {
        let env_value = match self.bindings.get_definition(name) {
            Some(t) => t,
            None => panic!("{} not found in environment", name),
        };
        assert_eq!(env_value.to_string(), value_string);
    }

    // Assert that these two names are defined to equal the same thing
    pub fn assert_def_eq(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_eq!(def1, def2);
    }

    // Assert that these two names are defined to be different things
    pub fn assert_def_ne(&self, name1: &str, name2: &str) {
        let def1 = self.bindings.get_definition(name1).unwrap();
        let def2 = self.bindings.get_definition(name2).unwrap();
        assert_ne!(def1, def2);
    }
}
