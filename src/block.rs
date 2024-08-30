use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::environment::{Environment, LineType};
use crate::fact::Fact;
use crate::goal::{Goal, GoalContext};
use crate::project::Project;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::statement::Body;
use crate::token::{self, Error, Token};

// Proofs are structured into blocks.
// The environment specific to this block can have a bunch of propositions that need to be
// proved, along with helper statements to express those propositions, but they are not
// visible to the outside world.
pub struct Block {
    // The generic types that this block is polymorphic over.
    // Internally to the block, these are opaque data types.
    // Externally, these are generic data types.
    type_params: Vec<String>,

    // The arguments to this block.
    // Internally to the block, the arguments are constants.
    // Externally, these arguments are variables.
    args: Vec<(String, AcornType)>,

    // The goal for a block is relative to its internal environment.
    // Everything in the block can be used to achieve this goal.
    pub goal: Option<Goal>,

    // The environment created inside the block.
    pub env: Environment,
}

impl Block {
    pub fn new(
        project: &mut Project,
        env: &Environment,
        type_params: Vec<String>,
        args: Vec<(String, AcornType)>,
        params: BlockParams,
        first_line: u32,
        last_line: u32,
        body: Option<&Body>,
    ) -> token::Result<Block> {
        let mut subenv = env.child(first_line, body.is_none());

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

        let goal = match params {
            BlockParams::Conditional(condition, range) => {
                subenv.add_node(
                    project,
                    true,
                    Proposition::premise(condition.clone(), env.module_id, range),
                    None,
                );
                None
            }
            BlockParams::Theorem(theorem_name, premise, unbound_goal) => {
                let arg_values = args
                    .iter()
                    .map(|(name, _)| subenv.bindings.get_constant_value(name).unwrap())
                    .collect::<Vec<_>>();

                // Within the theorem block, the theorem is treated like a function,
                // with propositions to define its identity.
                // This makes it less annoying to define inductive hypotheses.
                subenv.add_identity_props(project, theorem_name);

                if let Some((unbound_premise, premise_range)) = premise {
                    // Add the premise to the environment, when proving the theorem.
                    // The premise is unbound, so we need to bind the block's arg values.
                    let bound = unbound_premise.bind_values(0, 0, &arg_values);

                    subenv.add_node(
                        project,
                        true,
                        Proposition::premise(bound, env.module_id, premise_range),
                        None,
                    );
                }

                // We can prove the goal either in bound or in function form
                let bound_goal = unbound_goal.bind_values(0, 0, &arg_values);
                Some(Goal::Prove(Proposition::theorem(
                    false,
                    bound_goal,
                    env.module_id,
                    env.theorem_range(theorem_name).unwrap(),
                    theorem_name.to_string(),
                )))
            }
            BlockParams::FunctionSatisfy(unbound_goal, return_type, range) => {
                // In the block, we need to prove this goal in bound form, so bind args to it.
                let arg_values = args
                    .iter()
                    .map(|(name, _)| subenv.bindings.get_constant_value(name).unwrap())
                    .collect::<Vec<_>>();
                // The partial goal has variables 0..args.len() bound to the block's args,
                // but there one last variable that needs to be existentially quantified.
                let partial_goal = unbound_goal.bind_values(0, 0, &arg_values);
                let bound_goal = AcornValue::new_exists(vec![return_type], partial_goal);
                let prop = Proposition::anonymous(bound_goal, env.module_id, range);
                Some(Goal::Prove(prop))
            }
            BlockParams::Solve(target, range) => Some(Goal::Solve(target, range)),
            BlockParams::ForAll | BlockParams::Problem => None,
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
            goal,
        })
    }

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

    // Returns a claim usable in the outer environment, and a range where it comes from.
    pub fn export_last_claim(
        &self,
        outer_env: &Environment,
        token: &Token,
    ) -> token::Result<(AcornValue, Range)> {
        let (inner_claim, range) = match self.env.nodes.last() {
            Some(p) => (&p.claim.value, p.claim.source.range),
            None => {
                return Err(Error::new(token, "expected a claim in this block"));
            }
        };
        let outer_claim = self.export_bool(outer_env, inner_claim);
        Ok((outer_claim, range))
    }

    // Checks if this block solves for the given target.
    // If it does, returns an exported proposition with the solution, and the range where it
    // occurs.
    pub fn solves(
        &self,
        outer_env: &Environment,
        target: &AcornValue,
    ) -> Option<(AcornValue, Range)> {
        let (outer_claim, range) = match self.export_last_claim(outer_env, &Token::empty()) {
            Ok((c, r)) => (c, r),
            Err(_) => return None,
        };
        match &outer_claim {
            // We only allow <target> == <solution>, rather than the other way around.
            AcornValue::Binary(BinaryOp::Equals, left, _) => {
                if left.as_ref() == target {
                    Some((outer_claim, range))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

// The different ways to construct a block
pub enum BlockParams<'a> {
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

    // The expression to solve for, and the range of the "solve <target>" component.
    Solve(AcornValue, Range),

    // (unbound goal, function return type, range of condition)
    // This goal has one more unbound variable than the block args account for.
    // The last one, we are trying to prove there exists a variable that satisfies the goal.
    FunctionSatisfy(AcornValue, AcornType, Range),

    // No special params needed
    ForAll,
    Problem,
}

// Logically, the Environment is arranged like a tree structure.
// There are three types of nodes.
// 1. Structural nodes, that we can assume without proof
// 2. Plain claims, that we need to prove
// 3. Nodes with blocks, where we need to recurse into the block and prove those nodes.
pub struct Node {
    // Whether this proposition has already been proved structurally.
    // For example, this could be an axiom, or a definition.
    pub structural: bool,

    // The proposition represented by this tree.
    // If this proposition has a block, this represents the "external claim".
    // It is the value we can assume is true, in the outer environment, when everything
    // in the inner environment has been proven.
    // Besides the claim, nothing else from the block is visible externally.
    //
    // This claim needs to be proved for nonstructural propositions, when there is no block.
    pub claim: Proposition,

    // The body of the proposition, when it has an associated block.
    // When there is a block, proving every proposition in the block implies that the
    // claim is proven as well.
    pub block: Option<Block>,
}

impl Node {
    pub fn new(
        project: &Project,
        env: &Environment,
        structural: bool,
        proposition: Proposition,
        block: Option<Block>,
    ) -> Self {
        // Make sure we aren't adding an invalid claim.
        proposition
            .value
            .validate()
            .unwrap_or_else(|e| panic!("invalid claim: {} ({})", proposition.value, e));

        if structural {
            assert!(block.is_none());
        }

        let value = proposition
            .value
            .replace_constants_with_values(0, &|module_id, name| {
                let bindings = if env.module_id == module_id {
                    &env.bindings
                } else {
                    &project
                        .get_env(module_id)
                        .expect("missing module during add_proposition")
                        .bindings
                };
                if bindings.is_theorem(name) {
                    bindings.get_definition(name).clone()
                } else {
                    None
                }
            });
        let claim = proposition.with_value(value);
        Node {
            structural,
            claim,
            block,
        }
    }

    // Whether this node corresponds to a goal that needs to be proved.
    pub fn has_goal(&self) -> bool {
        if self.structural {
            return false;
        }
        match &self.block {
            Some(b) => b.goal.is_some(),
            None => true,
        }
    }
}

// A NodeCursor points at a node. It is used to traverse the nodes in an environment.
#[derive(Clone)]
pub struct NodeCursor<'a> {
    // All the environments that surround this node.
    // (env, index) pairs tell you that the node env.nodes[index] to get to
    // the next environment.
    annotated_path: Vec<(&'a Environment, usize)>,
}

impl fmt::Display for NodeCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.path())
    }
}

impl<'a> NodeCursor<'a> {
    pub fn from_path(env: &'a Environment, path: &[usize]) -> Self {
        assert!(path.len() > 0);
        let mut iter = NodeCursor::new(env, path[0]);
        for &i in &path[1..] {
            iter.descend(i);
        }
        iter
    }

    // Only call this on a module level environment.
    // Returns None if there are no nodes in the environment.
    pub fn new(env: &'a Environment, index: usize) -> Self {
        assert!(env.top_level);
        assert!(env.nodes.len() > index);
        NodeCursor {
            annotated_path: vec![(env, index)],
        }
    }

    pub fn env(&self) -> &'a Environment {
        self.annotated_path.last().unwrap().0
    }

    pub fn current(&self) -> &'a Node {
        let (env, index) = self.annotated_path.last().unwrap();
        &env.nodes[*index]
    }

    // Can use this as an identifier for the iterator, to compare two of them
    pub fn path(&self) -> Vec<usize> {
        self.annotated_path.iter().map(|(_, i)| *i).collect()
    }

    pub fn num_children(&self) -> usize {
        match self.current().block {
            Some(ref b) => b.env.nodes.len(),
            None => 0,
        }
    }

    // child_index must be less than num_children
    pub fn descend(&mut self, child_index: usize) {
        let new_env = match &self.current().block {
            Some(b) => &b.env,
            None => panic!("descend called on a node without a block"),
        };
        assert!(child_index < new_env.nodes.len());
        self.annotated_path.push((new_env, child_index));
    }

    // Whether we can advance to the next sibling, keeping environment the same.
    pub fn has_next(&self) -> bool {
        let (env, index) = self.annotated_path.last().unwrap();
        index + 1 < env.nodes.len()
    }

    // Advances to the next sibling, keeping environment the same.
    pub fn next(&mut self) {
        let (env, index) = self.annotated_path.last_mut().unwrap();
        assert!(*index + 1 < env.nodes.len());
        *index += 1;
    }

    pub fn can_ascend(&self) -> bool {
        self.annotated_path.len() > 1
    }

    pub fn ascend(&mut self) {
        assert!(self.can_ascend());
        self.annotated_path.pop();
    }

    // The fact at the current node.
    pub fn get_fact(&self) -> Fact {
        let truthiness = if self.env().top_level {
            Truthiness::Factual
        } else {
            Truthiness::Hypothetical
        };
        Fact::new(self.current().claim.clone(), truthiness)
    }

    // All facts that can be used to prove the current node.
    // This includes imported facts.
    pub fn usable_facts(&self, project: &Project) -> Vec<Fact> {
        let mut facts = project.imported_facts(self.env().module_id);
        for (env, i) in &self.annotated_path {
            for prop in &env.nodes[0..*i] {
                let truthiness = if env.top_level {
                    Truthiness::Factual
                } else {
                    Truthiness::Hypothetical
                };
                facts.push(Fact::new(prop.claim.clone(), truthiness));
            }
        }

        if let Some(block) = &self.current().block {
            for p in &block.env.nodes {
                facts.push(Fact::new(p.claim.clone(), Truthiness::Hypothetical));
            }
        }

        facts
    }

    // Get a goal context for the current node.
    pub fn goal_context(&self) -> Result<GoalContext, String> {
        let node = self.current();
        if node.structural {
            return Err(format!(
                "node {} does not need a proof, so it has no goal context",
                self
            ));
        }

        if let Some(block) = &node.block {
            let goal = match &block.goal {
                Some(goal) => goal,
                None => return Err(format!("block at {} has no goal", self)),
            };
            Ok(GoalContext::new(
                &block.env,
                goal.clone(),
                block.env.last_line(),
            ))
        } else {
            return Ok(GoalContext::new(
                self.env(),
                Goal::Prove(node.claim.clone()),
                node.claim.source.range.start.line,
            ));
        }
    }

    // Does a postorder traversal of everything with a goal, at and below this node
    pub fn find_goals(&mut self, output: &mut Vec<NodeCursor<'a>>) {
        for i in 0..self.num_children() {
            self.descend(i);
            self.find_goals(output);
            self.ascend();
        }
        if self.current().has_goal() {
            output.push(self.clone());
        }
    }
}
