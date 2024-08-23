use std::collections::HashMap;
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, BinaryOp};
use crate::atom::AtomId;
use crate::environment::Environment;
use crate::goal::Goal;
use crate::proposition::Proposition;
use crate::token::{self, Error, Token};

// Proofs are structured into blocks.
// The environment specific to this block can have a bunch of propositions that need to be
// proved, along with helper statements to express those propositions, but they are not
// visible to the outside world.
pub struct Block {
    // The generic types that this block is polymorphic over.
    // Internally to the block, these are opaque data types.
    // Externally, these are generic data types.
    pub type_params: Vec<String>,

    // The arguments to this block.
    // Internally to the block, the arguments are constants.
    // Externally, these arguments are variables.
    pub args: Vec<(String, AcornType)>,

    // The goal for a block is relative to its internal environment.
    // Everything in the block can be used to achieve this goal.
    pub goal: Option<Goal>,

    // The environment created inside the block.
    pub env: Environment,
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

// A NodeIterator is used to traverse the nodes in an environment.
#[derive(Clone)]
pub struct NodeIterator<'a> {
    // The path from the module environment to this iterator's environment.
    // Empty if this is the module environment.
    path: Vec<usize>,

    // The external environment for this node.
    // The last index in path is the index of the node in this environment.
    env: &'a Environment,

    // The index of the node within the environment.
    index: usize,
}

impl fmt::Display for NodeIterator<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.path)
    }
}

impl<'a> NodeIterator<'a> {
    // Takes a path that includes the last index.
    // TODO: eliminate this and replace it with something less weird
    pub fn bad_new(mut path: Vec<usize>, env: &'a Environment) -> Self {
        let index = path.pop().unwrap();
        NodeIterator { path, env, index }
    }

    // Only call this on a module level environment.
    // Returns None if there are no nodes in the environment.
    pub fn first(env: &'a Environment) -> Option<Self> {
        if env.nodes.is_empty() {
            return None;
        }
        Some(NodeIterator {
            env,
            path: vec![],
            index: 0,
        })
    }

    // Can use this as an identifier for the iterator, to compare two of them
    pub fn full_path(&self) -> Vec<usize> {
        let mut path = self.path.clone();
        path.push(self.index);
        path
    }

    pub fn num_children(&self) -> usize {
        match self.env.nodes[self.index].block {
            Some(ref b) => b.env.nodes.len(),
            None => 0,
        }
    }

    // child_index must be less than num_children
    pub fn descend(&mut self, child_index: usize) {
        self.path.push(self.index);
        self.env = match self.env.nodes[self.index].block {
            Some(ref b) => &b.env,
            None => panic!("descend called on a node without a block"),
        };
        self.index = child_index;
    }

    // Whether we can advance to the next sibling, keeping environment the same.
    pub fn has_next(&self) -> bool {
        self.index + 1 < self.env.nodes.len()
    }

    // Advances to the next sibling, keeping environment the same.
    pub fn next(&mut self) {
        assert!(self.has_next());
        self.index += 1;
    }
}
