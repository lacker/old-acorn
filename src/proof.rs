use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::code_gen_error::CodeGenError;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, ProofStepId, Rule};
use crate::proposition::{Source, SourceType};

// To conveniently manipulate the proof, we store it as a directed graph with its own ids.
// We need two sorts of ids because as we manipulate the condensed proof, the
// condensed steps won't be 1-to-1 related to the reduction steps any more.
type NodeId = u32;

// Each node in the graph represents proving a single thing.
// The NodeValue represents the way the prover found it.
// It can either be represented by an underlying clause, or be a special case.
#[derive(Debug)]
enum NodeValue<'a> {
    Clause(&'a Clause),

    // This node proves a contradiction, ie a "false".
    // It contradicts the hypothesis in the provided node.
    // When this node is used as a premise, it means that the negated hypothesis is used.
    Contradiction,

    // The goal is not explicitly represented by a clause or the negation of a clause, and
    // in general cannot be, because it may require multiple clauses.
    NegatedGoal,
}

impl fmt::Display for NodeValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NodeValue::Clause(clause) => write!(f, "Clause({})", clause),
            NodeValue::Contradiction => write!(f, "Contradiction"),
            NodeValue::NegatedGoal => write!(f, "NegatedGoal"),
        }
    }
}

// The ProofGraph is made up of ProofNodes.
//
// Each node represents a single proposition, either a clause or the negation of a clause,
// which can be proved using other nodes in the proof, external sources, or starting a
// proof by reduction.
struct ProofNode<'a> {
    // The value that should be displayed to represent this node in the graph.
    value: NodeValue<'a>,

    // Whether the value is negated from its original value when it is part of the proof.
    // When we are proving the goal, we represent it as a negated negated goal.
    // This way the negated goal works more like other sources.
    negated: bool,

    // Which other steps this step depends on.
    // This also includes dependencies on assumptions being proved by contradiction.
    premises: Vec<NodeId>,

    // Which other steps depend on this step.
    consequences: Vec<NodeId>,

    // What external sources this step depends on.
    // The goal is treated as a node rather than as a source, for the purpose of the graph.
    sources: Vec<&'a Source>,

    // Once we prove everything of depth n, the nodes of depth n+1 have a basic proof.
    depth: u32,
}

impl<'a> ProofNode<'a> {
    // Returns true if this node is the start of a proof by reduction.
    fn starts_reduction(&self) -> bool {
        !self.consequences.is_empty() && self.premises.is_empty() && self.sources.is_empty()
    }

    // Instead of removing nodes from the graph, we isolate them by removing all premises and
    // consequences.
    fn is_isolated(&self) -> bool {
        self.premises.is_empty() && self.consequences.is_empty()
    }

    fn to_code(
        &self,
        normalizer: &Normalizer,
        bindings: &BindingMap,
        next_k: &mut u32,
    ) -> Result<String, CodeGenError> {
        match &self.value {
            NodeValue::Clause(clause) => {
                let mut value = normalizer.denormalize(clause);
                if self.negated {
                    value = value.pretty_negate();
                }
                bindings.value_to_code(&value, next_k)
            }
            NodeValue::Contradiction => Ok("false".to_string()),
            NodeValue::NegatedGoal => Err(CodeGenError::ExplicitGoal),
        }
    }

    fn is_positive_goal(&self) -> bool {
        match &self.value {
            NodeValue::Clause(_) | NodeValue::Contradiction => false,
            NodeValue::NegatedGoal => self.negated,
        }
    }
}

// A proof that was successfully found by the prover.
//
// We store the proof in two different ways.
// First, we store each step of the proof in the order we found them, in `steps`.
// This starts with the negated goal and proves it by reducing it to a contradiction.
//
// Second, we store the proof as a graph in `nodes`.
// This form lets us manipulate the proof to create an equivalent version that we can use
// for code generation.
// This dual representation helps us avoid the problem of proof generation creating a proof
// that is unreadable because it repeats itself or uses unnecessarily indirect reasoning.
pub struct Proof<'a> {
    normalizer: &'a Normalizer,

    // Steps of the proof that can be directly verified.
    // When steps are condensed away, they still exist in all_steps.
    // all_steps always represents a proof by contradiction, with each step depending only on
    // previous steps.
    pub all_steps: Vec<(ProofStepId, &'a ProofStep)>,

    // The graph representation of the proof.
    // Nodes are indexed by node id.
    // The goal is always id zero.
    //
    // Nodes that get condensed out of the proof are not removed from this vector.
    // Instead, they are modified to have no content, with nothing depending on them.
    nodes: Vec<ProofNode<'a>>,

    // Whether we have called condense().
    condensed: bool,

    // A map from proof step ids to the ids nodes that correspond to them.
    id_map: HashMap<ProofStepId, NodeId>,
}

fn remove_edge(nodes: &mut Vec<ProofNode>, from: NodeId, to: NodeId) {
    nodes[from as usize].consequences.retain(|x| *x != to);
    nodes[to as usize].premises.retain(|x| *x != from);
}

// If the edge is already there, don't re-insert it.
fn insert_edge(nodes: &mut Vec<ProofNode>, from: NodeId, to: NodeId) {
    if !nodes[from as usize].consequences.contains(&to) {
        nodes[from as usize].consequences.push(to);
        nodes[to as usize].premises.push(from);
    }
}

fn move_sources_and_premises(nodes: &mut Vec<ProofNode>, from: NodeId, to: NodeId) {
    let sources = std::mem::take(&mut nodes[from as usize].sources);
    for source in sources {
        if !nodes[to as usize].sources.contains(&source) {
            nodes[to as usize].sources.push(source);
        }
    }
    let premises = std::mem::take(&mut nodes[from as usize].premises);
    for premise in premises {
        nodes[premise as usize].consequences.retain(|x| *x != from);
        insert_edge(nodes, premise, to);
    }
}

impl<'a> Proof<'a> {
    // Creates a new proof, with just one node for the negated goal.
    pub fn new<'b>(normalizer: &'a Normalizer) -> Proof<'a> {
        let mut proof = Proof {
            normalizer,
            all_steps: vec![],
            nodes: vec![],
            condensed: false,
            id_map: HashMap::new(),
        };

        let negated_goal = ProofNode {
            value: NodeValue::NegatedGoal,
            negated: false,
            premises: vec![],
            consequences: vec![],
            sources: vec![],
            depth: 0,
        };
        proof.nodes.push(negated_goal);

        proof
    }

    // Add a new step, which becomes a node in the graph.
    pub fn add_step(&mut self, id: ProofStepId, step: &'a ProofStep) {
        let value = match id {
            ProofStepId::Final => NodeValue::Contradiction,
            ProofStepId::Active(_) | ProofStepId::Passive(_) => NodeValue::Clause(&step.clause),
        };

        let node_id = self.nodes.len() as NodeId;
        self.nodes.push(ProofNode {
            value,
            negated: false,
            premises: vec![],
            consequences: vec![],
            sources: vec![],
            depth: step.depth,
        });

        if let Rule::Assumption(source) = &step.rule {
            if source.source_type == SourceType::NegatedGoal {
                insert_edge(&mut self.nodes, 0, node_id);
            } else {
                self.nodes[node_id as usize].sources.push(source);
            }
        }

        for i in step.dependencies() {
            insert_edge(&mut self.nodes, self.id_map[&i], node_id);
        }

        self.id_map.insert(id.clone(), node_id);
        self.all_steps.push((id, step));
    }

    // Contracts this node if possible.
    // (The goal and contradictions cannot be contracted.)
    //
    // If we start with
    // A & B -> C -> D & E
    // then we replace each in+out pair of C edges with an edge that goes directly.
    // A & B -> D & E
    //
    // Sources and premises are both copied to all consequences.
    fn contract(&mut self, node_id: NodeId) {
        let node = &self.nodes[node_id as usize];
        match &node.value {
            NodeValue::Clause(_) => {}
            NodeValue::Contradiction | NodeValue::NegatedGoal => return,
        };

        // Remove the node from the graph.
        let premises = std::mem::take(&mut self.nodes[node_id as usize].premises);
        let consequences = std::mem::take(&mut self.nodes[node_id as usize].consequences);
        let sources = std::mem::take(&mut self.nodes[node_id as usize].sources);

        for premise_id in &premises {
            self.nodes[*premise_id as usize]
                .consequences
                .retain(|x| *x != node_id);
        }

        for consequence_id in consequences {
            self.nodes[consequence_id as usize]
                .premises
                .retain(|x| *x != node_id);

            for premise_id in &premises {
                insert_edge(&mut self.nodes, *premise_id, consequence_id);
            }

            for source in &sources {
                self.nodes[consequence_id as usize].sources.push(source);
            }
        }
    }

    // Whether this node was cheap to create.
    fn is_cheap(&self, node_id: NodeId) -> bool {
        let node = &self.nodes[node_id as usize];
        match node.value {
            NodeValue::Contradiction | NodeValue::NegatedGoal => return false,
            _ => {}
        };

        if node.depth == 0 {
            return true;
        }

        for premise_id in &node.premises {
            let premise = &self.nodes[*premise_id as usize];
            if premise.depth == node.depth {
                return true;
            }
        }

        false
    }

    // Remove nodes that are cheap to regenerate.
    fn remove_cheap(&mut self) {
        for node_id in 0..self.nodes.len() as NodeId {
            if self.is_cheap(node_id) {
                self.contract(node_id)
            }
        }
    }

    // This is really just a heuristic.
    fn is_ugly(&self, node_id: NodeId) -> bool {
        let node = &self.nodes[node_id as usize];
        let clause = match &node.value {
            NodeValue::Contradiction | NodeValue::NegatedGoal => return false,
            NodeValue::Clause(clause) => clause,
        };

        if clause.len() > 1 {
            // Clauses with a bunch of literals are ugly because they are hard to read.
            return true;
        }

        if clause.has_any_variable() {
            // Unbound variables are ugly because we'll have to stick in extra "forall" and "exists".
            return true;
        }

        if clause.has_skolem() {
            // Skolem constants are ugly because they don't have a user-visible name.
            return true;
        }

        false
    }

    fn remove_ugly(&mut self) {
        for node_id in 0..self.nodes.len() as NodeId {
            if self.is_ugly(node_id) {
                self.contract(node_id)
            }
        }
    }

    // Some nodes in an indirect proof cannot be turned into nodes in a direct proof.
    // This happens when we assume the goal is false, use it to prove both A and B,
    // and then together A plus B lead to a contradiction.
    // A and B cannot be directly proven from our assumptions; they are only true in the
    // context of a proof by contradiction.
    // Since we want don't want to express "the negative goal" itself in our proof, we
    // eliminate this sort of node that is adjacent to the negative goal until we find
    // at least one node whose negation can be directly proven.
    //
    // This algorithm relies on the ordering of the nodes, that consequences must come
    // after premises. This method must be called before directing the proof.
    fn contract_indirect(&mut self) {
        while self.nodes[0].consequences.len() > 1 {
            assert!(matches!(self.nodes[0].value, NodeValue::NegatedGoal));

            // Find the earliest consequence, the min on consequences
            let consequence_id = self.nodes[0].consequences.iter().min().unwrap();
            self.contract(*consequence_id);
        }
    }

    fn display(&self, value: &NodeValue) -> String {
        match value {
            NodeValue::Clause(clause) => format!(
                "clause: {}",
                DisplayClause {
                    normalizer: self.normalizer,
                    clause: clause,
                }
            ),
            NodeValue::Contradiction => "contradiction".to_string(),
            NodeValue::NegatedGoal => "negated-goal".to_string(),
        }
    }

    pub fn print_graph(&self, message: &str) {
        println!("\n{}", message);
        println!("\nProof graph:");
        for (i, node) in self.nodes.iter().enumerate() {
            if node.is_isolated() {
                continue;
            }
            print!("node {}: ", i);
            if node.negated {
                print!("negated ");
            }
            println!("{}", self.display(&node.value));
            if !node.premises.is_empty() {
                println!("  premises: {:?}", node.premises);
            }
            if !node.consequences.is_empty() {
                println!("  consequences: {:?}", node.consequences);
            }
            if !node.sources.is_empty() {
                println!(
                    "  sources: {:?}",
                    node.sources
                        .iter()
                        .map(|x| &x.source_type)
                        .collect::<Vec<_>>()
                );
            }
        }
    }

    // In a direct proof, all of the statements are true statements, so it's more intuitive.
    // Howevever, we can't always create a direct proof. So the idea is to make the proof
    // "as direct as possible".
    //
    // Thus, this method tries to turn one step from indirect to direct, and then repeats.
    // We do this by reversing the logical order of this node and its immediate consequence.
    //
    // Converts:
    //
    // if A {
    //   B
    //   false
    // }
    //
    // into:
    //
    // if B {
    //   false
    // }
    // !A
    //
    // and then continues with the new hypothesis.
    fn remove_conditional(&mut self, from_id: NodeId) {
        let mut from_id = from_id;
        loop {
            let node = &self.nodes[from_id as usize];
            if !node.starts_reduction() {
                // This node is already direct
                return;
            }
            if node.negated {
                panic!("unexpected negation in make_direct");
            }
            if let NodeValue::Contradiction = node.value {
                // This is assuming !false, which is fine.
                return;
            }

            // Find the consequences that are inside the indirect block
            let mut counterfactual_consequences = vec![];
            for consequence_id in &node.consequences {
                if self.nodes[*consequence_id as usize].negated {
                    // The consequence has been negated, which means it already must be outside
                    continue;
                }
                counterfactual_consequences.push(*consequence_id);
            }

            if counterfactual_consequences.len() == 0 {
                panic!("a counterfactual is never disproven, in the proof");
            }

            if counterfactual_consequences.len() > 1 {
                // We can't make this direct, because it has multiple consequences.
                return;
            }

            // We only use this node for one thing, so we can reverse the outgoing edge.
            // Initially, the logic is that we assume "from", prove "to", then prove a contradiction.
            // Afterwards, we are going to assume "to", prove a contradiction, and conclude "!from".
            // Thus, we need to reverse the direction, negate from, and move all of to's sources
            // and premises to from.
            // If to is a contradiction, we don't want the resulting edge.
            let to_id = counterfactual_consequences[0];
            remove_edge(&mut self.nodes, from_id, to_id);

            self.nodes[from_id as usize].negated = true;
            move_sources_and_premises(&mut self.nodes, to_id, from_id);
            if !matches!(self.nodes[to_id as usize].value, NodeValue::Contradiction) {
                insert_edge(&mut self.nodes, to_id, from_id);
            }

            // Continue with the node that we just moved into the "if" condition
            from_id = to_id;
        }
    }

    // Reduce the graph as much as possible.
    // Call just once.
    pub fn condense(&mut self) {
        assert!(!self.condensed);
        self.remove_ugly();
        self.remove_cheap();
        self.contract_indirect();
        self.remove_conditional(0);
        self.condensed = true;
    }

    // Finds the contradiction that this node eventually leads to.
    // Returns None if it does not lead to any contradiction.
    fn find_contradiction(&self, node_id: NodeId) -> Option<NodeId> {
        let node = &self.nodes[node_id as usize];
        if let NodeValue::Contradiction = node.value {
            return Some(node_id);
        }
        for consequence_id in &node.consequences {
            if let Some(result) = self.find_contradiction(*consequence_id) {
                return Some(result);
            }
        }
        None
    }

    // Usually, the negated negated goal counts as a goal.
    // If we aren't actually using the goal, then use a contradiction as the goal.
    fn find_goal_node(&self) -> Option<NodeId> {
        if self.nodes[0].is_positive_goal() {
            return Some(0);
        }
        for (i, node) in self.nodes.iter().enumerate().rev() {
            if matches!(node.value, NodeValue::Contradiction) {
                return Some(i as NodeId);
            }
        }

        None
    }

    // Converts the proof to lines of code.
    //
    // The prover assumes the goal is false and then searches for a contradiction.
    // When we turn this sort of proof into code, it looks like one big proof by contradiction.
    // This often commingles lemma-style reasoning that seems intuitively true with
    // proof-by-contradiction-style reasoning that feels intuitively backwards.
    // Humans try to avoid mixing these different styles of reasoning.
    //
    // Code is generated with *tabs* even though I hate tabs. The consuming logic should
    // appropriately turn tabs into spaces.
    pub fn to_code(&self, bindings: &BindingMap) -> Result<Vec<String>, CodeGenError> {
        let goal_id = match self.find_goal_node() {
            Some(id) => id,
            None => return Err(CodeGenError::ExplicitGoal),
        };
        let mut next_k = 0;
        let mut output = vec![];
        self.to_code_helper(
            self.normalizer,
            bindings,
            goal_id,
            0,
            true,
            &mut next_k,
            &mut HashSet::new(),
            &mut output,
        )?;
        Ok(output)
    }

    // Write out code for the given node, and everything needed to prove it.
    fn to_code_helper(
        &self,
        normalizer: &Normalizer,
        bindings: &BindingMap,
        node_id: NodeId,
        tab_level: usize,
        node_is_goal: bool,
        next_k: &mut u32,
        proven: &mut HashSet<NodeId>,
        output: &mut Vec<String>,
    ) -> Result<(), CodeGenError> {
        if proven.contains(&node_id) {
            return Ok(());
        }
        // Mark this node as proven before we have written the proof.
        // This should be okay if there are no cycles.
        let node = &self.nodes[node_id as usize];

        if node.starts_reduction() {
            proven.insert(node_id);
            let condition = node.to_code(normalizer, bindings, next_k)?;
            output.push(format!("{}if {} {{", "\t".repeat(tab_level), condition));
            let contradiction = match self.find_contradiction(node_id) {
                Some(id) => id,
                None => {
                    return Err(CodeGenError::InternalError(
                        "lost the conclusion of the proof".to_string(),
                    ))
                }
            };
            self.to_code_helper(
                normalizer,
                bindings,
                contradiction,
                tab_level + 1,
                false,
                next_k,
                proven,
                output,
            )?;
            output.push(format!("{}}}", "\t".repeat(tab_level)));
            return Ok(());
        }

        for premise_id in &node.premises {
            self.to_code_helper(
                normalizer,
                bindings,
                *premise_id,
                tab_level,
                false,
                next_k,
                proven,
                output,
            )?;
        }
        proven.insert(node_id);

        // We don't need to put the goal in the proof because it's already expressed in the code
        if node_is_goal {
            return Ok(());
        }

        match node.to_code(normalizer, bindings, next_k) {
            Ok(code) => {
                output.push(format!("{}{}", "\t".repeat(tab_level), code));
                Ok(())
            }
            Err(CodeGenError::Skolem(_)) => {
                // Just ignore these and don't generate the skolem lines.
                // Maybe the other lines are good enough.
                Ok(())
            }
            Err(e) => Err(e),
        }
    }
}
