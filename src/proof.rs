use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::acorn_value::AcornValue;
use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::code_gen_error::CodeGenError;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, ProofStepId, Rule};
use crate::proposition::{Source, SourceType};

// Ranking for how difficult the proof was to find.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Difficulty {
    // When we find a simple proof, it doesn't need to be any simpler.
    // No need to prompt the user to add more steps.
    Simple,

    // An intermediate proof would be nice to make simpler if possible.
    // However, if there's no way to do it, it's fine.
    // So it's up to the Proof whether to suggest simplification or not.
    Intermediate,

    // A complicated proof definitely needs to be made simpler.
    Complicated,
}

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
    // Thus, we represent the negated goal using a value.
    // We only need to store a negated goal - we never generate the positive goal,
    // because it's already expressed in the code.
    NegatedGoal(AcornValue),
}

impl fmt::Display for NodeValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NodeValue::Clause(clause) => write!(f, "Clause({})", clause),
            NodeValue::Contradiction => write!(f, "Contradiction"),
            NodeValue::NegatedGoal(v) => write!(f, "NegatedGoal({})", v),
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

    // Whether the value in the proof is negated from the value used in the Prover.
    // This is a bit unintuitive for the NegatedGoal.
    // The prover uses the negated goal. Thus, a proof node representing the original goal
    // (which can be left implicit) would have node.negated = true.
    negated: bool,

    // Which other steps this step depends on.
    // This also includes dependencies on assumptions being proved by contradiction.
    premises: Vec<NodeId>,

    // Which other steps depend on this step.
    consequences: Vec<NodeId>,

    // What external sources this step depends on.
    // The goal is treated as a node rather than as a source, for the purpose of the graph.
    sources: Vec<&'a Source>,

    // From the ProofStep
    depth: u32,
    printable: bool,
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
    ) -> Result<String, CodeGenError> {
        match &self.value {
            NodeValue::Clause(clause) => {
                let mut value = normalizer.denormalize(clause);
                if self.negated {
                    value = value.pretty_negate();
                }
                bindings.value_to_code(&value)
            }
            NodeValue::Contradiction => Ok("false".to_string()),
            NodeValue::NegatedGoal(v) => {
                if self.negated {
                    Err(CodeGenError::ExplicitGoal)
                } else {
                    bindings.value_to_code(v)
                }
            }
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

    // The difficulty of finding this proof.
    difficulty: Difficulty,
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
    pub fn new<'b>(
        normalizer: &'a Normalizer,
        negated_goal: &AcornValue,
        difficulty: Difficulty,
    ) -> Proof<'a> {
        let mut proof = Proof {
            normalizer,
            all_steps: vec![],
            nodes: vec![],
            condensed: false,
            id_map: HashMap::new(),
            difficulty,
        };

        let negated_goal = ProofNode {
            value: NodeValue::NegatedGoal(negated_goal.clone()),
            negated: false,
            premises: vec![],
            consequences: vec![],
            sources: vec![],
            depth: 0,
            printable: false,
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
            printable: step.printable,
        });

        if let Rule::Assumption(info) = &step.rule {
            if info.source.source_type == SourceType::NegatedGoal {
                insert_edge(&mut self.nodes, 0, node_id);
            } else {
                self.nodes[node_id as usize].sources.push(&info.source);
            }
        }

        for i in step.dependencies() {
            insert_edge(&mut self.nodes, self.id_map[&i], node_id);
        }

        self.id_map.insert(id.clone(), node_id);
        self.all_steps.push((id, step));
    }

    pub fn has_active_id(&self, active_id: usize) -> bool {
        let id = ProofStepId::Active(active_id);
        self.id_map.contains_key(&id)
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
            NodeValue::Contradiction | NodeValue::NegatedGoal(_) => return,
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

    // An implicit node either does not need to be converted into code or cannot be
    // converted into code.
    fn is_implicit(&self, node_id: NodeId) -> bool {
        let node = &self.nodes[node_id as usize];
        if node.depth == 0 {
            return true;
        }
        match node.value {
            NodeValue::Contradiction | NodeValue::NegatedGoal(_) => return false,
            _ => {}
        };

        if !node.printable {
            return true;
        }

        // If we have a printable consequence at this depth, we can use that one instead.
        for consequence_id in &node.consequences {
            let consequence = &self.nodes[*consequence_id as usize];
            if let NodeValue::Contradiction = consequence.value {
                continue;
            }
            if consequence.printable && consequence.depth == node.depth {
                return true;
            }
        }

        false
    }

    // Remove nodes that we don't want to turn into explicit lines of code.
    fn remove_implicit(&mut self) {
        for node_id in 0..self.nodes.len() as NodeId {
            if self.is_implicit(node_id) {
                self.contract(node_id)
            }
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
            NodeValue::NegatedGoal(_) => "negated-goal".to_string(),
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
    fn try_to_make_direct(&mut self, from_id: NodeId) {
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
        self.remove_implicit();
        self.try_to_make_direct(0);
        self.condensed = true;
    }

    // Whether this proof could be simplified.
    // Since we already removed unprintable nodes, the proofs that cannot be simplified are
    // the ones in which the goal node is proven directly, with sources only, no other
    // nodes as premises.
    pub fn has_simplification(&self) -> bool {
        let goal_node = &self.nodes[0];

        if goal_node.consequences.is_empty() && goal_node.premises.is_empty() {
            // There are no other nodes connected to this goal that could be printed out
            // to make a simplification.
            return false;
        }

        true
    }

    // When we run the verifier, or are using the IDE, a proof that needs simplification will
    // show a warning.
    pub fn needs_simplification(&self) -> bool {
        match self.difficulty {
            Difficulty::Simple => false,

            // When the prover says the proof was intermediate difficulty, it's like saying,
            // "It would be nice to simplify this, but if we can't figure out how, that's okay."
            Difficulty::Intermediate => self.has_simplification(),

            Difficulty::Complicated => true,
        }
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
        let goal_id = 0;
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
            let condition = node.to_code(normalizer, bindings)?;
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

        match node.to_code(normalizer, bindings) {
            Ok(code) => {
                output.push(format!("{}{}", "\t".repeat(tab_level), code));
                Ok(())
            }
            Err(e) => {
                // We should have already filtered out any unprintable nodes, so if we
                // hit this code path it indicates a bug.
                Err(e)
            }
        }
    }
}
