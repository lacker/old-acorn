use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::code_gen_error::CodeGenError;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Rule};
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
                    value = value.negate();
                }
                bindings.value_to_code(&value)
            }
            NodeValue::Contradiction => Ok("false".to_string()),
            NodeValue::NegatedGoal => Err(CodeGenError::ImplicitGoal),
        }
    }

    // Whether this node is implicitly represented in the code already by the goal.
    // The negated negated goal is represented by the goal.
    // So is any negated clause that implies only the goal.
    // The goal is already represented, as are any nodes that are directly
    // implied by the negated goal, because those are created by normalization.
    fn already_represented(&self) -> bool {
        if !self.negated {
            return false;
        }
        match &self.value {
            NodeValue::Clause(_) => {
                for consequence_id in &self.consequences {
                    if *consequence_id != 0 {
                        return false;
                    }
                }
                true
            }
            NodeValue::Contradiction => false,
            NodeValue::NegatedGoal => true,
        }
    }
}

// The proof in graph form, to make it easier to manipulate.
pub struct ProofGraph<'a> {
    // All nodes, indexed by node id.
    //
    // The goal is always id zero.
    //
    // Nodes that get removed from the proof are not removed from this vector.
    // Instead, they are modified to have no content, with nothing depending on them.
    nodes: Vec<ProofNode<'a>>,
}

impl<'a> ProofGraph<'a> {
    // Creates a stub proof with a single node with id 0 that assumes the negated goal.
    fn new() -> ProofGraph<'a> {
        let negated_goal = ProofNode {
            value: NodeValue::NegatedGoal,
            negated: false,
            premises: vec![],
            consequences: vec![],
            sources: vec![],
        };
        ProofGraph {
            nodes: vec![negated_goal],
        }
    }

    fn insert_node(&mut self, value: NodeValue<'a>) -> NodeId {
        let id = self.nodes.len() as NodeId;
        self.nodes.push(ProofNode {
            value,
            negated: false,
            premises: vec![],
            consequences: vec![],
            sources: vec![],
        });
        id
    }

    fn add_source(&mut self, step_id: NodeId, source: &'a Source) {
        self.nodes[step_id as usize].sources.push(source);
    }

    fn insert_edge(&mut self, from: NodeId, to: NodeId) {
        self.nodes[from as usize].consequences.push(to);
        self.nodes[to as usize].premises.push(from);
    }

    // If this node only uses a single source, and no premises, remove it.
    // Any consequences will use the source instead.
    // Recursively removes any nodes that become single-source as a result.
    fn remove_single_source(&mut self, node_id: NodeId) {
        if node_id == 0 {
            // We should never remove the goal
            return;
        }

        let node = &self.nodes[node_id as usize];
        if node.premises.len() > 0 || node.sources.len() != 1 {
            return;
        }

        // This is in fact a single-source node, so we can remove it.
        let source = node.sources[0];
        let consequences = std::mem::take(&mut self.nodes[node_id as usize].consequences);
        for consequence_id in &consequences {
            self.nodes[*consequence_id as usize]
                .premises
                .retain(|x| *x != node_id);
            self.nodes[*consequence_id as usize].sources.push(source);
        }

        for consequence_id in &consequences {
            self.remove_single_source(*consequence_id);
        }
    }

    // Removes all single-source nodes from the graph.
    fn remove_all_single_source(&mut self) {
        for node_id in 1..self.nodes.len() as NodeId {
            self.remove_single_source(node_id);
        }
    }

    pub fn print(&self) {
        for (i, node) in self.nodes.iter().enumerate() {
            if node.is_isolated() {
                continue;
            }
            print!("node {}: ", i);
            if node.negated {
                print!("Negated ");
            }
            println!("{}", node.value);
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
    fn make_direct(&mut self, from_id: NodeId) {
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
        // Initially, the logic is that we assume "from", and prove "to".
        // Afterwards, we are going to assume "to", and prove "!from".
        // Thus, we need to reverse the direction, negate from, and move all of to's sources
        // to from.
        // If to is a contradiction, we don't need the resulting edge at all.
        let to_id = counterfactual_consequences[0];
        let to = &mut self.nodes[to_id as usize];
        let to_is_contradiction = matches!(to.value, NodeValue::Contradiction);
        to.premises.retain(|x| *x != from_id);
        if !to_is_contradiction {
            to.consequences.push(from_id);
        }
        let to_sources = std::mem::take(&mut to.sources);
        let from = &mut self.nodes[from_id as usize];
        from.consequences.retain(|x| *x != to_id);
        if !to_is_contradiction {
            from.premises.push(to_id);
        }
        from.negated = true;
        from.sources.extend(to_sources);
        self.make_direct(to_id);
    }

    fn condense(&mut self) {
        self.remove_all_single_source();
        self.make_direct(0);
    }

    // Finds the contradiction that this node eventually leads to.
    fn find_contradiction(&self, node_id: NodeId) -> NodeId {
        let mut node_id = node_id;
        loop {
            let node = &self.nodes[node_id as usize];
            if let NodeValue::Contradiction = node.value {
                return node_id;
            }
            if node.consequences.is_empty() {
                panic!("expected contradiction");
            }
            node_id = node.consequences[0];
        }
    }

    // Write out code for the given node, and everything needed to prove it.
    fn to_code(
        &self,
        normalizer: &Normalizer,
        bindings: &BindingMap,
        node_id: NodeId,
        tab_level: usize,
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
            let contradiction = self.find_contradiction(node_id);
            self.to_code(
                normalizer,
                bindings,
                contradiction,
                tab_level + 1,
                proven,
                output,
            )?;
            output.push(format!("{}}}", "\t".repeat(tab_level)));
            return Ok(());
        }

        for premise_id in &node.premises {
            self.to_code(normalizer, bindings, *premise_id, tab_level, proven, output)?;
        }
        proven.insert(node_id);
        if !node.already_represented() {
            let code = node.to_code(normalizer, bindings)?;
            output.push(format!("{}{}", "\t".repeat(tab_level), code));
        }
        Ok(())
    }
}

// A proof created by the Prover.
// It assumes the negated goal and finishes by proving a contradiction.
pub struct ReductionProof<'a> {
    normalizer: &'a Normalizer,

    // Maps clause id to proof step that proves it.
    // Does not include the final step, because the final step has no clause id.
    steps: BTreeMap<usize, ProofStep>,

    // The conclusion of this step should be a contradiction.
    final_step: ProofStep,
}

impl<'a> ReductionProof<'a> {
    pub fn new(normalizer: &'a Normalizer, final_step: ProofStep) -> ReductionProof<'a> {
        ReductionProof {
            normalizer,
            steps: BTreeMap::new(),
            final_step,
        }
    }

    // Just to be used during construction.
    pub fn add_step(&mut self, id: usize, step: ProofStep) {
        self.steps.insert(id, step);
    }

    fn display(&self, clause: &'a Clause) -> DisplayClause<'a> {
        DisplayClause {
            clause,
            normalizer: self.normalizer,
        }
    }

    fn print_step(&self, preface: &str, step: &ProofStep) {
        println!(
            "\n{}{} generated:\n    {}",
            preface,
            step.rule.name(),
            self.display(&step.clause)
        );
        for (description, i) in step.descriptive_dependencies() {
            let clause = &self.steps.get(&i).unwrap().clause;
            let dc = self.display(clause);
            println!("  using {} {}:\n    {}", description, i, dc);
        }
    }

    // Prints the reduction form of the proof, the way it was originally found by the prover.
    pub fn print_reduction(&self) {
        println!("the reduction proof uses {} steps:", self.steps.len());
        for (step_id, step) in &self.steps {
            println!("step {}: {}", step_id, step);
            let preface = if step.is_negated_goal() {
                format!("clause {} (negating goal): ", step_id)
            } else {
                format!("clause {}: ", step_id)
            };
            self.print_step(&preface, step);
        }
    }

    // Convert the reduction proof to a graphical form.
    // Each step in the proof becomes a node in the graph, plus we get an extra node for the goal.
    fn to_graph(&'a self) -> ProofGraph<'a> {
        // Maps clause id to node id.
        let mut id_map = HashMap::new();

        let mut graph = ProofGraph::new();

        for (clause_id, step) in self.iter_steps() {
            let value = match clause_id {
                Some(_) => NodeValue::Clause(&step.clause),
                None => NodeValue::Contradiction,
            };
            let node_id = graph.insert_node(value);

            if let Rule::Assumption(source) = &step.rule {
                if source.source_type == SourceType::NegatedGoal {
                    graph.insert_edge(0, node_id);
                } else {
                    graph.add_source(node_id, source);
                }
            }

            for i in step.dependencies() {
                graph.insert_edge(id_map[i], node_id);
            }

            if let Some(clause_id) = clause_id {
                id_map.insert(clause_id, node_id);
            }
        }

        graph
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
        let mut graph = self.to_graph();
        graph.condense();
        let mut output = vec![];
        graph.to_code(
            self.normalizer,
            bindings,
            0,
            0,
            &mut HashSet::new(),
            &mut output,
        )?;
        Ok(output)
    }

    // Iterates in order through the steps of the proof.
    // Includes the clause id in the tuple, til it gets to the last one which is None.
    pub fn iter_steps(&'a self) -> impl Iterator<Item = (Option<usize>, &'a ProofStep)> {
        self.steps
            .iter()
            .map(|(id, step)| (Some(*id), step))
            .chain(std::iter::once((None, &self.final_step)))
    }
}
