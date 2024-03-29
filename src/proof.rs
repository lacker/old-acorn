use std::collections::{BTreeMap, HashMap};

use crate::binding_map::BindingMap;
use crate::clause::Clause;
use crate::code_gen_error::CodeGenError;
use crate::display::DisplayClause;
use crate::normalizer::Normalizer;
use crate::proof_step::{ProofStep, Rule, Truthiness};
use crate::proposition::{Source, SourceType};

// To conveniently manipulate the proof, we store it as a directed graph with its own ids.
// We need two sorts of ids because as we manipulate the condensed proof, the
// condensed steps won't be 1-to-1 related to the reduction steps any more.
type NodeId = u32;

// Each node in the graph represents proving a single thing.
// It can either be represented by an underlying clause, or be a special case.
enum NodeValue<'a> {
    Clause(&'a Clause),

    // This node proves a contradiction, ie a "false".
    Contradiction,

    // The goal is not explicitly represented by a clause or the negation of a clause, and
    // in general cannot be, because it may require multiple clauses.
    Goal,
}

// The ProofGraph is made up of ProofNodes.
//
// Each node represents a single proposition, either a clause or the negation of a clause,
// which can be proved using a combination of other nodes in the proof and external
// assumptions.
//
// A node with neither premises nor sources is an assumption, which we are trying to
// prove by contradiction.
struct ProofNode<'a> {
    // The value that should be displayed to represent this node in the graph.
    value: NodeValue<'a>,

    // When 'negated' is true, this node represents the negation of its value.
    negated: bool,

    // Which other steps this step depends on.
    premises: Vec<NodeId>,

    // Which other steps depend on this step.
    consequences: Vec<NodeId>,

    // What external assumptions this step depends on.
    // The goal is not treated as "external" for the purpose of the graph.
    sources: Vec<&'a Source>,
}

impl<'a> ProofNode<'a> {
    fn is_goal(&self) -> bool {
        match self.value {
            NodeValue::Goal => true,
            _ => false,
        }
    }
}

// The proof in graph form, to make it easier to manipulate.
struct ProofGraph<'a> {
    // All nodes, indexed by node id.
    // The goal is always id zero.
    nodes: Vec<ProofNode<'a>>,
}

impl<'a> ProofGraph<'a> {
    // Creates a stub proof with a single node with id 0 that assumes the negated goal.
    fn new() -> ProofGraph<'a> {
        let negated_goal = ProofNode {
            value: NodeValue::Goal,
            negated: true,
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

    fn add_assumption(&mut self, step_id: NodeId, source: &'a Source) {
        self.nodes[step_id as usize].sources.push(source);
    }

    fn insert_edge(&mut self, from: NodeId, to: NodeId) {
        self.nodes[from as usize].consequences.push(to);
        self.nodes[to as usize].premises.push(from);
    }

    // If this node only uses a single source, and no premises, remove it.
    // Any consequences will use the source instead.
    // Recursively removes any nodes that become single-source as a result.
    fn try_remove_single_source(&mut self, node_id: NodeId) {
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
            self.try_remove_single_source(*consequence_id);
        }
    }

    // Removes all single-source nodes from the graph.
    fn remove_single_source(&mut self) {
        for node_id in 1..self.nodes.len() as NodeId {
            self.try_remove_single_source(node_id);
        }
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

    pub fn print(&self) {
        println!("the proof uses {} steps:", self.steps.len());
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

    fn clause_to_code(
        &self,
        clause: &Clause,
        bindings: &BindingMap,
        negate: bool,
    ) -> Result<String, CodeGenError> {
        let mut value = self.normalizer.denormalize(clause);
        if negate {
            value = value.negate();
        }
        bindings.value_to_code(&value)
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
                    graph.add_assumption(node_id, source);
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
    // In a direct proof, all of the statements are true statements, so it's more intuitive.
    // Howevever, we can't always create a direct proof. So the idea is to make the proof
    // "as direct as possible".
    //
    // Specifically, we turn the proof into something of the form:
    //
    // <proposition>
    // ...
    // <proposition>
    // if <condition> {
    //   <proposition>
    //   ...
    //   <proposition>
    //   false
    // }
    // <proposition>
    // ...
    // <proposition>
    //
    // So, a direct proof, followed by a proof by contradiction, followed by a direct proof.
    // Essentially, we start with a proof by contradiction and "extract" as many statements
    // as possible into the surrounding direct proofs.
    //
    // Code is generated with *tabs* even though I hate tabs. The consuming logic should
    // appropriately turn tabs into spaces.
    pub fn to_code(&self, bindings: &BindingMap) -> Result<Vec<String>, CodeGenError> {
        // Check how many times each clause is used by a subsequent clause.
        let mut use_count = HashMap::new();
        for step in self.steps.values() {
            for i in step.dependencies() {
                *use_count.entry(*i).or_insert(0) += 1;
            }
        }
        for i in self.final_step.dependencies() {
            *use_count.entry(*i).or_insert(0) += 1;
        }

        // The clauses before the if-block.
        let mut preblock = vec![];

        // The clauses that go into the if-block.
        // The first one is the assumption.
        // The block will end with a "false" that is not explicitly included.
        let mut conditional = vec![];

        // The clauses after the if-block.
        // Populated in the order the prover generated them. In the final proof they
        // will be negated and put in reverse order.
        let mut postblock = vec![];

        for (i, step) in self.steps.iter() {
            if step.truthiness != Truthiness::Counterfactual {
                // We can extract any clauses that are not counterfactual.
                // We don't want to generate code for the assumptions.
                if !step.rule.is_assumption() {
                    preblock.push(&step.clause);
                }
                continue;
            }

            if conditional.is_empty() && use_count[i] <= 1 {
                // We can extract this counterfactual.
                // We don't want to generate code for the negated goal, though.
                if !step.rule.is_assumption() {
                    postblock.push(&step.clause);
                }
                continue;
            }

            // We can't extract this counterfactual.
            // We *do* want to generate code if this is the negated goal.
            conditional.push(&step.clause);
        }

        let mut answer = vec![];
        for clause in preblock {
            let code = self.clause_to_code(clause, bindings, false)?;
            answer.push(code);
        }

        if !conditional.is_empty() {
            let code = self.clause_to_code(conditional[0], bindings, false)?;
            answer.push(format!("if {} {{", code));
            for clause in conditional.iter().skip(1) {
                let code = self.clause_to_code(clause, bindings, false)?;
                answer.push(format!("\t{}", code));
            }
            answer.push("\tfalse".to_string());
            answer.push("}".to_string());
        }

        for clause in postblock.iter().rev() {
            let code = self.clause_to_code(clause, bindings, true)?;
            answer.push(code);
        }

        Ok(answer)
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
