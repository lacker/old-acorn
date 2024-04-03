use std::collections::BTreeSet;

use crate::proof_step::{ProofStep, Score};

// The PassiveSet stores a bunch of clauses.
// A clause in the passive set can be activated, and it can be simplified, but to do
// anything more complicated it needs to be activated first.
pub struct PassiveSet {
    // Stores clauses in the passive set, along with their score.
    // We never shrink this vector, we just replace its entries with None.
    // The index into clauses acts like an id, but that id doesn't mean anything outside of the
    // PassiveSet.
    clauses: Vec<Option<(ProofStep, Score)>>,

    // Stores (score, clause id).
    // The queue lets us pick the highest-scoring clause to activate next.
    queue: BTreeSet<(Score, usize)>,
}

impl PassiveSet {
    pub fn new() -> PassiveSet {
        PassiveSet {
            clauses: vec![],
            queue: BTreeSet::new(),
        }
    }

    pub fn push(&mut self, step: ProofStep) {
        let score = step.score();
        let id = self.clauses.len();
        self.clauses.push(Some((step, score)));
        self.queue.insert((score, id));
    }

    pub fn pop(&mut self) -> Option<ProofStep> {
        // Remove the largest entry from queue
        let (_, id) = self.queue.pop_last()?;
        match self.clauses[id].take() {
            Some((step, _)) => Some(step),
            None => panic!("Queue and clauses are out of sync"),
        }
    }

    // The number of clauses remaining in the passive set.
    pub fn len(&self) -> usize {
        self.queue.len()
    }

    // Iterates over the steps from highest-scoring to lowest-scoring.
    pub fn iter_steps(&self) -> impl Iterator<Item = &ProofStep> {
        self.queue
            .iter()
            .rev()
            .map(|(_, id)| match &self.clauses[*id] {
                Some((step, _)) => step,
                None => panic!("Queue and clauses are out of sync"),
            })
    }

    // Finds the proof steps that are consequences of the given clause.
    // Sorts from best to worst, which is highest to lowest for ProofSteps.
    pub fn find_consequences<'a>(&'a self, id: usize) -> Vec<&'a ProofStep> {
        self.iter_steps()
            .filter(|step| step.depends_on(id))
            .collect()
    }
}
