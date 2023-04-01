use std::collections::BTreeMap;

use crate::fingerprint::Fingerprint;
use crate::term::{Clause, Term};

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    clauses: Vec<Clause>,

    resolution_targets: BTreeMap<Fingerprint, Vec<ResolutionTarget>>,
}

// A ResolutionTarget is a way of specifying one particular term that is "eligible for resolution".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ResolutionTarget {
    // Which clause the resolution target is in.
    // For now, we assume the resolution target is the first term in the first literal of the clause.
    // For resolution, the literal can be either positive or negative.
    clause_index: usize,

    // We resolve against subterms. This is the path from the root term to the subterm to resolve against.
    // An empty path means resolve against the root.
    path: Vec<usize>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            clauses: vec![],
            resolution_targets: BTreeMap::new(),
        }
    }

    // Recursively add all resolution targets for a term, prepending the provided path.
    // Single variables are not permitted as resolution targets.
    fn add_resolution_targets(&mut self, term: &Term, clause_index: usize, path: &mut Vec<usize>) {
        if term.is_atomic() {
            return;
        }

        // Add the target for the root term
        let target = ResolutionTarget {
            clause_index,
            path: path.clone(),
        };
        self.resolution_targets
            .entry(Fingerprint::new(&term))
            .or_insert(vec![])
            .push(target);

        // Add the targets for the subterms
        for (i, subterm) in term.args.iter().enumerate() {
            path.push(i);
            self.add_resolution_targets(subterm, clause_index, path);
            path.pop();
        }
    }

    fn get_resolution_term(&self, target: &ResolutionTarget) -> &Term {
        let clause = &self.clauses[target.clause_index];
        let mut term = clause.literals[0].first_term();
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Look for superposition inferences using a paramodulator which is not yet in the
    // active set.
    // Roughly, this is when we have just learned that pm_left = pm_right in some circumstances,
    // and we are looking for all the conclusions we can infer by rewriting pm_left -> pm-right
    // in existing formulas.
    // It is assumed that the first literal in pm_clause is the one with pm_left and pm_right,
    // which will get dropped in the inferred clause.
    pub fn activate_paramodulator(
        &self,
        pm_left: &Term,
        pm_right: &Term,
        pm_clause: &Clause,
    ) -> Vec<Clause> {
        // Look for resolution targets that match pm_left
        panic!("XXX");
    }

    pub fn add_clause(&mut self, clause: Clause) {
        // Add resolution targets for the new clause.
        let clause_index = self.clauses.len();
        let resolution_root = clause.literals[0].first_term();
        self.add_resolution_targets(&resolution_root, clause_index, &mut vec![]);

        self.clauses.push(clause);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        ActiveSet::new();
    }
}
