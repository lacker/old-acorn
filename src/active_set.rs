use std::collections::BTreeMap;

use crate::term::{Clause, Fingerprint, Term};

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    clauses: Vec<Clause>,

    resolution_targets: BTreeMap<Fingerprint, Vec<ResolutionTarget>>,
}

// A ResolutionTarget is a way of specifying one particular term that is "eligible for resolution".
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

    fn add_resolution_targets(&mut self, term: &Term, clause_index: usize, path: &mut Vec<usize>) {
        // Add the target for the root term
        let target = ResolutionTarget {
            clause_index,
            path: path.clone(),
        };
        self.resolution_targets
            .entry(term.fingerprint())
            .or_insert(vec![])
            .push(target);

        // Add the targets for the subterms
        for (i, subterm) in term.args.iter().enumerate() {
            path.push(i);
            self.add_resolution_targets(subterm, clause_index, path);
            path.pop();
        }
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
