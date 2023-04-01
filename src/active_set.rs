use crate::fingerprint::FingerprintTree;
use crate::term::{Clause, Literal, Term};
use crate::unifier::{Replacement, Scope, Unifier};

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    clauses: Vec<Clause>,

    resolution_targets: FingerprintTree<ResolutionTarget>,
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
            resolution_targets: FingerprintTree::new(),
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
        self.resolution_targets.insert(&term, target);

        // Add the targets for the subterms
        for (i, subterm) in term.args.iter().enumerate() {
            path.push(i);
            self.add_resolution_targets(subterm, clause_index, path);
            path.pop();
        }
    }

    fn get_resolution_term(&self, target: &ResolutionTarget) -> &Term {
        let clause = &self.clauses[target.clause_index];
        let mut term = clause.literals[0].left();
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Look for superposition inferences using a paramodulator which is not yet in the
    // active set.
    // At a high level, this is when we have just learned that s = t in some circumstances,
    // and we are looking for all the conclusions we can infer by rewriting s -> t
    // in existing formulas.
    //
    // At a lower level, the superposition rule is, given:
    // s = t | S
    // u ?= v | R
    //
    // If s matches a subterm of u, superposition lets you replace the s with t to infer that:
    //
    // u[s -> t] ?= v | S | R
    // (after the unifier has been applied to the whole thing)
    //
    // Sometimes we refer to s = t as the "paramodulator" and u ?= v as the "resolver".
    //
    // If ?= is =, it's "superposition into positive literals".
    // If ?= is !=, it's "superposition into negative literals".
    //
    // This function handles the case when s = t | S is the clause that is being activated, and
    // we are searching for any clauses that can fit the u ?= v | R in this formula.
    //
    // pm_clause is s = t | S. It is assumed that the first literal in pm_clause is the paramodulator,
    // which will get dropped in the inferred clause.
    //
    // Refer to page 3 of "E: A Brainiac Theorem Prover" for more detail.
    pub fn activate_paramodulator(&self, s: &Term, t: &Term, pm_clause: &Clause) -> Vec<Clause> {
        let result = vec![];

        // Look for resolution targets that match pm_left
        let targets = self.resolution_targets.get(s);
        for target in targets {
            let u_subterm = self.get_resolution_term(target);
            let mut unifier = Unifier::new();
            // We'll call the s/t scope "left" and the u/v scope "right"
            if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
                continue;
            }

            // The clauses do actually unify. Combine them according to the superposition rule.
            let resolution_clause = &self.clauses[target.clause_index];
            let resolution_literal = &resolution_clause.literals[0];
            let u = resolution_literal.left();
            let v = resolution_literal.right();
            let unified_u = unifier.apply_replace(
                Scope::Right,
                u,
                Some(Replacement {
                    path: &target.path,
                    scope: Scope::Left,
                    term: &t,
                }),
            );
            let unified_v = match v {
                Some(v_term) => Some(unifier.apply(Scope::Right, v_term)),
                None => None,
            };
            let new_literal = Literal::new(resolution_literal.is_positive(), unified_u, unified_v);

            // Now we just need to run the unifier on all the other literals from the input clauses.
            let mut literals = vec![];
            for literal in resolution_clause.literals[1..] {
                panic!("XXX");
            }

            panic!("XXX");
        }

        result
    }

    pub fn add_clause(&mut self, clause: Clause) {
        // Add resolution targets for the new clause.
        let clause_index = self.clauses.len();
        let resolution_root = clause.literals[0].left();
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
