use crate::fingerprint::FingerprintTree;
use crate::term::{Clause, Literal, Term};
use crate::unifier::{Scope, Unifier};

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    clauses: Vec<Clause>,

    resolution_targets: FingerprintTree<ResolutionTarget>,

    // The only information we need on a paramodulation target is the clause index, because
    // we use the entire paramodulator, not a subterm.
    paramodulation_targets: FingerprintTree<usize>,
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

// A ParamodulationTarget is a way of specifying one particular term that is
// "eligible for paramodulation".
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ParamodulationTarget {
    // Which clause the paramodulation target is in.
    // We assume it must be the first literal.
    clause_index: usize,

    // "forwards" paramodulation is when we use s = t to rewrite s to t.
    // "backwards" paramodulation is when we use s = t to rewrite t to s.
    forwards: bool,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet {
            clauses: vec![],
            resolution_targets: FingerprintTree::new(),
            paramodulation_targets: FingerprintTree::new(),
        }
    }

    // Recursively add all resolution targets for a term, prepending the provided path.
    // Single variables are not permitted as resolution targets.
    fn add_resolution_targets(&mut self, term: &Term, clause_index: usize, path: &mut Vec<usize>) {
        if term.atomic_variable().is_some() {
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
        let mut term = &clause.literals[0].left;
        for i in &target.path {
            term = &term.args[*i];
        }
        term
    }

    // Doesn't add any paramodulation targets if none are appropriate.
    pub fn add_paramodulation_targets(&mut self, literal: &Literal, clause_index: usize) {
        panic!(
            "TODO. literal: {:?}, clause_index: {}, pmt: {:?}",
            literal, clause_index, self.paramodulation_targets
        );
    }

    // Look for superposition inferences using a paramodulator which is not yet in the
    // active set.
    // At a high level, this is when we have just learned that s = t in some circumstances,
    // and we are looking for all the conclusions we can infer by rewriting s -> t
    // in existing formulas.
    // Specifically, this function handles the case when
    //
    //   s = t | S
    //
    // is the clause that is being activated, and we are searching for any clauses that can fit the
    //
    //   u ?= v | R
    //
    // in the superposition formula.
    pub fn activate_paramodulator(&self, s: &Term, t: &Term, pm_clause: &Clause) -> Vec<Clause> {
        let mut result = vec![];

        // Look for resolution targets that match pm_left
        let targets = self.resolution_targets.get(s);
        for target in targets {
            let u_subterm = self.get_resolution_term(target);
            let mut unifier = Unifier::new();
            // s/t must be in "left" scope and u/v must be in "right" scope
            if !unifier.unify(Scope::Left, s, Scope::Right, u_subterm) {
                continue;
            }

            // The clauses do actually unify. Combine them according to the superposition rule.
            let resolution_clause = &self.clauses[target.clause_index];
            let new_clause = unifier.superpose(t, pm_clause, &target.path, resolution_clause);

            result.push(new_clause);
        }

        result
    }

    pub fn add_clause(&mut self, clause: Clause) {
        // Add resolution targets for the new clause.
        let clause_index = self.clauses.len();
        let resolution_root = &clause.literals[0].left;
        self.add_resolution_targets(&resolution_root, clause_index, &mut vec![]);

        self.clauses.push(clause);
    }
}

#[cfg(test)]
mod tests {
    use crate::term::Literal;

    use super::*;

    #[test]
    fn test_activate_paramodulator() {
        // Create an active set that knows a0(a1) = a2
        let res_left = Term::parse("a0(a1)");
        let res_right = Term::parse("a2");
        let mut set = ActiveSet::new();
        set.add_clause(Clause::new(vec![Literal::equals(res_left, res_right)]));

        // We should be able to use a1 = a3 to paramodulate into a0(a3) = a2
        let pm_left = Term::parse("a1");
        let pm_right = Term::parse("a3");
        let pm_clause = Clause::new(vec![Literal::equals(pm_left.clone(), pm_right.clone())]);
        let result = set.activate_paramodulator(&pm_left, &pm_right, &pm_clause);

        assert_eq!(result.len(), 1);
        let expected = Clause::new(vec![Literal::equals(
            Term::parse("a0(a3)"),
            Term::parse("a2"),
        )]);
        assert_eq!(result[0], expected);
    }
}
