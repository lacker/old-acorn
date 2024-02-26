// The RewriteTree stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

use crate::atom::AtomId;
use crate::literal::Literal;
use crate::pattern_tree::{PatternTree, TermComponent};
use crate::term::Term;

// Each term can correspond with multiple RewriteValues.
struct RewriteValue {
    // Which rule this rewrite is generated from
    rule_id: usize,

    // For an s = t rule, "forwards" is rewriting s -> t, "backwards" is rewriting t -> s
    forwards: bool,

    // The term that we are rewriting into.
    // The term that we are rewriting *from* is kept in the key.
    output: Vec<TermComponent>,
}

pub struct RewriteTree {
    tree: PatternTree<Vec<RewriteValue>>,
}

impl RewriteTree {
    pub fn new() -> RewriteTree {
        RewriteTree {
            tree: PatternTree::new(),
        }
    }

    // Inserts one direction.
    // NOTE: The input term's variable ids must be normalized.
    pub fn insert_terms(
        &mut self,
        rule_id: usize,
        input_term: &Term,
        output_term: &Term,
        forwards: bool,
    ) {
        if input_term.is_true() {
            panic!("cannot rewrite true to something else");
        }
        let value = RewriteValue {
            rule_id,
            forwards,
            output: TermComponent::flatten_term(output_term),
        };
        PatternTree::insert_or_append(&mut self.tree, input_term, value);
    }

    // Inserts both directions.
    // NOTE: The input term's variable ids must be normalized.
    pub fn insert_literal(&mut self, rule_id: usize, literal: &Literal) {
        // Already normalized
        self.insert_terms(rule_id, &literal.left, &literal.right, true);

        if !literal.right.is_true() {
            let (right, left) = literal.normalized_reversed();
            self.insert_terms(rule_id, &right, &left, false);
        }
    }

    // Finds all the ways to rewrite the given term, at the root level.
    //
    // Sometimes rewrites have to create a new variable.
    // When we create new variables, we start numbering from next_var.
    //
    // Returns a list of (rule_id, forwards, new_term) tuples.
    pub fn find_rewrites(&self, input_term: &Term, next_var: AtomId) -> Vec<(usize, bool, Term)> {
        let mut answer = vec![];
        let components = TermComponent::flatten_term(input_term);
        let mut key = vec![];
        let mut replacements = vec![];
        self.tree.find_matches_while(
            &mut key,
            &components,
            &mut replacements,
            &mut |value_id, replacements| {
                for value in &self.tree.values[value_id] {
                    let new_components = TermComponent::replace_or_shift(
                        &value.output,
                        replacements,
                        Some(next_var),
                    );
                    let new_term = TermComponent::unflatten_term(&new_components);
                    answer.push((value.rule_id, value.forwards, new_term));
                }
                true
            },
        );
        answer
    }
}

#[cfg(test)]
mod tests {
    use crate::atom::Atom;

    use super::*;

    #[test]
    fn test_rewrite_tree_atoms() {
        let mut tree = RewriteTree::new();
        tree.insert_terms(0, &Term::parse("c1"), &Term::parse("c0"), true);
        let rewrites = tree.find_rewrites(&Term::parse("c1"), 0);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c0"));
    }

    #[test]
    fn test_rewrite_tree_functions() {
        let mut tree = RewriteTree::new();
        tree.insert_terms(0, &Term::parse("c1(x0)"), &Term::parse("c0(x0)"), true);
        let rewrites = tree.find_rewrites(&Term::parse("c1(c2)"), 0);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c0(c2)"));
    }

    #[test]
    fn test_rewrite_tree_multiple_rewrites() {
        let mut tree = RewriteTree::new();
        tree.insert_terms(0, &Term::parse("c1(x0, c2)"), &Term::parse("c3(x0)"), true);
        tree.insert_terms(1, &Term::parse("c1(c2, x0)"), &Term::parse("c4(x0)"), true);
        let rewrites = tree.find_rewrites(&Term::parse("c1(c2, c2)"), 0);
        assert_eq!(rewrites.len(), 2);
        assert_eq!(rewrites[0].2, Term::parse("c3(c2)"));
        assert_eq!(rewrites[1].2, Term::parse("c4(c2)"));
    }

    #[test]
    fn test_rewrite_tree_inserting_edge_literals() {
        let mut tree = RewriteTree::new();
        tree.insert_literal(0, &Literal::parse("x0 = c0"));
        tree.insert_literal(1, &Literal::parse("c0"));
    }

    #[test]
    fn test_new_variable_created_during_rewrite() {
        let mut tree = RewriteTree::new();
        tree.insert_literal(0, &Literal::parse("c1(x0) = c0"));
        let rewrites = tree.find_rewrites(&Term::parse("c0"), 1);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c1(x1)"));
    }

    #[test]
    fn test_rewrite_tree_checks_type() {
        let mut tree = RewriteTree::new();

        // Make a rule for type 2 variables
        let var2 = Term::atom(2, Atom::Variable(0));
        tree.insert_terms(0, &var2, &var2, true);

        // A type 2 constant should match it
        let const2 = Term::atom(2, Atom::GlobalConstant(2));
        let rewrites = tree.find_rewrites(&const2, 0);
        assert_eq!(rewrites.len(), 1);

        // A type 3 constant should not match it
        let const3 = Term::atom(3, Atom::GlobalConstant(3));
        let rewrites = tree.find_rewrites(&const3, 0);
        assert_eq!(rewrites.len(), 0);
    }
}
