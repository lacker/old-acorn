// The RewriteTree stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

use crate::atom::AtomId;
use crate::literal::Literal;
use crate::pattern_tree::{term_key_prefix, PatternTree, TermComponent};
use crate::term::Term;
use crate::type_map::TypeId;

// Each term can correspond with multiple RewriteValues.
struct RewriteValue {
    // Which rule this rewrite is generated from
    rule_id: usize,

    // Truthiness of the rule
    factual: bool,

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
        factual: bool,
        input_term: &Term,
        output_term: &Term,
        forwards: bool,
    ) {
        if input_term.is_true() {
            panic!("cannot rewrite true to something else");
        }
        let value = RewriteValue {
            rule_id,
            factual,
            forwards,
            output: TermComponent::flatten_term(output_term),
        };
        PatternTree::insert_or_append(&mut self.tree, input_term, value);
    }

    // Inserts both directions.
    // NOTE: The input term's variable ids must be normalized.
    pub fn insert_literal(&mut self, rule_id: usize, factual: bool, literal: &Literal) {
        // Already normalized
        self.insert_terms(rule_id, factual, &literal.left, &literal.right, true);

        if !literal.right.is_true() {
            let (right, left) = literal.normalized_reversed();
            self.insert_terms(rule_id, factual, &right, &left, false);
        }
    }

    // The callback is on (rule id, forwards, new components).
    fn find_rewrites<F>(
        &self,
        term_type: TypeId,
        components: &[TermComponent],
        allow_factual: bool,
        next_var: AtomId,
        callback: &mut F,
    ) where
        F: FnMut(usize, bool, &[TermComponent]),
    {
        let mut key = term_key_prefix(term_type);
        let mut replacements = vec![];
        self.tree.find_matches_while(
            &mut key,
            components,
            &mut replacements,
            &mut |value_id, replacements| {
                for value in &self.tree.values[value_id] {
                    if !allow_factual && value.factual {
                        continue;
                    }
                    let new_components = TermComponent::replace_or_shift(
                        &value.output,
                        replacements,
                        Some(next_var),
                    );
                    callback(value.rule_id, value.forwards, &new_components);
                }
                true
            },
        );
    }

    // Finds all the ways to rewrite the given term, at the root level.
    //
    // Sometimes rewrites have to create a new variable.
    // When we create new variables, we start numbering from next_var.
    //
    // Returns a list of (rule_id, forwards, new_term) tuples.
    pub fn get_rewrites(
        &self,
        input_term: &Term,
        allow_factual: bool,
        next_var: AtomId,
    ) -> Vec<(usize, bool, Term)> {
        let mut answer = vec![];
        let components = TermComponent::flatten_term(input_term);
        self.find_rewrites(
            input_term.term_type,
            &components,
            allow_factual,
            next_var,
            &mut |rule_id, forwards, new_components| {
                let new_term = TermComponent::unflatten_term(new_components);
                answer.push((rule_id, forwards, new_term));
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
        tree.insert_terms(0, false, &Term::parse("c1"), &Term::parse("c0"), true);
        let rewrites = tree.get_rewrites(&Term::parse("c1"), true, 0);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c0"));
    }

    #[test]
    fn test_rewrite_tree_functions() {
        let mut tree = RewriteTree::new();
        tree.insert_terms(
            0,
            false,
            &Term::parse("c1(x0)"),
            &Term::parse("c0(x0)"),
            true,
        );
        let rewrites = tree.get_rewrites(&Term::parse("c1(c2)"), true, 0);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c0(c2)"));
    }

    #[test]
    fn test_rewrite_tree_multiple_rewrites() {
        let mut tree = RewriteTree::new();
        tree.insert_terms(
            0,
            false,
            &Term::parse("c1(x0, c2)"),
            &Term::parse("c3(x0)"),
            true,
        );
        tree.insert_terms(
            1,
            false,
            &Term::parse("c1(c2, x0)"),
            &Term::parse("c4(x0)"),
            true,
        );
        let rewrites = tree.get_rewrites(&Term::parse("c1(c2, c2)"), true, 0);
        assert_eq!(rewrites.len(), 2);
        assert_eq!(rewrites[0].2, Term::parse("c3(c2)"));
        assert_eq!(rewrites[1].2, Term::parse("c4(c2)"));
    }

    #[test]
    fn test_rewrite_tree_inserting_edge_literals() {
        let mut tree = RewriteTree::new();
        tree.insert_literal(0, false, &Literal::parse("x0 = c0"));
        tree.insert_literal(1, false, &Literal::parse("c0"));
    }

    #[test]
    fn test_new_variable_created_during_rewrite() {
        let mut tree = RewriteTree::new();
        tree.insert_literal(0, false, &Literal::parse("c1(x0) = c0"));
        let rewrites = tree.get_rewrites(&Term::parse("c0"), true, 1);
        assert_eq!(rewrites.len(), 1);
        assert_eq!(rewrites[0].2, Term::parse("c1(x1)"));
    }

    #[test]
    fn test_rewrite_tree_checks_type() {
        let mut tree = RewriteTree::new();

        // Make a rule for type 2 variables
        let var2 = Term::atom(2, Atom::Variable(0));
        tree.insert_terms(0, false, &var2, &var2, true);

        // A type 2 constant should match it
        let const2 = Term::atom(2, Atom::GlobalConstant(2));
        let rewrites = tree.get_rewrites(&const2, true, 0);
        assert_eq!(rewrites.len(), 1);

        // A type 3 constant should not match it
        let const3 = Term::atom(3, Atom::GlobalConstant(3));
        let rewrites = tree.get_rewrites(&const3, true, 0);
        assert_eq!(rewrites.len(), 0);
    }
}
