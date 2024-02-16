// The RewriteMap stores a set of potential rewrites.
// A given pattern can be rewritten to multiple different output terms.

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

pub struct RewriteMap {
    tree: PatternTree<Vec<RewriteValue>>,
}

impl RewriteMap {
    pub fn new() -> RewriteMap {
        RewriteMap {
            tree: PatternTree::new(),
        }
    }

    // The input term's variable ids must be normalized.
    pub fn insert(
        &mut self,
        rule_id: usize,
        input_term: &Term,
        output_term: &Term,
        forwards: bool,
    ) {
        if input_term.atomic_variable().is_some() {
            panic!("cannot rewrite atomic variables to something else");
        }
        let value = RewriteValue {
            rule_id,
            forwards,
            output: TermComponent::flatten_term(output_term),
        };
        PatternTree::insert_or_append(&mut self.tree, input_term, value);
    }

    // Finds all the ways to rewrite the given term, at the root level.
    // Returns a list of (rule_id, forwards, new_term) tuples.
    pub fn find_rewrites(&self, term: &Term) -> Vec<(usize, bool, Term)> {
        let mut answer = vec![];
        todo!();
        answer
    }
}
