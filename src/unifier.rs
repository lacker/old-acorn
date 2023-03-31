use crate::atom::{Atom, AtomId};
use crate::term::Term;

// A Unifier combines terms whose variables exist in different scopes.
// There are two scopes, the "left" and the "right".
// For each scope we create a mapping from variable id to the term in the output scope.
// We leave the mapping as "None" when we haven't had to map it to anything yet.
pub struct Unifier {
    left: Vec<Option<Term>>,
    right: Vec<Option<Term>>,

    // The number of variables that we are creating in the output scope.
    num_vars: AtomId,
}

impl Unifier {
    pub fn new() -> Unifier {
        Unifier {
            left: vec![],
            right: vec![],
            num_vars: 0,
        }
    }

    fn has_mapping(&self, is_left: bool, i: AtomId) -> bool {
        let i = i as usize;
        let mapping = if is_left { &self.left } else { &self.right };
        i < mapping.len() && mapping[i].is_some()
    }

    fn set_mapping(&mut self, is_left: bool, i: AtomId, term: Term) {
        let i = i as usize;
        let mapping = if is_left {
            &mut self.left
        } else {
            &mut self.right
        };
        if i >= mapping.len() {
            mapping.resize(i + 1, None);
        }
        mapping[i] = Some(term);
    }

    fn get_mapping(&self, is_left: bool, i: AtomId) -> Option<&Term> {
        let mapping = if is_left { &self.left } else { &self.right };
        match mapping.get(i as usize) {
            Some(t) => t.as_ref(),
            None => None,
        }
    }

    pub fn apply(&mut self, is_left: bool, term: &Term) -> Term {
        // First apply to the head, flattening its args into this term if it's
        // a variable that expands into a term with its own arguments.
        let mut answer = match &term.head {
            Atom::Variable(i) => {
                if !self.has_mapping(is_left, *i) {
                    // We need to create a new variable to send this one to.
                    let var_id = self.num_vars;
                    self.num_vars += 1;
                    let new_var = Term {
                        term_type: term.head_type,
                        head_type: term.head_type,
                        head: Atom::Variable(var_id),
                        args: vec![],
                    };
                    self.set_mapping(is_left, *i, new_var);
                }

                // The head of our initial term expands to a full term.
                // Its term type isn't correct, though.
                let mut head = self.get_mapping(is_left, *i).unwrap().clone();
                head.term_type = term.term_type;
                head
            }
            head => Term {
                term_type: term.term_type,
                head_type: term.head_type,
                head: head.clone(),
                args: vec![],
            },
        };

        // Recurse on the arguments
        for arg in &term.args {
            answer.args.push(self.apply(is_left, arg))
        }
        answer
    }
}
