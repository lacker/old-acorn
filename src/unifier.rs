use crate::atom::{Atom, AtomId};
use crate::term::Term;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Scope {
    Left,
    Right,
    Output,
}

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

    fn mut_map(&mut self, scope: Scope) -> &mut Vec<Option<Term>> {
        match scope {
            Scope::Left => &mut self.left,
            Scope::Right => &mut self.right,
            _ => panic!("Can't mut_map the output scope"),
        }
    }

    fn map(&self, scope: Scope) -> &Vec<Option<Term>> {
        match scope {
            Scope::Left => &self.left,
            Scope::Right => &self.right,
            _ => panic!("Can't map the output scope"),
        }
    }

    fn has_mapping(&self, scope: Scope, i: AtomId) -> bool {
        let i = i as usize;
        i < self.map(scope).len() && self.map(scope)[i].is_some()
    }

    fn set_mapping(&mut self, scope: Scope, i: AtomId, term: Term) {
        let i = i as usize;
        let map = self.mut_map(scope);
        if i >= map.len() {
            map.resize(i + 1, None);
        }
        map[i] = Some(term);
    }

    fn get_mapping(&self, scope: Scope, i: AtomId) -> Option<&Term> {
        match self.map(scope).get(i as usize) {
            Some(t) => t.as_ref(),
            None => None,
        }
    }

    pub fn apply(&mut self, scope: Scope, term: &Term) -> Term {
        // First apply to the head, flattening its args into this term if it's
        // a variable that expands into a term with its own arguments.
        let mut answer = match &term.head {
            Atom::Variable(i) => {
                if !self.has_mapping(scope, *i) {
                    // We need to create a new variable to send this one to.
                    let var_id = self.num_vars;
                    self.num_vars += 1;
                    let new_var = Term {
                        term_type: term.head_type,
                        head_type: term.head_type,
                        head: Atom::Variable(var_id),
                        args: vec![],
                    };
                    self.set_mapping(scope, *i, new_var);
                }

                // The head of our initial term expands to a full term.
                // Its term type isn't correct, though.
                let mut head = self.get_mapping(scope, *i).unwrap().clone();
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
            answer.args.push(self.apply(scope, arg))
        }
        answer
    }

    // Replace variable i in the output scope with the given term (which is also in the output scope).
    // The term must not contain variable i.
    // If they're both variables, keep the one with the lower id.
    fn remap(&mut self, id: AtomId, term: &Term) {
        if let Some(other_id) = term.atomic_variable() {
            if other_id > id {
                // Let's keep this id and remap the other one instead
                let mut new_term = term.clone();
                new_term.head = Atom::Variable(id);
                self.remap(other_id, &new_term);
                return;
            }
        }
        for mapping in [&mut self.left, &mut self.right] {
            for i in 0..mapping.len() {
                if let Some(t) = &mapping[i] {
                    mapping[i] = Some(t.replace_variable(id, term));
                }
            }
        }
    }

    // Returns whether they can be unified.
    pub fn unify_variable(
        &mut self,
        var_scope: Scope,
        var_id: AtomId,
        term_scope: Scope,
        term: &Term,
    ) -> bool {
        if term_scope != Scope::Output {
            // Convert our term to the output scope and then unify.
            let term = self.apply(term_scope, term);
            return self.unify_variable(var_scope, var_id, Scope::Output, &term);
        }

        if var_scope == Scope::Output {
            if term.atomic_variable() == Some(var_id) {
                // We're unifying a variable with itself.
                return true;
            }

            if term.has_variable(var_id) {
                // We can't unify a variable with a term that contains it.
                return false;
            }

            // This is fine.
            self.remap(var_id, term);
            return true;
        }

        if self.has_mapping(var_scope, var_id) {
            // We already have a mapping for this variable.
            // Unify the existing mapping with the term.
            let existing = self.get_mapping(var_scope, var_id).unwrap().clone();
            return self.unify(Scope::Output, &existing, Scope::Output, term);
        }

        // We don't have a mapping for this variable, so we can just map it now.
        self.set_mapping(var_scope, var_id, term.clone());
        true
    }

    pub fn unify(&mut self, scope1: Scope, term1: &Term, scope2: Scope, term2: &Term) -> bool {
        if term1.term_type != term2.term_type {
            return false;
        }

        // Handle the case where we're unifying something with a variable
        if let Some(i) = term1.atomic_variable() {
            return self.unify_variable(scope1, i, scope2, term2);
        }
        if let Some(i) = term2.atomic_variable() {
            return self.unify_variable(scope2, i, scope1, term1);
        }

        // TODO: this won't correctly unify x0(a1) with a0(a1).
        // We also won't correctly unify higher-order functions whose head types don't match.
        // The Term itself doesn't support finding prefix-terms, though, so we need to fix that.

        if term1.head != term2.head {
            return false;
        }

        if term1.args.len() != term2.args.len() {
            return false;
        }

        for (a1, a2) in term1.args.iter().zip(term2.args.iter()) {
            if !self.unify(scope1, a1, scope2, a2) {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use crate::type_space::TypeSpace;

    use super::*;

    #[test]
    fn test_unifying_variables() {
        let mut s = TypeSpace::new();
        let bool0 = s.bref(0);
        let bool1 = s.bref(1);
        let bool2 = s.bref(2);
        let fterm = s.bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let mut u = Unifier::new();

        // Replace x0 with x1 and x1 with x2.
        assert!(u.unify_variable(Scope::Left, 0, Scope::Output, &bool1));
        assert!(u.unify_variable(Scope::Left, 1, Scope::Output, &bool2));
        let term = u.apply(Scope::Left, &fterm);
        assert_eq!(format!("{}", term), "a0(x1, x2)");
    }

    #[test]
    fn test_same_scope() {
        let mut s = TypeSpace::new();
        let bool0 = s.bref(0);
        let bool1 = s.bref(1);
        let bool2 = s.bref(2);
        let term1 = s.bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = s.bfn(Atom::Axiomatic(0), vec![bool1.clone(), bool2.clone()]);
        let mut u = Unifier::new();

        assert!(u.unify(Scope::Left, &term1, Scope::Left, &term2));
        let new1 = u.apply(Scope::Left, &term1);
        assert_eq!(format!("{}", new1), "a0(x0, x0)");
        let new2 = u.apply(Scope::Left, &term2);
        assert_eq!(format!("{}", new2), "a0(x0, x0)");
    }

    #[test]
    fn test_different_scope() {
        let mut s = TypeSpace::new();
        let bool0 = s.bref(0);
        let bool1 = s.bref(1);
        let bool2 = s.bref(2);
        let term1 = s.bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = s.bfn(Atom::Axiomatic(0), vec![bool1.clone(), bool2.clone()]);
        let mut u = Unifier::new();

        assert!(u.unify(Scope::Left, &term1, Scope::Right, &term2));
        let new1 = u.apply(Scope::Left, &term1);
        assert_eq!(format!("{}", new1), "a0(x0, x1)");
        let new2 = u.apply(Scope::Right, &term2);
        assert_eq!(format!("{}", new2), "a0(x0, x1)");
    }
}
