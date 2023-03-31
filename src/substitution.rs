use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::term::Term;

pub struct Substitution {
    // terms[i] is the replacement for Reference(i), if it should be replaced.
    pub terms: Vec<Option<Term>>,
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (i, term) in self.terms.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Some(t) = term {
                write!(f, "{}", t)?;
            } else {
                write!(f, "_")?;
            }
        }
        write!(f, "]")
    }
}

impl Substitution {
    // Make a substitution that doesn't substitute anything.
    // We instantiate variables as needed, so we don't need to know how many there are up front.
    pub fn new() -> Substitution {
        Substitution { terms: vec![] }
    }

    fn get_term(&self, i: AtomId) -> Option<&Term> {
        match self.terms.get(i as usize) {
            Some(t) => t.as_ref(),
            None => None,
        }
    }

    // Returns the term that this atom refers to, if there is any.
    fn dereference(&self, atom: &Atom, shift: AtomId) -> Option<&Term> {
        match atom {
            Atom::Variable(i) => self.get_term(*i + shift),
            _ => None,
        }
    }

    // Substitutes into this term, shifting its references first.
    pub fn sub_term(&self, term: &Term, shift: AtomId) -> Term {
        // Start with just the head (but keep the type_id correct for the answer)
        let mut answer = if let Some(t) = self.dereference(&term.head, shift) {
            Term {
                term_type: term.term_type,
                head_type: t.head_type,
                head: t.head.clone(),
                args: t.args.clone(),
            }
        } else {
            Term {
                term_type: term.term_type,
                head_type: term.head_type,
                head: term.head.clone(),
                args: vec![],
            }
        };

        for arg in &term.args {
            answer.args.push(self.sub_term(arg, shift))
        }

        answer
    }

    fn set_term(&mut self, i: AtomId, term: Term) {
        if i >= self.terms.len() as AtomId {
            self.terms.resize((i + 1) as usize, None);
        }
        self.terms[i as usize] = Some(term);
    }

    // Unifies a reference atom with a term, shifting the term's references first.
    // If this succeeds:
    //   self.sub(ref(index)) = self.sub(term, shift)
    // Subsequent calls to identify or unify will maintain this property.
    fn unify_reference(&mut self, index: AtomId, term: &Term, shift: AtomId) -> bool {
        if let Some(existing_term) = self.get_term(index) {
            return self.unify_terms(&existing_term.clone(), term, shift);
        }

        if let Some(i) = term.atomic_variable() {
            if index == i + shift {
                // References unify with themselves without any update needed
                return true;
            }
        }

        // This reference isn't bound to anything, so it should be okay to bind it,
        // as long as that doesn't create any circular references.
        let simplified_term = self.sub_term(term, shift);
        if simplified_term.variable(index) {
            return false;
        }

        // Replace any mentions of this reference in the current substitution map, so
        // that we don't have to recursively substitute in the future.
        for existing_term in self.terms.iter_mut() {
            if let Some(t) = existing_term {
                *existing_term = Some(t.replace_variable(index, &simplified_term));
            }
        }

        self.set_term(index, simplified_term);
        true
    }

    // Unifies two terms, after shifting term2's references by shift2.
    // If this succeeds:
    //   self.sub(term1, 0) = self.sub(term2, shift2)
    // Subsequent calls to identify or unify will maintain this property.
    pub fn unify_terms(&mut self, term1: &Term, term2: &Term, shift2: AtomId) -> bool {
        if term1.term_type != term2.term_type {
            return false;
        }

        // If we're just making two references equal, change the second one, to tend
        // toward sticking with lower numbers.
        // Either should be logically correct.
        if let Some(i) = term2.atomic_variable() {
            return self.unify_reference(i + shift2, term1, 0);
        }
        if let Some(i) = term1.atomic_variable() {
            return self.unify_reference(i, term2, shift2);
        }

        if term1.head != term2.head {
            return false;
        }

        // TODO: figure out how to unify terms with different lengths.
        // This should be possible in higher-order logic!
        if term1.args.len() != term2.args.len() {
            return false;
        }

        for (arg1, arg2) in term1.args.iter().zip(term2.args.iter()) {
            if !self.unify_terms(arg1, arg2, shift2) {
                return false;
            }
        }
        true
    }

    // Updates this substitution to match terms.
    // If this succeeds:
    //   self.sub(term1) = term2
    // Every variable must be substituted out of term1.
    // Subsequent unification will break this constraint, but subsequent calls to identify will not.
    // TODO: is that claim true? It seems like it could fail if some sub-part of term1 gets
    // identified with something else.
    pub fn match_terms(&mut self, term1: &Term, term2: &Term) -> bool {
        if term1.term_type != term2.term_type {
            return false;
        }

        // Atomic references in term1 must exactly substitute to term2
        if let Some(i) = term1.atomic_variable() {
            if let Some(existing_term) = self.get_term(i) {
                return existing_term == term2;
            }
            self.set_term(i, term2.clone());
            return true;
        }

        // TODO: this should also work if term1.head is a reference
        if term1.head != term2.head {
            return false;
        }

        // TODO: figure out how to unify terms with different lengths.
        // This should be possible in higher-order logic!
        if term1.args.len() != term2.args.len() {
            return false;
        }

        for (arg1, arg2) in term1.args.iter().zip(term2.args.iter()) {
            if !self.match_terms(arg1, arg2) {
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
    fn test_unify_reference() {
        let mut s = TypeSpace::new();
        let bool0 = s.bref(0);
        let bool1 = s.bref(1);
        let fterm = s.bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let mut sub = Substitution::new();

        // Replace x0 with x1
        assert!(sub.unify_reference(0, &bool1, 0));
        let term = sub.sub_term(&fterm, 0);
        assert_eq!(format!("{}", term), "a0(x1, x1)");
    }

    #[test]
    fn test_unify_terms() {
        let mut s = TypeSpace::new();
        let bool0 = s.bref(0);
        let bool1 = s.bref(1);
        let bool2 = s.bref(2);
        let term1 = s.bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = s.bfn(Atom::Axiomatic(0), vec![bool1.clone(), bool2.clone()]);
        let mut sub = Substitution::new();

        // Replace x0 with x1
        assert!(sub.unify_terms(&term1, &term2, 0));
        let new1 = sub.sub_term(&term1, 0);
        assert_eq!(format!("{}", new1), "a0(x0, x0)");
        let new2 = sub.sub_term(&term2, 0);
        assert_eq!(format!("{}", new2), "a0(x0, x0)");
    }
}
