use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, TypedAtom};

// A TermSpace contains information about a set of terms.
pub struct TermSpace {
    types: Vec<AcornType>,
}

impl TermSpace {
    pub fn new() -> TermSpace {
        TermSpace { types: vec![] }
    }

    // Returns the index of the type, or "itype".
    pub fn add_type(&mut self, acorn_type: AcornType) -> usize {
        for (i, t) in self.types.iter().enumerate() {
            if t == &acorn_type {
                return i;
            }
        }
        self.types.push(acorn_type);
        self.types.len() - 1
    }

    // Constructs a new term from an atom
    pub fn term_from_atom(&mut self, atom: TypedAtom) -> Term {
        Term {
            itype: self.add_type(atom.acorn_type),
            head: atom.atom,
            args: vec![],
        }
    }

    // Constructs a new term from a function application
    // Function applications that are nested like f(x)(y) are flattened to f(x, y)
    pub fn term_from_application(&mut self, application: FunctionApplication) -> Term {
        let itype = self.add_type(application.return_type());
        let func_term = self.term_from_value(*application.function);
        let head = func_term.head;
        let mut args = func_term.args;
        for arg in application.args {
            args.push(self.term_from_value(arg));
        }
        Term { itype, head, args }
    }

    // Constructs a new term from an AcornValue
    pub fn term_from_value(&mut self, value: AcornValue) -> Term {
        match value {
            AcornValue::Atom(atom) => self.term_from_atom(atom),
            AcornValue::Application(application) => self.term_from_application(application),
            _ => panic!("cannot convert value to term: {:?}", value),
        }
    }

    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    pub fn literal_from_value(&mut self, value: AcornValue) -> Literal {
        match value {
            AcornValue::Atom(atom) => Literal::Positive(self.term_from_atom(atom)),
            AcornValue::Application(app) => Literal::Positive(self.term_from_application(app)),
            AcornValue::Equals(left, right) => {
                let left_term = self.term_from_value(*left);
                let right_term = self.term_from_value(*right);
                if left_term <= right_term {
                    Literal::Equals(left_term, right_term)
                } else {
                    Literal::Equals(right_term, left_term)
                }
            }
            AcornValue::NotEquals(left, right) => {
                let left_term = self.term_from_value(*left);
                let right_term = self.term_from_value(*right);
                if left_term <= right_term {
                    Literal::NotEquals(left_term, right_term)
                } else {
                    Literal::NotEquals(right_term, left_term)
                }
            }
            AcornValue::Not(subvalue) => Literal::Negative(self.term_from_value(*subvalue)),
            _ => panic!("cannot convert {:?} to a literal", value),
        }
    }

    // Converts a value to Clausal Normal Form.
    // Everything below "and" and "or" nodes must be literals.
    // Skips any tautologies.
    // Appends all results found.
    pub fn into_cnf(&mut self, value: AcornValue, results: &mut Vec<Vec<Literal>>) {
        match value {
            AcornValue::And(left, right) => {
                self.into_cnf(*left, results);
                self.into_cnf(*right, results);
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                self.into_cnf(*left, &mut left_results);
                let mut right_results = Vec::new();
                self.into_cnf(*right, &mut right_results);
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
            }
            _ => {
                let literal = self.literal_from_value(value);
                if !literal.is_tautology() {
                    results.push(vec![literal]);
                }
            }
        }
    }

    // For testing, make a boolean reference
    #[cfg(test)]
    pub fn bref(&mut self, index: usize) -> Term {
        self.term_from_atom(TypedAtom {
            atom: Atom::Reference(index),
            acorn_type: AcornType::Bool,
        })
    }

    // For testing, make a function application with this head, return type bool
    #[cfg(test)]
    pub fn bfn(&mut self, head: Atom, args: Vec<Term>) -> Term {
        Term {
            itype: self.add_type(AcornType::Bool),
            head,
            args,
        }
    }
}

// A term with no args is a plain atom.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Term {
    pub itype: usize,
    head: Atom,
    args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        if self.args.len() > 0 {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Term {
    // Whether this term contains a reference with this index, anywhere in its body, recursively.
    pub fn has_reference(&self, index: usize) -> bool {
        if let Atom::Reference(i) = self.head {
            if i == index {
                return true;
            }
        }
        for arg in &self.args {
            if arg.has_reference(index) {
                return true;
            }
        }
        false
    }

    // If this term is a reference to the given index, return that index.
    pub fn atomic_reference(&self) -> Option<usize> {
        if self.args.len() > 0 {
            return None;
        }
        match self.head {
            Atom::Reference(i) => Some(i),
            _ => None,
        }
    }

    // value should have no references to index
    pub fn replace_reference(&self, index: usize, value: &Term) -> Term {
        // Start with just the head (but keep the itype correct for the answer)
        let mut answer = if self.head == Atom::Reference(index) {
            Term {
                itype: self.itype,
                head: value.head.clone(),
                args: value.args.clone(),
            }
        } else {
            Term {
                itype: self.itype,
                head: self.head,
                args: vec![],
            }
        };

        for arg in &self.args {
            answer.args.push(arg.replace_reference(index, value));
        }

        answer
    }

    // Make a copy of this term that shifts all of its reference ids.
    pub fn shift_references(&self, shift: usize) -> Term {
        Term {
            itype: self.itype,
            head: self.head.shift_references(shift),
            args: self
                .args
                .iter()
                .map(|arg| arg.shift_references(shift))
                .collect(),
        }
    }
}

// Literals are always boolean-valued.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum Literal {
    Positive(Term),
    Negative(Term),
    Equals(Term, Term),
    NotEquals(Term, Term),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Positive(term) => write!(f, "{}", term),
            Literal::Negative(term) => write!(f, "!{}", term),
            Literal::Equals(left, right) => write!(f, "{} = {}", left, right),
            Literal::NotEquals(left, right) => write!(f, "{} != {}", left, right),
        }
    }
}

impl Literal {
    // Returns true if this literal is a tautology, i.e. foo = foo
    pub fn is_tautology(&self) -> bool {
        if let Literal::Equals(left, right) = self {
            return left == right;
        }
        false
    }

    // Returns whether this clause is syntactically impossible, i.e. foo != foo
    pub fn is_impossible(&self) -> bool {
        if let Literal::NotEquals(left, right) = self {
            return left == right;
        }
        false
    }
}

// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
#[derive(Debug)]
pub struct Clause {
    pub universal: Vec<AcornType>,
    pub literals: Vec<Literal>,
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}", literal)?;
        }
        Ok(())
    }
}

impl Clause {
    // Sorts literals.
    // Removes any duplicate or impossible literals.
    pub fn new(universal: &Vec<AcornType>, literals: Vec<Literal>) -> Clause {
        let mut literals = literals
            .into_iter()
            .filter(|x| !x.is_impossible())
            .collect::<Vec<_>>();
        literals.sort();
        literals.dedup();
        Clause {
            universal: universal.clone(),
            literals,
        }
    }
}

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

    pub fn get_term(&self, i: usize) -> Option<&Term> {
        match self.terms.get(i) {
            Some(t) => t.as_ref(),
            None => None,
        }
    }

    // Returns the term that this atom refers to, if there is any.
    pub fn dereference(&self, atom: &Atom, shift: usize) -> Option<&Term> {
        match atom {
            Atom::Reference(i) => self.get_term(*i + shift),
            _ => None,
        }
    }

    // Substitutes into this term, shifting its references first.
    pub fn sub_term(&self, term: &Term, shift: usize) -> Term {
        // Start with just the head (but keep the itype correct for the answer)
        let mut answer = if let Some(t) = self.dereference(&term.head, shift) {
            Term {
                itype: term.itype,
                head: t.head.clone(),
                args: t.args.clone(),
            }
        } else {
            Term {
                itype: term.itype,
                head: term.head.clone(),
                args: vec![],
            }
        };

        for arg in &term.args {
            answer.args.push(self.sub_term(arg, shift))
        }

        answer
    }

    pub fn set_term(&mut self, i: usize, term: Term) {
        if i >= self.terms.len() {
            self.terms.resize(i + 1, None);
        }
        self.terms[i] = Some(term);
    }

    // Unifies a reference atom with a term, shifting the term's references first.
    // If this succeeds:
    //   self.sub(ref(index)) = self.sub(term, shift)
    // Subsequent calls to identify or unify will maintain this property.
    pub fn unify_reference(&mut self, index: usize, term: &Term, shift: usize) -> bool {
        if let Some(existing_term) = self.get_term(index) {
            return self.unify_terms(&existing_term.clone(), term, shift);
        }

        if let Some(i) = term.atomic_reference() {
            if index == i + shift {
                // References unify with themselves without any update needed
                return true;
            }
        }

        // This reference isn't bound to anything, so it should be okay to bind it,
        // as long as that doesn't create any circular references.
        let simplified_term = self.sub_term(term, shift);
        if simplified_term.has_reference(index) {
            return false;
        }

        // Replace any mentions of this reference in the current substitution map, so
        // that we don't have to recursively substitute in the future.
        for existing_term in self.terms.iter_mut() {
            if let Some(t) = existing_term {
                *existing_term = Some(t.replace_reference(index, &simplified_term));
            }
        }

        self.set_term(index, simplified_term);
        true
    }

    // Unifies two terms, after shifting term2's references by shift2.
    // If this succeeds:
    //   self.sub(term1, 0) = self.sub(term2, shift2)
    // Subsequent calls to identify or unify will maintain this property.
    pub fn unify_terms(&mut self, term1: &Term, term2: &Term, shift2: usize) -> bool {
        if term1.itype != term2.itype {
            return false;
        }

        // If we're just making two references equal, change the second one, to tend
        // toward sticking with lower numbers.
        // Either should be logically correct.
        if let Some(i) = term2.atomic_reference() {
            return self.unify_reference(i + shift2, term1, 0);
        }
        if let Some(i) = term1.atomic_reference() {
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

    // Updates this substitution to identify terms.
    // If this succeeds:
    //   self.sub(term1) = term2
    // Subsequent unification will break this constraint, but subsequent calls to identify will not.
    // TODO: is that claim true? It seems like it could fail if some sub-part of term1 gets
    // identified with something else.
    pub fn identify_terms(&mut self, term1: &Term, term2: &Term) -> bool {
        if term1.itype != term2.itype {
            return false;
        }

        // Atomic references in term1 must exactly substitute to term2
        if let Some(i) = term1.atomic_reference() {
            if let Some(existing_term) = self.get_term(i) {
                return existing_term == term2;
            }
            self.set_term(i, term2.clone());
            return true;
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
            if !self.identify_terms(arg1, arg2) {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_reference() {
        let mut s = TermSpace::new();
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
        let mut s = TermSpace::new();
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
