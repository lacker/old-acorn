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
            term: UntypedTerm::Atom(atom.atom),
        }
    }

    // Constructs a new term from a function application
    pub fn term_from_application(&mut self, application: FunctionApplication) -> Term {
        let itype = self.add_type(application.return_type());
        let mut subterms = vec![self.term_from_value(*application.function)];
        for arg in application.args {
            subterms.push(self.term_from_value(arg));
        }
        Term {
            itype,
            term: UntypedTerm::Composite(subterms),
        }
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

    // For testing, make a function application with this atom, typed (bool^n) -> bool
    #[cfg(test)]
    pub fn bfn(&mut self, atom: Atom, args: Vec<Term>) -> Term {
        use crate::acorn_type::FunctionType;

        let acorn_type = AcornType::Function(FunctionType {
            arg_types: args.iter().map(|_| AcornType::Bool).collect(),
            return_type: Box::new(AcornType::Bool),
        });

        let fterm = self.term_from_atom(TypedAtom { atom, acorn_type });

        let mut subterms = vec![fterm];
        subterms.extend(args);

        Term {
            itype: self.add_type(AcornType::Bool),
            term: UntypedTerm::Composite(subterms),
        }
    }
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum UntypedTerm {
    Atom(Atom),
    Composite(Vec<Term>),
}

impl fmt::Display for UntypedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            UntypedTerm::Atom(atom) => write!(f, "{}", atom),
            UntypedTerm::Composite(composite) => {
                for (i, term) in composite.iter().enumerate() {
                    if i > 1 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", term)?;
                    if i == 0 {
                        write!(f, "(")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Term {
    pub itype: usize,
    pub term: UntypedTerm,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.term.fmt(f)
    }
}

impl Term {
    pub fn weight(&self) -> u32 {
        match self.term {
            UntypedTerm::Atom(_) => 1,
            UntypedTerm::Composite(ref terms) => {
                let mut weight = 0;
                for term in terms {
                    weight += term.weight();
                }
                weight
            }
        }
    }

    // Whether this term contains a reference with this index, anywhere in its body, recursively.
    pub fn has_reference(&self, index: usize) -> bool {
        match self.term {
            UntypedTerm::Atom(Atom::Reference(i)) => i == index,
            UntypedTerm::Atom(_) => false,
            UntypedTerm::Composite(ref terms) => {
                for term in terms {
                    if term.has_reference(index) {
                        return true;
                    }
                }
                false
            }
        }
    }

    // If this term is a reference to the given index, return that index.
    pub fn atomic_reference(&self) -> Option<usize> {
        match self.term {
            UntypedTerm::Atom(Atom::Reference(i)) => Some(i),
            _ => None,
        }
    }

    // value should already not contain a reference to index
    pub fn replace_reference(&self, index: usize, value: &Term) -> Term {
        match self.term {
            UntypedTerm::Atom(Atom::Reference(i)) => {
                if i == index {
                    value.clone()
                } else {
                    self.clone()
                }
            }
            UntypedTerm::Atom(_) => self.clone(),
            UntypedTerm::Composite(ref terms) => {
                let mut new_terms = vec![];
                for term in terms {
                    new_terms.push(term.replace_reference(index, value));
                }
                return Term {
                    itype: self.itype,
                    term: UntypedTerm::Composite(new_terms),
                };
            }
        }
    }

    // The subindex is a series of indices.
    pub fn subterm(&self, subindex: &[usize]) -> Option<&Term> {
        let mut term = self;
        for i in subindex {
            if let UntypedTerm::Composite(ref subterms) = term.term {
                if *i >= subterms.len() {
                    return None;
                }
                term = &subterms[*i];
            } else {
                return None;
            }
        }
        Some(term)
    }

    // for_subterm calls f(subindex, subterm) on each subterm of the term.
    // The calls are in preorder.
    // The _helper version is provided a subindex that got to this point in the term.
    fn for_subterm_helper<F>(&self, subindex: &mut Vec<usize>, mut f: F)
    where
        F: FnMut(&Vec<usize>, &Term),
    {
        f(subindex, self);
        if let UntypedTerm::Composite(ref subterms) = self.term {
            for (i, subterm) in subterms.iter().enumerate() {
                subindex.push(i);
                subterm.for_subterm_helper(subindex, &mut f);
                subindex.pop();
            }
        }
    }

    pub fn for_subterm<F>(&self, mut f: F)
    where
        F: FnMut(&Vec<usize>, &Term),
    {
        let mut subindex = vec![];
        self.for_subterm_helper(&mut subindex, &mut f);
    }

    // Make a copy of this term that shifts all of its reference ids.
    pub fn shift_references(&self, shift: usize) -> Term {
        match self.term {
            UntypedTerm::Atom(Atom::Reference(i)) => Term {
                itype: self.itype,
                term: UntypedTerm::Atom(Atom::Reference(i + shift)),
            },
            UntypedTerm::Atom(_) => self.clone(),
            UntypedTerm::Composite(ref subterms) => {
                let mut new_subterms = vec![];
                for subterm in subterms {
                    new_subterms.push(subterm.shift_references(shift));
                }
                Term {
                    itype: self.itype,
                    term: UntypedTerm::Composite(new_subterms),
                }
            }
        }
    }

    pub fn set_subterm(&mut self, subindex: &[usize], value: Term) {
        let mut term = self;
        for i in subindex {
            if let UntypedTerm::Composite(ref mut subterms) = term.term {
                if *i >= subterms.len() {
                    panic!("subindex out of bounds");
                }
                term = &mut subterms[*i];
            } else {
                panic!("subindex out of bounds");
            }
        }
        *term = value;
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
        if self.universal.is_empty() {
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

    // Substitutes into this term, shifting its references first.
    pub fn sub(&self, term: &Term, shift: usize) -> Term {
        match &term.term {
            UntypedTerm::Atom(a) => {
                if let Atom::Reference(i) = a {
                    if let Some(t) = self.get_term(i + shift) {
                        return t.clone();
                    }
                }
                // This is an atom, but not a reference to anything we're substituting.
                // So we just need to shift it, if it's a reference.
                term.shift_references(shift)
            }
            UntypedTerm::Composite(subterms) => Term {
                itype: term.itype,
                term: UntypedTerm::Composite(
                    subterms
                        .into_iter()
                        .map(|t| self.sub(&t, shift))
                        .collect::<Vec<_>>(),
                ),
            },
        }
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

        // This reference isn't bound to anything, so it should be okay to bind it,
        // as long as that doesn't create any circular references.
        let simplified_term = self.sub(term, shift);
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

        match (&term1.term, &term2.term) {
            (UntypedTerm::Atom(a1), UntypedTerm::Atom(a2)) => a1 == a2,
            (UntypedTerm::Composite(subterms1), UntypedTerm::Composite(subterms2)) => {
                if subterms1.len() != subterms2.len() {
                    return false;
                }
                for (subterm1, subterm2) in subterms1.iter().zip(subterms2.iter()) {
                    if !self.unify_terms(subterm1, subterm2, shift2) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    // Updates this substitution to identify terms.
    // If this succeeds:
    //   self.sub(term1) = term2
    // Subsequent unification will break this constraint, but subsequent calls to identify will not.
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

        match (&term1.term, &term2.term) {
            (UntypedTerm::Atom(a1), UntypedTerm::Atom(a2)) => a1 == a2,
            (UntypedTerm::Composite(subterms1), UntypedTerm::Composite(subterms2)) => {
                if subterms1.len() != subterms2.len() {
                    return false;
                }
                for (subterm1, subterm2) in subterms1.iter().zip(subterms2.iter()) {
                    if !self.identify_terms(subterm1, subterm2) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
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
        let term = sub.sub(&fterm, 0);
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
        let new1 = sub.sub(&term1, 0);
        assert_eq!(format!("{}", new1), "a0(x0, x0)");
        let new2 = sub.sub(&term2, 0);
        assert_eq!(format!("{}", new2), "a0(x0, x0)");
    }
}
