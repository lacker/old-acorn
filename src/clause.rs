use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::{AcornValue, FunctionApplication};
use crate::atom::{Atom, TypedAtom};

// Clauses and their parts, like Literals and Terms.

// If args is not empty, then atom should be treated as a function.
// Otherwise, the term is just the atom.
// This is more general than typical first-order logic terms, because the
// function can be quantified.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Term {
    pub atom: TypedAtom,
    pub args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.atom)
        } else {
            write!(f, "{}(", self.atom)?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")
        }
    }
}

impl Term {
    pub fn new(atom: TypedAtom, args: Vec<Term>) -> Term {
        Term { atom, args }
    }

    pub fn from_atom(atom: TypedAtom) -> Term {
        Term {
            atom,
            args: Vec::new(),
        }
    }

    pub fn from_application(app: FunctionApplication) -> Term {
        let atom = match *app.function {
            AcornValue::Atom(atom) => atom,
            _ => panic!("cannot convert {:?} to a term", app.function),
        };
        Term {
            atom: atom,
            args: app.args.into_iter().map(|x| Term::from_value(x)).collect(),
        }
    }

    // Panics if this value cannot be converted to a term.
    pub fn from_value(value: AcornValue) -> Term {
        match value {
            AcornValue::Atom(atom) => Term::from_atom(atom),
            AcornValue::Application(app) => Term::from_application(app),
            _ => panic!("cannot convert {:?} to a term", value),
        }
    }

    // Whether this term contains a reference with this index, anywhere in its body, recursively.
    pub fn has_reference(&self, index: usize) -> bool {
        if let Atom::Reference(i) = self.atom.atom {
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

    // Whether this term is purely an atomic reference
    pub fn atomic_reference(&self) -> Option<usize> {
        if self.args.is_empty() {
            if let Atom::Reference(i) = self.atom.atom {
                return Some(i);
            }
        }
        None
    }

    // value should already not contain a reference to index
    pub fn replace_reference(&self, index: usize, value: &Term) -> Term {
        if let Atom::Reference(i) = self.atom.atom {
            if i == index {
                if self.args.is_empty() {
                    return value.clone();
                }
                if !value.args.is_empty() {
                    panic!("we can't create terms of the form f(x)(y)");
                }
                return Term {
                    atom: value.atom.clone(),
                    args: self.args.clone(),
                };
            }
        }
        Term {
            atom: self.atom.clone(),
            args: self
                .args
                .iter()
                .map(|x| x.replace_reference(index, value))
                .collect(),
        }
    }

    // The subindex is a slice of indices so that the subterm can be deeply nested.
    pub fn get_subterm(&self, subindex: &[usize]) -> &Term {
        if subindex.is_empty() {
            return self;
        }
        let i = subindex[0];
        if i >= self.args.len() {
            panic!("subindex {:?} is too long for term {:?}", subindex, self);
        }
        self.args[i].get_subterm(&subindex[1..])
    }

    // For testing, make a boolean reference
    #[cfg(test)]
    pub fn bref(index: usize) -> Term {
        Term::from_atom(TypedAtom {
            atom: Atom::Reference(index),
            acorn_type: AcornType::Bool,
        })
    }

    // For testing, make a function with this atom, typed (bool^n) -> bool
    #[cfg(test)]
    pub fn bfn(atom: Atom, args: Vec<Term>) -> Term {
        use crate::acorn_type::FunctionType;

        let ftype = AcornType::Function(FunctionType {
            arg_types: args.iter().map(|_| AcornType::Bool).collect(),
            return_type: Box::new(AcornType::Bool),
        });

        Term {
            atom: TypedAtom {
                atom,
                acorn_type: ftype,
            },
            args,
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
    // Panics if this value cannot be converted to a literal.
    // Swaps left and right if needed, to sort.
    pub fn from_value(value: AcornValue) -> Literal {
        match value {
            AcornValue::Atom(atom) => Literal::Positive(Term::from_atom(atom)),
            AcornValue::Application(app) => Literal::Positive(Term::from_application(app)),
            AcornValue::Equals(left, right) => {
                let left_term = Term::from_value(*left);
                let right_term = Term::from_value(*right);
                if left_term <= right_term {
                    Literal::Equals(left_term, right_term)
                } else {
                    Literal::Equals(right_term, left_term)
                }
            }
            AcornValue::NotEquals(left, right) => {
                let left_term = Term::from_value(*left);
                let right_term = Term::from_value(*right);
                if left_term <= right_term {
                    Literal::NotEquals(left_term, right_term)
                } else {
                    Literal::NotEquals(right_term, left_term)
                }
            }
            AcornValue::Not(subvalue) => Literal::Negative(Term::from_value(*subvalue)),
            _ => panic!("cannot convert {:?} to a literal", value),
        }
    }

    // Everything below "and" and "or" nodes must be literals.
    // Skips any tautologies.
    // Appends all results found.
    pub fn into_cnf(value: AcornValue, results: &mut Vec<Vec<Literal>>) {
        match value {
            AcornValue::And(left, right) => {
                Literal::into_cnf(*left, results);
                Literal::into_cnf(*right, results);
            }
            AcornValue::Or(left, right) => {
                let mut left_results = Vec::new();
                Literal::into_cnf(*left, &mut left_results);
                let mut right_results = Vec::new();
                Literal::into_cnf(*right, &mut right_results);
                for left_result in left_results {
                    for right_result in &right_results {
                        let mut combined = left_result.clone();
                        combined.extend(right_result.clone());
                        results.push(combined);
                    }
                }
            }
            _ => {
                let literal = Literal::from_value(value);
                if !literal.is_tautology() {
                    results.push(vec![literal]);
                }
            }
        }
    }

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
    // Make a substitution over n universal variables that doesn't substitute anything.
    //
    // In general, we produce substitutions via several steps of unification, where we
    // specify some entities that we want to be the same, in the resulting substitution.
    //
    // Unification should be a "narrowing" process, in the sense that if sub(x) = sub(y),
    // then sub(x) = sub(y) continues to be true after subsequent unifications.
    pub fn new(n: usize) -> Substitution {
        Substitution {
            terms: vec![None; n],
        }
    }

    // Fails if we try to replace an atom with a non-atom.
    // This doesn't work if we try to generate functional terms like:
    //   f = g(x) and y = f(z)
    // implies
    //   y = g(x)(z).
    pub fn sub_atom(&self, atom: &TypedAtom) -> TypedAtom {
        if let Atom::Reference(index) = atom.atom {
            if let Some(term) = &self.terms[index] {
                if term.args.len() > 0 {
                    panic!("cannot substitute a functional atom into a non-atomic term");
                }
                return TypedAtom {
                    atom: term.atom.atom.clone(),
                    acorn_type: atom.acorn_type.clone(),
                };
            }
        }
        atom.clone()
    }

    pub fn sub_term(&self, term: &Term) -> Term {
        if let Some(i) = term.atomic_reference() {
            if let Some(t) = &self.terms[i] {
                return t.clone();
            }
            return term.clone();
        }
        Term {
            atom: self.sub_atom(&term.atom),
            args: term.args.iter().map(|x| self.sub_term(x)).collect(),
        }
    }

    // Unifies a reference atom with a term.
    // Returns whether this is possible.
    pub fn unify_reference(&mut self, index: usize, term: &Term) -> bool {
        if let Some(existing_term) = &self.terms[index] {
            return self.unify_terms(&existing_term.clone(), term);
        }

        // This reference isn't bound to anything, so it should be okay to bind it,
        // as long as that doesn't create any circular references.
        let simplified_term = self.sub_term(term);
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

        self.terms[index] = Some(simplified_term);
        true
    }

    // Unifies two atoms.
    // Returns whether this is possible.
    pub fn unify_atoms(&mut self, atom1: &TypedAtom, atom2: &TypedAtom) -> bool {
        if atom1.acorn_type != atom2.acorn_type {
            return false;
        }
        if atom1.atom == atom2.atom {
            return true;
        }

        // If we're just making two references equal, change the second one, to tend
        // toward sticking with lower numbers.
        // Either should be logically correct.
        if let Atom::Reference(index) = atom2.atom {
            return self.unify_reference(index, &Term::from_atom(atom1.clone()));
        }
        if let Atom::Reference(index) = atom1.atom {
            return self.unify_reference(index, &Term::from_atom(atom2.clone()));
        }

        false
    }

    // Unifies two terms.
    // Returns whether this is possible.
    pub fn unify_terms(&mut self, term1: &Term, term2: &Term) -> bool {
        // If we're just making two references equal, change the second one, to tend
        // toward sticking with lower numbers.
        // Either should be logically correct.
        if let Some(i) = term2.atomic_reference() {
            return self.unify_reference(i, term1);
        }
        if let Some(i) = term1.atomic_reference() {
            return self.unify_reference(i, term2);
        }

        if term1.args.len() != term2.args.len() {
            return false;
        }

        if !self.unify_atoms(&term1.atom, &term2.atom) {
            return false;
        }

        for (arg1, arg2) in term1.args.iter().zip(term2.args.iter()) {
            if !self.unify_terms(arg1, arg2) {
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
        let bool0 = Term::bref(0);
        let bool1 = Term::bref(1);
        let fterm = Term::bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let mut sub = Substitution::new(2);

        // Replace x0 with x1
        assert!(sub.unify_reference(0, &bool1));
        let term = sub.sub_term(&fterm);
        assert_eq!(format!("{}", term), "a0(x1, x1)");
    }

    #[test]
    fn test_unify_terms() {
        let bool0 = Term::bref(0);
        let bool1 = Term::bref(1);
        let bool2 = Term::bref(2);
        let term1 = Term::bfn(Atom::Axiomatic(0), vec![bool0.clone(), bool1.clone()]);
        let term2 = Term::bfn(Atom::Axiomatic(0), vec![bool1.clone(), bool2.clone()]);
        let mut sub = Substitution::new(3);

        // Replace x0 with x1
        assert!(sub.unify_terms(&term1, &term2));
        let new1 = sub.sub_term(&term1);
        assert_eq!(format!("{}", new1), "a0(x0, x0)");
        let new2 = sub.sub_term(&term2);
        assert_eq!(format!("{}", new2), "a0(x0, x0)");
    }
}
