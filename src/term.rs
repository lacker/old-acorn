use std::cmp::Ordering;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::atom::Atom;
use crate::substitution::Substitution;

// A term with no args is a plain atom.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
    pub itype: usize,
    pub head: Atom,
    pub args: Vec<Term>,
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

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<Ordering> {
        let atom_cmp = self.atom_weight().cmp(&other.atom_weight());
        if atom_cmp != Ordering::Equal {
            return Some(atom_cmp);
        }

        let var_cmp = self.var_weight().cmp(&other.var_weight());
        if var_cmp != Ordering::Equal {
            return Some(var_cmp);
        }

        let tiebreak = self.partial_tiebreak(other);
        if tiebreak != Ordering::Equal {
            return Some(tiebreak);
        }

        Some(self.total_tiebreak(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Term) -> Ordering {
        self.partial_cmp(other).unwrap()
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

    // If these two terms differ in only one subterm, return references to those subterms.
    pub fn matches_but_one<'a, 'b>(&'a self, other: &'b Term) -> Option<(&'a Term, &'b Term)> {
        if self.head != other.head {
            return None;
        }
        if self.args.len() != other.args.len() {
            return None;
        }
        let mut answer = None;
        for (arg1, arg2) in self.args.iter().zip(other.args.iter()) {
            if arg1 != arg2 {
                if answer.is_some() {
                    return None;
                }
                answer = Some((arg1, arg2));
            }
        }
        answer
    }

    // Total number of atoms in this term, including the head.
    fn atom_weight(&self) -> u32 {
        let mut answer = 1;
        for arg in &self.args {
            answer += arg.atom_weight();
        }
        answer
    }

    // Total number of occurrences of variables in this term, including the head.
    fn var_weight(&self) -> u32 {
        let mut answer = 0;
        if let Atom::Reference(_) = self.head {
            answer += 1;
        }
        for arg in &self.args {
            answer += arg.var_weight();
        }
        answer
    }

    // Does a partial ordering that is stable under variable renaming.
    // This is less good than using a weight, so just use it as a tiebreak.
    fn partial_tiebreak(&self, other: &Term) -> Ordering {
        let head_cmp = self.head.stable_partial_order(&other.head);
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // I feel like a top-level function with more arguments is more "flattened",
        // and thus simpler.
        let len_cmp = other.args.len().cmp(&self.args.len());
        if len_cmp != Ordering::Equal {
            return len_cmp;
        }

        for (arg1, arg2) in self.args.iter().zip(other.args.iter()) {
            let arg_cmp = arg1.partial_tiebreak(arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    // Does a total ordering, not stable under variable renaming.
    // Only run this after the partial tiebreak.
    fn total_tiebreak(&self, other: &Term) -> Ordering {
        let head_cmp = other.head.cmp(&self.head);
        if head_cmp != Ordering::Equal {
            return head_cmp;
        }

        // The partial tiebreak should have caught this
        assert!(self.args.len() == other.args.len());

        for (arg1, arg2) in self.args.iter().zip(other.args.iter()) {
            let arg_cmp = arg1.cmp(arg2);
            if arg_cmp != Ordering::Equal {
                return arg_cmp;
            }
        }

        Ordering::Equal
    }

    // Once this finds a single rewrite, it stops and returns the new term.
    pub fn rewrite(&self, find: &Term, replace: &Term) -> Option<Term> {
        // See if this entire term matches
        let mut sub = Substitution::new();
        if sub.match_terms(find, self) {
            let candidate = sub.sub_term(replace, 0);
            if &candidate < self {
                return Some(candidate);
            }
        }

        for (i, arg) in self.args.iter().enumerate() {
            if let Some(new_arg) = arg.rewrite(find, replace) {
                let mut answer = self.clone();
                answer.args[i] = new_arg;

                // The ordering should be designed so that this is the case, but
                // let's just make sure.
                assert!(&answer < self);

                return Some(answer);
            }
        }

        None
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

    pub fn num_quantifiers(&self) -> usize {
        self.universal.len()
    }
}
