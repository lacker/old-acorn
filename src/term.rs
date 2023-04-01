use std::cmp::Ordering;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::atom::{Atom, AtomId};
use crate::substitution::Substitution;
use crate::type_space::TypeId;

// A term with no args is a plain atom.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Term {
    // The term type is the type of the entire term.
    // For example "2 < 3" has type "bool".
    pub term_type: TypeId,

    // The head type is the type of just the head atom.
    // For example the head type of "2 < 3" is "(int, int) -> bool".
    pub head_type: TypeId,

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

// The comparison for terms is an extension of the Knuth-Bendix ordering.
// This comparison is total, whereas the KBO is not.
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<Ordering> {
        let kbo_cmp = self.kbo_helper(other, false);
        if kbo_cmp != Ordering::Equal {
            return Some(kbo_cmp);
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

// Returns true if a[i] >= b[i] for all i, defaulting to zero.
// Can be assumed the last element of each array is not zero.
fn dominates(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if b.len() > a.len() {
        return false;
    }
    for i in 0..b.len() {
        if a[i] < b[i] {
            return false;
        }
    }
    true
}

impl Term {
    // This creates an untyped term, good for testing but not for real use.
    // For example, this parses
    //   a0(a1, a2(x0, x1))
    // into a term with head a0 and args [a1, a2(x0, x1)].
    pub fn parse(s: &str) -> Term {
        let first_paren = match s.find('(') {
            Some(i) => i,
            None => {
                return Term {
                    term_type: 0,
                    head_type: 0,
                    head: Atom::new(s),
                    args: vec![],
                };
            }
        };

        // Figure out which commas are inside precisely one level of parentheses.
        let mut terminator_indices = vec![];
        let mut num_parens = 0;
        for (i, c) in s.chars().enumerate() {
            match c {
                '(' => num_parens += 1,
                ')' => {
                    num_parens -= 1;
                    if num_parens == 0 {
                        terminator_indices.push(i);
                    }
                }
                ',' => {
                    if num_parens == 1 {
                        terminator_indices.push(i);
                    }
                }
                _ => (),
            }
        }

        // Split the string into the head and the args.
        let head = &s[0..first_paren];
        let mut args = vec![];
        for (i, comma_index) in terminator_indices.iter().enumerate() {
            let start = if i == 0 {
                first_paren + 1
            } else {
                terminator_indices[i - 1] + 1
            };
            args.push(Term::parse(&s[start..*comma_index]));
        }

        Term {
            term_type: 0,
            head_type: 0,
            head: Atom::new(head),
            args,
        }
    }

    pub fn is_atomic(&self) -> bool {
        self.args.len() == 0
    }

    // Whether this term contains a variable with this index, anywhere in its body, recursively.
    pub fn has_variable(&self, index: AtomId) -> bool {
        if let Atom::Variable(i) = self.head {
            if i == index {
                return true;
            }
        }
        for arg in &self.args {
            if arg.has_variable(index) {
                return true;
            }
        }
        false
    }

    // If this term is a variable with the given index, return that index.
    pub fn atomic_variable(&self) -> Option<AtomId> {
        if self.args.len() > 0 {
            return None;
        }
        match self.head {
            Atom::Variable(i) => Some(i),
            _ => None,
        }
    }

    // value should have no instances of this variable.
    pub fn replace_variable(&self, index: AtomId, value: &Term) -> Term {
        // Start with just the head (but keep the type_id correct for the answer)
        let mut answer = if self.head == Atom::Variable(index) {
            Term {
                term_type: self.term_type,
                head_type: value.head_type,
                head: value.head.clone(),
                args: value.args.clone(),
            }
        } else {
            Term {
                term_type: self.term_type,
                head_type: self.head_type,
                head: self.head,
                args: vec![],
            }
        };

        for arg in &self.args {
            answer.args.push(arg.replace_variable(index, value));
        }

        answer
    }

    // Make a copy of this term that shifts all of its variable ids.
    pub fn shift_variables(&self, shift: AtomId) -> Term {
        Term {
            term_type: self.term_type,
            head_type: self.head_type,
            head: self.head.shift_variables(shift),
            args: self
                .args
                .iter()
                .map(|arg| arg.shift_variables(shift))
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

    // The first return value is the number of non-variable atoms in the term.
    // The second return value gives each atom a different weight according to its index.
    // These are meant to be used in tiebreak fashion, and should distinguish most
    // distinguishable terms.
    // refcounts adds up the number of references to each variable.
    fn multi_weight(&self, refcounts: &mut Vec<u8>) -> (u32, u32) {
        let mut weight1 = 0;
        let mut weight2 = 0;
        match self.head {
            Atom::Variable(i) => {
                while refcounts.len() <= i as usize {
                    refcounts.push(0);
                }
                refcounts[i as usize] += 1;
            }
            Atom::Axiomatic(i) => {
                weight1 += 1;
                weight2 += 2 * i as u32;
            }
            Atom::Skolem(i) => {
                weight1 += 1;
                weight2 += 1 + 2 * i as u32;
            }
        }
        for arg in &self.args {
            let (w1, w2) = arg.multi_weight(refcounts);
            weight1 += w1;
            weight2 += w2;
        }
        (weight1, weight2)
    }

    // A "reduction order" is stable under variable substitution.
    // This implements a Knuth-Bendix reduction ordering.
    // Returns Greater if we should rewrite self -> other.
    // Returns Less if we should rewrite other -> self.
    // Returns Equal if they cannot be placed in a reduction order.
    pub fn kbo(&self, other: &Term) -> Ordering {
        self.kbo_helper(other, true)
    }

    // Lets you extend the KBO ordering to skip the domination check.
    fn kbo_helper(&self, other: &Term, check_domination: bool) -> Ordering {
        let mut self_refcounts = vec![];
        let (self_weight1, self_weight2) = self.multi_weight(&mut self_refcounts);

        let mut other_refcounts = vec![];
        let (other_weight1, other_weight2) = other.multi_weight(&mut other_refcounts);

        if self_weight1 > other_weight1
            || self_weight1 == other_weight1 && self_weight2 > other_weight2
        {
            if !check_domination || dominates(&self_refcounts, &other_refcounts) {
                return Ordering::Greater;
            }
            return Ordering::Equal;
        }

        if self_weight1 < other_weight1
            || self_weight1 == other_weight1 && self_weight2 < other_weight2
        {
            if !check_domination || dominates(&other_refcounts, &self_refcounts) {
                return Ordering::Less;
            }
            return Ordering::Equal;
        }

        Ordering::Equal
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

    pub fn get_term_at_path(&self, path: &[usize]) -> Option<&Term> {
        let mut current_term = self;
        for &i in path {
            if i >= current_term.args.len() {
                return None;
            }
            current_term = &current_term.args[i];
        }
        Some(current_term)
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
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Literal {
    Positive(Term),
    Equals(Term, Term),
    Negative(Term),
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

    pub fn first_term(&self) -> &Term {
        match self {
            Literal::Positive(term) => term,
            Literal::Negative(term) => term,
            Literal::Equals(left, _) => left,
            Literal::NotEquals(left, _) => left,
        }
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
        literals.reverse();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_ordering() {
        assert!(Term::parse("a0") < Term::parse("a1"));
        assert!(Term::parse("a2") < Term::parse("a0(a1)"));
        assert!(Term::parse("x0(x1)") < Term::parse("x0(s0(x0))"));
    }
}
