use std::cmp::Ordering;
use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::type_space::{TypeId, ANY, BOOL};
use crate::unifier::Unifier;

// A term with no args is a plain atom.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
        if s == "true" {
            return Term::atom(BOOL, Atom::True);
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return Term::atom(ANY, Atom::new(s)),
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

    pub fn atom(type_id: TypeId, atom: Atom) -> Term {
        Term {
            term_type: type_id,
            head_type: type_id,
            head: atom,
            args: vec![],
        }
    }

    pub fn is_atomic(&self) -> bool {
        self.args.len() == 0
    }

    // Whether this term is structurally identical to the atom "true".
    pub fn is_true(&self) -> bool {
        self.head == Atom::True
    }

    pub fn new_true() -> Term {
        Term::atom(BOOL, Atom::True)
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

    pub fn has_synthetic(&self) -> bool {
        if let Atom::Synthetic(_) = self.head {
            return true;
        }
        for arg in &self.args {
            if arg.has_synthetic() {
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

    pub fn is_variable(&self) -> bool {
        self.atomic_variable().is_some()
    }

    pub fn var_type(&self, index: AtomId) -> Option<TypeId> {
        if self.head == Atom::Variable(index) {
            return Some(self.head_type);
        }
        for arg in &self.args {
            if let Some(t) = arg.var_type(index) {
                return Some(t);
            }
        }
        None
    }

    // A higher order term is one that has a variable as its head.
    pub fn is_higher_order(&self) -> bool {
        match self.head {
            Atom::Variable(_) => true,
            _ => false,
        }
    }

    pub fn atoms_for_type(&self, type_id: TypeId) -> Vec<Atom> {
        let mut answer = vec![];
        if self.term_type == type_id {
            answer.push(self.head);
        }
        for arg in &self.args {
            answer.append(&mut arg.atoms_for_type(type_id));
        }
        answer
    }

    // Does not deduplicate
    pub fn typed_atoms(&self) -> Vec<(TypeId, Atom)> {
        let mut answer = vec![];
        answer.push((self.head_type, self.head));
        for arg in &self.args {
            answer.append(&mut arg.typed_atoms());
        }
        answer
    }

    // value should have no instances of this variable.
    pub fn replace_variable(&self, id: AtomId, value: &Term) -> Term {
        // Start with just the head (but keep the type_id correct for the answer)
        let mut answer = if self.head == Atom::Variable(id) {
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
            answer.args.push(arg.replace_variable(id, value));
        }

        answer
    }

    pub fn replace_atom(&self, atom: &Atom, new_atom: &Atom) -> Term {
        let new_head = if self.head == *atom {
            new_atom.clone()
        } else {
            self.head.clone()
        };

        let new_args = self
            .args
            .iter()
            .map(|arg| arg.replace_atom(atom, new_atom))
            .collect();

        Term {
            term_type: self.term_type,
            head_type: self.head_type,
            head: new_head,
            args: new_args,
        }
    }

    pub fn replace_args(&self, new_args: Vec<Term>) -> Term {
        Term {
            term_type: self.term_type,
            head_type: self.head_type,
            head: self.head,
            args: new_args,
        }
    }

    // Assumes any intermediate ones are taken, so essentially 1 plus the maximum.
    pub fn num_quantifiers(&self) -> AtomId {
        let mut answer = match self.head {
            Atom::Variable(i) => i + 1,
            _ => 0,
        };
        for arg in &self.args {
            answer = answer.max(arg.num_quantifiers());
        }
        answer
    }

    // The first return value is the number of non-variable atoms in the term.
    // The second return value gives each atom a different weight according to its index.
    // These are meant to be used in tiebreak fashion, and should distinguish most
    // distinguishable terms.
    // refcounts adds up the number of references to each variable.
    // "true" is weightless.
    fn multi_weight(&self, refcounts: &mut Vec<u8>) -> (u32, u32) {
        let mut weight1 = 0;
        let mut weight2 = 0;
        match self.head {
            Atom::True => {}
            Atom::Variable(i) => {
                while refcounts.len() <= i as usize {
                    refcounts.push(0);
                }
                refcounts[i as usize] += 1;
            }
            Atom::Constant(i) => {
                weight1 += 1;
                weight2 += 2 * i as u32;
            }
            Atom::Skolem(i) => {
                weight1 += 1;
                weight2 += 1 + 3 * i as u32;
            }
            Atom::Synthetic(i) => {
                weight1 += 1;
                weight2 += 2 + 3 * i as u32;
            }
            Atom::Anonymous => {
                panic!("cannot calculate weight of an anonymous atom");
            }
        }
        for arg in &self.args {
            let (w1, w2) = arg.multi_weight(refcounts);
            weight1 += w1;
            weight2 += w2;
        }
        (weight1, weight2)
    }

    // "true" counts as 0.
    fn atom_count(&self) -> u32 {
        let mut answer = if self.head == Atom::True { 0 } else { 1 };
        for arg in &self.args {
            answer += arg.atom_count();
        }
        answer
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

    // Finds all subterms of this term, and with their paths, appends to "answer".
    // prepends "prefix" to all paths.
    fn push_subterms<'a>(
        &'a self,
        prefix: &mut Vec<usize>,
        answer: &mut Vec<(Vec<usize>, &'a Term)>,
    ) {
        answer.push((prefix.clone(), self));
        for (i, arg) in self.args.iter().enumerate() {
            prefix.push(i);
            arg.push_subterms(prefix, answer);
            prefix.pop();
        }
    }

    pub fn subterms(&self) -> Vec<(Vec<usize>, &Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_subterms(&mut prefix, &mut answer);
        answer
    }

    // Replaces x_i with x_{var_map[i]}.
    pub fn remap_variables(&self, var_map: &Vec<AtomId>) -> Term {
        Term {
            head_type: self.head_type,
            term_type: self.term_type,
            head: self.head.remap_variables(var_map),
            args: self
                .args
                .iter()
                .map(|arg| arg.remap_variables(var_map))
                .collect(),
        }
    }
}

// Literals are always boolean-valued.
// In normalized form, left is the "larger" term.
// Literals like "foo(a, b, c)" are treated as equalities having both
// a left and a right side, by making a right side equal to the special constant "true".
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub positive: bool,
    pub left: Term,
    pub right: Term,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            if self.is_boolean() {
                write!(f, "{}", self.left)
            } else {
                write!(f, "{} = {}", self.left, self.right)
            }
        } else {
            if self.is_boolean() {
                write!(f, "!{}", self.left)
            } else {
                write!(f, "{} != {}", self.left, self.right)
            }
        }
    }
}

impl Literal {
    // Normalizes the direction.
    // The larger term should be on the left of the literal.
    pub fn new(positive: bool, left: Term, right: Term) -> Literal {
        if left < right {
            Literal {
                positive,
                left: right,
                right: left,
            }
        } else {
            Literal {
                positive,
                left,
                right,
            }
        }
    }

    pub fn positive(term: Term) -> Literal {
        Literal::new(true, term, Term::new_true())
    }

    pub fn negative(term: Term) -> Literal {
        Literal::new(false, term, Term::new_true())
    }

    pub fn equals(left: Term, right: Term) -> Literal {
        Literal::new(true, left, right)
    }

    pub fn not_equals(left: Term, right: Term) -> Literal {
        Literal::new(false, left, right)
    }

    pub fn negate(&self) -> Literal {
        Literal {
            positive: !self.positive,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    pub fn parse(s: &str) -> Literal {
        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::equals(left, right)
        } else if s.starts_with("!") {
            let term = Term::parse(&s[1..]);
            Literal::negative(term)
        } else {
            let term = Term::parse(s);
            Literal::positive(term)
        }
    }

    pub fn has_synthetic(&self) -> bool {
        self.left.has_synthetic() || self.right.has_synthetic()
    }

    // Returns true if this literal is a tautology, i.e. foo = foo
    pub fn is_tautology(&self) -> bool {
        self.positive && self.left == self.right
    }

    // Returns whether this clause is syntactically impossible, i.e. foo != foo
    pub fn is_impossible(&self) -> bool {
        !self.positive && self.left == self.right
    }

    // Returns whether this literal is a boolean literal, i.e. "foo" or "!foo"
    pub fn is_boolean(&self) -> bool {
        self.right.is_true()
    }

    pub fn is_higher_order(&self) -> bool {
        self.left.is_higher_order() || self.right.is_higher_order()
    }

    pub fn num_quantifiers(&self) -> AtomId {
        self.left
            .num_quantifiers()
            .max(self.right.num_quantifiers())
    }

    pub fn var_type(&self, i: AtomId) -> Option<AtomId> {
        self.left.var_type(i).or_else(|| self.right.var_type(i))
    }

    // Deduplicates
    pub fn typed_atoms(&self) -> Vec<(TypeId, Atom)> {
        let mut answer = self.left.typed_atoms();
        answer.extend(self.right.typed_atoms());
        answer.sort();
        answer.dedup();
        answer
    }

    pub fn map(&self, f: &mut impl FnMut(&Term) -> Term) -> Literal {
        Literal::new(self.positive, f(&self.left), f(&self.right))
    }

    pub fn replace_atom(&self, atom: &Atom, replacement: &Atom) -> Literal {
        self.map(&mut |term| term.replace_atom(atom, replacement))
    }

    fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }
}

// Literals are ordered so that you can normalize a clause by sorting its literals.
// So, negative literals come first.
// Then, we order backwards by term ordering for the left term.
// Then, backwards (I guess?) for the right term.
impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let positive_cmp = self.positive.cmp(&other.positive);
        if positive_cmp != Ordering::Equal {
            return Some(positive_cmp);
        }

        let left_cmp = other.left.cmp(&self.left);
        if left_cmp != Ordering::Equal {
            return Some(left_cmp);
        }

        Some(other.right.cmp(&self.right))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// A clause is a disjunction (an "or") of literals, universally quantified over some variables.
// We include the types of the universal variables it is quantified over.
// It cannot contain existential quantifiers.
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct Clause {
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
    // An empty clause indicates an impossible clause.
    pub fn new(literals: Vec<Literal>) -> Clause {
        let mut literals = literals
            .into_iter()
            .filter(|x| !x.is_impossible())
            .collect::<Vec<_>>();
        literals.sort();
        literals.dedup();

        Clause {
            literals: Unifier::normalize_var_ids(&literals),
        }
    }

    pub fn impossible() -> Clause {
        Clause::new(vec![])
    }

    pub fn parse(s: &str) -> Clause {
        Clause::new(
            s.split(" | ")
                .map(|x| Literal::parse(x))
                .collect::<Vec<_>>(),
        )
    }

    pub fn num_quantifiers(&self) -> AtomId {
        let mut answer = 0;
        for literal in &self.literals {
            answer = answer.max(literal.num_quantifiers());
        }
        answer
    }

    pub fn is_tautology(&self) -> bool {
        // Find the index of the first positive literal
        if let Some(first_pos) = self.literals.iter().position(|x| x.positive) {
            // Check for (!p, p) pairs which cause a tautology
            for neg_literal in &self.literals[0..first_pos] {
                for pos_literal in &self.literals[first_pos..] {
                    if neg_literal.left == pos_literal.left
                        && neg_literal.right == pos_literal.right
                    {
                        return true;
                    }
                }
            }
        }

        self.literals.iter().any(|x| x.is_tautology())
    }

    pub fn is_impossible(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn atom_count(&self) -> u32 {
        self.literals.iter().map(|x| x.atom_count()).sum()
    }

    pub fn is_rewrite_rule(&self) -> bool {
        if self.literals.len() != 1 {
            return false;
        }
        let literal = &self.literals[0];
        if !literal.positive {
            return false;
        }
        return literal.left.kbo(&literal.right) == Ordering::Greater;
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

    #[test]
    fn test_clause_is_rewrite_rule() {
        assert!(Clause::parse("a0(x0) = x0").is_rewrite_rule());
        assert!(Clause::parse("a0(x0, x0) = x0").is_rewrite_rule());
        assert!(!Clause::parse("a0(x0, x0) != x0").is_rewrite_rule());
        assert!(!Clause::parse("a0(x0, x1) = a0(x1, x0)").is_rewrite_rule());
    }

    #[test]
    fn test_remap_variables() {
        let old_term = Term::parse("a2(x0, x1)");
        let var_map = vec![3, 2];
        let new_term = old_term.remap_variables(&var_map);
        assert_eq!(new_term, Term::parse("a2(x3, x2)"));
    }
}
