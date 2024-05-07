use std::cmp::Ordering;
use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::type_map::{TypeId, BOOL, EMPTY};

// A term with no args is a plain atom.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Term {
    // The term type is the type of the entire term.
    // For example "2 < 3" has type "Bool".
    pub term_type: TypeId,

    // The head type is the type of just the head atom.
    // For example the head type of "2 < 3" is "(int, int) -> bool".
    pub head_type: TypeId,

    pub head: Atom,
    pub args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tf = TermFormatter {
            term: self,
            var: 'x',
        };
        write!(f, "{}", tf)
    }
}

// Formatting terms with slight changes.
pub struct TermFormatter<'a> {
    pub term: &'a Term,
    pub var: char,
}

impl fmt::Display for TermFormatter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.term.head {
            Atom::Variable(i) => write!(f, "{}{}", self.var, i)?,
            _ => write!(f, "{}", self.term.head)?,
        }
        if self.term.args.len() > 0 {
            write!(f, "(")?;
            for (i, arg) in self.term.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(
                    f,
                    "{}",
                    TermFormatter {
                        term: &arg,
                        var: self.var
                    }
                )?;
            }
            write!(f, ")")?;
        }
        Ok(())
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
    pub fn new(term_type: TypeId, head_type: TypeId, head: Atom, args: Vec<Term>) -> Term {
        Term {
            term_type,
            head_type,
            head,
            args,
        }
    }

    pub fn get_term_type(&self) -> TypeId {
        self.term_type
    }

    pub fn get_head_type(&self) -> TypeId {
        self.head_type
    }

    pub fn get_head(&self) -> &Atom {
        &self.head
    }

    pub fn iter_args(&self) -> impl Iterator<Item = &Term> {
        self.args.iter()
    }

    // This doesn't change the term type, so the caller is responsible for making sure
    // the type is correct.
    pub fn push_arg(&mut self, arg: Term) {
        self.args.push(arg);
    }

    pub fn num_args(&self) -> usize {
        self.args.len()
    }

    // This creates a mistyped term, okay for testing but not for real use.
    // For example, this parses
    //   c0(c1, c2(x0, x1))
    // into a term with head c0 and args [c1, c2(x0, x1)].
    pub fn parse(s: &str) -> Term {
        if s == "true" {
            return Term::atom(BOOL, Atom::True);
        }

        let first_paren = match s.find('(') {
            Some(i) => i,
            None => return Term::atom(EMPTY, Atom::new(s)),
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

    pub fn has_any_variable(&self) -> bool {
        if self.head.is_variable() {
            return true;
        }
        for arg in &self.args {
            if arg.has_any_variable() {
                return true;
            }
        }
        false
    }

    pub fn has_local_constant(&self) -> bool {
        if self.head.is_local_constant() {
            return true;
        }
        for arg in &self.args {
            if arg.has_local_constant() {
                return true;
            }
        }
        false
    }

    pub fn has_skolem(&self) -> bool {
        if matches!(self.head, Atom::Skolem(_)) {
            return true;
        }
        for arg in &self.args {
            if arg.has_skolem() {
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

    // The lowest variable number this term doesn't use.
    pub fn least_unused_variable(&self) -> AtomId {
        let mut answer = match self.head {
            Atom::Variable(i) => i + 1,
            _ => 0,
        };
        for arg in &self.args {
            answer = answer.max(arg.least_unused_variable());
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
            Atom::GlobalConstant(i) => {
                weight1 += 1;
                weight2 += 4 * i as u32;
            }
            Atom::LocalConstant(i) => {
                weight1 += 1;
                weight2 += 1 + 4 * i as u32;
            }
            Atom::Monomorph(i) => {
                weight1 += 1;
                weight2 += 2 + 4 * i as u32;
            }
            Atom::Skolem(i) => {
                weight1 += 1;
                weight2 += 3 + 4 * i as u32;
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
    pub fn atom_count(&self) -> u32 {
        let mut answer = if self.head == Atom::True { 0 } else { 1 };
        for arg in &self.args {
            answer += arg.atom_count();
        }
        answer
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

    // A "reduction order" is stable under variable substitution.
    // This implements a Knuth-Bendix partial reduction ordering.
    // Returns Greater if self > other.
    // Returns Less if other > self.
    // Returns Equal if they cannot be ordered. (This is not "Equal" in the usual sense.)
    pub fn kbo_cmp(&self, other: &Term) -> Ordering {
        self.kbo_helper(other, true)
    }

    // Extends the kbo comparison to be a total ordering, so that the only equal things
    // are identical terms.
    pub fn extended_kbo_cmp(&self, other: &Term) -> Ordering {
        let kbo_cmp = self.kbo_helper(other, false);
        if kbo_cmp != Ordering::Equal {
            return kbo_cmp;
        }

        let tiebreak = self.partial_tiebreak(other);
        if tiebreak != Ordering::Equal {
            return tiebreak;
        }

        self.total_tiebreak(other)
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
            let arg_cmp = arg1.extended_kbo_cmp(arg2);
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

    pub fn replace_at_path(&self, path: &[usize], replacement: Term) -> Term {
        if path.is_empty() {
            return replacement;
        }
        let mut new_args = self.args.clone();
        new_args[path[0]] = self.args[path[0]].replace_at_path(&path[1..], replacement);
        Term {
            term_type: self.term_type,
            head_type: self.head_type,
            head: self.head.clone(),
            args: new_args,
        }
    }

    // Finds all rewritable subterms of this term, and with their paths, appends to "answer".
    // It is an error to call this on any variables.
    // Otherwise, any term is rewritable except for "true".
    fn push_rewritable_subterms<'a>(
        &'a self,
        prefix: &mut Vec<usize>,
        answer: &mut Vec<(Vec<usize>, &'a Term)>,
    ) {
        if self.is_true() {
            return;
        }
        if self.is_variable() {
            panic!("expected no variables");
        }
        for (i, arg) in self.args.iter().enumerate() {
            prefix.push(i);
            arg.push_rewritable_subterms(prefix, answer);
            prefix.pop();
        }
        answer.push((prefix.clone(), self));
    }

    pub fn rewritable_subterms(&self) -> Vec<(Vec<usize>, &Term)> {
        let mut answer = vec![];
        let mut prefix = vec![];
        self.push_rewritable_subterms(&mut prefix, &mut answer);
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

    fn inorder_helper(&self, answer: &mut Vec<(TypeId, TypeId, Atom, Vec<TypeId>)>) {
        let arg_types = self.args.iter().map(|arg| arg.term_type).collect();
        answer.push((self.term_type, self.head_type, self.head, arg_types));
        for arg in &self.args {
            arg.inorder_helper(answer);
        }
    }

    // An inorder traversal of each subterm. Returns a vector of:
    // (term type, head type, head, arg types).
    pub fn inorder(&self) -> Vec<(TypeId, TypeId, Atom, Vec<TypeId>)> {
        let mut answer = vec![];
        self.inorder_helper(&mut answer);
        answer
    }

    // var_ids tracks the order each input variable is seen.
    // Replace each var id with its index in var_ids.
    pub fn normalize_var_ids(&mut self, var_ids: &mut Vec<AtomId>) {
        if let Atom::Variable(i) = self.head {
            let pos = var_ids.iter().position(|&x| x == i);
            match pos {
                Some(j) => self.head = Atom::Variable(j as AtomId),
                None => {
                    self.head = Atom::Variable(var_ids.len() as AtomId);
                    var_ids.push(i);
                }
            }
        }
        for arg in &mut self.args {
            arg.normalize_var_ids(var_ids);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_kbo_cmp() {
        assert_eq!(
            Term::parse("c0").extended_kbo_cmp(&Term::parse("c1")),
            Ordering::Less
        );
        assert_eq!(
            Term::parse("c2").extended_kbo_cmp(&Term::parse("c0(c1)")),
            Ordering::Less
        );
        assert_eq!(
            Term::parse("x0(x1)").extended_kbo_cmp(&Term::parse("x0(c0(x0))")),
            Ordering::Less
        );
    }

    #[test]
    fn test_remap_variables() {
        let old_term = Term::parse("c2(x0, x1)");
        let var_map = vec![3, 2];
        let new_term = old_term.remap_variables(&var_map);
        assert_eq!(new_term, Term::parse("c2(x3, x2)"));
    }

    #[test]
    fn test_replace_at_path() {
        let old_term = Term::parse("c2(x0, x1)");
        let new_term = Term::parse("c0(x0)");
        let replaced = old_term.replace_at_path(&[1], new_term);
        assert_eq!(replaced, Term::parse("c2(x0, c0(x0))"));
    }
}
