use std::fmt;

use crate::atom::{Atom, AtomId};
use crate::literal::Literal;

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
                write!(f, " or ")?;
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

        // Normalize the variable ids
        let mut var_ids = vec![];
        for literal in &mut literals {
            literal.left.normalize_var_ids(&mut var_ids);
            literal.right.normalize_var_ids(&mut var_ids);
        }
        Clause { literals }
    }

    // An unsatisfiable clause. Like a lone "false".
    pub fn impossible() -> Clause {
        Clause::new(vec![])
    }

    pub fn parse(s: &str) -> Clause {
        Clause::new(
            s.split(" or ")
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

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    pub fn has_skolem(&self) -> bool {
        self.literals.iter().any(|x| x.has_skolem())
    }

    pub fn has_local_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_local_constant())
    }

    pub fn num_positive_literals(&self) -> usize {
        self.literals.iter().filter(|x| x.positive).count()
    }

    // Whether every literal in this clause is exactly contained by the other clause.
    pub fn contains(&self, other: &Clause) -> bool {
        for literal in &other.literals {
            if !self.literals.iter().any(|x| x == literal) {
                return false;
            }
        }
        true
    }

    // Whether any top level term has the given atom as its head.
    pub fn has_head(&self, atom: &Atom) -> bool {
        self.literals.iter().any(|x| x.has_head(atom))
    }

    // Whether we are willing to turn this clause into a line of code in a proof.
    pub fn is_printable(&self) -> bool {
        if self.len() > 1 {
            return false;
        }
        if self.has_skolem() {
            return false;
        }
        true
    }
}
