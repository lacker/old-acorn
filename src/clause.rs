use std::cmp::Ordering;
use std::fmt;

use crate::atom::AtomId;
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

    pub fn len(&self) -> usize {
        self.literals.len()
    }

    pub fn has_any_variable(&self) -> bool {
        self.literals.iter().any(|x| x.has_any_variable())
    }

    pub fn has_local_constant(&self) -> bool {
        self.literals.iter().any(|x| x.has_local_constant())
    }

    pub fn num_positive_literals(&self) -> usize {
        self.literals.iter().filter(|x| x.positive).count()
    }

    // Whether it is cheap to conclude this clause from the other clause.
    // We don't want there to be extremely long chains of reasoning, each step of which it is
    // cheap to conclude from the previous one.
    pub fn extended_kbo_less_than(&self, other: &Clause) -> bool {
        if self.len() == other.len() {
            self.literals[0].extended_kbo_cmp(&other.literals[0]) == Ordering::Less
        } else {
            self.len() < other.len()
        }
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
}
