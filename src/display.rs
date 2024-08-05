use std::fmt;

use crate::atom::Atom;
use crate::clause::Clause;
use crate::literal::Literal;
use crate::normalizer::Normalizer;
use crate::term::Term;

struct DisplayAtom<'a> {
    atom: Atom,
    normalizer: &'a Normalizer,
}

impl fmt::Display for DisplayAtom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.normalizer.atom_str(&self.atom))
    }
}

pub struct DisplayTerm<'a> {
    pub term: &'a Term,
    pub normalizer: &'a Normalizer,
}

impl fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            DisplayAtom {
                atom: self.term.head,
                normalizer: self.normalizer
            }
        )?;
        if self.term.args.len() > 0 {
            write!(f, "(")?;
            for (i, arg) in self.term.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(
                    f,
                    "{}",
                    DisplayTerm {
                        term: arg,
                        normalizer: self.normalizer
                    }
                )?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

struct DisplayLiteral<'a> {
    literal: &'a Literal,
    normalizer: &'a Normalizer,
}

impl DisplayLiteral<'_> {
    fn term<'a>(&'a self, term: &'a Term) -> DisplayTerm {
        DisplayTerm {
            term,
            normalizer: self.normalizer,
        }
    }
}

impl fmt::Display for DisplayLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literal.positive {
            if self.literal.is_boolean() {
                write!(f, "{}", self.term(&self.literal.left))
            } else {
                write!(
                    f,
                    "{} = {}",
                    self.term(&self.literal.left),
                    self.term(&self.literal.right)
                )
            }
        } else {
            if self.literal.is_boolean() {
                write!(f, "not {}", self.term(&self.literal.left),)
            } else {
                write!(
                    f,
                    "{} != {}",
                    self.term(&self.literal.left),
                    self.term(&self.literal.right),
                )
            }
        }
    }
}

pub struct DisplayClause<'a> {
    pub clause: &'a Clause,
    pub normalizer: &'a Normalizer,
}

impl fmt::Display for DisplayClause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.clause.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.clause.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " or ")?;
            }
            write!(
                f,
                "{}",
                DisplayLiteral {
                    literal,
                    normalizer: self.normalizer
                }
            )?;
        }
        Ok(())
    }
}
