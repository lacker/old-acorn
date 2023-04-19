use std::fmt;

use crate::atom::Atom;
use crate::environment::Environment;
use crate::term::{Clause, Literal, Term};

pub struct DisplayAtom<'a> {
    atom: Atom,
    env: &'a Environment,
}

impl fmt::Display for DisplayAtom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.atom {
            Atom::True => write!(f, "true"),
            Atom::Axiomatic(i) => write!(f, "{}", self.env.get_axiomatic_name(i)),
            Atom::Skolem(i) => write!(f, "s{}", i),
            Atom::Synthetic(i) => write!(f, "p{}", i),
            Atom::Variable(i) => write!(f, "x{}", i),
        }
    }
}

pub struct DisplayTerm<'a> {
    term: &'a Term,
    env: &'a Environment,
}

impl fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            DisplayAtom {
                atom: self.term.head,
                env: self.env
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
                        env: self.env
                    }
                )?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

pub struct DisplayLiteral<'a> {
    literal: &'a Literal,
    env: &'a Environment,
}

impl fmt::Display for DisplayLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literal.positive {
            if self.literal.is_boolean() {
                write!(
                    f,
                    "{}",
                    DisplayTerm {
                        term: &self.literal.left,
                        env: self.env
                    }
                )
            } else {
                write!(
                    f,
                    "{} = {}",
                    DisplayTerm {
                        term: &self.literal.left,
                        env: self.env
                    },
                    DisplayTerm {
                        term: &self.literal.right,
                        env: self.env
                    }
                )
            }
        } else {
            if self.literal.is_boolean() {
                write!(
                    f,
                    "!{}",
                    DisplayTerm {
                        term: &self.literal.left,
                        env: self.env
                    }
                )
            } else {
                write!(
                    f,
                    "{} != {}",
                    DisplayTerm {
                        term: &self.literal.left,
                        env: self.env
                    },
                    DisplayTerm {
                        term: &self.literal.right,
                        env: self.env
                    }
                )
            }
        }
    }
}

pub struct DisplayClause<'a> {
    pub clause: &'a Clause,
    pub env: &'a Environment,
}

impl fmt::Display for DisplayClause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.clause.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.clause.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(
                f,
                "{}",
                DisplayLiteral {
                    literal,
                    env: self.env
                }
            )?;
        }
        Ok(())
    }
}
