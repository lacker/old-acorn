use std::fmt;

use crate::atom::Atom;
use crate::clause::Clause;
use crate::environment::Environment;
use crate::normalizer::Normalizer;
use crate::term::{Literal, Term};

struct DisplayAtom<'a> {
    atom: Atom,
    env: &'a Environment,
    normalizer: &'a Normalizer,
}

impl fmt::Display for DisplayAtom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.atom {
            Atom::True => write!(f, "true"),
            Atom::Constant(i) => write!(f, "{}", self.env.get_constant_name(i)),
            Atom::Skolem(i) => write!(f, "s{}", i),
            Atom::Synthetic(i) => write!(f, "p{}", i),
            Atom::Variable(i) => write!(f, "x{}", i),
            Atom::Anonymous => write!(f, "_"),
        }
    }
}

pub struct DisplayTerm<'a> {
    term: &'a Term,
    env: &'a Environment,
    normalizer: &'a Normalizer,
}

impl fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            DisplayAtom {
                atom: self.term.head,
                env: self.env,
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
                        env: self.env,
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
    env: &'a Environment,
    normalizer: &'a Normalizer,
}

impl DisplayLiteral<'_> {
    fn term<'a>(&'a self, term: &'a Term) -> DisplayTerm {
        DisplayTerm {
            term,
            env: self.env,
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
                write!(f, "!{}", self.term(&self.literal.left),)
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
    pub env: &'a Environment,
    pub normalizer: &'a Normalizer,
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
                    env: self.env,
                    normalizer: self.normalizer
                }
            )?;
        }
        Ok(())
    }
}
