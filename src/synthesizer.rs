use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::term::{Clause, Literal, Term};
use crate::type_space::{TypeId, BOOL};

pub struct Synthesizer {
    // Map of var_type to the "var_type -> bool" type, for each argument we want to synthesize
    types: HashMap<TypeId, TypeId>,

    // The next synthetic proposition id to use
    next_id: AtomId,

    // Stores all (literal, free var id) pairs we've already synthesized
    history: HashMap<Literal, Vec<AtomId>>,
}

impl Synthesizer {
    pub fn new() -> Synthesizer {
        Synthesizer {
            types: HashMap::new(),
            next_id: 0,
            history: HashMap::new(),
        }
    }

    // Adds entries to types for any higher-order variables that are observed.
    pub fn observe(&mut self, clause: &Clause) {
        for lit in &clause.literals {
            if lit.is_boolean() && lit.is_higher_order() {
                let term = &lit.left;
                if term.args.len() != 1 {
                    // For now we only synthesize propositions with a single argument
                    continue;
                }
                let var_type = term.args[0].term_type;
                let prop_type = term.head_type;
                if !self.types.contains_key(&var_type) {
                    self.types.insert(var_type, prop_type);
                }
            }
        }
    }

    // Synthesize some new functions that provide alternative ways of writing the given clause.
    pub fn synthesize(&mut self, clause: &Clause) -> Vec<Clause> {
        let mut answer = Vec::new();
        if clause.literals.len() > 1 {
            // For now we only synthesize clauses with a single literal
            return answer;
        }
        let literal = &clause.literals[0];
        if literal.has_synthetic() {
            // For now we only synthesize clauses with no synthetic atoms
            return answer;
        }

        for (var_type, prop_type) in &self.types {
            let mut atoms = literal.left.atoms_for_type(*var_type);
            atoms.extend(literal.right.atoms_for_type(*var_type));
            atoms.sort();
            atoms.dedup();

            for atom in atoms {
                // For each atom, one way to abstract this literal is by replacing that atom with
                // a free variable. Do the replacement, tracking the free variable id.
                let (var_id, abstract_literal) = match atom {
                    Atom::Variable(id) => {
                        // No replacement is needed, just use the existing variable
                        (id, literal.clone())
                    }
                    atom => {
                        // Create a new variable to replace the atom
                        let var_id = clause.num_quantifiers();
                        (var_id, literal.replace_atom(&atom, &Atom::Variable(var_id)))
                    }
                };

                // Skip synthesizing if we already synthesized an equivalent function
                if let Some(ids) = self.history.get(&abstract_literal) {
                    if ids.contains(&var_id) {
                        continue;
                    }
                }
                self.history
                    .entry(abstract_literal.clone())
                    .or_insert(Vec::new())
                    .push(var_id);
                self.history
                    .entry(abstract_literal.negate())
                    .or_insert(Vec::new())
                    .push(var_id);

                // Synthesize an atom like "p1" for the new var_type -> bool function
                let first_prop_atom = Atom::Synthetic(self.next_id);
                self.next_id += 1;

                // The free variable in our "definition", something like "x3"
                let var_term = Term {
                    term_type: *var_type,
                    head_type: *var_type,
                    head: Atom::Variable(var_id),
                    args: vec![],
                };

                // p1(x3)
                let first_prop_term = Term {
                    term_type: BOOL,
                    head_type: *prop_type,
                    head: first_prop_atom,
                    args: vec![var_term.clone()],
                };

                // We want to define:
                //   p1(x3) <-> abstract_literal
                // We can do this with two clauses.
                //   p1(x3) | !abstract_literal
                //   !p1(x3) | abstract_literal
                println!("defining {} <-> {}", first_prop_term, abstract_literal);
                answer.push(Clause::new(vec![
                    Literal::positive(first_prop_term.clone()),
                    abstract_literal.negate(),
                ]));
                answer.push(Clause::new(vec![
                    Literal::negative(first_prop_term.clone()),
                    abstract_literal,
                ]));

                // Now we want to define p2 = !p1
                let second_prop_atom = Atom::Synthetic(self.next_id);
                self.next_id += 1;

                // p2(x3)
                let second_prop_term = Term {
                    term_type: BOOL,
                    head_type: *prop_type,
                    head: second_prop_atom,
                    args: vec![var_term],
                };

                // We want to define:
                //   p2(x3) <-> !p1(x3)
                // We can do this with two clauses.
                //   !p2(x3) | !p1(x3)
                //   p2(x3) | p1(x3)
                answer.push(Clause::new(vec![
                    Literal::negative(second_prop_term.clone()),
                    Literal::negative(first_prop_term.clone()),
                ]));
                answer.push(Clause::new(vec![
                    Literal::positive(second_prop_term),
                    Literal::positive(first_prop_term),
                ]));
            }
        }

        answer
    }
}

#[cfg(test)]
mod tests {
    use crate::environment::Environment;
    use crate::normalizer::Normalizer;

    use super::*;

    #[test]
    fn test_synthesis() {
        let mut env = Environment::new();
        let mut norm = Normalizer::new();
        let mut synth = Synthesizer::new();

        env.add("type Thing: axiom");
        env.add("define t: Thing = axiom");
        env.add("axiom t_implies_all(q: Thing -> bool): q(t) -> forall(x: Thing, q(x))");
        env.add("theorem goal(x: Thing): x = t");

        let clauses = norm.normalize(env.get_value("t_implies_all").unwrap().clone());
        for clause in &clauses {
            synth.observe(clause);
        }

        let neg_goal_clauses = norm.normalize(env.get_value("goal").unwrap().clone().negate());
        assert_eq!(neg_goal_clauses.len(), 1);
        let synthesized = synth.synthesize(&neg_goal_clauses[0]);
        assert_eq!(synthesized.len(), 8);
        for clause in synthesized {
            norm.typespace.check_clause(&clause);
        }

        // Check that we won't re-synthesize
        let synthesized_again = synth.synthesize(&neg_goal_clauses[0]);
        assert_eq!(synthesized_again.len(), 0);
    }
}
