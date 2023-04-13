use std::collections::HashMap;

use crate::atom::{Atom, AtomId};
use crate::term::{Clause, Term};
use crate::type_space::{TypeId, BOOL};

pub struct Synthesizer {
    // Map of var_type to a list of templates
    templates: HashMap<TypeId, Vec<Template>>,

    // The next synthetic proposition id to use
    next_id: AtomId,
}

struct Template {
    // The type of the free variable in the synthesized proposition.
    var_type: TypeId,

    // The type of the synthesized proposition variable itself.
    // Represents a function from var_type to bool.
    prop_type: TypeId,

    // The id of the free variable in the template that we will replace with our
    // synthesized proposition.
    prop_id: AtomId,

    // The clause that we will use as a template for synthesis.
    clause: Clause,
}

impl Synthesizer {
    pub fn new() -> Synthesizer {
        Synthesizer {
            templates: HashMap::new(),
            next_id: 0,
        }
    }

    // Whether this clause can be expanded with synthesized propositions.
    pub fn is_template(clause: &Clause) -> bool {
        clause
            .literals
            .iter()
            .any(|lit| lit.is_boolean() && lit.is_higher_order())
    }

    pub fn add_template(&mut self, clause: Clause) {
        for lit in &clause.literals {
            if lit.is_boolean() && lit.is_higher_order() {
                let term = &lit.left;
                if term.args.len() != 1 {
                    // For now we only synthesize propositions with a single argument
                    continue;
                }
                let var_type = term.args[0].term_type;
                let prop_type = term.head_type;
                let prop_id = match term.head {
                    Atom::Variable(id) => id,
                    _ => continue,
                };
                let template = Template {
                    var_type,
                    prop_type,
                    prop_id,
                    clause,
                };
                self.templates
                    .entry(var_type)
                    .or_insert_with(Vec::new)
                    .push(template);
                return;
            }
        }
        panic!("clause could not be added as a template: {}", clause);
    }

    pub fn synthesize(&mut self, clause: &Clause) -> Vec<Clause> {
        let mut answer = Vec::new();
        if clause.literals.len() > 1 {
            // For now we only synthesize clauses with a single literal
            return answer;
        }
        let literal = &clause.literals[0];

        for (var_type, templates) in &self.templates {
            let mut atoms = literal.left.atoms_for_type(*var_type);
            atoms.extend(literal.right.atoms_for_type(*var_type));
            atoms.sort();
            atoms.dedup();

            for atom in atoms {
                // For each atom, one way to abstract this literal is by replacing that atom with
                // a free variable. Do the replacement, tracking the free variable id.
                let (var_id, abstract_left, abstract_right) = match atom {
                    Atom::Variable(id) => {
                        // No replacement is needed, just use the existing variable
                        (id, literal.left.clone(), literal.right.clone())
                    }
                    atom => {
                        // Create a new variable to replace the atom
                        let var_id = clause.num_quantifiers();
                        let var_term = Term {
                            term_type: *var_type,
                            head_type: *var_type,
                            head: Atom::Variable(var_id),
                            args: vec![],
                        };
                        (
                            var_id,
                            literal.left.replace_atom(&atom, &var_term),
                            literal.right.replace_atom(&atom, &var_term),
                        )
                    }
                };

                // TODO: skip synthesizing if we already did this one

                let prop_atom = Atom::Synthetic(self.next_id);
                self.next_id += 1;
                let var_term = Term {
                    term_type: *var_type,
                    head_type: *var_type,
                    head: Atom::Variable(var_id),
                    args: vec![],
                };

                for template in templates {
                    let prop_term = Term {
                        term_type: BOOL,
                        head_type: template.prop_type,
                        head: prop_atom,
                        args: vec![var_term],
                    };

                    todo!("synthesize");
                }
            }
        }

        answer
    }
}
