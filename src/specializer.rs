use crate::atom::{Atom, AtomId};
use crate::term::Term;
use crate::type_space::TypeId;

// A Specializer finds substitutions that specialize, to turn a more general term
// into a more specific one.
pub struct Specializer {
    map: Vec<Option<Term>>,
}

impl Specializer {
    pub fn new() -> Specializer {
        Specializer { map: Vec::new() }
    }

    fn match_var(&mut self, var_id: AtomId, special_term: &Term) -> bool {
        let var_id = var_id as usize;
        if var_id >= self.map.len() {
            self.map.resize(var_id + 1, None);
        }
        match &self.map[var_id] {
            None => {
                self.map[var_id] = Some(special_term.clone());
                true
            }
            Some(general_term) => general_term == special_term,
        }
    }

    fn match_atoms(&mut self, atom_type: TypeId, general: &Atom, special: &Atom) -> bool {
        if let Atom::Variable(i) = general {
            self.match_var(*i, &Term::atom(atom_type, *special))
        } else {
            general == special
        }
    }

    pub fn match_terms(&mut self, general: &Term, special: &Term) -> bool {
        if general.term_type != special.term_type {
            return false;
        }

        // Handle the case where a general variable is specializing to the whole term
        if let Some(i) = general.atomic_variable() {
            return self.match_var(i, special);
        }

        // These checks mean we won't catch higher-order functions whose head types don't match.
        if general.head_type != special.head_type {
            return false;
        }
        if general.args.len() != special.args.len() {
            return false;
        }

        if !self.match_atoms(general.head_type, &general.head, &special.head) {
            return false;
        }

        for (g, s) in general.args.iter().zip(special.args.iter()) {
            if !self.match_terms(g, s) {
                return false;
            }
        }
        true
    }
}
