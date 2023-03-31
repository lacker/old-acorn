use crate::term::Clause;

// The ActiveSet stores rich data for a bunch of terms.
// Within the ActiveSet, term data is perfectly shared, so that
// we can check term equality cheaply, and cheaply augment terms with
// additional data as needed.
pub struct ActiveSet {
    clauses: Vec<Clause>,
}

impl ActiveSet {
    pub fn new() -> ActiveSet {
        ActiveSet { clauses: vec![] }
    }

    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        ActiveSet::new();
    }
}
