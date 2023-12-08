use std::{cmp::Ordering, fmt};

use crate::clause::Clause;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Truthiness {
    // The facts include both the normalized facts the prover was initialized with, and any
    // deduction that comes from other facts.
    // In general, facts should be true. If not, there's an inconsistency.
    Factual,

    // The basic operation of the prover is that we give it many true facts as assumptions,
    // and we also give it some negated goals, and it tries to find a contradiction.
    // Clauses that are based in part on the negated goals are thus hypothetical.
    // We hope to discover that they are actually false - that would conclude the proof.
    Hypothetical,
}

impl Truthiness {
    // Highest priority should be processed first
    fn priority(&self) -> u8 {
        match self {
            Truthiness::Factual => 2,
            Truthiness::Hypothetical => 0,
        }
    }

    // Two facts combine to form a fact.
    // Once any hypothetical is involved, the result is hypothetical.
    fn combine(&self, other: Truthiness) -> Truthiness {
        match (self, other) {
            (Truthiness::Factual, Truthiness::Factual) => Truthiness::Factual,
            _ => Truthiness::Hypothetical,
        }
    }
}

impl Ord for Truthiness {
    fn cmp(&self, other: &Truthiness) -> Ordering {
        self.priority().cmp(&other.priority())
    }
}

impl PartialOrd for Truthiness {
    fn partial_cmp(&self, other: &Truthiness) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// The rules that can generate new clauses.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Rule {
    Assumption,
    ActivatingParamodulator,
    ActivatingResolver,
    EqualityFactoring,
    EqualityResolution,
}

// A proof is made up of ProofSteps.
// Each ProofStep contains an output clause, plus a bunch of heuristic information about it, to
// decide if we should "activate" the proof step or not.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ProofStep {
    // The proof step is primarily defined by a clause that it proves.
    // Semantically, this clause is implied by the input clauses (activated and existing).
    pub clause: Clause,

    // Whether this clause is the normal sort of true, or just something we're hypothesizing for
    // the sake of the proof.
    pub truthiness: Truthiness,

    // How this clause was generated.
    pub rule: Rule,

    // The clause index in the active set that was activated to generate this clause.
    pub activated: Option<usize>,

    // The index of the already-activated clause in the active set we used, if there was any.
    pub existing: Option<usize>,

    // The clauses that we used for rewrites.
    pub rewrites: Vec<usize>,

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    // This also ignores rewrites, which may or may not be the ideal behavior.
    pub proof_size: u32,

    // Cached for simplicity
    pub atom_count: u32,

    // The order in which this ProofStep was created.
    // This is different from the order in which the ProofStep was activated.
    pub generation_ordinal: usize,
}

impl Ord for ProofStep {
    // The heuristic used to decide which clause is the most promising.
    // The passive set is a "max heap", so we want the best clause to compare as the largest.
    fn cmp(&self, other: &ProofStep) -> Ordering {
        // Do facts, then negated goal, then others
        let by_type = self.truthiness.cmp(&other.truthiness);
        if by_type != Ordering::Equal {
            return by_type;
        }

        if self.truthiness == Truthiness::Hypothetical {
            // Use the simplicity heuristic
            let by_simplicity = other.simplicity().cmp(&self.simplicity());
            if by_simplicity != Ordering::Equal {
                return by_simplicity;
            }
        }

        // Prefer clauses that were added earlier
        other.generation_ordinal.cmp(&self.generation_ordinal)
    }
}

impl PartialOrd for ProofStep {
    fn partial_cmp(&self, other: &ProofStep) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} atoms, {} proof size",
            self.atom_count, self.proof_size
        )
    }
}

impl ProofStep {
    fn new(
        clause: Clause,
        truthiness: Truthiness,
        rule: Rule,
        activated: Option<usize>,
        existing: Option<usize>,
        rewrites: Vec<usize>,
        proof_size: u32,
        generation_ordinal: usize,
    ) -> ProofStep {
        let atom_count = clause.atom_count();
        ProofStep {
            clause,
            truthiness,
            rule,
            activated,
            existing,
            rewrites,
            proof_size,
            atom_count,
            generation_ordinal,
        }
    }

    // Construct a ProofStep for one of the facts from the initial set of facts.
    pub fn new_initial_fact(clause: Clause, generation_ordinal: usize) -> ProofStep {
        ProofStep::new(
            clause,
            Truthiness::Factual,
            Rule::Assumption,
            None,
            None,
            vec![],
            0,
            generation_ordinal,
        )
    }

    // Construct a ProofStep for the negated goal that we are trying to prove.
    pub fn new_negated_goal(clause: Clause, generation_ordinal: usize) -> ProofStep {
        ProofStep::new(
            clause,
            Truthiness::Hypothetical,
            Rule::Assumption,
            None,
            None,
            vec![],
            0,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep that is a direct implication of a single activated step,
    // not requiring any other clauses.
    pub fn new_direct(
        activated_id: usize,
        activated_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness,
            rule,
            Some(activated_id),
            None,
            vec![],
            activated_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep that is a combined implication of an activated step and an existing step.
    pub fn new_combined(
        activated_id: usize,
        activated_step: &ProofStep,
        existing_id: usize,
        existing_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness.combine(existing_step.truthiness),
            rule,
            Some(activated_id),
            Some(existing_id),
            vec![],
            activated_step.proof_size + existing_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Create a replacement for this clause that has extra rewrites
    pub fn rewrite(&self, clause: Clause, new_rewrites: Vec<usize>) -> ProofStep {
        let rewrites = self
            .rewrites
            .iter()
            .chain(new_rewrites.iter())
            .cloned()
            .collect();
        ProofStep::new(
            clause,
            self.truthiness,
            self.rule,
            self.activated,
            self.existing,
            rewrites,
            self.proof_size,
            self.generation_ordinal,
        )
    }

    // Construct a ProofStep with fake heuristic data for testing
    pub fn mock(s: &str) -> ProofStep {
        let clause = Clause::parse(s);

        ProofStep::new_initial_fact(clause, 0)
    }

    // A heuristic for how simple this clause is.
    // The lower the simplicity, the more likely we are to select it.
    fn simplicity(&self) -> u32 {
        self.atom_count + self.proof_size
    }

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> impl Iterator<Item = &usize> {
        self.activated
            .iter()
            .chain(self.existing.iter())
            .chain(self.rewrites.iter())
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // Whether this step is just the direct normalization of the negated goal
    pub fn is_negated_goal(&self) -> bool {
        self.rule == Rule::Assumption && self.truthiness != Truthiness::Factual
    }

    // A heuristic for whether this clause is so bad, it should be rejected immediately.
    pub fn heuristic_reject(&self) -> bool {
        self.truthiness == Truthiness::Factual && self.proof_size > 2
    }
}
