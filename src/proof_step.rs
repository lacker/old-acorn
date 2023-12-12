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
    pub fn combine(&self, other: Truthiness) -> Truthiness {
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

// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Rule {
    Assumption,

    // (paramodulator, resolver)
    Superposition(usize, usize),

    // The equality rules only have one source clause
    EqualityFactoring(usize),
    EqualityResolution(usize),
}

impl Rule {
    // The ids of the clauses that this rule depends on.
    fn dependencies(&self) -> impl Iterator<Item = &usize> {
        match self {
            Rule::Assumption => vec![].into_iter(),
            Rule::Superposition(paramodulator, resolver) => {
                vec![paramodulator, resolver].into_iter()
            }
            Rule::EqualityFactoring(rewritten) => vec![rewritten].into_iter(),
            Rule::EqualityResolution(rewritten) => vec![rewritten].into_iter(),
        }
    }

    // (description, id) for every clause this rule depends on.
    pub fn descriptive_dependencies(&self) -> Vec<(String, usize)> {
        let mut answer = vec![];
        match self {
            Rule::Assumption => {}
            Rule::Superposition(paramodulator, resolver) => {
                answer.push(("paramodulator".to_string(), *paramodulator));
                answer.push(("resolver".to_string(), *resolver));
            }
            Rule::EqualityFactoring(source) => {
                answer.push(("source".to_string(), *source));
            }
            Rule::EqualityResolution(source) => {
                answer.push(("source".to_string(), *source));
            }
        }
        answer
    }
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

    // The clauses that we used for rewrites.
    pub rewrites: Vec<usize>,

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    // This also ignores rewrites, which may or may not be the ideal behavior.
    proof_size: u32,

    // Cached for simplicity
    atom_count: u32,

    // The order in which this ProofStep was created.
    // This is different from the order in which the ProofStep was activated.
    generation_ordinal: usize,
}

impl Ord for ProofStep {
    // The heuristic used to decide which clause is the most promising.
    // The passive set is a "max heap", so we want the best clause to compare as the largest.
    fn cmp(&self, other: &ProofStep) -> Ordering {
        self.heuristic_score().cmp(&other.heuristic_score())
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
        rewrites: Vec<usize>,
        proof_size: u32,
        generation_ordinal: usize,
    ) -> ProofStep {
        let atom_count = clause.atom_count();
        ProofStep {
            clause,
            truthiness,
            rule,
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
            vec![],
            0,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep that is a direct implication of a single activated step,
    // not requiring any other clauses.
    pub fn new_direct(
        activated_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness,
            rule,
            vec![],
            activated_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Construct a new ProofStep that is a combined implication of an activated step and an existing step.
    pub fn new_combined(
        activated_step: &ProofStep,
        existing_step: &ProofStep,
        rule: Rule,
        clause: Clause,
        generation_ordinal: usize,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            activated_step.truthiness.combine(existing_step.truthiness),
            rule,
            vec![],
            activated_step.proof_size + existing_step.proof_size + 1,
            generation_ordinal,
        )
    }

    // Create a replacement for this clause that has extra rewrites
    pub fn rewrite(
        &self,
        clause: Clause,
        new_rewrites: Vec<usize>,
        new_truthiness: Truthiness,
    ) -> ProofStep {
        let rewrites = self
            .rewrites
            .iter()
            .chain(new_rewrites.iter())
            .cloned()
            .collect();
        ProofStep::new(
            clause,
            new_truthiness,
            self.rule,
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

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> impl Iterator<Item = &usize> {
        self.rule.dependencies().chain(self.rewrites.iter())
    }

    // (description, id) for every clause this rule depends on.
    pub fn descriptive_dependencies(&self) -> Vec<(String, usize)> {
        let mut answer = self.rule.descriptive_dependencies();
        for rewrite in &self.rewrites {
            answer.push(("rewrite".to_string(), *rewrite));
        }
        answer
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // Whether this step is just the direct normalization of the negated goal
    pub fn is_negated_goal(&self) -> bool {
        self.rule == Rule::Assumption && self.truthiness != Truthiness::Factual
    }

    // The better the score, the more we want to activate this proof step.
    pub fn heuristic_score(&self) -> i32 {
        let base_score = match self.truthiness {
            Truthiness::Hypothetical => -1 * (self.atom_count + self.proof_size) as i32,
            Truthiness::Factual => 1,
        };

        if false {
            // This is an alternate heuristic.
            // Unit tests should pass with any heuristic.
            // We need some way to debug differences on our regular codebase.
            if self.rule == Rule::Assumption {
                // We don't want to skip assumptions
                base_score + 100 + self.generation_ordinal as i32
            } else {
                base_score
            }
        } else {
            // Use fifo as a tiebreaker
            1000000 * base_score - self.generation_ordinal as i32
        }
    }

    // A heuristic for whether this clause is so bad, it should be rejected immediately.
    pub fn heuristic_reject(&self) -> bool {
        self.truthiness == Truthiness::Factual && self.proof_size > 2
    }
}
