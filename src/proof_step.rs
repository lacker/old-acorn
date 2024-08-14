use std::cmp::Ordering;
use std::fmt;

use crate::clause::Clause;
use crate::literal::Literal;
use crate::proposition::{Source, SourceType};
use crate::term::Term;

// Use this to toggle experimental algorithm mode
pub const EXPERIMENT: bool = false;

// The different sorts of proof steps.
#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub enum ProofStepId {
    // A proof step that was activated and exists in the active set.
    Active(usize),

    // A proof step that was never activated, but was used to find a contradiction.
    Passive(u32),

    // The final step of a proof.
    // No active id because it never gets inserted into the active set.
    Final,
}

impl ProofStepId {
    pub fn active_id(&self) -> Option<usize> {
        match self {
            ProofStepId::Active(id) => Some(*id),
            _ => None,
        }
    }
}

// The "truthiness" categorizes the different types of true statements, relative to a proof.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Truthiness {
    // A "factual" truth is true globally, regardless of this particular proof.
    Factual,

    // A "hypothetical" truth is something that we are assuming true in the context of this proof.
    // For example, we might assume that a and b are nonzero, and then prove that a * b != 0.
    Hypothetical,

    // When we want to prove a goal G, we tell the prover that !G is true, and search
    // for contradictions.
    // A "counterfactual" truth is this negated goal, or something derived from it, that we expect
    // to lead to a contradiction.
    Counterfactual,
}

impl Truthiness {
    // When combining truthinesses, the result is the "most untruthy" of the two.
    pub fn combine(&self, other: Truthiness) -> Truthiness {
        match (self, other) {
            (Truthiness::Counterfactual, _) => Truthiness::Counterfactual,
            (_, Truthiness::Counterfactual) => Truthiness::Counterfactual,
            (Truthiness::Hypothetical, _) => Truthiness::Hypothetical,
            (_, Truthiness::Hypothetical) => Truthiness::Hypothetical,
            (Truthiness::Factual, Truthiness::Factual) => Truthiness::Factual,
        }
    }
}

// Information about a resolution inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolutionInfo {
    // Which clauses were used as the sources.
    // The short clause must have only one literal.
    pub short_id: usize,

    // The long clause will usually have more than one literal. It can have just one literal
    // if we're finding a contradiction.
    pub long_id: usize,
}

// Information about a rewrite inference.
// Rewrites have two parts, the "pattern" that determines what gets rewritten into what,
// and the "target" which contains the subterm that gets rewritten.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteInfo {
    // Which clauses were used as the sources.
    pub pattern_id: usize,
    pub target_id: usize,

    // The truthiness of the source clauses.
    pattern_truthiness: Truthiness,
    target_truthiness: Truthiness,
}

// Always a contradiction, found by rewriting one side of an inequality into the other.
#[derive(Debug, PartialEq, Eq)]
pub struct MultipleRewriteInfo {
    pub inequality_id: usize,
    pub active_ids: Vec<usize>,
    pub passive_ids: Vec<u32>,
}

// The rules that can generate new clauses, along with the clause ids used to generate.
#[derive(Debug, PartialEq, Eq)]
pub enum Rule {
    Assumption(Source),

    // Rules based on multiple source clauses
    Resolution(ResolutionInfo),
    Rewrite(RewriteInfo),

    // Rules with only one source clause
    EqualityFactoring(usize),
    EqualityResolution(usize),
    FunctionElimination(usize),
    Specialization(usize),

    // A contradiction found by repeatedly rewriting identical terms.
    MultipleRewrite(MultipleRewriteInfo),
}

impl Rule {
    // The ids of the clauses that this rule directly depends on.
    fn premises(&self) -> Vec<ProofStepId> {
        match self {
            Rule::Assumption(_) => vec![],
            Rule::Resolution(info) => vec![
                ProofStepId::Active(info.short_id),
                ProofStepId::Active(info.long_id),
            ],
            Rule::Rewrite(info) => vec![
                ProofStepId::Active(info.pattern_id),
                ProofStepId::Active(info.target_id),
            ],
            Rule::EqualityFactoring(rewritten)
            | Rule::EqualityResolution(rewritten)
            | Rule::FunctionElimination(rewritten)
            | Rule::Specialization(rewritten) => vec![ProofStepId::Active(*rewritten)],
            Rule::MultipleRewrite(multi_rewrite_info) => {
                let mut answer = vec![ProofStepId::Active(multi_rewrite_info.inequality_id)];
                for id in &multi_rewrite_info.active_ids {
                    answer.push(ProofStepId::Active(*id));
                }
                for id in &multi_rewrite_info.passive_ids {
                    answer.push(ProofStepId::Passive(*id));
                }
                answer
            }
        }
    }

    // Human-readable.
    pub fn name(&self) -> &str {
        match self {
            Rule::Assumption(_) => "Assumption",
            Rule::Resolution(_) => "Resolution",
            Rule::Rewrite(_) => "Rewrite",
            Rule::EqualityFactoring(_) => "Equality Factoring",
            Rule::EqualityResolution(_) => "Equality Resolution",
            Rule::FunctionElimination(_) => "Function Elimination",
            Rule::Specialization(_) => "Specialization",
            Rule::MultipleRewrite(..) => "Multiple Rewrite",
        }
    }

    pub fn is_rewrite(&self) -> bool {
        match self {
            Rule::Rewrite(_) => true,
            _ => false,
        }
    }

    pub fn is_assumption(&self) -> bool {
        match self {
            Rule::Assumption(_) => true,
            _ => false,
        }
    }

    pub fn is_negated_goal(&self) -> bool {
        match self {
            Rule::Assumption(source) => matches!(source.source_type, SourceType::NegatedGoal),
            _ => false,
        }
    }
}

// A proof is made up of ProofSteps.
// Each ProofStep contains an output clause, plus a bunch of information we track about it.
#[derive(Debug, Eq, PartialEq)]
pub struct ProofStep {
    // The proof step is primarily defined by a clause that it proves.
    // Semantically, this clause is implied by the input clauses (activated and existing).
    pub clause: Clause,

    // Whether this clause is the normal sort of true, or just something we're hypothesizing for
    // the sake of the proof.
    pub truthiness: Truthiness,

    // How this clause was generated.
    pub rule: Rule,

    // Clauses that we used for additional simplification.
    pub simplification_rules: Vec<usize>,

    // The number of proof steps that this proof step depends on.
    // The size includes this proof step itself, but does not count assumptions and definitions.
    // So the size for any assumption or definition is zero.
    // This does not deduplicate among different branches, so it may be an overestimate.
    pub proof_size: u32,

    // The dependency depth is the largest depth of any dependency.
    pub dependency_depth: u32,

    // Some proof steps are categorized as "basic".
    // In a user-written proof, these can be assumed without being explicitly stated.
    // In the prover, we can use them to prove other things without increasing the depth.
    pub basic: bool,
}

impl fmt::Display for ProofStep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ; rule = {:?}", self.clause, self.rule)
    }
}

impl ProofStep {
    fn new(
        clause: Clause,
        truthiness: Truthiness,
        rule: Rule,
        simplification_rules: Vec<usize>,
        proof_size: u32,
        dependency_depth: u32,
        basic: bool,
    ) -> ProofStep {
        ProofStep {
            clause,
            truthiness,
            rule,
            simplification_rules,
            proof_size,
            dependency_depth,
            basic,
        }
    }
    // If this proof step is basic, its depth is the same as its dependency depth.
    // If this proof step is not basic, its depth is one more than its dependency depth.
    pub fn depth(&self) -> u32 {
        if self.basic {
            self.dependency_depth
        } else {
            self.dependency_depth + 1
        }
    }

    // Construct a new assumption ProofStep that is not dependent on any other steps.
    // Assumptions are always basic, but as we add more theorems we will have to revisit that.
    pub fn new_assumption(clause: Clause, truthiness: Truthiness, source: &Source) -> ProofStep {
        let rule = Rule::Assumption(source.clone());
        ProofStep::new(clause, truthiness, rule, vec![], 0, 0, true)
    }

    // Construct a new ProofStep that is a direct implication of a single activated step,
    // not requiring any other clauses.
    pub fn new_direct(activated_step: &ProofStep, rule: Rule, clause: Clause) -> ProofStep {
        let basic = activated_step.proof_size == 0
            || activated_step.rule.is_negated_goal()
            || activated_step.clause.len() == 1
            || clause.len() > 1;
        ProofStep::new(
            clause,
            activated_step.truthiness,
            rule,
            vec![],
            activated_step.proof_size + 1,
            activated_step.depth(),
            basic,
        )
    }

    // Construct a ProofStep that is a specialization of a general pattern.
    pub fn new_specialization(
        general_id: usize,
        general_step: &ProofStep,
        clause: Clause,
    ) -> ProofStep {
        ProofStep::new(
            clause,
            general_step.truthiness,
            Rule::Specialization(general_id),
            vec![],
            general_step.proof_size + 1,
            general_step.depth(),
            false,
        )
    }

    // Construct a new ProofStep via resolution.
    pub fn new_resolution(
        short_id: usize,
        short_step: &ProofStep,
        long_id: usize,
        long_step: &ProofStep,
        clause: Clause,
    ) -> ProofStep {
        let rule = Rule::Resolution(ResolutionInfo { short_id, long_id });

        let truthiness = short_step.truthiness.combine(long_step.truthiness);

        // We need to ensure that a single theorem application is basic, even if it
        // requires multiple steps of resolution.
        // This is still hacky due to the normalization process. A theorem application
        // that looks like a single step to the user may require multiple steps of resolution.
        let basic = short_step.rule.is_negated_goal()
            || long_step.rule.is_negated_goal()
            || clause.len() != 1
            || (long_step.rule.is_assumption()
                && clause.has_skolem()
                && !clause.has_any_variable()
                && !short_step.clause.has_skolem());
        let dependency_depth = std::cmp::max(short_step.depth(), long_step.depth());

        ProofStep::new(
            clause,
            truthiness,
            rule,
            vec![],
            short_step.proof_size + long_step.proof_size + 1,
            dependency_depth,
            basic,
        )
    }

    // Construct a new ProofStep via rewriting.
    // We are replacing a subterm of the target literal with a new subterm.
    pub fn new_rewrite(
        pattern_id: usize,
        pattern_step: &ProofStep,
        target_id: usize,
        target_step: &ProofStep,
        target_left: bool,
        path: &[usize],
        new_subterm: &Term,
    ) -> ProofStep {
        assert_eq!(target_step.clause.literals.len(), 1);
        let target_literal = &target_step.clause.literals[0];
        let (u, v) = if target_left {
            (&target_literal.left, &target_literal.right)
        } else {
            (&target_literal.right, &target_literal.left)
        };
        let new_u = u.replace_at_path(path, new_subterm.clone());
        let new_literal = Literal::new(target_literal.positive, new_u, v.clone());
        let basic = new_literal.extended_kbo_cmp(&target_literal) == Ordering::Less;
        let clause = Clause::new(vec![new_literal]);

        let rule = Rule::Rewrite(RewriteInfo {
            pattern_id,
            target_id,
            pattern_truthiness: pattern_step.truthiness,
            target_truthiness: target_step.truthiness,
        });

        let dependency_depth = std::cmp::max(pattern_step.depth(), target_step.depth());

        ProofStep::new(
            clause,
            pattern_step.truthiness.combine(target_step.truthiness),
            rule,
            vec![],
            pattern_step.proof_size + target_step.proof_size + 1,
            dependency_depth,
            basic,
        )
    }

    // A proof step for finding a contradiction via a series of rewrites.
    pub fn new_multiple_rewrite(
        inequality_id: usize,
        active_ids: Vec<usize>,
        passive_ids: Vec<u32>,
        truthiness: Truthiness,
        dependency_depth: u32,
    ) -> ProofStep {
        let rule = Rule::MultipleRewrite(MultipleRewriteInfo {
            inequality_id,
            active_ids,
            passive_ids,
        });

        // Multiple rewrites are always basic themselves because they lead to contradictions.
        // It's the specializations that may require explicit steps.
        ProofStep::new(
            Clause::impossible(),
            truthiness,
            rule,
            vec![],
            0,
            dependency_depth,
            true,
        )
    }

    // Create a replacement for this clause that has extra simplification rules.
    // We could probably handle basicness better if we had access to all of the source clauses.
    pub fn new_simplified(
        self,
        new_clause: Clause,
        new_rules: Vec<usize>,
        new_truthiness: Truthiness,
    ) -> ProofStep {
        let rules = self
            .simplification_rules
            .iter()
            .chain(new_rules.iter())
            .cloned()
            .collect();
        let new_basic = self.proof_size == 0 || new_clause.len() != 1;
        ProofStep::new(
            new_clause,
            new_truthiness,
            self.rule,
            rules,
            self.proof_size,
            self.dependency_depth,
            new_basic,
        )
    }

    // Construct a ProofStep with fake heuristic data for testing
    pub fn mock(s: &str) -> ProofStep {
        let clause = Clause::parse(s);
        ProofStep::new(
            clause,
            Truthiness::Factual,
            Rule::Assumption(Source::mock()),
            vec![],
            0,
            0,
            true,
        )
    }

    // The ids of the other clauses that this clause depends on.
    pub fn dependencies(&self) -> Vec<ProofStepId> {
        let mut answer = self.rule.premises();
        for rule in &self.simplification_rules {
            answer.push(ProofStepId::Active(*rule));
        }
        answer
    }

    pub fn active_dependencies(&self) -> Vec<usize> {
        self.dependencies()
            .iter()
            .filter_map(|id| match id {
                ProofStepId::Active(id) => Some(*id),
                _ => None,
            })
            .collect()
    }

    pub fn depends_on_active(&self, id: usize) -> bool {
        self.dependencies()
            .iter()
            .any(|i| *i == ProofStepId::Active(id))
    }

    // Whether this is the last step of the proof
    pub fn finishes_proof(&self) -> bool {
        self.clause.is_impossible()
    }

    // We have to strictly limit deduction that happens between two library facts, because
    // the plan is for the library to grow very large.
    pub fn automatic_reject(&self) -> bool {
        if self.truthiness == Truthiness::Factual && self.proof_size > 2 {
            // Only do one step of deduction with global facts.
            return true;
        }

        false
    }
}
