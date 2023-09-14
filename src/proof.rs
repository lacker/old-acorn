// This file contains the data structures that make up a proof, along with heuristics of how it is found.

use std::cmp::Ordering;

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum ClauseType {
    Fact,
    NegatedGoal,
    Other,
}

impl ClauseType {
    // Highest priority should be processed first
    fn priority(&self) -> u8 {
        match self {
            ClauseType::Fact => 2,
            ClauseType::NegatedGoal => 1,
            ClauseType::Other => 0,
        }
    }
}

impl Ord for ClauseType {
    fn cmp(&self, other: &ClauseType) -> Ordering {
        self.priority().cmp(&other.priority())
    }
}

impl PartialOrd for ClauseType {
    fn partial_cmp(&self, other: &ClauseType) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
