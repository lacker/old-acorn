// Interfaces between the language server and various consumers.
// The "Params" structs are requests that come into the language server.
// The "Response" structs are responses that go out of the language server.
//
// This file should be kept parallel to vscode/interfaces.d.ts.

use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Range, Url};

use crate::prover::Prover;

// The language server stores one progress struct, and returns it at any time.
// 0/0 only occurs at initialization. It means "there have never been any progress bars".
// Once we ever show a progress bar, we leave it at the previous finished state.
// When progress is cancelled or interrupted, we should update this so that done = total.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressResponse {
    pub done: i32,
    pub total: i32,
}

impl ProgressResponse {
    pub fn default() -> ProgressResponse {
        ProgressResponse { done: 0, total: 0 }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressParams {}

// The SearchParams are sent from extension to language server to start searching for a proof.
//
// NOTE: this struct defines the format used for the params in JavaScript as well.
//  See:
//  the SearchParams interface in extension.ts
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchParams {
    // Which document
    pub uri: Url,
    pub version: i32,

    // The selected line in the document
    pub selected_line: u32,

    // The search id, set by the extension.
    pub id: i32,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ClauseInfo {
    // A format for the user to see.
    // None if this is a contradiction.
    pub text: Option<String>,

    // Only activated clauses have an id
    pub id: Option<usize>,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Location {
    // Which document this assumption was made in.
    pub uri: Url,

    // The range in the source document corresponding to this proposition.
    // This is here for UI purposes. It is the place we should jump to or highlight to show
    // the user where this proposition is defined.
    pub range: Range,
}

// Information about one step in a proof.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofStepInfo {
    // The clause we are proving
    pub clause: ClauseInfo,

    // The clauses that we used to prove this one.
    // Each clause is tagged with its description.
    pub premises: Vec<(String, ClauseInfo)>,

    // Description of the rule used in this proof step
    pub rule: String,

    // Source is set when this proof step is based on a specific part of a codebase,
    // and we can find a location for it.
    pub location: Option<Location>,

    // Whether the source of this step is a trivial one.
    // TODO: this is an older concept of "trivial" that perhaps we should get rid of.
    // It is only used to determine whether to describe a theorem dependency or not.
    pub trivial: bool,

    // The depth of this proof step in the proof tree, counting only expensive deductions.
    // TODO: should we get rid of this?
    pub depth: u32,
}

// The SearchStatus contains information about a search which may be finished, or may be in progress.
// outcome is None while the search is in progress.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchStatus {
    // Code for the proof that can be inserted.
    // If we don't have a proof, this is None.
    pub code: Option<Vec<String>>,

    // If we failed to generate the "code" field, this is the error message.
    pub code_error: Option<String>,

    // Steps in the proof, as we found them.
    // If we failed to find a proof, this is None.
    pub steps: Option<Vec<ProofStepInfo>>,

    // A stringification of the prover's Outcome, if it has finished.
    pub outcome: Option<String>,

    // How many clauses we have activated.
    // Any id below this, we can handle info requests to provide information for it.
    pub num_activated: usize,
}

impl SearchStatus {
    pub fn default() -> SearchStatus {
        SearchStatus {
            code: None,
            code_error: None,
            steps: None,
            outcome: None,
            num_activated: 0,
        }
    }

    fn new(
        code: Option<Vec<String>>,
        code_error: Option<String>,
        steps: Option<Vec<ProofStepInfo>>,
        prover: &Prover,
    ) -> SearchStatus {
        SearchStatus {
            code,
            code_error,
            steps,
            outcome: prover.get_outcome().map(|o| o.to_string()),
            num_activated: prover.num_activated(),
        }
    }

    // Indicate that the search found a proof
    pub fn success(code: Vec<String>, steps: Vec<ProofStepInfo>, prover: &Prover) -> SearchStatus {
        SearchStatus::new(Some(code), None, Some(steps), prover)
    }

    // Indicate a failure during code generation.
    pub fn code_gen_error(
        steps: Vec<ProofStepInfo>,
        error: String,
        prover: &Prover,
    ) -> SearchStatus {
        SearchStatus::new(None, Some(error), Some(steps), prover)
    }

    // Indicate that the search does not have a proof.
    pub fn no_proof(prover: &Prover) -> SearchStatus {
        SearchStatus::new(None, None, None, prover)
    }
}

// The SearchResponse is sent from language server -> extension -> webview with the result of a
// proof search, or information about a partial result.
//
// The SearchResponse will be polled until the SearchResult is available, so it can
// contain data that is updated over time.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchResponse {
    // Which document this search is for.
    pub uri: Url,
    pub version: i32,

    // A failure is distinct from an error. An error is a problem with the language server,
    // or the extension. Those are reported as jsonrpc errors.
    // A failure is when the user requested some operation that we can't do.
    // When we have a failure, this contains a failure message.
    pub failure: Option<String>,

    // When loading is true, it means that we can't start a search, because the version
    // requested is not loaded. The caller can wait and retry, or just abandon.
    pub loading: bool,

    // Information about the goal
    pub goal_name: Option<String>,
    pub goal_range: Option<Range>,

    // The line where we would insert a proof for this goal.
    // We insert proofs at the beginning of the line.
    pub proof_insertion_line: u32,

    // Whether the goal already has an appropriate block to put the proof in.
    // If this is false, to create the proof we'll need to create a "by" block.
    pub has_block: bool,

    // The status of the search process.
    // If it has not completed yet, this is None.
    pub status: SearchStatus,

    // The id for the search, provided by the extension
    pub id: i32,
}

impl SearchResponse {
    pub fn new(params: SearchParams) -> SearchResponse {
        SearchResponse {
            uri: params.uri,
            version: params.version,
            failure: None,
            loading: false,
            goal_name: None,
            goal_range: None,
            status: SearchStatus::default(),
            proof_insertion_line: 0,
            has_block: false,
            id: params.id,
        }
    }
}

// The InfoParams are sent from webview -> extension -> language server, when the user is requesting
// more information about a search in progress.
//
// NOTE: keep this parallel to interfaces.ts in the webview.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoParams {
    // Each info request is associated with a single proof search.
    // We track this correlation using the id for the search request.
    pub search_id: i32,

    // Which clause we are requesting information for
    pub clause_id: usize,
}

// The InfoResult is sent from language server -> extension -> webview with the result of
// an info request.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoResult {
    // How we proved this clause
    pub step: ProofStepInfo,

    // The clauses that this clause can be used to prove
    pub consequences: Vec<ProofStepInfo>,
}

// If the request is out of sync with the server state, and we want to just ignore this request,
// returns a None result, along with a failure string describing what happened.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoResponse {
    // Matching to the request
    pub search_id: i32,

    pub failure: Option<String>,
    pub result: Option<InfoResult>,
}
