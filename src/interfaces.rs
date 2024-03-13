// Interfaces between the language server and various consumers.
// The "Params" structs are requests that come into the language server.
// The "Response" structs are responses that go out of the language server.
//
// This file should be kept parallel to vscode/interfaces.d.ts.

use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::Url;

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

// The SearchResult contains information that is produced once, when the search completes.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
pub struct SearchResult {
    // Code for the proof that can be inserted.
    // If we failed to find a proof, this is None.
    pub code: Option<Vec<String>>,
}

impl SearchResult {
    pub fn success(code: Vec<String>) -> SearchResult {
        SearchResult { code: Some(code) }
    }

    pub fn failure() -> SearchResult {
        SearchResult { code: None }
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

    // If something went wrong, this contains an error message.
    pub error: Option<String>,

    // When loading is true, it means that we can't start a search, because the version
    // requested is not loaded. The caller can wait and retry, or just abandon.
    pub loading: bool,

    pub goal_name: Option<String>,

    // The text output will keep growing as the search task runs.
    pub text_output: Vec<String>,

    // The line where we would insert a proof for this goal
    pub proof_insertion_line: u32,

    // The result of the search process.
    // If it has not completed yet, this is None.
    pub result: Option<SearchResult>,

    // The id for the search, provided by the extension
    pub id: i32,
}

impl SearchResponse {
    pub fn new(params: SearchParams) -> SearchResponse {
        SearchResponse {
            uri: params.uri,
            version: params.version,
            error: None,
            loading: false,
            goal_name: None,
            text_output: vec![],
            result: None,
            proof_insertion_line: 0,
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

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ClauseInfo {
    // A format for the user to see
    pub text: String,

    // Only activated clauses have an id
    pub id: Option<usize>,
}

// The InfoResponse is sent from language server -> extension -> webview with the result of
// an info request.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoResponse {
    // The clause we are providing information for
    pub clause: ClauseInfo,

    // The clauses that we used to prove this one
    pub premises: Vec<ClauseInfo>,

    // The clauses that this clause can be used to prove
    pub consequences: Vec<ClauseInfo>,

    // How we proved this rule
    pub rule: String,
}
