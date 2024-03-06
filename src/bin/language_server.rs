use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use acorn::module::Module;
use acorn::project::Project;
use acorn::prover::{Outcome, Prover};
use acorn::token::{Token, LSP_TOKEN_TYPES};
use chrono;
use crossbeam::queue::SegQueue;
use dashmap::DashMap;
use serde::{Deserialize, Serialize};
use tokio::sync::{mpsc, Mutex, OnceCell, RwLock, RwLockWriteGuard};
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

// The language server stores one progress struct, and returns it at any time.
// 0/0 only occurs at initialization. It means "there have never been any progress bars".
// Once we ever show a progress bar, we leave it at the previous finished state.
// When progress is cancelled or interrupted, we should update this so that done = total.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct ProgressResponse {
    done: i32,
    total: i32,
}

impl ProgressResponse {
    fn default() -> ProgressResponse {
        ProgressResponse { done: 0, total: 0 }
    }
}

// A structure representing a particular version of a document.
#[derive(Clone)]
struct Document {
    url: Url,
    text: String,
    version: i32,

    // superseded is set to true when there is a newer version of the document.
    superseded: Arc<AtomicBool>,
}

impl Document {
    fn new(url: Url, text: String, version: i32) -> Document {
        Document {
            url,
            text,
            version,
            superseded: Arc::new(AtomicBool::new(false)),
        }
    }

    fn log(&self, message: &str) {
        // Extract the last component of the url
        let filename = self.url.path_segments().unwrap().last().unwrap();
        let versioned = format!("{} v{}: {}", filename, self.version, message);
        log(&versioned);
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressParams {}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchParams {
    // Which document
    pub uri: Url,
    pub version: i32,

    // The selected location in the document
    pub start: Position,
    pub end: Position,
}

// The SearchResult contains information that is produced once, when the search completes.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
pub struct SearchResult {
    // Code for the proof that can be inserted.
    // If we failed to find a proof, this is None.
    pub code: Option<Vec<String>>,
}

impl SearchResult {
    fn success(code: Vec<String>) -> SearchResult {
        SearchResult { code: Some(code) }
    }

    fn failure() -> SearchResult {
        SearchResult { code: None }
    }
}

// NOTE: you have to keep this definition in sync with handleSearchResponse in App.svelte.
//
// The SearchResponse will be polled until the SearchResult is available, so it can
// contain data that is updated over time.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchResponse {
    // This message is designed to be displayed in the client.
    pub message: Option<String>,

    pub goal_name: Option<String>,

    // The lines vector will keep growing as the search task runs.
    pub lines: Vec<String>,

    // The line where we would insert a proof for this goal
    pub proof_insertion_line: u32,

    // The result of the search process.
    // If it has not completed yet, this is None.
    pub result: Option<SearchResult>,
}

impl SearchResponse {
    fn default() -> SearchResponse {
        SearchResponse {
            message: None,
            goal_name: None,
            lines: vec![],
            result: None,
            proof_insertion_line: 0,
        }
    }
}

// A search task is a long-running task that searches for a proof.
// The language server can work on one search task at a time.
// The SearchTask tracks information around that request.
// It will typically be accessed in parallel.
// The thread doing the search updates the task with its information, while threads handling
// concurrent user requests can read it.
#[derive(Clone)]
struct SearchTask {
    project: Arc<RwLock<Project>>,
    document: Arc<Document>,

    // The module that we're searching for a proof in
    module_name: String,

    // The range in the document corresponding to the goal we're proving
    range: Range,

    // The path to the goal
    path: Vec<usize>,

    // The name of the goal
    goal_name: String,

    // The queue of lines logged by the search task
    queue: Arc<SegQueue<String>>,

    // Unstructured partial output of the search process
    lines: Arc<RwLock<Vec<String>>>,

    // Final result of the search, if it has completed
    result: Arc<OnceCell<SearchResult>>,

    // Set this flag to true when a subsequent search task has been created
    superseded: Arc<AtomicBool>,

    // Zero-based line where we would insert a proof for this goal
    proof_insertion_line: u32,
}

impl SearchTask {
    fn overlaps_selection(&self, start: Position, end: Position) -> bool {
        return start <= self.range.end && end >= self.range.start;
    }

    // Makes a response based on the current state of the task
    async fn response(&self) -> SearchResponse {
        let lines = {
            let mut locked_output = self.lines.write().await;
            while let Some(line) = self.queue.pop() {
                locked_output.push(line);
            }
            locked_output.clone()
        };
        let result = self.result.get().map(|r| r.clone());
        SearchResponse {
            message: None,
            goal_name: Some(self.goal_name.clone()),
            lines,
            result,
            proof_insertion_line: self.proof_insertion_line,
        }
    }

    // Runs the search task.
    async fn run(&self) {
        // Get the environment for this module
        let project = self.project.read().await;
        let env = match project.get_env_by_name(&self.module_name) {
            Some(env) => env,
            None => {
                log(&format!("no environment for {}", self.module_name));
                return;
            }
        };

        log(&format!("running search task for {}", self.goal_name));

        // Get the specific goal to prove
        let goal_context = env.get_goal_context(&project, &self.path);
        let mut prover = Prover::new(&project, &goal_context, true, Some(self.queue.clone()));

        // By default, the prover will stop if the build is stopped.
        // We also want to stop it if we get a subsequent search request, to work on something else.
        prover.stop_flags.push(self.superseded.clone());

        let outcome = prover.medium_search();
        self.queue.push("".to_string());

        let result = match outcome {
            Outcome::Success => {
                self.queue.push("Success!".to_string());
                prover.print_proof();
                self.queue.push("".to_string());
                let proof = prover.get_proof().unwrap();
                match env.proof_to_code(&proof) {
                    Ok(code) => {
                        self.queue.push("Proof converted to code:".to_string());
                        for line in &code {
                            self.queue.push(line.to_string());
                        }
                        SearchResult::success(code)
                    }
                    Err(s) => {
                        self.queue
                            .push("Error converting proof to code:".to_string());
                        self.queue.push(s);
                        SearchResult::failure()
                    }
                }
            }
            Outcome::Inconsistent => {
                self.queue.push("Found inconsistency!".to_string());
                prover.print_proof();
                SearchResult::failure()
            }
            Outcome::Exhausted => {
                self.queue
                    .push("All possibilities have been exhausted.".to_string());
                SearchResult::failure()
            }
            Outcome::Unknown => {
                // We failed. Let's add more information about the final state of the prover.
                self.queue
                    .push("Timeout. The final passive set:".to_string());
                prover.print_passive(None);
                SearchResult::failure()
            }
            Outcome::Interrupted => {
                self.queue.push("Interrupted.".to_string());
                return;
            }
            Outcome::Error => {
                self.queue.push(format!(
                    "Error: {}",
                    prover.error.unwrap_or("?".to_string())
                ));

                return;
            }
        };

        log(&format!("search task for {} completed", self.goal_name));
        self.result.set(result).expect("result was already set");
    }
}

struct Backend {
    client: Client,

    // The project we're working on
    project: Arc<RwLock<Project>>,

    // Progress requests share this value with the client.
    // Long-running tasks update it as they go.
    progress: Arc<Mutex<ProgressResponse>>,

    // Maps uri to the most recent version of a document
    documents: DashMap<Url, Arc<Document>>,

    // The current search task, if any
    search_task: Arc<RwLock<Option<SearchTask>>>,
}

impl Backend {
    fn new(client: Client) -> Backend {
        Backend {
            project: Arc::new(RwLock::new(Project::new("math"))),
            client,
            progress: Arc::new(Mutex::new(ProgressResponse::default())),
            documents: DashMap::new(),
            search_task: Arc::new(RwLock::new(None)),
        }
    }

    // Run a build in a background thread, proving the goals in all open documents.
    // Both spawned threads hold a read lock on the project while doing their work.
    // This ensures that the project doesn't change for the duration of the build.
    fn spawn_build(&self) {
        let start_time = chrono::Local::now();

        // This channel passes the build events
        let (tx, mut rx) = mpsc::unbounded_channel();

        // Spawn a thread to run the build.

        let project = self.project.clone();
        tokio::spawn(async move {
            let project = project.read().await;

            tokio::task::block_in_place(move || {
                let success = project.build(&mut |event| {
                    tx.send(event).unwrap();
                });

                let duration = chrono::Local::now() - start_time;
                let seconds = duration.num_milliseconds() as f64 / 1000.0;
                let verb = if success { "succeeded" } else { "failed" };
                log(&format!("build {} after {:.2}s", verb, seconds));
            });
        });

        // Spawn a thread to process the build events.
        let project = self.project.clone();
        let progress = self.progress.clone();
        let client = self.client.clone();
        tokio::spawn(async move {
            let project = project.read().await;
            let mut diagnostic_map: HashMap<Url, Vec<Diagnostic>> = HashMap::new();
            while let Some(event) = rx.recv().await {
                if let Some((done, total)) = event.progress {
                    if total > 0 {
                        let mut locked_progress = progress.lock().await;
                        *locked_progress = ProgressResponse { done, total };
                    }
                }

                if let Some(message) = event.log_message {
                    log(&message);
                }

                if let Some((module_name, diagnostic)) = event.diagnostic {
                    let path = match project.path_from_module_name(&module_name) {
                        Ok(path) => path,
                        Err(_) => {
                            log(&format!("no path available for {}", module_name));
                            return;
                        }
                    };
                    let url = Url::from_file_path(path).unwrap();
                    let diagnostics = diagnostic_map.entry(url.clone()).or_default();
                    if let Some(d) = diagnostic {
                        diagnostics.push(d);
                    }
                    client
                        .publish_diagnostics(url, diagnostics.clone(), None)
                        .await;
                }
            }
        });
    }

    // This updates a document in the backend, but not in the project.
    // The backend tracks every single change; the project only gets them when we want it to use them.
    // This means that typing a little bit won't cancel an ongoing build.
    fn update_doc_in_backend(&self, url: Url, text: String, version: i32, tag: &str) {
        let new_doc = Document::new(url.clone(), text, version);
        new_doc.log(&format!("did_{}; updating document", tag));
        if let Some(old_doc) = self.documents.get(&url) {
            old_doc.log(&format!("superseded by v{}", version));
            old_doc
                .superseded
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
        self.documents.insert(url.clone(), Arc::new(new_doc));
    }

    // If there is a build happening, stops it.
    // Acquires the write lock on the project.
    // Returns a writable reference to the project.
    async fn stop_build_and_get_project(&self) -> RwLockWriteGuard<Project> {
        {
            let project = self.project.read().await;
            project.stop_build();
        }
        // Reallow the build once we acquire the write lock
        let mut project = self.project.write().await;
        project.allow_build();
        project
    }

    // This updates a document in the project, based on the state in the backend.
    async fn update_doc_in_project(&self, url: &Url) {
        let content = self.documents.get(url);
        if content.is_none() {
            log("no text available for update_doc_in_project");
            return;
        }
        let content = &content.unwrap().text;
        let path = match url.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                log(format!("no path available for {} in update_doc_in_project", url).as_str());
                return;
            }
        };
        {
            // Check if the project already has this document state.
            // If the update is a no-op, there's no need to stop the build.
            let project = self.project.read().await;
            if project.matches_open_file(&path, content) {
                return;
            }
        }
        let mut project = self.stop_build_and_get_project().await;
        log(format!("updating {} with {} bytes", path.display(), content.len()).as_str());
        project.update_file(path, content);
    }

    fn fail(&self, message: &str) -> jsonrpc::Result<SearchResponse> {
        log(message);
        Ok(SearchResponse {
            message: Some(message.to_string()),
            ..SearchResponse::default()
        })
    }

    async fn handle_progress_request(
        &self,
        _params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        let locked_progress = self.progress.lock().await;
        Ok(locked_progress.clone())
    }

    async fn handle_search_request(&self, params: SearchParams) -> jsonrpc::Result<SearchResponse> {
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return self.fail("no text available");
            }
        };
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.document.url == params.uri
                && current_task.document.version == params.version
                && current_task.overlaps_selection(params.start, params.end)
            {
                // This request matches the current task.
                // Respond based on the current task.
                return Ok(current_task.response().await);
            }
        }

        let project = self.project.read().await;
        let path = match doc.url.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                // There should be a path available, because we don't run this task without one.
                return self.fail("no path available in SearchTask::run");
            }
        };
        let module_name = match project.module_name_from_path(&path) {
            Ok(name) => name,
            Err(e) => return self.fail(&format!("module_name_from_path failed: {:?}", e)),
        };
        let env = match project.get_module_by_name(&module_name) {
            Module::Ok(env) => env,
            _ => {
                return self.fail(&format!("could not load module named {}", module_name));
            }
        };

        let (path, goal_context) = match env.find_location(&project, params.start, params.end) {
            Some(tuple) => tuple,
            None => {
                return self.fail("no goal at this location");
            }
        };

        // Create a new search task
        let new_task = SearchTask {
            project: self.project.clone(),
            document: doc.clone(),
            module_name,
            range: goal_context.range,
            path,
            goal_name: goal_context.name.clone(),
            queue: Arc::new(SegQueue::new()),
            lines: Arc::new(RwLock::new(vec![])),
            result: Arc::new(OnceCell::new()),
            superseded: Arc::new(AtomicBool::new(false)),
            proof_insertion_line: goal_context.proof_insertion_line,
        };

        // Replace the locked singleton task
        {
            let mut locked_task = self.search_task.write().await;
            if let Some(old_task) = locked_task.as_ref() {
                // Cancel the old task
                old_task
                    .superseded
                    .store(true, std::sync::atomic::Ordering::Relaxed);
            }
            *locked_task = Some(new_task.clone());
        }

        // A minimal response before any data has been collected
        let response = new_task.response().await;

        tokio::spawn(async move {
            new_task.run().await;
        });

        Ok(response)
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        log("initializing...");
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::FULL),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                            include_text: Some(false),
                        })),
                        ..TextDocumentSyncOptions::default()
                    },
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensRegistrationOptions(
                        SemanticTokensRegistrationOptions {
                            text_document_registration_options: {
                                TextDocumentRegistrationOptions {
                                    document_selector: Some(vec![DocumentFilter {
                                        language: Some("acorn".to_string()),
                                        scheme: Some("file".to_string()),
                                        pattern: None,
                                    }]),
                                }
                            },
                            semantic_tokens_options: SemanticTokensOptions {
                                work_done_progress_options: WorkDoneProgressOptions::default(),
                                legend: SemanticTokensLegend {
                                    token_types: LSP_TOKEN_TYPES.into(),
                                    token_modifiers: vec![],
                                },
                                range: Some(false),
                                full: Some(SemanticTokensFullOptions::Bool(true)),
                            },
                            static_registration_options: StaticRegistrationOptions::default(),
                        },
                    ),
                ),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        log("did_save");
        self.update_doc_in_project(&params.text_document.uri).await;
        self.spawn_build();
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.update_doc_in_backend(uri.clone(), text, version, "open");
        self.update_doc_in_project(&uri).await;
        self.spawn_build();
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = std::mem::take(&mut params.content_changes[0].text);
        let version = params.text_document.version;
        self.update_doc_in_backend(uri, text, version, "change");
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        log("shutdown");
        Ok(())
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> jsonrpc::Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let doc = match self.documents.get(&uri) {
            Some(doc) => doc,
            None => {
                log("no text available for semantic_tokens_full");
                return Ok(None);
            }
        };
        doc.log("semantic_tokens_full");
        let tokens = Token::scan(&doc.text);

        // Convert tokens to LSP semantic tokens
        let mut semantic_tokens: Vec<SemanticToken> = vec![];
        let mut prev_line = 0;
        let mut prev_start = 0;
        for token in tokens {
            let line = token.line_number as u32;
            let start = token.start as u32;
            let length = token.len as u32;
            let token_type = match token.lsp_type_u32() {
                Some(t) => t,
                None => continue,
            };
            let token_modifiers_bitset = 0;
            let delta_line = line - prev_line;
            let delta_start = if delta_line == 0 {
                start - prev_start
            } else {
                start
            };
            semantic_tokens.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type,
                token_modifiers_bitset,
            });
            prev_line = line;
            prev_start = start;
        }

        let result = SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: semantic_tokens,
        });
        Ok(Some(result))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(Backend::new)
        .custom_method("acorn/search", Backend::handle_search_request)
        .custom_method("acorn/progress", Backend::handle_progress_request)
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
