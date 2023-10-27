use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use acorn::environment::Environment;
use acorn::namespace::FIRST_NORMAL;
use acorn::project::Project;
use acorn::prover::{Outcome, Prover};
use acorn::token::{Token, LSP_TOKEN_TYPES};
use chrono;
use crossbeam::queue::SegQueue;
use dashmap::DashMap;
use serde::{Deserialize, Serialize};
use tokio::sync::{Mutex, RwLock};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

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

    progress: Arc<Mutex<ProgressResponse>>,

    // superseded is set to true when there is a newer version of the document.
    superseded: Arc<AtomicBool>,

    // env is set by the background diagnostics task.
    // It is None before that completes.
    env: Arc<RwLock<Option<Environment>>>,
}

impl Document {
    fn new(url: Url, text: String, version: i32) -> Document {
        Document {
            url,
            text,
            version,
            progress: Arc::new(Mutex::new(ProgressResponse::default())),
            superseded: Arc::new(AtomicBool::new(false)),
            env: Arc::new(RwLock::new(None)),
        }
    }

    fn log(&self, message: &str) {
        // Extract the last component of the url
        let filename = self.url.path_segments().unwrap().last().unwrap();
        let versioned = format!("{} v{}: {}", filename, self.version, message);
        log(&versioned);
    }

    // Create diagnostics based on the cached data for the given url.
    // Publishes them incrementally as each new diagnostic is found.
    // The task completes when all diagnostics are created.
    async fn run_diagnostics(&self, client: Client) {
        let start_time = chrono::Local::now();
        self.log("running diagnostics");

        let mut diagnostics = vec![];
        // TODO: use a real Project rather than the stub
        let mut env = Environment::new(FIRST_NORMAL);
        let tokens = Token::scan(&self.text);
        if let Err(e) = env.add_tokens(&mut Project::new_mock(), tokens) {
            self.log(&format!("env.add failed: {:?}", e));
            diagnostics.push(Diagnostic {
                range: e.token.range(),
                severity: Some(DiagnosticSeverity::ERROR),
                message: e.to_string(),
                ..Diagnostic::default()
            });
            client
                .publish_diagnostics(self.url.clone(), diagnostics, None)
                .await;
            return;
        }

        // Save the environment for use by other tasks.
        // We can't mutate it after this point.
        *self.env.write().await = Some(env);
        let shared_env = self.env.read().await;
        let env = shared_env.as_ref().unwrap().clone();

        let paths = env.goal_paths();
        let mut done = 0;
        let total = paths.len() as i32;
        for path in paths {
            let goal_context = env.get_goal_context(&path);
            let mut prover = Prover::new(&goal_context, false, None);
            prover.stop_flags.push(self.superseded.clone());
            let outcome = prover.search_for_contradiction(1000, 1.0);

            // Update progress
            done += 1;
            let new_progress = ProgressResponse { done, total };
            {
                let mut locked_progress = self.progress.lock().await;
                *locked_progress = new_progress;
            }

            let description = match outcome {
                Outcome::Success => continue,
                Outcome::Exhausted => "is unprovable",
                Outcome::Unknown => "timed out",
                Outcome::Interrupted => "was interrupted",
            };
            let message = format!("{} {}", goal_context.name, description);
            self.log(&message);
            if outcome == Outcome::Interrupted {
                return;
            }

            diagnostics.push(Diagnostic {
                range: goal_context.range,
                severity: Some(DiagnosticSeverity::WARNING),
                message,
                ..Diagnostic::default()
            });
            client
                .publish_diagnostics(self.url.clone(), diagnostics.clone(), None)
                .await;
        }

        if diagnostics.is_empty() {
            client
                .publish_diagnostics(self.url.clone(), diagnostics.clone(), None)
                .await;
        }
        let duration = chrono::Local::now() - start_time;
        let seconds = duration.num_milliseconds() as f64 / 1000.0;
        self.log(&format!(
            "diagnostics complete after {:.2}s. {} issue{} found",
            seconds,
            diagnostics.len(),
            if diagnostics.len() == 1 { "" } else { "s" }
        ));
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressParams {
    // Which document
    pub uri: Url,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DebugParams {
    // Which document
    pub uri: Url,
    pub version: i32,

    // The selected location in the document
    pub start: Position,
    pub end: Position,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DebugResponse {
    // This message is designed to be displayed in the client.
    pub message: Option<String>,

    pub goal_name: Option<String>,

    pub output: Vec<String>,
    pub completed: bool,
}

impl DebugResponse {
    fn message(message: &str) -> DebugResponse {
        DebugResponse {
            message: Some(message.to_string()),
            goal_name: None,
            output: vec![],
            completed: false,
        }
    }
}

// The language server can work on one expensive "debug" task at a time.
// The DebugTask tracks information around that request.
#[derive(Clone)]
struct DebugTask {
    document: Arc<Document>,

    // The range in the document corresponding to the goal we're debugging
    range: Range,

    // The path to the goal
    path: Vec<usize>,

    // The name of the goal
    goal_name: String,

    // The queue of lines printed by the debug task
    queue: Arc<SegQueue<String>>,

    // The last return value of the debug task, just in "lines printed" format
    output: Arc<RwLock<Vec<String>>>,

    // Set this flag to true when the task is completed successfully
    completed: Arc<AtomicBool>,

    // Set this flag to true when a subsequent task has been created
    superseded: Arc<AtomicBool>,
}

impl DebugTask {
    fn overlaps_selection(&self, start: Position, end: Position) -> bool {
        return start <= self.range.end && end >= self.range.start;
    }

    // Makes a response based on the current state of the task
    async fn response(&self) -> DebugResponse {
        let completed = self.completed.load(std::sync::atomic::Ordering::Relaxed);
        let lines = {
            let mut locked_output = self.output.write().await;
            while let Some(line) = self.queue.pop() {
                locked_output.push(line);
            }
            locked_output.clone()
        };
        DebugResponse {
            message: None,
            goal_name: Some(self.goal_name.clone()),
            output: lines,
            completed,
        }
    }

    // Runs the debug task.
    async fn run(&self) {
        // Get the environment for the full document
        let read_doc_env = self.document.env.read().await;
        let doc_env = match read_doc_env.as_ref() {
            Some(doc_env) => doc_env,
            None => {
                // There should be an env available, because we don't run this task without one.
                log("no env available in DebugTask::run");
                return;
            }
        };

        log(&format!("running debug task for {}", self.goal_name));

        // Get the environment for this specific goal
        let goal_context = doc_env.get_goal_context(&self.path);
        let mut prover = Prover::new(&goal_context, true, Some(self.queue.clone()));

        // Stop the prover if either this task or this document version is superseded
        prover.stop_flags.push(self.superseded.clone());
        prover.stop_flags.push(self.document.superseded.clone());
        let outcome = prover.search_for_contradiction(3000, 3.0);
        self.queue.push("".to_string());

        match outcome {
            Outcome::Success => {
                self.queue.push("Success!".to_string());
                prover.print_proof();
            }
            Outcome::Exhausted => {
                self.queue
                    .push("All possibilities have been exhausted.".to_string());
            }
            Outcome::Unknown => {
                // We failed. Let's add more information about the final state of the prover.
                self.queue
                    .push("Timeout. The final passive set:".to_string());
                prover.print_passive(None);
            }
            Outcome::Interrupted => {
                return;
            }
        }
        log(&format!("debug task for {} completed", self.goal_name));

        self.completed
            .store(true, std::sync::atomic::Ordering::Relaxed);
    }
}

struct Backend {
    client: Client,

    // Maps uri to the most recent version of a document
    documents: DashMap<Url, Arc<Document>>,

    // The current debug task, if any
    debug_task: Arc<RwLock<Option<DebugTask>>>,
}

impl Backend {
    fn new(client: Client) -> Backend {
        Backend {
            client,
            documents: DashMap::new(),
            debug_task: Arc::new(RwLock::new(None)),
        }
    }

    // Spawn a background task to create diagnostics for the given url
    fn spawn_diagnostics(&self, uri: Url) {
        let doc: Arc<Document> = match self.documents.get(&uri) {
            Some(doc) => doc.clone(),
            None => {
                log("no text available for diagnostics");
                return;
            }
        };
        let client = self.client.clone();
        tokio::spawn(async move {
            doc.run_diagnostics(client).await;
        });
    }

    fn update_document(&self, url: Url, text: String, version: i32, tag: &str) {
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

    fn fail(&self, message: &str) -> Result<DebugResponse> {
        log(message);
        Ok(DebugResponse::message(message))
    }

    async fn handle_progress_request(&self, params: ProgressParams) -> Result<ProgressResponse> {
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return Ok(ProgressResponse::default());
            }
        };
        let locked_progress = doc.progress.lock().await;
        Ok(locked_progress.clone())
    }

    async fn handle_debug_request(&self, params: DebugParams) -> Result<DebugResponse> {
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return self.fail("no text available");
            }
        };
        if let Some(current_task) = self.debug_task.read().await.as_ref() {
            if current_task.document.url == params.uri
                && current_task.document.version == params.version
                && current_task.overlaps_selection(params.start, params.end)
            {
                // This request matches the current task.
                // Respond based on the current task.
                return Ok(current_task.response().await);
            }
        }

        let read_env = doc.env.read().await;
        let env = match read_env.as_ref() {
            Some(env) => env,
            None => {
                return self.fail("no env available");
            }
        };

        let (path, goal_context) = match env.find_location(params.start, params.end) {
            Some(tuple) => tuple,
            None => {
                return self.fail("no goal at this location");
            }
        };

        // Create a new debug task
        let new_task = DebugTask {
            document: doc.clone(),
            range: goal_context.range,
            path,
            goal_name: goal_context.name.clone(),
            queue: Arc::new(SegQueue::new()),
            output: Arc::new(RwLock::new(vec![])),
            completed: Arc::new(AtomicBool::new(false)),
            superseded: Arc::new(AtomicBool::new(false)),
        };

        // Replace the locked singleton task
        {
            let mut locked_task = self.debug_task.write().await;
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
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
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
        self.spawn_diagnostics(params.text_document.uri);
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.update_document(uri.clone(), text, version, "open");
        self.spawn_diagnostics(uri);
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = std::mem::take(&mut params.content_changes[0].text);
        let version = params.text_document.version;
        self.update_document(uri, text, version, "change");
    }

    async fn shutdown(&self) -> Result<()> {
        log("shutdown");
        Ok(())
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
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
        .custom_method("acorn/debug", Backend::handle_debug_request)
        .custom_method("acorn/progress", Backend::handle_progress_request)
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
