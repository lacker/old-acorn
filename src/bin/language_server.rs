use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};
use acorn::token::{Token, LSP_TOKEN_TYPES};
use chrono;
use dashmap::DashMap;
use serde::{Deserialize, Serialize};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

// A structure representing a particular version of a document.
// superseded_flag should be set to true when there is a newer version of the document.
#[derive(Debug)]
struct Document {
    url: Url,
    text: String,
    version: i32,
    superseded_flag: Arc<AtomicBool>,
}

fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

impl Document {
    fn new(url: Url, text: String, version: i32) -> Document {
        Document {
            url,
            text,
            version,
            superseded_flag: Arc::new(AtomicBool::new(false)),
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
pub struct DebugParams {
    pub uri: Url,
    pub start: Position,
    pub end: Position,
}

#[derive(Clone, Debug)]
struct Backend {
    client: Client,

    // Maps uri to the most recent version of a document
    cache: Arc<DashMap<Url, Document>>,
}

impl Backend {
    fn new(client: Client) -> Backend {
        Backend {
            client,
            cache: Arc::new(DashMap::new()),
        }
    }

    fn is_current_version(&self, uri: &Url, version: i32) -> bool {
        match self.cache.get(uri) {
            Some(doc) => doc.version == version,
            None => false,
        }
    }

    // Create diagnostics based on the cached data for the given url.
    // The task completes when all diagnostics are created.
    async fn make_diagnostics(&self, uri: Url) {
        let doc = match self.cache.get(&uri) {
            Some(doc) => doc,
            None => {
                log("no text available for diagnostics");
                return;
            }
        };
        doc.log("making diagnostics");

        let mut diagnostics = vec![];
        let mut env = Environment::new();
        let tokens = Token::scan(&doc.text);
        if let Err(e) = env.add_tokens(tokens) {
            doc.log(&format!("env.add failed: {:?}", e));
            diagnostics.push(Diagnostic {
                range: e.token.range(),
                severity: Some(DiagnosticSeverity::ERROR),
                message: e.to_string(),
                ..Diagnostic::default()
            });
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
            return;
        }

        let paths = env.goal_paths();
        for path in paths {
            let goal_context = env.get_goal_context(&path);
            let mut prover = Prover::load_goal(&goal_context);
            prover.stop_flag = doc.superseded_flag.clone();
            let outcome = prover.search_for_contradiction(1000, 1.0);

            if !self.is_current_version(&uri, doc.version) {
                doc.log("diagnostics stopped");
                return;
            }
            let description = match outcome {
                Outcome::Success => continue,
                Outcome::Exhausted => "is unprovable",
                Outcome::Unknown => "timed out",
                Outcome::Interrupted => "was interrupted",
            };
            let message = format!("{} {}", goal_context.name, description);
            doc.log(&message);
            if outcome == Outcome::Interrupted {
                return;
            }

            diagnostics.push(Diagnostic {
                range: goal_context.range,
                severity: Some(DiagnosticSeverity::WARNING),
                message,
                ..Diagnostic::default()
            });
            self.client
                .publish_diagnostics(uri.clone(), diagnostics.clone(), None)
                .await;
            doc.log(&format!("{} diagnostics published", diagnostics.len()));
        }
        doc.log("done making diagnostics");
    }

    // Spawn a background task to create diagnostics for the given url
    fn background_diagnostics(&self, uri: Url) {
        log("spawning background diagnostics");
        let clone = self.clone();
        tokio::spawn(async move {
            clone.make_diagnostics(uri).await;
        });
    }

    fn update_document(&self, url: Url, text: String, version: i32, tag: &str) {
        let new_doc = Document::new(url.clone(), text, version);
        new_doc.log(&format!("did_{}; updating document", tag));
        if let Some(old_doc) = self.cache.get(&url) {
            old_doc.log(&format!("superseded by v{}", version));
            old_doc
                .superseded_flag
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
        self.cache.insert(url.clone(), new_doc);
    }

    async fn handle_debug_request(&self, _: DebugParams) -> Result<i32> {
        Ok(1234)
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
        self.background_diagnostics(params.text_document.uri);
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.update_document(uri.clone(), text, version, "open");
        self.background_diagnostics(uri);
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
        let doc = match self.cache.get(&uri) {
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
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
