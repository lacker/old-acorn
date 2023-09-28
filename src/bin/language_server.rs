use acorn::environment::Environment;
use acorn::prover::{Outcome, Prover};
use acorn::token::{Token, LSP_TOKEN_TYPES};
use chrono;
use dashmap::DashMap;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Document {
    text: String,
    version: i32,
}

impl Document {
    fn new(text: String, version: i32) -> Document {
        Document { text, version }
    }
}

#[derive(Debug)]
struct Backend {
    client: Client,

    // Maps uri to the most recent version of a document
    cache: DashMap<Url, Document>,
}

impl Backend {
    fn new(client: Client) -> Backend {
        Backend {
            client,
            cache: DashMap::new(),
        }
    }

    fn is_current_version(&self, uri: &Url, version: i32) -> bool {
        match self.cache.get(uri) {
            Some(doc) => doc.version == version,
            None => false,
        }
    }

    // Allow formatting messages
    async fn log_info(&self, message: &str) {
        let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
        let stamped = format!("[{}] {}", timestamp, message);
        eprintln!("{}", stamped);
    }

    // Create diagnostics based on the cached data for the given url
    async fn make_diagnostics(&self, uri: Url) {
        let doc = match self.cache.get(&uri) {
            Some(doc) => doc,
            None => {
                self.log_info("no text available for diagnostics").await;
                return;
            }
        };

        let mut diagnostics = vec![];
        let mut env = Environment::new();
        let tokens = Token::scan(&doc.text);
        if let Err(e) = env.add_tokens(tokens) {
            self.log_info(&format!("env.add failed: {:?}", e)).await;
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
            let outcome = prover.search_for_contradiction(1000, 1.0);

            if !self.is_current_version(&uri, doc.version) {
                self.log_info("diagnostics stopped").await;
                return;
            }
            if outcome == Outcome::Success {
                continue;
            }
            let message = if outcome == Outcome::Exhausted {
                format!("{} is unprovable", goal_context.name)
            } else {
                format!("{} could not be proved", goal_context.name)
            };

            diagnostics.push(Diagnostic {
                range: goal_context.range,
                severity: Some(DiagnosticSeverity::WARNING),
                message,
                ..Diagnostic::default()
            });
            self.client
                .publish_diagnostics(uri.clone(), diagnostics.clone(), None)
                .await;
            self.log_info(&format!("{} diagnostics published", diagnostics.len()))
                .await;
        }
        self.log_info("done making diagnostics").await;
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        self.log_info("initializing...").await;
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
        self.log_info("did_save").await;
        let uri = params.text_document.uri;
        self.make_diagnostics(uri).await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.log_info("did_open").await;
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.cache.insert(uri.clone(), Document::new(text, version));
        self.make_diagnostics(uri).await;
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        self.log_info("did_change").await;
        let uri = params.text_document.uri;
        let text = std::mem::take(&mut params.content_changes[0].text);
        let version = params.text_document.version;
        self.cache.insert(uri, Document::new(text, version));
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        self.log_info("semantic_tokens_full").await;
        let uri = params.text_document.uri;
        let doc = match self.cache.get(&uri) {
            Some(doc) => doc,
            None => {
                self.log_info("no text available for semantic tokens").await;
                return Ok(None);
            }
        };
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

    let (service, socket) = LspService::build(Backend::new).finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
