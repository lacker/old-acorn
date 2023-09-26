use acorn::environment::Environment;
use acorn::token::{Error, Token, LSP_TOKEN_TYPES};
use dashmap::DashMap;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,

    // Maps uri to full document text
    cache: DashMap<Url, String>,
}

fn get_range(text: &str, error: &Error) -> Range {
    match error {
        Error::Token(token_error) => {
            let line = token_error.line_index as u32;
            let character = token_error.char_index as u32;
            let end_character = character + token_error.text.len() as u32;
            let start = Position { line, character };
            let end = Position {
                line,
                character: end_character,
            };
            Range { start, end }
        }
        Error::EOF => {
            let line = text.lines().count() as u32;
            let character = text.lines().last().unwrap().len() as u32;
            let start = Position { line, character };
            let end = Position { line, character };
            Range { start, end }
        }
    }
}

impl Backend {
    fn new(client: Client) -> Backend {
        Backend {
            client,
            cache: DashMap::new(),
        }
    }

    // Allow formatting messages
    async fn log_info(&self, message: &str) {
        self.client.log_message(MessageType::INFO, message).await;
    }

    // Create diagnostics based on the cached data for the given url
    async fn make_diagnostics(&self, uri: Url) {
        let text = match self.cache.get(&uri) {
            Some(text) => text,
            None => {
                self.log_info("no text available for diagnostics").await;
                return;
            }
        };

        let mut env = Environment::new();
        let tokens = Token::scan(&text);
        match env.add_tokens(tokens) {
            Ok(()) => {
                self.client.publish_diagnostics(uri, vec![], None).await;
                self.log_info("env.add OK").await;
            }
            Err(e) => {
                self.log_info(&format!("env.add failed: {:?}", e)).await;
                let range = get_range(&text, &e);
                let diagnostic = Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.to_string(),
                    ..Diagnostic::default()
                };

                self.client
                    .publish_diagnostics(uri, vec![diagnostic], None)
                    .await;

                self.log_info("diagnostic sent").await;
            }
        }
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
                            include_text: Some(true),
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
        let text = match params.text {
            Some(text) => text,
            None => {
                self.log_info("no text available at save time").await;
                return;
            }
        };
        let uri = params.text_document.uri;
        self.cache.insert(uri.clone(), text);
        self.make_diagnostics(uri).await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        // self.log_info("did_open").await;
        let uri = params.text_document.uri;
        self.cache.insert(uri.clone(), params.text_document.text);
        self.make_diagnostics(uri).await;
    }

    async fn did_change(&self, mut params: DidChangeTextDocumentParams) {
        self.log_info("did_change").await;
        self.cache.insert(
            params.text_document.uri,
            std::mem::take(&mut params.content_changes[0].text),
        );
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
        let text = match self.cache.get(&uri) {
            Some(text) => text,
            None => {
                self.log_info("no text available for semantic tokens").await;
                return Ok(None);
            }
        };
        let tokens = Token::scan(&text);

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
    env_logger::init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(Backend::new).finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
