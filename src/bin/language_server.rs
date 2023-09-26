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
    cache: DashMap<String, String>,
}

fn get_range(doc: &TextDocument, error: &Error) -> Range {
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
            let line = doc.text.lines().count() as u32;
            let character = doc.text.lines().last().unwrap().len() as u32;
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

    async fn process_document(&self, doc: TextDocument) {
        // Get the basename of the uri
        let basename = doc.uri.path_segments().unwrap().last().unwrap();
        self.log_info(&format!("{} changed. text:\n{}", basename, doc.text))
            .await;
        self.cache.insert(doc.uri.to_string(), doc.text.clone());

        let mut env = Environment::new();
        let tokens = Token::scan(&doc.text);
        match env.add_tokens(tokens) {
            Ok(()) => {
                self.client.publish_diagnostics(doc.uri, vec![], None).await;
                self.log_info("env.add OK").await;
            }
            Err(e) => {
                self.log_info(&format!("env.add failed: {:?}", e)).await;
                let range = get_range(&doc, &e);
                let diagnostic = Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.to_string(),
                    ..Diagnostic::default()
                };

                self.client
                    .publish_diagnostics(doc.uri, vec![diagnostic], None)
                    .await;

                self.log_info("diagnostic sent").await;
            }
        }
    }
}

struct TextDocument {
    uri: Url,
    text: String,
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
        self.log_info(&format!("did_save. text = [{:?}]", &params.text))
            .await;
        let text = match params.text {
            Some(text) => text,
            None => {
                self.log_info("oops no text").await;
                return;
            }
        };
        let doc = TextDocument {
            uri: params.text_document.uri,
            text,
        };
        self.process_document(doc).await
    }

    async fn did_change(&self, _: DidChangeTextDocumentParams) {
        self.log_info("did_change").await;
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
        let text = match self.cache.get(&uri.to_string()) {
            Some(text) => text,
            None => {
                self.log_info("oops no text").await;
                return Ok(None);
            }
        };
        let tokens = Token::scan(&text);

        // Convert tokens to LSP semantic tokens
        let mut semantic_tokens: Vec<SemanticToken> = vec![];
        let mut prev_line = 0;
        let mut prev_start = 0;
        for token in tokens {
            let line = token.line_index as u32;
            let start = token.char_index as u32;
            let length = token.text.len() as u32;
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
            self.log_info(&format!(
                "token: {}, token type: {:?}, delta_line: {}, delta_start: {}",
                token.text, token.token_type, delta_line, delta_start
            ))
            .await;
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
