use acorn::environment::Environment;
use acorn::token::Error;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,
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
    // Allow formatting messages
    async fn log_info(&self, message: &str) {
        self.client.log_message(MessageType::INFO, message).await;
    }

    async fn process_document(&self, doc: TextDocument) {
        // Get the basename of the uri
        let basename = doc.uri.path_segments().unwrap().last().unwrap();
        self.log_info(&format!("{} changed. text:\n{}", basename, doc.text))
            .await;

        let mut env = Environment::new();
        match env.safe_add(&doc.text) {
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
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(|client| Backend { client }).finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
