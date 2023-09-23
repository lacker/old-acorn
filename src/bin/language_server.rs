use acorn::environment::Environment;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,
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
                self.log_info("env.add OK").await;
            }
            Err(e) => {
                self.log_info(&format!("env.add failed: {:?}", e)).await;
                // TODO: send diagnostic
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
