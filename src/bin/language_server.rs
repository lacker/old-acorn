use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::{
    DidSaveTextDocumentParams, InitializeParams, InitializeResult, MessageType, ServerCapabilities,
};
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
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        self.log_info("als: initializing...").await;
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities::default(),
        })
    }

    async fn did_save(&self, _: DidSaveTextDocumentParams) {
        self.log_info("als: file saved.").await;
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
