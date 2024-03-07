import {
  commands,
  Disposable,
  ExtensionContext,
  Position,
  ProgressLocation,
  TextDocument,
  TextEditor,
  Uri,
  ViewColumn,
  WebviewPanel,
  window,
  workspace,
} from "vscode";
import * as path from "path";
import * as fs from "fs";
import {
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient;

interface SearchParams {
  uri: string;
  start: Position;
  end: Position;
  version: number;
}

function searchParamsEqual(a: SearchParams, b: SearchParams) {
  return (
    a.uri == b.uri &&
    a.start.isEqual(b.start) &&
    a.end.isEqual(b.end) &&
    a.version == b.version
  );
}

class SearchPanel implements Disposable {
  panel: WebviewPanel;
  listener: Disposable;
  disposables: Disposable[];
  currentParams: SearchParams;
  distPath: string;
  currentRequestId: number;

  constructor(distPath: string) {
    this.distPath = distPath;
    this.currentRequestId = 0;
    this.disposables = [
      commands.registerTextEditorCommand("acorn.displaySearchPanel", (editor) =>
        this.display(editor)
      ),

      commands.registerTextEditorCommand("acorn.toggleSearchPanel", (editor) =>
        this.toggle(editor)
      ),
      window.onDidChangeActiveTextEditor(() => {
        this.updateLocation();
      }),
      window.onDidChangeTextEditorSelection(() => {
        this.updateLocation();
      }),
      workspace.onDidChangeTextDocument(() => {
        this.updateLocation();
      }),
    ];
  }

  // Updates the current location in the document
  updateLocation() {
    let editor = window.activeTextEditor;
    if (!editor) {
      return;
    }
    if (editor.document.languageId != "acorn") {
      return;
    }
    if (!this.panel) {
      return;
    }

    let uri = editor.document.uri.toString();
    let { start, end } = editor.selection;
    let version = editor.document.version;

    // No need to send the request if nothing has changed.
    let params: SearchParams = { uri, start, end, version };
    if (this.currentParams && searchParamsEqual(this.currentParams, params)) {
      return;
    }

    this.sendSearchRequest(params);
  }

  // Sends a search request to the language server
  sendSearchRequest(params: SearchParams) {
    console.log("sending search request:", params);
    this.currentRequestId += 1;
    let id = this.currentRequestId;

    this.currentParams = params;

    client.sendRequest("acorn/search", params).then((response: any) => {
      if (!this.panel) {
        // The user closed the search panel since we sent the request.
        return;
      }
      if (id != this.currentRequestId) {
        // This request has been superseded by a newer one.
        return;
      }
      if (response.message) {
        console.log("language server responded:", response.message);
        return;
      }
      console.log("posting message:", response);
      this.panel.webview.postMessage(response);
      if (!response.result) {
        // The search response is not complete. Send another request after waiting a bit.
        let ms = 100;
        setTimeout(() => this.sendSearchRequest(params), ms);
      }
    });
  }

  display(editor: TextEditor) {
    let column =
      editor && editor.viewColumn ? editor.viewColumn + 1 : ViewColumn.Two;
    if (column === 4) {
      column = ViewColumn.Three;
    }
    if (this.panel) {
      this.panel.reveal(column);
      return;
    }
    this.panel = window.createWebviewPanel(
      "acornSearchPanel",
      "Proof Search",
      { viewColumn: column, preserveFocus: true },
      {
        enableFindWidget: true,
        retainContextWhenHidden: true,
        enableScripts: true,
        localResourceRoots: [Uri.file(this.distPath)],
      }
    );

    this.listener = this.panel.webview.onDidReceiveMessage((message) => {
      console.log("command: ", message.command);
    });

    this.panel.onDidDispose(() => {
      this.listener.dispose();
      this.listener = null;
      this.panel = null;
    });

    // Set the webview's initial content
    let distPathInWebview = this.panel.webview.asWebviewUri(
      Uri.file(this.distPath)
    );
    let indexPath = Uri.file(path.join(this.distPath, "index.html"));
    let html = fs.readFileSync(indexPath.fsPath, "utf8");
    // Inject a new base href tag
    let injected = html.replace(
      "<head>",
      `<head>\n<base href="${distPathInWebview}/">`
    );
    console.log("post-injection html:\n", injected);
    this.panel.webview.html = injected;
  }

  toggle(editor: TextEditor) {
    if (this.panel) {
      this.panel.dispose();
      this.panel = null;
      return;
    }

    this.display(editor);
  }

  dispose() {
    for (let subscription of this.disposables) {
      subscription.dispose();
    }
    this.panel.dispose();
  }
}

async function getProgress() {
  return await client.sendRequest("acorn/progress", {});
}

// Automatically hides it when we are done.
async function showProgressBar() {
  let startTime = Date.now();

  let response: any = await getProgress();

  while (response.done === response.total) {
    // Maybe progress just hasn't started yet.
    // Let's wait a bit and try again.
    await new Promise((resolve) => setTimeout(resolve, 100));
    response = await getProgress();

    let elapsed = Date.now() - startTime;
    if (elapsed > 2000) {
      // It's been a while. Let's give up.
      console.log("giving up on progress bar");
      return;
    }
  }

  let previousPercent = 0;
  window.withProgress(
    {
      location: ProgressLocation.Notification,
      title: "Acorn Validation",
      cancellable: true,
    },
    async (progress, token) => {
      token.onCancellationRequested(() => {
        console.log("acorn validation progress bar canceled");
      });

      while (response.total !== response.done) {
        let percent = Math.floor((100 * response.done) / response.total);
        let increment = percent - previousPercent;
        progress.report({ increment });
        previousPercent = percent;

        // We have something to show, so we can wait a bit before updating.
        await new Promise((resolve) => setTimeout(resolve, 100));
        response = await getProgress();
      }
    }
  );
}

export function activate(context: ExtensionContext) {
  let timestamp = new Date().toLocaleTimeString();
  console.log("activating acorn language extension at", timestamp);
  let searchPath = context.asAbsolutePath("../search/dist");
  context.subscriptions.push(new SearchPanel(searchPath));

  let traceOutputChannel = window.createOutputChannel("Acorn Language Server");

  let command = process.env.SERVER_PATH;
  if (!command) {
    window.showErrorMessage(
      "The SERVER_PATH environment variable is not defined."
    );
    return;
  }

  let exec: Executable = {
    command,
    options: {
      env: {
        RUST_BACKTRACE: "1",
        ...process.env,
      },
    },
  };

  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
  let serverOptions: ServerOptions = {
    run: exec,
    debug: exec,
  };

  let clientOptions: LanguageClientOptions = {
    // Register the server for plain text documents
    documentSelector: [{ scheme: "file", language: "acorn" }],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
    },
    traceOutputChannel,
  };

  // Create the language client and start the client.
  client = new LanguageClient(
    "acornClient",
    "Acorn Client",
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  client.start();

  let onDocumentChange = async (document: TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }
    await showProgressBar();
  };

  let hasAcornDocs = false;
  for (let doc of workspace.textDocuments) {
    if (doc.languageId === "acorn") {
      hasAcornDocs = true;
      break;
    }
  }
  if (hasAcornDocs) {
    showProgressBar();
  }

  context.subscriptions.push(workspace.onDidSaveTextDocument(onDocumentChange));
  context.subscriptions.push(workspace.onDidOpenTextDocument(onDocumentChange));
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
