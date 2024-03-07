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
  requestViewColumn: number;

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

    // This view column is probably the one the user is actively writing in.
    // When in doubt, we can use this view column to do code-writing operations.
    this.requestViewColumn = editor.viewColumn;

    this.sendSearchRequest(params);
  }

  // Sends a search request to the language server, passing the response on to the webview.
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
      if (response.error) {
        console.log("language server error:", response.error);
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

  // Handles messages from the webview.
  async handleWebviewMessage(message: any) {
    console.log("XXX handleWebviewMessage:", message);
    if (message.command === "insertProof") {
      await this.insertProof(message.uri, message.line, message.code);
    } else {
      console.log("unhandled message:", message);
    }
  }

  // Heuristically find an editor for the given uri and focus it.
  // If we can't, return null.
  async focusEditor(uri: string): Promise<TextEditor | null> {
    // Ideally we use an editor that's already visible
    for (let editor of window.visibleTextEditors) {
      if (editor.document.uri.toString() === uri) {
        await window.showTextDocument(editor.document, editor.viewColumn);
        return editor;
      }
    }

    // If the document is open but not visible, we have to guess a view column.
    for (let document of workspace.textDocuments) {
      if (document.uri.toString() === uri) {
        return window.showTextDocument(document, this.requestViewColumn);
      }
    }

    return null;
  }

  async insertProof(uri: string, line: number, code: string[]) {
    let editor = await this.focusEditor(uri);
    if (!editor) {
      let parts = uri.split("/");
      let filename = parts[parts.length - 1];
      window.showWarningMessage(`${filename} has been closed`);
      return;
    }

    console.log(`XXX line: ${line}, code: ${code.join("\n")}`);

    let success = await editor.edit((edit) => {
      let position = new Position(line, 0);
      edit.insert(position, code.join("\n") + "\n");
    });
    if (!success) {
      window.showErrorMessage("failed to insert proof");
    }
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

    this.listener = this.panel.webview.onDidReceiveMessage(
      this.handleWebviewMessage,
      this
    );

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
