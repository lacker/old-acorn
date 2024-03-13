import {
  commands,
  Disposable,
  ExtensionContext,
  Position,
  ProgressLocation,
  Range,
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

// Whether these search params will definitely yield the same result, just based
// on the local information we have.
function searchParamsEquivalent(a: SearchParams, b: SearchParams) {
  return (
    a.uri === b.uri &&
    a.selectedLine === b.selectedLine &&
    a.version === b.version
  );
}

class SearchPanel implements Disposable {
  panel: WebviewPanel;
  listener: Disposable;
  disposables: Disposable[];
  currentParams: SearchParams;
  distPath: string;
  currentSearchId: number;
  requestViewColumn: number;

  constructor(distPath: string) {
    this.distPath = distPath;
    this.currentSearchId = 0;
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

  // Updates the current location in the document.
  // Also updates the document version.
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
    let selectedLine = editor.selection.start.line;
    let version = editor.document.version;

    // No need to send the request if nothing has changed.
    let id = this.currentSearchId + 1;
    let params: SearchParams = { uri, selectedLine, version, id };
    if (
      this.currentParams &&
      searchParamsEquivalent(this.currentParams, params)
    ) {
      return;
    }

    // This view column is probably the one the user is actively writing in.
    // When in doubt, we can use this view column to do code-writing operations.
    this.requestViewColumn = editor.viewColumn;

    this.sendSearchRequest(params);
  }

  // Sends a search request to the language server, passing the response on to the webview.
  sendSearchRequest(params: SearchParams) {
    console.log(
      `search request ${params.id}: ${params.uri} v${params.version} line ${params.selectedLine}`
    );
    this.currentSearchId = params.id;
    this.currentParams = params;

    client
      .sendRequest("acorn/search", params)
      .then((response: SearchResponse) => {
        if (!this.panel) {
          // The user closed the search panel since we sent the request.
          return;
        }
        if (params.id != this.currentSearchId) {
          // This request has been superseded by a newer one.
          return;
        }
        if (response.error) {
          console.log("search error:", response.error);
          return;
        }
        if (!response.loading) {
          this.panel.webview.postMessage(response);
        }
        if (!response.result) {
          // The search response is not complete. Send another request after waiting a bit.
          let ms = 100;
          setTimeout(() => this.retrySearchRequest(params.id), ms);
        }
      });
  }

  retrySearchRequest(id: number) {
    if (!this.panel) {
      // The user closed the search panel since we sent the request.
      return;
    }
    if (id != this.currentSearchId) {
      // This request has been superseded by a newer one.
      return;
    }
    this.sendSearchRequest(this.currentParams);
  }

  // Handles messages from the webview.
  async handleWebviewMessage(message: any) {
    if (message.command === "insertProof") {
      await this.insertProof(
        message.uri,
        message.version,
        message.line,
        message.code
      );
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

  // Inserts a proof at the given line.
  // Code already at that line will be shifted down, so that it follows the inserted code.
  async insertProof(
    uri: string,
    version: number,
    line: number,
    code: string[]
  ) {
    let parts = uri.split("/");
    let filename = parts[parts.length - 1];

    let editor = await this.focusEditor(uri);
    if (!editor) {
      window.showWarningMessage(`${filename} has been closed`);
      return;
    }

    if (editor.document.version != version) {
      window.showWarningMessage(`${filename} has pending changes`);
      return;
    }

    if (line < 0 || line > editor.document.lineCount) {
      window.showErrorMessage(`invalid line number: ${line}`);
      return;
    }

    let config = workspace.getConfiguration("editor", editor.document.uri);
    let tabSize = config.get("tabSize", 4);
    let lineText = editor.document.lineAt(line).text;

    // Figure out how much to indent the inserted code.
    let indent = 0;
    for (let i = 0; i < lineText.length; i++) {
      if (lineText[i] === " ") {
        indent += 1;
        continue;
      }
      if (lineText[i] === "\t") {
        indent += tabSize;
        continue;
      }
      if (lineText[i] === "}") {
        // We're inserting into a block that this line closes.
        // So we want the inserted code to be more indented than this line is.
        indent += tabSize;
      }
      break;
    }
    let spacer = " ".repeat(indent);
    let formatted = [];
    for (let c of code) {
      formatted.push(spacer + c + "\n");
    }

    let success = await editor.edit((edit) => {
      // Insert the new code itself.
      let insertPos = new Position(line, 0);
      edit.insert(insertPos, formatted.join(""));

      // If the line before our insertion is empty, we want to delete it, so that
      // the net effect is inserting this code at the empty line.
      if (
        line > 0 &&
        editor.document.lineAt(line - 1).text.trim().length === 0
      ) {
        let prevPos = new Position(line - 1, 0);
        edit.delete(new Range(prevPos, insertPos));
      }
    });

    if (!success) {
      window.showErrorMessage("failed to insert proof");
      return;
    }

    // If the line before our insertion is empty, we want to delete it.
    if (line > 0 && editor.document.lineAt(line - 1).text.trim().length === 0) {
      let start = new Position(line - 1, 0);
      let end = new Position(line, 0);
      let success = await editor.edit((edit) => {
        edit.delete(new Range(start, end));
      });
      if (!success) {
        window.showErrorMessage("failed to delete empty line");
        return;
      }
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

    // Always reissue the search request on panel open
    this.currentParams = null;
    this.updateLocation();
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
