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

interface DebugParams {
  uri: string;
  start: Position;
  end: Position;
  version: number;
}

function debugParamsEqual(a: DebugParams, b: DebugParams) {
  return (
    a.uri == b.uri &&
    a.start.isEqual(b.start) &&
    a.end.isEqual(b.end) &&
    a.version == b.version
  );
}

class Debugger implements Disposable {
  panel: WebviewPanel;
  disposables: Disposable[];
  currentParams: DebugParams;
  distPath: string;
  currentRequestId: number;

  constructor(distPath: string) {
    this.distPath = distPath;
    this.currentRequestId = 0;
    this.disposables = [
      commands.registerTextEditorCommand("acorn.displayDebugger", (editor) =>
        this.display(editor)
      ),

      commands.registerTextEditorCommand("acorn.toggleDebugger", (editor) =>
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
    let params: DebugParams = { uri, start, end, version };
    if (this.currentParams && debugParamsEqual(this.currentParams, params)) {
      return;
    }

    this.sendDebugRequest(params);
  }

  // Sends a debug request to the language server
  sendDebugRequest(params: DebugParams) {
    console.log("sending debug request:", params);
    this.currentRequestId += 1;
    let id = this.currentRequestId;

    this.currentParams = params;

    client.sendRequest("acorn/debug", params).then((result: any) => {
      if (!this.panel) {
        // The user closed the debug panel since we sent the request.
        return;
      }
      if (id != this.currentRequestId) {
        // This request has been superseded by a newer one.
        return;
      }
      if (result.message) {
        console.log("language server responded:", result.message);
        return;
      }
      console.log("posting message:", result);
      this.panel.webview.postMessage(result);
      if (!result.completed) {
        // The debug response is not complete. Send another request after waiting a bit.
        let ms = 100;
        setTimeout(() => this.sendDebugRequest(params), ms);
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
      "acornDebugger",
      "Acorn Debugger",
      { viewColumn: column, preserveFocus: true },
      {
        enableFindWidget: true,
        retainContextWhenHidden: true,
        enableScripts: true,
        localResourceRoots: [Uri.file(this.distPath)],
      }
    );

    this.panel.onDidDispose(() => {
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

export function activate(context: ExtensionContext) {
  let timestamp = new Date().toLocaleTimeString();
  console.log("activating acorn language extension at", timestamp);
  let debuggerPath = context.asAbsolutePath("../debugger/dist");
  context.subscriptions.push(new Debugger(debuggerPath));

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

  let showProgressBar = async (document: TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }

    // Wait a bit before showing progress
    await new Promise((resolve) => setTimeout(resolve, 250));

    let uri = document.uri.toString();
    let basename = path.basename(document.uri.fsPath);
    let params = { uri };
    let previousPercent = 0;
    window.withProgress(
      {
        location: ProgressLocation.Notification,
        title: "Validating " + basename,
        cancellable: true,
      },
      async (progress, token) => {
        token.onCancellationRequested(() => {
          console.log("acorn validation progress bar canceled");
        });

        while (true) {
          let response: any = await client.sendRequest(
            "acorn/progress",
            params
          );
          if (response.total === response.done) {
            return;
          }

          let percent = Math.floor((100 * response.done) / response.total);
          let increment = percent - previousPercent;
          progress.report({ increment });
          previousPercent = percent;
        }
      }
    );
  };

  workspace.textDocuments.forEach(showProgressBar);
  context.subscriptions.push(workspace.onDidSaveTextDocument(showProgressBar));
  context.subscriptions.push(workspace.onDidOpenTextDocument(showProgressBar));
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
