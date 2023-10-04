import {
  commands,
  Disposable,
  ExtensionContext,
  Position,
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

class Infoview implements Disposable {
  panel: WebviewPanel;
  disposables: Disposable[];
  lastParams: DebugParams;
  distPath: string;

  constructor(distPath: string) {
    this.distPath = distPath;
    this.disposables = [
      commands.registerTextEditorCommand("acorn.displayInfoview", (editor) =>
        this.display(editor)
      ),

      commands.registerTextEditorCommand("acorn.toggleInfoview", (editor) =>
        this.toggle(editor)
      ),
      window.onDidChangeActiveTextEditor(() => {
        this.updateLocation("1");
      }),
      window.onDidChangeTextEditorSelection(() => {
        this.updateLocation("2");
      }),
      workspace.onDidChangeTextDocument(() => {
        this.updateLocation("3");
      }),
    ];
  }

  // Updates the current location in the document
  updateLocation(source?: string) {
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
    if (this.lastParams && debugParamsEqual(this.lastParams, params)) {
      return;
    }
    this.lastParams = params;

    client.sendRequest("acorn/debug", params).then((result: any) => {
      if (!this.panel) {
        return;
      }
      if (!debugParamsEqual(this.lastParams, params)) {
        // This request must have been superseded by a newer one.
        return;
      }
      console.log("debug result:", result);
      this.panel.webview.postMessage(result);
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
      "acornInfoview",
      "Acorn Infoview",
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
  let infoviewPath = context.asAbsolutePath("../infoview/dist");
  context.subscriptions.push(new Infoview(infoviewPath));

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
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
