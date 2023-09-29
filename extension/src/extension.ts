import { commands, window, workspace, ExtensionContext } from "vscode";
import {
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";
import * as vscode from "vscode";

let client: LanguageClient;
let infopanel: vscode.WebviewPanel;

function makeHTML() {
  return `<!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <title>Hello Acorn World</title>
        </head>
        <body>
            <h1>Hello, Acorn World!</h1>
        </body>
        </html>`;
}

function displayInfoview(editor: vscode.TextEditor) {
  let column =
    editor && editor.viewColumn ? editor.viewColumn + 1 : vscode.ViewColumn.Two;
  if (column === 4) {
    column = vscode.ViewColumn.Three;
  }
  if (infopanel) {
    infopanel.reveal(column);
    return;
  }
  infopanel = vscode.window.createWebviewPanel(
    "acornInfoview",
    "Acorn Infoview",
    { viewColumn: column, preserveFocus: true },
    {
      enableFindWidget: true,
      retainContextWhenHidden: true,
    }
  );

  infopanel.onDidDispose(() => {
    infopanel = null;
  });

  // Set the webview's initial content
  infopanel.webview.html = makeHTML();
}

function toggleInfoview(editor: vscode.TextEditor) {
  if (infopanel) {
    infopanel.dispose();
    infopanel = null;
    return;
  }

  displayInfoview(editor);

  // Set the webview's initial content
  infopanel.webview.html = makeHTML();
}

export function activate(context: ExtensionContext) {
  console.log("activating acorn language extension.");

  context.subscriptions.push(
    commands.registerTextEditorCommand("acorn.displayInfoview", displayInfoview)
  );
  context.subscriptions.push(
    commands.registerTextEditorCommand("acorn.toggleInfoview", toggleInfoview)
  );

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
