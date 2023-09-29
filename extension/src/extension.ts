import { commands, window, workspace, ExtensionContext } from "vscode";
import {
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";
import * as vscode from "vscode";

let client: LanguageClient;

export function activate(context: ExtensionContext) {
  console.log("activating acorn language extension.");

  context.subscriptions.push(
    commands.registerTextEditorCommand("acorn.toggleInfoview", (editor) => {
      let column =
        editor && editor.viewColumn
          ? editor.viewColumn + 1
          : vscode.ViewColumn.Two;
      if (column === 4) {
        column = vscode.ViewColumn.Three;
      }
      let panel = vscode.window.createWebviewPanel(
        "acornInfoview",
        "Acorn Infoview",
        { viewColumn: column, preserveFocus: true },
        {
          enableFindWidget: true,
          retainContextWhenHidden: true,
        }
      );

      // Set the webview's initial content
      panel.webview.html = makeHTML();
    })
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
