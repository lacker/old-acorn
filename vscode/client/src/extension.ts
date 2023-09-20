import {
    workspace,
    EventEmitter,
    ExtensionContext,
    window,
    Range,
    TextDocumentChangeEvent,
    commands,
    Selection,
    Uri,
} from "vscode";

import {
    Disposable,
    Executable,
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient;

export async function activate(context: ExtensionContext) {
    let disposable = commands.registerCommand("helloworld.helloWorld", async uri => {
        // The code you place here will be executed every time your command is executed
        // Display a message box to the user
        const url = Uri.parse('/home/victor/Documents/test-dir/nrs/another.nrs')
        let document = await workspace.openTextDocument(uri);
        await window.showTextDocument(document);

        // console.log(uri)
        window.activeTextEditor.document
        let editor = window.activeTextEditor;
        let range = new Range(1, 1, 1, 1)
        editor.selection = new Selection(range.start, range.end);
    });

    context.subscriptions.push(disposable);

    const traceOutputChannel = window.createOutputChannel("Acorn Language Server trace");
    const command = process.env.SERVER_PATH || "acorn-language-server";
    const run: Executable = {
        command,
        options: {
            env: {
                ...process.env,
                // eslint-disable-next-line @typescript-eslint/naming-convention
                RUST_LOG: "debug",
            },
        },
    };
    const serverOptions: ServerOptions = {
        run,
        debug: run,
    };
    // If the extension is launched in debug mode then the debug server options are used
    // Otherwise the run options are used
    // Options to control the language client
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
        "acorn-language-server", "acorn language server", serverOptions, clientOptions);
    client.start();
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

export function activateInlayHints(ctx: ExtensionContext) {
    const maybeUpdater = {
        hintsProvider: null as Disposable | null,
        updateHintsEventEmitter: new EventEmitter<void>(),

        async onConfigChange() {
            this.dispose();

            const event = this.updateHintsEventEmitter.event;

        },

        onDidChangeTextDocument({ contentChanges, document }: TextDocumentChangeEvent) {
        },

        dispose() {
            this.hintsProvider?.dispose();
            this.hintsProvider = null;
            this.updateHintsEventEmitter.dispose();
        },
    };

    workspace.onDidChangeConfiguration(maybeUpdater.onConfigChange, maybeUpdater, ctx.subscriptions);
    workspace.onDidChangeTextDocument(maybeUpdater.onDidChangeTextDocument, maybeUpdater, ctx.subscriptions);

    maybeUpdater.onConfigChange().catch(console.error);
}