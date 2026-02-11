import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

function createClient(): LanguageClient {
  const config = vscode.workspace.getConfiguration("specl");
  const serverPath = config.get<string>("serverPath") || "specl-lsp";

  const serverOptions: ServerOptions = {
    run: { command: serverPath, transport: TransportKind.stdio },
    debug: { command: serverPath, transport: TransportKind.stdio },
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "specl" }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher("**/*.specl"),
    },
    outputChannelName: "Specl Language Server",
  };

  return new LanguageClient(
    "specl",
    "Specl Language Server",
    serverOptions,
    clientOptions
  );
}

export async function activate(context: vscode.ExtensionContext) {
  client = createClient();
  await client.start();

  context.subscriptions.push(
    vscode.commands.registerCommand("specl.restartServer", async () => {
      if (client) {
        await client.stop();
      }
      client = createClient();
      await client.start();
      vscode.window.showInformationMessage("Specl language server restarted.");
    })
  );
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
