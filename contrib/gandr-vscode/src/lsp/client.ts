import type { Executable } from "vscode-languageclient/node";

import * as vscode from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

export class GandrLanguageClient extends LanguageClient {
  private constructor(
    id: string,
    name: string,
    serverOptions: ServerOptions,
    clientOptions: LanguageClientOptions,
    forceDebug?: boolean,
  ) {
    super(id, name, serverOptions, clientOptions, forceDebug);
  }

  public static create(): GandrLanguageClient {
    const outputChannel: vscode.LogOutputChannel = vscode.window.createOutputChannel(
      "gandr language server",
      {
        log: true,
      },
    );
    const traceOutputChannel: vscode.LogOutputChannel = vscode.window.createOutputChannel(
      "gandr language server trace",
      { log: true },
    );
    // `gandr lsp` reaches the engine hub of its working directory, so the
    // server starts in the first workspace folder: every window on one
    // workspace then shares one hub.
    const root = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    const server: Executable =
      root === undefined
        ? { command: "gandr", args: ["lsp"] }
        : { command: "gandr", args: ["lsp"], options: { cwd: root } };
    const serverOptions: ServerOptions = {
      run: server,
      debug: server,
    };
    // The server reads `gandr.diagnostics.verbosity` from the initialization
    // options at startup, and from the `gandr` section each configuration
    // change pushes, republishing open documents at the new level.
    const verbosity = vscode.workspace
      .getConfiguration("gandr")
      .get<string>("diagnostics.verbosity", "user");
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: "file", language: "gandr" }],
      initializationOptions: { diagnostics: { verbosity } },
      synchronize: { configurationSection: "gandr" },
      outputChannel,
      traceOutputChannel,
    };
    const client = new this("gandr", "gandr language server", serverOptions, clientOptions);
    client.registerProposedFeatures();
    return client;
  }
}
