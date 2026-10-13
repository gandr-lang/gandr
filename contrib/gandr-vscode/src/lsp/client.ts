import type { Executable } from "vscode-languageclient/node";

import * as vscode from "vscode";
import { LanguageClient, LanguageClientOptions, ServerOptions } from "vscode-languageclient/node";

export class GandrLanguageClient extends LanguageClient {
  private readonly configurationListener: vscode.Disposable;

  private constructor(
    id: string,
    name: string,
    serverOptions: ServerOptions,
    clientOptions: LanguageClientOptions,
    forceDebug?: boolean,
  ) {
    super(id, name, serverOptions, clientOptions, forceDebug);
    // The server reads the pushed `gandr` section. It does not pull
    // `workspace/configuration`, so a change has to be sent.
    this.configurationListener = vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("gandr")) {
        void this.pushConfiguration();
      }
    });
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
    // options at startup, and from the `gandr` section each
    // `workspace/didChangeConfiguration` pushes, republishing open documents
    // at the new level.
    const verbosity = vscode.workspace
      .getConfiguration("gandr")
      .get<string>("diagnostics.verbosity", "user");
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: "file", language: "gandr" }],
      initializationOptions: { diagnostics: { verbosity } },
      outputChannel,
      traceOutputChannel,
    };
    const client = new this("gandr", "gandr language server", serverOptions, clientOptions);
    client.registerProposedFeatures();
    return client;
  }

  public override async start(): Promise<void> {
    await super.start();
    await this.pushConfiguration();
  }

  public override dispose(timeout?: number): Promise<void> {
    this.configurationListener.dispose();
    return super.dispose(timeout);
  }

  private pushConfiguration(): Promise<void> {
    if (!this.isRunning()) {
      return Promise.resolve();
    }
    const verbosity = vscode.workspace
      .getConfiguration("gandr")
      .get<string>("diagnostics.verbosity", "user");
    return this.sendNotification("workspace/didChangeConfiguration", {
      settings: { gandr: { diagnostics: { verbosity } } },
    }).then(
      () => undefined,
      (error: unknown) => {
        this.error("Sending workspace/didChangeConfiguration failed", error);
      },
    );
  }
}
