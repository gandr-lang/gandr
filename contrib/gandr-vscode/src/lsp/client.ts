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
    // The server reads `gandr.diagnostics.verbosity`,
    // `gandr.diagnostics.quiet`, `gandr.presentation.form`,
    // `gandr.presentation.spelling` and `gandr.inlineCompletion.trigger` from
    // the initialization options at startup, and from the `gandr` section each
    // `workspace/didChangeConfiguration` pushes, republishing open documents
    // at a new verbosity or spelling. With `supportHtml` the client announces the `span`,
    // `pre` and `code` tags, and the server colours each hover by the roles
    // its semantic tokens carry, through the `gandr.hover.*` colours.
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: "file", language: "gandr" }],
      initializationOptions: settings(),
      markdown: { supportHtml: true },
      outputChannel,
      traceOutputChannel,
    };
    const client = new this("gandr", "gandr language server", serverOptions, clientOptions);
    client.registerProposedFeatures();
    return client;
  }

  public override dispose(timeout?: number): Promise<void> {
    this.configurationListener.dispose();
    return super.dispose(timeout);
  }

  // Never called from `start()`: `sendNotification` ensures a connection by
  // awaiting `start()` itself, so a push from an override of `start()`
  // recurses without bound and the extension host dies. The startup value
  // travels in the initialization options. The form toggle awaits it, so the
  // hover it asks for next is answered in the new form.
  public pushConfiguration(): Promise<void> {
    if (!this.isRunning()) {
      return Promise.resolve();
    }
    return this.sendNotification("workspace/didChangeConfiguration", {
      settings: { gandr: settings() },
    }).then(
      () => undefined,
      (error: unknown) => {
        this.error("Sending workspace/didChangeConfiguration failed", error);
      },
    );
  }
}

// The `gandr` settings the server reads, as the `gandr` section carries them.
function settings(): {
  diagnostics: { verbosity: string; quiet: number };
  presentation: { form: string; spelling: string | null };
  inlineCompletion: { trigger: string };
} {
  const gandr = vscode.workspace.getConfiguration("gandr");
  return {
    diagnostics: {
      verbosity: gandr.get<string>("diagnostics.verbosity", "user"),
      quiet: gandr.get<number>("diagnostics.quiet", 1.5),
    },
    presentation: {
      form: gandr.get<string>("presentation.form", "sugared"),
      spelling: gandr.get<string | null>("presentation.spelling", null),
    },
    inlineCompletion: {
      trigger: gandr.get<string>("inlineCompletion.trigger", "invoked"),
    },
  };
}
