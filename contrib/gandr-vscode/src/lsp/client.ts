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
    const server: Executable = {
      command: "gandr",
      args: ["lsp"],
    };
    const serverOptions: ServerOptions = {
      run: server,
      debug: server,
    };
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: "file", language: "gandr" }],
      outputChannel,
      traceOutputChannel,
    };
    const client = new this("gandr", "gandr language server", serverOptions, clientOptions);
    client.registerProposedFeatures();
    return client;
  }
}
