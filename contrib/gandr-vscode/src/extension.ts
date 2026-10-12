import * as vscode from "vscode";

import { GandrLanguageClient } from "./lsp/client";

export async function activate(context: vscode.ExtensionContext) {
  const languageClient = GandrLanguageClient.create();
  context.subscriptions.push(languageClient);
  await languageClient.start();
}

export function deactivate() {}
