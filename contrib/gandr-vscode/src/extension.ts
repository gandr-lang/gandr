import * as vscode from "vscode";

import { IMPORT_DROP, ImportDrop } from "./drop";
import { GandrLanguageClient } from "./lsp/client";

export async function activate(context: vscode.ExtensionContext) {
  const languageClient = GandrLanguageClient.create();
  context.subscriptions.push(languageClient);
  context.subscriptions.push(
    vscode.commands.registerCommand("gandr.toggleForm", () => toggleForm(languageClient)),
  );
  context.subscriptions.push(
    vscode.languages.registerDocumentDropEditProvider(
      { language: "gandr" },
      new ImportDrop(languageClient),
      { dropMimeTypes: ["text/uri-list"], providedDropEditKinds: [IMPORT_DROP] },
    ),
  );
  await languageClient.start();
}

export function deactivate() {}

// Flip `gandr.presentation.form` where it is set, the user settings when
// nowhere, push it to the server, and hover again at the cursor of a gandr
// editor so the type shows in the form just chosen.
async function toggleForm(languageClient: GandrLanguageClient): Promise<void> {
  const gandr = vscode.workspace.getConfiguration("gandr");
  const form = gandr.get<string>("presentation.form", "sugared");
  const inspected = gandr.inspect<string>("presentation.form");
  const target =
    inspected?.workspaceFolderValue !== undefined
      ? vscode.ConfigurationTarget.WorkspaceFolder
      : inspected?.workspaceValue !== undefined
        ? vscode.ConfigurationTarget.Workspace
        : vscode.ConfigurationTarget.Global;
  await gandr.update("presentation.form", form === "sugared" ? "explicit" : "sugared", target);
  await languageClient.pushConfiguration();
  if (vscode.window.activeTextEditor?.document.languageId === "gandr") {
    await vscode.commands.executeCommand("editor.action.showHover");
  }
}
