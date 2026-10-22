import type { Location, Position } from "vscode-languageclient/node";

import * as vscode from "vscode";

import { IMPORT_DROP, ImportDrop } from "./drop";
import { registerInputMethod } from "./input/method";
import { GandrLanguageClient } from "./lsp/client";
import { COPIED_SOURCES, IMPORT_PASTE, ImportPaste } from "./paste";

export async function activate(context: vscode.ExtensionContext) {
  const languageClient = GandrLanguageClient.create();
  context.subscriptions.push(languageClient);
  registerInputMethod(context);
  context.subscriptions.push(
    vscode.commands.registerCommand("gandr.toggleForm", () => toggleForm(languageClient)),
  );
  context.subscriptions.push(
    vscode.commands.registerCommand("gandr.showSyntaxTree", showSyntaxTree),
  );
  context.subscriptions.push(
    vscode.commands.registerCommand(
      "gandr.showReferences",
      (uri: string, position: Position, locations: Location[]) =>
        showReferences(languageClient, uri, position, locations),
    ),
  );
  context.subscriptions.push(
    vscode.languages.registerDocumentDropEditProvider(
      { language: "gandr" },
      new ImportDrop(languageClient),
      { dropMimeTypes: ["text/uri-list"], providedDropEditKinds: [IMPORT_DROP] },
    ),
  );
  context.subscriptions.push(
    vscode.languages.registerDocumentPasteEditProvider(
      { language: "gandr" },
      new ImportPaste(languageClient),
      {
        copyMimeTypes: [COPIED_SOURCES],
        pasteMimeTypes: [COPIED_SOURCES],
        providedPasteEditKinds: [IMPORT_PASTE],
      },
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

// Show the uses a references lens counted, from the lens's command: the
// server sends the document's URI, the name's position and the locations in
// protocol shape, and the editor's references view takes them converted.
async function showReferences(
  languageClient: GandrLanguageClient,
  uri: string,
  position: Position,
  locations: Location[],
): Promise<void> {
  const convert = languageClient.protocol2CodeConverter;
  await vscode.commands.executeCommand(
    "editor.action.showReferences",
    convert.asUri(uri),
    convert.asPosition(position),
    locations.map((location) => convert.asLocation(location)),
  );
}

// Open the molded tree of the active gandr editor's document beside it, as
// the server's `gandr-tree` virtual document: the server serves its text over
// `workspace/textDocumentContent` and asks for it again after each change, so
// the view follows the edits. Shown as plain text, not as gandr.
async function showSyntaxTree(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (editor?.document.languageId !== "gandr" || editor.document.uri.scheme !== "file") {
    return;
  }
  const tree = editor.document.uri.with({ scheme: "gandr-tree" });
  const document = await vscode.languages.setTextDocumentLanguage(
    await vscode.workspace.openTextDocument(tree),
    "plaintext",
  );
  await vscode.window.showTextDocument(document, {
    viewColumn: vscode.ViewColumn.Beside,
    preserveFocus: true,
    preview: false,
  });
}
