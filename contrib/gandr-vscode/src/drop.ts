import type { TextEdit } from "vscode-languageclient/node";

import * as vscode from "vscode";

import type { GandrLanguageClient } from "./lsp/client";

// The kind of a drop that imports the sources dropped.
export const IMPORT_DROP = vscode.DocumentDropOrPasteEditKind.TextUpdateImports.append("gandr");

// Gandr sources dropped into a gandr document are imported: the server answers
// `gandr/importFiles` with an `import "…" ;` line for each source the document
// does not import yet, after its last import, and nothing is written where
// they were dropped. A drop the server adds nothing for is left to the editor's
// own drop.
export class ImportDrop implements vscode.DocumentDropEditProvider {
  private readonly languageClient: GandrLanguageClient;

  public constructor(languageClient: GandrLanguageClient) {
    this.languageClient = languageClient;
  }

  public async provideDocumentDropEdits(
    document: vscode.TextDocument,
    _position: vscode.Position,
    dataTransfer: vscode.DataTransfer,
    token: vscode.CancellationToken,
  ): Promise<vscode.DocumentDropEdit | undefined> {
    const listed = await dataTransfer.get("text/uri-list")?.asString();
    // RFC 2483: one URI per line, a line starting with `#` a comment.
    const files = (listed ?? "")
      .split(/\r?\n/)
      .filter((line) => line !== "" && !line.startsWith("#"));
    if (files.length === 0 || token.isCancellationRequested) {
      return undefined;
    }
    const edits = await this.languageClient.sendRequest<TextEdit[] | null>(
      "gandr/importFiles",
      {
        textDocument: this.languageClient.code2ProtocolConverter.asTextDocumentIdentifier(document),
        files,
      },
      token,
    );
    const converted = await this.languageClient.protocol2CodeConverter.asTextEdits(edits, token);
    if (converted === undefined || converted.length === 0) {
      return undefined;
    }
    const drop = new vscode.DocumentDropEdit("", "Import the gandr sources", IMPORT_DROP);
    drop.additionalEdit = new vscode.WorkspaceEdit();
    drop.additionalEdit.set(document.uri, converted);
    return drop;
  }
}
