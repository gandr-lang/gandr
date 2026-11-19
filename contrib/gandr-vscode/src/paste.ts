import type { TextEdit } from "vscode-languageclient/node";

import * as vscode from "vscode";

import type { GandrLanguageClient } from "./lsp/client";

// The kind of a paste that imports the sources the pasted text names.
export const IMPORT_PASTE = vscode.DocumentDropOrPasteEditKind.TextUpdateImports.append("gandr");

// The type under which a copy keeps the sources its names are declared in.
export const COPIED_SOURCES = "application/vnd.gandr.sources";

// What a copy keeps: the document copied from and the sources its names are
// declared in, by URI.
interface Copied {
  readonly resource: string;
  readonly files: string[];
}

// Text copied from a gandr document and pasted into another is pasted with
// imports: the copy asks the server, by `gandr/copiedSources`, which sources
// declare what it names, and the paste asks `gandr/importFiles` for an
// `import "…" ;` line for each the document does not import yet. A paste into
// the document copied from, or one the server adds nothing for, is left to the
// editor's own paste.
export class ImportPaste implements vscode.DocumentPasteEditProvider {
  private readonly languageClient: GandrLanguageClient;

  public constructor(languageClient: GandrLanguageClient) {
    this.languageClient = languageClient;
  }

  public async prepareDocumentPaste(
    document: vscode.TextDocument,
    ranges: readonly vscode.Range[],
    dataTransfer: vscode.DataTransfer,
    token: vscode.CancellationToken,
  ): Promise<void> {
    const files = await this.languageClient.sendRequest<string[] | null>(
      "gandr/copiedSources",
      {
        textDocument: this.languageClient.code2ProtocolConverter.asTextDocumentIdentifier(document),
        ranges: ranges.map((range) => this.languageClient.code2ProtocolConverter.asRange(range)),
      },
      token,
    );
    if (files === null || files.length === 0 || token.isCancellationRequested) {
      return;
    }
    const copied: Copied = { resource: document.uri.toString(), files };
    dataTransfer.set(COPIED_SOURCES, new vscode.DataTransferItem(JSON.stringify(copied)));
  }

  public async provideDocumentPasteEdits(
    document: vscode.TextDocument,
    _ranges: readonly vscode.Range[],
    dataTransfer: vscode.DataTransfer,
    _context: vscode.DocumentPasteEditContext,
    token: vscode.CancellationToken,
  ): Promise<vscode.DocumentPasteEdit[] | undefined> {
    const text = await dataTransfer.get("text/plain")?.asString();
    const kept = await dataTransfer.get(COPIED_SOURCES)?.asString();
    if (text === undefined || kept === undefined || token.isCancellationRequested) {
      return undefined;
    }
    let copied: Copied;
    try {
      copied = JSON.parse(kept) as Copied;
    } catch {
      return undefined;
    }
    if (copied.resource === document.uri.toString()) {
      return undefined;
    }
    const edits = await this.languageClient.sendRequest<TextEdit[] | null>(
      "gandr/importFiles",
      {
        textDocument: this.languageClient.code2ProtocolConverter.asTextDocumentIdentifier(document),
        files: copied.files,
      },
      token,
    );
    const converted = await this.languageClient.protocol2CodeConverter.asTextEdits(edits, token);
    if (converted === undefined || converted.length === 0) {
      return undefined;
    }
    const paste = new vscode.DocumentPasteEdit(text, "Paste with gandr imports", IMPORT_PASTE);
    paste.additionalEdit = new vscode.WorkspaceEdit();
    paste.additionalEdit.set(document.uri, converted);
    paste.yieldTo = [vscode.DocumentDropOrPasteEditKind.Text.append("plain")];
    return [paste];
  }
}
