import type {
  ClientCapabilities,
  FeatureState,
  Range,
  StaticFeature,
} from "vscode-languageclient/node";

import * as vscode from "vscode";

import type { GandrLanguageClient } from "./lsp/client";

// The notification that carries a document's kernel tiers, gandr's own.
export const KERNEL_TIERS = "gandr/kernelTiers";

// The five warrants of gandr's visual language. Each one has one glyph and
// one colour id, and the extension draws no other colour for a tier.
const WARRANTS = {
  pending: "·",
  checked: "✓",
  replayed: "✓✓",
  refused: "✗",
  withheld: "○",
} as const;

type Warrant = keyof typeof WARRANTS;

// One declaration's mark, as the server sends it.
interface TierMark {
  range: Range;
  warrant: Warrant;
  glyph: string;
  title: string;
}

// The kernel tiers of one document at the version whose admission ended.
interface KernelTiersParams {
  uri: string;
  version: number;
  tiers: TierMark[];
}

// The client declares `experimental.kernelTiers`, so the server sends the
// tiers when each admission ends. A client that does not declare it is sent
// nothing.
export class KernelTiersFeature implements StaticFeature {
  public fillClientCapabilities(capabilities: ClientCapabilities): void {
    const experimental =
      typeof capabilities.experimental === "object" && capabilities.experimental !== null
        ? capabilities.experimental
        : {};
    capabilities.experimental = { ...experimental, kernelTiers: true };
  }

  public getState(): FeatureState {
    return { kind: "static" };
  }

  public initialize(): void {}

  public clear(): void {}
}

// The tiers each open document last received, with the line of each mark
// moved by the edits since. A document whose version moved past its tiers
// draws every mark in the `pending` warrant, until its next admission ends.
class Tiers {
  private readonly held = new Map<string, { version: number; marks: TierMark[] }>();

  private readonly kinds: Map<Warrant, vscode.TextEditorDecorationType>;

  public constructor() {
    this.kinds = new Map(
      Object.entries(WARRANTS).map(([warrant, glyph]) => {
        const colour = new vscode.ThemeColor(`gandr.warrant.${warrant}`);
        return [
          warrant as Warrant,
          vscode.window.createTextEditorDecorationType({
            before: { contentText: glyph, color: colour, margin: "0 1ch 0 0" },
            overviewRulerColor: colour,
            overviewRulerLane: vscode.OverviewRulerLane.Left,
            rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
          }),
        ];
      }),
    );
  }

  public dispose(): void {
    for (const kind of this.kinds.values()) {
      kind.dispose();
    }
  }

  public received(params: KernelTiersParams): void {
    this.held.set(params.uri, { version: params.version, marks: params.tiers });
    this.drawAll(params.uri);
  }

  // Move each mark below an edit by the lines the edit adds or removes. A
  // mark inside an edited range stays at its line.
  public changed(event: vscode.TextDocumentChangeEvent): void {
    const uri = event.document.uri.toString();
    const held = this.held.get(uri);
    if (held === undefined) {
      return;
    }
    for (const change of event.contentChanges) {
      const added = change.text.split("\n").length - 1;
      const removed = change.range.end.line - change.range.start.line;
      const moved = added - removed;
      if (moved === 0) {
        continue;
      }
      for (const mark of held.marks) {
        if (mark.range.start.line > change.range.end.line) {
          const line = mark.range.start.line + moved;
          mark.range = {
            start: { line, character: 0 },
            end: { line, character: 0 },
          };
        }
      }
    }
    this.drawAll(uri);
  }

  public closed(document: vscode.TextDocument): void {
    this.held.delete(document.uri.toString());
  }

  public draw(editor: vscode.TextEditor): void {
    const held = this.held.get(editor.document.uri.toString());
    const stale = held === undefined || held.version !== editor.document.version;
    for (const [warrant, kind] of this.kinds) {
      const marks = (held?.marks ?? []).filter(
        (mark) => (stale ? "pending" : mark.warrant) === warrant,
      );
      editor.setDecorations(
        kind,
        marks.map((mark) => ({
          range: new vscode.Range(mark.range.start.line, 0, mark.range.start.line, 0),
          hoverMessage: mark.title,
        })),
      );
    }
  }

  private drawAll(uri: string): void {
    for (const editor of vscode.window.visibleTextEditors) {
      if (editor.document.uri.toString() === uri) {
        this.draw(editor);
      }
    }
  }
}

// Draw a glyph beside each declaration of a gandr editor, in its tier's
// warrant: the glyph and its colour carry the warrant, and the hover over it
// carries the lens's title. The checker answers on each keystroke. The kernel
// replays the declarations after it, off the keystroke path, and the glyph
// changes when that admission ends. The glyph is a text decoration before the
// first line, because a gutter icon is an image and takes no theme colour.
export function registerKernelTiers(
  context: vscode.ExtensionContext,
  client: GandrLanguageClient,
): void {
  const tiers = new Tiers();
  context.subscriptions.push(
    tiers,
    client.onNotification(KERNEL_TIERS, (params: KernelTiersParams) => tiers.received(params)),
    vscode.workspace.onDidChangeTextDocument((event) => tiers.changed(event)),
    vscode.workspace.onDidCloseTextDocument((document) => tiers.closed(document)),
    vscode.window.onDidChangeVisibleTextEditors((editors) => {
      for (const editor of editors) {
        tiers.draw(editor);
      }
    }),
  );
}
