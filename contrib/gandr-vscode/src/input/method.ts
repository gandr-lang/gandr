// The unicode input method: a `\`-command written in a document whose
// language enables `gandr.inputMethod.enabled` is offered its glyphs through
// the suggest widget, beside the commands that continue it. Accepting a glyph
// replaces the command; accepting a continuation writes it and asks again;
// space accepts the selected suggestion while the method's list shows.

import * as vscode from "vscode";

import { entries } from "./table";
import { build, commandAt, continuations, type Node } from "./trie";

const ACTIVE = "gandr.inputMethod.active";

export function registerInputMethod(context: vscode.ExtensionContext): void {
  const commands = entries();
  const root = build(commands);
  const triggers = new Set<string>(["\\"]);
  for (const [command] of commands) {
    for (const point of command) if (!/[\p{L}\p{N}]/u.test(point)) triggers.add(point);
  }
  let active = false;
  const activate = (value: boolean): void => {
    if (value === active) return;
    active = value;
    void vscode.commands.executeCommand("setContext", ACTIVE, value);
  };
  const provider: vscode.CompletionItemProvider = {
    provideCompletionItems(document, position) {
      const enabled = vscode.workspace
        .getConfiguration("gandr.inputMethod", document)
        .get<boolean>("enabled", false);
      const line = document.lineAt(position.line).text.slice(0, position.character);
      const found = enabled ? commandAt(root, line) : undefined;
      activate(found !== undefined);
      if (found === undefined) return undefined;
      const range = new vscode.Range(position.line, found.start, position.line, position.character);
      return new vscode.CompletionList(items(found.node, found.command, range), true);
    },
  };
  context.subscriptions.push(
    vscode.languages.registerCompletionItemProvider(
      [{ scheme: "file" }, { scheme: "untitled" }],
      provider,
      ...triggers,
    ),
  );
}

// The glyphs `command` offers, the first preselected, then the commands
// continuing it, each of which asks again once accepted.
function items(node: Node, command: string, range: vscode.Range): vscode.CompletionItem[] {
  const offered: vscode.CompletionItem[] = node.glyphs.map((glyph, index) => {
    const item = new vscode.CompletionItem(
      { label: glyph, description: command },
      vscode.CompletionItemKind.Text,
    );
    item.detail = Array.from(glyph)
      .map(
        (point) => `U+${(point.codePointAt(0) ?? 0).toString(16).toUpperCase().padStart(4, "0")}`,
      )
      .join(" ");
    item.insertText = glyph;
    item.filterText = command;
    item.range = range;
    item.sortText = `0${String(index).padStart(4, "0")}`;
    item.preselect = index === 0;
    return item;
  });
  continuations(node, command).forEach((continuation, index) => {
    const more = continuation.reachable > continuation.sample.length ? " …" : "";
    const item = new vscode.CompletionItem(
      { label: continuation.command, description: `${continuation.sample.join(" ")}${more}` },
      vscode.CompletionItemKind.Folder,
    );
    item.detail = `${continuation.reachable} glyph${continuation.reachable === 1 ? "" : "s"}`;
    item.insertText = continuation.command;
    item.filterText = continuation.command;
    item.range = range;
    item.sortText = `1${String(index).padStart(4, "0")}`;
    item.command = { command: "editor.action.triggerSuggest", title: "Continue the command" };
    offered.push(item);
  });
  return offered;
}
