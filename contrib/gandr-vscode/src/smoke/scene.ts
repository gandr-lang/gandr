// The scene the end-to-end smoke plays inside a real VS Code: the extension
// activates, a corpus source opens, a definition is typed into it, and a
// hover over the typed name is answered once, in the server's HTML markup.
//
// Activation is #290's witness: an override of `start()` that pushed the
// configuration re-entered `start()` without bound, and the extension host
// hung before it resolved. The hover is #347's: the client announces
// `supportHtml`, so the server colours the hover by role, one `<span>` per
// run, inside `<pre><code>`; a client without it gets a Markdown fence. The
// server that answers is #3538's: VS Code keeps the runner's environment, so
// the `gandr` the runner puts first on `PATH` serves, not one the login
// shell finds first.

import * as assert from "node:assert/strict";
import * as vscode from "vscode";

// What the scene types at the end of the source: a definition naming the
// source's first, so its hover reads a type only the server can give.
const TYPED = "\ndef typed = greeting;";

export async function run(): Promise<void> {
  const source = process.env["GANDR_SMOKE_SOURCE"];
  assert.ok(source !== undefined, "the runner names the source the scene opens");
  const extension = vscode.extensions.getExtension("gandr-lang.gandr-vscode");
  assert.ok(extension !== undefined, "the extension under development is installed");
  await extension.activate();
  const document = await vscode.workspace.openTextDocument(source);
  const editor = await vscode.window.showTextDocument(document);
  const { end } = document.lineAt(document.lineCount - 1).range;
  editor.selection = new vscode.Selection(end, end);
  await vscode.commands.executeCommand("type", { text: TYPED });
  const typed = document.getText().indexOf("def typed");
  assert.notEqual(typed, -1, "the typed definition is in the document");
  const name = document.positionAt(typed + "def ".length);
  const hovers = await vscode.commands.executeCommand<vscode.Hover[]>(
    "vscode.executeHoverProvider",
    document.uri,
    name,
  );
  assert.equal(hovers.length, 1, "exactly one hover answers the typed name");
  const [hover] = hovers;
  assert.ok(hover !== undefined);
  assert.equal(hover.contents.length, 1, "the hover carries one piece of content");
  const [content] = hover.contents;
  assert.ok(content instanceof vscode.MarkdownString, "the hover's content is Markdown");
  assert.equal(content.supportHtml, true, "the client renders the hover's HTML");
  assert.match(content.value, /^<pre><code>/u, "the server wrote the hover as HTML");
  assert.match(
    content.value,
    /<span style="color:var\(--vscode-gandr-hover-[A-Za-z]+\);">typed<\/span>/u,
    "the typed name is coloured by its role",
  );
  assert.match(content.value, />String<\/span>/u, "the hover names the type the server judged");
}
