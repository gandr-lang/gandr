import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import * as oniguruma from "vscode-oniguruma";
import * as textmate from "vscode-textmate";

// The grammars as the manifest registers them, read with the tokenizer that
// VS Code uses. No editor window opens.

const root = join(__dirname, "..", "..");

interface Contributed {
  scopeName: string;
  path: string;
  injectTo?: string[];
}

const contributed = (
  JSON.parse(readFileSync(join(root, "package.json"), "utf8")) as {
    contributes: { grammars: Contributed[] };
  }
).contributes.grammars;

let loaded: Promise<textmate.IGrammar> | undefined;

function gandr(): Promise<textmate.IGrammar> {
  loaded ??= load();
  return loaded;
}

async function load(): Promise<textmate.IGrammar> {
  const wasm = readFileSync(require.resolve("vscode-oniguruma/release/onig.wasm"));
  await oniguruma.loadWASM(wasm.buffer.slice(wasm.byteOffset, wasm.byteOffset + wasm.byteLength));
  const registry = new textmate.Registry({
    onigLib: Promise.resolve({
      createOnigScanner: (sources: string[]) => new oniguruma.OnigScanner(sources),
      createOnigString: (text: string) => new oniguruma.OnigString(text),
    }),
    loadGrammar: (scope: string) => {
      const grammar = contributed.find((entry) => entry.scopeName === scope);
      if (grammar === undefined) return Promise.resolve(null);
      const path = join(root, grammar.path);
      return Promise.resolve(textmate.parseRawGrammar(readFileSync(path, "utf8"), path));
    },
    getInjections: (scope: string) =>
      contributed
        .filter((entry) => entry.injectTo?.includes(scope) === true)
        .map((entry) => entry.scopeName),
  });
  const grammar = await registry.loadGrammar("source.gandr");
  assert.ok(grammar !== null, "the manifest registers source.gandr");
  return grammar;
}

/** Each token of each line: its text and its innermost scopes, the root left out. */
async function scoped(lines: string[]): Promise<[string, string[]][][]> {
  const grammar = await gandr();
  let stack = textmate.INITIAL;
  return lines.map((line) => {
    const result = grammar.tokenizeLine(line, stack);
    stack = result.ruleStack;
    return result.tokens.map((token): [string, string[]] => [
      line.slice(token.startIndex, token.endIndex),
      token.scopes.slice(1),
    ]);
  });
}

/** The scopes of the first token on `line` whose text is `text`. */
function scopesOf(line: [string, string[]][] | undefined, text: string): string[] | undefined {
  return line?.find(([written]) => written.trim() === text)?.[1];
}

const COMMENT = "comment.line.double-slash.gandr";
const PUNCTUATION = "punctuation.definition.comment.gandr";
const RAW = "markup.inline.raw.gandr";

void test("a line comment scopes as before", async () => {
  const [line, doc, inner] = await scoped(["// a comment", "/// a doc", "//! an inner doc"]);
  assert.deepEqual(line, [
    ["//", [COMMENT, PUNCTUATION]],
    [" a comment", [COMMENT]],
  ]);
  assert.deepEqual(scopesOf(doc, "/ a doc"), [COMMENT], "a doc comment is a line comment");
  assert.deepEqual(scopesOf(inner, "! an inner doc"), [COMMENT]);
});

void test("a line comment ends with its line", async () => {
  const [, code] = await scoped(["// one", "def x = 1 ;"]);
  assert.deepEqual(scopesOf(code, "def"), ["keyword.other.def.gandr"]);
});

void test("each code span takes the inline code style", async () => {
  const [line] = await scoped(["// see `apply` and `count[<]` here"]);
  assert.deepEqual(scopesOf(line, "apply"), [COMMENT, RAW]);
  assert.deepEqual(scopesOf(line, "count[<]"), [COMMENT, RAW]);
  assert.deepEqual(scopesOf(line, "and"), [COMMENT], "the text between spans is comment text");
  assert.deepEqual(scopesOf(line, "here"), [COMMENT], "a closing backquote opens no span");
});

void test("a span across comment lines closes at its backquote", async () => {
  const [first, second, code] = await scoped(["// a `long", "// span` after", "def x = 1 ;"]);
  assert.deepEqual(scopesOf(first, "long"), [COMMENT, RAW]);
  assert.deepEqual(scopesOf(second, "//"), [COMMENT, RAW, PUNCTUATION]);
  assert.deepEqual(scopesOf(second, "span"), [COMMENT, RAW]);
  assert.deepEqual(scopesOf(second, "after"), [COMMENT]);
  assert.deepEqual(scopesOf(code, "def"), ["keyword.other.def.gandr"]);
});

void test("a span left open ends at a line that is not a comment", async () => {
  const [, code] = await scoped(["// an `open span", "def x = 1 ;"]);
  assert.deepEqual(scopesOf(code, "def"), ["keyword.other.def.gandr"]);
});

void test("a block comment's span takes the inline code style", async () => {
  const [line] = await scoped(["/* see `x` here */"]);
  assert.deepEqual(scopesOf(line, "x"), ["comment.block.gandr", RAW]);
  assert.deepEqual(scopesOf(line, "here"), ["comment.block.gandr"]);
});
