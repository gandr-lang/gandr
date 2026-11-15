// Generate the input method's command table, `src/input/table.json`, from
// three pinned sources read by digest: Agda's own translations, the W3C
// character entity list's LaTeX and unicode-math names, and the LaTeX
// kernel's math symbol declarations. The composition is Agda's: its own
// translations first, the TeX names appended under `agda-input-inherit`'s
// tweak (the `\` prefix dropped, `^` and `_` keys kept but for `^l`, `^o`,
// `^r` and `^v`, five keys dropped), every key then given its `\`.
//
// node contrib/gandr-vscode/scripts/input-table.ts <output file>
//
// Each source is fetched once into `target/input-sources/<sha256>` and refused
// if its digest differs from the pin.

import { createHash } from "node:crypto";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

interface Source {
  readonly name: string;
  readonly revision: string;
  readonly url: string;
  readonly sha256: string;
  readonly licence: string;
  readonly notice: string;
}

const AGDA: Source = {
  name: "Agda's input method, agda-input.el",
  revision: "v2.8.0.2",
  url: "https://raw.githubusercontent.com/agda/agda/v2.8.0.2/src/data/emacs-mode/agda-input.el",
  sha256: "21666bf0fd5290f93d2c7c86098fad3d31744779544150aa6e146d636cfe5fbb",
  licence: "MIT",
  notice:
    'Copyright (c) 2005-2026 remains with the authors. Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions: The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software. THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.',
};

const W3C: Source = {
  name: "W3C XML entity definitions for characters, unicode.xml",
  revision: "0f766d761eebd0908b4f2cfaa30cf9b06bdc79b0",
  url: "https://raw.githubusercontent.com/w3c/xml-entities/0f766d761eebd0908b4f2cfaa30cf9b06bdc79b0/unicode.xml",
  sha256: "8ad442b9360ea43f3ba0704f033c4e6db4c15356184838d000a4ac12182fb935",
  licence: "W3C Software Notice and License",
  notice:
    "Copyright David Carlisle 1999-2025. W3C Software Notice and License, http://www.w3.org/Consortium/Legal/2002/copyright-software-20021231.html. Changed: the characters' LaTeX and unicode-math names and their Unicode names are read and reshaped into this table's commands.",
};

const LATEX: Source = {
  name: "The LaTeX kernel's math symbol declarations, fontdef.dtx",
  revision: "release-2026-06-01",
  url: "https://raw.githubusercontent.com/latex3/latex2e/release-2026-06-01/base/fontdef.dtx",
  sha256: "a3376423114232dc36439df7388b588d5b3bc42655d31f87800bb55fb0109dc4",
  licence: "LPPL-1.3c",
  notice:
    "The LaTeX Project Public License, version 1.3c, https://www.latex-project.org/lppl.txt. Read: which command names the kernel declares at one symbol slot, nothing of the file reproduced.",
};

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..", "..", "..");

async function read(source: Source): Promise<string> {
  const cache = join(ROOT, "target", "input-sources");
  const path = join(cache, source.sha256);
  if (!existsSync(path)) {
    const response = await fetch(source.url);
    if (!response.ok) throw new Error(`${source.url}: ${response.status}`);
    mkdirSync(cache, { recursive: true });
    writeFileSync(path, Buffer.from(await response.arrayBuffer()));
  }
  const bytes = readFileSync(path);
  const digest = createHash("sha256").update(bytes).digest("hex");
  if (digest !== source.sha256) {
    throw new Error(`${source.name}: sha256 ${digest}, pinned ${source.sha256}`);
  }
  return bytes.toString("utf8");
}

// An s-expression of the elisp subset the translations are written in.
type Sexp = string | { readonly symbol: string } | { readonly unquote: Sexp } | readonly Sexp[];

function readSexp(text: string, at: { i: number }): Sexp {
  for (;;) {
    const c = text[at.i];
    if (c === undefined) throw new Error("unexpected end of the translations");
    if (c === ";") {
      while (at.i < text.length && text[at.i] !== "\n") at.i++;
    } else if (/\s/.test(c)) {
      at.i++;
    } else {
      break;
    }
  }
  const c = text[at.i];
  if (c === "(") {
    at.i++;
    const items: Sexp[] = [];
    for (;;) {
      while (at.i < text.length && /\s/.test(text[at.i] ?? "")) at.i++;
      if (text[at.i] === ";") {
        while (at.i < text.length && text[at.i] !== "\n") at.i++;
        continue;
      }
      if (text[at.i] === ")") {
        at.i++;
        return items;
      }
      items.push(readSexp(text, at));
    }
  }
  if (c === '"') {
    at.i++;
    let value = "";
    for (;;) {
      const d = text[at.i++];
      if (d === undefined) throw new Error("unterminated string");
      if (d === '"') return value;
      if (d === "\\") {
        const e = text[at.i++];
        if (e === undefined) throw new Error("unterminated escape");
        value += e === "n" ? "\n" : e === "t" ? "\t" : e;
      } else {
        value += d;
      }
    }
  }
  if (c === ",") {
    at.i++;
    return { unquote: readSexp(text, at) };
  }
  if (c === "`" || c === "'") {
    at.i++;
    return readSexp(text, at);
  }
  const start = at.i;
  while (at.i < text.length && !/[\s()"]/.test(text[at.i] ?? "")) at.i++;
  return { symbol: text.slice(start, at.i) };
}

// `agda-input-to-string-list`: each character of the string but spaces and
// line breaks.
function toStringList(s: string): string[] {
  return Array.from(s).filter((c) => c !== " " && c !== "\n");
}

function agdaTranslations(source: string): [string, string[]][] {
  const head = source.indexOf("(defcustom agda-input-translations");
  const open = source.indexOf("`(", head);
  if (head < 0 || open < 0) throw new Error("agda-input-translations not found");
  const list = readSexp(source, { i: open + 1 });
  if (!Array.isArray(list)) throw new Error("agda-input-translations is not a list");
  return list.map((pair: Sexp): [string, string[]] => {
    if (!Array.isArray(pair) || pair.length !== 3) {
      throw new Error(`unread pair ${JSON.stringify(pair)}`);
    }
    const key: Sexp | undefined = pair[0];
    const value: Sexp | undefined = pair[2];
    if (value === undefined) throw new Error(`unread pair ${JSON.stringify(pair)}`);
    if (typeof key !== "string") throw new Error(`unread key ${JSON.stringify(key)}`);
    if (Array.isArray(value)) {
      return [key, value.map((glyph) => (typeof glyph === "string" ? glyph : String(glyph)))];
    }
    if (typeof value === "object" && "unquote" in value) {
      const call = value.unquote;
      if (Array.isArray(call) && call.length === 2 && typeof call[1] === "string") {
        return [key, toStringList(call[1])];
      }
    }
    throw new Error(`unread translation of ${key}`);
  });
}

interface Character {
  readonly glyph: string;
  readonly name: string;
  readonly latex: readonly string[];
  readonly unicodeMath: readonly string[];
}

function characters(xml: string): Character[] {
  const read: Character[] = [];
  for (const m of xml.matchAll(
    /<character\b[^>]*\bid="U([0-9A-F-]+)"[^>]*>([\s\S]*?)<\/character>/g,
  )) {
    const [, id = "", body = ""] = m;
    const points = id.split("-").map((hex) => Number.parseInt(hex, 16));
    const glyph = String.fromCodePoint(...points);
    const name = body.match(/<description[^>]*>([^<]*)<\/description>/)?.[1]?.trim() ?? "";
    const latex = [...body.matchAll(/<latex>([^<]*)<\/latex>/g)].map((l) => (l[1] ?? "").trim());
    const unicodeMath = [
      ...body.matchAll(/<mathlatex set="unicode-math">([^<]*)<\/mathlatex>/g),
    ].map((l) => (l[1] ?? "").trim());
    read.push({ glyph, name, latex, unicodeMath });
  }
  return read;
}

const COMMAND = /^\\[A-Za-z]+$/;
const ACCENT = /^\\([^A-Za-z\s{}])\{([A-Za-z])\}$/;
const LETTER_ACCENT = /^\\([A-Za-z])\{([A-Za-z])\}$/;

// The TeX keys, each without its `\`, with the glyphs they name.
function texKeys(chars: readonly Character[], kernel: string): [string, string][] {
  const keys: [string, string][] = [];
  const commandOf = new Map<string, string>();
  const glyphOf = new Map<string, string>();
  for (const { glyph, latex, unicodeMath } of chars) {
    for (const spelling of [...latex, ...unicodeMath]) {
      if (COMMAND.test(spelling)) {
        keys.push([spelling.slice(1), glyph]);
        if (!commandOf.has(glyph)) commandOf.set(glyph, spelling);
        if (!glyphOf.has(spelling)) glyphOf.set(spelling, glyph);
        continue;
      }
      const accent = spelling.match(ACCENT);
      if (accent) {
        const [, mark = "", base = ""] = accent;
        keys.push([`${mark}{${base}}`, glyph], [`${mark}${base}`, glyph]);
        continue;
      }
      const letterAccent = spelling.match(LETTER_ACCENT);
      if (letterAccent) keys.push([spelling.slice(1), glyph]);
    }
  }
  // A command the kernel declares at the slot of one this list names.
  const slots = new Map<string, string[]>();
  for (const m of kernel.matchAll(
    /^\\DeclareMath(?:Symbol|Delimiter)\{?(\\[A-Za-z]+)\}?\{\\math[a-z]+\}\{([a-z]+)\}\{"([0-9A-F]+)\}/gm,
  )) {
    const slot = `${m[2]} ${m[3]}`;
    const commands = slots.get(slot) ?? [];
    commands.push(m[1] ?? "");
    slots.set(slot, commands);
  }
  for (const commands of slots.values()) {
    const glyph = commands.map((command) => glyphOf.get(command)).find((g) => g !== undefined);
    if (glyph === undefined) continue;
    for (const command of commands) if (!glyphOf.has(command)) keys.push([command.slice(1), glyph]);
  }
  // A subscript or superscript of a character the list spells: `_1`, `^\beta`.
  const byName = new Map<string, string>();
  for (const { glyph, name } of chars) {
    if (name !== "" && !byName.has(name)) byName.set(name, glyph);
  }
  for (const { glyph, name } of chars) {
    const m = name.match(/^(?:(.*) )?(SUBSCRIPT|SUPERSCRIPT) (.+)$/);
    if (!m) continue;
    const rest = [m[1], m[3]].filter((part) => part !== undefined).join(" ");
    const bases = [rest, `DIGIT ${rest}`, `HYPHEN-${rest}`, `${rest} SIGN`]
      .map((candidate) => byName.get(candidate))
      .filter((base) => base !== undefined);
    const spelled =
      bases.find((base) => (base.codePointAt(0) ?? 128) < 128) ??
      bases.map((base) => commandOf.get(base)).find((command) => command !== undefined);
    if (spelled === undefined) continue;
    keys.push([`${m[2] === "SUBSCRIPT" ? "_" : "^"}${spelled}`, glyph]);
  }
  return keys;
}

const DROPPED = new Set(["geq", "leq", "bullet", "qed", "par", "^l", "^o", "^r", "^v"]);

function compose(
  agda: readonly [string, string[]][],
  tex: readonly [string, string][],
): [string, string[]][] {
  const table = new Map<string, string[]>();
  const add = (key: string, glyph: string) => {
    if (key === "\\") return;
    const glyphs = table.get(key) ?? [];
    if (!glyphs.includes(glyph)) glyphs.push(glyph);
    table.set(key, glyphs);
  };
  for (const [key, glyphs] of agda) {
    if (key === "") continue;
    for (const glyph of glyphs) add(`\\${key}`, glyph);
  }
  for (const [key, glyph] of tex) {
    if (DROPPED.has(key) || Array.from(glyph).every((c) => (c.codePointAt(0) ?? 0) < 128)) continue;
    add(`\\${key}`, glyph);
  }
  return [...table].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
}

const [output] = process.argv.slice(2);
if (output === undefined) throw new Error("usage: input-table.mts <output file>");
const [agda, xml, kernel] = await Promise.all([read(AGDA), read(W3C), read(LATEX)]);
const table = compose(agdaTranslations(agda), texKeys(characters(xml), kernel));
const sources = [AGDA, W3C, LATEX].map((source) => `    ${JSON.stringify(source)}`).join(",\n");
const commands = table.map((entry) => `    ${JSON.stringify(entry)}`).join(",\n");
writeFileSync(
  output,
  `{\n  "sources": [\n${sources}\n  ],\n  "commands": [\n${commands}\n  ]\n}\n`,
);
