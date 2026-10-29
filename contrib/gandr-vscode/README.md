# gandr for Visual Studio Code

Language support for `.gandr` sources. The extension registers the `gandr` language and starts the gandr language server, `gandr lsp`, over standard input and output for every `.gandr` file opened from disk. The server publishes the diagnostics `gandr check` prints, answers semantic-token requests with the highlighter's roles, and answers hovers with types coloured by the same roles. A small TextMate grammar colors comments and a few keywords until the server's tokens arrive.

## Contents

- [Requirements](#requirements)
- [Install the gandr binary](#install-the-gandr-binary)
- [Install the extension](#install-the-extension)
- [Check the connection](#check-the-connection)
- [Hover colours](#hover-colours)
- [Drop to import](#drop-to-import)
- [Paste with imports](#paste-with-imports)
- [Unicode input](#unicode-input)
- [Develop the extension](#develop-the-extension)

## Requirements

- Visual Studio Code 1.140 or later.
- `rustup`, which installs the toolchain the repository pins in `rust-toolchain.toml`.
- `mise`, which installs Node.js and the `aube` package manager at the versions `mise.toml` pins.
- A trusted workspace: the extension runs a local binary, so it stays disabled in Restricted Mode.

## Install the gandr binary

The extension runs `gandr` from `PATH`. Install it from a clone of the repository:

```sh
git clone https://github.com/gandr-lang/gandr
cd gandr
cargo install --locked --path crates/surface-driver
```

The driver's package is `gandr-lang`; it installs one binary, `gandr`, into Cargo's binary directory, `~/.cargo/bin` unless `CARGO_HOME` moves it. Confirm that the directory is on `PATH` and that the server starts:

```sh
gandr --version
gandr lsp --capabilities
```

The second command prints the server's capabilities as one line of JSON. Rerun `cargo install` after pulling to update the binary; a running editor picks it up after **Developer: Restart Extension Host** or a window reload.

## Install the extension

From the repository root, install the tools and the aube workspace, then package the extension:

```sh
mise install
mise exec -- aube install --frozen-lockfile
cd contrib/gandr-vscode
mise exec -- aube run package
```

`aube run package` type-checks the sources with `tsc`, bundles them with the language client into `dist/extension.js`, and writes `gandr-vscode-0.1.0.vsix`. Install the package:

```sh
code --install-extension gandr-vscode-0.1.0.vsix
```

**Extensions: Install from VSIX…** in the Command Palette does the same. Reinstall the same way after rebuilding; `code --uninstall-extension gandr-lang.gandr-vscode` removes it.

## Check the connection

Open a folder that contains a `.gandr` file, then open the file. The extension activates for the `gandr` language and for any workspace containing a `.gandr` file. A source with an unresolved name shows the refusal in the editor and in the Problems panel:

```gandr
def answer = 42 ;
def broken = missing ;
```

The **gandr language server** output channel (**View: Toggle Output**) carries the server's standard error, one timing line per synchronisation. When the server fails to start, the channel names the error; the usual cause is `gandr` missing from the `PATH` that Visual Studio Code inherited. On macOS, quit and relaunch the editor after changing the shell profile. To log every protocol message, set the **gandr language server trace** channel's log level to Trace with **Developer: Set Log Level…**; `"gandr.trace.server": "verbose"` in the user settings adds each message's parameters.

No setting selects the server's features. The client adopts what `initialize` advertises: incremental document synchronisation, so an edit sends only the changed range, and semantic tokens for the whole document and for a range.

`gandr.diagnostics.verbosity` chooses how much of each report a diagnostic shows, at the levels `gandr check --verbosity` names: `user`, the default, shows the message, the label and the note; `detailed` adds the report's class, the checker's own wording and the offending source text; `debug` adds every locus's byte span and the checker's refusal as its implementers print it; `json` shows the whole report as one line of JSON. Changing it republishes the open files' diagnostics at the new level.

`gandr.diagnostics.quiet` keeps the form you are typing free of red: a diagnostic of the form the cursor is in waits until the cursor leaves the form, the form's `;` or `}` arrives, or the file goes that many seconds without a change, 1.5 by default. A diagnostic elsewhere in the file shows at once. `0` shows every diagnostic at once.

`gandr.inlineCompletion.trigger` chooses when the syntax the parser expects next shows as ghost text. `invoked`, the default, shows it only when asked for with **Trigger Inline Suggestion** (`Alt+\`), so typing never fills the line ahead of the cursor. `automatic` shows it as you type.

`gandr.presentation.form` chooses how a hover spells a type. `sugared`, the default, writes every sugar the surface reads where the type has its shape: `Integer => String` for `+U (Integer -> -F String)`, `A * B`, `A + B`, `C & D`, and `(a, b)` for a tuple. `explicit` writes the formers the core is made of. **gandr: Toggle sugared/explicit types** in the Command Palette flips it and hovers again at the cursor.

`gandr.presentation.spelling` chooses how hovers and diagnostics write a construct that has a glyph: `unicode` writes `≃`, `≅`, `⇝` and `∷`; `ascii` writes `<~>`, `Iso(A, B)`, `~~>` and `::`. Unset, the default, the server follows `presentation.spelling` in the user's `gandr/config.toml`, else Unicode. Changing it republishes the open files' diagnostics in the new spelling.

## Hover colours

The server colours a hover by the roles its semantic tokens carry: the extension's client announces that its hovers render HTML, and the server writes each type, name and checked fill as `<pre><code>` with every classified run in a `span` coloured by a theme colour the extension contributes. Each colour defaults, per theme kind, to what the built-in theme of that kind gives the role's semantic token, so a hover reads as the line it describes. Override any of them under `workbench.colorCustomizations`. A run the highlighter classifies as `other`, such as the `:` of a signature, is left in the hover's foreground, as the editor leaves it.

| Role | Colour | Semantic token | Dark Modern | Light Modern | Dark High Contrast | Light High Contrast |
| ---- | ------ | -------------- | ----------- | ------------ | ------------------ | ------------------- |
| keyword | `gandr.hover.keyword` | `keyword` | `#C586C0` | `#AF00DB` | `#C586C0` | `#B5200D` |
| boolean | `gandr.hover.boolean` | `keyword` | `#C586C0` | `#AF00DB` | `#C586C0` | `#B5200D` |
| operator | `gandr.hover.operator` | `operator` | `#D4D4D4` | `#000000` | `#D4D4D4` | `#000000` |
| functionDef | `gandr.hover.functionDef` | `function` | `#DCDCAA` | `#795E26` | `#DCDCAA` | `#5E2CBC` |
| functionCall | `gandr.hover.functionCall` | `function` | `#DCDCAA` | `#795E26` | `#DCDCAA` | `#5E2CBC` |
| variableDef | `gandr.hover.variableDef` | `variable` | `#9CDCFE` | `#001080` | `#9CDCFE` | `#001080` |
| variable | `gandr.hover.variable` | `variable` | `#9CDCFE` | `#001080` | `#9CDCFE` | `#001080` |
| variableParam | `gandr.hover.variableParam` | `parameter` | `#9CDCFE` | `#001080` | `#9CDCFE` | `#001080` |
| member | `gandr.hover.member` | `property` | `#9CDCFE` | `#001080` | `#9CDCFE` | `#001080` |
| constructor | `gandr.hover.constructor` | `enumMember` | `#4FC1FF` | `#0070C1` | `#9CDCFE` | `#02715D` |
| type | `gandr.hover.type` | `type` | `#4EC9B0` | `#267F99` | `#4EC9B0` | `#185E73` |
| typeBuiltin | `gandr.hover.typeBuiltin` | `type.defaultLibrary` | `#4EC9B0` | `#267F99` | `#4EC9B0` | `#185E73` |
| typeVariable | `gandr.hover.typeVariable` | `typeParameter` | `#4EC9B0` | `#267F99` | `#4EC9B0` | `#185E73` |
| number | `gandr.hover.number` | `number` | `#B5CEA8` | `#098658` | `#B5CEA8` | `#096D48` |
| stringLit | `gandr.hover.stringLit` | `string` | `#CE9178` | `#A31515` | `#CE9178` | `#0F4A85` |
| character | `gandr.hover.character` | `string` | `#CE9178` | `#A31515` | `#CE9178` | `#0F4A85` |
| escape | `gandr.hover.escape` | `string` | `#CE9178` | `#A31515` | `#CE9178` | `#0F4A85` |
| path | `gandr.hover.path` | `string` | `#CE9178` | `#A31515` | `#CE9178` | `#0F4A85` |
| comment | `gandr.hover.comment` | `comment` | `#6A9955` | `#008000` | `#7CA668` | `#515151` |
| hole | `gandr.hover.hole` | `macro` | `#569CD6` | `#0000FF` | `#DCDCAA` | `#0F4A85` |
| directive | `gandr.hover.directive` | `macro` | `#569CD6` | `#0000FF` | `#DCDCAA` | `#0F4A85` |
| label | `gandr.hover.label` | `label` | hover foreground | hover foreground | hover foreground | hover foreground |

## Drop to import

Drag `.gandr` files from the Explorer into a gandr editor, holding Shift, and each source the document does not import yet is imported: the server writes an `import "…" ;` line for it after the document's last import, or at its start when it has none, addressed from the document's directory. Nothing is written where the files were dropped. A drop of only sources the document imports already falls back to the editor's own drop.

## Paste with imports

Copy text from one gandr editor and paste it into another, and the paste control offers _Paste with gandr imports_: the pasted text, plus an `import "…" ;` line for each source declaring a name it uses that the document does not import yet. A name declared in the text copied, or bound inside it, needs no import. The editor's plain paste stays the default; set `"editor.pasteAs.preferences": ["text.updateImports.gandr"]` to make the imports the default. A paste into the document copied from adds nothing.

## Unicode input

Type a `\`-command and the suggest list offers its glyphs: `\to` offers `→`, `\lambda` `λ`, `\::` `∷`. A command that others continue lists them beneath its glyphs, each with the glyphs it leads to: accepting `\r-` writes the command and asks again, so a fork completes one step at a time. Space, Enter or Tab accepts the selected suggestion, a glyph replacing the command; a space typed after a command that offers glyphs accepts its first, so write a lambda's binder as `\x.`, as the formatter does. The method is on for gandr; `"[gandr]": { "gandr.inputMethod.enabled": false }` turns it off, and the same setting under another language turns it on there.

The commands are Agda's input method and the TeX names it inherits, read from public sources each pinned by digest: Agda's `agda-input.el` (MIT), the W3C character entity list's LaTeX and unicode-math names (W3C Software Notice and License), and the commands the LaTeX kernel declares at one symbol, such as `\to` beside `\rightarrow` (LPPL). `src/input/table.json` names them with their licences; `node scripts/input-table.mts src/input/table.json` regenerates it, and `mise run check:input-table` fails while the committed table differs.

## Develop the extension

`mise exec -- aube run watch` recompiles on every change into `dist/src`.

Formatting and linting run with the repository's treefmt pass: oxfmt formats the TypeScript and JSON, and type-aware oxlint applies its rules and the TypeScript checker under the strict `tsconfig.json`. `mise run check:extension` from the repository root type-checks, lints, compiles, runs the `node:test` suites under `src/`, bundles, and packages the extension; a deprecation fails that gate.

`mise run check:vscode-smoke` runs the end-to-end smoke after that gate, and it is the extension's only surface check. VS Code at the manifest's floor, downloaded once into `~/.cache/gandr/vscode`, starts without a display on a scratch copy of `corpus/model/basics/definitions.gandr` with this extension alone, served by the `gandr` the workspace builds. The scene in `src/smoke/scene.ts` activates the extension, types a definition, and holds its hover to exactly one answer in the server's HTML. The smoke runs only on Linux in GitHub Actions, where the editor starts headless. Anywhere else the task exits at once and names #3696, so no workstation opens an editor window. Hosted CI does not run it yet, as its image carries no Electron runtime.
