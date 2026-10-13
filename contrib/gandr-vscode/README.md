# gandr for Visual Studio Code

Language support for `.gandr` sources. The extension registers the `gandr` language and starts the gandr language server, `gandr lsp`, over standard input and output for every `.gandr` file opened from disk. The server publishes the diagnostics `gandr check` prints and answers semantic-token requests with the highlighter's roles. A small TextMate grammar colors comments and a few keywords until the server's tokens arrive.

## Contents

- [Requirements](#requirements)
- [Install the gandr binary](#install-the-gandr-binary)
- [Install the extension](#install-the-extension)
- [Check the connection](#check-the-connection)
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

`aube run package` type-checks the sources with `tsc`, bundles them with the language client into `dist/extension.js`, and writes `gandr-vscode-0.0.0.vsix`. Install the package:

```sh
code --install-extension gandr-vscode-0.0.0.vsix
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

## Develop the extension

`mise exec -- aube run watch` recompiles on every change into `dist/src`. To run the extension without installing it, bundle once and start an Extension Development Host:

```sh
mise exec -- aube run vscode:prepublish
code --extensionDevelopmentPath="$PWD"
```

Formatting and linting run with the repository's treefmt pass: oxfmt formats the TypeScript and JSON, and type-aware oxlint applies its rules and the TypeScript checker under the strict `tsconfig.json`. `mise run check:extension` from the repository root type-checks, lints, bundles, and packages the extension; a deprecation fails that gate.
