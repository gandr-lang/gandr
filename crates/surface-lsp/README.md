# gandr-surface-lsp

The gandr language server: diagnostics, semantic tokens, completion, signature help, inline completion, the document's outline, hover, definitions, and the checked fills a model proposes, over the Language Server Protocol, served over any pair of byte streams, or by one engine hub to every client of a workspace.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-lsp` serves a subset of the Language Server Protocol 3.17 and, from 3.18, `textDocument/inlineCompletion`: the base protocol's framing, the JSON-RPC 2.0 envelope with its standard error codes, the lifecycle from `initialize` to `exit`, incremental document synchronisation and the requests the coverage table in [`src/lib.rs`](src/lib.rs) lists method by method. `serve` runs one session over any `BufRead` and `Write` pair, logging one timing line per synchronisation to a third `Write`; `Capabilities` displays what `initialize` answers. On Unix, `run_hub` serves every connection a socket accepts over one shared set of open documents, `bind` and `socket_for` find the one hub per workspace, and `relay` carries a client's streams to it. The driver's `gandr lsp` relays standard input and output to the hub of the current directory, starting `gandr serve` when none runs; `gandr lsp --standalone` serves in its own process.

**Why.** An editor should show what `gandr check` prints, where it prints it, while the source is written. The server is a face over the pipeline's own outputs, never a second pipeline: its diagnostics are projections of the diagnostics `gandr-surface-diagnostics` builds for the dispatcher's step, the same ones the terminal lays out, and its tokens are the roles `gandr-surface-grammar`'s highlighter classifies, so an editor, a terminal and a test cannot disagree about a refusal or a token.

**How.** Each connection's copy of an open document holds a `gandr-surface-session` session under the source root its `file` URI's path classifies as. A synchronisation applies the client's changes to the connection's copy; the copy's session judges the text on the worker pool, off the serving loop, a later change retiring it, and the server reads the judgement's step through `gandr-surface-dispatcher`'s `entries` under `check --goals` and publishes each diagnostic the model builds as one LSP diagnostic, mapped field by field as [`recheck`](src/recheck.rs) tabulates. Then it runs the kernel admission the judgement left. The first structural request after a change parses the copy's text once, and that reading answers each of them until the next change ([`reading`](src/reading.rs)). Every request about a name reads the dispatcher's `TypeTable`, built once per edit. Formatting lays the held text out through `gandr-surface-format`.

## Provided features

- `serve` and `Served`: one session over a stream pair and a log, ending cleanly at `exit` or boundary EOF after `shutdown`, and abruptly before shutdown.
- A shared workspace: each connection that opens a document holds its own copy, answered and published for the text that connection holds, so two clients of one buffer each apply an edit once and two diverging editors are each answered for their own text; the copy that synchronised last is the one the other faces read, and the document is forgotten once the last holder closes it or leaves.
- `run_hub`, `bind`, `bind::Absent`, `socket_for` and `LINGER`, on Unix: one hub per workspace socket, every connection served over the shared workspace on its own threads, a killed client leaving the others served, and the hub removing its socket and returning once no client has connected for its linger.
- `relay`, on Unix: a client's frames carried to a hub and back, the session ending as a standalone one would.
- `Face`, on Unix: `run_hub`'s second face, handed every connection whose first byte is `{` rather than a frame's header, over the same workspace.
- `Workspace::held`, `Workspace::published`, `Workspace::watch` and `Workspace::query`: what another face reads off the shared workspace, each off the copy that synchronised last — the open documents and their versions, the diagnostics last published for each, a channel told of each publication and forgotten document, and any request the server answers, run on a connection that holds nothing.
- `Workspace::trial`, `Tried` and `Reached`, with `ContentChange`, `Range`, `Position`, `Line` and `Character`: candidate changes, each applied alone to the text of a held document's latest copy as a synchronisation applies it, judged by that copy's session's trial without submitting any and ranked best first, each with the diagnostics a synchronisation to its text would publish; every copy and its session unchanged.
- `Workspace::propose`, `Proposal` and `ProposalRefusal`: a model's fill of a range kept beside the document once it checks, refused when stale or failing, and withdrawn by the next synchronisation; kept fills served as ghost text, code lenses, code actions and hover notes.
- `RENDER_BUS_PREFACE`, `Workspace::greeting` and `Workspace::rendered`: the render bus on the hub's socket — a connection opening with the preface greeted with the held documents and sent each one's report, then the report of every publication; a resync answered at the current version, a detach closing it, another bus version detached at once.
- Incremental synchronisation: each content change applied in order and the document judged again in its session on the worker pool, molding only the forms the change touched; one log line per publication.
- Notebook synchronisation: a Jupyter `.ipynb` of `gandr` cells judged as one document, each cell published its own diagnostics ([`notebook`](src/notebook.rs)).
- `Server::admit`, `Server::admitted`, `Admissions` and `Awaiting`: the judgement each synchronisation leaves due, run on the worker pool and published once delivered, then the kernel admission it left, run once its diagnostics are published.
- `read_frame`, `read_frame::Absent`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing, with a ceiling on a header line and on a body.
- The envelope: requests, notifications and responses told apart; a body outside the decoder-supported JSON fragment answered with a parse error; a decoded batch or other invalid message refused as an invalid request.
- Published diagnostics: one per diagnostic the model builds for the document's step, at its lead range, under its code, with its message and related information; republished at every change, cleared at close. A client that pulls diagnostics is answered the same set when it asks, named by its digest, and asked to pull again when a recheck it did not ask for changes it.
- The `gandr.diagnostics.verbosity` and `quiet` settings, pushed or pulled: a new verbosity republishes open documents; `quiet` is how long a diagnostic of the form being typed waits ([`quiet`](src/quiet.rs)).
- Imports read an editor's copy before the disk: an edit, or a `.gandr` file or folder changed, created, deleted or renamed, rechecks each open document importing it.
- Semantic tokens for the whole document, as edits of the last answer, and for a range, each use typed by its referent; `TOKEN_TYPES` and `TOKEN_MODIFIERS`, the legend.
- Completion: the binders in scope, the import closure's names and the keywords the slot at the cursor admits, each starting with the word typed.
- Cancellation: a request withdrawn by a `$/cancelRequest`, or by a change of the document it reads, before it is handled is answered without being run ([`quiet`](src/quiet.rs)); one about a document being judged waits for its publication.
- Progress and trace: an open and a recheck of changed files reported to a client showing progress; each log line sent as `$/logTrace` at the client's level.
- Signature help: the head the called name was written with, its documentation, and the argument at the cursor.
- Inline completion: ranked snippets closing the form at the cursor or filling its hole, each hole a named tab stop.
- The outline: document symbols nesting each declaration inside its holder, folding ranges over multi-line forms, documentation and block comments, and selection ranges growing from the innermost node to the whole document.
- Hover: the type of the innermost node under the cursor, and a declaration's documentation or refusal; inlay hints: binders' unwritten types.
- Definitions and declarations: what the name under the cursor refers to, at its definition or its signature, and the families its type names, here or in an imported sibling; links: path imports to their files.
- Highlights, and linked editing of a local binder: where the name under the cursor is declared and used in the document; references and rename: in every open document and importer under the opened folders; a file renamed: its importers' addresses.
- Workspace symbols: the names the open documents' import closures declare, each holding the query's characters in order.
- Formatting: the whole document, also before a save, as one edit trimmed to the span its layout changes; ranges, and the form a typed `;` closes, one edit per top-level form.
- Positions in UTF-16 code units, clamped past a line's end or the last line.
- `Capabilities`: the `initialize` result as one line of JSON.
- A `file` URI's percent-decoded path.
- One grammar per process, built at the first recheck.

## Expected features

- **A client that reads UTF-16 positions.** The server answers `positionEncoding: "utf-16"`, the encoding every client supports, whatever encodings the client offers.
- **Documents named by `file` URIs.** The path classifies the document's source root as `gandr check` classifies a path: a document under a `fixture` directory settles as a fixture, one under `fixture/pending` is pending, and any other is strict. A URI of another scheme classifies as strict.

## Examples

```text
gandr lsp --capabilities
gandr lsp
gandr lsp --standalone
gandr serve --linger-ms 600000
```

`gandr lsp --capabilities` prints the `initialize` result as one line and exits; `gandr lsp` carries a session on standard input and output to the current directory's hub until `exit`, starting one when none runs; `gandr lsp --standalone` serves the session in its own process; `gandr serve` runs the hub itself, here lingering ten minutes after its last client. The crate-level example serves a session from `initialize` to `exit` in memory.

The crate's tests run with `cargo nextest run -p gandr-surface-lsp`; the crate-level example runs with `cargo test -p gandr-surface-lsp --doc`.

## Where the detail lives

Mechanism and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Synchronisation, publication and admission; diagnostics as projections of the model | [`recheck`](src/recheck.rs) |
| One parse per held text, shared by the structural requests | [`reading`](src/reading.rs) |
| Semantic tokens | [`tokens`](src/tokens.rs) |
| Completion | [`complete`](src/complete.rs) |
| Signature help | [`signature`](src/signature.rs) |
| Inline completion | [`inline`](src/inline.rs) |
| The outline | [`outline`](src/outline.rs) |
| Hover | [`hover`](src/hover.rs) |
| Definitions, declarations | [`goto`](src/goto.rs) |
| Workspace symbols | [`search`](src/search.rs) |
| Highlights, references; rename; file moves | [`uses`](src/uses.rs); [`rename`](src/rename.rs); [`relocate`](src/relocate.rs) |
| UTF-16 positions | [`position`](src/position.rs) |
| The lifecycle, its error codes, document URIs | [`server`](src/server.rs) |
| Formatting | [`format`](src/format.rs) |
| One hub per workspace | [`hub`](src/hub.rs) |
| Model proposals | [`proposal`](src/proposal.rs) |
| The render bus | [`bus`](src/bus.rs) |
| The transport | [`transport`](src/transport.rs) |
| Coverage of the specification, editors and extensions, specification evidence, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
