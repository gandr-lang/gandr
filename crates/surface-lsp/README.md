# gandr-surface-lsp

The gandr language server: diagnostics, semantic tokens, completion, signature help, inline completion, the document's outline, hover, definitions, and the checked fills a model proposes, over the Language Server Protocol, served over any pair of byte streams, or by one engine hub to every client of a workspace.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-lsp` serves a subset of the Language Server Protocol 3.17 and, from 3.18, `textDocument/inlineCompletion`: the base protocol's framing, the JSON-RPC 2.0 envelope and its error codes, the lifecycle from `initialize` to `exit`, incremental document synchronisation and the requests [`src/lib.rs`](src/lib.rs) tabulates by method. `serve` runs one session over any `BufRead` and `Write` pair, logging one timing line per synchronisation to a third `Write`; `Capabilities` displays what `initialize` answers. On Unix, `run_hub` serves every connection a socket accepts over one shared set of open documents, `bind` and `socket_for` find the one hub per workspace and build, and `relay` carries a client's streams to it, as [`hub`](src/hub.rs) states.

**Why.** An editor should show what `gandr check` prints, where it prints it, while the source is written. The server is a face over the pipeline's own outputs, never a second pipeline: its diagnostics are projections of the diagnostics `gandr-surface-diagnostics` builds for the dispatcher's step, the same ones the terminal lays out, and its tokens are the roles `gandr-surface-grammar`'s highlighter classifies, so an editor, a terminal and a test cannot disagree about a refusal or a token.

**How.** Each connection's copy of an open document holds a `gandr-surface-session` session under the source root its `file` URI's path classifies as. A synchronisation applies the client's changes to the connection's copy; the copy's session judges the text on the worker pool, off the serving loop, a later change retiring it, and the server reads the judgement's step and publishes each diagnostic the model builds as one LSP diagnostic, mapped as [`recheck`](../surface-lsp-diagnostics/src/recheck.rs) tabulates. Then it runs the kernel admission the judgement left. Each structural request, name request and formatting request reads what the table below names.

## Provided features

- `serve` and `Served`: one session over a stream pair and a log, ending cleanly at `exit` or boundary EOF after `shutdown`, and abruptly before shutdown.
- A shared workspace: each connection that opens a document holds its own copy, answered and published for its own text; the copy that synchronised last is the one the other faces read, and the document is forgotten once the last holder closes it or leaves.
- `run_hub`, `bind`, `bind::Absent`, `socket_for`, `Unnamed` and `LINGER`, on Unix: one hub per workspace and build, every connection served over the shared workspace on its own threads, a killed client leaving the others served, and the hub removing its socket and returning once no client has connected for its linger.
- `relay`, on Unix: a client's frames carried to a hub and back, the session ending as a standalone one would.
- `Face`, on Unix: `run_hub`'s second face, handed every connection whose first byte is `{` rather than a frame's header, over the same workspace.
- `Workspace::held`, `published`, `watch`, `query` and `prepared`: what another face reads off the shared workspace: the open documents and their versions, the diagnostics last published for each, a channel told of each publication and forgotten document, any read-only request, and what a run reads, which then runs with no lock.
- `Workspace::trial`, `Tried` and `Reached`, with `ContentChange`, `Range`, `Position`, `Line` and `Character`: candidate changes judged without submitting any, ranked best first, each with the diagnostics its text would publish; every copy and its session unchanged.
- `Workspace::propose`, `Proposal` and `ProposalRefusal`: a model's fill of a range kept beside the document once it checks, refused when stale or failing, and withdrawn by the next synchronisation; kept fills served as ghost text, code lenses, code actions and hover notes.
- `RENDER_BUS_PREFACE`, `Stored`, and `Workspace::greeting`, `rendered` and `storing`: the render bus on the hub's socket, with its greeting, the store's card, its reports, the stack at the editor's cursor, a resync and a detach.
- With the `instrument` feature, `Activities`, `Cadence` and `Tick`: the hub's fold of the activity ring at its cadence, and the pool's pane on the render bus; `Workspace::trace`, `derived` and `opened`: a view's trace layer, the derivation card at the editor's cursor and a node's whole goal.
- Incremental synchronisation: each content change applied in order and the document judged again in its session on the worker pool, molding only the forms the change touched; one log line per publication.
- Notebook synchronisation: a Jupyter `.ipynb` of `gandr` cells judged as one document, each cell published its own diagnostics ([`notebook`](../surface-lsp-base/src/notebook.rs)).
- `Server::admit`, `Server::admitted`, `Admissions` and `Awaiting`: the judgement each synchronisation leaves due, run on the worker pool and published once delivered, then the kernel admission it left, run once its diagnostics are published.
- `read_frame`, `read_frame::Absent`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing, with a ceiling on a header line and on a body.
- The envelope: requests, notifications and responses told apart; a body outside the decoder-supported JSON fragment answered with a parse error; a decoded batch or other invalid message refused as an invalid request.
- Published diagnostics: one per diagnostic the model builds for the document's step, at its lead range, under its code, with its message and related information; republished at every change, cleared at close. A client that pulls diagnostics is answered the same set when it asks, named by its digest, and asked to pull again when a recheck it did not ask for changes it.
- The `gandr.diagnostics.verbosity` and `quiet` settings, pushed or pulled: a new verbosity republishes open documents; `quiet` is how long a diagnostic of the form being typed waits ([`quiet`](src/quiet.rs)).
- Imports read an editor's copy before the disk: an edit, or a `.gandr` file or folder changed, created, deleted or renamed, rechecks each open document importing it.
- Semantic tokens for the whole document, as edits of the last answer, and for a range, each use typed by its referent; `TOKEN_TYPES` and `TOKEN_MODIFIERS`, the legend.
- Completion: the binders in scope, the import closure's names and the keywords the slot at the cursor admits, each starting with the word typed.
- Cancellation: a request withdrawn before it is handled is answered without being run ([`quiet`](src/quiet.rs)).
- Progress and trace: an open and a recheck of changed files reported to a client showing progress; each log line sent as `$/logTrace` at the client's level; a session's messages traced to the file `sessionTrace` names, which `replay` holds a fresh server to.
- Signature help: each spine at the cursor, innermost first, as its head was written, with its documentation and slot; a space opens the next slot.
- Inline completion: ranked snippets closing the form at the cursor or filling its hole, each hole a named tab stop.
- The outline: document symbols nesting each declaration inside its holder, folding ranges over multi-line forms, documentation and block comments, and selection ranges from the innermost node outward.
- Hover: the type of the innermost node under the cursor, and a declaration's documentation or refusal; at the trace layer, the derivation path; inlay hints: binders' unwritten types.
- `page`, `index`, `site` and `sourced`: `gandr doc`'s pages and site, each declaration as its hover shows it.
- Definitions and declarations: what the name under the cursor refers to, at its definition or its signature, and the families its type names, here or in an imported sibling; links: path imports to their files.
- Highlights, and linked editing of a local binder: where the name under the cursor is declared and used in the document; references and rename: in every open document and importer in the opened projects; a file renamed: its importers' addresses.
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

`gandr lsp` serves a session through the workspace's hub, `gandr serve` runs the hub, and the driver's rustdoc (`gandr-lang`, `src/main.rs`) tabulates each invocation and its exit. The crate's example serves a session from `initialize` to `exit` in memory.

Tests: `cargo nextest run -p gandr-surface-lsp`; the example: `cargo test -p gandr-surface-lsp --doc`.

## Where the detail lives

Mechanism and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The lifecycle, its error codes, document URIs | [`server`](src/server.rs) |
| One hub per workspace | [`hub`](src/hub.rs) |
| The render bus | [`bus`](src/bus.rs) |
| The families that the server's handlers call, which their READMEs tabulate | [`gandr-surface-lsp-core`](../surface-lsp-core/README.md), [`gandr-surface-lsp-navigation`](../surface-lsp-navigation/README.md), [`gandr-surface-lsp-diagnostics`](../surface-lsp-diagnostics/README.md) |
| The parts that read neither the dispatcher nor the session, which the base's README tabulates | [`gandr-surface-lsp-base`](../surface-lsp-base/README.md) |
| Specification coverage, editors and extensions, evidence, references | [`src/lib.rs`](src/lib.rs) |

## References

- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: an item slot offers `flow`.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: `flow` supplies an import's translation.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: a renaming in a `flow` body is free.
- `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the warrants that `tier` draws.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: § kernel-reassessment-design item 9.
- `vault:01a178ab-2ecf-7893-afda-f14010a8acbe` — anchor: a shadow is a diagnostic, off by default.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
