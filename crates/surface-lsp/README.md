# gandr-surface-lsp

The gandr language server: diagnostics, semantic tokens, inline completion, the document's outline, hover, and the checked fills a model proposes, over the Language Server Protocol, served over any pair of byte streams, or by one engine hub to every client of a workspace.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-lsp` serves a subset of the Language Server Protocol 3.17: the base protocol's framing, the JSON-RPC 2.0 envelope with its standard error codes, the lifecycle from `initialize` to `exit`, incremental document synchronisation, `textDocument/publishDiagnostics` after every synchronisation, `textDocument/semanticTokens/full` and `textDocument/semanticTokens/range`, `textDocument/documentSymbol`, `textDocument/foldingRange` and `textDocument/selectionRange`, `textDocument/hover`, and `textDocument/codeLens` and `textDocument/codeAction` over checked model proposals; and, from 3.18, `textDocument/inlineCompletion`. `serve` runs one session over any `BufRead` and `Write` pair, logging one timing line per synchronisation to a third `Write`; `Capabilities` displays what `initialize` answers. On Unix, `run_hub` serves every connection a socket accepts over one shared set of open documents, `bind` and `socket_for` find the one hub per workspace, and `relay` carries a client's streams to it. The driver's `gandr lsp` relays standard input and output to the hub of the current directory, starting `gandr serve` when none runs; `gandr lsp --standalone` serves in its own process.

**Why.** An editor should show what `gandr check` prints, where it prints it, while the source is written. The server is a face over the pipeline's own outputs, never a second pipeline: its diagnostics are projections of the diagnostics `gandr-surface-diagnostics` builds for the dispatcher's step, the same ones the terminal lays out, and its tokens are the roles `gandr-surface-grammar`'s highlighter classifies, so an editor, a terminal and a test cannot disagree about a refusal or a token.

**How.** Each connection's copy of an open document holds a `gandr-surface-session` session under the source root its `file` URI's path classifies as. A synchronisation applies the client's changes to the connection's copy and judges the text in the copy's session, reads the judgement's step through `gandr-surface-dispatcher`'s `entries` under `check --goals`, and publishes each diagnostic the model builds as one LSP diagnostic, mapped field by field as [`recheck`](src/recheck.rs) tabulates. Then it runs the kernel admission the judgement left. The first token, outline, hover or render request after a change parses the copy's text once, and that reading answers each of them until the next change. A token request takes the reading's highlighter spans and delta-encodes them under the standard legend. An inline-completion request molds the form the cursor is in up to the cursor, asks `gandr-surface-parser`'s completion query for the ways to go on from there, subtracts what is already written after the cursor and answers the best of them as ranked snippets. An outline request reads the declarations, the multi-line forms or the forms around a position off the reading. A hover request reads the innermost node's type off the dispatcher's `TypeTable`, built once per edit, and a declaration's documentation off the copy's session. A formatting request lays the held text out through `gandr-surface-format` and answers the edits that turn the text into that layout. Every position is a UTF-16 position read through `gandr-surface-render-remote`'s `LineIndex`. A workspace keeps the open documents, each with every holding connection's copy of its text and session; a connection keeps only its place in the lifecycle. The process keeps one grammar.

## Provided features

- `serve` and `Served`: one session over a stream pair and a log, ending cleanly at `exit` or boundary EOF after `shutdown`, and abruptly before shutdown.
- A shared workspace: each connection that opens a document holds its own copy, answered and published for the text that connection holds, so two clients of one buffer each apply an edit once and two diverging editors are each answered for their own text; the copy that synchronised last is the one the other faces read, and the document is forgotten once the last holder closes it or leaves.
- `run_hub`, `bind`, `bind::Absent`, `socket_for` and `LINGER`, on Unix: one hub per workspace socket, every connection served over the shared workspace on its own threads, a killed client leaving the others served, and the hub removing its socket and returning once no client has connected for its linger.
- `relay`, on Unix: a client's frames carried to a hub and back, the session ending as a standalone one would.
- `Face`, on Unix: `run_hub`'s second face, handed every connection whose first byte is `{` rather than a frame's header, over the same workspace.
- `Workspace::held`, `Workspace::published`, `Workspace::watch` and `Workspace::query`: what another face reads off the shared workspace, each off the copy that synchronised last — the open documents and their versions, the diagnostics last published for each, a channel told of each publication and forgotten document, and any request the server answers, run on a connection that holds nothing.
- `Workspace::trial`, `Tried` and `Reached`, with `ContentChange`, `Range`, `Position`, `Line` and `Character`: candidate changes, each applied alone to the text of a held document's latest copy as a synchronisation applies it, judged by that copy's session's trial without submitting any and ranked best first, each with the diagnostics a synchronisation to its text would publish; every copy and its session unchanged.
- `Workspace::propose`, `Proposal` and `ProposalRefusal`: a model's fill of a range kept beside the document once it checks, refused when stale or failing, and withdrawn by the next synchronisation; kept fills served as ghost text, code lenses, code actions and hover notes.
- `RENDER_BUS_PREFACE`, `Workspace::greeting` and `Workspace::rendered`: the render bus on the hub's socket — a connection opening with the preface greeted with the held documents and sent each one's report, then the report of every publication; a resync answered at the current version, a detach closing it, another bus version detached at once. A report is the held text, its highlights, a card per published error or warning and marks under errors and holes.
- Incremental synchronisation: each content change applied in order, a ranged one to its range and one naming no range as the whole text, and the document judged again in its session, which molds only the forms the change touched; one log line per synchronisation, its fields as [`recheck`](src/recheck.rs) states.
- `Server::admit`: the kernel admission each synchronisation left, run once its diagnostics are published.
- `read_frame`, `read_frame::Absent`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing, with a ceiling on a header line and on a body.
- The envelope: requests, notifications and responses told apart; a body outside the decoder-supported JSON fragment answered with a parse error, including invalid UTF-8 and exceeded number or nesting limits; a decoded batch or other invalid message refused as an invalid request.
- Published diagnostics: one per diagnostic the model builds for the document's step, at its lead range, under its code, with its message and related information; republished at every change, cleared at close.
- The `gandr.diagnostics.verbosity` and `quiet` settings, read at `initialize` and at each `workspace/didChangeConfiguration`: a new verbosity republishes open documents; `quiet` is how long a diagnostic of the form being typed waits ([`quiet`](src/quiet.rs)).
- Semantic tokens for the whole document and for a range, and `TOKEN_TYPES` and `TOKEN_MODIFIERS`, the legend.
- Inline completion: up to eight ranked snippets at every cursor — the cheapest closing of the innermost form, its alternatives, and the forms that can fill the hole at the cursor — with holes as tab stops named by what fills them, never `?`; see [`inline`](src/inline.rs).
- The outline: document symbols nesting each declaration inside the one that holds it, folding ranges over multi-line forms, documentation and block comments, and selection ranges growing from the innermost node around a position to the whole document.
- Hover: the type of the innermost node under the cursor, and a declaration's documentation or refusal; see [`hover`](src/hover.rs).
- Formatting: the whole document as one edit trimmed to the span its layout changes, and a range as one edit per top-level form it touches, each from `gandr-surface-format`.
- Positions in UTF-16 code units, a position past a line's end or past the last line clamped.
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

`gandr lsp --capabilities` prints the `initialize` result as one line and exits; `gandr lsp` carries a session on standard input and output to the current directory's hub until `exit`, starting one when none runs; `gandr lsp --standalone` serves the session in its own process; `gandr serve` runs the hub itself, here lingering ten minutes after its last client. In memory:

```rust
use std::io::Cursor;

use gandr_surface_lsp::Body;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::Spelling;
use gandr_surface_lsp::serve;
use gandr_surface_lsp::write_frame;

let mut input = Vec::new();
for message in [
    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
    r#"{"jsonrpc":"2.0","method":"exit"}"#,
] {
    write_frame(&mut input, &Body::from(message.as_bytes().to_vec()))?;
}
let mut output = Vec::new();
let served = serve(&mut Cursor::new(input), &mut output, &mut Vec::new(), Spelling::Unicode)?;
assert_eq!(served, Served::Clean, "exit after shutdown ends the session cleanly");
# Ok::<(), Box<dyn core::error::Error>>(())
```

The crate's tests run with `cargo nextest run -p gandr-surface-lsp`; the crate-level example runs with `cargo test -p gandr-surface-lsp --doc`.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Synchronisation, publication and admission; diagnostics as projections of the model | [`recheck`](src/recheck.rs) |
| One parse per held text, shared by the structural requests | [`reading`](src/reading.rs) |
| Semantic tokens | [`tokens`](src/tokens.rs) |
| Inline completion | [`inline`](src/inline.rs) |
| The outline | [`outline`](src/outline.rs) |
| Hover | [`hover`](src/hover.rs) |
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
