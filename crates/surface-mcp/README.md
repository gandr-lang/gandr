# gandr-surface-mcp

The gandr Model Context Protocol server: the documents the engine hub holds open, their diagnostics and the language server's queries over them, served to models as tools and resources.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Models read what the editor shows](#models-read-what-the-editor-shows)
- [Both eras of the protocol](#both-eras-of-the-protocol)
- [Changes ride on every tool result](#changes-ride-on-every-tool-result)
- [A trial splices each candidate into the held text](#a-trial-splices-each-candidate-into-the-held-text)
- [One socket, two faces](#one-socket-two-faces)
- [The protocol is written here](#the-protocol-is-written-here)
- [Specification evidence](#specification-evidence)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-mcp` serves the Model Context Protocol's tools and resources over the engine hub's shared workspace. Six tools: `diagnostics` (the last diagnostics published for an open document), `documents` (every open document and its version), `outline` (its declarations, nested), `expected_syntax` (the syntax the parser expects at a position, as snippets), `trial` (candidate fills judged without changing the document, best first) and `type_of` (the type and documentation of the declaration named at a position). One resource per open document, `gandr://<path>/diagnostics`, readable and subscribable. On Unix the hub hands it every connection whose first byte is `{`; `gandr mcp` relays a model host's standard streams to that hub.

**Why.** A model writing gandr should see what the author's editor shows, at the version the editor last synchronised, without a second checker that could disagree with the first, and without re-running the pipeline on every read.

**How.** A `Connection` holds one model's protocol state: its era's subscriptions, its listening streams and the versions of the documents it has seen. Each request it handles reads the `gandr_surface_lsp::Workspace` the hub's editor connections share, under the hub's one lock: diagnostics are read off the copy the last synchronisation published, and the other tools are answered by the language server's own handlers over the held session through `Workspace::query`. `serve` runs a connection on the hub's socket, a watcher thread turning each publication or forgotten document into the notifications its subscriptions hear.

## References

- Model Context Protocol. "Specification 2026-07-28." <https://modelcontextprotocol.io/specification/2026-07-28> — the per-request `_meta` version, `server/discover`, `subscriptions/listen` and its acknowledgement, the `resultType`, `ttlMs` and `cacheScope` result fields, and the `-32022` unsupported-version error.
- Model Context Protocol. "Specification 2025-11-25." <https://modelcontextprotocol.io/specification/2025-11-25> — the `initialize` handshake, `resources/subscribe` and `notifications/resources/updated`, tool results with `structuredContent`, and the newline-delimited stdio transport.
- JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification> — the envelope and the reserved error codes.
- The MCP Rust SDK. "rmcp." <https://crates.io/crates/rmcp> — the alternative [The protocol is written here](#the-protocol-is-written-here) weighs.

## Provided features

- `Connection`, `MODERN` and `LEGACY`: either era's opening, the tool list, resource listing and reading, both subscription styles and their notifications, and the protocol's error codes. Witnesses: `connection::tests::each_era_opens_and_lists_the_tools`, `connection::tests::an_unsupported_version_names_the_supported_ones`, `connection::tests::resources_name_each_documents_diagnostics`, `connection::tests::subscriptions_hear_only_their_documents`.
- The six tools and `ToolRefusal`: each answered off the shared workspace, a refusal answered as a tool error the model reads. Witnesses: `connection::tests::each_tool_answers_through_the_wire`, `connection::tests::a_trial_ranks_fills_through_the_wire`.
- `serve`, on Unix: a model's connection to the hub, notified as editors' synchronisations publish. Witness: `face::tests::an_edit_through_the_hub_notifies_its_subscribers`.
- `relay`, on Unix: a host's standard streams carried to the hub as lines. Witnesses: `face::tests::a_relay_carries_a_model_session`, `cli::cli::mcp_reads_what_an_editor_holds_open`.

## Expected features

- The goals at a document's holes with their spelled types, once the language server answers them.
- Normalisation and conversion queries, once the session exposes them.
- The explanation of a refusal, beside the verbosity levels of the diagnostics renderer.
- Proposals a model makes for the editor to apply.
- A transport beside the hub's socket: streamable HTTP, and the authorisation it carries.

## Examples

```rust
use gandr_surface_lsp::Workspace;
use gandr_surface_mcp::Connection;
use serde_json::json;

let mut connection = Connection::default();
let replies = connection.handle(
    &Workspace::default(),
    &json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
);
assert_eq!(replies[0]["result"]["tools"][0]["name"], "diagnostics");
```

From a shell, in a workspace an editor has open through `gandr lsp`:

```sh
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"documents","arguments":{}}}' | gandr mcp
```

## Models read what the editor shows

**Choice.** The server holds no document of its own. Every tool and resource reads the documents the hub's editor connections hold, at the version their last synchronisation reached; a document no editor holds is refused by name. Diagnostics are the copy the synchronisation published, kept beside the document, so reading them costs a lookup and never a judgement. The queries reuse the language server's handlers by handing them a request on a reader connection that holds nothing, so an outline, a completion or a hover reads exactly what the editor's would.

**Alternatives.** A model could open documents of its own through the server, at the cost of a second text of one file that the editor's edits do not reach. Re-judging a document per diagnostics read would answer the same reports at the price of a judgement. Translating each tool into its own walk over the session would duplicate the language server's position handling and could drift from it.

**Reversal.** A model that must check text no editor holds gains a tool that judges a given text in a scratch session; a query the language server does not answer gets its own handler here.

## Both eras of the protocol

**Choice.** A connection answers both the handshake era (an `initialize` naming one of `LEGACY`, then `resources/subscribe`) and the per-request era of `MODERN` (the version in each request's `_meta`, `server/discover`, and `subscriptions/listen` streams acknowledged by `notifications/subscriptions/acknowledged`). An `initialize` naming an unknown version is answered with the newest legacy one, as that era requires; a `_meta` naming an unknown version is refused with `-32022`, naming the supported ones. Results carry `resultType: "complete"`, and list and read results `ttlMs: 0` with `cacheScope: "private"`, since every answer depends on the editors' latest edit.

**Alternatives.** Serving the newest era alone would turn away the hosts that still open with `initialize`; serving the handshake era alone would leave modern hosts to negotiate down. Neither era's state leaks into the other: a connection may hold legacy subscriptions and listening streams at once.

**Reversal.** The handshake era is dropped once the hosts in use all speak the per-request one.

## Changes ride on every tool result

**Choice.** Every tool result carries `changes`: the documents opened or changed since this connection's previous call, with their versions, and those closed. A host that never surfaces subscription notifications to its model still tells the model, on its next call, that an editor moved underneath it.

**Alternatives.** Subscriptions alone reach a model only through a host that forwards them; a separate `changes` tool would have to be called to be useful, which a model does not know to do.

**Reversal.** The field is dropped once the hosts in use forward resource updates to their models.

## A trial splices each candidate into the held text

**Choice.** The `trial` tool takes up to 32 candidate texts and an optional range. With a range — a hole, or a declaration's body — each candidate replaces it in the document's held text, as an editor's ranged change would; without one, each candidate is the whole text. The language server's `Workspace::trial` judges every candidate as a fresh session would, in parallel, and the results come back best first: those judged before those the lowering refused whole, then fewer refused and unsettled declarations, then the candidate's own position. Each result carries the diagnostics a synchronisation to that text would publish. The document, its session and what the editor shows are unchanged.

**Alternatives.** Candidates as whole texts alone would make a model copy the document once per candidate for a fill of a few characters. A target named by a declaration rather than a range would need a resolution step from name to span that the editor's range already gives. No cap would let one call hold the hub's lock for as long as a model cares to send; 32 is past the batch the session's measurements were taken at (8 and 16), and a batch at 16 candidates across the performance cores already costs a fraction of a model turn.

**Reversal.** A model host measured to send larger batches raises the cap, or moves the trial off the hub's lock onto a copy of the session; a face that names holes by their goal resolves the range from the goal.

## One socket, two faces

**Choice.** The model's server is a face of the engine hub, on the hub's own socket. The hub reads a connection's first byte: a language-server frame begins with its `Content-Length` header, a model's message with `{`, and the hub hands the second kind to the face `run_hub` was given. The face is a parameter, so the language server's crate never depends on this one; the driver wires `serve` into the hub it runs. `gandr mcp` reaches the hub as `gandr lsp` does, starting it when none answers.

**Alternatives.** A second socket per workspace would double the discovery and the stale-socket probe for one more listener. A separate model server process would hold a second workspace that the editors' edits never reach.

**Reversal.** A third protocol whose first byte cannot be told from these two moves the hub to a socket per protocol.

## The protocol is written here

**Choice.** The envelope, the methods and the result shapes are written over `serde_json` values in this crate, on blocking standard-library streams, as the language server's are.

**Alternatives.** `rmcp`, the protocol's official Rust SDK (3.5.1 at this writing), would supply the types and the dispatch. Its `server` feature brings `tokio` with `tokio-util`, `schemars` and `uuid`, none of which the workspace builds today, and its service model is asynchronous where the hub serves each connection on its own threads. The methods served here are few enough that the types they need are a page.

**Reversal.** A transport this crate would otherwise have to write — streamable HTTP, or the authorisation flows that ride on it — moves the server onto `rmcp`, with the asynchronous runtime it brings.

## Specification evidence

Executable predicates bound what a connection answers: one reply at most per message, one notification at most per subscription and listening stream per change, resource names that round-trip to the document they name, a tool list sorted by name with object input schemas, and a tool's success always an object. `serve` and `relay` own sockets and opaque streams; their exemptions are witnessed by sessions through a running hub, in this crate's tests and the driver's.

Adequacy is behavioural over the wire: each era's opening and its errors, every tool answered and refused, resources listed and read for open and unknown documents, and notifications heard only by the subscriptions and streams that name the edited document. Diagnostic contents are compared by their code and count, never by message wording.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
