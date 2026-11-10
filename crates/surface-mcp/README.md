# gandr-surface-mcp

The gandr Model Context Protocol server: the documents the engine hub holds open, their diagnostics and the language server's queries over them, served to models as tools and resources.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-mcp` serves the Model Context Protocol's tools and resources over the engine hub's shared workspace. Nine tools: `diagnostics` (the last diagnostics published for an open document), `documents` (every open document and its version), `outline` (its declarations, nested), `expected_syntax` (the syntax the parser expects at a position, as snippets), `trial` (candidate fills judged without changing the document, best first), `propose` (a fill offered to the document's editors, kept once it checks), `type_of` (the type and documentation of the declaration named at a position), and `ledger_list` and `ledger_show` (the features ledger, as `gandr ledger list` and `gandr ledger show` print it). One resource per open document, `gandr://<path>/diagnostics`, readable and subscribable. On Unix the hub hands it every connection whose first byte is `{`; `gandr mcp` relays a model host's standard streams to that hub.

**Why.** A model writing gandr should see what the author's editor shows, at the version the editor last synchronised, without a second checker that could disagree with the first, and without re-running the pipeline on every read.

**How.** A `Connection` holds one model's protocol state: its era's subscriptions, its listening streams and the versions of the documents it has seen. Each request it handles reads the `gandr_surface_lsp::Workspace` the hub's editor connections share, under the hub's one lock: diagnostics are read off the copy the last synchronisation published, and the other tools are answered by the language server's own handlers over the held session through `Workspace::query`. `serve` runs a connection on the hub's socket, a watcher thread turning each publication or forgotten document into the notifications its subscriptions hear.

The same tools reach an agent runtime through the Reactive Agent Protocol, the default face for an agent. A RAP call answers by a callback, so a long call blocks no agent, and an agent can subscribe to new states. One table holds each operation's name, description, schema and function over the hub. `tools/list` and the toolset's manifest each encode that table, and both faces call through it, so the faces cannot drift. `gandr serve` gives the hub a `Toolset` on a free port of the loopback interface, or on the port that `--port` names. The hub writes the manifest's URL to a file beside its socket, with the extension `rap`, and a runtime reads the URL there.

The `Toolset` acknowledges each invocation at once with a row in its store under the XDG state directory, and owes each answer to the caller's callback URL as a `tool_result`. The answer of `diagnostics` is a frame of the render bus: the document's cards and version, with the lines `gandr view` prints as its `display_as`. A subscription hears a `subscription_event` that holds the whole frame after each publication that changes it. Each callback carries an `Idempotency-Key`, and each delivery leaves on a thread of the toolset, retried as the `Policy` states.

The Model Context Protocol stays for compatibility, and `gandr mcp` serves it on request. A runtime that proxies MCP servers reaches `gandr mcp` as any server. A runtime that speaks RAP reads the manifest directly and needs no proxy.

## Provided features

- `Connection`, `MODERN` and `LEGACY`: either era's opening, the tool list, resource listing and reading, both subscription styles and their notifications, and the protocol's error codes.
- The nine operations of one table and `ToolRefusal`: each answered off the shared workspace through either face, a refusal answered as a tool error the model reads.
- `serve`, on Unix: a model's connection to the hub, notified as editors' synchronisations publish.
- `relay`, on Unix: a host's standard streams carried to the hub as lines.
- `Toolset`, on Unix: the Reactive Agent Protocol's manifest and invoke endpoint beside the hub's socket, each call answered by a callback, each call that a crash cut short answered again or with an error, and each subscription's new frame owed as an event.
- `Announcement` and `Announced`, on Unix: the file beside the hub's socket that names the toolset's URL, refused while another toolset listens there, and removed when the hub stops.
- `Policy` and `Retries`, on Unix: when the toolset tries a failed callback again and how often, which the `[deliveries]` table of the user's configuration names.

## Expected features

- The goals at a document's holes with their spelled types, once the language server answers them.
- Normalisation and conversion queries, once the session exposes them.
- The explanation of a refusal, beside the verbosity levels of the diagnostics renderer.
- A transport beside the hub's socket for the Model Context Protocol: streamable HTTP, and the authorisation it carries.
- The toolset's subscription operations and their durable table; its long operations and view updates.

## Examples

```rust
use gandr_surface_lsp::Workspace;
use gandr_surface_mcp::Connection;
use serde_json::json;

let mut connection = Connection::default();
let replies = connection.handle(
    &mut Workspace::default(),
    &json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
);
assert_eq!(replies[0]["result"]["tools"][0]["name"], "diagnostics");
```

From a shell, in a workspace an editor has open through `gandr lsp`:

```sh
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"documents","arguments":{}}}' | gandr mcp
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| What models read, both eras of the protocol, the protocol written here, specification evidence, references | [`src/lib.rs`](src/lib.rs) |
| Changes on every tool result, trials | [`tools`](src/tools.rs) |
| One socket, two faces | [`face`](src/face.rs) |
| The Reactive Agent Protocol's toolset, its store, its bearer, its frames and its subscriptions | [`rap`](src/rap.rs) |
| The deliveries of the toolset, their lanes and their retries | [`rap::deliver`](src/rap/deliver.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
