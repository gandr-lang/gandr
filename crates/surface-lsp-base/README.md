# gandr-surface-lsp-base

The base of gandr's language server: the parts of `gandr-surface-lsp` that read neither the dispatcher nor the session. The server compiles over this crate, so this crate compiles beside the dispatcher and the session.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The protocol's messages as serde types, the base protocol's framing and the JSON-RPC envelope, and positions in UTF-16 code units. The semantic token stream and its legend, the forms an inline completion offers, and the markup that colours gandr text in a hover. The edits of a held text, a notebook's cells, the syntax tree view, a session handed across builds, and the process's one grammar. The document's outline, the hints and removals of unused names, the imports a missing name needs, and the hub's watch of the files on disk with the inbox it hands their changes to. The form under the caret that the quiet publication holds, the checked fills a model proposed, the hub's socket and its relay, and the trace of a session with its replay. `gandr-surface-lsp` names each module at its old path and re-exports each item that it exported before.

**Why.** A cold build of the driver compiles the server after the dispatcher and the session. A part of the server that reads neither compiles in a crate of its own, beside them, and leaves the build's longest chain. Each later split of the server adds its parts here or in a family crate over this one.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate, or tests of `gandr-surface-lsp` that read the item through the server, spelled with that package's name.

## Provided features

- The protocol's parameters, results and notifications, `DocumentUri` and `ContentChange` among them ([`protocol`](src/protocol.rs)).
- `read_frame`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing ([`transport`](src/transport.rs)); requests, notifications and responses told apart, and the answers written ([`rpc`](src/rpc.rs)).
- `Position`, `Range`, `Line` and `Character`: positions in UTF-16 code units, clamped past a line's end ([`position`](src/position.rs)).
- `TokenStream`, `TokensEdit`, `ResultId`, `TOKEN_TYPES` and `TOKEN_MODIFIERS`: the token stream, its edits, the digest that names an answer, and the legend ([`tokens`](src/tokens.rs)).
- Inline completion: ranked snippets closing the form at the cursor or filling its hole ([`inline`](src/inline.rs)).
- The markup of a hover and the colours of a fragment of gandr text ([`markup`](src/markup.rs), [`fragment`](src/fragment.rs)).
- `apply` and `edit_text`: a content change applied to a held text ([`edit`](src/edit.rs)); a notebook's cells as one document ([`notebook`](src/notebook.rs)).
- The syntax tree view ([`syntax`](src/syntax.rs)) and the gaps that a hover cannot show yet ([`tracking`](src/tracking.rs)).
- `Handover`, `Carried` and `REPLAY`: a session handed across builds ([`handover`](src/handover.rs)); `Peer`: one connection of a workspace ([`peer`](src/peer.rs)).
- One grammar, role table and form set per process, built at the first use ([`toolkit`](src/toolkit.rs)).
- The outline: symbols, folding ranges and selection ranges read off the parsed tree ([`outline`](src/outline.rs)).
- The hints of an unused binder and an unused import, and the removal of an unused import ([`unused`](src/unused.rs)).
- The quick fix that imports a source for a name that names nothing ([`missing`](src/missing.rs)), over the names that sources elsewhere declare ([`elsewhere`](src/elsewhere.rs)).
- `Inbox`, `Changes`, `Behind` and `Unread`: what a paced loop's reader and its watches hand it ([`inbox`](src/inbox.rs)); on Unix, the hub's watch of the files on disk ([`disk`](src/disk.rs)).
- `QUIET`, `Holding`, `Met`, `caret_form` and `publishable`: the form under the caret, whose diagnostics the quiet publication holds ([`quiet`](src/quiet.rs)).
- `Proposal`, `Settles` and `ProposalRefusal`: a checked fill that a model proposed, with its ghost text, its lens, its action and its note ([`proposal`](src/proposal.rs)).
- `bind`, `relay`, `workspace_name`, `LINGER` and `Relayed`: the hub's socket, its name and the relay of a client's frames ([`hub`](src/hub.rs)).
- `SessionTrace`, `TraceLine` and `Divergence`: the trace of a session, and where a replay parts from it ([`session_trace`](src/session_trace.rs)).
- `Signature`, `Calling`, `heads_among` and `parameters_documented`: the head of each declaration and constructor of a text, read off its declaring form, and the signature a client is answered with ([`signature`](src/signature.rs)).

## Expected features

- **A client that reads UTF-16 positions.** The positions count UTF-16 code units, the encoding every client supports.
- **A tree from the parser.** The inline completion and the syntax tree view read a `SyntaxTree` that `gandr-surface-parser` builds.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The protocol's messages | [`protocol`](src/protocol.rs) |
| The transport and the envelope | [`transport`](src/transport.rs), [`rpc`](src/rpc.rs) |
| UTF-16 positions | [`position`](src/position.rs) |
| The token stream | [`tokens`](src/tokens.rs) |
| Inline completion | [`inline`](src/inline.rs) |
| The markup of a hover | [`markup`](src/markup.rs), [`fragment`](src/fragment.rs) |
| A session across builds | [`handover`](src/handover.rs) |
| The outline | [`outline`](src/outline.rs) |
| Unused names, missing imports | [`unused`](src/unused.rs), [`missing`](src/missing.rs), [`elsewhere`](src/elsewhere.rs) |
| The watch of the files on disk | [`disk`](src/disk.rs), [`inbox`](src/inbox.rs) |
| The quiet publication | [`quiet`](src/quiet.rs) |
| The checked fills of a model | [`proposal`](src/proposal.rs) |
| The hub's socket and relay | [`hub`](src/hub.rs) |
| The trace of a session | [`session_trace`](src/session_trace.rs) |
| The heads of a text | [`signature`](src/signature.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
