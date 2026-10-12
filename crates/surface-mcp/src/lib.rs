//! **The Model Context Protocol server**: the engine hub's open documents,
//! their diagnostics and the language server's queries over them, served to
//! models.
//!
//! # Models read what the editor shows
//!
//! The server is a face of the engine hub, beside the language server: a
//! model's connection reads the documents the editors' connections hold, at
//! the version they last synchronised. Its tools answer the diagnostics last
//! published for a document, its outline, the syntax expected at a position
//! and the type of a declaration, judge a batch of candidate fills without
//! changing the document, and offer a fill to the editors, kept once it
//! checks; its resources name each open document's
//! diagnostics, and a subscription to one hears every publication. Every
//! tool result also carries what changed since the connection's previous
//! call, for a host that does not surface subscription updates to its model.
//!
//! **Choice.** The server holds no document of its own. Every tool and resource
//! reads the documents the hub's editor connections hold, at the version their
//! last synchronisation reached; a document no editor holds is refused by name.
//! Diagnostics are the copy the synchronisation published, kept beside the
//! document, so reading them costs a lookup and never a judgement. The queries
//! reuse the language server's handlers by handing them a request on a reader
//! connection that holds nothing, so an outline, a completion or a hover reads
//! exactly what the editor's would.
//!
//! **Alternatives.** A model could open documents of its own through the
//! server, at the cost of a second text of one file that the editor's edits do
//! not reach. Re-judging a document per diagnostics read would answer the same
//! reports at the price of a judgement. Translating each tool into its own walk
//! over the session would duplicate the language server's position handling and
//! could drift from it.
//!
//! **Reversal.** A model that must check text no editor holds gains a tool that
//! judges a given text in a scratch session; a query the language server does
//! not answer gets its own handler here.
//!
//! # Both eras of the protocol
//!
//! A [`Connection`] answers a legacy client that opens with `initialize` and
//! subscribes through `resources/subscribe`, and a modern one that names
//! [`MODERN`] in each request's `_meta`, discovers the server through
//! `server/discover` and subscribes through `subscriptions/listen`.
//!
//! **Choice.** A connection answers both the handshake era (an `initialize`
//! naming one of `LEGACY`, then `resources/subscribe`) and the per-request era
//! of `MODERN` (the version in each request's `_meta`, `server/discover`, and
//! `subscriptions/listen` streams acknowledged by
//! `notifications/subscriptions/acknowledged`). An `initialize` naming an
//! unknown version is answered with the newest legacy one, as that era
//! requires; a `_meta` naming an unknown version is refused with `-32022`,
//! naming the supported ones. Results carry `resultType: "complete"`, and list
//! and read results `ttlMs: 0` with `cacheScope: "private"`, since every answer
//! depends on the editors' latest edit.
//!
//! **Alternatives.** Serving the newest era alone would turn away the hosts
//! that still open with `initialize`; serving the handshake era alone would
//! leave modern hosts to negotiate down. Neither era's state leaks into the
//! other: a connection may hold legacy subscriptions and listening streams at
//! once.
//!
//! **Reversal.** The handshake era is dropped once the hosts in use all speak
//! the per-request one.
//!
//! # The transport is a line per message
//!
//! On Unix, [`serve`] is the hub's line face: a connection whose first byte
//! is `{` speaks newline-delimited JSON, and the hub hands it here. [`relay`]
//! carries a client's standard streams to the hub, as `gandr mcp` does.
//!
//! # Example
//!
//! ```
//! use gandr_surface_lsp::Workspace;
//! use gandr_surface_mcp::Connection;
//! use serde_json::json;
//!
//! let mut connection = Connection::default();
//! let replies = connection.handle(
//!     &mut Workspace::default(),
//!     &json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
//! );
//! assert_eq!(replies[0]["result"]["tools"][0]["name"], "diagnostics");
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # The protocol is written here
//!
//! **Choice.** The envelope, the methods and the result shapes are written over
//! `serde_json` values in this crate, on blocking standard-library streams, as
//! the language server's are.
//!
//! **Alternatives.** `rmcp`, the protocol's official Rust SDK, would supply the
//! types and the dispatch. Its `server` feature brings `tokio` with
//! `tokio-util`, `schemars` and `uuid`, none of which the workspace otherwise
//! builds, and its service model is asynchronous where the hub serves each
//! connection on its own threads. The methods served here are few enough that
//! the types they need are a page.
//!
//! **Reversal.** A transport this crate would otherwise have to write —
//! streamable HTTP, or the authorisation flows that ride on it — moves the
//! server onto `rmcp`, with the asynchronous runtime it brings.
//!
//! # Specification evidence
//!
//! Executable predicates bound what a connection answers: one reply at most per
//! message, one notification at most per subscription and listening stream per
//! change, resource names that round-trip to the document they name, a tool
//! list sorted by name with object input schemas, and a tool's success always
//! an object. `serve` and `relay` own sockets and opaque streams; their
//! exemptions are witnessed by sessions through a running hub, in this crate's
//! tests and the driver's.
//!
//! Adequacy is behavioural over the wire: each era's opening and its errors,
//! every tool answered and refused, resources listed and read for open and
//! unknown documents, and notifications heard only by the subscriptions and
//! streams that name the edited document. Diagnostic contents are compared by
//! their code and count, never by message wording.
//!
//! # References
//!
//! - Model Context Protocol. "Specification 2026-07-28." <https://modelcontextprotocol.io/specification/2026-07-28>
//!   — the per-request `_meta` version, `server/discover`,
//!   `subscriptions/listen` and its acknowledgement, the `resultType`, `ttlMs`
//!   and `cacheScope` result fields, and the `-32022` unsupported-version
//!   error.
//! - Model Context Protocol. "Specification 2025-11-25." <https://modelcontextprotocol.io/specification/2025-11-25>
//!   — the `initialize` handshake, `resources/subscribe` and
//!   `notifications/resources/updated`, tool results with `structuredContent`,
//!   and the newline-delimited stdio transport.
//! - JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification>
//!   — the envelope and the reserved error codes.
//! - The MCP Rust SDK. "rmcp." <https://crates.io/crates/rmcp> — the
//!   alternative § The protocol is written here weighs.

extern crate alloc;

mod connection;
#[cfg(unix)]
mod face;
mod tools;

pub use crate::connection::Connection;
pub use crate::connection::LEGACY;
pub use crate::connection::MODERN;
pub use crate::connection::Refusal;
#[cfg(unix)]
pub use crate::face::relay;
#[cfg(unix)]
pub use crate::face::serve;
pub use crate::tools::ToolRefusal;
