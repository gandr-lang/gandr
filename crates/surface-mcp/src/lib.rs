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
//! and the type of a declaration; its resources name each open document's
//! diagnostics, and a subscription to one hears every publication. Every
//! tool result also carries what changed since the connection's previous
//! call, for a host that does not surface subscription updates to its model.
//!
//! # Both eras of the protocol
//!
//! A [`Connection`] answers a legacy client that opens with `initialize` and
//! subscribes through `resources/subscribe`, and a modern one that names
//! [`MODERN`] in each request's `_meta`, discovers the server through
//! `server/discover` and subscribes through `subscriptions/listen`.
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
//!     &Workspace::default(),
//!     &json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
//! );
//! assert_eq!(replies[0]["result"]["tools"][0]["name"], "diagnostics");
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

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
