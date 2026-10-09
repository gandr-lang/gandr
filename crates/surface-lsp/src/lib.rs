//! **The language server**: diagnostics and semantic tokens over the Language
//! Server Protocol, served over any pair of byte streams.
//!
//! # Every request rechecks the whole document
//!
//! A synchronisation composes the document whole through the dispatcher's
//! composition and publishes, as editor diagnostics, the reports the
//! diagnostics renderer gives that step: the same reports, at the same spans,
//! under the same refusal names `gandr check --goals` prints. A token request
//! highlights the document whole through the grammar's role table, the same
//! classification a terminal face styles. Positions are counted in UTF-16 code
//! units through the renderer seam's line index. The server keeps nothing
//! between requests but the open documents' text and the one grammar the
//! process builds.
//!
//! # The transport is the base protocol, written here
//!
//! A frame is a `Content-Length` header block and a JSON-RPC 2.0 body;
//! [`serve`] reads frames from one stream, handles each, and writes every
//! answer and notification to the other until `exit`. [`Capabilities`] is what
//! `initialize` answers, for a client that reads it before starting a
//! session.
//!
//! # Example
//!
//! ```
//! use std::io::Cursor;
//!
//! use gandr_surface_lsp::Body;
//! use gandr_surface_lsp::Served;
//! use gandr_surface_lsp::serve;
//! use gandr_surface_lsp::write_frame;
//!
//! let mut input = Vec::new();
//! for message in [
//!     r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
//!     r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
//!     r#"{"jsonrpc":"2.0","method":"exit"}"#,
//! ] {
//!     write_frame(&mut input, &Body::from(message.as_bytes().to_vec()))?;
//! }
//! let mut output = Vec::new();
//! let served = serve(&mut Cursor::new(input), &mut output)?;
//! assert_eq!(
//!     served,
//!     Served::Clean,
//!     "exit after shutdown ends the session cleanly"
//! );
//! let written = String::from_utf8(output)?;
//! assert!(
//!     written.ends_with(r#"{"jsonrpc":"2.0","id":2,"result":null}"#),
//!     "{written}"
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

extern crate alloc;

use core::fmt;

mod position;
mod protocol;
mod recheck;
mod rpc;
mod server;
mod tokens;
mod transport;

pub use crate::server::Served;
pub use crate::server::serve;
pub use crate::tokens::TOKEN_MODIFIERS;
pub use crate::tokens::TOKEN_TYPES;
pub use crate::transport::Body;
pub use crate::transport::TransportFault;
pub use crate::transport::read_frame;
pub use crate::transport::write_frame;

/// The capabilities the server advertises: what `initialize` answers,
/// displayed as one line of JSON.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Capabilities;

impl fmt::Display for Capabilities
{
    /// Writes the `initialize` result as one line of JSON: the capabilities
    /// and the server's name and version.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the `result` an `initialize` request is answered
    ///   with, compact, with no line terminator.
    /// - provides: the driver's `gandr lsp --capabilities` line.
    /// - fails: propagates the formatter's own write failure, and reports one
    ///   for a result that does not encode.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the line is decoded and compared whole with the
    ///   legend the crate exports.
    /// - witness: `capabilities::capabilities::advertised_capabilities_name_the_token_legend`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let line = serde_json::to_string(&protocol::InitializeResult::advertised())
            .map_err(|_unencodable| fmt::Error)?;
        f.write_str(&line)
    }
}
