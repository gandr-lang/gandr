//! **The base of the language server**: the parts of the server that read
//! neither the dispatcher nor the session.
//!
//! A cold build compiles the server after the dispatcher and the session. The
//! parts of the server that read neither can compile beside them. This crate
//! holds those parts, and `gandr-surface-lsp` compiles over it.
//!
//! The crate holds the protocol's messages as serde types, the transport and
//! its envelopes, the positions that the wire counts in UTF-16 code units, and
//! the semantic token stream. It holds the forms an inline completion offers
//! and the markup that colours a fragment of gandr text. It also holds the
//! edits of a held text, a notebook's cells, the syntax tree view, a session
//! handed across builds, and the process's one grammar.
//!
//! The server's families and its loop stay in `gandr-surface-lsp`. That crate
//! re-exports each item of this crate that it exported before, at its old
//! path. The modules state their decisions.
//!
//! # References
//!
//! - Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>
//!   — the base protocol's header and content parts, the messages this crate
//!   types, and the position encodings it counts in.
//! - Microsoft. "Language Server Protocol Specification 3.18." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.18/specification/>
//!   — the inline completion's `StringValue` and the snippet syntax a ghost
//!   text's tab stops are written in.
//! - JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification>
//!   — the envelope and the reserved error codes.
//! - Matthew Kerwin. "The 'file' URI Scheme." RFC 8089, February 2017.
//!   `doi:10.17487/RFC8089` — the URI a document is named by, and its
//!   percent-decoded path.

// Module documentation that predates the shape lint. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

pub mod edit;
pub mod fragment;
pub mod handover;
pub mod inline;
pub mod markup;
pub mod notebook;
pub mod peer;
pub mod position;
pub mod protocol;
pub mod rpc;
pub mod syntax;
pub mod tokens;
pub mod toolkit;
pub mod tracking;
pub mod transport;
