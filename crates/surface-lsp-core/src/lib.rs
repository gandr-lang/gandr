//! **The core of the language server's families**: the reading of a held
//! text, hover, completion, definitions, signature help, semantic tokens and
//! the files of a workspace.
//!
//! A cold build compiles the server after the dispatcher and the session. The
//! families of the server read both, but no family reads the server's state.
//! So the families compile in crates of their own, below the server. This
//! crate holds the families that the others read: the reading of a held text
//! and the hover's table of a judged copy, with the requests that read them
//! directly. `gandr-surface-lsp-navigation` and
//! `gandr-surface-lsp-diagnostics` compile over it, beside each other, and
//! `gandr-surface-lsp` compiles over the three.
//!
//! The modules state their decisions.

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

use gandr_surface_lsp_base::elsewhere;
use gandr_surface_lsp_base::fragment;
use gandr_surface_lsp_base::inline;
use gandr_surface_lsp_base::markup;
#[cfg(test)]
use gandr_surface_lsp_base::missing;
use gandr_surface_lsp_base::outline;
use gandr_surface_lsp_base::peer;
use gandr_surface_lsp_base::position;
use gandr_surface_lsp_base::protocol;
use gandr_surface_lsp_base::rpc;
use gandr_surface_lsp_base::toolkit;
use gandr_surface_lsp_base::tracking;

#[cfg(feature = "instrument")]
pub mod activity;
#[cfg(any(test, feature = "fixture"))]
pub mod anchor;
pub mod build;
pub mod complete;
#[cfg(feature = "instrument")]
pub mod derivation;
pub mod files;
pub mod format;
pub mod goto;
pub mod hover;
pub mod instrument;
pub mod reading;
pub mod relocate;
pub mod search;
pub mod signature;
#[cfg(unix)]
pub mod stored;
pub mod sweep;
pub mod tokens;
pub mod view;
