//! **The diagnostics of the language server**: the recheck of a document,
//! the kernel tiers, the repairs and fills of a hole, a model's proposals and
//! the checkpoints a save keeps.
//!
//! Each family of this crate reads the reading of a held text and the hover's
//! table, which `gandr-surface-lsp-core` holds. No family of this crate reads
//! the navigation, so this crate compiles beside
//! `gandr-surface-lsp-navigation`. `gandr-surface-lsp` compiles over both.
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
use gandr_surface_lsp_base::inline;
use gandr_surface_lsp_base::position;
use gandr_surface_lsp_base::protocol;
use gandr_surface_lsp_base::toolkit;
use gandr_surface_lsp_core::build;
use gandr_surface_lsp_core::complete;
use gandr_surface_lsp_core::hover;
use gandr_surface_lsp_core::instrument;
use gandr_surface_lsp_core::reading;
use gandr_surface_lsp_core::signature;

pub mod fix;
pub mod proposal;
pub mod recheck;
pub mod saved;
#[cfg(test)]
mod tests;
pub mod tier;
