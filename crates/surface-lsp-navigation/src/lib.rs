//! **The navigation of the language server**: references, highlights, rename,
//! the call hierarchy, inlay hints, copied sources, shadowing and the
//! documentation site.
//!
//! Each family of this crate reads the hover's table of a judged copy, which
//! `gandr-surface-lsp-core` holds. No family of this crate reads the
//! diagnostics, so this crate compiles beside
//! `gandr-surface-lsp-diagnostics`. `gandr-surface-lsp` compiles over both.
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

use gandr_surface_lsp_base::fragment;
use gandr_surface_lsp_base::markup;
use gandr_surface_lsp_base::position;
use gandr_surface_lsp_base::protocol;
use gandr_surface_lsp_base::toolkit;
#[cfg(test)]
use gandr_surface_lsp_core::anchor;
use gandr_surface_lsp_core::goto;
use gandr_surface_lsp_core::hover;
use gandr_surface_lsp_core::reading;

pub mod calls;
pub mod doc;
pub mod inlay;
pub mod paste;
pub mod rename;
pub mod shadowed;
pub mod site;
pub mod uses;
