//! **The base of the glued value domain**: the per-run arena and its ids,
//! closures and environments, values, neutrals and eliminations, the free
//! indices of a core term, the content guards, element identity, the stage
//! terms, and the sharing overlay with its erasure and its measure.
//!
//! The evaluator, readback, the conversion machine and the overlay's evaluator
//! are in `gandr-core-nbe`, which compiles over this crate and re-exports each
//! path a consumer names today. Its crate documentation states the decisions
//! that interlock and the references. An edit of the evaluator rebuilds
//! neither this crate nor a crate that reads only this crate.

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
#![no_std]

extern crate alloc;

pub mod arena;
pub mod closure;
pub mod domain;
pub mod free;
pub mod guard;
pub mod identity;
pub mod measure;
pub mod overlay;
pub mod spec;
pub mod stage;

pub use crate::closure::ValueBody;
