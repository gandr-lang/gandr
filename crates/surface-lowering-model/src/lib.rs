//! **The model and arity family of the lowering**: type families and the
//! model signatures they derive, the packing of a module as a model, the
//! flattened model implicits, reducts, forgettings and signature matches, and
//! the arity of the type forms: telescopes, records, sums, observations,
//! copatterns, selections and the groups of outputs. The family compiles over
//! `gandr-surface-lowering-base` and beside the rest of the lowering, and an
//! edit of another family does not type-check it again.
//!
//! The family reads the lowering through its host, `F: Families`: the host
//! holds the lowering's context and answers each call into another family.
//! `gandr-surface-lowering` is the host, and a call from it into this family
//! builds [`Models::new`](lower::model::Models::new). Each call is static.
//!
//! | Module | What it holds |
//! | --- | --- |
//! | [`lower::model`] | type families, derived model signatures, packing, model implicits, reducts, forgettings and signature matches |
//! | [`lower::arity`] | the arity of the type forms: telescopes, records, sums, observations, copatterns, selections and groups of outputs |
//!
//! The family keeps its homes at `lower::model` and `lower::arity`, as in the
//! lowering. A witness of an item is a test of `gandr-surface-lowering`,
//! spelled with that package's name, because the case lowers a source and
//! this crate does not lower.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the seam test. The
//!   family reads the lowering only through `Families`, a trait of the base, so
//!   no cycle crosses the crate boundary and the family compiles over the base
//!   alone.

// Module documentation that predates the shape lint, moved whole from the
// lowering's `lower::model` and `lower::arity`. Each allow leaves with the
// rewrite that clears its count.
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
// The profiler's instrumentation names `std`; it links only into the
// benchmark build.
#[cfg(feature = "hotpath")]
extern crate std;

pub mod lower;

use gandr_surface_lowering_base::by_form;
use gandr_surface_lowering_base::derive;
use gandr_surface_lowering_base::description;
use gandr_surface_lowering_base::error;
use gandr_surface_lowering_base::form;
use gandr_surface_lowering_base::import;
use gandr_surface_lowering_base::model;
use gandr_surface_lowering_base::module;
use gandr_surface_lowering_base::origin;
use gandr_surface_lowering_base::resolve;
use gandr_surface_lowering_base::slot;
use gandr_surface_lowering_base::unbuilt;
use gandr_surface_lowering_base::unit;
