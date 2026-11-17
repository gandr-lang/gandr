//! **The expression and type lowering**: the lowering of each expression, type,
//! pattern, block and declaration body, over the lowering's base and its
//! families. The crate compiles above the families, since it calls them
//! directly, and below the top, which holds the dispatch and the host.
//!
//! The expression lowering reads the lowering through its host, `F: Families`:
//! the host holds the lowering's context and answers each call into a family.
//! `gandr-surface-lowering` is the host, and a call from it into this crate
//! builds [`Expressions::new`](lower::Expressions::new). Each call is static.
//!
//! The crate keeps its homes at `lower` and its submodules, as in the
//! lowering. A witness of an item is a test of `gandr-surface-lowering`,
//! spelled with that package's name, because the case lowers a source and
//! this crate does not lower.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the seam test. The
//!   expression lowering reads the lowering only through `Families`, a trait of
//!   the base, and calls each family below it, so no cycle crosses a crate
//!   boundary.

// Module documentation that predates the shape lint, moved whole from the
// lowering's `lower` module. Each allow leaves with the rewrite that clears
// its count.
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

use gandr_surface_lowering_base::attribute;
use gandr_surface_lowering_base::by_form;
use gandr_surface_lowering_base::certify;
use gandr_surface_lowering_base::classify;
use gandr_surface_lowering_base::coincide;
use gandr_surface_lowering_base::description;
use gandr_surface_lowering_base::doc;
use gandr_surface_lowering_base::error;
use gandr_surface_lowering_base::form;
use gandr_surface_lowering_base::import;
use gandr_surface_lowering_base::layout;
use gandr_surface_lowering_base::model;
use gandr_surface_lowering_base::module;
use gandr_surface_lowering_base::namespace;
use gandr_surface_lowering_base::operation;
use gandr_surface_lowering_base::origin;
use gandr_surface_lowering_base::resolve;
use gandr_surface_lowering_base::slot;
use gandr_surface_lowering_base::unbuilt;
use gandr_surface_lowering_base::unit;
use gandr_surface_lowering_base::written_import;

use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::resolve::InScope;
use crate::resolve::Resolution;
