//! **The native family of the lowering**: a data family where a type is read,
//! a constructor applied to its fields, a data declaration's signature, and a
//! match compiled to native eliminations. The family compiles over
//! `gandr-surface-lowering-base` and beside the rest of the lowering, and an
//! edit of another family does not type-check it again.
//!
//! The family reads the lowering through its host, `F: Families`: the
//! host holds the lowering's context and answers each call into another
//! family. `gandr-surface-lowering` is the host, and a call from it into this
//! family builds [`Native::new`](lower::native::Native::new). Each call is
//! static. The family's reads of the context alone stand on
//! [`NativeRef`](lower::native::NativeRef), which borrows the context and never
//! the lowering.
//!
//! | Module | What it holds |
//! | --- | --- |
//! | [`lower::native`] | the native family: data families, constructors, signatures and match compilation |
//!
//! The family keeps its home at `lower::native`, as in the lowering. A witness
//! of an item is a test of `gandr-surface-lowering`, spelled with that
//! package's name, because the case lowers a source and this crate does not
//! lower.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the seam test. The
//!   family reads the lowering only through `Families`, a trait of the base, so
//!   no cycle crosses the crate boundary and the family compiles over the base
//!   alone.

// Module documentation that predates the shape lint, moved whole from the
// lowering's `lower::native`. Each allow leaves with the rewrite that clears
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

pub mod lower;

use gandr_surface_lowering_base::by_form;
use gandr_surface_lowering_base::error;
use gandr_surface_lowering_base::form;
use gandr_surface_lowering_base::module;
use gandr_surface_lowering_base::namespace;
use gandr_surface_lowering_base::origin;
use gandr_surface_lowering_base::origin::Omitted;
use gandr_surface_lowering_base::resolve;
use gandr_surface_lowering_base::resolve::CandidateCount;
use gandr_surface_lowering_base::unbuilt;
