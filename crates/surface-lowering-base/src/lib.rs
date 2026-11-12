//! **The base of the lowering**: the parts of `gandr-surface-lowering` that
//! read nothing of the lowering itself. The lowering's families compile over
//! this crate. A family that this crate holds compiles beside the lowering,
//! and an edit of the lowering does not recompile it.
//!
//! | Module | What it holds |
//! | --- | --- |
//! | [`namespace`] | the namespace engine: the trie, the scope, the events, their handlers and the outermost [`Recognition`](namespace::Recognition) |
//! | [`table`] | the per-node table that a resumed lowering shares with the lowering it resumes |
//! | [`by_form`] | the stretch of each top-level form among a tree's positions |
//! | [`circuit`] | the circuit readings of a rule's body, their spider canon and their embeddings |
//!
//! `gandr-surface-lowering` re-exports [`namespace`] and [`circuit`] at their
//! old paths. Each module states its decisions, and its witnesses are this
//! crate's own tests.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the seam test. A
//!   crate boundary encloses a strongly connected component of the module graph
//!   and never cuts through one, so the base takes the four leaves whole.

// Module documentation that predates the shape lint: 16 headings outside the
// vocabulary, 2 decision records, 2 issue references and 1 budget exceeded.
// Each allow leaves with the rewrite that clears its count.
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

pub mod by_form;
pub mod circuit;
pub mod namespace;
pub mod table;
