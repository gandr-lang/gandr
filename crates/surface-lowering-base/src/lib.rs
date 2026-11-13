//! **The base of the lowering**: the parts of `gandr-surface-lowering` that
//! read nothing of the lowering itself. The lowering's families compile over
//! this crate. A family that this crate holds compiles beside the lowering,
//! and an edit of the lowering does not recompile it.
//!
//! The base holds the vocabulary the lowering states its answers in: the
//! refusals and their classes, the forms and the names, the origins, and the
//! description route that reads `data`, `codata` and `theory` declarations
//! into checked descriptions and cells. It also holds the module pass, which
//! collects the declarations of a module by name before the lowering reads a
//! body.
//!
//! | Module | What it holds |
//! | --- | --- |
//! | [`error`] | the typed refusals, [`LoweringRefusal`](error::LoweringRefusal), and where a form left the fragment |
//! | [`classify`] | the four-class failure classifier every refusal carries |
//! | [`unbuilt`] | the features the lowering has not built, each named where a refusal declines it |
//! | [`budget`] | the allowance a lowering spends, the tank of each charged pass and the cells of a face poset |
//! | [`form`] | the named-kind dispatch: the forms the lowering reads and their own tiles |
//! | [`resolve`] | the surface names, the type-head tables and the binder scope |
//! | [`origin`] | the origin side table from each minted core node to its syntax node |
//! | [`attribute`] | the attribute registry, the payload verdicts and the attribute table |
//! | [`unit`](mod@unit) | the sources one lowering reads, end to end |
//! | [`prelude`] | the source laid before every program |
//! | [`written_import`] | an import as its tiles spell it, read before any import binds |
//! | [`slot`] | the role of a lowered slot and whether its source exports it |
//! | [`layered`] | a table and a list held in two parts, the closure's and the module's own |
//! | [`description`] | the description route: declarations read into checked descriptions |
//! | [`desc_cells`] | descriptions elaborated into checked cells |
//! | [`coincide`] | a block's rules decided as one rewriting system |
//! | [`certify`] | the rule certificate the kernel replays |
//! | [`derive`](mod@derive) | a derived equation over a theory's operations and its proof |
//! | [`model`] | `Model(S)`, the signature of a theory's models |
//! | [`described`] | the type each described node states, for a face |
//! | [`namespace`] | the namespace engine: the trie, the scope, the events, their handlers and the outermost [`Recognition`](namespace::Recognition) |
//! | [`table`] | the per-node table that a resumed lowering shares with the lowering it resumes |
//! | [`by_form`] | the stretch of each top-level form among a tree's positions |
//! | [`circuit`] | the circuit readings of a rule's body, their spider canon and their embeddings |
//! | [`module`] | the module pass: declarations collected by name, a module flattened to its members, and the lowered module the checker reads |
//! | [`import`] | the imports of a module, their bindings and their scopes |
//! | [`operation`] | an operation's rules planned as a routing tree and minted as one function |
//! | [`doc`] | documentation comments and their links |
//! | [`layout`] | a bracket that the layout of a block misplaces, read where it was written |
//! | [`lower`] | the records the module pass and the lowering share, exits, runs and literals, the refusal of a `cells` node and a theory read as a capability's interface |
//!
//! `gandr-surface-lowering` names each module at its old path, and re-exports
//! the modules its consumers read. Each module states its decisions. A witness
//! of an item is a test of this crate, a unit test beside its item or a case
//! of the integration target, `tests::<area>::<name>`. Or it is a test of
//! `gandr-surface-lowering`, spelled with that package's name, because the case
//! lowers a source and this crate does not lower.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the seam test. A
//!   crate boundary encloses a strongly connected component of the module graph
//!   and never cuts through one, so the base takes the lowering's tables,
//!   refusals, descriptions and module pass whole.

// Module documentation that predates the shape lint: 114 headings outside the
// vocabulary, 44 decision records, 68 issue references and 26 budgets exceeded.
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
// The profiler's instrumentation names `std`; it links only into the
// benchmark build.
#[cfg(feature = "hotpath")]
extern crate std;

pub mod attribute;
pub mod budget;
pub mod by_form;
pub mod certify;
pub mod circuit;
pub mod classify;
pub mod coincide;
pub mod derive;
pub mod desc_cells;
pub mod described;
pub mod description;
pub mod doc;
pub mod error;
#[cfg(any(test, feature = "fixture"))]
pub mod fixture;
pub mod form;
pub mod import;
pub mod layered;
pub mod layout;
pub mod lower;
pub mod model;
pub mod module;
pub mod namespace;
pub mod operation;
pub mod origin;
pub mod prelude;
pub mod resolve;
pub mod slot;
pub mod table;
pub mod unbuilt;
pub mod unit;
pub mod written_import;
