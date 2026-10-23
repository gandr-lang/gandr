//! **Incremental checking over the core judgement**: a front end hands over
//! one program per revision, as items under stable keys; the crate answers
//! every item's typing exactly as the batch checker would, judging again only
//! the items whose earlier answer has gone stale.
//!
//! # Five pieces
//!
//! **The item seam.** [`Program`] holds [`Item`]s — a front end's
//! [`ItemKey`] beside the checker's own [`gandr_core_checker::Declaration`] —
//! over one arena. Constants are read as the [`Reference`] their position
//! resolves to, so nothing that must survive an edit is stated in positions.
//!
//! **The conservative footprint.** [`footprint_of`] lists every reference an
//! item mentions, and those in type positions apart: the read relation a value
//! change closes over.
//!
//! **Validated resume.** [`resume`] runs the one forward pass batch runs, with
//! a memo recalling each item's base checkpoint by content; a recalled
//! checkpoint is adopted only when its support — the signature answers its
//! judgement consulted — holds pointwise in the edited program and no type
//! position of it reads a definition whose value changed. [`check_program`]
//! is the same pass with a memo that recalls nothing.
//!
//! **Content-addressed checkpoints.** [`Checkpoints`] persist under their
//! program's BLAKE3 address in a [`MemoryCheckpointStore`] or an atomic
//! [`FileCheckpointStore`], in one canonical encoding that refuses anything
//! else on the way back in.
//!
//! **The synthesis stream.** [`SynthesisStream`] publishes one event per item
//! — its [`ItemHandle`], typing and adoption — then the match liveness its
//! producer computed.
//!
//! # Example
//!
//! ```
//! use gandr_core_checker::CheckBudget;
//! use gandr_core_checker::Declaration;
//! use gandr_core_checker::OriginToken;
//! use gandr_core_checker::signature;
//! use gandr_core_incremental::Adoption;
//! use gandr_core_incremental::Item;
//! use gandr_core_incremental::ItemKey;
//! use gandr_core_incremental::Program;
//! use gandr_core_incremental::check_program;
//! use gandr_core_incremental::resume;
//! use gandr_core_term::CoreArena;
//! use gandr_kernel_term::ConstantIndex;
//! use gandr_kernel_term::IntegerLiteral;
//! use gandr_kernel_term::Literal;
//! use gandr_kernel_term::Magnitude;
//! use gandr_kernel_term::Sign;
//! use quenchant_shape::shape::Maybe;
//!
//! // def a = 0 ; def b = a
//! let program = |edited: bool| {
//!     let mut arena = CoreArena::new();
//!     let digits = if edited { "1" } else { "0" };
//!     let literal = arena.value_literal(Literal::Integer(IntegerLiteral::new(
//!         Sign::NonNegative,
//!         Magnitude::from_decimal_text(digits.into()).expect("decimal digits"),
//!     )));
//!     let a = arena.value_constant(ConstantIndex::from(0_usize));
//!     let item = |key: &str, position: usize, body| {
//!         Item::new(
//!             ItemKey::from(key),
//!             Declaration::new(
//!                 ConstantIndex::from(position),
//!                 Maybe::Absent(signature::Absent::Unsigned),
//!                 Maybe::Present(body),
//!                 OriginToken::from(position),
//!             ),
//!         )
//!     };
//!     Program::new(arena, vec![item("a", 0, literal), item("b", 1, a)]).expect("ascending")
//! };
//!
//! let base = check_program(&mut program(false), CheckBudget::DEFAULT).expect("order");
//! let edited = resume(base, &mut program(true)).expect("order");
//! // a's value changed and its type did not: b still reads an integer.
//! assert_eq!(edited.adoptions(), [Adoption::Judged, Adoption::Adopted]);
//! ```
//!
//! # Specification evidence
//!
//! Item-level `#[spec]` predicates check observable boundaries and transitions.
//! Each `# Adequacy` section names its witness and bounds the claim; a data
//! declaration, abstract protocol or unsupported opaque return states why it
//! has no executable predicate. Generated differential cases support a
//! finite-domain claim, not a proof over every program.
//!
//! | Evidence | Witness surface | Boundary |
//! | -------- | --------------- | -------- |
//! | Batch equivalence and real adoption | the differential suite, `tests/incremental.rs` | faithful records, named edits, generated single edits and edit chains; forged records expose the trust premise |
//! | Edit and lowering semantics | `tests/common.rs` and `tests/generate.rs` | forward and shadowed names, maximal literals, missing indices, clamped insertion, coordinated rename and modular integer selection |
//! | Type-position dependencies | `footprint` and the guards in `checkpoint` | quoted abstract types, recorded-answer types, cycles and opaque readers |
//! | Canonical representation | `content` and `codec` | all supported node sorts, graph discovery, payloads, malformed tags, lengths and canonicality |
//! | Store failure atomicity | `persistence` and `tests/defects.rs` | dangling ids and capped levels preserve stored records; filesystem cleanup remains best effort |
//! | Reachability and work | `tests/defects.rs` | deterministic value-only-edit census, shadowing termination and exact work counts for chains of 250 through 2,000 items; zero-length chains are empty |
//! | Session and stream transitions | `session` and `stream` | retained state on failure, item ordering, liveness and terminal events |
//!
//! The content vocabulary includes sorted universes, quotes, decodes, static
//! operators and native paths. A static Pi seats as a value type; static
//! lambdas, applications and quotes are terms, not seatable types. The native
//! content format in `content` binds that vocabulary and its refusal payloads;
//! another magic is rejected rather than interpreted under different tags.
//! Native primitives, modules and packages are outside this crate’s vocabulary.
//!
//! # Consumer
//!
//! The first consumer is `gandr-surface-session`: it lowers each submission,
//! hands the program to `IncrementalSession`, and reports the resume beside the
//! dispatcher's composition of the same text.
//!
//! # References
//!
//! - Thomas J. Porter, Marisa Kirisame, Ivan Wei, Pavel Panchekha, and Cyrus
//!   Omar. "Incremental Bidirectional Typing via Order Maintenance."
//!   _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October
//!   2025), pages 1865–1892. `doi:10.1145/3763117`; preprint `arXiv:2504.08946`
//!   — incremental typing over an order-maintenance structure, the setting this
//!   crate's item order serves.
//! - Paul F. Dietz and Daniel D. Sleator. "Two Algorithms for Maintaining Order
//!   in a List." In _Proceedings of the Nineteenth Annual ACM Symposium on
//!   Theory of Computing (STOC '87)_, pages 365–372, 1987.
//!   `doi:10.1145/28395.28434` — the order-maintenance problem the handles live
//!   in.
//! - Andrey Mokhov, Neil Mitchell, and Simon Peyton Jones. "Build Systems à la
//!   Carte." _Proceedings of the ACM on Programming Languages_ 2, ICFP (2018),
//!   Article 79. `doi:10.1145/3236774` — verifying traces: a result is reused
//!   when the recorded values of what it read still match, which is what a
//!   checkpoint's support is.
//! - Michael L. Fredman. "On Computing the Length of Longest Increasing
//!   Subsequences." _Discrete Mathematics_ 11, 1 (1975), pages 29–35.
//!   `doi:10.1016/0012-365X(75)90103-X` — the patience-sorting bound the handle
//!   splice runs in.
//! - Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko
//!   Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." 2020.
//!   <https://github.com/BLAKE3-team/BLAKE3-specs> — the digest behind memo
//!   identities and content addresses.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is stated in the documentation of the module it governs.

// Module documentation that predates the shape lint: 31 headings outside the
// vocabulary, 8 decision records and 7 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

mod boundary;
mod checkpoint;
mod codec;
mod content;
#[cfg(test)]
mod fixture;
mod footprint;
mod order;
mod persistence;
mod region;
mod session;
mod stream;
mod support;
mod typing;

pub use crate::boundary::ItemCount;
pub use crate::boundary::ItemOrdinal;
pub use crate::boundary::LivenessEmpty;
pub use crate::boundary::MatchOrdinal;
pub use crate::boundary::NodeIndex;
pub use crate::boundary::Occurrence;
pub use crate::boundary::RecordCount;
pub use crate::boundary::SourceItemOrdinal;
pub use crate::boundary::SubmissionOrdinal;
pub use crate::checkpoint::Adoption;
pub use crate::checkpoint::Answer;
pub use crate::checkpoint::Answered;
pub use crate::checkpoint::Checkpoints;
pub use crate::checkpoint::ContentKey;
pub use crate::checkpoint::ItemCheckpoint;
pub use crate::checkpoint::Leading;
pub use crate::checkpoint::Resume;
pub use crate::checkpoint::ResumeCensus;
pub use crate::checkpoint::ResumeError;
pub use crate::checkpoint::check_program;
pub use crate::checkpoint::content_keys;
pub use crate::checkpoint::lead;
pub use crate::checkpoint::leading;
pub use crate::checkpoint::recall;
pub use crate::checkpoint::resume;
pub use crate::checkpoint::resume_after;
pub use crate::checkpoint::resume_from;
pub use crate::codec::CheckpointBytes;
pub use crate::codec::UnsupportedPersistence;
pub use crate::content::AbstractRoots;
pub use crate::content::ContentNode;
pub use crate::content::DataContent;
pub use crate::content::DataRoots;
pub use crate::content::DeclarationRoots;
pub use crate::content::InterfaceRoots;
pub use crate::content::ItemContent;
pub use crate::content::Opacity;
pub use crate::content::Sort;
pub use crate::content::TypeContent;
pub use crate::content::map_children;
pub use crate::content::referencing;
pub use crate::content::seating;
pub use crate::content::site;
pub use crate::footprint::Footprint;
pub use crate::footprint::HoleMark;
pub use crate::footprint::footprint_of;
pub use crate::order::ItemHandle;
pub use crate::order::SpliceCensus;
pub use crate::order::handle;
pub use crate::persistence::BackendArtifact;
pub use crate::persistence::CheckpointAddress;
pub use crate::persistence::CheckpointObserver;
pub use crate::persistence::CheckpointStore;
pub use crate::persistence::CheckpointStoreError;
pub use crate::persistence::DiscardingCheckpointStore;
pub use crate::persistence::FileCheckpointStore;
pub use crate::persistence::Keeping;
pub use crate::persistence::MemoryCheckpointStore;
pub use crate::persistence::RestoreFrom;
pub use crate::persistence::Restorer;
pub use crate::persistence::address_of;
pub use crate::persistence::decode_checkpoints;
pub use crate::persistence::encode_checkpoints;
pub use crate::persistence::persist;
pub use crate::persistence::restore;
pub use crate::persistence::restored;
pub use crate::persistence::stored;
pub use crate::region::Item;
pub use crate::region::ItemKey;
pub use crate::region::ItemSource;
pub use crate::region::Program;
pub use crate::region::ProgramError;
pub use crate::region::Reference;
pub use crate::region::naming;
pub use crate::session::IncrementalSession;
pub use crate::session::SessionError;
pub use crate::session::submitted;
pub use crate::stream::Liveness;
pub use crate::stream::MatchOrigin;
pub use crate::stream::SynthesisEvent;
pub use crate::stream::SynthesisStream;
pub use crate::stream::displaced;
pub use crate::support::SupportedNode;
pub use crate::typing::Form;
pub use crate::typing::Refusal;
pub use crate::typing::Site;
pub use crate::typing::Typing;
pub use crate::typing::project;
