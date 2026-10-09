//! **Incremental checking over the core judgement**: a front end hands over
//! one program per revision, as items under stable keys; the crate answers
//! every item's typing exactly as the batch checker would, judging again only
//! the items whose earlier answer no longer holds.
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
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

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
pub use crate::checkpoint::ItemCheckpoint;
pub use crate::checkpoint::Resume;
pub use crate::checkpoint::ResumeCensus;
pub use crate::checkpoint::ResumeError;
pub use crate::checkpoint::check_program;
pub use crate::checkpoint::recall;
pub use crate::checkpoint::resume;
pub use crate::checkpoint::resume_from;
pub use crate::codec::CheckpointBytes;
pub use crate::codec::UnsupportedPersistence;
pub use crate::content::ContentNode;
pub use crate::content::ItemContent;
pub use crate::content::Opacity;
pub use crate::content::Sort;
pub use crate::content::TypeContent;
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
pub use crate::persistence::FileCheckpointStore;
pub use crate::persistence::MemoryCheckpointStore;
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
pub use crate::stream::BranchStatus;
pub use crate::stream::Liveness;
pub use crate::stream::MatchOrigin;
pub use crate::stream::SynthesisEvent;
pub use crate::stream::SynthesisStream;
pub use crate::stream::displaced;
pub use crate::typing::Form;
pub use crate::typing::Refusal;
pub use crate::typing::Site;
pub use crate::typing::Typing;
pub use crate::typing::project;
