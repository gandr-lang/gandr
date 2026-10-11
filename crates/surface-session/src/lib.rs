//! The interactive session above the dispatcher: each revision of one source
//! lowered, judged, resumed through the incremental checker and persisted.
//!
//! A [`Session`] holds what the batch pipeline does not: the incremental
//! checker's latest resume, the checkpoint store it persists into, and the
//! import scope of the latest accepted revision. Its faces — the REPL, the
//! language server, a terminal interface — read it; it reads none of them.
//!
//! # A submission is a whole revision the caller owns
//!
//! [`Session::submit`] takes the full text of a revision and returns a
//! [`Submission`] borrowing it. The session keeps no text: a face that
//! accumulates lines, or applies an editor's changes, owns the buffer and
//! submits it whole.
//!
//! # The report is the dispatcher's composition
//!
//! A submission runs the dispatcher's two composition halves —
//! [`lower_source`](gandr_surface_dispatcher::lower_source), then
//! [`judge_module`](gandr_surface_dispatcher::judge_module) — so its verdicts
//! are exactly the ones `gandr check` gives the same text, and hands the same
//! lowered declarations, through [`program`], to the incremental checker,
//! which adopts what still answers and persists the checkpoints.
//!
//! # Edits are reconstructed from the lowered core
//!
//! Each accepted [`Submission`] carries the [`EditScript`] from the latest
//! accepted revision before it: [`diff`] of their [`Snapshot`]s, the id-free
//! image of each revision's lowered core. The session keeps the latest
//! snapshot, so a face localizes a source range against it with
//! [`Snapshot::localize`].
//!
//! # A hole-free item is evaluated
//!
//! [`Submission::evaluate`] runs one declaration of the revision on the
//! dispatcher's run stage — the [`Program`](gandr_surface_dispatcher::Program)
//! the composition built — when the checker accepted it whole: a declaration
//! owed its body is a hole and declines, and so does a refused one. A run that
//! reaches a goal is blamed on it rather than declined, because the item run
//! has no hole of its own.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

extern crate alloc;

mod edit;
mod item_source;
mod session;

pub use crate::edit::Action;
pub use crate::edit::ChildSlot;
pub use crate::edit::CorePath;
pub use crate::edit::DeclarationTree;
pub use crate::edit::EditScript;
pub use crate::edit::ItemTree;
pub use crate::edit::Snapshot;
pub use crate::edit::SourceEdit;
pub use crate::edit::Tree;
pub use crate::edit::addressed;
pub use crate::edit::apply;
pub use crate::edit::body_path;
pub use crate::edit::diff;
pub use crate::edit::located;
pub use crate::edit::spanned;
pub use crate::item_source::Revision;
pub use crate::item_source::RevisionFault;
pub use crate::item_source::SurfaceItems;
pub use crate::item_source::fault_span;
pub use crate::item_source::program;
pub use crate::session::ImportRow;
pub use crate::session::KernelCheckpoint;
pub use crate::session::Persistence;
pub use crate::session::Reopened;
pub use crate::session::Resumed;
pub use crate::session::Session;
pub use crate::session::SessionFault;
pub use crate::session::Submission;
pub use crate::session::evaluate;
pub use crate::session::evaluation;
pub use crate::session::import;
pub use crate::session::reopened;
pub use crate::session::resumed;
