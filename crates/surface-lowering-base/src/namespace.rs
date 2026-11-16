//! The namespace engine: hierarchical names, the modifier language that
//! transforms namespaces, the scope that carries them, and the outermost scope
//! builtin names are seeded into.
//!
//! The design is yuujinchou's: a namespace is a finite trie from paths to
//! bindings, namespaces are implicit — `nat` names nothing on its own and
//! coexists with `nat.plus` — and every transformation is a term of a small
//! modifier language run where two namespaces meet. What the engine would
//! otherwise have to decide — a selection that matched nothing, two bindings at
//! one path, an extension point — is performed as one of three events and
//! settled by a handler the caller installs.
//!
//! | module | holds |
//! | --- | --- |
//! | [`path`] | [`Segment`], [`NamePath`] and the dotted boundary |
//! | [`trie`] | the carrier [`Trie`] in one arena, [`Binding`], [`Collision`] |
//! | [`modifier`] | the six-constructor [`Modifier`] language and its interpreter |
//! | [`event`] | the three events, [`NamespaceEventHandler`] and the permissive default |
//! | [`scope`] | the two-namespace [`Scope`] and its sections |
//! | [`recognition`] | the outermost [`Recognition`] scope, its seed tables and shadow policy |
//!
//! A path is reachability, never identity: nothing here mints, compares or
//! reads a core identity, and a binding's payload is the caller's business.
//! Every walk is a loop over an explicit stack; nothing recurses at a depth a
//! source controls.
//!
//! # The engine sits in the lowering
//!
//! The alternatives were a crate of its own and the dispatcher. It sits here
//! because the lowering is its one reader: imports and outermost names are
//! decided during lowering. Reversal: a second reader of scope state outside
//! lowering, a session or a language server, moves it to its own crate.
//!
//! # Namespaces, modifiers and scopes
//!
//! `namespace` follows yuujinchou (see the crate's references). A namespace is
//! a finite trie from hierarchical names to bindings; a modifier — `all`, `id`,
//! `none`, `only`, `except`, `renaming`, `in`, `seq`, `union`, `hook` —
//! rewrites one through six core constructors and one interpreter; every
//! not-found, shadow and hook event goes to a `NamespaceEventHandler` at the
//! full path where it happened, so a policy is a handler, never an engine
//! change. A `Scope` holds a visible and an export namespace and a stack of
//! sections: an import reaches the visible namespace, an include both, and
//! closing a section includes its export under a prefix once a modifier has
//! chosen what passes.
//!
//! `NamePath` compares and composes opaque segments, not their diagnostic
//! rendering. The dotted boundary maps the empty string to the root and splits
//! every nonempty string at each period, retaining empty and Unicode segments.
//! A raw segment may itself contain a period; it stays one segment through
//! composition and prefix removal. Display writes the root as `.` and is not an
//! inverse of the dotted boundary. A formatter refusal stops rendering and is
//! returned to the caller.
//!
//! The permissive handler appends one record per callback in execution order.
//! Clearing starts a fresh log without changing the policy: a later binding
//! still wins a collision and a hook still returns its subject. Runtime
//! predicates check event kind, full path, append count and retained binding
//! count without adding equality bounds to generic labels or payloads; bounded
//! interpreter witnesses check those values. Required callback contracts
//! describe how the interpreter uses their outcomes, not properties a callback
//! can establish about a future run.
//!
//! Imports and modifiers commit their target namespace only on success.
//! Includes merge visible before export and retain entries merged before a
//! refusal. Closing a section consumes it before running the closing modifier:
//! modifier refusal restores the parent unchanged, while merge refusal keeps
//! the partial include in that parent. Neither failure reopens the section; a
//! later close reports `NoOpenSection`. Scope predicates check namespace counts
//! and section-stack transitions without requiring equality or cloning generic
//! payloads; the witnesses check exact retained bindings.

mod event;
mod modifier;
mod path;
mod recognition;
mod scope;
mod trie;

pub use crate::namespace::event::EventKind;
pub use crate::namespace::event::EventRejection;
pub use crate::namespace::event::NamespaceEvent;
pub use crate::namespace::event::NamespaceEventHandler;
pub use crate::namespace::event::PermissiveHandler;
pub use crate::namespace::event::RejectionReason;
pub use crate::namespace::modifier::Modifier;
pub use crate::namespace::path::DottedName;
pub use crate::namespace::path::NamePath;
pub use crate::namespace::path::Segment;
pub use crate::namespace::path::SegmentCount;
pub use crate::namespace::path::remainder;
pub use crate::namespace::recognition::Declines;
pub use crate::namespace::recognition::PathResolution;
pub use crate::namespace::recognition::Recognition;
pub use crate::namespace::recognition::RecognitionSite;
pub use crate::namespace::recognition::Recognized;
pub use crate::namespace::recognition::SeedEntry;
pub use crate::namespace::recognition::SeedKind;
pub use crate::namespace::recognition::SeedPosition;
pub use crate::namespace::recognition::SeedTable;
pub use crate::namespace::recognition::ShadowPolicy;
pub use crate::namespace::recognition::ShadowedBuiltin;
pub use crate::namespace::scope::Scope;
pub use crate::namespace::scope::ScopeError;
pub use crate::namespace::trie::Binding;
pub use crate::namespace::trie::BindingCount;
pub use crate::namespace::trie::Bindings;
pub use crate::namespace::trie::Collision;
pub use crate::namespace::trie::Emptiness;
pub use crate::namespace::trie::Trie;
pub use crate::namespace::trie::binding;
pub use crate::namespace::trie::displaced;
