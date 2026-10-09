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
