//! The **core language and its one unified context**: call-by-push-value
//! syntax in a flat arena, the two-zone typing context every rule reads, the
//! per-scope definitional environment, and the arena-free definition chain a
//! normalizer lowers.
//!
//! The crate holds **syntax and contexts only**. There is no elaborator here,
//! no value domain, no evaluation and no conversion; those consume this
//! vocabulary rather than living in it.
//!
//! # The alphabet is shared with the kernel; the grammar is not
//!
//! Levels, base types, literals, sum sides, de Bruijn indices, admission
//! positions and canonical subterm-table entry indices are re-used from the
//! trusted base. Sharing the alphabet is what keeps the erasure that carries a
//! core term down to a kernel term an id remapping rather than a payload
//! translation, and what stops the two languages disagreeing about what a
//! literal or a level *is*.
//!
//! The node enums, the arena and the context are this crate's own, and that is
//! the half that matters: an elaboration-only former — a mark, a typed hole, a
//! pattern hole — enters here rather than widening the vocabulary the kernel is
//! obliged to represent, whose closedness is one of the trusted base's stated
//! properties.
//!
//! # One context, four properties
//!
//! There is exactly one spelling of "the context", and it is flat, de Bruijn,
//! id-addressed and name-free. Names live in the surface syntax and in
//! diagnostics, above this crate.
//!
//! **Two zones, kept and flattened.** `Γ` is structural and `Σ` is linear, each
//! a flat stack with its own de Bruijn index space, which is why an occurrence
//! names its zone. The linear zone is the type-level form of "a control capture
//! cannot be naively duplicated" — the half a duplication policy asks rather
//! than re-decides — and its laws are unit-tested here rather than left vacuous
//! until the deferred former that introduces its binders lands.
//!
//! **The definition chain carries content ids.** An arena id is meaningful only
//! in the arena that minted it, and a context is cloned into whatever
//! normalizer a conversion mints, so the chain carries canonical
//! subterm-table entry indices instead: arena-independent by construction,
//! because the table is canonical.
//!
//! **The definitional environment is per-scope from the start.** Transparent
//! ascription forces it — the same atom is manifest inside a sealed module and
//! opaque outside — and the empty per-scope environment degenerates to the flat
//! one at no cost, which is why the shape is paid before the feature that needs
//! it arrives.
//!
//! **The error path is single-valued.** A failing context operation leaves the
//! context at the failure point rather than unwinding it, and that state is
//! asserted rather than described. With recursion banned there is one face, so
//! the divergence the prototype papered over by comparing error values cannot
//! recur.
//!
//! The named ideas, the crate's status, and its plan-milestone mapping are in
//! this crate's `README.md`.

#![no_std]

extern crate alloc;

mod arena;
mod context;
mod definition;
mod syntax;

pub use crate::arena::ArenaWatermark;
pub use crate::arena::CompTypeId;
pub use crate::arena::ComputationId;
pub use crate::arena::CoreArena;
pub use crate::arena::ValueId;
pub use crate::arena::ValueTypeId;
pub use crate::context::BinderDepth;
pub use crate::context::Context;
pub use crate::context::ContextError;
pub use crate::context::LinearUse;
pub use crate::definition::DefinitionChain;
pub use crate::definition::DefinitionEntry;
pub use crate::definition::DefinitionError;
pub use crate::definition::DefinitionHeight;
pub use crate::definition::DefinitionalEnvironment;
pub use crate::definition::ScopeId;
pub use crate::definition::Transparency;
pub use crate::syntax::CompType;
pub use crate::syntax::Computation;
pub use crate::syntax::Value;
pub use crate::syntax::ValueType;
pub use crate::syntax::Zone;
