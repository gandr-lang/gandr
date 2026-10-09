//! The core call-by-push-value language: its syntax in a flat arena, the one
//! unified typing context, the definition chain, and the per-scope
//! definitional environment.
//!
//! - [`CoreArena`] owns every [`Value`], [`Computation`], [`ValueType`] and
//!   [`CompType`] node, addressed by four typed ids.
//! - [`Classifier`] is what a type's own type is: a ground sort and a level.
//!   `Type[+, l]` and `Type[-, l]` are the two universe families, and a quote
//!   is the code of a type in one of them.
//! - [`shift_value_type`], [`shift_comp_type`], [`instantiate_comp_type`] and
//!   [`strengthen_comp_type`] are the rewrites a type that mentions a bound
//!   variable needs, as iterative machines memoized per node.
//! - [`Context`] is the two-zone typing context `Γ; Σ`: flat, de Bruijn,
//!   id-addressed and name-free. Names live in the surface syntax and in
//!   diagnostics, above this crate.
//! - [`DefinitionChain`] records each definition's body, as a canonical
//!   subterm-table entry index, and its unfolding height.
//! - [`DefinitionalEnvironment`] decides, scope by scope, whether a definition
//!   is manifest.
//! - [`FailureClass`] is the four-class vocabulary every refusal of the core
//!   pipeline answers to, whichever crate produced it.
//!
//! The crate holds syntax and contexts; evaluation and readback live in
//! `gandr-core-nbe`, which consumes this vocabulary. The design is stated in
//! this crate's `README.md`, § Synopsis, and in the sections it links.

#![no_std]

extern crate alloc;

mod arena;
mod classifier;
mod context;
mod definition;
mod failure;
mod rewrite;
mod syntax;

pub use crate::arena::ArenaWatermark;
pub use crate::arena::CompTypeId;
pub use crate::arena::ComputationId;
pub use crate::arena::CoreArena;
pub use crate::arena::ValueId;
pub use crate::arena::ValueTypeId;
pub use crate::classifier::Classifier;
pub use crate::classifier::Sort;
pub use crate::classifier::SortParameter;
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
pub use crate::failure::FailureClass;
pub use crate::rewrite::Binders;
pub use crate::rewrite::instantiate_comp_type;
pub use crate::rewrite::shift_comp_type;
pub use crate::rewrite::shift_value_type;
pub use crate::rewrite::strengthen_comp_type;
pub use crate::rewrite::strengthening;
pub use crate::syntax::CompType;
pub use crate::syntax::Computation;
pub use crate::syntax::Value;
pub use crate::syntax::ValueType;
pub use crate::syntax::Zone;
