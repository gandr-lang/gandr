//! The records of a flattened model implicit that the lowering's context
//! holds.
//!
//! A function that quantifies over a model binds one implicit parameter for
//! each component of the model's signature. These records hold the components,
//! the slot a call reads and what a supply passes for it.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::hole::HoleId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;

use super::BundledTheory;
use super::Packed;
use crate::form::Placed;
use crate::model::ModelComponent;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;

/// A component's place among its slot's components, in signature order: the
/// parameter it binds, and the value a supply passes for it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentPlace(usize);

impl From<usize> for ComponentPlace
{
    /// The component at `place`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: usize) -> Self
    {
        Self(place)
    }
}

impl From<ComponentPlace> for usize
{
    /// The position `place` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: ComponentPlace) -> Self
    {
        place.0
    }
}

/// One component of a flattened model implicit.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlatComponent
{
    /// Its name in the theory.
    pub name: Name,
    /// The frame its parameter binds.
    pub frame: ScopeId,
    /// Whether it is an unindexed sort, which `s.x` reads as a type.
    pub sort: bool,
}

/// A model implicit flattened into one parameter per component, kept by the
/// frame its name resolves to: the last component's.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Flattened
{
    /// The implicit's binder, as the declaration writes it.
    pub binder: Placed,
    /// The components, in signature order.
    pub components: Vec<FlatComponent>,
    /// The sorts the model type fixes, each sort's name beside the type it
    /// is.
    pub fixed: BTreeMap<Name, Placed>,
}

/// The theory a model implicit's type names, as a call or a declaration
/// reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModelSlot
{
    /// The bundle's theories, the outermost first, which holds no component
    /// `fixed` names.
    pub theories: Vec<BundledTheory>,
    /// The sorts the model type fixes, each sort's name beside the type it
    /// is.
    pub fixed: BTreeMap<Name, Placed>,
    /// The theory's path, its name tile last.
    pub theory: crate::form::WrittenPath,
}

impl ModelSlot
{
    /// The components a model of the slot passes, in signature order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn components(&self) -> &[ModelComponent]
    {
        self.theories
            .first()
            .map_or(&[], |theory| theory.signature.components.as_slice())
    }

    /// The sorts the model type fixes, each sort's name beside the type it is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fixed(&self) -> &BTreeMap<Name, Placed>
    {
        &self.fixed
    }
}

/// What a supply passes for a flattened model implicit: one value per
/// component of the slot.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Supplied
{
    /// A module's members, as `pack M at Model(S)` reads them.
    Module(Arc<Packed>),
    /// The parameters of the caller's model implicit, one per component, each
    /// variable's index from the call beside its frame.
    Bound(Vec<(DeBruijnIndex, ScopeId)>),
    /// The holes a capability scope naming no model nominates, one per
    /// component, which the checker fills from the one candidate left.
    Nominated(Vec<HoleId>),
}

/// A model implicit as its declaration writes it, `[s : Model(S) with sort x
/// = A]`: what a printed telescope writes in place of the parameters its
/// components bind.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct WrittenSlot<'source>
{
    /// The implicit's name, `s`.
    pub name: SurfaceName<'source>,
    /// Where the implicit's name is written.
    pub named: ByteSpan,
    /// The node of its model type, `Model(S) with sort x = A`.
    pub declared: NodeIndex,
    /// The theory its model type names, `S`.
    pub theory: SurfaceName<'source>,
    /// Each component's name in signature order, beside whether it is a
    /// sort.
    pub components: Vec<(Name, bool)>,
    /// Each sort the model type fixes, beside the node of the type it fixes
    /// it to.
    pub fixed: Vec<(Name, NodeIndex)>,
}

/// A model slot that a call omits, as the call plans it.
///
/// It holds the declaration that makes the call, the hole nominated for each
/// component, the sorts that the slot's type fixes and the candidates. Each
/// candidate is the module it names beside what it passes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct PlannedModel<'source>
{
    /// The declaration whose body makes the call.
    pub caller: gandr_kernel_term::ConstantIndex,
    /// The hole nominated for each component, in signature order.
    pub holes: Vec<gandr_core_term::hole::HoleId>,
    /// Each sort the slot's model type fixes beside the type it fixes it to,
    /// in the order of the sorts' names.
    pub fixed: Vec<(Name, Placed)>,
    /// The candidates, in the order their modules are declared.
    pub candidates: Vec<(SurfaceName<'source>, Supplied)>,
}
