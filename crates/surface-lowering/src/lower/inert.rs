//! The inert fields of a model. A theory's operation marked `@[ inert ]` is a
//! field the manifest step reads, a package's name or version: a model's
//! component for it is inert, and only another inert component reads it. A
//! content key names what an item references, not what that holds, so an
//! edit to an inert value moves no other item's key exactly when nothing else
//! reads it (#533 § p2); the package address then leaves the inert components
//! out.
//!
//! # Witnesses
//! - `tests::modules::models::an_inert_field_is_read_only_by_another_3029`

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Site;
use crate::SurfaceName;
use crate::error::LoweringRefusal;
use crate::module::Container;
use crate::module::DeclarationSlot;
use crate::module::Role;
use crate::module::SlotIndex;

impl<'source> Lowerer<'_, 'source>
{
    /// Whether `slot` is a model's inert component: a member declared in a
    /// module ascribed `Model(T)` under the name of an operation `T` marks
    /// `@[ inert ]`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly for a declared member of a module whose
    ///   ascription derives a model signature with an inert component of the
    ///   member's name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::inert_read`].
    /// - witness: `tests::modules::models::an_inert_field_is_read_only_by_another_3029`
    #[spec(ensures: |ret| !ret.0 || matches!(slot.role, Role::Declared))]
    fn inert_component(
        &self,
        slot: &DeclarationSlot<'_>,
    ) -> Inert
    {
        let (Role::Declared, Container::Module(module)) = (slot.role, slot.container)
        else {
            return Inert(false);
        };
        let Some(Maybe::Present(model)) = self
            .collected
            .structures
            .get(usize::from(module))
            .map(|structure| structure.model)
        else {
            return Inert(false);
        };
        Inert(
            self.collected
                .models
                .get(usize::from(model))
                .is_some_and(|signature| {
                    signature.components.iter().any(|component| {
                        component.inert && component.name.as_ref() == slot.name.as_ref()
                    })
                }),
        )
    }

    /// Refuse the read, at `site`, of `reached` when it is an inert component
    /// and the declaration `site` belongs to is none.
    ///
    /// # Specification
    /// - requires: `site` is a name or a path read as a value, and `reached` is
    ///   what it resolved to: the slot it names, or the inert component a
    ///   selection off a model binder reads.
    /// - ensures: nothing when the read component is not inert, or when the
    ///   reading declaration is itself an inert component.
    /// - provides: the one check every read of an inert field passes.
    /// - fails: [`LoweringRefusal::InertRead`] at `site`, naming the reading
    ///   declaration and the inert component.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a top-level declaration reading a package's name by
    ///   its path, a member of the model reading it by its name, a function
    ///   selecting it off a model binder, and a model's version read from
    ///   another model's, each asserted as the exact refusal or reading.
    /// - witness: `tests::modules::models::an_inert_field_is_read_only_by_another_3029`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::InertRead { span, reached: read, .. }) => span == site.at.span
            && match reached {
                | Read::Slot(slot) => self.collected.slots.get(usize::from(slot)).is_some_and(|entry| entry.name == read),
                | Read::Selected(name) => name == read,
            },
        | Err(_) => false,
        | Ok(()) => true,
    })]
    pub(super) fn inert_read(
        &self,
        site: Site,
        reached: Read<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let read = match reached {
            Read::Slot(slot) => match self.collected.slots.get(usize::from(slot)) {
                Some(entry) if self.inert_component(entry).0 => entry.name,
                Some(_) | None => return Ok(()),
            },
            Read::Selected(name) => name,
        };
        let reader = match self.collected.owner_of(site.at.node) {
            Maybe::Present(own) => self.collected.slots.get(usize::from(own)),
            Maybe::Absent(_) => None,
        };
        match reader {
            Some(entry) if !self.inert_component(entry).0 => Err(LoweringRefusal::InertRead {
                span: site.at.span,
                member: entry.name,
                reached: read,
            }),
            Some(_) | None => Ok(()),
        }
    }
}

/// Whether a slot is a model's inert component.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Inert(bool);

/// What a read resolved to, for [`Lowerer::inert_read`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Read<'source>
{
    /// A declaration, by its slot.
    Slot(SlotIndex),
    /// A component its theory marks inert, selected off a model binder, by
    /// its name.
    Selected(SurfaceName<'source>),
}
