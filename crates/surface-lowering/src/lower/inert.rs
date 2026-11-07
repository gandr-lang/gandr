//! Inert declarations. A theory's operation marked `@[ inert ]` is a field
//! the manifest step reads, a package's name or version: a model's component
//! for it is inert. A definition marked `@[ inert ]` is inert too, so a map
//! or a render over inert fields has a declaration to live in. Only another
//! inert declaration reads an inert one. A content key names what an item
//! references, not what that holds, so an edit to an inert value moves no
//! other item's key exactly when nothing else reads it (#533 § p2); the
//! package address then leaves the inert declarations out.
//!
//! # Witnesses
//! - `tests::modules::models::an_inert_field_is_read_only_by_another_3029`
//! - `tests::modules::models::an_inert_definition_is_read_only_by_an_inert_reader_6141`

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Site;
use crate::SurfaceName;
use crate::error::LoweringRefusal;
use crate::module::Container;
use crate::module::DeclarationSlot;
use crate::module::Inertness;
use crate::module::Role;
use crate::module::SlotIndex;

impl<'source> Lowerer<'_, 'source>
{
    /// Whether the declaration at `slot` is inert: a definition marked
    /// `@[ inert ]`, or a model's inert component, a member declared in a
    /// module ascribed `Model(T)` under the name of an operation `T` marks
    /// `@[ inert ]`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: affirmative exactly for a marked definition, and for a
    ///   declared member of a module whose ascription derives a model signature
    ///   with an inert component of the member's name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::inert_read`].
    /// - witness: `tests::modules::models::an_inert_field_is_read_only_by_another_3029`
    /// - witness: `tests::modules::models::an_inert_definition_is_read_only_by_an_inert_reader_6141`
    #[spec(ensures: |ret| ret == Inertness::Content
        || self.collected.inert.contains(&slot)
        || self.collected.slots.get(usize::from(slot)).is_some_and(|entry| matches!(entry.role, Role::Declared)))]
    pub(super) fn inertness(
        &self,
        slot: SlotIndex,
    ) -> Inertness
    {
        if self.collected.inert.contains(&slot) {
            return Inertness::Inert;
        }
        let Some(&DeclarationSlot {
            role: Role::Declared,
            container: Container::Module(module),
            name,
            ..
        }) = self.collected.slots.get(usize::from(slot))
        else {
            return Inertness::Content;
        };
        let Some(Maybe::Present(model)) = self
            .collected
            .structures
            .get(usize::from(module))
            .map(|structure| structure.model)
        else {
            return Inertness::Content;
        };
        let inert = matches!(
            self.collected.models.get(&model),
            Maybe::Present(signature) if signature.components.iter().any(|component| {
                component.inert && component.name.as_ref() == name.as_ref()
            })
        );
        if inert {
            Inertness::Inert
        }
        else {
            Inertness::Content
        }
    }

    /// Refuse the read, at `site`, of `reached` when it is inert and the
    /// declaration `site` belongs to is not.
    ///
    /// # Specification
    /// - requires: `site` is a name or a path read as a value, and `reached` is
    ///   what it resolved to: the slot it names, or the inert component a
    ///   selection off a model binder reads.
    /// - ensures: nothing when the read declaration is not inert, or when the
    ///   reading declaration is itself inert.
    /// - provides: the one check every read of an inert declaration passes.
    /// - fails: [`LoweringRefusal::InertRead`] at `site`, naming the reading
    ///   declaration and the inert declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a top-level declaration reading a package's name by
    ///   its path, a member of the model reading it by its name, a function
    ///   selecting it off a model binder, and a model's version read from
    ///   another model's, each asserted as the exact refusal or reading; an
    ///   inert definition reading an inert field and another inert definition,
    ///   and a content definition refused at its read of an inert definition.
    /// - witness: `tests::modules::models::an_inert_field_is_read_only_by_another_3029`
    /// - witness: `tests::modules::models::an_inert_definition_is_read_only_by_an_inert_reader_6141`
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
                Some(entry) if self.inertness(slot) == Inertness::Inert => entry.name,
                Some(_) | None => return Ok(()),
            },
            Read::Selected(name) => name,
        };
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(());
        };
        match self.collected.slots.get(usize::from(own)) {
            Some(entry) if self.inertness(own) == Inertness::Content => {
                Err(LoweringRefusal::InertRead {
                    span: site.at.span,
                    member: entry.name,
                    reached: read,
                })
            },
            Some(_) | None => Ok(()),
        }
    }
}

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
