//! The phase order a module's members stand in. A type member, and a type a
//! signature states, is static; a module's value member and a parameter's
//! value component are dynamic. The two points are ordered, static below
//! dynamic, and a member reads only members at or below its own point: a type
//! reads types, a value reads types and values. A top-level declaration is no
//! module's member and stands outside the order, and so does a slot that only
//! checks or carries another's form.
//!
//! # Witnesses
//! - `tests::modules::a_type_member_reads_types_and_never_values`
//! - `tests::modules::functors::a_type_member_never_reads_its_parameter_s_value`
//!
//! # References
//! - Sterling and Harper, _Logical relations as types: proof-relevant
//!   parametricity for program modules_, JACM 2021 — the phase distinction as
//!   the open and closed modalities of one static proposition.
//! - Harper, Mitchell and Moggi, _Higher-order modules and the phase
//!   distinction_, POPL 1990 — a module's static part a function of its
//!   arguments' static parts alone.

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Site;
use crate::error::LoweringRefusal;
use crate::module::Container;
use crate::module::DeclarationSlot;
use crate::module::Role;
use crate::module::SlotIndex;

quenchant_shape::reason_enum! {
    /// Why a slot stands at no phase.
    mod phased {
        /// The reason the slot is outside the phase order.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The slot is a top-level declaration, or one that checks,
            /// mints or carries another's form rather than standing as a
            /// member.
            Outside,
        }
    }
}

/// Where a module's member stands: static below dynamic.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Phase
{
    /// A type member, or a type a signature states.
    Static,
    /// A value member, or a parameter's value component.
    Dynamic,
}

impl Phase
{
    /// The phase the slot `slot` stands at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a held slot of a module — the owner of a type member's type
    ///   or of a type a signature states — is static; a declared member of a
    ///   module and a parameter's component are dynamic; every other slot is
    ///   outside the order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type member reading a module's value, a type member
    ///   reading a parameter's value, and a value reading a type member, each
    ///   asserted as the exact refusal or reading.
    /// - witness: `tests::modules::a_type_member_reads_types_and_never_values`
    /// - witness: `tests::modules::functors::a_type_member_never_reads_its_parameter_s_value`
    #[spec(ensures: |ret| match (slot.role, slot.container) {
        | (Role::Held, Container::Module(_)) => ret == Maybe::Present(Self::Static),
        | (Role::Declared | Role::Parameter, Container::Module(_)) => ret == Maybe::Present(Self::Dynamic),
        | _ => matches!(ret, Maybe::Absent(_)),
    })]
    fn of(slot: &DeclarationSlot<'_>) -> Maybe<Self, phased::Absent>
    {
        match (slot.role, slot.container) {
            (Role::Held, Container::Module(_)) => Maybe::Present(Self::Static),
            (Role::Declared | Role::Parameter, Container::Module(_)) => {
                Maybe::Present(Self::Dynamic)
            },
            (Role::Held | Role::Declared | Role::Parameter, Container::TopLevel(_))
            | (Role::Witness | Role::Operation | Role::Abstract | Role::Words, _) => {
                Maybe::Absent(phased::Absent::Outside)
            },
        }
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Refuse the read, at `site`, of the member `reached` when it stands
    /// above the phase of the member `site` belongs to.
    ///
    /// # Specification
    /// - requires: `site` is a name or a path read as a value, and `reached` is
    ///   the slot it resolved to.
    /// - ensures: nothing when either slot is outside the order, or when the
    ///   member read stands at or below the reading member.
    /// - provides: the one phase check every value read inside a type passes.
    /// - fails: [`LoweringRefusal::PhaseDependence`] at `site`, naming the
    ///   static member `site` belongs to and the dynamic member it reads.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type member reading a module's value, a type member
    ///   reading a parameter's value, and a value reading a type member, each
    ///   asserted as the exact refusal or reading.
    /// - witness: `tests::modules::a_type_member_reads_types_and_never_values`
    /// - witness: `tests::modules::functors::a_type_member_never_reads_its_parameter_s_value`
    #[spec(ensures: |ret| match ret {
        | Err(LoweringRefusal::PhaseDependence { span, member, reached: read }) => span == site.at.span
            && matches!(self.collected.owner_of(site.at.node), Maybe::Present(own) if self.collected.slots.get(usize::from(own)).is_some_and(|slot| slot.name == member && Phase::of(slot) == Maybe::Present(Phase::Static)))
            && self.collected.slots.get(usize::from(reached)).is_some_and(|slot| slot.name == read && Phase::of(slot) == Maybe::Present(Phase::Dynamic)),
        | Err(_) => false,
        | Ok(()) => true,
    })]
    pub(super) fn phased(
        &self,
        site: Site,
        reached: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(());
        };
        let (Some(reader), Some(read)) = (
            self.collected.slots.get(usize::from(own)),
            self.collected.slots.get(usize::from(reached)),
        )
        else {
            return Ok(());
        };
        match (Phase::of(reader), Phase::of(read)) {
            (Maybe::Present(at), Maybe::Present(found)) if found > at => {
                Err(LoweringRefusal::PhaseDependence {
                    span: site.at.span,
                    member: reader.name,
                    reached: read.name,
                })
            },
            (Maybe::Present(_) | Maybe::Absent(_), Maybe::Present(_) | Maybe::Absent(_)) => Ok(()),
        }
    }
}
