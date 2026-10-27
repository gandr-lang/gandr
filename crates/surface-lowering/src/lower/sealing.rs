//! The lowering half of an abstract component: the declaration each abstract
//! slot amounts to once its kind and its representation have lowered, and
//! the refusal a slot inherits from a representation that did not lower. The
//! design lives with the collection pass (`crate::module::sealing`).

use anodized::spec;
use gandr_core_term::Sort;
use gandr_kernel_strata::Level;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use super::Lowerer;
use super::Sink;
use super::Universe;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::shape_of;
use crate::module::Role;
use crate::module::Sealing;
use crate::module::SlotIndex;

/// Whether a pass refused a slot it had not refused before.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Refused(pub bool);

impl<'source> Lowerer<'_, 'source>
{
    /// Carry each refused representation's refusal to the abstract slots
    /// that read it, and refuse each abstract slot whose representation is a
    /// computation type.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every abstract slot, sealed or a kind witness, whose body
    ///   member's held slot holds a refusal holds one too, the member's own
    ///   when the slot held none; one whose body member's definition is a
    ///   computation type holds the wrong-sort refusal at that definition, as
    ///   its atom and its kind are value types; the answer is affirmative
    ///   exactly when some slot was unrefused before the call.
    /// - provides: the rule that no atom is declared over a representation that
    ///   did not lower or is no value type, so a reader of the atom inherits
    ///   the refusal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed module whose type member names an unbound
    ///   type refuses its atom and every client of it, while an unrelated
    ///   declaration still lowers.
    /// - witness: `tests::modules::a_sealed_component_over_a_refused_member_is_refused_with_it`
    /// - witness: `tests::modules::a_type_member_names_a_computation_type_3080`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every abstract slot once; the check counts the refused ones before and after and reads each once more"
        )
    )]
    #[spec(
        captures: before = self.collected.abstracts.keys().filter(|&&slot| matches!(self.collected.slots.get(usize::from(slot)).map(|own| own.refusal), Some(Maybe::Present(_)))).count(),
        ensures: |ret| {
            self.collected.abstracts.iter().all(|(&slot, recorded)| match recorded.representation {
                | Maybe::Present(represented) => {
                    !matches!(self.collected.slots.get(usize::from(represented.held)).map(|held| held.refusal), Some(Maybe::Present(_)))
                        || matches!(self.collected.slots.get(usize::from(slot)).map(|own| own.refusal), Some(Maybe::Present(_)))
                },
                | Maybe::Absent(_) => true,
            }) && ret.0 == (self.collected.abstracts.keys().filter(|&&slot| matches!(self.collected.slots.get(usize::from(slot)).map(|own| own.refusal), Some(Maybe::Present(_)))).count() > before)
        },
    )]
    pub(super) fn refuse_unrepresented(&mut self) -> Refused
    {
        let mut refused = false;
        for (&slot, recorded) in self
            .collected
            .abstracts
            .range(SlotIndex::from(self.current.slots) ..)
        {
            let Maybe::Present(represented) = recorded.representation
            else {
                continue;
            };
            let inherited = match self
                .collected
                .slots
                .get(usize::from(represented.held))
                .map(|held| held.refusal)
            {
                Some(Maybe::Present(held)) => held,
                Some(Maybe::Absent(_)) | None => {
                    let Some(refusal) = self.computation_refusal(represented.defined)
                    else {
                        continue;
                    };
                    (represented.defined.node, refusal)
                },
            };
            if let Some(own) = self.collected.slots.get_mut(usize::from(slot))
                && let Maybe::Absent(_) = own.refusal
            {
                own.refuse(inherited.0, inherited.1);
                refused = true;
            }
        }

        Refused(refused)
    }

    /// The refusal of the type member defined at `defined` where a value type
    /// is read of it, when its definition is a computation type.
    ///
    /// # Specification
    /// - requires: the member's definition is seeded.
    /// - ensures: for a definition among the computation members, the
    ///   wrong-sort refusal at it naming its form, or the refusal reading its
    ///   form met; nothing for a value member or a definition with no form.
    /// - provides: the one refusal of a computation member read as a value type
    ///   by an abstract component, an ascription's or a functor parameter's.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a seal and a functor's abstract parameter over a
    ///   computation member are each refused at its definition.
    /// - witness: `tests::modules::a_type_member_names_a_computation_type_3080`
    #[spec(ensures: |ret| ret.is_none() || self.computation_members.contains(&defined.node))]
    pub(super) fn computation_refusal(
        &self,
        defined: Placed,
    ) -> Option<LoweringRefusal<'source>>
    {
        if !self.computation_members.contains(&defined.node) {
            return None;
        }
        match shape_of(self.pbg, self.tree.node(defined.node)?) {
            Ok(Shape::Form { name, .. }) => Some(LoweringRefusal::OutOfFragment {
                span: defined.span,
                form: name,
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            }),
            Ok(_) => None,
            Err(refusal) => Some(refusal),
        }
    }

    /// Lower every unrefused abstract slot to its declaration.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each unrefused abstract slot whose representation and written
    ///   kind lowered is recorded with its kind, the fuss-free universe minted
    ///   at the component's name when none is written: an opaque ascription's
    ///   slot as the abstract type over the representation, with its extent and
    ///   site, and a transparent one's kind witness as the check of the
    ///   representation's code at the kind, the code's origin the member's
    ///   type.
    /// - provides: the declarations [`Self::outcome`] reads for abstract slots.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed component with no kind, one with a written
    ///   universe and a transparent one each lower to the exact declaration.
    /// - witness: `tests::modules::opaque_ascription_seals`
    /// - witness: `tests::modules::an_abstract_component_kinds_at_a_universe`
    /// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every abstract slot once, minting each declaration; the check reads each minted sealing and kind check once"
        )
    )]
    #[spec(
        ensures: self.sealings.keys().chain(self.kind_checks.keys()).all(|slot| {
            self.collected.abstracts.contains_key(slot)
                && self.collected.slots.get(usize::from(*slot)).is_some_and(|own| matches!(own.refusal, Maybe::Absent(_)))
        }),
    )]
    pub(super) fn mint_abstracts(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        for (&slot, recorded) in self
            .collected
            .abstracts
            .range(SlotIndex::from(self.current.slots) ..)
        {
            let Some(own) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            let (Maybe::Absent(_), Maybe::Present(represented)) =
                (own.refusal, recorded.representation)
            else {
                continue;
            };
            let (Maybe::Present(representation), Maybe::Present(named), Maybe::Present(written)) = (
                self.value_type_at(represented.defined.node),
                self.origin_at(recorded.named.node),
                self.origin_at(represented.defined.node),
            )
            else {
                continue;
            };
            let kind = match recorded.kind {
                Maybe::Present(kind) => {
                    let Maybe::Present(id) = self.value_type_at(kind.node)
                    else {
                        continue;
                    };
                    id
                },
                Maybe::Absent(_) => {
                    let id = sink.arena.value_type_universe(
                        Sort::Ground(Universe::FUSS_FREE.sort),
                        Level::constant(Universe::FUSS_FREE.level),
                    );
                    sink.origins.record_value_type(id, named);
                    id
                },
            };
            match own.role {
                Role::Abstract => {
                    let _replaced = self.sealings.insert(slot, Sealing {
                        kind,
                        representation,
                        extent: SealExtent::from(recorded.extent),
                        sealing: recorded.structure,
                        component: recorded.component,
                        mark: recorded.mark,
                    });
                },
                Role::Witness => {
                    let code = sink.arena.value_quote(representation);
                    let _minted = sink.value(code, written);
                    let _replaced = self.kind_checks.insert(slot, (kind, code));
                },
                Role::Declared
                | Role::Held
                | Role::Operation
                | Role::Derived
                | Role::Words
                | Role::Parameter
                | Role::Generic
                | Role::Admitted => {},
            }
        }
    }
}
