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
use crate::module::Role;
use crate::module::Sealing;

/// Whether a pass refused a slot it had not refused before.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Refused(pub bool);

impl Lowerer<'_, '_>
{
    /// Carry each refused representation's refusal to the abstract slots
    /// that read it.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every abstract slot, sealed or a kind witness, whose body
    ///   member's held slot holds a refusal holds one too, the member's own
    ///   when the slot held none; the answer is affirmative exactly when some
    ///   slot was unrefused before the call.
    /// - provides: the rule that no atom is declared over a representation that
    ///   did not lower, so a reader of the atom inherits the refusal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed module whose type member names an unbound
    ///   type refuses its atom and every client of it, while an unrelated
    ///   declaration still lowers.
    /// - witness: `modules::modules::a_sealed_component_over_a_refused_member_is_refused_with_it`
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
        for (&slot, recorded) in &self.collected.abstracts {
            let Maybe::Present(represented) = recorded.representation
            else {
                continue;
            };
            let Some(Maybe::Present((at, refusal))) = self
                .collected
                .slots
                .get(usize::from(represented.held))
                .map(|held| held.refusal)
            else {
                continue;
            };
            if let Some(own) = self.collected.slots.get_mut(usize::from(slot))
                && let Maybe::Absent(_) = own.refusal
            {
                own.refuse(at, refusal);
                refused = true;
            }
        }

        Refused(refused)
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
    /// - witness: `modules::modules::opaque_ascription_seals`
    /// - witness: `modules::modules::an_abstract_component_kinds_at_a_universe`
    /// - witness: `modules::modules::a_transparent_abstract_component_reads_its_type_member`
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
        for (&slot, recorded) in &self.collected.abstracts {
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
                | Maybe::Present(kind) => {
                    let Maybe::Present(id) = self.value_type_at(kind.node)
                    else {
                        continue;
                    };
                    id
                },
                | Maybe::Absent(_) => {
                    let id = sink.arena.value_type_universe(
                        Sort::Ground(Universe::FUSS_FREE.sort),
                        Level::constant(Universe::FUSS_FREE.level),
                    );
                    sink.origins.record_value_type(id, named);
                    id
                },
            };
            match own.role {
                | Role::Abstract => {
                    let _replaced = self.sealings.insert(slot, Sealing {
                        kind,
                        representation,
                        extent: SealExtent::from(recorded.extent),
                        sealing: recorded.structure,
                        component: recorded.component,
                    });
                },
                | Role::Witness => {
                    let code = sink.arena.value_quote(representation);
                    let _minted = sink.value(code, written);
                    let _replaced = self.kind_checks.insert(slot, (kind, code));
                },
                | Role::Declared | Role::Held | Role::Operation => {},
            }
        }
    }
}
