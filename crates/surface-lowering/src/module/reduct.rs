//! Reducts and forgetting maps, as the collection pass reads them.
//!
//! A `theory` block that includes another keeps the inclusion beside its
//! presentation, and a model of the block restricts along it to a model of
//! the theory it includes. Each theory the block includes, directly or through
//! a theory it includes, takes one slot after the block's, [`Role::Derived`]
//! with the definition half [`Operand::Derived`]: the reduct
//! `Model(T') -> Model(T)` the lowering mints along the composed inclusion
//! ([`ReductSlot`]). A theory reached two ways round takes one slot, the first
//! way's; the ways compose to one inclusion. The slot is entered in no name
//! table; the lowering enters it under the block's path, `T'.T`.
//!
//! A block whose models bundle and which declares an unindexed sort takes one
//! more slot after its reducts, the same way: the forgetting map from its
//! models with every unindexed sort manifest to its models
//! ([`ForgetSlot`]), `(x : Type, …) -> Model(T) with sort C = x … -> Model(T)`,
//! which drops the cell each manifest fixes. The slot carries the block's own
//! name and is entered in no name table.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::TheoryInclusion;
use quenchant_shape::shape::Maybe;

use super::Collected;
use super::Collector;
use super::DeclarationSlot;
use super::Half;
use super::Operand;
use super::Role;
use super::SlotIndex;
use super::declaration_half;
use super::slot_refusal;
use crate::form::Placed;
use crate::model::Included;
use crate::model::ModelForm;
use crate::model::derive;

/// A slot a theory's reduct takes: the theory whose models it restricts, the
/// theory it restricts them to, and the inclusion it restricts along.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `inclusion` places each member of the theory whose block holds
///   the slot `target` among the members of the one whose block holds the slot
///   `source`, composed along every `include` between them.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a monoid's model restricts to its semigroup's, and a
///   theory including two extensions of the semigroup restricts to it once.
/// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReductSlot
{
    /// The including theory's slot.
    pub source: SlotIndex,
    /// The included theory's slot.
    pub target: SlotIndex,
    /// Where each member of the included theory stands in the including one.
    pub inclusion: TheoryInclusion,
}

/// A slot a theory's forgetting map takes: the theory whose models it
/// forgets the manifest sorts of.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: `theory` is the slot of a `theory` block whose models bundle and
///   whose presentation declares an unindexed sort.
/// - executable: none — the record is data the lowering reads.
///
/// # Adequacy
/// - hypothesis: L3 — a counter's models, its carrier manifest at the integers,
///   stand where a counter's are asked.
/// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct ForgetSlot
{
    /// The theory's slot.
    pub theory: SlotIndex,
}

impl Collector<'_, '_>
{
    /// Collect the reducts and the forgetting map of the `theory` block
    /// `block`, which took the slot `theory` and includes `inclusions`.
    ///
    /// # Specification
    /// - requires: `theory` is the clean slot `block` took, and `inclusions`
    ///   its presentation's, in written order.
    /// - ensures: every theory an inclusion names, and every theory that one
    ///   includes as this pass recorded it, is recorded as one the block
    ///   includes, with the inclusion composed along the way it was first
    ///   reached. When the block's models are a bundled record, each such
    ///   theory whose models are one too takes one [`Role::Derived`] slot, in
    ///   that order, under the included theory's name, its definition the
    ///   reduct the lowering mints, named at the `include` it was reached
    ///   through. An inclusion naming no collected block is passed over. A
    ///   block whose models bundle and which declares an unindexed sort then
    ///   takes one [`Role::Derived`] slot under its own name, its definition
    ///   the forgetting map the lowering mints.
    /// - provides: the reduct and forgetting half of the theory collection.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a monoid's semigroup, an extension of the monoid
    ///   reaching the semigroup through it, and two extensions of the semigroup
    ///   included together, reaching it once. A counter, whose carrier is
    ///   unindexed, takes a forgetting map.
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    /// - witness: `description::theory::tests::the_include_subject_s_ways_round_compose_to_one_inclusion`
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    #[spec(
        captures: before = self.collected.slots.len(),
        ensures: self.collected.slots.len() >= before
            && self.collected.slots.len().saturating_sub(before) <= self.collected.included.get(&theory).map_or(0, Vec::len).saturating_add(1),
    )]
    pub(super) fn reducts(
        &mut self,
        (theory, block): (SlotIndex, Placed),
        inclusions: &[Included],
    )
    {
        let mut reached: Vec<(SlotIndex, TheoryInclusion, Placed)> = Vec::new();
        let mut seen: BTreeSet<SlotIndex> = BTreeSet::new();
        for included in inclusions {
            let Maybe::Present(target) = self.collected.owner_of(included.block.node)
            else {
                continue;
            };
            let beyond = self
                .collected
                .included
                .get(&target)
                .cloned()
                .unwrap_or_default();
            let ways = core::iter::once((target, Some(included.inclusion.clone()))).chain(
                beyond
                    .into_iter()
                    .map(|(further, inner)| (further, inner.then(&included.inclusion))),
            );
            for (reaches, inclusion) in ways {
                if let Some(inclusion) = inclusion
                    && seen.insert(reaches)
                {
                    reached.push((reaches, inclusion, included.named));
                }
            }
        }
        let _first = self.collected.included.insert(
            theory,
            reached
                .iter()
                .map(|&(target, ref inclusion, _)| (target, inclusion.clone()))
                .collect(),
        );
        // A reduct is minted between two bundled records, so a theory whose
        // models no record states, a circuit rule's among them, takes none.
        let bundles = |collected: &Collected<'_>, node: NodeIndex| {
            collected
                .descriptions
                .get(&node)
                .and_then(|entry| match entry.presentation {
                    Maybe::Present(ref presentation) => derive(presentation).ok(),
                    Maybe::Absent(_) => None,
                })
                .filter(|signature| {
                    signature
                        .components
                        .iter()
                        .all(|component| component.form.is_ok())
                })
        };
        let Some(own) = bundles(self.collected, block.node)
        else {
            return;
        };
        let container = self.collected.top(block.span.start());
        for (target, inclusion, through) in reached {
            let Some(included) = self.collected.slots.get(usize::from(target))
            else {
                continue;
            };
            let name = included.name;
            if bundles(self.collected, included.introduced_by.node).is_none() {
                continue;
            }
            let minted = SlotIndex(self.collected.slots.len());
            self.collected.slots.push(DeclarationSlot {
                name,
                container,
                role: Role::Derived,
                constant: ConstantIndex::from(minted.0),
                introduced_by: block,
                named: through,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Present(Half {
                    declaration: block,
                    named: through,
                    operand: Operand::Derived,
                }),
                attributes: Vec::new(),
                docs: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            });
            let _fresh = self.collected.reducts.insert(minted, ReductSlot {
                source: theory,
                target,
                inclusion,
            });
        }
        // A model whose unindexed sorts are manifest is a model of the theory
        // once the cells the manifests fix are dropped: the forgetting map.
        let manifests = own.components.iter().any(|component| {
            matches!(component.form, Ok(ModelForm::Sort { ref indices }) if indices.is_empty())
        });
        let Some(held) = self.collected.slots.get(usize::from(theory))
        else {
            return;
        };
        if !manifests {
            return;
        }
        let (name, named) = (held.name, held.named);
        let minted = SlotIndex(self.collected.slots.len());
        self.collected.slots.push(DeclarationSlot {
            name,
            container,
            role: Role::Derived,
            constant: ConstantIndex::from(minted.0),
            introduced_by: block,
            named,
            signature: Maybe::Absent(declaration_half::Absent::Unwritten),
            definition: Maybe::Present(Half {
                declaration: block,
                named,
                operand: Operand::Derived,
            }),
            attributes: Vec::new(),
            docs: Vec::new(),
            refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
        });
        let _fresh = self.collected.forgets.insert(minted, ForgetSlot { theory });
    }
}
