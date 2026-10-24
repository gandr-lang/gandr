//! Reducts, as the lowering mints them.
//!
//! Each slot a reduct takes ([`crate::module::ReductSlot`]) restricts the
//! models of the including theory `T'` to the theory `T` it includes:
//!
//! ```text
//! T'.T : U(Model(T') -> F Model(T))
//! T'.T = thunk(λm. r)
//! ```
//!
//! `r` destructures `m` into one binder per field, splitting it link by link
//! where its record nests as pairs, and returns `T`'s bundled record of the
//! fields the inclusion places `T`'s members at, nested as its own fields bind
//! ([`packed_record`]). A sort is its own field of `m`, so the reduct seals
//! nothing. The checker inserts the reduct where a model of `T'` stands at
//! `Model(T)`.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use quenchant_shape::shape::Maybe;

use super::Bundled;
use super::Missing;
use super::bundle_dependence;
use super::packed_record;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::lower::Lowered;
use crate::lower::Lowerer;
use crate::lower::Reading;
use crate::lower::Sink;
use crate::lower::Site;
use crate::model::Dependent;
use crate::model::ModelSignature;
use crate::model::derive;
use crate::module::ComponentPlace;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;

/// A theory a reduct or a forgetting map reads: the theories of its bundled
/// record, the record's type, and how many sorts, operations and rules its
/// signature holds before the laws it states.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(super) struct Bundle
{
    /// The record's theories, the theory itself first.
    bundled: Bundled,
    /// The record's type.
    model: ValueTypeId,
    /// The sorts the theory presents.
    sorts: usize,
    /// The operations it presents.
    operations: usize,
    /// The rules it presents, its faces.
    faces: usize,
}

impl Bundle
{
    /// The record's theories, the theory itself first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(super) const fn bundled(&self) -> &Bundled
    {
        &self.bundled
    }

    /// The record's type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(super) const fn model(&self) -> ValueTypeId
    {
        self.model
    }
}

/// How a lambda over a model of a bundled record destructures it into one
/// binder per field, the last innermost: split link by link where the record
/// nests as pairs — a binding link a dependent pair, split at the returner the
/// lambda returns at, which reads no binder — each split taking the rest of
/// the nesting the one before it bound, and each field bound by its
/// projection where the record is labelled.
///
/// # Specification
/// - executable: none — a data declaration [`Destructured::of`] fills.
#[derive(Clone, Debug)]
pub(super) struct Destructured
{
    /// How many fields the record holds.
    count: usize,
    /// Whether each field's link binds.
    binds: Vec<Dependent>,
    /// Whether the record nests as pairs.
    paired: bool,
}

impl Destructured
{
    /// How a model of the record `signature` bundles is destructured.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn of(signature: &ModelSignature) -> Self
    {
        let binds = bundle_dependence(signature);
        let paired = binds.iter().any(|binds| binds.0);
        Self {
            count: signature.components.len(),
            binds,
            paired,
        }
    }

    /// The index the field at the place `field` is bound at where the body
    /// the destructuring wraps stands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a labelled record, the field's distance from the last;
    ///   for pairs, zero for the last field and, for each one before it, the
    ///   odd index of the first component of the split binding it; nothing past
    ///   the record or past what an index holds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Lowerer::mint_reducts`].
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    #[spec(ensures: |ret| ret.is_none() || usize::from(field) < self.count)]
    pub(super) fn bound_at(
        &self,
        field: ComponentPlace,
    ) -> Option<DeBruijnIndex>
    {
        let field = usize::from(field);
        let last = self.count.checked_sub(1)?;
        let index = if !self.paired {
            last.checked_sub(field)?
        }
        else if field == last {
            0
        }
        else {
            last.checked_sub(field)?
                .checked_sub(1)?
                .checked_mul(2)?
                .checked_add(1)?
        };
        u32::try_from(index).ok().map(DeBruijnIndex::from)
    }

    /// How many binders the destructuring places between the model and the
    /// body it wraps.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one per field for a labelled record; two per split, one split
    ///   per field but the last, for pairs; nothing past what an index holds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's manifest model, its fields labelled, read
    ///   past its own binders.
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    #[spec(ensures: |ret| ret.is_none_or(|depth| {
        usize::try_from(u32::from(depth)).is_ok_and(|depth| depth <= self.count.saturating_mul(2))
    }))]
    pub(super) fn depth(&self) -> Option<Binders>
    {
        let depth = if self.paired {
            self.count.saturating_sub(1).checked_mul(2)?
        }
        else {
            self.count
        };
        u32::try_from(depth).ok().map(Binders::from)
    }

    /// `body` under the destructuring of the model standing at index zero
    /// where the destructuring begins, every node minted carrying `origin`.
    ///
    /// # Specification
    /// - requires: `self` was made of `signature`; `body` reads each field at
    ///   [`Self::bound_at`] and anything outside the model past [`Self::depth`]
    ///   more binders; `returner` reads no binder.
    /// - ensures: for pairs, one split per field but the last, outermost first,
    ///   each of the rest the one before it bound — a dependent split at
    ///   `returner` where the field's link binds; for a labelled record, one
    ///   bind per field of its projection, the first outermost, each reading
    ///   the model past the fields bound before it; `body` itself for no field.
    /// - fails: nothing past what an index holds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Lowerer::mint_reducts`], and a forgetting map's
    ///   labelled manifest model.
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    #[spec(ensures: |ret| ret.is_none_or(|wrapped| sink.arena.computation(wrapped).is_some()))]
    pub(super) fn wrap(
        &self,
        signature: &ModelSignature,
        (body, returner): (ComputationId, CompTypeId),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Option<ComputationId>
    {
        let mut destructured = body;
        if self.paired {
            for link in self.binds.iter().take(self.count.saturating_sub(1)).rev() {
                let rest = sink
                    .arena
                    .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                sink.origins.record_value(rest, origin);
                let pair = ComponentCount::from(2_usize);
                destructured = if link.0 {
                    sink.arena
                        .computation_dependent_split(rest, pair, returner, destructured)
                }
                else {
                    sink.arena.computation_split(rest, pair, destructured)
                };
                sink.origins.record_computation(destructured, origin);
            }
            return Some(destructured);
        }
        for (field, component) in signature.components.iter().enumerate().rev() {
            // `m` stands past the binders of the fields before this one.
            let index = u32::try_from(field).ok()?;
            let model = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
            sink.origins.record_value(model, origin);
            let projection = sink.arena.computation_record_projection(
                model,
                FieldLabel::from(String::from(component.name.as_ref())),
            );
            sink.origins.record_computation(projection, origin);
            destructured = sink.arena.computation_bind(projection, destructured);
            sink.origins.record_computation(destructured, origin);
        }
        Some(destructured)
    }
}

impl<'source> Lowerer<'_, 'source>
{
    /// Mint each reduct the current source's theories take.
    ///
    /// # Specification
    /// - requires: the collection planned the reducts.
    /// - ensures: each reduct slot of the current source holding no refusal is
    ///   minted to its type and body, or refused as unminted.
    /// - panics: none.
    /// - executable: none — each slot's type and body are the checker's to
    ///   judge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a monoid's model restricted to its semigroup's, which
    ///   the checker accepts and inserts.
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    #[cfg_attr(feature = "hotpath", hotpath::measure(impl_type = "Lowerer"))]
    pub(in crate::lower) fn mint_reducts(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let slots: Vec<SlotIndex> = self
            .collected
            .reducts
            .range(SlotIndex::from(self.current.slots) ..)
            .map(|(&slot, _)| slot)
            .collect();
        for slot in slots {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let (span, name) = (entry.named.span, entry.name);
            let origin = Origin::new(entry.named.node, entry.named.span);
            match self.reduct(slot, sink, origin) {
                Ok(minted) => {
                    let _first = self.derivations.insert(slot, minted);
                },
                Err(Missing::Refused(refusal)) => {
                    let _first = self.faults.insert(slot, refusal);
                },
                Err(Missing::Unlowered) => {
                    let _first = self
                        .faults
                        .insert(slot, LoweringRefusal::Unminted { span, name });
                },
            }
        }
    }

    /// The type and body of the reduct slot `slot`, every node of both
    /// carrying `origin` marked [`Insertion::Derived`]: the `include` the slot
    /// is named at answers with the theory it names, never with the reduct.
    ///
    /// # Specification
    /// - requires: `slot` is a reduct slot of the current source.
    /// - ensures: the type `U(Model(T') -> F Model(T))` and the body `thunk(λm.
    ///   r)`, `r` destructuring `m` into one binder per field and returning
    ///   `T`'s record of the fields the slot's inclusion places `T`'s members
    ///   at; a law `T` states, and a circuit rule, which the inclusion does not
    ///   place, at the member of `T'` past its rules of the same name, where
    ///   the include copied it.
    /// - fails: [`Missing::Unlowered`] where either model type does not mint,
    ///   or the inclusion places a member past the including signature or at a
    ///   member of another name.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_reducts`].
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ty, body)| sink.arena.value_type(ty).is_some() && sink.arena.value(body).is_some()))]
    fn reduct(
        &self,
        slot: SlotIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<(ValueTypeId, ValueId), Missing<'source>>
    {
        let reduct = self
            .collected
            .reducts
            .get(&slot)
            .ok_or(Missing::Unlowered)?;
        let below = origin.inserted(Insertion::Derived);
        let source = self.reduct_bundle(reduct.source, sink, below)?;
        let target = self.reduct_bundle(reduct.target, sink, below)?;
        let including = &source
            .bundled
            .theories
            .first()
            .ok_or(Missing::Unlowered)?
            .signature;
        let included = &target
            .bundled
            .theories
            .first()
            .ok_or(Missing::Unlowered)?
            .signature;
        let inclusion = &reduct.inclusion;
        // The member at a place of `T`'s signature — its sorts, then its
        // operations, then its rules — stands at the place of `T'`'s the
        // inclusion gives it, counted the same way; a stated law or a circuit
        // after them stands at `T'`'s member of its name past `T'`'s rules.
        let operations = target.sorts.saturating_add(target.operations);
        let rules = operations.saturating_add(target.faces);
        let stated = source
            .sorts
            .saturating_add(source.operations)
            .saturating_add(source.faces);
        let placed = |place: usize, name: &gandr_theory_levitation::Name| {
            let (list, offset, at) = if place < target.sorts {
                (&inclusion.sorts, 0, place)
            }
            else if place < operations {
                (
                    &inclusion.operations,
                    source.sorts,
                    place.saturating_sub(target.sorts),
                )
            }
            else if place < rules {
                (
                    &inclusion.rules,
                    source.sorts.saturating_add(source.operations),
                    place.saturating_sub(operations),
                )
            }
            else {
                return including
                    .components
                    .iter()
                    .enumerate()
                    .skip(stated)
                    .find(|&(_, held)| held.name == *name)
                    .map(|(at, _)| at);
            };
            list.get(at)
                .map(|&position| offset.saturating_add(usize::from(position)))
        };
        let destructuring = Destructured::of(including);
        let returner = sink.arena.comp_type_returner(target.model);
        sink.origins.record_comp_type(returner, below);
        let mut fields = Vec::with_capacity(included.components.len());
        for (place, member) in included.components.iter().enumerate() {
            let index = placed(place, &member.name)
                .filter(|&at| {
                    including
                        .components
                        .get(at)
                        .is_some_and(|held| held.name == member.name)
                })
                .and_then(|at| destructuring.bound_at(ComponentPlace(at)))
                .ok_or(Missing::Unlowered)?;
            let field = sink.arena.value_variable(Zone::Intuitionistic, index);
            sink.origins.record_value(field, below);
            fields.push(field);
        }
        let record =
            packed_record(included, &fields, sink, (below, below)).ok_or(Missing::Unlowered)?;
        let returned = sink.arena.computation_return(record);
        sink.origins.record_computation(returned, below);
        let destructured = destructuring
            .wrap(including, (returned, returner), sink, below)
            .ok_or(Missing::Unlowered)?;
        let lambda = sink.arena.computation_lambda(destructured);
        sink.origins.record_computation(lambda, below);
        let body = sink.arena.value_thunk(lambda);
        sink.origins.record_value(body, below);
        let arrow = sink.arena.comp_type_arrow(source.model, returner);
        sink.origins.record_comp_type(arrow, below);
        let declared = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(declared, below);

        Ok((declared, body))
    }

    /// The theory whose block holds the slot `theory`, as a reduct reads it:
    /// its bundled record, minted carrying `origin`.
    ///
    /// # Specification
    /// - requires: `theory` is a `theory` block's slot.
    /// - ensures: the theories [`Self::bundled_from`] reads off the block's own
    ///   presentation, the record [`Self::mint_bundle`] mints of them, and the
    ///   counts of the presentation's sorts and operations.
    /// - fails: [`Missing::Unlowered`] where the block presents nothing, its
    ///   signature or a nested theory's does not derive, or the record does not
    ///   mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_reducts`].
    /// - witness: `tests::modules::models::a_model_of_an_extension_stands_where_the_included_model_is_asked`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |bundle| sink.arena.value_type(bundle.model).is_some()))]
    pub(super) fn reduct_bundle(
        &self,
        theory: SlotIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<Bundle, Missing<'source>>
    {
        let held = self
            .collected
            .slots
            .get(usize::from(theory))
            .ok_or(Missing::Unlowered)?;
        let Some(&Maybe::Present(ref presentation)) = self
            .collected
            .descriptions
            .get(&held.introduced_by.node)
            .map(|entry| &entry.presentation)
        else {
            return Err(Missing::Unlowered);
        };
        let members = presentation
            .members()
            .map_err(|_fault| Missing::Unlowered)?;
        let signature = derive(presentation).map_err(|_fault| Missing::Unlowered)?;
        let site = Site {
            at: held.named,
            name: FormName::DECLARATION,
            reading: Reading::ValueType(Frame::Outermost),
        };
        let theories = self
            .bundled_from(site, (theory, held.introduced_by.span.start(), signature))
            .map_err(|_refused| Missing::Unlowered)?;
        let bundled = Bundled {
            theories,
            named: held.named.node,
            manifests: Vec::new(),
        };
        let Maybe::Present(Lowered::ValueType(model)) = self.mint_bundle(&bundled, sink, origin)
        else {
            return Err(Missing::Unlowered);
        };
        Ok(Bundle {
            bundled,
            model,
            sorts: members.sorts.len(),
            operations: members.operations.len(),
            faces: members.laws.len(),
        })
    }
}
