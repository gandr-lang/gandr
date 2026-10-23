//! Forgetting maps, as the lowering mints them.
//!
//! The slot a forgetting map takes ([`crate::module::ForgetSlot`]) carries a
//! model of a theory whose sorts `C₁ … Cₙ` are manifest to a model of the
//! theory, dropping the cell each manifest fixes, or to a model of a theory it
//! includes, restricting along the inclusion after:
//!
//! ```text
//! T.forget : U((x₁ : Type) → … → (m : Model(T) with sort C₁ = x₁ …) → F Model(S))
//! T.forget = thunk(λx₁ … λm. r)
//! ```
//!
//! `S` is `T` itself or a theory a reduct of `T` restricts to. `r`
//! destructures `m` as a reduct does ([`super::reduct`]) and returns `S`'s
//! bundled record, each fixed sort's field the carrier it is fixed to and
//! every other field, an unfixed sort's among them, the binder of `m`'s field
//! of its name: a reduct places each member of `S` at the member of `T` of its
//! name. The checker inserts the map where a model with those sorts manifest
//! stands at `Model(S)`, solving the carriers from the model's type.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::Bundled;
use super::Missing;
use super::packed_record;
use super::reduct::Destructured;
use crate::error::LoweringRefusal;
use crate::lower::Lowered;
use crate::lower::Lowerer;
use crate::lower::Sink;
use crate::lower::Universe;
use crate::model::ModelForm;
use crate::module::ComponentPlace;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::Origin;

impl<'source> Lowerer<'_, 'source>
{
    /// Mint each forgetting map the current source's theories take.
    ///
    /// # Specification
    /// - requires: the collection planned the forgetting maps.
    /// - ensures: each forgetting slot of the current source holding no refusal
    ///   is minted to its type and body, or refused as unminted.
    /// - panics: none.
    /// - executable: none — each slot's type and body are the checker's to
    ///   judge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's map, which the checker accepts and
    ///   inserts where a counter whose carrier is manifest is asked for a
    ///   counter.
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    pub(in crate::lower) fn mint_forgets(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let slots: Vec<SlotIndex> = self
            .collected
            .forgets
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
            match self.forget(slot, sink, origin) {
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

    /// The type and body of the forgetting slot `slot`, every node of both
    /// carrying `origin` marked [`Insertion::Derived`].
    ///
    /// # Specification
    /// - requires: `slot` is a forgetting slot of the current source.
    /// - ensures: the type `U((x₁ : Type) → … → M → F Model(S))`, one dependent
    ///   arrow over the fuss-free universe per sort the slot fixes, in
    ///   signature order, `M` the record of `T`'s models with each such sort
    ///   manifest at the decode of its carrier, and `S` the theory the slot
    ///   returns a model of; the body `thunk(λx₁ … λm. r)`, `r` destructuring
    ///   `m` as [`Destructured`] does and returning `S`'s record, each fixed
    ///   sort's field its carrier and every other field the binder of the field
    ///   of `M` of its name.
    /// - fails: [`Missing::Unlowered`] where a model type does not mint, a
    ///   field of `S` names no field of `M` nor a fixed sort, or an index
    ///   outgrows what one holds.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_forgets`].
    /// - witness: `tests::modules::models::a_manifest_model_stands_where_its_theory_s_model_is_asked`
    /// - witness: `tests::modules::models::a_manifest_model_of_an_extension_stands_where_the_included_model_is_asked_2136`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ty, body)| sink.arena.value_type(ty).is_some() && sink.arena.value(body).is_some()))]
    fn forget(
        &self,
        slot: SlotIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<(ValueTypeId, ValueId), Missing<'source>>
    {
        let plan = self
            .collected
            .forgets
            .get(&slot)
            .ok_or(Missing::Unlowered)?;
        let below = origin.inserted(Insertion::Derived);
        let plain = self.reduct_bundle(plan.theory, sink, below)?;
        let full = &plain
            .bundled()
            .theories
            .first()
            .ok_or(Missing::Unlowered)?
            .signature;
        // The manifest model drops each sort the slot fixes of the outermost
        // theory, each read as the decode of its carrier.
        let mut theories = plain.bundled().theories.clone();
        let outermost = theories.first_mut().ok_or(Missing::Unlowered)?;
        let mut fixed: Vec<Name> = Vec::new();
        outermost.signature.components.retain(|component| {
            let manifest = plan.fixed.contains(&component.name)
                && matches!(
                    component.form,
                    Ok(ModelForm::Sort { ref indices }) if indices.is_empty()
                );
            if manifest {
                fixed.push(component.name.clone());
            }
            !manifest
        });
        let carriers = u32::try_from(fixed.len()).map_err(|_overflow| Missing::Unlowered)?;
        let last = carriers.checked_sub(1).ok_or(Missing::Unlowered)?;
        let universe = sink.arena.value_type_universe(
            Sort::Ground(Universe::FUSS_FREE.sort),
            Level::constant(Universe::FUSS_FREE.level),
        );
        sink.origins.record_value_type(universe, below);
        // Beneath the carriers, the one at place `i` stands at index
        // `n - 1 - i`.
        let mut decoded = Vec::with_capacity(fixed.len());
        for (place, name) in fixed.iter().enumerate() {
            let place = u32::try_from(place).map_err(|_overflow| Missing::Unlowered)?;
            let index = last.checked_sub(place).ok_or(Missing::Unlowered)?;
            let code = sink
                .arena
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
            sink.origins.record_value(code, below);
            let element = sink
                .arena
                .value_type_element(code, Level::constant(Universe::FUSS_FREE.level));
            sink.origins.record_value_type(element, below);
            decoded.push((name, element));
        }
        let manifest_bundle = Bundled {
            theories,
            named: plain.bundled().named,
            manifests: Vec::new(),
        };
        let Maybe::Present(Lowered::ValueType(manifest)) =
            self.mint_bundle_fixed(&manifest_bundle, &decoded, sink, below)
        else {
            return Err(Missing::Unlowered);
        };
        let source = &manifest_bundle
            .theories
            .first()
            .ok_or(Missing::Unlowered)?
            .signature;
        let destructuring = Destructured::of(source);
        let past = u32::from(destructuring.depth().ok_or(Missing::Unlowered)?);
        // The map returns the theory's own record, or the record of the
        // theory it restricts to.
        let restricted = if plan.onto == plan.theory {
            None
        }
        else {
            Some(self.reduct_bundle(plan.onto, sink, below)?)
        };
        let (onto, model) = match restricted {
            Some(ref bundle) => (
                &bundle
                    .bundled()
                    .theories
                    .first()
                    .ok_or(Missing::Unlowered)?
                    .signature,
                bundle.model(),
            ),
            None => (full, plain.model()),
        };
        let returner = sink.arena.comp_type_returner(model);
        sink.origins.record_comp_type(returner, below);
        // Where each name stands: a carrier's place among the carriers, any
        // other field's among the manifest model's.
        let carrier_at: BTreeMap<&Name, u32> = fixed.iter().zip(0_u32 ..).collect();
        let kept_at: BTreeMap<&Name, usize> = source
            .components
            .iter()
            .enumerate()
            .map(|(at, held)| (&held.name, at))
            .collect();
        let mut fields = Vec::with_capacity(onto.components.len());
        for component in &onto.components {
            let index = match carrier_at.get(&component.name) {
                // A carrier stands past the destructuring, `m`, and the
                // carriers after it.
                Some(&carrier) => last
                    .checked_sub(carrier)
                    .and_then(|after| past.checked_add(1)?.checked_add(after))
                    .map(DeBruijnIndex::from),
                None => kept_at
                    .get(&component.name)
                    .and_then(|&at| destructuring.bound_at(ComponentPlace(at))),
            }
            .ok_or(Missing::Unlowered)?;
            let field = sink.arena.value_variable(Zone::Intuitionistic, index);
            sink.origins.record_value(field, below);
            fields.push(field);
        }
        let record =
            packed_record(onto, &fields, sink, (below, below)).ok_or(Missing::Unlowered)?;
        let returned = sink.arena.computation_return(record);
        sink.origins.record_computation(returned, below);
        let destructured = destructuring
            .wrap(source, (returned, returner), sink, below)
            .ok_or(Missing::Unlowered)?;
        let mut lambda = sink.arena.computation_lambda(destructured);
        sink.origins.record_computation(lambda, below);
        let mut arrow = sink.arena.comp_type_arrow(manifest, returner);
        sink.origins.record_comp_type(arrow, below);
        for _ in 0 .. carriers {
            lambda = sink.arena.computation_lambda(lambda);
            sink.origins.record_computation(lambda, below);
            arrow = sink.arena.comp_type_pi(universe, arrow);
            sink.origins.record_comp_type(arrow, below);
        }
        let body = sink.arena.value_thunk(lambda);
        sink.origins.record_value(body, below);
        let declared = sink.arena.value_type_thunk(arrow);
        sink.origins.record_value_type(declared, below);

        Ok((declared, body))
    }
}
