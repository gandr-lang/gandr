//! Derived rules, as the lowering mints them.
//!
//! Each slot a `derive` declaration takes ([`DerivedSlot`]) states its law
//! over every model of its theory and proves it from the plan the collection
//! keeps:
//!
//! ```text
//! T.r : U(Π(m : Model(T)). F U(Π x₁ … xₙ. F Path(S, l, r)))
//! T.r = thunk(λm. return thunk(λx₁ … λxₙ. return p))
//! ```
//!
//! The model's operations and laws are its fields, each read as the
//! projection of `m` the bundled record's nesting gives ([`Projected`]). The
//! path `p` composes the plan's two legs by `then`, a leg read back by
//! `back`. A step is the law or lemma it fires, applied to the terms its
//! variables matched: a law is the model's field, read back when the step runs
//! against its direction; a lemma is the earlier slot of the declaration's run,
//! applied to `m`. A step below the root is carried up its context as `cong`
//! is, a transport of reflexivity whose family's right endpoint is the context
//! with the motive's binder in its hole.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::identity::back;
use gandr_core_term::identity::then;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermView;
use quenchant_shape::shape::Maybe;

use super::Bundled;
use super::Context;
use super::Members;
use super::Minting;
use super::Missing;
use super::Projected;
use super::bundle_dependence;
use crate::derive::Fired;
use crate::derive::HOLE;
use crate::derive::Leg;
use crate::derive::Step;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::lower::Lowered;
use crate::lower::Lowerer;
use crate::lower::Reading;
use crate::lower::Sink;
use crate::lower::Site;
use crate::lower::native::record_since;
use crate::lower::native::rooted;
use crate::model::Binder;
use crate::model::Dependent;
use crate::model::ModelForm;
use crate::model::ModelSignature;
use crate::model::SortTerm;
use crate::module::DerivedSlot;
use crate::module::SlotIndex;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;

/// What a proof is minted under: the law's telescope, every binder binding,
/// the model's fields, and the type of the terms its legs rewrite.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Proving<'proof, 'source, 'model>
{
    /// The binders the proof stands under.
    context: Context<'proof>,
    /// Where it reads the model's fields.
    minting: &'proof Minting<'source, 'model>,
    /// The signature the model states.
    signature: &'proof ModelSignature,
    /// The type of the terms the legs rewrite.
    over: ValueTypeId,
    /// The first slot of the declaration's run.
    run: SlotIndex,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Mint each derived rule the current source declares.
    ///
    /// # Specification
    /// - requires: the collection planned the derived rules.
    /// - ensures: each derived slot of the current source holding no refusal is
    ///   minted to its type and proof, or refused: by the refusal its theory's
    ///   model type earns, or as unminted; a slot after a refused lemma of its
    ///   run is refused as that lemma is.
    /// - panics: none.
    /// - executable: none — each slot's type and proof are the checker's to
    ///   judge, and a refused one the verdict's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a group's inverse of a product mints its lemmas and
    ///   itself, which the checker accepts.
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    pub(in crate::lower) fn mint_derived_rules(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let slots: Vec<SlotIndex> = self
            .collected
            .derived
            .range(SlotIndex::from(self.current.slots) ..)
            .map(|(&slot, _)| slot)
            .collect();
        let mut refused: BTreeMap<SlotIndex, LoweringRefusal<'source>> = BTreeMap::new();
        for slot in slots {
            let Some(entry) = self.collected.slots.get(usize::from(slot))
            else {
                continue;
            };
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let (span, name) = (entry.introduced_by.span, entry.name);
            let origin = Origin::new(entry.named.node, entry.named.span);
            let run = self.collected.derived.get(&slot).map(|derived| derived.run);
            if let Some(&refusal) = run.and_then(|run| refused.get(&run)) {
                let _first = self.faults.insert(slot, refusal);
                continue;
            }
            let refusal = match self.derived_rule(slot, sink, origin) {
                Ok(minted) => {
                    let _first = self.derivations.insert(slot, minted);
                    continue;
                },
                Err(Missing::Refused(refusal)) => refusal,
                Err(Missing::Unlowered) => LoweringRefusal::Unminted { span, name },
            };
            let _first = self.faults.insert(slot, refusal);
            if let Some(run) = run {
                let _first = refused.insert(run, refusal);
            }
        }
    }

    /// The type and proof of the derived slot `slot`: the declared type and
    /// the proof's thunk carrying `origin`, every node below them `origin`
    /// marked [`Insertion::Derived`], the proof's lambda and return among
    /// them: the statement's name answers with the law over every model.
    ///
    /// # Specification
    /// - requires: `slot` is a derived slot of the current source.
    /// - ensures: the type `U(Π(m : Model(T)). F L)`, `L` the law the slot
    ///   states read with `m`'s fields, and the proof `thunk(λm. return P)`,
    ///   `P` the law's proof under `m`.
    /// - fails: the refusal the theory's model type earns;
    ///   [`Missing::Unlowered`] where the model type, the law or a step does
    ///   not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ty, proof)| sink.arena.value_type(ty).is_some() && sink.arena.value(proof).is_some()))]
    fn derived_rule(
        &mut self,
        slot: SlotIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Result<(ValueTypeId, ValueId), Missing<'source>>
    {
        let derived = self
            .collected
            .derived
            .get(&slot)
            .cloned()
            .ok_or(Missing::Unlowered)?;
        let site = Site {
            at: derived.theory,
            name: FormName::DERIVE_DECLARATION,
            reading: Reading::ValueType(Frame::Outermost),
        };
        let theory = self.name_at(derived.theory);
        let theories = self
            .bundled(site, (derived.at, theory))
            .map_err(Missing::Refused)?;
        if theories.len() != 1 {
            return Err(Missing::Unlowered);
        }
        let bundled = Bundled {
            theories,
            named: derived.theory.node,
            manifests: Vec::new(),
        };
        let Maybe::Present(Lowered::ValueType(model)) = self.mint_bundle(&bundled, sink, origin)
        else {
            return Err(Missing::Unlowered);
        };
        let signature = &bundled
            .theories
            .first()
            .ok_or(Missing::Unlowered)?
            .signature;
        let binds = bundle_dependence(signature);
        let minting = Minting {
            members: Members::Projected(Projected {
                components: &signature.components,
                binds: &binds,
            }),
            origin: origin.inserted(Insertion::Derived),
        };
        let law = self.mint_form(&derived.lemma.law, &minting, sink)?;
        let returner = sink.arena.comp_type_returner(law);
        sink.origins.record_comp_type(returner, origin);
        let quantified = sink.arena.comp_type_pi(model, returner);
        sink.origins.record_comp_type(quantified, origin);
        let declared = sink.arena.value_type_thunk(quantified);
        sink.origins.record_value_type(declared, origin);
        let proof = self.proof(&derived, &minting, signature, sink)?;
        let returned = sink.arena.computation_return(proof);
        sink.origins.record_computation(returned, minting.origin);
        let lambda = sink.arena.computation_lambda(returned);
        sink.origins.record_computation(lambda, minting.origin);
        let body = sink.arena.value_thunk(lambda);
        sink.origins.record_value(body, origin);

        Ok((declared, body))
    }

    /// The proof of the law `derived` states, under the model `minting`
    /// reads: `thunk(λx₁ … λxₙ. return p)`.
    ///
    /// # Specification
    /// - requires: the model is bound just outside the law's telescope.
    /// - ensures: `p` the composite of the legs that take a step, `here` at the
    ///   law's left side when neither does.
    /// - fails: [`Missing::Unlowered`] for a form that is no law, or a term, a
    ///   sort or a step that does not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value(id).is_some()))]
    fn proof(
        &self,
        derived: &DerivedSlot,
        minting: &Minting<'source, '_>,
        signature: &ModelSignature,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = minting.origin;
        let ModelForm::Law {
            ref telescope,
            ref carrier,
            ref left,
            ..
        } = derived.lemma.law
        else {
            return Err(Missing::Unlowered);
        };
        let dependent = vec![Dependent(true); telescope.len()];
        let context = Context {
            binders: telescope,
            dependent: &dependent,
        };
        let over = self.sort_type(carrier, context, minting, sink)?;
        let proving = Proving {
            context,
            minting,
            signature,
            over,
            run: derived.run,
        };
        let mut composed: Option<(ValueId, ValueId)> = None;
        for leg in &derived.lemma.legs {
            let Some((start, path)) = self.leg(leg, proving, sink)?
            else {
                continue;
            };
            composed = Some(match composed {
                None => (start, path),
                Some((first_start, first)) => {
                    let mark = sink.arena.watermark();
                    let joined = then(sink.arena, over, first_start, first, path);
                    let joined = sink.arena.value_returned(joined);
                    record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));
                    (first_start, joined)
                },
            });
        }
        let path = if let Some((_, path)) = composed {
            path
        }
        else {
            let point = self.term_value(left, context, minting, sink)?;
            let here = sink.arena.value_here(point);
            sink.origins.record_value(here, origin);
            here
        };
        let mut body = sink.arena.computation_return(path);
        sink.origins.record_computation(body, origin);
        for _ in telescope {
            body = sink.arena.computation_lambda(body);
            sink.origins.record_computation(body, origin);
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins.record_value(thunk, origin);

        Ok(thunk)
    }

    /// The path a leg runs, with its left endpoint: its steps composed from
    /// the term it starts at, read back when the leg is.
    ///
    /// # Specification
    /// - ensures: nothing for a leg of no step; otherwise the steps composed by
    ///   `then` from the leg's start, and for a leg read back that path's
    ///   `back` from the term its last step reaches.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&leg| leg.is_none_or(|(start, path)| sink.arena.value(start).is_some() && sink.arena.value(path).is_some())))]
    fn leg(
        &self,
        leg: &Leg,
        proving: Proving<'_, 'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<Option<(ValueId, ValueId)>, Missing<'source>>
    {
        let origin = proving.minting.origin;
        let Some((first, rest)) = leg.steps.split_first()
        else {
            return Ok(None);
        };
        let from = self.term_value(&leg.from, proving.context, proving.minting, sink)?;
        let mut chain = self.step(first, proving, sink)?;
        for step in rest {
            let next = self.step(step, proving, sink)?;
            let mark = sink.arena.watermark();
            let joined = then(sink.arena, proving.over, from, chain, next);
            chain = sink.arena.value_returned(joined);
            record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));
        }
        if !leg.back {
            return Ok(Some((from, chain)));
        }
        let reached = leg.steps.last().map_or(&leg.from, |step| &step.whole.1);
        let to = self.term_value(reached, proving.context, proving.minting, sink)?;
        let mark = sink.arena.watermark();
        let reversed = back(sink.arena, proving.over, from, chain);
        let reversed = sink.arena.value_returned(reversed);
        record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));

        Ok(Some((to, reversed)))
    }

    /// The path one step takes: the law or lemma it fires, at the terms its
    /// variables matched, carried up the step's context.
    ///
    /// # Specification
    /// - ensures: a law's field applied to the matched terms in its telescope's
    ///   order, read back for a step against the law; a lemma's slot applied to
    ///   the model, then to the matched terms; below the root, `cong` of the
    ///   context with its hole bound, from the whole term before the step.
    /// - fails: [`Missing::Unlowered`] for a law the signature does not state,
    ///   a lemma no slot of the run holds, a variable the step did not match,
    ///   or a term or sort that does not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| sink.arena.value(id).is_some()))]
    fn step(
        &self,
        step: &Step,
        proving: Proving<'_, 'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = proving.minting.origin;
        let (context, minting) = (proving.context, proving.minting);
        let fired = match step.fired {
            Fired::Law { ref name, backward } => {
                let telescope = law_telescope(proving.signature, name)?;
                let arguments = self.matched(telescope, step, proving, sink)?;
                let Members::Projected(projected) = minting.members
                else {
                    return Err(Missing::Unlowered);
                };
                let field = projected
                    .head(name, context, sink, origin)
                    .ok_or(Missing::Unlowered)?;
                sink.origins.record_value(field, origin);
                let applied = applied(field, &arguments, sink, origin);
                if backward {
                    let redex = SortTerm {
                        sort: step.sorts.0.clone(),
                        indices: Vec::new(),
                    };
                    let carrier = self.sort_type(&redex, context, minting, sink)?;
                    let fixed = self.term_value(&step.redex.1, context, minting, sink)?;
                    let mark = sink.arena.watermark();
                    let reversed = back(sink.arena, carrier, fixed, applied);
                    let reversed = sink.arena.value_returned(reversed);
                    record_since(sink, mark, origin, Maybe::Absent(rooted::Absent::Unminted));
                    reversed
                }
                else {
                    applied
                }
            },
            Fired::Lemma(place) => {
                let slot = SlotIndex::from(usize::from(proving.run).saturating_add(place.0));
                let lemma = self
                    .collected
                    .derived
                    .get(&slot)
                    .ok_or(Missing::Unlowered)?;
                let ModelForm::Law { ref telescope, .. } = lemma.lemma.law
                else {
                    return Err(Missing::Unlowered);
                };
                let constant = self
                    .collected
                    .slots
                    .get(usize::from(slot))
                    .ok_or(Missing::Unlowered)?
                    .constant;
                let arguments = self.matched(telescope, step, proving, sink)?;
                let head = sink.arena.value_constant(constant);
                sink.origins.record_value(head, origin);
                let bound = context.dependent.iter().filter(|binds| binds.0).count();
                let model = sink.arena.value_variable(
                    Zone::Intuitionistic,
                    DeBruijnIndex::from(
                        u32::try_from(bound).map_err(|_overflow| Missing::Unlowered)?,
                    ),
                );
                sink.origins.record_value(model, origin);
                let at_model = applied(head, &[model], sink, origin);
                applied(at_model, &arguments, sink, origin)
            },
        };
        if let TermView::Var(hole) = step.context.view()
            && hole.as_ref() == HOLE
        {
            return Ok(fired);
        }
        self.carried_up(step, fired, proving, sink)
    }

    /// `path`, a step's path at its redex, carried up the step's context:
    /// `cong(C, path)` from the whole term before the step, the context read
    /// as the family `h. Path(S, C[a], C[h])` rather than as a function, so
    /// no map stands to be synthesised.
    ///
    /// # Specification
    /// - ensures: the transport `tr(h. Path(S↑, start↑, C[h]), path,
    ///   here(start))` returned, `S` the whole term's sort, `start` the whole
    ///   term before the step and `C[h]` the context read with its hole the
    ///   motive's binder.
    /// - fails: [`Missing::Unlowered`] for a context, a term or a sort that
    ///   does not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&id| matches!(sink.arena.value(id), Some(&Value::Returned(_)))))]
    fn carried_up(
        &self,
        step: &Step,
        path: ValueId,
        proving: Proving<'_, 'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<ValueId, Missing<'source>>
    {
        let origin = proving.minting.origin;
        let (context, minting) = (proving.context, proving.minting);
        let whole = SortTerm {
            sort: step.sorts.1.clone(),
            indices: Vec::new(),
        };
        let start = self.term_value(&step.whole.0, context, minting, sink)?;
        let mut binders = context.binders.to_vec();
        binders.push(Binder {
            name: Name::from(HOLE),
            over: Vec::new(),
            sort: SortTerm {
                sort: step.sorts.0.clone(),
                indices: Vec::new(),
            },
        });
        let dependent = vec![Dependent(true); binders.len()];
        let holed = Context {
            binders: &binders,
            dependent: &dependent,
        };
        let over = self.sort_type(&whole, holed, minting, sink)?;
        let from = self.term_value(&step.whole.0, holed, minting, sink)?;
        let filled = self.term_value(&step.context, holed, minting, sink)?;
        let motive = sink.arena.value_type_path(over, from, filled);
        sink.origins.record_value_type(motive, origin);
        let base = sink.arena.value_here(start);
        sink.origins.record_value(base, origin);
        let moved = sink.arena.computation_path_transport(motive, path, base);
        sink.origins.record_computation(moved, origin);
        let moved = sink.arena.value_returned(moved);
        sink.origins.record_value(moved, origin);

        Ok(moved)
    }

    /// The terms `step` matched for `telescope`'s variables, in its order.
    ///
    /// # Specification
    /// - ensures: one value per binder, the term the step's substitution holds
    ///   for its name.
    /// - fails: [`Missing::Unlowered`] for a binder the step did not match, or
    ///   a term that does not mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the fails clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_derived_rules`].
    /// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |values| values.len() == telescope.len() && values.iter().all(|&id| sink.arena.value(id).is_some())))]
    fn matched(
        &self,
        telescope: &[Binder],
        step: &Step,
        proving: Proving<'_, 'source, '_>,
        sink: &mut Sink<'_>,
    ) -> Result<Vec<ValueId>, Missing<'source>>
    {
        let mut arguments = Vec::with_capacity(telescope.len());
        for binder in telescope {
            let term = step
                .substitution
                .get(&binder.name)
                .ok_or(Missing::Unlowered)?;
            arguments.push(self.term_value(term, proving.context, proving.minting, sink)?);
        }

        Ok(arguments)
    }
}

/// The telescope of the law `name` states in `signature`.
///
/// # Specification
/// - ensures: the variables of the last component of the name, when it is a
///   law.
/// - fails: [`Missing::Unlowered`] for a name no law bears.
/// - panics: none.
/// - executable: none — the result is the lookup itself.
///
/// # Errors
/// [`Missing::Unlowered`].
///
/// # Adequacy
/// - hypothesis: L3 — the group's laws read by the steps that fire them.
/// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
fn law_telescope<'signature, 'source>(
    signature: &'signature ModelSignature,
    name: &Name,
) -> Result<&'signature [Binder], Missing<'source>>
{
    match signature
        .components
        .iter()
        .rfind(|component| component.name == *name)
        .map(|component| &component.form)
    {
        Some(&Ok(ModelForm::Law { ref telescope, .. })) => Ok(telescope),
        Some(
            &(Ok(
                ModelForm::Sort { .. }
                | ModelForm::Operation { .. }
                | ModelForm::Constant(_)
                | ModelForm::Nested(_),
            )
            | Err(_)),
        )
        | None => Err(Missing::Unlowered),
    }
}

/// `head` forced and applied to `arguments`, returned as a value:
/// `↑((force head) a₁ … aₙ)`.
///
/// # Specification
/// - ensures: the returned call, every node carrying `origin`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the group's laws and lemmas applied by the steps that
///   fire them.
/// - witness: `tests::modules::models::a_derived_rule_reads_the_model_it_quantifies_over`
#[spec(ensures: |ret| matches!(sink.arena.value(ret), Some(&Value::Returned(_))))]
fn applied(
    head: ValueId,
    arguments: &[ValueId],
    sink: &mut Sink<'_>,
    origin: Origin,
) -> ValueId
{
    let mut call = sink.arena.computation_force(head);
    sink.origins.record_computation(call, origin);
    for &argument in arguments {
        call = sink.arena.computation_application(call, argument);
        sink.origins.record_computation(call, origin);
    }
    let returned = sink.arena.value_returned(call);
    sink.origins.record_value(returned, origin);
    returned
}
