//! Model implicits, flattened: a function quantifying over a model in its
//! prefix block, `@[s : Model(S)]`, binds one implicit parameter per component
//! of the signature `S` derives — each sort at its universe, each operation,
//! constant and law at its derived type, in signature order, each later one
//! read under the ones before it — and no parameter holding a record of the
//! model.
//!
//! # The flattening is the dictionary
//!
//! A model passed to a function is its components, passed as ordinary
//! arguments: the core holds no record of a model, and a body reads `s.x` and
//! `s.op` as the variables of their parameters. A model a function quantifies
//! over is never a value of its own, so `s` named alone is refused,
//! [`LoweringRefusal::ModelImplicitValue`]. A sort a manifest model type
//! fixes, `@[s : Model(S) with sort x = A]`, binds no parameter: `s.x` reads
//! `A`, as it reads off a binder held at that type. A nested component's model
//! stays the record of its theory, one parameter.
//!
//! # A supply names a module or a model
//!
//! `f[s = M]` passes the module `M`'s members, one per component, as `pack M
//! at Model(S)` reads them: a module of a theory that includes `S` passes the
//! members `S` places, its reduct, and a module wanting one is refused as the
//! pack is. `f[s = t]`, for a model implicit `t` of the caller's, passes `t`'s
//! component of each name. Anything else a slot is supplied is refused,
//! [`LoweringRefusal::ModelImplicitValue`]: a model implicit is supplied by a
//! path, never by a value. A call omitting the slot nominates one hole per
//! component, which the checker solves.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::BundledTheory;
use super::Packed;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Former;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::lower::Code;
use crate::lower::Lowerer;
use crate::lower::Parameter;
use crate::lower::Plan;
use crate::lower::Produced;
use crate::lower::Reading;
use crate::lower::Resolved;
use crate::lower::Sink;
use crate::lower::Site;
use crate::lower::Stretch;
use crate::lower::Universe;
use crate::lower::arity;
use crate::lower::closed;
use crate::lower::lowered;
use crate::model::Dependent;
use crate::model::ModelComponent;
use crate::model::ModelForm;
use crate::module::TelescopeEntry;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;

/// A component's place among its slot's components, in signature order: the
/// parameter it binds, and the value a supply passes for it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(in crate::lower) struct ComponentPlace(usize);

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
struct FlatComponent
{
    /// Its name in the theory.
    name: Name,
    /// The frame its parameter binds.
    frame: ScopeId,
    /// Whether it is an unindexed sort, which `s.x` reads as a type.
    sort: bool,
}

/// A model implicit flattened into one parameter per component, kept by the
/// frame its name resolves to: the last component's.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct Flattened
{
    /// The implicit's binder, as the declaration writes it.
    binder: Placed,
    /// The components, in signature order.
    components: Vec<FlatComponent>,
    /// The sorts the model type fixes, each sort's name beside the type it
    /// is.
    fixed: BTreeMap<Name, Placed>,
}

/// The theory a model implicit's type names, as a call or a declaration
/// reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(in crate::lower) struct ModelSlot
{
    /// The bundle's theories, the outermost first, which holds no component
    /// `fixed` names.
    theories: Vec<BundledTheory>,
    /// The sorts the model type fixes, each sort's name beside the type it
    /// is.
    fixed: BTreeMap<Name, Placed>,
    /// The theory's name tile.
    theory: Placed,
}

impl ModelSlot
{
    /// The components a model of the slot passes, in signature order.
    ///
    /// # Specification
    /// trivial.
    pub(in crate::lower) fn components(&self) -> &[ModelComponent]
    {
        self.theories
            .first()
            .map_or(&[], |theory| theory.signature.components.as_slice())
    }
}

/// What a supply passes for a flattened model implicit: one value per
/// component of the slot.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(in crate::lower) enum Supplied
{
    /// A module's members, as `pack M at Model(S)` reads them.
    Module(Arc<Packed>),
    /// The parameters of the caller's model implicit, one per component, each
    /// variable's index from the call beside its frame.
    Bound(Vec<(DeBruijnIndex, ScopeId)>),
}

impl<'source> Lowerer<'_, 'source>
{
    /// The theory the type `declared` names when it is a model type,
    /// `Model(S)` or `Model(S) with sort x = A …`.
    ///
    /// # Specification
    /// - requires: `declared` is a parameter's written type in `site`.
    /// - ensures: the slot of the theory `S` names, its outermost theory
    ///   holding no sort the type fixes, each fixed sort beside the type it is,
    ///   when the type is a model type; nothing for any other type.
    /// - fails: a manifest type's bindings out of shape; the refusals
    ///   [`Self::bundled`] yields for a theory nothing presents.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model implicit binds its components, a manifest one
    ///   all but the sorts it fixes, and an implicit at any other type binds as
    ///   written.
    /// - witness: `lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    /// - witness: `lower::implicit::tests::a_manifest_model_implicit_binds_no_fixed_sort_739`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |slot| slot.as_ref().is_none_or(|slot| !slot.theories.is_empty())))]
    pub(in crate::lower) fn model_slot(
        &mut self,
        site: Site,
        declared: Placed,
    ) -> Result<Option<ModelSlot>, LoweringRefusal<'source>>
    {
        let written = Site {
            at: declared,
            ..site
        };
        let (applied, bound) = match self.form_at(declared)? {
            Some((_, Former::TypeApplication)) => (declared, None),
            Some((_, Former::ManifestType)) => {
                let mut pieces = Pieces::new();
                read_pieces(self.pbg, self.tree, declared.node, &mut pieces)?;
                let mut cursor = Cursor::new(&pieces.pieces, declared.span);
                let applied = written.one(cursor.operands())?;
                closed(written, &mut cursor, TileName::WITH)?;
                let bound = written.one(cursor.operands())?;
                (applied, Some(bound))
            },
            _ => return Ok(None),
        };
        let at_applied = Site {
            at: applied,
            ..site
        };
        let Ok(theory) =
            self.stated_theory(at_applied, at_applied.out(FragmentBoundary::WrongSort))
        else {
            return Ok(None);
        };
        let mut sorts = Vec::new();
        if let Some(bound) = bound {
            let mut scratch = Pieces::new();
            self.bindings(written, bound, &mut scratch, &mut sorts)?;
        }
        let fixed: BTreeMap<Name, Placed> = sorts
            .iter()
            .map(|&(sort, stated)| (Name::from(self.name_at(sort).as_ref()), stated))
            .collect();
        let named = Site { at: theory, ..site };
        let mut theories = self.bundled(named, (declared.span.start(), self.name_at(theory)))?;
        if let Some(outermost) = theories.first_mut() {
            outermost
                .signature
                .components
                .retain(|component| !fixed.contains_key(&component.name));
        }

        Ok(Some(ModelSlot {
            theories,
            fixed,
            theory,
        }))
    }

    /// Bind the model implicit `entry`, written at the model type `declared`
    /// whose slot is `slot`, as one parameter per component under `frame`.
    ///
    /// # Specification
    /// - requires: `slot` is [`Self::model_slot`]'s answer for `declared`, and
    ///   states a component.
    /// - ensures: the type is read as a value type under `frame`; one frame per
    ///   component, in signature order, each named as the implicit is and held
    ///   at its type, mentioned so the declared type binds it, each extending
    ///   the one before it and recorded as a parameter of its component's
    ///   place; the last frame keeps the components, and is returned.
    /// - fails: the binder's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's model implicit binds its sort, its zero,
    ///   its step and its reading, in order.
    /// - witness: `lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    #[spec(
        captures: before = self.parameters.len(),
        ensures: |ret| ret.is_err() || self.parameters.len() == before.saturating_add(slot.components().len()),
    )]
    pub(in crate::lower) fn flatten_implicit(
        &mut self,
        entry: TelescopeEntry<'source>,
        declared: Placed,
        slot: &ModelSlot,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        self.read(declared.node, Reading::ValueType(frame));
        self.note_binder(entry.binder, entry.name)?;
        let written = Maybe::Present(entry.binder.span);
        let mut frame = frame;
        let mut components = Vec::with_capacity(slot.components().len());
        for (place, component) in slot.components().iter().enumerate() {
            let bound = self
                .scope
                .extend_typed(frame, entry.name, declared.node, written);
            self.scope.mention(bound);
            self.parameters.push(Parameter {
                binder: entry.binder.node,
                frame: bound,
                declared: Maybe::Present(declared.node),
                component: Some(ComponentPlace::from(place)),
            });
            components.push(FlatComponent {
                name: component.name.clone(),
                frame: bound,
                sort: matches!(component.form, Ok(ModelForm::Sort { ref indices }) if indices.is_empty()),
            });
            frame = Frame::Inner(bound);
        }
        if let Frame::Inner(last) = frame {
            let _first = self.flattened.insert(last, Flattened {
                binder: entry.binder,
                components,
                fixed: slot.fixed.clone(),
            });
        }

        Ok(frame)
    }

    /// Refuse `resolved`, the binder a name written at `site` names, when it
    /// is a flattened model implicit: the model is its components, no value.
    ///
    /// # Specification
    /// - requires: `resolved` is what the name at `site` resolved to.
    /// - ensures: `Ok` for a declaration and for any other binder.
    /// - fails: [`LoweringRefusal::ModelImplicitValue`] at `site` for a model
    ///   implicit.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model implicit named alone is refused, its
    ///   components read.
    /// - witness: `lower::implicit::tests::a_model_implicit_named_alone_is_refused_739`
    #[spec(ensures: |ret| ret.is_ok() || matches!(resolved, Resolved::Binder(bound) if self.flattened.contains_key(&bound.binder)))]
    pub(in crate::lower) fn unflattened(
        &self,
        site: Site,
        resolved: Resolved,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        match resolved {
            Resolved::Binder(bound) => {
                self.flattened
                    .get(&bound.binder)
                    .map_or(Ok(()), |flattened| {
                        Err(LoweringRefusal::ModelImplicitValue {
                            span: site.at.span,
                            implicit: self.name_at(flattened.binder),
                        })
                    })
            },
            Resolved::Declaration { .. } => Ok(()),
        }
    }

    /// The flattened model implicit the frame `binder` binds, if any.
    ///
    /// # Specification
    /// trivial.
    pub(in crate::lower) fn flattened_at(
        &self,
        binder: ScopeId,
    ) -> Option<Flattened>
    {
        self.flattened.get(&binder).cloned()
    }

    /// Classify `s.x`, written at `site` with the model implicit `s` at
    /// `head` flattened as `flattened`, where a type is read: the sort `x`.
    ///
    /// # Specification
    /// - requires: `head` names the binder `flattened` is kept by, `member` the
    ///   sort.
    /// - ensures: a sort the model type fixes is planned as the type it is
    ///   fixed to, raised past the components' binders; any other unindexed
    ///   sort as its parameter's code decoded in the fuss-free universe, the
    ///   parameter named in the type.
    /// - fails: [`LoweringRefusal::UnknownMember`] for a name no component
    ///   bears; the wrong-sort refusal for a component that is no unindexed
    ///   sort, and where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's carrier read off its model implicit, and
    ///   a fixed one.
    /// - witness: `lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    /// - witness: `lower::implicit::tests::a_manifest_model_implicit_binds_no_fixed_sort_739`
    #[spec(ensures: |ret| !matches!(ret, Ok(arity::Planned(true))) || matches!(self.plans.get(site.at.node), Some(&(Plan::Decode(..) | Plan::FixedCarrier(..)))))]
    pub(in crate::lower) fn flattened_sort(
        &mut self,
        site: Site,
        head: Placed,
        member: Placed,
        flattened: &Flattened,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let frame = site.reading.frame();
        let name = self.name_at(member);
        let Some(first) = flattened
            .components
            .first()
            .map(|component| component.frame)
        else {
            return Ok(arity::Planned(false));
        };
        if let Some((_, &written)) = flattened
            .fixed
            .iter()
            .find(|&(sort, _)| sort.as_ref() == name.as_ref())
        {
            let _frame = self.require(site, Produced::ValueType)?;
            self.fixed_carriers.push(written);
            let telescope = self.telescope_at(site.at.node);
            self.plan(
                site,
                Plan::FixedCarrier(
                    Code::Bound {
                        from: frame,
                        binder: first,
                        telescope,
                    },
                    written.node,
                ),
            );
            return Ok(arity::Planned(true));
        }
        let Some(component) = flattened
            .components
            .iter()
            .find(|component| component.name.as_ref() == name.as_ref())
        else {
            return Err(LoweringRefusal::UnknownMember {
                span: member.span,
                module: self.name_at(head),
                member: name,
            });
        };
        if !component.sort {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        let _frame = self.require(site, Produced::ValueType)?;
        let telescope = self.name_in_type(site.at.node, component.frame);
        let none = Stretch {
            start: self.operands.len(),
            end: self.operands.len(),
        };
        self.plan(
            site,
            Plan::Decode(
                Code::Bound {
                    from: frame,
                    binder: component.frame,
                    telescope,
                },
                none,
                Universe::FUSS_FREE,
            ),
        );

        Ok(arity::Planned(true))
    }

    /// Classify `s.x`, written at `site` with the model implicit `s` at
    /// `target` bound as `bound` and flattened as `flattened`, where a value is
    /// read: the component `x`'s parameter.
    ///
    /// # Specification
    /// - requires: `target` names the binder `flattened` is kept by, and
    ///   `bound` is what it resolved to; `selected` is the component's name.
    /// - ensures: the component's variable — counted from the reading as a type
    ///   counts its binders where a type is read, and past every frame between
    ///   otherwise — standing as a value; the name `s` is kept as resolved to
    ///   the implicit.
    /// - fails: [`LoweringRefusal::UnknownMember`] for a name no component
    ///   bears; the wrong-sort refusal for a sort the model type fixes, and
    ///   where no value is read.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's step and reading read off its model
    ///   implicit and run.
    /// - witness: `lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    #[spec(ensures: |ret| !matches!(ret, Ok(arity::Planned(true))) || matches!(self.plans.get(site.at.node), Some(&(Plan::Variable(..) | Plan::StaticApplication(..)))))]
    pub(in crate::lower) fn flattened_member(
        &mut self,
        site: Site,
        (target, selected): (Placed, Placed),
        bound: Bound,
        flattened: &Flattened,
    ) -> Result<arity::Planned, LoweringRefusal<'source>>
    {
        let name = self.name_at(selected);
        if flattened
            .fixed
            .iter()
            .any(|(sort, _)| sort.as_ref() == name.as_ref())
        {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        let Some(place) = flattened
            .components
            .iter()
            .position(|component| component.name.as_ref() == name.as_ref())
        else {
            return Err(LoweringRefusal::UnknownMember {
                span: selected.span,
                module: self.name_at(target),
                member: name,
            });
        };
        let Some(component) = flattened.components.get(place)
        else {
            return Ok(arity::Planned(false));
        };
        let frame = self.require(site, Produced::Value)?;
        self.resolved(target.span, Resolved::Binder(bound));
        let plan = if self.in_type.contains(&site.at.node) {
            let telescope = self.name_in_type(site.at.node, component.frame);
            let none = Stretch {
                start: self.operands.len(),
                end: self.operands.len(),
            };
            Plan::StaticApplication(
                Code::Bound {
                    from: frame,
                    binder: component.frame,
                    telescope,
                },
                none,
            )
        }
        else {
            let behind = flattened
                .components
                .len()
                .saturating_sub(place)
                .saturating_sub(1);
            let index =
                u32::from(bound.index).saturating_add(u32::try_from(behind).unwrap_or(u32::MAX));
            Plan::Variable(DeBruijnIndex::from(index), component.frame)
        };
        self.plan(site, plan);

        Ok(arity::Planned(true))
    }

    /// What the resident `value` a call at `site`, read under `frame`, writes
    /// for the model implicit `implicit`, of the slot `slot`, passes.
    ///
    /// # Specification
    /// - requires: `value` is the resident's value, `slot` the implicit's slot.
    /// - ensures: a capitalised name passes the members of the module it names,
    ///   as [`Self::packed_module`] reads them at the slot's theory; the name
    ///   of a model implicit of the caller's passes, for each component of the
    ///   slot, the variable of its component of that name, and is kept as
    ///   resolved.
    /// - fails: the refusals [`Self::packed_module`] yields;
    ///   [`LoweringRefusal::UnresolvedName`] for a name no binder answers;
    ///   [`LoweringRefusal::UnknownMember`] for a component the caller's model
    ///   lacks; [`LoweringRefusal::ModelImplicitValue`] naming `implicit` at a
    ///   resident that is neither.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module supplied by name runs as its pack does, a
    ///   module of an including theory passes its reduct, a model implicit
    ///   passes itself on, and a value is refused.
    /// - witness: `lower::implicit::tests::a_module_supplied_for_a_model_implicit_passes_its_members_739`
    /// - witness: `lower::implicit::tests::a_model_implicit_supplied_by_a_value_is_refused_739`
    #[spec(ensures: |ret| match ret {
        Ok(Supplied::Bound(ref variables)) => variables.len() == slot.components().len(),
        Ok(Supplied::Module(_)) | Err(_) => true,
    })]
    pub(in crate::lower) fn supply_model(
        &mut self,
        site: Site,
        frame: Frame,
        (implicit, slot): (SurfaceName<'source>, &ModelSlot),
        value: NodeIndex,
    ) -> Result<Supplied, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(value)
        else {
            return Err(LoweringRefusal::ModelImplicitValue {
                span: site.at.span,
                implicit,
            });
        };
        let resident = Placed::of(value, node);
        let unnamed = LoweringRefusal::ModelImplicitValue {
            span: resident.span,
            implicit,
        };
        match self.form_at(resident)? {
            Some((_, Former::Constructor | Former::TypeHead)) => {
                let packed = self.packed_module(site, resident, slot.theory, &slot.fixed)?;
                Ok(Supplied::Module(Arc::new(packed)))
            },
            Some((_, Former::Name)) => {
                let name = self.name_at(resident);
                let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)?
                else {
                    return Err(LoweringRefusal::UnresolvedName {
                        span: resident.span,
                        name,
                    });
                };
                let Some(flattened) = self.flattened_at(bound.binder)
                else {
                    return Err(unnamed);
                };
                let count = flattened.components.len();
                let mut variables = Vec::with_capacity(slot.components().len());
                for component in slot.components() {
                    let Some((place, own)) = flattened
                        .components
                        .iter()
                        .enumerate()
                        .find(|&(_, own)| own.name == component.name)
                    else {
                        return Err(LoweringRefusal::UnknownMember {
                            span: resident.span,
                            module: name,
                            member: self.name_at(component.named),
                        });
                    };
                    let behind = count.saturating_sub(place).saturating_sub(1);
                    let index = u32::from(bound.index)
                        .saturating_add(u32::try_from(behind).unwrap_or(u32::MAX));
                    variables.push((DeBruijnIndex::from(index), own.frame));
                }
                self.resolved(resident.span, Resolved::Binder(bound));
                Ok(Supplied::Bound(variables))
            },
            _ => Err(unnamed),
        }
    }

    /// Mint the value `supplied` passes for the component at `place` of its
    /// slot, raised past `under` binders a standing supply opens.
    ///
    /// # Specification
    /// - requires: `place` is a component of the slot `supplied` was read for.
    /// - ensures: a module's member as [`Self::packed_member`] mints it, or the
    ///   record of its nested module as [`Self::packed_records`] mints it, for
    ///   a module; the variable of the caller's component for a model implicit,
    ///   raised past `under`; every node carrying `origin` marked
    ///   [`Insertion::Implicit`]; nothing when a member did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::supply_model`].
    /// - witness: `lower::implicit::tests::a_module_supplied_for_a_model_implicit_passes_its_members_739`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(id) if sink.arena.value(id).is_some()))]
    pub(in crate::lower) fn mint_supplied(
        &self,
        supplied: &Supplied,
        place: ComponentPlace,
        under: Binders,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        let place = usize::from(place);
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let inserted = origin.inserted(Insertion::Implicit);
        match *supplied {
            Supplied::Module(ref packed) => {
                let (Some(theory), Some(&module)) =
                    (packed.theories.first(), packed.modules.first())
                else {
                    return unminted;
                };
                let Some(component) = theory.signature.components.get(place)
                else {
                    return unminted;
                };
                let value = if let Ok(ModelForm::Nested(_)) = component.form {
                    let before = theory
                        .signature
                        .components
                        .iter()
                        .take(place)
                        .filter(|earlier| matches!(earlier.form, Ok(ModelForm::Nested(_))))
                        .count();
                    theory.nested.get(before).and_then(|&inner| {
                        self.packed_records(packed, sink, inserted)?
                            .get(inner)
                            .copied()
                            .flatten()
                    })
                }
                else {
                    self.packed_member(module, component, sink, inserted)
                };
                value.map_or(unminted, Maybe::Present)
            },
            Supplied::Bound(ref variables) => {
                let Some(&(index, binder)) = variables.get(place)
                else {
                    return unminted;
                };
                let id = sink.arena.value_variable(self.scope.zone(binder), index);
                sink.origins.record_value(id, inserted);
                let raised = if under == Binders::NONE {
                    id
                }
                else {
                    gandr_core_term::shift_value(sink.arena, id, under).settle(sink.arena)
                };
                Maybe::Present(raised)
            },
        }
    }

    /// The types of the parameters a model implicit written at `declared`
    /// binds, one per component, each read under the ones before it.
    ///
    /// # Specification
    /// - requires: the mint sweep has minted the model type at `declared`.
    /// - ensures: one type per component of the outermost theory, in signature
    ///   order, as [`Self::bundle_fields`] states it with every link binding —
    ///   a component it names read as the variable of the parameter before it —
    ///   a nested model as its bundled record, each sort the type fixes as its
    ///   type raised past the parameters before the reading, every node
    ///   carrying the theory's origin marked [`Insertion::Model`]; nothing when
    ///   a type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per nested theory of the finite bundle.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter's implicit's parameters are its sort's
    ///   universe, then its zero, step and reading over the sort's variable.
    /// - witness: `lower::implicit::tests::a_model_implicit_binds_one_parameter_per_component_739`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(ret, Maybe::Present(ref domains) if !domains.is_empty()))]
    pub(in crate::lower) fn flattened_domains(
        &self,
        declared: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Vec<ValueTypeId>, lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let mut node = declared;
        let bundled = loop {
            match self.plans.get(node) {
                Some(&Plan::Transparent(inner)) => node = inner,
                Some(&Plan::Bundle(ref bundled)) => break Arc::clone(bundled),
                _ => return unminted,
            }
        };
        let fixed: Option<Vec<(&Name, ValueTypeId)>> = bundled
            .manifests
            .iter()
            .map(|&(ref name, defined)| match self.value_type_at(defined) {
                Maybe::Present(id) => Some((name, id)),
                Maybe::Absent(_) => None,
            })
            .collect();
        let Some(fixed) = fixed
        else {
            return unminted;
        };
        let below = match self.origin_at(bundled.named) {
            Maybe::Present(named) => named.inserted(Insertion::Model),
            Maybe::Absent(_) => origin.inserted(Insertion::Model),
        };
        let mut minted: Vec<Option<ValueTypeId>> = vec![None; bundled.theories.len()];
        for (place, theory) in bundled.theories.iter().enumerate().skip(1).rev() {
            let nested: Option<Vec<ValueTypeId>> = theory
                .nested
                .iter()
                .map(|&inner| minted.get(inner).copied().flatten())
                .collect();
            let Some(nested) = nested
            else {
                return unminted;
            };
            let Ok(id) = self.bundle_type(&theory.signature, &nested, &[], sink, (below, below))
            else {
                return unminted;
            };
            if let Some(at) = minted.get_mut(place) {
                *at = Some(id);
            }
        }
        let Some(outermost) = bundled.theories.first()
        else {
            return unminted;
        };
        let nested: Option<Vec<ValueTypeId>> = outermost
            .nested
            .iter()
            .map(|&inner| minted.get(inner).copied().flatten())
            .collect();
        let Some(nested) = nested
        else {
            return unminted;
        };
        let binds = vec![Dependent(true); outermost.signature.components.len()];
        match self.bundle_fields(&outermost.signature, &binds, &nested, &fixed, sink, below) {
            Ok(domains) if !domains.is_empty() => Maybe::Present(domains),
            Ok(_) | Err(_) => unminted,
        }
    }
}
