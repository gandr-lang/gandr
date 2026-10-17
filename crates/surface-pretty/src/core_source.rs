//! The core arena as a [`Source`]: checked types, the values evaluation and
//! readback leave in the arena, and bodies, an elaborated one read as written
//! through its [`Restoration`].

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::identity::Relation;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::session::SessionAction;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Side;
use quenchant_shape::shape::Maybe;

use crate::former::Arity;
use crate::former::Component;
use crate::former::Former;
use crate::former::Name;
use crate::former::Source;
use crate::former::Unreadable;

/// A node of a core arena, of any of its four families.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CoreNode
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// The nodes an elaboration rebuilt, each read as the node it rebuilt it
/// from.
///
/// The checker elaborates a body by rebuilding the nodes above every
/// computation written where a value is read; [`Carried`] pairs each
/// rebuilt node with its original. A [`CoreSource`] restoring them reads an
/// elaborated body as the body the checker read, whose inferred runs are
/// written as the computations they run.
///
/// # Specification
/// - requires: the pairs come from one elaboration of one arena.
/// - ensures: each rebuilt node answers the node it was rebuilt from, the first
///   pair naming it when several do; every other node answers itself.
/// - provides: the reading [`crate::present_computation`] prints an elaborated
///   body's canonical form through.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an elaborated call nested in an argument, read with and
///   without its restoration, distinguishes a lost restoration from a restored
///   minted bind.
/// - witness: `core_source::tests::a_restored_elaboration_reads_as_written`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Restoration(BTreeMap<CoreNode, CoreNode>);

impl Restoration
{
    /// The restoration of the nodes `carried` pairs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each node a pair rebuilt maps to the node it was rebuilt
    ///   from, the first pair winning.
    /// - provides: the restoration of a checker's recorded elaboration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Restoration`].
    /// - witness: `core_source::tests::a_restored_elaboration_reads_as_written`
    #[spec(ensures: |ret| carried.iter().all(|pair| ret.0.contains_key(&match *pair {
        | Carried::Value(_, rebuilt) => CoreNode::Value(rebuilt),
        | Carried::Computation(_, rebuilt) => CoreNode::Computation(rebuilt),
        | Carried::ValueType(_, rebuilt) => CoreNode::ValueType(rebuilt),
        | Carried::CompType(_, rebuilt) => CoreNode::CompType(rebuilt),
    })))]
    #[inline]
    #[must_use]
    pub fn of(carried: &[Carried]) -> Self
    {
        let mut restored = BTreeMap::new();
        for pair in carried {
            let (original, rebuilt) = match *pair {
                Carried::Value(original, rebuilt) => {
                    (CoreNode::Value(original), CoreNode::Value(rebuilt))
                },
                Carried::Computation(original, rebuilt) => (
                    CoreNode::Computation(original),
                    CoreNode::Computation(rebuilt),
                ),
                Carried::ValueType(original, rebuilt) => {
                    (CoreNode::ValueType(original), CoreNode::ValueType(rebuilt))
                },
                Carried::CompType(original, rebuilt) => {
                    (CoreNode::CompType(original), CoreNode::CompType(rebuilt))
                },
            };
            restored.entry(rebuilt).or_insert(original);
        }
        Self(restored)
    }

    /// The node `node` was rebuilt from, or `node` itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn restored(
        &self,
        node: CoreNode,
    ) -> CoreNode
    {
        self.0.get(&node).copied().unwrap_or(node)
    }
}

/// The restoration that restores nothing.
const UNRESTORED: &Restoration = &Restoration(BTreeMap::new());

/// The constructor names of the data families a presentation meets, and the
/// family each data case eliminates.
///
/// The core names a constructor by its family and its tag, and a data case
/// matches by tag alone, so neither holds a constructor's name. A source
/// reads them here: a family's constructors by the family's name, in tag
/// order with each one's field count, and a data case's family by the case.
/// Two families of one name keep the first one recorded. A family of words
/// is recorded consed: each of its one-field constructors is a letter, written
/// before the rest of the word.
///
/// # Specification
/// - requires: the families are named as the source names a family and the
///   cases are computations of the source's arena.
/// - ensures: a recorded family answers its constructors by tag; a recorded
///   case answers its family; everything else answers nothing.
/// - provides: the patterns a data case is written in and the head a
///   constructor value is written under.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family of a nullary and a unary constructor names a
///   constructor value and both branches of a case over it; a shifted tag
///   changes the golden.
/// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Constructors<'text>
{
    /// Each family's constructors in tag order, with their field counts.
    families: BTreeMap<Name<'text>, Vec<(Name<'text>, Arity)>>,
    /// The families whose one-field constructors are letters of a word.
    consed: BTreeSet<Name<'text>>,
    /// The family each data case eliminates.
    cases: BTreeMap<ComputationId, Name<'text>>,
}

impl<'text> Constructors<'text>
{
    /// The family `family`'s constructors, in tag order with their field
    /// counts, recorded unless a family of that name already is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the family answers the constructors of its first record.
    /// - provides: the constructor names a source reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Constructors`].
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    #[spec(ensures: self.families.contains_key(&family))]
    #[inline]
    pub fn family<I>(
        &mut self,
        family: Name<'text>,
        constructors: I,
    ) where
        I: IntoIterator<Item = (Name<'text>, Arity)>,
    {
        let _first = self
            .families
            .entry(family)
            .or_insert_with(|| constructors.into_iter().collect());
    }

    /// The family `family` of words, its constructors in tag order with
    /// their field counts: each one-field constructor is a letter, consed
    /// onto the rest of the word.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::family`]; the family is consed.
    /// - provides: the letters a source spells a word with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Placement`](crate::Placement).
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    #[spec(ensures: self.families.contains_key(&family) && self.consed.contains(&family))]
    #[inline]
    pub fn words<I>(
        &mut self,
        family: Name<'text>,
        constructors: I,
    ) where
        I: IntoIterator<Item = (Name<'text>, Arity)>,
    {
        self.family(family, constructors);
        let _fresh = self.consed.insert(family);
    }

    /// The data case `case` eliminates a value of `family`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the case answers `family`, the first record winning.
    /// - provides: the family a case's patterns are named from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Constructors`].
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    #[spec(ensures: self.cases.contains_key(&case))]
    #[inline]
    pub fn case(
        &mut self,
        case: ComputationId,
        family: Name<'text>,
    )
    {
        let _first = self.cases.entry(case).or_insert(family);
    }

    /// The constructor of `family` at `tag`, and its field count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constructor(
        &self,
        family: Name<'_>,
        tag: Component,
    ) -> Option<(Name<'text>, Arity)>
    {
        self.families
            .get(family.as_ref())?
            .get(usize::from(tag))
            .copied()
    }

    /// How a constructor of `family` taking `arity` fields is laid out: consed
    /// when it is a letter of a word — one field, of a family registered by
    /// [`Self::words`] — and applied otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn placement(
        &self,
        family: Name<'_>,
        arity: Arity,
    ) -> crate::Placement
    {
        if usize::from(arity) == 1 && self.consed.contains(family.as_ref()) {
            crate::Placement::Consed
        }
        else {
            crate::Placement::Applied
        }
    }
}

/// The constructor table that names nothing.
const UNNAMED: &Constructors<'static> = &Constructors {
    families: BTreeMap::new(),
    consed: BTreeSet::new(),
    cases: BTreeMap::new(),
};

/// A core arena read through the names of the constants it mentions.
///
/// A core node names a constant or an abstract type by its admission
/// position; `names` spells position `i` as its `i`-th entry. A position past
/// the table reads as [`Former::Unreadable`]. A source restoring an
/// elaboration reads every node the elaboration rebuilt as its original; one
/// naming constructors reads them from its [`Constructors`]; one within a
/// context reads a variable past the root's binders by the context's names.
///
/// # Specification
/// - requires: `names` is indexed by admission position.
/// - ensures: arena nodes retain their formers; missing naming-table entries
///   read as unreadable; a restored node reads as its original.
/// - provides: the printer's input over checked types, readback values and
///   bodies.
/// - panics: none.
/// - executable: none — admission-order correctness relates this naming table
///   to declarations the arena does not store. The per-node conversion
///   obligations are executable on the reader methods.
///
/// # Adequacy
/// - hypothesis: L3 — distinct admission names, the exact table end and handles
///   dropped by truncation distinguish shifted naming and stale reads. External
///   declaration-to-name correspondence is outside these fixtures because the
///   adapter does not own declarations.
/// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
/// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
/// - witness: `core_source::tests::a_restored_elaboration_reads_as_written`
#[derive(Clone, Copy, Debug)]
pub struct CoreSource<'arena>
{
    /// The arena whose nodes are read.
    arena: &'arena CoreArena,
    /// The constants' names, by admission position.
    names: &'arena [Name<'arena>],
    /// The rebuilt nodes read as their originals.
    restoration: &'arena Restoration,
    /// The constructors' names, by family.
    constructors: &'arena Constructors<'arena>,
    /// The names of the binders the root stands under, outermost first.
    context: &'arena [Option<Name<'arena>>],
    /// The names of the capability scopes the root stands in, outermost
    /// first.
    regions: &'arena [Option<Name<'arena>>],
    /// The name the source writes for each dependent arrow's binder,
    /// ascending by the arrow.
    arrows: &'arena [(CompTypeId, Name<'arena>)],
    /// The relation each type the source writes as `A ≅ B`, `A ≃ B` or
    /// `A ⇝ B` abbreviates, ascending by the type.
    relations: &'arena [(ValueTypeId, Relation)],
}

impl<'arena> CoreSource<'arena>
{
    /// `arena`, its constants named by `names`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        arena: &'arena CoreArena,
        names: &'arena [Name<'arena>],
    ) -> Self
    {
        Self {
            arena,
            names,
            restoration: UNRESTORED,
            constructors: UNNAMED,
            context: &[],
            regions: &[],
            arrows: &[],
            relations: &[],
        }
    }

    /// This source, reading each node `restoration` restores as its
    /// original.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn restoring(
        self,
        restoration: &'arena Restoration,
    ) -> Self
    {
        Self {
            restoration,
            ..self
        }
    }

    /// This source, naming constructors and data cases from `constructors`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn naming(
        self,
        constructors: &'arena Constructors<'arena>,
    ) -> Self
    {
        Self {
            constructors,
            ..self
        }
    }

    /// This source, its roots standing under binders named by `context`,
    /// outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn within(
        self,
        context: &'arena [Option<Name<'arena>>],
    ) -> Self
    {
        Self { context, ..self }
    }

    /// This source, its roots standing in capability scopes named by
    /// `regions`, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scoped(
        self,
        regions: &'arena [Option<Name<'arena>>],
    ) -> Self
    {
        Self { regions, ..self }
    }

    /// This source, naming each dependent arrow's binder as `arrows` writes
    /// it, ascending by the arrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn naming_arrows(
        self,
        arrows: &'arena [(CompTypeId, Name<'arena>)],
    ) -> Self
    {
        Self { arrows, ..self }
    }

    /// This source, spelling each type `relations` records as the relation
    /// it was written as, ascending by the type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relating(
        self,
        relations: &'arena [(ValueTypeId, Relation)],
    ) -> Self
    {
        Self { relations, ..self }
    }

    /// The name at admission position `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the table's entry for `constant`; none past the table.
    /// - provides: the constant, abstract-type and family readings.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the constant and abstract-type readings at a live
    ///   admission position and the exact table end expose shifted names or a
    ///   missing-entry fallback.
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    #[spec(ensures: |ret| ret == self.names.get(usize::from(constant)).copied())]
    fn name(
        &self,
        constant: ConstantIndex,
    ) -> Option<Name<'arena>>
    {
        self.names.get(usize::from(constant)).copied()
    }

    /// The name a world is written by: a declared world's own name; none for
    /// the host's, which the surface never names.
    ///
    /// # Specification
    /// trivial.
    fn world_name(
        &self,
        world: World,
    ) -> Option<Name<'arena>>
    {
        match world {
            World::Host => None,
            World::Declared(constant) => self.name(constant),
        }
    }

    /// The name the family `datatype` names, a data type of the arena.
    ///
    /// # Specification
    /// trivial.
    fn family(
        &self,
        datatype: ValueTypeId,
    ) -> Option<Name<'arena>>
    {
        match *self.arena.value_type(self.unstaged(datatype))? {
            ValueType::Data { declaration, .. } => self.name(declaration),
            ValueType::Record(_)
            | ValueType::PathUniverse(..)
            | ValueType::Path { .. }
            | ValueType::Flow { .. }
            | ValueType::Run(_)
            | ValueType::Base(_)
            | ValueType::Product(_)
            | ValueType::Sum(_)
            | ValueType::List(_)
            | ValueType::Thunk(_)
            | ValueType::Universe { .. }
            | ValueType::Lift { .. }
            | ValueType::Element { .. }
            | ValueType::Abstract(_)
            | ValueType::StaticPi { .. }
            | ValueType::Sigma { .. }
            | ValueType::Unknown
            | ValueType::Stack { .. }
            | ValueType::Session(_)
            | ValueType::Capability { .. }
            | ValueType::Staged { .. }
            | ValueType::World(_) => None,
        }
    }

    /// The type the staged type `id` refines, or `id` itself: a stage is the
    /// recursion typing's own, and a source never writes one, so a staged
    /// type reads as the type it refines.
    ///
    /// # Specification
    /// - ensures: never a staged type, since the arena holds no stage over a
    ///   stage.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a staged type spells as the type it refines.
    /// - witness: `core_source::tests::a_staged_type_reads_as_the_type_it_refines`
    #[spec(ensures: |ret| !matches!(self.arena.value_type(ret), Some(ValueType::Staged { .. })))]
    fn unstaged(
        &self,
        id: ValueTypeId,
    ) -> ValueTypeId
    {
        match self.arena.value_type(id) {
            Some(&ValueType::Staged { base, .. }) => base,
            Some(_) | None => id,
        }
    }

    /// The relation the type `id` was written as, when the source records
    /// one, its operands read off the record or the flow it abbreviates.
    ///
    /// # Specification
    /// - requires: `relations` is ascending by the type.
    /// - ensures: for a recorded quasi-inverse or equivalence, the relation
    ///   over the forward map's domain and result, read off the record's first
    ///   component `+U (A -> -F B)`; for a recorded flow, the relation over the
    ///   flow's two codes; nothing for an unrecorded type, or a recorded one
    ///   whose node is no longer that shape.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each relation over its record or its flow spells as
    ///   written; the same record unrecorded spells as the record.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    #[spec(ensures: |ret| ret.is_none() || self.relations.binary_search_by_key(&id, |&(held, _)| held).is_ok())]
    fn related(
        &self,
        id: ValueTypeId,
    ) -> Option<Former<'arena, CoreNode>>
    {
        let at = self
            .relations
            .binary_search_by_key(&id, |&(held, _)| held)
            .ok()?;
        let &(_, relation) = self.relations.get(at)?;
        let (left, right) = match (relation, self.arena.value_type(id)?) {
            (Relation::Flow, &ValueType::Flow { source, target, .. }) => {
                (CoreNode::Value(source), CoreNode::Value(target))
            },
            (Relation::Isomorphism | Relation::Equivalence, &ValueType::Sigma { first, .. }) => {
                let &ValueType::Thunk(arrow) = self.arena.value_type(first)?
                else {
                    return None;
                };
                let &CompType::Arrow { domain, codomain } = self.arena.comp_type(arrow)?
                else {
                    return None;
                };
                let &CompType::Returner { result, .. } = self.arena.comp_type(codomain)?
                else {
                    return None;
                };
                (CoreNode::ValueType(domain), CoreNode::ValueType(result))
            },
            _ => return None,
        };

        Some(Former::Relation {
            relation,
            left,
            right,
        })
    }

    /// The value `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each value former read as its [`Former`];
    ///   [`Former::Unreadable`] for an id the arena does not hold.
    /// - provides: the value half of [`Source::read`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — concrete value formers retain their spellings; a pair
    ///   with distinct children and a truncated value handle distinguish
    ///   swapped child addresses and stale reads. Unrendered thunk bodies and
    ///   lift targets are deliberately not exposed by the adapter.
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
    /// - witness: `core_source::tests::holes_marks_and_the_unknown_type_read_as_unreadable`
    /// - witness: `core_source::tests::only_a_parameterised_constructor_carries_its_classifier`
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    /// - witness: `goldens::tests::native_paths_preserve_ordered_endpoints_and_maps`
    #[spec(ensures: |ret| match (self.arena.value(id), ret) {
        | (Some(&Value::ListCons(head, tail)), Former::ListCons(h, t)) => h == CoreNode::Value(head) && t == CoreNode::Value(tail),
        | (Some(&Value::Primitive { primitive, .. }), Former::Constant(name)) => name.as_ref() == primitive.name().as_ref(),
        | (Some(&Value::PathRefl(code)), Former::PathRefl(actual)) => actual == CoreNode::Value(code),
        | (Some(&Value::Here(point)), Former::Here(actual))
        | (Some(&Value::Stay(point)), Former::Stay(actual))
        | (Some(&Value::Forward(point)), Former::Forward(actual)) => actual == CoreNode::Value(point),
        | (Some(&Value::Univalence(record, _)), Former::Univalence(actual)) => actual == CoreNode::Value(record),
        | (Some(&Value::Funext(left, right)), Former::Funext(actual_left, actual_right))
        | (Some(&Value::Then(left, right)), Former::Then(actual_left, actual_right))
        | (Some(&Value::FlowProduct(left, right)), Former::FlowProduct(actual_left, actual_right))
        | (Some(&Value::FunctionFlow(left, right)), Former::FunctionFlow(actual_left, actual_right)) =>
            actual_left == CoreNode::Value(left) && actual_right == CoreNode::Value(right),
        | (Some(&Value::Equiv(forward, backward)), Former::Equiv(actual_forward, actual_backward))
        | (Some(&Value::PathEquiv { forward, backward, .. }), Former::PathEquiv(actual_forward, actual_backward)) =>
            actual_forward == CoreNode::Value(forward) && actual_backward == CoreNode::Value(backward),
        | (Some(&Value::SessionRelated { relation, source, target }), Former::SessionRelated(actual, actual_source, actual_target)) =>
            relation == actual && actual_source == CoreNode::Value(source) && actual_target == CoreNode::Value(target),
        | (Some(&Value::Ua { stratum, ref sides, forward, backward }), Former::Ua { stratum: actual_stratum, source, target, forward: actual_forward, backward: actual_backward }) =>
            stratum == actual_stratum && source.as_ref() == sides.source.name.as_ref() && target.as_ref() == sides.target.name.as_ref()
                && actual_forward == CoreNode::Value(forward) && actual_backward == CoreNode::Value(backward),
        | (Some(&Value::Variable { zone, index }), Former::Variable { zone: actual_zone, index: actual_index }) =>
            zone == actual_zone && index == actual_index,
        | (Some(&Value::Constant(index)), Former::Constant(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&Value::Constant(index)), Former::Unreadable(Unreadable::Unnamed)) => usize::from(index) >= self.names.len(),
        | (Some(&Value::Constructor { datatype, tag, ref fields }), Former::Constructor { name, arity, placement, classifier }) =>
            usize::from(arity) == fields.len() && name == self.family(datatype)
                .and_then(|family| self.constructors.constructor(family, Component::from(usize::from(tag))))
                .map(|(held, _)| held)
                && placement == self.family(datatype).map_or(crate::Placement::Applied, |family| self.constructors.placement(family, arity))
                && classifier.is_some() == matches!(self.arena.value_type(datatype), Some(ValueType::Data { arguments, .. }) if !arguments.is_empty()),
        | (Some(&Value::Recorded(ref moves)), Former::Recorded { payloads, .. }) =>
            usize::from(payloads) == moves.iter().filter(|step| matches!(step.payload(), Maybe::Present(_))).count(),
        (Some(&Value::Hole(_)), Former::Unreadable(Unreadable::Hole)) | (Some(&Value::Mark { .. }), Former::Unreadable(Unreadable::Mark))
            | (Some(&Value::Lift { .. }), Former::Unreadable(Unreadable::Lift)) | (None, Former::Unreadable(Unreadable::Dangling))
            | (Some(&Value::Reify(_)), Former::Reify) | (Some(&Value::ListNil), Former::ListNil) => true,
        | (Some(&Value::Thunk(body)), Former::Thunk(actual))
        | (Some(&Value::Nested(body)), Former::Nested(actual))
        | (Some(&Value::Returned(body)), Former::Returned(actual))
        | (Some(&Value::Run(body)), Former::Run(actual)) => actual == CoreNode::Computation(body),
        | (Some(&Value::Record(ref fields)), Former::Unit) => fields.is_empty(),
        | (Some(&Value::Record(ref fields)), Former::Record(arity)) => !fields.is_empty() && usize::from(arity) == fields.len(),
        | (Some(&Value::Literal(ref literal)), Former::Literal(actual)) =>
            core::ptr::eq(core::ptr::from_ref(literal), core::ptr::from_ref(actual)),
        | (Some(&Value::Tuple(ref components)), Former::Unit) => components.is_empty(),
        | (Some(&Value::Tuple(ref components)), Former::Tuple(arity)) => !components.is_empty() && usize::from(arity) == components.len(),
        | (Some(&Value::PathProduct(first, second)), Former::PathProduct(actual_first, actual_second)) =>
            actual_first == CoreNode::Value(first) && actual_second == CoreNode::Value(second),
        | (Some(&Value::Injection(summand, body)), Former::Injection(actual_summand, actual_body)) =>
            usize::from(summand) == usize::from(actual_summand) && actual_body == CoreNode::Value(body),
        | (Some(&Value::Quote(quoted)), Former::Quote(actual)) => actual == CoreNode::ValueType(quoted),
        | (Some(&Value::QuoteComputation(quoted)), Former::QuoteComputation(actual)) => actual == CoreNode::CompType(quoted),
        | (Some(&Value::StaticLambda(body)), Former::StaticLambda(actual)) => actual == CoreNode::Value(body),
        | (Some(&Value::StaticApplication(operator, argument)), Former::StaticApplication(actual_operator, actual_argument)) =>
            actual_operator == CoreNode::Value(operator) && actual_argument == CoreNode::Value(argument),
        | _ => false,
    })]
    fn value(
        &self,
        id: ValueId,
    ) -> Former<'arena, CoreNode>
    {
        let Some(value) = self.arena.value(id)
        else {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a handle that names no node: a malformed source, with no term to \
                              spell"
                )
            )]
            return Former::Unreadable(Unreadable::Dangling);
        };
        match *value {
            Value::Constructor {
                datatype,
                tag,
                ref fields,
            } => {
                let family = self.family(datatype);
                Former::Constructor {
                    name: family
                        .and_then(|family| {
                            self.constructors
                                .constructor(family, Component::from(usize::from(tag)))
                        })
                        .map(|(name, _)| name),
                    arity: Arity::from(fields.len()),
                    placement: family.map_or(crate::Placement::Applied, |family| {
                        self.constructors
                            .placement(family, Arity::from(fields.len()))
                    }),
                    classifier: match self.arena.value_type(datatype) {
                        Some(&ValueType::Data { ref arguments, .. }) if !arguments.is_empty() => {
                            Some(CoreNode::ValueType(datatype))
                        },
                        Some(_) | None => None,
                    },
                }
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a hole, a term the author has not written: the walk writes it as \
                              the grammar's hole `?`"
                )
            )]
            Value::Hole(_) => Former::Unreadable(Unreadable::Hole),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a mark, a term the elaborator could not type: the grammar has no \
                              spelling for a mark"
                )
            )]
            Value::Mark { .. } => Former::Unreadable(Unreadable::Mark),
            Value::Returned(body) => Former::Returned(CoreNode::Computation(body)),
            Value::Recorded(ref moves) => Former::Recorded {
                moves,
                payloads: Arity::from(
                    moves
                        .iter()
                        .filter(|step| matches!(step.payload(), Maybe::Present(_)))
                        .count(),
                ),
            },
            Value::SessionRelated {
                relation,
                source,
                target,
            } => Former::SessionRelated(relation, CoreNode::Value(source), CoreNode::Value(target)),
            Value::Stay(point) => Former::Stay(CoreNode::Value(point)),
            Value::Then(first, second) => {
                Former::Then(CoreNode::Value(first), CoreNode::Value(second))
            },
            Value::FlowProduct(first, second) => {
                Former::FlowProduct(CoreNode::Value(first), CoreNode::Value(second))
            },
            Value::Forward(translator) => Former::Forward(CoreNode::Value(translator)),
            Value::FunctionFlow(domain, codomain) => {
                Former::FunctionFlow(CoreNode::Value(domain), CoreNode::Value(codomain))
            },
            Value::Here(point) => Former::Here(CoreNode::Value(point)),
            Value::Nested(body) => Former::Nested(CoreNode::Computation(body)),
            Value::Run(body) => Former::Run(CoreNode::Computation(body)),
            Value::Funext(left, right) => {
                Former::Funext(CoreNode::Value(left), CoreNode::Value(right))
            },
            Value::Equiv(forward, backward) => {
                Former::Equiv(CoreNode::Value(forward), CoreNode::Value(backward))
            },
            Value::Univalence(record, _) => Former::Univalence(CoreNode::Value(record)),
            Value::Ua {
                stratum,
                ref sides,
                forward,
                backward,
            } => Former::Ua {
                stratum,
                source: Name::from(sides.source.name.as_ref()),
                target: Name::from(sides.target.name.as_ref()),
                forward: CoreNode::Value(forward),
                backward: CoreNode::Value(backward),
            },
            Value::Record(ref fields) if fields.is_empty() => Former::Unit,
            Value::Record(ref fields) => Former::Record(Arity::from(fields.len())),
            Value::Reify(_) => Former::Reify,
            Value::Primitive { primitive, .. } => {
                Former::Constant(Name::from(<&'static str>::from(primitive.name())))
            },
            Value::PathRefl(code) => Former::PathRefl(CoreNode::Value(code)),
            Value::PathProduct(first, second) => {
                Former::PathProduct(CoreNode::Value(first), CoreNode::Value(second))
            },
            Value::PathEquiv {
                forward, backward, ..
            } => Former::PathEquiv(CoreNode::Value(forward), CoreNode::Value(backward)),
            Value::Variable { zone, index } => Former::Variable { zone, index },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a name the naming table does not hold: a malformed table, with no \
                              name to write"
                )
            )]
            Value::Constant(constant) => self
                .name(constant)
                .map_or(Former::Unreadable(Unreadable::Unnamed), Former::Constant),
            Value::ListNil => Former::ListNil,
            Value::ListCons(head, tail) => {
                Former::ListCons(CoreNode::Value(head), CoreNode::Value(tail))
            },
            Value::Literal(ref literal) => Former::Literal(literal),
            Value::Tuple(ref components) if components.is_empty() => Former::Unit,
            Value::Tuple(ref components) => Former::Tuple(Arity::from(components.len())),
            Value::Injection(summand, body) => {
                Former::Injection(Component::from(usize::from(summand)), CoreNode::Value(body))
            },
            Value::Thunk(body) => Former::Thunk(CoreNode::Computation(body)),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a universe lift: the core's explicit cumulativity, which the \
                              surface grammar has no syntax for"
                )
            )]
            Value::Lift { .. } => Former::Unreadable(Unreadable::Lift),
            Value::Quote(quoted) => Former::Quote(CoreNode::ValueType(quoted)),
            Value::QuoteComputation(quoted) => Former::QuoteComputation(CoreNode::CompType(quoted)),
            Value::StaticLambda(body) => Former::StaticLambda(CoreNode::Value(body)),
            Value::StaticApplication(operator, argument) => {
                Former::StaticApplication(CoreNode::Value(operator), CoreNode::Value(argument))
            },
        }
    }

    /// The value type `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each value-type former read as its [`Former`];
    ///   [`Former::Unreadable`] for an id the arena does not hold.
    /// - provides: the value-type half of [`Source::read`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden type, universe and static-operator
    ///   fixtures observe constructor choice, child order and levels; exact-end
    ///   names and truncated handles observe absence. Lift targets remain
    ///   outside the former exposed here, and arbitrary type trees are not
    ///   enumerated by these fixtures.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::universes_spell_their_sort_and_level`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
    /// - witness: `core_source::tests::holes_marks_and_the_unknown_type_read_as_unreadable`
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    /// - witness: `goldens::tests::native_paths_preserve_ordered_endpoints_and_maps`
    /// - witness: `goldens::tests::session_types_spell_their_protocol_and_payloads`
    #[spec(ensures: |ret| match (self.arena.value_type(self.unstaged(id)), ret) {
        | (Some(&ValueType::Stack { input, output }), Former::Stack(a, b)) => a == CoreNode::CompType(input) && b == CoreNode::CompType(output),
        | (Some(&ValueType::PathUniverse(source, target)), Former::PathUniverse(actual_source, actual_target)) => actual_source == CoreNode::Value(source) && actual_target == CoreNode::Value(target),
        | (Some(&ValueType::Data { declaration, ref arguments }), Former::Data { name, arity }) =>
            usize::from(arity) == arguments.len() && self.name(declaration) == name,
        | (Some(&ValueType::Path { carrier, left, right }), Former::Path { carrier: actual_carrier, left: actual_left, right: actual_right })
        | (Some(&ValueType::Flow { carrier, source: left, target: right }), Former::Flow { carrier: actual_carrier, left: actual_left, right: actual_right }) =>
            actual_carrier == CoreNode::ValueType(carrier) && actual_left == CoreNode::Value(left) && actual_right == CoreNode::Value(right),
        (Some(&ValueType::Unknown), Former::Unreadable(Unreadable::UnknownType)) | (Some(&ValueType::Lift { .. }), Former::Unreadable(Unreadable::Lift))
            | (Some(&ValueType::World(WorldType::Capability(_))), Former::Unreadable(Unreadable::WorldCapability))
            | (None, Former::Unreadable(Unreadable::Dangling)) => true,
        | (Some(&ValueType::Record(ref fields)), Former::Product(arity)) => fields.is_empty() && usize::from(arity) == 0_usize,
        | (Some(&ValueType::Record(ref fields)), Former::RecordType(arity)) => !fields.is_empty() && usize::from(arity) == fields.len(),
        | (Some(&ValueType::Base(base)), Former::BaseType(actual)) => base == actual,
        | (Some(&ValueType::Product(ref parts)), Former::Product(arity))
        | (Some(&ValueType::Sum(ref parts)), Former::Sum(arity)) => usize::from(arity) == parts.len(),
        | (Some(&ValueType::List(element)), Former::List(actual)) => actual == CoreNode::ValueType(element),
        | (Some(&ValueType::Thunk(body)), Former::ThunkType(actual)) => actual == CoreNode::CompType(body),
        | (Some(&ValueType::Universe { sort, ref level }), Former::Universe { sort: actual_sort, level: actual_level }) =>
            sort == actual_sort && core::ptr::eq(core::ptr::from_ref(level), core::ptr::from_ref(actual_level)),
        | (Some(&ValueType::Element { code, .. }), Former::Element(actual))
        | (Some(&ValueType::Run(code)), Former::RunType(actual)) => actual == CoreNode::Value(code),
        | (Some(&ValueType::Abstract(index)), Former::Abstract(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&ValueType::Abstract(index)), Former::Unreadable(Unreadable::Unnamed)) => usize::from(index) >= self.names.len(),
        | (Some(&ValueType::StaticPi { domain, codomain }), Former::StaticPi { domain: actual_domain, codomain: actual_codomain })
        | (Some(&ValueType::Sigma { first: domain, second: codomain }), Former::Sigma { first: actual_domain, second: actual_codomain }) =>
            actual_domain == CoreNode::ValueType(domain) && actual_codomain == CoreNode::ValueType(codomain),
        | (Some(&ValueType::Session(ref session)), Former::Session { protocol, state, payloads }) =>
            core::ptr::eq(core::ptr::from_ref(protocol), core::ptr::from_ref(session.protocol())) && state == session.state() && usize::from(payloads) == session.payloads().len(),
        | (Some(&ValueType::Capability { grade, region, .. }), Former::Capability { grade: actual_grade, region: actual_region, .. }) =>
            grade == actual_grade && region == actual_region,
        | (Some(&ValueType::World(WorldType::At { inner, world })), Former::Located { inner: actual, world: named }) =>
            actual == CoreNode::ValueType(inner) && named == self.world_name(world),
        | (Some(&(ValueType::Sigma { .. } | ValueType::Flow { .. })), Former::Relation { .. }) =>
            self.relations.binary_search_by_key(&id, |&(held, _)| held).is_ok(),
        | _ => false,
    })]
    fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Former<'arena, CoreNode>
    {
        if let Some(related) = self.related(id) {
            return related;
        }
        let Some(value_type) = self.arena.value_type(self.unstaged(id))
        else {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a handle that names no node: a malformed source, with no term to \
                              spell"
                )
            )]
            return Former::Unreadable(Unreadable::Dangling);
        };
        match *value_type {
            ValueType::Data {
                declaration,
                ref arguments,
            } => Former::Data {
                name: self.name(declaration),
                arity: Arity::from(arguments.len()),
            },
            ValueType::Path {
                carrier,
                left,
                right,
            } => Former::Path {
                carrier: CoreNode::ValueType(carrier),
                left: CoreNode::Value(left),
                right: CoreNode::Value(right),
            },
            ValueType::Flow {
                carrier,
                source,
                target,
            } => Former::Flow {
                carrier: CoreNode::ValueType(carrier),
                left: CoreNode::Value(source),
                right: CoreNode::Value(target),
            },
            ValueType::Run(code) => Former::RunType(CoreNode::Value(code)),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the unknown type a hole or a mark synthesises: the walk writes it \
                              as the grammar's `unknown_type` where a type is read"
                )
            )]
            ValueType::Unknown => Former::Unreadable(Unreadable::UnknownType),
            ValueType::Record(ref fields) if fields.is_empty() => {
                Former::Product(Arity::from(0_usize))
            },
            ValueType::Record(ref fields) => Former::RecordType(Arity::from(fields.len())),
            ValueType::Product(ref parts) => Former::Product(Arity::from(parts.len())),
            ValueType::Sum(ref parts) => Former::Sum(Arity::from(parts.len())),
            ValueType::Stack { input, output } => {
                Former::Stack(CoreNode::CompType(input), CoreNode::CompType(output))
            },
            ValueType::PathUniverse(source, target) => {
                Former::PathUniverse(CoreNode::Value(source), CoreNode::Value(target))
            },
            ValueType::Base(base) => Former::BaseType(base),
            ValueType::List(element) => Former::List(CoreNode::ValueType(element)),
            ValueType::Thunk(body) => Former::ThunkType(CoreNode::CompType(body)),
            ValueType::Universe { sort, ref level } => Former::Universe { sort, level },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a universe lift: the core's explicit cumulativity, which the \
                              surface grammar has no syntax for"
                )
            )]
            ValueType::Lift { .. } => Former::Unreadable(Unreadable::Lift),
            ValueType::Element { code, .. } => Former::Element(CoreNode::Value(code)),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a name the naming table does not hold: a malformed table, with no \
                              name to write"
                )
            )]
            ValueType::Abstract(atom) => self
                .name(atom)
                .map_or(Former::Unreadable(Unreadable::Unnamed), Former::Abstract),
            ValueType::StaticPi { domain, codomain } => Former::StaticPi {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::ValueType(codomain),
            },
            ValueType::Sigma { first, second } => Former::Sigma {
                first: CoreNode::ValueType(first),
                second: CoreNode::ValueType(second),
            },
            ValueType::Session(ref session) => Former::Session {
                protocol: session.protocol(),
                state: session.state(),
                payloads: Arity::from(session.payloads().len()),
            },
            ValueType::Capability {
                ref authority,
                grade,
                region,
            } => Former::Capability {
                authority,
                grade,
                region,
            },
            ValueType::World(WorldType::At { inner, world }) => Former::Located {
                inner: CoreNode::ValueType(inner),
                world: self.world_name(world),
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a world's capability: the linear resource a migration spends, which \
                              the surface never writes"
                )
            )]
            ValueType::World(WorldType::Capability(_)) => {
                Former::Unreadable(Unreadable::WorldCapability)
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "never reached: the read strips a stage first, and the arena holds \
                              no stage over a stage"
                )
            )]
            // Never read: the arena holds no stage over a stage.
            ValueType::Staged { .. } => Former::Unreadable(Unreadable::Dangling),
        }
    }

    /// The computation type `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each computation-type former read as its [`Former`];
    ///   [`Former::Unreadable`] for an id the arena does not hold.
    /// - provides: the computation-type half of [`Source::read`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returners, arrows, dependent types and computation
    ///   codes in the finite grammar fixtures distinguish wrong formers and
    ///   child positions. A direct returner read and truncation distinguish the
    ///   child family and stale handles; arbitrary dependent trees are outside
    ///   these fixtures.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::static_operators_spell_as_the_grammar_writes_them`
    /// - witness: `goldens::tests::dependent_function_type_breaks_before_codomain`
    /// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
    /// - witness: `core_source::tests::holes_marks_and_the_unknown_type_read_as_unreadable`
    #[spec(ensures: |ret| match (self.arena.comp_type(id), ret) {
        | (Some(&CompType::With(first, second)), Former::With(a, b)) => a == CoreNode::CompType(first) && b == CoreNode::CompType(second),
        | (Some(&CompType::Unknown), Former::Unreadable(Unreadable::UnknownType)) | (None, Former::Unreadable(Unreadable::Dangling)) => true,
        | (Some(&CompType::Returner { result, ref effects }), Former::Returner(actual)) => actual == CoreNode::ValueType(result) && effects.purity() == gandr_core_term::effect::Purity::Pure,
        | (Some(&CompType::Returner { result, ref effects }), Former::EffectfulReturner { result: actual, .. }) => actual == CoreNode::ValueType(result) && effects.purity() == gandr_core_term::effect::Purity::Effectful,
        | (Some(&CompType::Arrow { domain, codomain }), Former::Arrow { domain: actual_domain, codomain: actual_codomain })
        | (Some(&CompType::Pi { domain, codomain }), Former::Pi { domain: actual_domain, codomain: actual_codomain }) =>
            actual_domain == CoreNode::ValueType(domain) && actual_codomain == CoreNode::CompType(codomain),
        | (Some(&CompType::Element { code, .. }), Former::ComputationElement(actual)) => actual == CoreNode::Value(code),
        | _ => false,
    })]
    fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Former<'arena, CoreNode>
    {
        let Some(comp_type) = self.arena.comp_type(id)
        else {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a handle that names no node: a malformed source, with no term to \
                              spell"
                )
            )]
            return Former::Unreadable(Unreadable::Dangling);
        };
        match *comp_type {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "the unknown type a hole or a mark synthesises: the walk writes it \
                              as the grammar's `unknown_type` where a type is read"
                )
            )]
            CompType::Unknown => Former::Unreadable(Unreadable::UnknownType),
            CompType::With(first, second) => {
                Former::With(CoreNode::CompType(first), CoreNode::CompType(second))
            },
            CompType::Returner {
                result,
                ref effects,
            } => {
                if effects.purity() == gandr_core_term::effect::Purity::Pure {
                    Former::Returner(CoreNode::ValueType(result))
                }
                else {
                    Former::EffectfulReturner {
                        result: CoreNode::ValueType(result),
                        effects,
                    }
                }
            },
            CompType::Arrow { domain, codomain } => Former::Arrow {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::CompType(codomain),
            },
            CompType::Pi { domain, codomain } => Former::Pi {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::CompType(codomain),
            },
            CompType::Element { code, .. } => Former::ComputationElement(CoreNode::Value(code)),
        }
    }

    /// The computation `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each computation former read as its [`Former`], its children
    ///   as nodes of their families and its names spelled: a primitive by its
    ///   prelude function's name, an operation and a record field by their own,
    ///   a scope by its interface's; a hole and a mark as the honest set's, and
    ///   an id the arena does not hold as dangling.
    /// - provides: the computation half of [`Source::read`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the computation golden reads every computation former
    ///   and its children in order; a truncated arena reads dangling.
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
    /// - witness: `core_source::tests::holes_marks_and_the_unknown_type_read_as_unreadable`
    #[spec(ensures: |ret| match (self.arena.computation(id), ret) {
        | (Some(&Computation::Hole(_)), Former::Unreadable(Unreadable::Hole))
        | (Some(&Computation::Mark { .. }), Former::Unreadable(Unreadable::Mark))
        | (None, Former::Unreadable(Unreadable::Dangling)) => true,
        | (Some(&Computation::Return(value)), Former::Return(actual))
        | (Some(&Computation::Force(value)), Former::Force(actual)) => actual == CoreNode::Value(value),
        | (Some(&Computation::Lambda(body)), Former::Lambda(actual))
        | (Some(&Computation::Fixpoint { body, .. }), Former::Fixpoint(actual))
        | (Some(&Computation::Reset(body)), Former::Reset(actual))
        | (Some(&Computation::Shift(body)), Former::Shift(actual)) => actual == CoreNode::Computation(body),
        | (Some(&Computation::Bind(bound, rest)), Former::Bind(actual_bound, actual_rest)) =>
            actual_bound == CoreNode::Computation(bound) && actual_rest == CoreNode::Computation(rest),
        | (Some(&Computation::Ascribe { body, ty }), Former::Ascription { body: actual_body, ty: actual_ty }) =>
            actual_body == CoreNode::Computation(body) && actual_ty == CoreNode::CompType(ty),
        | (Some(&Computation::Application(function, argument)), Former::Application(actual_function, actual_argument)) =>
            actual_function == CoreNode::Computation(function) && actual_argument == CoreNode::Value(argument),
        | (Some(&Computation::Primitive { primitive, ref arguments }), Former::Primitive { name, arity }) =>
            name.as_ref() == primitive.name().as_ref() && usize::from(arity) == arguments.len(),
        | (Some(&Computation::Case { scrutinee, ref branches }), Former::Case { scrutinee: actual, arity }) =>
            actual == CoreNode::Value(scrutinee) && usize::from(arity) == branches.len(),
        | (Some(&Computation::DataCase { scrutinee, ref branches, .. }), Former::DataCase { scrutinee: actual, arity }) =>
            actual == CoreNode::Value(scrutinee) && usize::from(arity) == branches.len(),
        | (Some(&Computation::Split { scrutinee, arity, body, .. }), Former::Split { scrutinee: actual, arity: actual_arity, body: actual_body }) =>
            actual == CoreNode::Value(scrutinee) && usize::from(arity) == usize::from(actual_arity) && actual_body == CoreNode::Computation(body),
        | (Some(&Computation::Handle { ref clauses, .. }), Former::Handle { clauses: count, .. })
        | (Some(&Computation::Scope { ref clauses, .. }), Former::Scope { clauses: count, .. }) => usize::from(count) == clauses.len(),
        | (Some(&Computation::Session(ref action)), _) => match (action, ret) {
            | (&SessionAction::Send { endpoint, payload }, Former::Send { endpoint: actual, payload: actual_payload }) =>
                endpoint == actual && actual_payload == CoreNode::Value(payload),
            | (&SessionAction::Receive { endpoint }, Former::Receive(actual))
            | (&SessionAction::Close { endpoint }, Former::Close(actual)) => endpoint == actual,
            | (&SessionAction::Select { endpoint, ref label }, Former::Select { endpoint: actual, label: actual_label }) =>
                endpoint == actual && actual_label.as_ref() == label.as_ref(),
            | (&SessionAction::Offer { endpoint, ref arms }, Former::Offer { endpoint: actual, arms: count }) =>
                endpoint == actual && usize::from(count) == arms.len(),
            | (&SessionAction::Fork { .. }, Former::Fork { .. }) => true,
            | _ => false,
        },
        | (Some(&Computation::Memory(ref form)), _) => match (form, ret) {
            | (&MemoryForm::Hold { value, body }, Former::Hold { value: held, body: scope }) =>
                held == CoreNode::Value(value) && scope == CoreNode::Computation(body),
            | (&MemoryForm::Access { held, body, unwind }, Former::Access { held: actual, body: lent, unwind: unwound }) =>
                held == actual && lent == CoreNode::Computation(body) && unwound == CoreNode::Computation(unwind),
            | (&MemoryForm::Resume { view, value }, Former::ResumeView { view: actual, value: written }) =>
                view == actual && written == CoreNode::Value(value),
            | (&MemoryForm::Abort { view }, Former::AbortView(actual)) => view == actual,
            | _ => false,
        },
        | (Some(&Computation::World(ref form)), _) => match (form, ret) {
            | (&WorldForm::Hold { value }, Former::WorldHold(held)) => held == CoreNode::Value(value),
            | (&WorldForm::Leta { value, body }, Former::Leta { value: opened, body: rest }) =>
                opened == CoreNode::Value(value) && rest == CoreNode::Computation(body),
            | (&WorldForm::Migrate { world, body }, Former::Migrate { world: named, body: run }) =>
                run == CoreNode::Computation(body) && named == self.world_name(world),
            | _ => false,
        },
        | (Some(_), _) => !matches!(ret, Former::Unreadable(_)),
        | (None, _) => false,
    })]
    fn computation(
        &self,
        id: ComputationId,
    ) -> Former<'arena, CoreNode>
    {
        let value = CoreNode::Value;
        let computation = CoreNode::Computation;
        let Some(held) = self.arena.computation(id)
        else {
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a handle that names no node: a malformed source, with no term to \
                              spell"
                )
            )]
            return Former::Unreadable(Unreadable::Dangling);
        };
        match *held {
            Computation::Return(returned) => Former::Return(value(returned)),
            Computation::Bind(bound, rest) => Former::Bind(computation(bound), computation(rest)),
            Computation::Ascribe { body, ty } => Former::Ascription {
                body: computation(body),
                ty: CoreNode::CompType(ty),
            },
            Computation::Force(thunk) => Former::Force(value(thunk)),
            Computation::Application(function, argument) => {
                Former::Application(computation(function), value(argument))
            },
            Computation::Lambda(body) => Former::Lambda(computation(body)),
            Computation::Primitive {
                primitive,
                ref arguments,
            } => Former::Primitive {
                name: Name::from(<&'static str>::from(primitive.name())),
                arity: Arity::from(arguments.len()),
            },
            Computation::Transport(path, transported) => {
                Former::Transport(value(path), value(transported))
            },
            Computation::PathTransport {
                motive,
                path,
                value: transported,
            } => Former::PathTransport {
                motive: CoreNode::ValueType(motive),
                path: value(path),
                value: value(transported),
            },
            Computation::Ride {
                motive,
                flow,
                value: moved,
            } => Former::Ride {
                motive: CoreNode::ValueType(motive),
                flow: value(flow),
                value: value(moved),
            },
            Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value: transported,
            } => Former::TelescopeTransport {
                motive: CoreNode::CompType(motive),
                path: value(path),
                start: value(start),
                over: value(over),
                value: value(transported),
            },
            Computation::Fixpoint { body, .. } => Former::Fixpoint(computation(body)),
            Computation::Case {
                scrutinee,
                ref branches,
            } => Former::Case {
                scrutinee: value(scrutinee),
                arity: Arity::from(branches.len()),
            },
            Computation::Split {
                scrutinee,
                arity,
                body,
                ..
            } => Former::Split {
                scrutinee: value(scrutinee),
                arity: Arity::from(usize::from(arity)),
                body: computation(body),
            },
            Computation::DataCase {
                scrutinee,
                ref branches,
                ..
            } => Former::DataCase {
                scrutinee: value(scrutinee),
                arity: Arity::from(branches.len()),
            },
            Computation::RecordProjection(record, ref label) => {
                Former::RecordProjection(value(record), Name::from(label.as_ref()))
            },
            Computation::TupleProjection(tuple, component) => {
                Former::TupleProjection(value(tuple), Component::from(usize::from(component)))
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a hole, a term the author has not written: the walk writes it as \
                              the grammar's hole `?`"
                )
            )]
            Computation::Hole(_) => Former::Unreadable(Unreadable::Hole),
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    answer_totality,
                    reason = "a mark, a term the elaborator could not type: the grammar has no \
                              spelling for a mark"
                )
            )]
            Computation::Mark { .. } => Former::Unreadable(Unreadable::Mark),
            Computation::ListFold {
                list,
                on_nil,
                on_cons,
                ..
            } => Former::ListFold {
                list: value(list),
                nil: computation(on_nil),
                cons: computation(on_cons),
            },
            Computation::Perform {
                ref operation,
                payload,
                ..
            } => Former::Perform {
                operation: Name::from(operation.as_ref()),
                payload: value(payload),
            },
            Computation::Handle {
                subject,
                on_return,
                ref clauses,
                ..
            } => Former::Handle {
                subject: computation(subject),
                on_return: computation(on_return),
                clauses: Arity::from(clauses.len()),
            },
            Computation::Exercise {
                capability,
                ref operation,
                payload,
                ..
            } => Former::Exercise {
                capability: value(capability),
                operation: Name::from(operation.as_ref()),
                payload: value(payload),
            },
            Computation::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => Former::Scope {
                interface: Name::from(signature.name().as_ref()),
                subject: computation(subject),
                on_return: computation(on_return),
                clauses: Arity::from(clauses.len()),
            },
            Computation::Resume(stack, resumed) => {
                Former::Resume(value(stack), computation(resumed))
            },
            Computation::Reset(body) => Former::Reset(computation(body)),
            Computation::Shift(body) => Former::Shift(computation(body)),
            Computation::With(first, second) => {
                Former::Lazy(computation(first), computation(second))
            },
            Computation::Project(side, observed) => Former::Project(
                Component::from(match side {
                    Side::Left => 0_usize,
                    Side::Right => 1_usize,
                }),
                computation(observed),
            ),
            Computation::Session(ref action) => match *action {
                SessionAction::Send { endpoint, payload } => Former::Send {
                    endpoint,
                    payload: value(payload),
                },
                SessionAction::Receive { endpoint } => Former::Receive(endpoint),
                SessionAction::Select {
                    endpoint,
                    ref label,
                } => Former::Select {
                    endpoint,
                    label: Name::from(label.as_ref()),
                },
                SessionAction::Offer { endpoint, ref arms } => Former::Offer {
                    endpoint,
                    arms: Arity::from(arms.len()),
                },
                SessionAction::Close { endpoint } => Former::Close(endpoint),
                SessionAction::Fork {
                    protocol,
                    child,
                    parent,
                } => Former::Fork {
                    protocol: CoreNode::ValueType(protocol),
                    child: computation(child),
                    parent: computation(parent),
                },
            },
            Computation::Memory(ref form) => match *form {
                MemoryForm::Hold { value: held, body } => Former::Hold {
                    value: value(held),
                    body: computation(body),
                },
                MemoryForm::Access { held, body, unwind } => Former::Access {
                    held,
                    body: computation(body),
                    unwind: computation(unwind),
                },
                MemoryForm::Resume {
                    view,
                    value: written,
                } => Former::ResumeView {
                    view,
                    value: value(written),
                },
                MemoryForm::Abort { view } => Former::AbortView(view),
            },
            Computation::World(ref form) => match *form {
                WorldForm::Hold { value: held } => Former::WorldHold(value(held)),
                WorldForm::Leta {
                    value: opened,
                    body,
                } => Former::Leta {
                    value: value(opened),
                    body: computation(body),
                },
                WorldForm::Migrate { world, body } => Former::Migrate {
                    world: self.world_name(world),
                    body: computation(body),
                },
            },
        }
    }
}

impl Source for CoreSource<'_>
{
    type Node = CoreNode;

    /// The node `node` names in the arena.
    ///
    /// # Specification
    /// - requires: nothing; an id from another arena reads as whatever this
    ///   arena holds at it, or as unreadable.
    /// - ensures: as [`Source::read`], of the node `node` restores to: each
    ///   family read by its own reader, every former of the family as its own
    ///   [`Former`] over its children, the honest set's members — a hole, a
    ///   mark, the unknown type, a lift — as unreadable, and a missing handle
    ///   as dangling.
    /// - provides: the printer's reading of the core arena.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact golden spellings distinguish constructor
    ///   selection over the finite type and value fixtures. Direct reads of all
    ///   four families, distinct pair children and a truncated arena
    ///   distinguish namespace confusion, reversed children and stale handles.
    ///   An arbitrary arena or naming table is outside this finite evidence.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `core_source::tests::family_reads_preserve_children_and_reject_truncation`
    /// - witness: `core_source::tests::holes_marks_and_the_unknown_type_read_as_unreadable`
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    /// - witness: `goldens::tests::native_paths_preserve_ordered_endpoints_and_maps`
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `core_source::tests::a_restored_elaboration_reads_as_written`
    #[spec(captures: restored = self.restoration.restored(node), ensures: |ret| match restored {
        | CoreNode::Value(id) if self.arena.value(id).is_none() => matches!(ret, Former::Unreadable(Unreadable::Dangling)),
        | CoreNode::Computation(id) if self.arena.computation(id).is_none() => matches!(ret, Former::Unreadable(Unreadable::Dangling)),
        | CoreNode::ValueType(id) if self.arena.value_type(id).is_none() => matches!(ret, Former::Unreadable(Unreadable::Dangling)),
        | CoreNode::CompType(id) if self.arena.comp_type(id).is_none() => matches!(ret, Former::Unreadable(Unreadable::Dangling)),
        | CoreNode::Value(_) | CoreNode::Computation(_) | CoreNode::ValueType(_) | CoreNode::CompType(_) => true,
    })]
    #[inline]
    fn read(
        &self,
        node: CoreNode,
    ) -> Former<'_, CoreNode>
    {
        match self.restoration.restored(node) {
            CoreNode::Value(id) => self.value(id),
            CoreNode::Computation(id) => self.computation(id),
            CoreNode::ValueType(id) => self.value_type(id),
            CoreNode::CompType(id) => self.comp_type(id),
        }
    }

    /// The handle of component `index` of the n-ary former `node` names in
    /// the arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the node `node` restores to, the value type at `index`
    ///   among a held product's, sum's or record type's components and a
    ///   session type's payloads; the value at `index` among a held tuple's,
    ///   record's or constructor's fields and a family's arguments; the value
    ///   among a primitive's arguments and the computation among a case's or a
    ///   data case's branches, a handler's operation clauses and an offer's
    ///   arms; a record's fields and an offer's arms in label order; none for
    ///   an index past them, another former, another family or a missing
    ///   handle.
    /// - provides: the printer's reading of an n-ary former.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a record's field is reached by counting through its
    ///   label-ordered map, linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden braces read every component of products
    ///   and sums of arity one to three, of tuples of arity one to three and of
    ///   records of two fields, in order, and the computation golden a case's
    ///   branches and a handler's clauses; a direct read past the arity and of
    ///   a non-product observes the absence.
    /// - witness: `goldens::tests::n_ary_products_and_sums_spell_between_their_braces`
    /// - witness: `goldens::tests::n_ary_tuples_and_injections_spell_between_their_braces`
    /// - witness: `goldens::tests::records_spell_their_fields_in_label_order`
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `core_source::tests::components_read_in_order_and_stop_at_the_arity`
    #[spec(captures: restored = self.restoration.restored(node), ensures: |ret| match restored {
        | CoreNode::ValueType(id) => ret == match self.arena.value_type(self.unstaged(id)) {
            | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => parts.get(usize::from(index)).map(|&part| CoreNode::ValueType(part)),
            | Some(&ValueType::Record(ref fields)) => fields.values().nth(usize::from(index)).map(|&field| CoreNode::ValueType(field)),
            | Some(&ValueType::Data { ref arguments, .. }) => arguments.get(usize::from(index)).map(|&argument| CoreNode::Value(argument)),
            | Some(_) | None => ret,
        },
        | CoreNode::Value(id) => ret == match self.arena.value(id) {
            | Some(&Value::Tuple(ref components)) => components.get(usize::from(index)).map(|&component| CoreNode::Value(component)),
            | Some(&Value::Record(ref fields)) => fields.values().nth(usize::from(index)).map(|&field| CoreNode::Value(field)),
            | Some(&Value::Constructor { ref fields, .. }) => fields.get(usize::from(index)).map(|&field| CoreNode::Value(field)),
            | Some(&Value::Recorded(ref moves)) => moves.iter()
                .filter_map(|step| match step.payload() { Maybe::Present(payload) => Some(CoreNode::Value(payload)), Maybe::Absent(_) => None })
                .nth(usize::from(index)),
            | Some(_) | None => None,
        },
        | CoreNode::Computation(id) => self.arena.computation(id).is_some() || ret.is_none(),
        | CoreNode::CompType(_) => ret.is_none(),
    })]
    #[inline]
    fn component(
        &self,
        node: CoreNode,
        index: Component,
    ) -> Option<CoreNode>
    {
        let at = usize::from(index);
        match self.restoration.restored(node) {
            CoreNode::ValueType(id) => match *self.arena.value_type(self.unstaged(id))? {
                ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                    parts.get(at).map(|&part| CoreNode::ValueType(part))
                },
                ValueType::Record(ref fields) => fields
                    .values()
                    .nth(at)
                    .map(|&field| CoreNode::ValueType(field)),
                ValueType::Session(ref session) => session
                    .payloads()
                    .get(at)
                    .map(|&payload| CoreNode::ValueType(payload)),
                ValueType::Data { ref arguments, .. } => {
                    arguments.get(at).map(|&argument| CoreNode::Value(argument))
                },
                ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Run(_)
                | ValueType::Base(_)
                | ValueType::List(_)
                | ValueType::Thunk(_)
                | ValueType::Universe { .. }
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::StaticPi { .. }
                | ValueType::Sigma { .. }
                | ValueType::Unknown
                | ValueType::Stack { .. }
                | ValueType::Capability { .. }
                | ValueType::Staged { .. }
                | ValueType::World(_) => None,
            },
            CoreNode::Value(id) => match *self.arena.value(id)? {
                Value::Tuple(ref components) => components
                    .get(at)
                    .map(|&component| CoreNode::Value(component)),
                Value::Record(ref fields) => {
                    fields.values().nth(at).map(|&field| CoreNode::Value(field))
                },
                Value::Constructor { ref fields, .. } => {
                    fields.get(at).map(|&field| CoreNode::Value(field))
                },
                Value::Recorded(ref moves) => moves
                    .iter()
                    .filter_map(|step| match step.payload() {
                        Maybe::Present(payload) => Some(CoreNode::Value(payload)),
                        Maybe::Absent(_) => None,
                    })
                    .nth(at),
                Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..)
                | Value::Primitive { .. }
                | Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::PathEquiv { .. }
                | Value::Here(_)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Univalence(..)
                | Value::Ua { .. }
                | Value::Returned(_)
                | Value::Nested(_)
                | Value::Run(_)
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Injection(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticLambda(_)
                | Value::StaticApplication(..)
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::Reify(_) => None,
            },
            CoreNode::Computation(id) => match *self.arena.computation(id)? {
                Computation::Primitive { ref arguments, .. } => {
                    arguments.get(at).map(|&argument| CoreNode::Value(argument))
                },
                Computation::Case { ref branches, .. } => branches
                    .get(at)
                    .map(|&branch| CoreNode::Computation(branch)),
                Computation::DataCase { ref branches, .. } => branches
                    .get(at)
                    .map(|&branch| CoreNode::Computation(branch)),
                Computation::Handle { ref clauses, .. }
                | Computation::Scope { ref clauses, .. } => clauses
                    .get(at)
                    .map(|clause| CoreNode::Computation(clause.body)),
                Computation::Session(SessionAction::Offer { ref arms, .. }) => {
                    arms.values().nth(at).map(|&arm| CoreNode::Computation(arm))
                },
                Computation::Session(
                    SessionAction::Send { .. }
                    | SessionAction::Receive { .. }
                    | SessionAction::Select { .. }
                    | SessionAction::Close { .. }
                    | SessionAction::Fork { .. },
                )
                | Computation::Memory(_)
                | Computation::World(_)
                | Computation::Transport(..)
                | Computation::PathTransport { .. }
                | Computation::TelescopeTransport { .. }
                | Computation::Ride { .. }
                | Computation::Lambda(_)
                | Computation::Fixpoint { .. }
                | Computation::Application(..)
                | Computation::Return(_)
                | Computation::Bind(..)
                | Computation::Force(_)
                | Computation::Split { .. }
                | Computation::RecordProjection(..)
                | Computation::TupleProjection(..)
                | Computation::Hole(_)
                | Computation::Mark { .. }
                | Computation::ListFold { .. }
                | Computation::Ascribe { .. }
                | Computation::Perform { .. }
                | Computation::Exercise { .. }
                | Computation::Resume(..)
                | Computation::Reset(_)
                | Computation::Shift(_)
                | Computation::With(..)
                | Computation::Project(..) => None,
            },
            CoreNode::CompType(_) => None,
        }
    }

    /// The label of entry `index` of the record, the record type, the
    /// handler or the offer `node` names in the arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the node `node` restores to, the label at `index` among a
    ///   held record's or record type's fields and an offer's arms, in label
    ///   order, and the operation a handler's clause at `index` answers; none
    ///   for an index past them, another former, another family or a missing
    ///   handle.
    /// - provides: the printer's reading of a record's labels, a handler's
    ///   operations and an offer's labels.
    /// - fails: never.
    /// - panics: none.
    /// - intension: as [`Self::component`], linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — records and record types of two fields written out of
    ///   label order spell each field under its own label, and a handler's
    ///   clause its operation; a direct read past the fields and of a tuple
    ///   observes the absence.
    /// - witness: `goldens::tests::records_spell_their_fields_in_label_order`
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    /// - witness: `core_source::tests::components_read_in_order_and_stop_at_the_arity`
    #[spec(captures: restored = self.restoration.restored(node), ensures: |ret| match restored {
        | CoreNode::ValueType(id) => ret.as_ref().map(|name| -> &str { name.as_ref() }) == match self.arena.value_type(self.unstaged(id)) {
            | Some(&ValueType::Record(ref fields)) => fields.keys().nth(usize::from(index)).map(AsRef::as_ref),
            | Some(_) | None => None,
        },
        | CoreNode::Value(id) => ret.as_ref().map(|name| -> &str { name.as_ref() }) == match self.arena.value(id) {
            | Some(&Value::Record(ref fields)) => fields.keys().nth(usize::from(index)).map(AsRef::as_ref),
            | Some(_) | None => None,
        },
        | CoreNode::Computation(id) => self.arena.computation(id).is_some() || ret.is_none(),
        | CoreNode::CompType(_) => ret.is_none(),
    })]
    #[inline]
    fn label(
        &self,
        node: CoreNode,
        index: Component,
    ) -> Option<Name<'_>>
    {
        let at = usize::from(index);
        let label: &str = match self.restoration.restored(node) {
            CoreNode::ValueType(id) => match *self.arena.value_type(self.unstaged(id))? {
                ValueType::Record(ref fields) => fields.keys().nth(at).map(AsRef::as_ref),
                ValueType::Data { .. }
                | ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Run(_)
                | ValueType::Base(_)
                | ValueType::Product(_)
                | ValueType::Sum(_)
                | ValueType::List(_)
                | ValueType::Thunk(_)
                | ValueType::Universe { .. }
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::StaticPi { .. }
                | ValueType::Sigma { .. }
                | ValueType::Unknown
                | ValueType::Stack { .. }
                | ValueType::Session(_)
                | ValueType::Capability { .. }
                | ValueType::Staged { .. }
                | ValueType::World(_) => None,
            },
            CoreNode::Value(id) => match *self.arena.value(id)? {
                Value::Record(ref fields) => fields.keys().nth(at).map(AsRef::as_ref),
                Value::Primitive { .. }
                | Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::PathEquiv { .. }
                | Value::Here(_)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Univalence(..)
                | Value::Ua { .. }
                | Value::Returned(_)
                | Value::Nested(_)
                | Value::Run(_)
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Tuple(_)
                | Value::Injection(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticLambda(_)
                | Value::StaticApplication(..)
                | Value::Constructor { .. }
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::Reify(_)
                | Value::Recorded(_)
                | Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..) => None,
            },
            CoreNode::Computation(id) => match *self.arena.computation(id)? {
                Computation::Handle { ref clauses, .. }
                | Computation::Scope { ref clauses, .. } => {
                    clauses.get(at).map(|clause| clause.operation.as_ref())
                },
                Computation::Session(SessionAction::Offer { ref arms, .. }) => {
                    arms.keys().nth(at).map(AsRef::as_ref)
                },
                Computation::Session(
                    SessionAction::Send { .. }
                    | SessionAction::Receive { .. }
                    | SessionAction::Select { .. }
                    | SessionAction::Close { .. }
                    | SessionAction::Fork { .. },
                )
                | Computation::Memory(_)
                | Computation::World(_)
                | Computation::Primitive { .. }
                | Computation::Transport(..)
                | Computation::PathTransport { .. }
                | Computation::TelescopeTransport { .. }
                | Computation::Ride { .. }
                | Computation::Lambda(_)
                | Computation::Fixpoint { .. }
                | Computation::Application(..)
                | Computation::Return(_)
                | Computation::Bind(..)
                | Computation::Force(_)
                | Computation::Case { .. }
                | Computation::Split { .. }
                | Computation::DataCase { .. }
                | Computation::RecordProjection(..)
                | Computation::TupleProjection(..)
                | Computation::Hole(_)
                | Computation::Mark { .. }
                | Computation::ListFold { .. }
                | Computation::Perform { .. }
                | Computation::Exercise { .. }
                | Computation::Resume(..)
                | Computation::Reset(_)
                | Computation::Shift(_)
                | Computation::With(..)
                | Computation::Ascribe { .. }
                | Computation::Project(..) => None,
            },
            CoreNode::CompType(_) => None,
        }?;
        Some(Name::from(label))
    }

    /// The constructor of the family the data case `node` eliminates at tag
    /// `index`, and its field count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a held data case the constructor table records a family
    ///   for, the family's constructor at `index`; none otherwise.
    /// - provides: a data case's patterns.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Source::constructor`].
    /// - witness: `goldens::tests::an_elaborated_body_prints_with_its_exits_elided`
    #[spec(ensures: |ret| ret.is_none() || matches!(self.restoration.restored(node), CoreNode::Computation(_)))]
    #[inline]
    fn constructor(
        &self,
        node: CoreNode,
        index: Component,
    ) -> Option<(Name<'_>, Arity)>
    {
        let CoreNode::Computation(id) = self.restoration.restored(node)
        else {
            return None;
        };
        let family = *self.constructors.cases.get(&id)?;
        self.constructors.constructor(family, index)
    }

    /// The names of the binders the root stands under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn context(&self) -> &[Option<Name<'_>>]
    {
        self.context
    }

    /// The names of the capability scopes the root stands in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn regions(&self) -> &[Option<Name<'_>>]
    {
        self.regions
    }

    /// The name the source writes for a dependent arrow's binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn arrow_binder(
        &self,
        node: CoreNode,
    ) -> Option<Name<'_>>
    {
        let CoreNode::CompType(id) = self.restoration.restored(node)
        else {
            return None;
        };
        self.arrows
            .binary_search_by_key(&id, |&(arrow, _)| arrow)
            .ok()
            .and_then(|at| self.arrows.get(at))
            .map(|&(_, name)| name)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;

    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FieldLabel;

    use super::Component;
    use super::ConstantIndex;
    use super::CoreArena;
    use super::CoreNode;
    use super::CoreSource;
    use super::Former;
    use super::Name;
    use super::Source as _;
    use super::Unreadable;

    /// Node families retain child order and refuse handles dropped by
    /// truncation.
    #[test]
    fn family_reads_preserve_children_and_reject_truncation()
    {
        let mut arena = CoreArena::new();
        let mark = arena.watermark();
        let first = arena.value_unit();
        let second = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
        let pair = arena.value_tuple(&[first, second]);
        let computation = arena.computation_return(first);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        let source = CoreSource::new(&arena, &[]);
        assert!(matches!(
            source.read(CoreNode::Value(pair)),
            Former::Tuple(arity) if usize::from(arity) == 2
        ));
        assert_eq!(
            [
                Some(CoreNode::Value(first)),
                Some(CoreNode::Value(second)),
                None
            ],
            [0_usize, 1, 2]
                .map(|index| source.component(CoreNode::Value(pair), Component::from(index))),
            "a tuple's components read in order and stop at its arity"
        );
        assert!(matches!(
            source.read(CoreNode::Computation(computation)),
            Former::Return(value) if value == CoreNode::Value(first)
        ));
        assert!(matches!(
            source.read(CoreNode::ValueType(value_type)),
            Former::Product(arity) if usize::from(arity) == 0
        ));
        assert!(
            matches!(source.read(CoreNode::CompType(comp_type)), Former::Returner(body)
            if body == CoreNode::ValueType(value_type))
        );
        arena.truncate_to(mark);
        let source = CoreSource::new(&arena, &[]);
        for node in [
            CoreNode::Value(pair),
            CoreNode::Computation(computation),
            CoreNode::ValueType(value_type),
            CoreNode::CompType(comp_type),
        ] {
            assert!(matches!(
                source.read(node),
                Former::Unreadable(Unreadable::Dangling)
            ));
        }
    }

    /// A staged type reads as the type it refines: a stage is the recursion
    /// typing's own, and its components are the refined type's.
    #[test]
    fn a_staged_type_reads_as_the_type_it_refines()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let product = arena.value_type_product(&[integer, string]);
        let staged = arena.value_type_staged(
            product,
            gandr_kernel_term::Stage::At(gandr_kernel_term::StageId::from(0_usize)),
        );
        let source = CoreSource::new(&arena, &[]);
        assert!(matches!(
            source.read(CoreNode::ValueType(staged)),
            Former::Product(arity) if usize::from(arity) == 2
        ));
        assert_eq!(
            source.component(CoreNode::ValueType(staged), Component::from(1_usize)),
            Some(CoreNode::ValueType(string))
        );
    }

    /// A product's, a sum's and a record's components read in order, a
    /// record's fields and labels in label order whatever order they were
    /// given in, and nothing reads past the arity or below another former.
    #[test]
    fn components_read_in_order_and_stop_at_the_arity()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let unit = arena.value_type_product(&[]);
        let product = arena.value_type_product(&[integer, string, unit]);
        let sum = arena.value_type_sum(&[string, integer]);
        let returns = arena.comp_type_returner(product);
        let record_type = arena.value_type_record(BTreeMap::from([
            (FieldLabel::from(String::from("b")), string),
            (FieldLabel::from(String::from("a")), integer),
        ]));
        let first = arena.value_unit();
        let second = arena.value_tuple(&[first]);
        let record = arena.value_record(BTreeMap::from([
            (FieldLabel::from(String::from("y")), second),
            (FieldLabel::from(String::from("x")), first),
        ]));
        let source = CoreSource::new(&arena, &[]);
        let read = |node: ValueTypeId, index: usize| {
            source.component(CoreNode::ValueType(node), Component::from(index))
        };
        let labels = |node: CoreNode| {
            [0_usize, 1, 2].map(|index| {
                source
                    .label(node, Component::from(index))
                    .map(|label| String::from(label.as_ref()))
            })
        };
        assert!(matches!(
            source.read(CoreNode::ValueType(product)),
            Former::Product(arity) if usize::from(arity) == 3
        ));
        assert_eq!(
            [
                read(product, 0),
                read(product, 1),
                read(product, 2),
                read(product, 3)
            ],
            [
                Some(CoreNode::ValueType(integer)),
                Some(CoreNode::ValueType(string)),
                Some(CoreNode::ValueType(unit)),
                None
            ]
        );
        assert_eq!([read(sum, 0), read(sum, 1), read(sum, 2)], [
            Some(CoreNode::ValueType(string)),
            Some(CoreNode::ValueType(integer)),
            None
        ]);
        assert_eq!(
            [
                read(record_type, 0),
                read(record_type, 1),
                read(record_type, 2)
            ],
            [
                Some(CoreNode::ValueType(integer)),
                Some(CoreNode::ValueType(string)),
                None
            ],
            "a record type's fields read in label order"
        );
        assert_eq!(
            [0_usize, 1, 2]
                .map(|index| source.component(CoreNode::Value(record), Component::from(index))),
            [
                Some(CoreNode::Value(first)),
                Some(CoreNode::Value(second)),
                None
            ],
            "a record's fields read in label order"
        );
        assert_eq!(
            labels(CoreNode::ValueType(record_type)),
            [Some(String::from("a")), Some(String::from("b")), None],
            "a record type's labels read in label order and stop at its fields"
        );
        assert_eq!(
            labels(CoreNode::Value(record)),
            [Some(String::from("x")), Some(String::from("y")), None],
            "a record's labels read in label order and stop at its fields"
        );
        assert_eq!(
            labels(CoreNode::ValueType(product)),
            [None, None, None],
            "a product has no labels"
        );
        assert_eq!(
            labels(CoreNode::Value(second)),
            [None, None, None],
            "a tuple has no labels"
        );
        assert_eq!(read(unit, 0), None, "the unit has no component");
        assert_eq!(read(integer, 0), None, "a base type has no component");
        assert_eq!(
            source.component(CoreNode::CompType(returns), Component::from(0_usize)),
            None,
            "a computation type has no component"
        );
    }

    /// Admission position, not the first available name, governs both named
    /// formers.
    #[test]
    fn names_use_admission_positions_and_refuse_the_exact_end()
    {
        let mut arena = CoreArena::new();
        let constant = arena.value_constant(ConstantIndex::from(1_usize));
        let abstract_type = arena.value_type_abstract(ConstantIndex::from(1_usize));
        let names = [Name::from("Other"), Name::from("Chosen")];
        let source = CoreSource::new(&arena, &names);
        assert!(
            matches!(source.read(CoreNode::Value(constant)), Former::Constant(name)
            if name.as_ref() == "Chosen")
        );
        assert!(
            matches!(source.read(CoreNode::ValueType(abstract_type)), Former::Abstract(name)
            if name.as_ref() == "Chosen")
        );
        let source = CoreSource::new(&arena, &names[.. 1]);
        assert!(matches!(
            source.read(CoreNode::Value(constant)),
            Former::Unreadable(Unreadable::Unnamed)
        ));
        assert!(matches!(
            source.read(CoreNode::ValueType(abstract_type)),
            Former::Unreadable(Unreadable::Unnamed)
        ));
    }

    /// A hole, a mark and the unknown type have no source spelling; their
    /// neighbours keep theirs.
    #[test]
    fn holes_marks_and_the_unknown_type_read_as_unreadable()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let hole = arena.value_hole(gandr_core_term::hole::HoleId::from(0_u32));
        let marked = arena.value_mark(gandr_core_term::hole::MarkIndex::from(0_u32), unit);
        let returned = arena.computation_return(unit);
        let computation_hole = arena.computation_hole(gandr_core_term::hole::HoleId::from(1_u32));
        let computation_mark =
            arena.computation_mark(gandr_core_term::hole::MarkIndex::from(1_u32), returned);
        let unknown = arena.value_type_unknown();
        let unknown_computation = arena.comp_type_unknown();
        let source = CoreSource::new(&arena, &[]);
        for (node, reason) in [
            (CoreNode::Value(hole), Unreadable::Hole),
            (CoreNode::Value(marked), Unreadable::Mark),
            (CoreNode::Computation(computation_hole), Unreadable::Hole),
            (CoreNode::Computation(computation_mark), Unreadable::Mark),
            (CoreNode::ValueType(unknown), Unreadable::UnknownType),
            (
                CoreNode::CompType(unknown_computation),
                Unreadable::UnknownType,
            ),
        ] {
            assert!(
                matches!(source.read(node), Former::Unreadable(read) if read == reason),
                "{node:?}"
            );
        }
        assert!(matches!(source.read(CoreNode::Value(unit)), Former::Unit));
        assert!(matches!(
            source.read(CoreNode::Computation(returned)),
            Former::Return(value) if value == CoreNode::Value(unit)
        ));
    }

    /// An elaborated body reads as the body it was elaborated from through
    /// its restoration, and as the bind the elaboration minted without it.
    #[test]
    fn a_restored_elaboration_reads_as_written()
    {
        let mut arena = CoreArena::new();
        let constant = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(constant);
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let inner = arena.computation_application(forced, argument);
        let nested = arena.value_nested(inner);
        let outer = arena.computation_application(forced, nested);
        let lambda = arena.computation_lambda(outer);
        let subject = arena.value_thunk(lambda);
        let (mut carried, mut binds) = (Vec::new(), Vec::new());
        let elaborated = gandr_core_term::elaborate_nested_traced(
            &mut arena,
            subject,
            &BTreeMap::from([(nested, gandr_core_term::Nesting::Run)]),
            &mut carried,
            &mut binds,
        )
        .expect("the run stands in the call's values");
        let Some(&super::Value::Thunk(body)) = arena.value(elaborated)
        else {
            panic!("the elaborated subject stays a thunk");
        };
        let names = [Name::from("f")];
        let restoration = super::Restoration::of(&carried);
        let print = |source: &CoreSource<'_>| {
            crate::present_computation(
                source,
                CoreNode::Computation(body),
                crate::PageWidth::from(100_u32),
                crate::Form::Explicit,
            )
            .expect("the body lays out")
            .to_string()
        };
        assert_eq!(
            print(&CoreSource::new(&arena, &names)),
            "fn (a) { run b <- f(a) ; f(b) }",
            "unrestored, the minted bind is read"
        );
        assert_eq!(
            print(&CoreSource::new(&arena, &names).restoring(&restoration)),
            "fn (a) { f(f(a)) }",
            "restored, the run is read as written"
        );
        assert!(matches!(
            CoreSource::new(&arena, &names)
                .restoring(&restoration)
                .read(CoreNode::Value(nested)),
            Former::Nested(computation) if computation == CoreNode::Computation(inner)
        ));
    }

    /// A constructor of a family applied to arguments carries its value type
    /// as its classifier, so the printer can annotate it; one of a family with
    /// no parameters carries none.
    #[test]
    fn only_a_parameterised_constructor_carries_its_classifier()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let bare = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let applied = arena.value_type_data(ConstantIndex::from(0_usize), Vec::from([unit]));
        let tag = gandr_kernel_term::ConstructorTag::from(0_usize);
        let of_bare = arena.value_constructor(bare, tag, Vec::new());
        let of_applied = arena.value_constructor(applied, tag, Vec::new());
        let source = CoreSource::new(&arena, &[]);
        assert!(
            matches!(
                source.read(CoreNode::Value(of_applied)),
                Former::Constructor { classifier: Some(held), .. } if held == CoreNode::ValueType(applied)
            ),
            "a parameterised constructor carries its family's application"
        );
        assert!(
            matches!(source.read(CoreNode::Value(of_bare)), Former::Constructor {
                classifier: None,
                ..
            }),
            "a constructor of a family without parameters carries nothing"
        );
    }
}
