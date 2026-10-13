//! The core arena as a [`Source`]: checked types, the values evaluation and
//! readback leave in the arena, and bodies, an elaborated one read as written
//! through its [`Restoration`].

use alloc::collections::BTreeMap;

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
use gandr_kernel_term::ConstantIndex;

use crate::former::Arity;
use crate::former::Component;
use crate::former::Former;
use crate::former::Name;
use crate::former::Source;

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
                | Carried::Value(original, rebuilt) => {
                    (CoreNode::Value(original), CoreNode::Value(rebuilt))
                },
                | Carried::Computation(original, rebuilt) => (
                    CoreNode::Computation(original),
                    CoreNode::Computation(rebuilt),
                ),
                | Carried::ValueType(original, rebuilt) => {
                    (CoreNode::ValueType(original), CoreNode::ValueType(rebuilt))
                },
                | Carried::CompType(original, rebuilt) => {
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

/// A core arena read through the names of the constants it mentions.
///
/// A core node names a constant or an abstract type by its admission
/// position; `names` spells position `i` as its `i`-th entry. A position past
/// the table reads as [`Former::Unreadable`]. A source restoring an
/// elaboration reads every node the elaboration rebuilt as its original.
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

    /// The name at admission position `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `wrap` over the table's entry for `constant`;
    ///   [`Former::Unreadable`] past the table.
    /// - provides: the constant and abstract-type readings.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the constant and abstract-type wrappers at a live
    ///   admission position and the exact table end expose shifted names or a
    ///   missing-entry fallback. Arbitrary callback behavior is excluded.
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    #[spec(ensures: |ret| usize::from(constant) < self.names.len()
        || matches!(ret, Former::Unreadable)
    )]
    fn named(
        &self,
        constant: ConstantIndex,
        wrap: fn(Name<'arena>) -> Former<'arena, CoreNode>,
    ) -> Former<'arena, CoreNode>
    {
        self.names
            .get(usize::from(constant))
            .map_or(Former::Unreadable, |name| wrap(*name))
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
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    /// - witness: `goldens::tests::native_paths_preserve_ordered_endpoints_and_maps`
    #[spec(ensures: |ret| match (self.arena.value(id), ret) {
        | (Some(&Value::ListCons(head, tail)), Former::ListCons(h, t)) => h == CoreNode::Value(head) && t == CoreNode::Value(tail),
        | (Some(&Value::Primitive { primitive, .. }), Former::Constant(name)) => name.as_ref() == primitive.name().as_ref(),
        | (Some(&Value::PathRefl(code)), Former::PathRefl(actual)) => actual == CoreNode::Value(code),
        | (Some(&Value::Here(point)), Former::Here(actual)) => actual == CoreNode::Value(point),
        | (Some(&Value::Funext(left, right)), Former::Funext(actual_left, actual_right)) =>
            actual_left == CoreNode::Value(left) && actual_right == CoreNode::Value(right),
        | (Some(&Value::Equiv(forward, backward)), Former::Equiv(actual_forward, actual_backward))
        | (Some(&Value::PathEquiv { forward, backward, .. }), Former::PathEquiv(actual_forward, actual_backward)) =>
            actual_forward == CoreNode::Value(forward) && actual_backward == CoreNode::Value(backward),
        | (Some(&Value::Ua { stratum, ref sides, forward, backward }), Former::Ua { stratum: actual_stratum, source, target, forward: actual_forward, backward: actual_backward }) =>
            stratum == actual_stratum && source.as_ref() == sides.source.name.as_ref() && target.as_ref() == sides.target.name.as_ref()
                && actual_forward == CoreNode::Value(forward) && actual_backward == CoreNode::Value(backward),
        | (Some(&Value::Variable { zone, index }), Former::Variable { zone: actual_zone, index: actual_index }) =>
            zone == actual_zone && index == actual_index,
        | (Some(&Value::Constant(index)), Former::Constant(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&Value::Constant(index)), Former::Unreadable) => usize::from(index) >= self.names.len(),
        (Some(&Value::Constructor { .. } | &Value::Hole(_) | &Value::Mark { .. } | &Value::Returned(_)) | None,
Former::Unreadable) | (Some(&Value::Reify(_)), Former::Reify) | (Some(&Value::ListNil), Former::ListNil) |
(Some(&Value::Lift { .. }), Former::ValueLift) => true,
        | (Some(&Value::Thunk(body)), Former::Thunk(actual))
        | (Some(&Value::Nested(body)), Former::Nested(actual))
        | (Some(&Value::Run(body)), Former::Run(actual)) => actual == CoreNode::Computation(body),
        | (Some(&Value::Record(ref fields)), Former::Unreadable) => fields.is_empty(),
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
            return Former::Unreadable;
        };
        match *value {
            // The source grammar has no native data reader. A hole or a mark
            // is displayed by the session, not spelled here, a compound
            // endpoint has no former of its own, and the surface writes no
            // empty record: `#{}` is the unit. Element identity is `here`,
            // function extensionality `funext`, universe equivalence `equiv`
            // and univalence at a stratum `ua[n, k]`.
            | Value::Constructor { .. }
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::Returned(_) => Former::Unreadable,
            | Value::Here(point) => Former::Here(CoreNode::Value(point)),
            | Value::Nested(body) => Former::Nested(CoreNode::Computation(body)),
            | Value::Run(body) => Former::Run(CoreNode::Computation(body)),
            | Value::Funext(left, right) => {
                Former::Funext(CoreNode::Value(left), CoreNode::Value(right))
            },
            | Value::Equiv(forward, backward) => {
                Former::Equiv(CoreNode::Value(forward), CoreNode::Value(backward))
            },
            | Value::Ua {
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
            | Value::Record(ref fields) if fields.is_empty() => Former::Unreadable,
            | Value::Record(ref fields) => Former::Record(Arity::from(fields.len())),
            | Value::Reify(_) => Former::Reify,
            | Value::Primitive { primitive, .. } => {
                Former::Constant(Name::from(<&'static str>::from(primitive.name())))
            },
            | Value::PathRefl(code) => Former::PathRefl(CoreNode::Value(code)),
            | Value::PathProduct(first, second) => {
                Former::PathProduct(CoreNode::Value(first), CoreNode::Value(second))
            },
            | Value::PathEquiv {
                forward, backward, ..
            } => Former::PathEquiv(CoreNode::Value(forward), CoreNode::Value(backward)),
            | Value::Variable { zone, index } => Former::Variable { zone, index },
            | Value::Constant(constant) => self.named(constant, Former::Constant),
            | Value::ListNil => Former::ListNil,
            | Value::ListCons(head, tail) => {
                Former::ListCons(CoreNode::Value(head), CoreNode::Value(tail))
            },
            | Value::Literal(ref literal) => Former::Literal(literal),
            | Value::Tuple(ref components) if components.is_empty() => Former::Unit,
            | Value::Tuple(ref components) => Former::Tuple(Arity::from(components.len())),
            | Value::Injection(summand, body) => {
                Former::Injection(Component::from(usize::from(summand)), CoreNode::Value(body))
            },
            | Value::Thunk(body) => Former::Thunk(CoreNode::Computation(body)),
            | Value::Lift { .. } => Former::ValueLift,
            | Value::Quote(quoted) => Former::Quote(CoreNode::ValueType(quoted)),
            | Value::QuoteComputation(quoted) => {
                Former::QuoteComputation(CoreNode::CompType(quoted))
            },
            | Value::StaticLambda(body) => Former::StaticLambda(CoreNode::Value(body)),
            | Value::StaticApplication(operator, argument) => {
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
    #[spec(ensures: |ret| match (self.arena.value_type(id), ret) {
        | (Some(&ValueType::Stack { input, output }), Former::Stack(a, b)) => a == CoreNode::CompType(input) && b == CoreNode::CompType(output),
        | (Some(&ValueType::PathUniverse(source, target)), Former::PathUniverse(actual_source, actual_target)) => actual_source == CoreNode::Value(source) && actual_target == CoreNode::Value(target),
        (Some(&ValueType::Data { .. } | &ValueType::Unknown | &ValueType::Path { .. }) | None,
Former::Unreadable) |
(Some(&ValueType::Lift { .. }), Former::TypeLift) => true,
        | (Some(&ValueType::Record(ref fields)), Former::Unreadable) => fields.is_empty(),
        | (Some(&ValueType::Record(ref fields)), Former::RecordType(arity)) => !fields.is_empty() && usize::from(arity) == fields.len(),
        | (Some(&ValueType::Base(base)), Former::BaseType(actual)) => base == actual,
        | (Some(&ValueType::Product(ref parts)), Former::Product(arity))
        | (Some(&ValueType::Sum(ref parts)), Former::Sum(arity)) => usize::from(arity) == parts.len(),
        | (Some(&ValueType::List(element)), Former::List(actual)) => actual == CoreNode::ValueType(element),
        | (Some(&ValueType::Thunk(body)), Former::ThunkType(actual)) => actual == CoreNode::CompType(body),
        | (Some(&ValueType::Universe { sort, ref level }), Former::Universe { sort: actual_sort, level: actual_level }) =>
            sort == actual_sort && core::ptr::eq(core::ptr::from_ref(level), core::ptr::from_ref(actual_level)),
        | (Some(&ValueType::Element { code, .. }), Former::Element(actual)) => actual == CoreNode::Value(code),
        | (Some(&ValueType::Abstract(index)), Former::Abstract(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&ValueType::Abstract(index)), Former::Unreadable) => usize::from(index) >= self.names.len(),
        | (Some(&ValueType::StaticPi { domain, codomain }), Former::StaticPi { domain: actual_domain, codomain: actual_codomain }) =>
            actual_domain == CoreNode::ValueType(domain) && actual_codomain == CoreNode::ValueType(codomain),
        | (Some(&ValueType::Session(ref session)), Former::Session { protocol, state, payloads }) =>
            core::ptr::eq(core::ptr::from_ref(protocol), core::ptr::from_ref(session.protocol())) && state == session.state() && usize::from(payloads) == session.payloads().len(),
        | (Some(&ValueType::Capability { grade, region, .. }), Former::Capability { grade: actual_grade, region: actual_region, .. }) =>
            grade == actual_grade && region == actual_region,
        | _ => false,
    })]
    fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Former<'arena, CoreNode>
    {
        let Some(value_type) = self.arena.value_type(id)
        else {
            return Former::Unreadable;
        };
        match *value_type {
            // A native data classifier and a path type have no spelling in the
            // source grammar, and the surface writes no empty record type:
            // `#{}` is `Unit`.
            | ValueType::Data { .. } | ValueType::Unknown | ValueType::Path { .. } => {
                Former::Unreadable
            },
            | ValueType::Record(ref fields) if fields.is_empty() => Former::Unreadable,
            | ValueType::Record(ref fields) => Former::RecordType(Arity::from(fields.len())),
            | ValueType::Product(ref parts) => Former::Product(Arity::from(parts.len())),
            | ValueType::Sum(ref parts) => Former::Sum(Arity::from(parts.len())),
            | ValueType::Stack { input, output } => {
                Former::Stack(CoreNode::CompType(input), CoreNode::CompType(output))
            },
            | ValueType::PathUniverse(source, target) => {
                Former::PathUniverse(CoreNode::Value(source), CoreNode::Value(target))
            },
            | ValueType::Base(base) => Former::BaseType(base),
            | ValueType::List(element) => Former::List(CoreNode::ValueType(element)),
            | ValueType::Thunk(body) => Former::ThunkType(CoreNode::CompType(body)),
            | ValueType::Universe { sort, ref level } => Former::Universe { sort, level },
            | ValueType::Lift { .. } => Former::TypeLift,
            | ValueType::Element { code, .. } => Former::Element(CoreNode::Value(code)),
            | ValueType::Abstract(atom) => self.named(atom, Former::Abstract),
            | ValueType::StaticPi { domain, codomain } => Former::StaticPi {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::ValueType(codomain),
            },
            | ValueType::Session(ref session) => Former::Session {
                protocol: session.protocol(),
                state: session.state(),
                payloads: Arity::from(session.payloads().len()),
            },
            | ValueType::Capability {
                ref authority,
                grade,
                region,
            } => Former::Capability {
                authority,
                grade,
                region,
            },
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
        | (Some(&CompType::Unknown) | None, Former::Unreadable) => true,
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
            return Former::Unreadable;
        };
        match *comp_type {
            | CompType::Unknown => Former::Unreadable,
            | CompType::With(first, second) => {
                Former::With(CoreNode::CompType(first), CoreNode::CompType(second))
            },
            | CompType::Returner {
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
            | CompType::Arrow { domain, codomain } => Former::Arrow {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::CompType(codomain),
            },
            | CompType::Pi { domain, codomain } => Former::Pi {
                domain: CoreNode::ValueType(domain),
                codomain: CoreNode::CompType(codomain),
            },
            | CompType::Element { code, .. } => Former::ComputationElement(CoreNode::Value(code)),
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
    /// - ensures: as [`Source::read`], of the node `node` restores to; a
    ///   return, a bind, a force, an application and a lambda read as their own
    ///   formers over their children, every other held computation but a hole
    ///   or a mark as [`Former::Computation`], and a hole, a mark or a missing
    ///   handle as unreadable.
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
        | CoreNode::Computation(id) => match (self.arena.computation(id), ret) {
            | (Some(&(Computation::Hole(_) | Computation::Mark { .. })) | None, Former::Unreadable) => true,
            | (Some(&Computation::Return(value)), Former::Return(actual))
            | (Some(&Computation::Force(value)), Former::Force(actual)) => actual == CoreNode::Value(value),
            | (Some(&Computation::Lambda(body)), Former::Lambda(actual)) => actual == CoreNode::Computation(body),
            | (Some(&Computation::Bind(bound, rest)), Former::Bind(actual_bound, actual_rest)) =>
                actual_bound == CoreNode::Computation(bound) && actual_rest == CoreNode::Computation(rest),
            | (Some(&Computation::Application(function, argument)), Former::Application(actual_function, actual_argument)) =>
                actual_function == CoreNode::Computation(function) && actual_argument == CoreNode::Value(argument),
            | (Some(&(Computation::Return(_) | Computation::Force(_) | Computation::Lambda(_) | Computation::Bind(..)
                | Computation::Application(..) | Computation::Hole(_) | Computation::Mark { .. })), _) => false,
            | (Some(_), Former::Computation) => true,
            | _ => false,
        },
        | CoreNode::Value(id) if self.arena.value(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::ValueType(id) if self.arena.value_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::CompType(id) if self.arena.comp_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::Value(_) => matches!(ret, Former::Variable { .. } | Former::Constant(_) | Former::Unit
            | Former::Literal(_) | Former::Tuple(_) | Former::Record(_) | Former::Injection(..) | Former::Thunk(_)
            | Former::ValueLift | Former::Reify | Former::ListNil | Former::ListCons(..)
            | Former::Quote(_) | Former::QuoteComputation(_) | Former::StaticLambda(_) | Former::StaticApplication(..)
            | Former::PathRefl(_) | Former::PathEquiv(..) | Former::PathProduct(..) | Former::Here(_) | Former::Funext(..) | Former::Equiv(..)
            | Former::Ua { .. } | Former::Nested(_) | Former::Run(_) | Former::Unreadable),
        | CoreNode::ValueType(_) => matches!(ret, Former::BaseType(_) | Former::Product(_) | Former::RecordType(_)
            | Former::Stack(..) | Former::List(_)
            | Former::Sum(_) | Former::ThunkType(_) | Former::Universe { .. } | Former::TypeLift
            | Former::Element(_) | Former::Abstract(_) | Former::StaticPi { .. } | Former::Capability { .. } | Former::PathUniverse(..) | Former::Session { .. } | Former::Unreadable),
        | CoreNode::CompType(_) => matches!(ret, Former::Returner(_) | Former::EffectfulReturner { .. } | Former::Arrow { .. } | Former::Pi { .. }
            | Former::With(..) | Former::ComputationElement(_) | Former::Unreadable),
    })]
    #[inline]
    fn read(
        &self,
        node: CoreNode,
    ) -> Former<'_, CoreNode>
    {
        match self.restoration.restored(node) {
            | CoreNode::Value(id) => self.value(id),
            | CoreNode::Computation(id) => match self.arena.computation(id) {
                | Some(&Computation::Return(value)) => Former::Return(CoreNode::Value(value)),
                | Some(&Computation::Bind(bound, rest)) => {
                    Former::Bind(CoreNode::Computation(bound), CoreNode::Computation(rest))
                },
                | Some(&Computation::Force(thunk)) => Former::Force(CoreNode::Value(thunk)),
                | Some(&Computation::Application(function, argument)) => {
                    Former::Application(CoreNode::Computation(function), CoreNode::Value(argument))
                },
                | Some(&Computation::Lambda(body)) => Former::Lambda(CoreNode::Computation(body)),
                | Some(
                    &(Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Primitive { .. }
                    | Computation::DataCase { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Scope { .. }
                    | Computation::Resume(..)
                    | Computation::Split { .. }
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Fixpoint { .. }
                    | Computation::ListFold { .. }
                    | Computation::Case { .. }
                    | Computation::Session(_)),
                ) => Former::Computation,
                | Some(&(Computation::Hole(_) | Computation::Mark { .. })) | None => {
                    Former::Unreadable
                },
            },
            | CoreNode::ValueType(id) => self.value_type(id),
            | CoreNode::CompType(id) => self.comp_type(id),
        }
    }

    /// The handle of component `index` of the product, the sum, the tuple,
    /// the record or the record type `node` names in the arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the node `node` restores to, the value type at `index`
    ///   among a held product's, sum's or record type's components, and the
    ///   value at `index` among a held tuple's or record's, a record's fields
    ///   in label order; none for an index past them, another former, another
    ///   family or a missing handle.
    /// - provides: the printer's reading of an n-ary former.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a record's field is reached by counting through its
    ///   label-ordered map, linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden braces read every component of products
    ///   and sums of arity one to three, of tuples of arity one to three and of
    ///   records of two fields, in order; a direct read past the arity and of a
    ///   non-product observes the absence.
    /// - witness: `goldens::tests::n_ary_products_and_sums_spell_between_their_braces`
    /// - witness: `goldens::tests::n_ary_tuples_and_injections_spell_between_their_braces`
    /// - witness: `goldens::tests::records_spell_their_fields_in_label_order`
    /// - witness: `core_source::tests::components_read_in_order_and_stop_at_the_arity`
    #[spec(captures: restored = self.restoration.restored(node), ensures: |ret| ret == match restored {
        | CoreNode::ValueType(id) => match self.arena.value_type(id) {
            | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => parts.get(usize::from(index)).map(|&part| CoreNode::ValueType(part)),
            | Some(&ValueType::Session(ref session)) => session.payloads().get(usize::from(index)).map(|&payload| CoreNode::ValueType(payload)),
            | Some(&ValueType::Record(ref fields)) => fields.values().nth(usize::from(index)).map(|&field| CoreNode::ValueType(field)),
            | _ => None,
        },
        | CoreNode::Value(id) => match self.arena.value(id) {
            | Some(&Value::Tuple(ref components)) => components.get(usize::from(index)).map(|&component| CoreNode::Value(component)),
            | Some(&Value::Record(ref fields)) => fields.values().nth(usize::from(index)).map(|&field| CoreNode::Value(field)),
            | _ => None,
        },
        | CoreNode::Computation(_) | CoreNode::CompType(_) => None,
    })]
    #[inline]
    fn component(
        &self,
        node: CoreNode,
        index: Component,
    ) -> Option<CoreNode>
    {
        match self.restoration.restored(node) {
            | CoreNode::ValueType(id) => match *self.arena.value_type(id)? {
                | ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts
                    .get(usize::from(index))
                    .map(|&part| CoreNode::ValueType(part)),
                | ValueType::Record(ref fields) => fields
                    .values()
                    .nth(usize::from(index))
                    .map(|&field| CoreNode::ValueType(field)),
                | ValueType::Session(ref session) => session
                    .payloads()
                    .get(usize::from(index))
                    .map(|&payload| CoreNode::ValueType(payload)),
                | _ => None,
            },
            | CoreNode::Value(id) => match *self.arena.value(id)? {
                | Value::Tuple(ref components) => components
                    .get(usize::from(index))
                    .map(|&component| CoreNode::Value(component)),
                | Value::Record(ref fields) => fields
                    .values()
                    .nth(usize::from(index))
                    .map(|&field| CoreNode::Value(field)),
                | _ => None,
            },
            | CoreNode::Computation(_) | CoreNode::CompType(_) => None,
        }
    }

    /// The label of field `index` of the record or the record type `node`
    /// names in the arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the node `node` restores to, the label at `index` among a
    ///   held record's or record type's fields, in label order; none for an
    ///   index past them, another former, another family or a missing handle.
    /// - provides: the printer's reading of a record's labels.
    /// - fails: never.
    /// - panics: none.
    /// - intension: as [`Self::component`], linear in the fields before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — records and record types of two fields written out of
    ///   label order spell each field under its own label; a direct read past
    ///   the fields and of a tuple observes the absence.
    /// - witness: `goldens::tests::records_spell_their_fields_in_label_order`
    /// - witness: `core_source::tests::components_read_in_order_and_stop_at_the_arity`
    #[spec(captures: restored = self.restoration.restored(node), ensures: |ret| ret.as_ref().map(|name| -> &str { name.as_ref() }) == match restored {
        | CoreNode::ValueType(id) => match self.arena.value_type(id) {
            | Some(&ValueType::Record(ref fields)) => fields.keys().nth(usize::from(index)).map(AsRef::as_ref),
            | _ => None,
        },
        | CoreNode::Value(id) => match self.arena.value(id) {
            | Some(&Value::Record(ref fields)) => fields.keys().nth(usize::from(index)).map(AsRef::as_ref),
            | _ => None,
        },
        | CoreNode::Computation(_) | CoreNode::CompType(_) => None,
    })]
    #[inline]
    fn label(
        &self,
        node: CoreNode,
        index: Component,
    ) -> Option<Name<'_>>
    {
        let label = match self.restoration.restored(node) {
            | CoreNode::ValueType(id) => match *self.arena.value_type(id)? {
                | ValueType::Record(ref fields) => fields.keys().nth(usize::from(index)),
                | _ => None,
            },
            | CoreNode::Value(id) => match *self.arena.value(id)? {
                | Value::Record(ref fields) => fields.keys().nth(usize::from(index)),
                | _ => None,
            },
            | CoreNode::Computation(_) | CoreNode::CompType(_) => None,
        }?;
        Some(Name::from(label.as_ref()))
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
            assert!(matches!(source.read(node), Former::Unreadable));
        }
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
            Former::Unreadable
        ));
        assert!(matches!(
            source.read(CoreNode::ValueType(abstract_type)),
            Former::Unreadable
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
        for node in [
            CoreNode::Value(hole),
            CoreNode::Value(marked),
            CoreNode::Computation(computation_hole),
            CoreNode::Computation(computation_mark),
            CoreNode::ValueType(unknown),
            CoreNode::CompType(unknown_computation),
        ] {
            assert!(matches!(source.read(node), Former::Unreadable), "{node:?}");
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
}
