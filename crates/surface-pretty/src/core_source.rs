//! The core arena as a [`Source`]: checked types, and the values evaluation
//! and readback leave in the arena.

use anodized::spec;
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

/// A core arena read through the names of the constants it mentions.
///
/// A core node names a constant or an abstract type by its admission
/// position; `names` spells position `i` as its `i`-th entry. A position past
/// the table reads as [`Former::Unreadable`].
///
/// # Specification
/// - requires: `names` is indexed by admission position.
/// - ensures: arena nodes retain their formers; missing naming-table entries
///   read as unreadable.
/// - provides: the printer's input over checked types and readback values.
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
#[derive(Clone, Copy, Debug)]
pub struct CoreSource<'arena>
{
    /// The arena whose nodes are read.
    arena: &'arena CoreArena,
    /// The constants' names, by admission position.
    names: &'arena [Name<'arena>],
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
        Self { arena, names }
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
        | (Some(&Value::PathEquiv { forward, backward, .. }), Former::PathEquiv(actual_forward, actual_backward)) => actual_forward == CoreNode::Value(forward) && actual_backward == CoreNode::Value(backward),
        | (Some(&Value::Variable { zone, index }), Former::Variable { zone: actual_zone, index: actual_index }) =>
            zone == actual_zone && index == actual_index,
        | (Some(&Value::Constant(index)), Former::Constant(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&Value::Constant(index)), Former::Unreadable) => usize::from(index) >= self.names.len(),
        (Some(&Value::Constructor { .. } | &Value::Record(_) | &Value::Hole(_) | &Value::Mark { .. } | &Value::Here(_) | &Value::Returned(_)) | None,
Former::Unreadable) | (Some(&Value::Reify(_)), Former::Reify) | (Some(&Value::ListNil), Former::ListNil) |
(Some(&Value::Thunk(_)), Former::Thunk) |
(Some(&Value::Lift { .. }), Former::ValueLift) => true,
        | (Some(&Value::Literal(ref literal)), Former::Literal(actual)) =>
            core::ptr::eq(core::ptr::from_ref(literal), core::ptr::from_ref(actual)),
        | (Some(&Value::Tuple(ref components)), Former::Unit) => components.is_empty(),
        | (Some(&Value::Tuple(ref components)), Former::Tuple(arity)) => !components.is_empty() && usize::from(arity) == components.len(),
        | (Some(&Value::PathProduct(first, second)), Former::PathProduct(actual_first, actual_second)) =>
            actual_first == CoreNode::Value(first) && actual_second == CoreNode::Value(second),
        | (Some(&Value::Injection(summand, body)), Former::Injection(actual_side, actual_body)) =>
            summand == actual_side.into() && actual_body == CoreNode::Value(body),
        | (Some(&Value::Injection(summand, _)), Former::Unreadable) => usize::from(summand) > 1,
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
            // The source grammar has no native data or record reader, a hole
            // or a mark is displayed by the session, not spelled here, and
            // reflexivity and a compound endpoint have no former of their own.
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::Here(_)
            | Value::Returned(_) => Former::Unreadable,
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
            // The surface writes only the first two summands.
            | Value::Injection(summand, body) => match gandr_kernel_term::Side::try_from(summand) {
                | Ok(side) => Former::Injection(side, CoreNode::Value(body)),
                | Err(_) => Former::Unreadable,
            },
            | Value::Thunk(_) => Former::Thunk,
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
    #[spec(ensures: |ret| match (self.arena.value_type(id), ret) {
        | (Some(&ValueType::Stack { input, output }), Former::Stack(a, b)) => a == CoreNode::CompType(input) && b == CoreNode::CompType(output),
        | (Some(&ValueType::PathUniverse(source, target)), Former::PathUniverse(actual_source, actual_target)) => actual_source == CoreNode::Value(source) && actual_target == CoreNode::Value(target),
        (Some(&ValueType::Data { .. } | &ValueType::Record(_) | &ValueType::Unknown | &ValueType::Path { .. }) | None,
Former::Unreadable) |
(Some(&ValueType::Lift { .. }), Former::TypeLift) => true,
        | (Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)), Former::Unreadable) => parts.len() == 1,
        | (Some(&ValueType::Base(base)), Former::BaseType(actual)) => base == actual,
        | (Some(&ValueType::Product(ref parts)), Former::Product(arity))
        | (Some(&ValueType::Sum(ref parts)), Former::Sum(arity)) => parts.len() != 1 && usize::from(arity) == parts.len(),
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
            // These classifiers have no spelling in the source grammar.
            | ValueType::Data { .. } | ValueType::Record(_) | ValueType::Unknown => {
                Former::Unreadable
            },
            | ValueType::Path { .. } => Former::Unreadable,
            // The 1-ary product and sum have no spelling yet.
            | ValueType::Product(ref parts) | ValueType::Sum(ref parts) if parts.len() == 1 => {
                Former::Unreadable
            },
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
    /// - ensures: as [`Source::read`]; every held computation but a hole or a
    ///   mark reads as [`Former::Computation`], and a hole, a mark or a missing
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
    #[spec(ensures: |ret| match node {
        | CoreNode::Computation(id) => match self.arena.computation(id) {
            | Some(&(Computation::Hole(_) | Computation::Mark { .. })) | None => matches!(ret, Former::Unreadable),
            | Some(_) => matches!(ret, Former::Computation),
        },
        | CoreNode::Value(id) if self.arena.value(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::ValueType(id) if self.arena.value_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::CompType(id) if self.arena.comp_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::Value(_) => matches!(ret, Former::Variable { .. } | Former::Constant(_) | Former::Unit
            | Former::Literal(_) | Former::Tuple(_) | Former::Injection(..) | Former::Thunk | Former::ValueLift
            | Former::Reify | Former::ListNil | Former::ListCons(..)
            | Former::Quote(_) | Former::QuoteComputation(_) | Former::StaticLambda(_) | Former::StaticApplication(..)
            | Former::PathRefl(_) | Former::PathEquiv(..) | Former::PathProduct(..) | Former::Unreadable),
        | CoreNode::ValueType(_) => matches!(ret, Former::BaseType(_) | Former::Product(_)
            | Former::Stack(..) | Former::List(_)
            | Former::Sum(_) | Former::ThunkType(_) | Former::Universe { .. } | Former::TypeLift
            | Former::Element(_) | Former::Abstract(_) | Former::StaticPi { .. } | Former::PathUniverse(..) | Former::Unreadable),
        | CoreNode::CompType(_) => matches!(ret, Former::Returner(_) | Former::EffectfulReturner { .. } | Former::Arrow { .. } | Former::Pi { .. }
            | Former::With(..) | Former::ComputationElement(_) | Former::Unreadable),
    })]
    #[inline]
    fn read(
        &self,
        node: CoreNode,
    ) -> Former<'_, CoreNode>
    {
        match node {
            | CoreNode::Value(id) => self.value(id),
            | CoreNode::Computation(id) => match self.arena.computation(id) {
                | Some(
                    &(Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::Primitive { .. }
                    | Computation::DataCase { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Resume(..)
                    | Computation::Split { .. }
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Lambda(_)
                    | Computation::Fixpoint { .. }
                    | Computation::Application(..)
                    | Computation::Return(_)
                    | Computation::Bind(..)
                    | Computation::Force(_)
                    | Computation::ListFold { .. }
                    | Computation::Case { .. }),
                ) => Former::Computation,
                | Some(&(Computation::Hole(_) | Computation::Mark { .. })) | None => {
                    Former::Unreadable
                },
            },
            | CoreNode::ValueType(id) => self.value_type(id),
            | CoreNode::CompType(id) => self.comp_type(id),
        }
    }

    /// The handle of component `index` of the product, the sum or the tuple
    /// `node` names in the arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value type at `index` among a held product's or sum's
    ///   components, and the value at `index` among a held tuple's; none for an
    ///   index past them, another former, another family or a missing handle.
    /// - provides: the printer's reading of an n-ary product, sum or tuple.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the golden chains read every component of products
    ///   and sums of arity two and three, and of tuples of arity one to three,
    ///   in order; a direct read past the arity and of a non-product observes
    ///   the absence.
    /// - witness: `goldens::tests::n_ary_products_and_sums_spell_as_one_chain`
    /// - witness: `goldens::tests::n_ary_tuples_spell_with_their_commas`
    /// - witness: `core_source::tests::components_read_in_order_and_stop_at_the_arity`
    #[spec(ensures: |ret| ret == match node {
        | CoreNode::ValueType(id) => match self.arena.value_type(id) {
            | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => parts.get(usize::from(index)).map(|&part| CoreNode::ValueType(part)),
            | _ => None,
        },
        | CoreNode::Value(id) => match self.arena.value(id) {
            | Some(&Value::Tuple(ref components)) => components.get(usize::from(index)).map(|&component| CoreNode::Value(component)),
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
        match node {
            | CoreNode::ValueType(id) => match *self.arena.value_type(id)? {
                | ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts
                    .get(usize::from(index))
                    .map(|&part| CoreNode::ValueType(part)),
                | _ => None,
            },
            | CoreNode::Value(id) => match *self.arena.value(id)? {
                | Value::Tuple(ref components) => components
                    .get(usize::from(index))
                    .map(|&component| CoreNode::Value(component)),
                | _ => None,
            },
            | CoreNode::Computation(_) | CoreNode::CompType(_) => None,
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;

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
            Former::Computation
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

    /// A product's and a sum's components read in order, and nothing reads
    /// past the arity or below another former.
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
        let source = CoreSource::new(&arena, &[]);
        let read = |node: ValueTypeId, index: usize| {
            source.component(CoreNode::ValueType(node), Component::from(index))
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
            Former::Computation
        ));
    }
}
