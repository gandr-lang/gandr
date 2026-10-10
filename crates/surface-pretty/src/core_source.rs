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
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    #[spec(ensures: |ret| match (self.arena.value(id), ret) {
        | (Some(&Value::Variable { zone, index }), Former::Variable { zone: actual_zone, index: actual_index }) =>
            zone == actual_zone && index == actual_index,
        | (Some(&Value::Constant(index)), Former::Constant(name)) => self.names.get(usize::from(index))
            .is_some_and(|held| held.as_ref() == name.as_ref()),
        | (Some(&Value::Constant(index)), Former::Unreadable) => usize::from(index) >= self.names.len(),
        | (None, Former::Unreadable)
        | (Some(&Value::Unit), Former::Unit)
        | (Some(&Value::Thunk(_)), Former::Thunk)
        | (Some(&Value::Lift { .. }), Former::ValueLift) => true,
        | (Some(&Value::Literal(ref literal)), Former::Literal(actual)) =>
            core::ptr::eq(core::ptr::from_ref(literal), core::ptr::from_ref(actual)),
        | (Some(&Value::Pair(first, second)), Former::Pair(actual_first, actual_second)) =>
            actual_first == CoreNode::Value(first) && actual_second == CoreNode::Value(second),
        | (Some(&Value::Injection(side, body)), Former::Injection(actual_side, actual_body)) =>
            side == actual_side && actual_body == CoreNode::Value(body),
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
            | Value::Variable { zone, index } => Former::Variable { zone, index },
            | Value::Constant(constant) => self.named(constant, Former::Constant),
            | Value::Unit => Former::Unit,
            | Value::Literal(ref literal) => Former::Literal(literal),
            | Value::Pair(first, second) => {
                Former::Pair(CoreNode::Value(first), CoreNode::Value(second))
            },
            | Value::Injection(side, body) => Former::Injection(side, CoreNode::Value(body)),
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
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    #[spec(ensures: |ret| match (self.arena.value_type(id), ret) {
        | (None, Former::Unreadable)
        | (Some(&ValueType::Unit), Former::UnitType)
        | (Some(&ValueType::Lift { .. }), Former::TypeLift) => true,
        | (Some(&ValueType::Base(base)), Former::BaseType(actual)) => base == actual,
        | (Some(&ValueType::Product(first, second)), Former::Product(actual_first, actual_second))
        | (Some(&ValueType::Sum(first, second)), Former::Sum(actual_first, actual_second)) =>
            actual_first == CoreNode::ValueType(first) && actual_second == CoreNode::ValueType(second),
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
            | ValueType::Base(base) => Former::BaseType(base),
            | ValueType::Unit => Former::UnitType,
            | ValueType::Product(first, second) => {
                Former::Product(CoreNode::ValueType(first), CoreNode::ValueType(second))
            },
            | ValueType::Sum(first, second) => {
                Former::Sum(CoreNode::ValueType(first), CoreNode::ValueType(second))
            },
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
    #[spec(ensures: |ret| match (self.arena.comp_type(id), ret) {
        | (None, Former::Unreadable) => true,
        | (Some(&CompType::Returner(result)), Former::Returner(actual)) => actual == CoreNode::ValueType(result),
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
            | CompType::Returner(result) => Former::Returner(CoreNode::ValueType(result)),
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
    /// - ensures: as [`Source::read`]; every held computation reads as
    ///   [`Former::Computation`], and a missing handle as unreadable.
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
    /// - witness: `core_source::tests::names_use_admission_positions_and_refuse_the_exact_end`
    #[spec(ensures: |ret| match node {
        | CoreNode::Computation(id) => matches!((self.arena.computation(id).is_some(), ret),
            (true, Former::Computation) | (false, Former::Unreadable)),
        | CoreNode::Value(id) if self.arena.value(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::ValueType(id) if self.arena.value_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::CompType(id) if self.arena.comp_type(id).is_none() => matches!(ret, Former::Unreadable),
        | CoreNode::Value(_) => matches!(ret, Former::Variable { .. } | Former::Constant(_) | Former::Unit
            | Former::Literal(_) | Former::Pair(..) | Former::Injection(..) | Former::Thunk | Former::ValueLift
            | Former::Quote(_) | Former::QuoteComputation(_) | Former::StaticLambda(_) | Former::StaticApplication(..)
            | Former::Unreadable),
        | CoreNode::ValueType(_) => matches!(ret, Former::BaseType(_) | Former::UnitType | Former::Product(..)
            | Former::Sum(..) | Former::ThunkType(_) | Former::Universe { .. } | Former::TypeLift
            | Former::Element(_) | Former::Abstract(_) | Former::StaticPi { .. } | Former::Unreadable),
        | CoreNode::CompType(_) => matches!(ret, Former::Returner(_) | Former::Arrow { .. } | Former::Pi { .. }
            | Former::ComputationElement(_) | Former::Unreadable),
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
                    &(Computation::Lambda(_)
                    | Computation::Application(..)
                    | Computation::Return(_)
                    | Computation::Bind(..)
                    | Computation::Force(_)
                    | Computation::Case { .. }),
                ) => Former::Computation,
                | None => Former::Unreadable,
            },
            | CoreNode::ValueType(id) => self.value_type(id),
            | CoreNode::CompType(id) => self.comp_type(id),
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

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
        let pair = arena.value_pair(first, second);
        let computation = arena.computation_return(first);
        let value_type = arena.value_type_unit();
        let comp_type = arena.comp_type_returner(value_type);
        let source = CoreSource::new(&arena, &[]);
        assert!(
            matches!(source.read(CoreNode::Value(pair)), Former::Pair(left, right)
            if left == CoreNode::Value(first) && right == CoreNode::Value(second))
        );
        assert!(matches!(
            source.read(CoreNode::Computation(computation)),
            Former::Computation
        ));
        assert!(matches!(
            source.read(CoreNode::ValueType(value_type)),
            Former::UnitType
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
}
