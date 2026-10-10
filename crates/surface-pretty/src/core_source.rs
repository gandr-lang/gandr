//! The core arena as a [`Source`]: checked types, and the values evaluation
//! and readback leave in the arena.

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
/// - ensures: every node of `arena` reads as its own former.
/// - provides: the printer's input over checked types and readback values.
/// - panics: none.
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
            | Value::PathRefl(code) => Former::PathRefl(CoreNode::Value(code)),
            | Value::PathProduct(first, second) => {
                Former::PathProduct(CoreNode::Value(first), CoreNode::Value(second))
            },
            | Value::PathEquiv {
                forward, backward, ..
            } => Former::PathEquiv(CoreNode::Value(forward), CoreNode::Value(backward)),
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
            | ValueType::PathUniverse(source, target) => {
                Former::PathUniverse(CoreNode::Value(source), CoreNode::Value(target))
            },
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
    /// - ensures: as [`Source::read`]; a computation of any former reads as
    ///   [`Former::Computation`].
    /// - provides: the printer's reading of the core arena.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every value-type, computation-type and value former
    ///   of the core is printed at its exact spelling by the goldens, and a
    ///   dangling id and a computation each spell `?`.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
    /// - witness: `goldens::tests::pair_of_injections_pins_sum_notation`
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
                    | Computation::Lambda(_)
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
