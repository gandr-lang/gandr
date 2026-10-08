//! The type language: [`ValueType`] on the positive side and [`CompType`] on
//! the negative side.
//!
//! The vocabulary is closed: no hole, metavariable, mark, or effect-row
//! constructor exists to be represented.
//!
//! # One former is indexed by a value term, and that makes the arrow dependent
//!
//! [`ValueType::Element`] reads a type off a **code**: a value whose type is a
//! universe. It is the only former whose child crosses from the type language
//! into the term language, and everything a dependent codomain can say goes
//! through it — without it a codomain scoped under a binder has nothing to
//! mention, and the dependent arrow is dependent in name only.
//!
//! Two consequences ride on that one child and are stated here because every
//! consumer inherits them: a type can carry a free de Bruijn index, so a type
//! stored in a context is open and has to be shifted; and type conversion
//! descends into terms, so definitional equality on types is more than a walk
//! over types.
//!
//! # Two arrows, and why the dependent one is its own node
//!
//! [`CompType::Arrow`] is the non-dependent function type: its codomain stands
//! in the ambient context. [`CompType::Pi`] is the dependent one: its codomain
//! is scoped under one value binder, so the same two children mean two
//! different things and a flag on one former would make the meaning of a child
//! depend on a payload byte. The two are therefore distinct nodes at distinct
//! tags, and the numbering that gives the dependent former its tag is settled
//! in [`crate::tags`] together with the reserved stored-sharing block.
//!
//! Nothing a codomain can mention is a term at this vocabulary, so a `Pi` whose
//! codomain ignores its binder denotes what the `Arrow` over the same children
//! denotes. The two remain distinct types at the kernel's definitional
//! equality, and the producer's obligation is the one that keeps that from
//! being an incompleteness: the dependent former is emitted only where the
//! codomain is genuinely scoped.
//!
//! Children are typed arena ids and the derived relations are shallow, with the
//! child-id-equality caveat stated once in [`crate::term`].

use gandr_kernel_strata::Level;

use crate::arena::CompTypeId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::BaseType;
use crate::term::ConstantIndex;

/// A value type: the positive fragment of the type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueType
{
    /// A rigid base-type atom.
    Base(BaseType),
    /// The unit type, inhabited by [`crate::Value::Unit`] alone.
    Unit,
    /// The non-dependent product `A × B`.
    Product(ValueTypeId, ValueTypeId),
    /// The sum `A + B`, with left and right injections.
    Sum(ValueTypeId, ValueTypeId),
    /// The thunk type `U C` of a computation type `C`.
    Thunk(CompTypeId),
    /// The universe former at a canonical level `l`. Its own level is `l + 1`,
    /// so the universe rule is one call into the strict-order predicate of the
    /// level oracle.
    Universe(Level),
    /// An explicit lift of a value type into a strictly higher universe: the
    /// inner type relocated to `target`, valid when the inner type's level is
    /// strictly below it. There is no implicit cumulativity.
    Lift
    {
        /// The value type being lifted.
        inner: ValueTypeId,
        /// The target universe level, which is the lifted type's level.
        target: Level,
    },
    /// The type a code denotes: `El l v`, where `v` is a value of type
    /// `Universe l`.
    ///
    /// **The level is carried rather than inferred, and that is what keeps type
    /// formation a walk over types.** Reading the level off the node makes
    /// formation a lookup — the same shape [`Self::Abstract`] already has —
    /// where synthesizing the code's type would make the formation walk depend
    /// on the checking machine. The carried level is *checked* rather than
    /// trusted: admission re-derives that the code checks against
    /// `Universe level`, so a producer that writes the wrong level is refused
    /// rather than believed.
    Element
    {
        /// The code: a value whose type is `Universe level`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
    /// A sealed abstract type: a minted nominal atom, named by the admission
    /// position of the declaration that introduced it.
    ///
    /// This is the one type-level reference form the grammar admits, and it is
    /// deliberately the only one: the kernel names an atom, never a definition,
    /// so no type-level unfolding rule exists to be written. Opacity is
    /// therefore re-derived from a closed match rather than imported as a claim
    /// — no arm anywhere replaces an atom by a representation.
    Abstract(ConstantIndex),
}

/// A computation type: the negative fragment of the type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CompType
{
    /// The returner `F A` of a value type `A`: the type of a computation
    /// returning a value of type `A`. It is pure — there is no effect row.
    Returner(ValueTypeId),
    /// The function type `A → C` from a value type to a computation type.
    ///
    /// Non-dependent: the codomain stands in the ambient context and binds
    /// nothing, so a de Bruijn index in it counts the same binders it would
    /// count outside the arrow.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain.
        codomain: CompTypeId,
    },
    /// The dependent function type `Π (x : A). C`, binding one value variable
    /// for its codomain.
    ///
    /// The codomain stands in the ambient context **extended by the domain**,
    /// so de Bruijn index zero within it names this former's own binder and
    /// every outer index counts one further out than it does at the `Pi`
    /// itself. That scoping is the whole difference from [`Self::Arrow`]
    /// and it is why the two are distinct nodes rather than one former with
    /// a flag.
    Pi
    {
        /// The value-type domain, in the ambient context.
        domain: ValueTypeId,
        /// The computation-type codomain, under the domain's binder.
        codomain: CompTypeId,
    },
}
