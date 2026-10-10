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

use core::fmt;

use gandr_kernel_strata::Level;

use crate::arena::CompTypeId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::BaseType;
use crate::term::ConstantIndex;

/// One of the two ground sorts a universe family is indexed by: the value
/// types and the computation types.
///
/// A sort is the first half of a classifier and the level is the second, so
/// `Type[+, l]` and `Type[-, l]` are two families at one level rather than one
/// family with a polarity flag on its members. The literal spellings are the
/// positive and negative types of the polarized literature.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GroundSort
{
    /// The value types, spelled `+`: the positive sort.
    Value,
    /// The computation types, spelled `-`: the negative sort.
    Computation,
}

impl fmt::Display for GroundSort
{
    /// The sort's literal: `+` for the value sort, `-` for the computation
    /// sort.
    ///
    /// # Specification
    /// - requires: a formatter accepting or refusing writes.
    /// - ensures: writes + for the value sort and - for the computation sort.
    /// - provides: the polarity literal of the selected universe family.
    /// - fails: propagates the formatter write failure.
    /// - panics: none.
    /// - executable: none — Formatter has no readable output or refusal state;
    ///   a predicate cannot observe these effects without wrapping or replaying
    ///   the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers every refusal category and site, all tag-byte
    ///   spellings, version and quantity ceilings, the two sort literals, and
    ///   refusal by a real exhausted byte sink. It observes distinct causes,
    ///   complete numeric payloads and exact sink error kinds, separating
    ///   collapsed classifications, lost high bits and swallowed failures.
    ///   Diagnostic wording and nondefault formatter flags are outside the
    ///   hypothesis.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Value => f.write_str("+"),
            | Self::Computation => f.write_str("-"),
        }
    }
}

/// A value type: the positive fragment of the type vocabulary.
///
/// # Specification
/// - requires: payload types are well formed; formation, code classification
///   and live-child resolution are external obligations.
/// - ensures: retains the selected positive type former, levels and typed child
///   ids; derived equality is shallow in graph depth.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 builds all former families with distinguishable children,
///   nonzero levels and literal payloads, observes the exact stored nodes and
///   ordered edges, and checks each operation changes only its own family
///   length. Quote decoding covers matching, crossed and non-quote codes
///   without allocating an alias node. These distinguish child permutations,
///   payload loss, wrong-family minting and accidental hash-consing; the probes
///   are not a typing or arena-provenance proof.
/// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
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
    /// The universe of one ground sort at a canonical level `l`: the codes of
    /// the value types at `l` when `sort` is [`GroundSort::Value`], of the
    /// computation types at `l` when it is [`GroundSort::Computation`]. Either
    /// way it is a value type — a code is a value — and its own level is
    /// `l + 1`, so the universe rule is one call into the strict-order
    /// predicate of the level oracle.
    Universe
    {
        /// The sort of the types whose codes it holds.
        sort: GroundSort,
        /// The level of those types.
        level: Level,
    },
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
    /// The static Pi from `A` to `B`: the classifier of a type operator from
    /// codes at `A` to codes at `B`.
    ///
    /// It is non-dependent: the codomain stands in the ambient context, as
    /// [`CompType::Arrow`]'s does, so the former binds nothing. Both children
    /// are static classifiers — universes, or static Pis over them — which
    /// formation checks; its inhabitants are codes, so it is a value type at
    /// the join of its children's levels.
    StaticPi
    {
        /// The classifier of the operand.
        domain: ValueTypeId,
        /// The classifier of the result.
        codomain: ValueTypeId,
    },
}

/// A computation type: the negative fragment of the type vocabulary.
///
/// # Specification
/// - requires: payload types are well formed; formation, code classification
///   and live-child resolution are external obligations.
/// - ensures: retains the selected negative type former; Arrow and Pi remain
///   distinct even with the same children, and derived equality is shallow in
///   graph depth.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 builds all former families with distinguishable children,
///   nonzero levels and literal payloads, observes the exact stored nodes and
///   ordered edges, and checks each operation changes only its own family
///   length. Quote decoding covers matching, crossed and non-quote codes
///   without allocating an alias node. These distinguish child permutations,
///   payload loss, wrong-family minting and accidental hash-consing; the probes
///   are not a typing or arena-provenance proof.
/// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
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
    /// The computation type a code denotes: `El⁻ l v`, where `v` is a value of
    /// type `Universe⁻ l`.
    ///
    /// The computation-family twin of [`ValueType::Element`], carrying its
    /// level for the same reason: formation reads the level off the node and
    /// owes the code's check rather than deciding it.
    Element
    {
        /// The code: a value whose type is the computation universe at
        /// `target`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
}
