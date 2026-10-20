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
//! A `Pi` whose codomain ignores its binder denotes what the `Arrow` over the
//! same children denotes. The two stay distinct nodes; conversion identifies
//! them, weakening the plain codomain past the dependent binder (#577), since
//! no producer can keep the dependent former to codomains that name their
//! binder when a family applied at the binder reads to a constant type only
//! once its code is read. The decision is in `gandr-kernel-core`'s `conv`.
//!
//! # Universe families and quotes
//!
//! **Choice.** Universes come in two families, one per ground sort:
//! [`ValueType::Universe`] with [`GroundSort::Value`] classifies value types at
//! its level, and with [`GroundSort::Computation`] classifies computation
//! types at its level. Both are value types one level up — a code is a value
//! whatever family it decodes into. A code is a quote, [`Value::Quote`] of a
//! value type or [`Value::QuoteComputation`] of a computation type, and a type
//! is read off a code by the decoding former of its family,
//! [`ValueType::Element`] or [`CompType::Element`].
//!
//! **Decode on mint.** [`TermArena::value_type_element`] over a value quote
//! returns the quoted type and mints nothing, and
//! [`TermArena::comp_type_element`] does the same over a computation quote.
//! The decoding rule `El ⌜A⌝ = A` therefore fires at the one place a decode is
//! made, so no arena holds the redex, and no artifact either: a table writing a
//! decode over a quote reads back as the quoted type, and the re-encoding
//! check refuses it as non-canonical. A decode across the families — a
//! computation decode of a value quote — is minted as written, for the checker
//! to refuse as a type mismatch.
//!
//! **Alternatives.** One universe over both sorts: a value type and a
//! computation type are different kinds of thing in call-by-push-value, and a
//! single universe would need a sort test at every decode. A sort parameter on
//! the universe is the surface's business: none reaches this crate, so
//! [`GroundSort`] has exactly the two ground sorts. A decode node the checker
//! reduces would put a redex in front of every conversion and every walk.
//!
//! **Reversal.** A decoding rule that needs a context to fire, which a
//! constructor cannot see.
//!
//! # Static operators
//!
//! **Choice.** A type operator is classified by [`ValueType::StaticPi`] and
//! eliminated by [`Value::StaticApplication`]. The static Pi is
//! non-dependent: its codomain stands in the ambient context and the former
//! binds nothing. The kernel has no static lambda. An operator's body is an
//! elaborator-side definition; what reaches an admitted declaration is its
//! static normal form, where every application of a defined operator has been
//! reduced away and a remaining static application is neutral — headed by a
//! variable or an opaque constant. A δβ-step a certificate replays hands the
//! kernel the operator's body with its binders stripped (the conversion replay
//! in `gandr-kernel-core`), so no node in this arena binds a static parameter.
//!
//! **Alternatives.** A static lambda former would make every static redex a
//! kernel concern: the checker would owe a β-rule at values, conversion would
//! owe it too, and the trusted base would grow by a reduction the elaborator
//! already performs and certifies. A dependent static Pi: no former indexed by
//! a code is applied to a static argument at this vocabulary.
//!
//! **Reversal.** A static lambda former arrives when a declaration must carry
//! an operator itself rather than its instances — an operator exported across
//! a module boundary whose instances the importer forms.
//!
//! # N-ary products and sums
//!
//! [`ValueType::Product`] and [`ValueType::Sum`] hold a list of parts;
//! [`Value::Tuple`] holds its components, [`Value::Injection`] names its
//! summand by position, [`Computation::TupleProjection`] names a tuple's
//! component by position and returns it, and [`Computation::Case`] holds one
//! branch per summand. The unit is the product of no parts and the empty
//! tuple; the empty type is the sum of no summands, and a case of no branches
//! eliminates it. There is no unit, empty, pair or absurd variant, and no side
//! alphabet. [`ValueType::unit`], [`ValueType::empty`] and [`Value::unit`]
//! build the zero-ary nodes; [`Value::components`],
//! [`ValueType::product_parts`] and [`ValueType::summands`] read the lists.
//!
//! **Choice.** One former per shape, counted, so `A × B × C` is not
//! `(A × B) × C` and the zero-ary cases are the same former at count zero.
//! **Alternatives.** Binary formers with a unit terminator would encode an
//! n-ary product as a right-nested chain the checker and the surface would
//! both re-associate, and two spellings of one type would need a
//! canonicalization rule. Unit and empty variants beside counted formers
//! would leave two canonical forms of each. **Reversal.** None planned; a new
//! arity-dependent former takes a new byte.
//!
//! **Tuple projection.** **Choice.** A positional projection, mirroring the
//! record projection: `TupleProjection(tuple, i)` synthesises `F Aᵢ` from a
//! tuple of type `A₀ × … × Aₙ` and reduces on a tuple literal to the return of
//! its `i`-th component. A component at or past the arity is refused as an
//! absent component. **Alternatives.** A split eliminator binding every
//! component at once (`split v as (x₀, …, xₙ) in M`) also reads arity zero,
//! where no component exists to project; it binds n variables in one node
//! where projection binds none. A split erased to a chain of projections keeps
//! the kernel to one product eliminator. **Reversal.** A split former arrives
//! in the kernel if an erased split's projection chain proves costly to check
//! or replay.
//!
//! # The lazy product
//!
//! [`CompType::With`] is the computation product `C₀ & … & Cₙ₋₁` of
//! call-by-push-value (Paul Blain Levy, *Call-By-Push-Value: A
//! Functional/Imperative Synthesis*, Springer 2003, the computation product
//! with its projections), n-ary as [`ValueType::Product`] is: the empty lazy
//! product is the terminal computation type `⊤`. [`Computation::With`] pairs
//! computations without running any; [`Computation::Project`] observes the
//! component at one position and runs it. The β law is
//! `Project(i, With(M₀, …, Mₙ₋₁)) = Mᵢ`. The η law is the type's definition
//! as a destructor-defined (negative) type: a computation `M : C₀ & … & Cₙ₋₁`
//! is `With(Project(0, M), …, Project(n - 1, M))`, the pairing of its own
//! projections, so every computation of `⊤` is the empty pairing.
//!
//! The former is native rather than the record of thunks the
//! call-by-push-value isomorphism `U(&{l : C_l}) ≅ #{l : U C_l}` would derive
//! it as. Under that encoding a computation of the lazy product is a value of
//! a record type, so `With`'s η no longer holds, and a pattern can match the
//! record where only an observation should reach a component.
//!
//! # Codata
//!
//! [`CompType::Codata`] names a codata declaration at its parameters, the
//! greatest fixpoint `νX. &{dᵢ : Bᵢ}` of the declaration's observations
//! (Andreas Abel, Brigitte Pientka, David Thibodeau and Anton Setzer,
//! *Copatterns: programming infinite structures by observations*, POPL 2013).
//! It is read as the lazy product of its observations, `&{B₀, B₁, …}`, one
//! observation a lazy product of one, each instantiated at the arguments and
//! naming the type itself where the declaration names `X`. The reading is
//! taken where a computation is checked against the type and where a
//! projection observes a computation of it; conversion
//! compares the declaration and the arguments and never unfolds, so the type
//! has no η.
//!
//! # The returned endpoint
//!
//! [`Value::Returned`] is the value a pure computation returns, standing where
//! a value is read: the endpoint `mul(neutral, x)` of a path is a call, not a
//! value former. It mirrors the core's node of the same name. It inhabits `A`
//! when its computation returns `A`; a returner is pure, because no
//! computation type here carries an effect row. It reads as the value its
//! computation reduces to `return` of, and one whose computation is stuck
//! stays the node, compared by its computation.
//!
//! **Choice.** A value node over one computation child, at `0x34` in the
//! element-identity range, so the kernel holds the call and re-derives what
//! it returns by its own reduction.
//!
//! **Alternatives.** Normalising the endpoint in the producer and persisting
//! the value it returns, which needs no node but puts a reduction outside the
//! kernel's re-derivation: the producer's normaliser becomes trusted
//! computation. A stuck endpoint, such as `x + 1` over a variable, would have
//! no image at all.
//!
//! **Reversal.** None while endpoints are terms.
//!
//! Children are typed arena ids and the derived relations are shallow, with the
//! child-id-equality caveat stated once in [`crate::term`].
//!
//! [`Value::Quote`]: crate::Value::Quote
//! [`Value::QuoteComputation`]: crate::Value::QuoteComputation
//! [`Value::StaticApplication`]: crate::Value::StaticApplication
//! [`Value::Tuple`]: crate::Value::Tuple
//! [`Value::Injection`]: crate::Value::Injection
//! [`Value::unit`]: crate::Value::unit
//! [`Value::components`]: crate::Value::components
//! [`Computation::TupleProjection`]: crate::Computation::TupleProjection
//! [`Computation::Case`]: crate::Computation::Case
//! [`Value::Returned`]: crate::Value::Returned
//! [`Computation::With`]: crate::Computation::With
//! [`Computation::Project`]: crate::Computation::Project
//! [`TermArena::value_type_element`]: crate::TermArena::value_type_element
//! [`TermArena::comp_type_element`]: crate::TermArena::comp_type_element

use core::fmt;

use anodized::spec;
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
            Self::Value => f.write_str("+"),
            Self::Computation => f.write_str("-"),
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
    /// A generative datatype applied to its declaration telescope.
    Data
    {
        /// Admission position of the datatype declaration; never unfolds.
        declaration: ConstantIndex,
        /// Arguments in telescope order, including quoted type parameters.
        arguments: alloc::vec::Vec<ValueId>,
    },
    /// A structural record, canonically ordered by field label.
    Record(alloc::collections::BTreeMap<crate::FieldLabel, ValueTypeId>),
    /// A closed finite session graph with a product telescope of payload codes.
    Session
    {
        /// Raw syntax; formation checks closure and contractivity.
        graph: alloc::sync::Arc<crate::session::Graph>,
        /// The payload product, one component per payload code, in order.
        payloads: ValueTypeId,
    },
    /// Certified equivalences between two quoted closed first-order codes.
    /// Both endpoints form at level zero; formation checks each code.
    PathUniverse(ValueId, ValueId),
    /// Forward-only certificates between two quoted closed codes of the
    /// `Flow_U` vocabulary: first-order, function and session codes. Both
    /// endpoints form at level zero; formation checks each code and grants no
    /// inverse.
    FlowUniverse(ValueId, ValueId),
    /// Element identity `Path(A, a, b)` between two values of one value type.
    /// Formation checks both endpoints at the domain and refuses an open
    /// domain; an introduction form other than `here` checks against the
    /// identity fibre the kernel computes at the closed domain.
    Path
    {
        /// The value type the endpoints inhabit.
        domain: ValueTypeId,
        /// The source endpoint.
        left: ValueId,
        /// The target endpoint.
        right: ValueId,
    },
    /// Directed element identity `Flow(A, x, y)`: `x` transports into `y`,
    /// with no inverse. Formation checks both endpoints at the domain, as for
    /// `Path`; at the closed level-zero value universe it and `Flow_U(x, y)`
    /// are two readings of one classifier, and elsewhere `stay`, composition
    /// and neutrals inhabit it.
    Flow
    {
        /// The value type the endpoints inhabit.
        domain: ValueTypeId,
        /// The source endpoint, consumed contravariantly.
        source: ValueId,
        /// The target endpoint, produced covariantly.
        target: ValueId,
    },
    /// The bridge `Br(A, a, b)` between two values of one value type: the
    /// relation the identity fold computes in its non-fibrant reading.
    /// Formation checks both endpoints at the domain and requires the domain
    /// closed, free of sealed atoms and inside the bridge fold; an introduction
    /// form checks against the bridge fibre the kernel computes there. No
    /// reflexivity, transport or eliminator belongs to it.
    Bridge
    {
        /// The value type the endpoints inhabit.
        domain: ValueTypeId,
        /// The source endpoint.
        left: ValueId,
        /// The target endpoint.
        right: ValueId,
    },
    /// A rigid base-type atom.
    Base(BaseType),
    /// The product of its components, in order: `Product([])` is the unit
    /// type, inhabited by the empty [`crate::Value::Tuple`] alone, and
    /// `Product([A, B])` the pair type `A × B`.
    Product(alloc::boxed::Box<[ValueTypeId]>),
    /// The dependent pair `Σ (x : A). B`, the second factor under one value
    /// binder of the first: a positive type at the join of its factors'
    /// levels. A [`crate::Value::Tuple`] of two components checks against it,
    /// the second at `B` instantiated at the first, and never synthesizes it;
    /// the dependent split and the positional projection eliminate it.
    ///
    /// It is a different node from the product of the same two children: the
    /// scoping of the second child is the whole difference, as it is between
    /// [`CompType::Pi`] and [`CompType::Arrow`].
    Sigma
    {
        /// The first factor, in the ambient context.
        first: ValueTypeId,
        /// The second factor, under the first's binder.
        second: ValueTypeId,
    },
    /// The sum of its summands, in order: `Sum([])` is the empty type, with
    /// no introduction rule, and `Sum([A, B])` the binary sum `A + B`.
    Sum(alloc::boxed::Box<[ValueTypeId]>),
    /// The strictly positive fixed point List A = μX. 1 + A × X.
    /// Its code is finite; inhabitants are observed through guarded replay.
    List(ValueTypeId),
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
    /// `A^s`: the values of `base` at the stage `s` of a recursion. Admission
    /// alone mints it — at a fixpoint's staged parameter, its self-reference's
    /// domain and the recursive fields of a case on a staged value — so it is
    /// no wire former: the decoder never produces it, formation refuses it in
    /// a presented type, and the encoder writes its base. A stage refines the
    /// type's values and never its identity: `A^s` is assignable where `A` is
    /// wanted, and every other comparison takes it for itself. The base is
    /// never itself staged.
    Staged
    {
        /// The type the stage refines.
        base: ValueTypeId,
        /// The stage.
        stage: crate::Stage,
    },
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

impl ValueType
{
    /// The unit type: the product of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Product([])`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit built here and the one the arena mints are
    ///   the same node, and neither a product of two components nor the empty
    ///   sum is the unit.
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| matches!(ret, Self::Product(ref components) if components.is_empty()))]
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self::Product(alloc::boxed::Box::default())
    }

    /// The empty type: the sum of no summands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Sum([])`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::unit`].
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| matches!(ret, Self::Sum(ref summands) if summands.is_empty()))]
    #[inline]
    #[must_use]
    pub fn empty() -> Self
    {
        Self::Sum(alloc::boxed::Box::default())
    }

    /// The parts of a product, in order; nothing for any other former.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the product's own part list for a product, and nothing for
    ///   every other former, a sum included.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of two parts, the unit and the empty type
    ///   separate the product reading from the sum reading.
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| match *self { Self::Product(ref parts) => ret == Some(&**parts), Self::Data { .. } | Self::Record(_) | Self::Session { .. } | Self::PathUniverse(..) | Self::FlowUniverse(..) | Self::Path { .. } | Self::Flow { .. } | Self::Bridge { .. } | Self::Base(_) | Self::Sigma { .. } | Self::Sum(_) | Self::List(_) | Self::Thunk(_) | Self::Universe { .. } | Self::Lift { .. } | Self::Element { .. } | Self::Abstract(_) | Self::Staged { .. } | Self::StaticPi { .. } => ret.is_none() })]
    #[inline]
    #[must_use]
    pub fn product_parts(&self) -> Option<&[ValueTypeId]>
    {
        match *self {
            Self::Product(ref parts) => Some(parts),
            Self::Data { .. }
            | Self::Record(_)
            | Self::Session { .. }
            | Self::PathUniverse(..)
            | Self::FlowUniverse(..)
            | Self::Path { .. }
            | Self::Flow { .. }
            | Self::Bridge { .. }
            | Self::Base(_)
            | Self::Sigma { .. }
            | Self::Sum(_)
            | Self::List(_)
            | Self::Thunk(_)
            | Self::Universe { .. }
            | Self::Lift { .. }
            | Self::Element { .. }
            | Self::Abstract(_)
            | Self::Staged { .. }
            | Self::StaticPi { .. } => None,
        }
    }

    /// The summands of a sum, in order; nothing for any other former.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum's own summand list for a sum, and nothing for every
    ///   other former, a product included.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::product_parts`].
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| match *self { Self::Sum(ref summands) => ret == Some(&**summands), Self::Data { .. } | Self::Record(_) | Self::Session { .. } | Self::PathUniverse(..) | Self::FlowUniverse(..) | Self::Path { .. } | Self::Flow { .. } | Self::Bridge { .. } | Self::Base(_) | Self::Product(_) | Self::Sigma { .. } | Self::List(_) | Self::Thunk(_) | Self::Universe { .. } | Self::Lift { .. } | Self::Element { .. } | Self::Abstract(_) | Self::Staged { .. } | Self::StaticPi { .. } => ret.is_none() })]
    #[inline]
    #[must_use]
    pub fn summands(&self) -> Option<&[ValueTypeId]>
    {
        match *self {
            Self::Sum(ref summands) => Some(summands),
            Self::Data { .. }
            | Self::Record(_)
            | Self::Session { .. }
            | Self::PathUniverse(..)
            | Self::FlowUniverse(..)
            | Self::Path { .. }
            | Self::Flow { .. }
            | Self::Bridge { .. }
            | Self::Base(_)
            | Self::Product(_)
            | Self::Sigma { .. }
            | Self::List(_)
            | Self::Thunk(_)
            | Self::Universe { .. }
            | Self::Lift { .. }
            | Self::Element { .. }
            | Self::Abstract(_)
            | Self::Staged { .. }
            | Self::StaticPi { .. } => None,
        }
    }
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
    /// The lazy product `C₀ & … & Cₙ₋₁` of computation types, the terminal
    /// computation type when there are none: a computation of this type runs
    /// no component until a projection observes one.
    With(alloc::boxed::Box<[CompTypeId]>),
    /// A nominal codata type applied to its declaration's parameters: the
    /// greatest fixpoint `νX. &{dᵢ : Bᵢ}` of its observations.
    ///
    /// It is read as the lazy product of its observations, each instantiated
    /// at `arguments`, where a computation is introduced against it or one of
    /// its observations is taken, and nowhere else: two codata types convert
    /// exactly when they name one declaration at convertible arguments, and no
    /// computation of the type is equal to the product of its observations.
    Codata
    {
        /// The admitted codata declaration.
        declaration: ConstantIndex,
        /// One value per parameter of the declaration's telescope.
        arguments: alloc::vec::Vec<ValueId>,
    },
}
