//! The term language: [`Value`] on the positive side and [`Computation`] on the
//! negative side, together with the reference forms [`DeBruijnIndex`] and
//! [`ConstantIndex`] and the binary [`Side`].
//!
//! Terms are nameless. A bound value variable is a [`DeBruijnIndex`] counting
//! binders outward from its use site, so α-equivalence is syntactic identity
//! and no name capture is representable. A [`Value::Constant`] names a prior
//! declaration by its admission position.
//!
//! The vocabulary is closed: no hole, metavariable, mark, annotation, effect
//! row, handler, or control operator exists to be represented.
//!
//! # Children are ids, and the derived relations are shallow
//!
//! A node's children are typed arena ids ([`ValueId`], [`ComputationId`])
//! rather than owned pointers; leaf payloads stay inline. Because an id is
//! `Copy`, the derived `Clone`, `Drop`, `PartialEq`, `Eq` and `Hash` are
//! **shallow** — they do not walk term depth — which is what retires the
//! hand-written iterative destructor an owned-tree representation needs and
//! makes arena teardown a flat vector drop.
//!
//! **The derived equality is child-id equality, not structural equality.** Two
//! structurally equal subterms need not share an id, because the kernel
//! preserves the sharing a decode handed it and never creates more. Every use
//! site therefore either compares only inline leaf payloads or resolves ids
//! explicitly; the format's deduplication is keyed on encoded content, never on
//! a node's derived equality.
//!
//! # Nominal data and structural records
//!
//! [`DeclarationContent::Data`] carries parameter classifiers, constructor
//! field lists and a universe kind; its declaration-kind byte is
//! [`KIND_DATA`]. A nominal application names the admitted declaration and
//! retains every argument as a value child; a constructor carries its complete
//! classifier, tag and fields. A case carries its scrutinee, a motive binding
//! that scrutinee and ambient branch functions. Record types and values carry
//! fields in strictly increasing UTF-8 label order; projection carries one
//! label and its record value.
//!
//! These six nodes use counted arities where their children vary. Canonical
//! encoding includes counts, labels and every child, including empty records
//! and nullary constructors. Decoding rejects malformed ordering, lengths and
//! child families; it grants no typing authority. Ordinary kernel admission
//! checks the reconstructed declaration, and `gandr-kernel-core`'s
//! `native_declarations_and_eliminators_survive_canonical_decode` exercises
//! that complete path.
//!
//! A recursive declaration needs no new framing: a field naming its own family
//! is an ordinary nominal application whose declaration index is the
//! declaration's own position. Admission, not the reader, decides whether that
//! occurrence is strictly positive and uniform. The fixpoint carries one
//! evidence byte, [`FIXPOINT_PARTIAL`], [`FIXPOINT_STRUCTURAL_DESCENT`] or
//! [`FIXPOINT_STAGED`] followed by the staged position as a varint, then one
//! computation child: its body under the self binder. Any other evidence byte
//! is refused as an unknown tag at the evidence site. The byte records a claim
//! kernel admission replays as the stage typing, the descent byte at position
//! zero; decoding it grants nothing. The encoder's entry goldens and the
//! decoder's former-preservation witness pin every byte.
//!
//! **Choice.** Native identity and field structure, not atom names or product
//! offsets. New node and declaration-kind bytes extend the closed vocabulary
//! without changing existing byte meanings, so they hold the version.
//! **Reversal.** A changed framing or reassigned meaning requires a version
//! change; mutual blocks, indexed families and further conversion evidence
//! need explicit new readers.
//!
//! [`ValueId`]: crate::ValueId
//! [`ComputationId`]: crate::ComputationId
//! [`DeclarationContent::Data`]: crate::DeclarationContent::Data
//! [`KIND_DATA`]: crate::KIND_DATA
//! [`FIXPOINT_PARTIAL`]: crate::FIXPOINT_PARTIAL
//! [`FIXPOINT_STRUCTURAL_DESCENT`]: crate::FIXPOINT_STRUCTURAL_DESCENT
//! [`FIXPOINT_STAGED`]: crate::FIXPOINT_STAGED

use anodized::spec;
use gandr_kernel_strata::Level;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::Literal;

/// A bound value variable, as a de Bruijn index counting binders outward: `0`
/// is the nearest enclosing binder.
///
/// # Specification
/// - requires: all u32 distances are representable; binder scope is checked by
///   admission.
/// - ensures: carries a binder distance distinct from a declaration position.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeBruijnIndex(u32);

impl From<u32> for DeBruijnIndex
{
    /// The index for a binder distance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<DeBruijnIndex> for u32
{
    /// The binder distance the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: DeBruijnIndex) -> Self
    {
        index.0
    }
}

/// A reference to a prior declaration by its admission position, where `0` is
/// the first admitted declaration.
///
/// An admission position and a subterm-table index are two different things
/// that both spell as an integer, and confusing them is the format's most
/// available mistake; the wrapper is what stops one being passed where the
/// other belongs.
///
/// # Specification
/// - requires: all host positions are representable; declaration existence is
///   checked by admission.
/// - ensures: carries a declaration position distinct from a binder distance
///   and a wire-table index.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstantIndex(usize);

impl From<usize> for ConstantIndex
{
    /// The index for an admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ConstantIndex> for usize
{
    /// The admission position the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ConstantIndex) -> Self
    {
        index.0
    }
}

/// One side of a binary former: the injection into a summand of `A + B`, or
/// the projection of a component of the lazy product `C & D`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// The left side: the left summand of `A + B`, the left component of
    /// `C & D`.
    Left,
    /// The right side: the right summand of `A + B`, the right component of
    /// `C & D`.
    Right,
}

/// The wiring a composition requests between its two flows.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Seam
{
    /// The first output feeds the second input: one directed edge.
    Sequence,
    /// The second output also feeds back into the first input: a two-edge
    /// cycle, which composition refuses.
    Feedback,
}

/// A value: the positive fragment of the term vocabulary.
///
/// Values are the total, thunkable half of the polarity split. No value
/// constructor introduces a computation effect. Two values embed a
/// computation: [`Self::Thunk`] suspends it, and [`Self::Returned`] stands for
/// what a pure one returns, which the kernel reads by running it.
///
/// # Specification
/// - requires: payload types are well formed; typing, live-child resolution and
///   scoping are external obligations.
/// - ensures: retains the selected positive former and its typed child ids;
///   derived equality compares child ordinals rather than recursively comparing
///   graphs.
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
pub enum Value
{
    /// A datatype constructor with an explicit instantiated classifier.
    Constructor
    {
        /// The nominal datatype application.
        datatype: ValueTypeId,
        /// Position in the declaration's constructor table.
        tag: crate::ConstructorTag,
        /// Constructor fields in declaration order.
        fields: alloc::vec::Vec<ValueId>,
    },
    /// A structural record in canonical label order.
    Record(alloc::collections::BTreeMap<crate::FieldLabel, ValueId>),
    /// A session bisimulation inhabiting a native `Path_U` classifier.
    SessionPath
    {
        /// Source and target session codes.
        path_type: ValueTypeId,
        /// Finite untrusted relation, replayed at formation.
        evidence: alloc::sync::Arc<crate::session::Evidence>,
        /// Native payload-path tuple, one path per payload, in order.
        payload_paths: ValueId,
    },
    /// A session simulation inhabiting a native `Flow_U` classifier: Gay–Hole
    /// subtyping from the source code to the target, with no inverse.
    SessionFlow
    {
        /// Source and target session codes.
        flow_type: ValueTypeId,
        /// Finite untrusted relation, replayed at formation.
        evidence: alloc::sync::Arc<crate::session::Evidence>,
        /// Native payload-path tuple, one path per payload obligation, in
        /// order.
        payload_paths: ValueId,
    },
    /// Directed reflexivity `stay(a)`: inhabits `Flow(A, a, a)`, `Flow_U(a,
    /// a)` at a code, and every flow whose endpoints convert with `a`.
    Stay
    {
        /// The point `a`.
        point: ValueId,
        /// The dialogue relating the point to each endpoint, untrusted.
        dialogues: alloc::sync::Arc<crate::EndpointDialogues>,
    },
    /// A leaf-natural forward translator inhabiting its `Flow_U` classifier,
    /// with one proposed image per source constructor pattern and no inverse.
    ForwardFlow
    {
        /// The native universe-flow classifier over first-order codes.
        flow_type: ValueTypeId,
        /// The closed translator `U (source → F target)`.
        translator: ValueId,
        /// One proposed image per kernel-generated source pattern, in
        /// pattern order: `thunk(λ…λ. return o)`, one binder per pattern
        /// leaf in leaf order, so the output `o` names leaves by de Bruijn
        /// index and stays closed under every rewrite.
        outputs: alloc::boxed::Box<[ValueId]>,
        /// One replay dialogue per output, untrusted.
        dialogues: alloc::sync::Arc<[crate::Dialogue]>,
    },
    /// The arrow's action at function codes: a flow of results over a flow
    /// of arguments, each boundary running the way its variance fixes.
    FunctionFlow
    {
        /// The native universe-flow classifier over two function codes.
        flow_type: ValueTypeId,
        /// The contravariant argument boundary, `Flow_U(A', A)`.
        domain: ValueId,
        /// The covariant result boundary, `Flow_U(B, B')`.
        codomain: ValueId,
    },
    /// Composition `then(p, q)`: `p` from `x` to `y` and `q` from `y` to `z`
    /// compose to a flow from `x` to `z`, over an explicit seam.
    Then
    {
        /// The first flow, whose output feeds the second.
        first: ValueId,
        /// The second flow.
        second: ValueId,
        /// The requested wiring; only a sequence admits.
        seam: Seam,
    },
    /// A componentwise flow between product codes: the first flow relates
    /// the left components, the second the right, at the level-zero universe.
    FlowProduct(ValueId, ValueId),
    /// Reflexivity at a quoted closed first-order or session code.
    PathRefl(ValueId),
    /// A componentwise path between product codes.
    PathProduct(ValueId, ValueId),
    /// An equivalence whose round trips are replayed during formation.
    PathEquiv
    {
        /// The native universe-path classifier.
        path_type: ValueTypeId,
        /// The closed forward translator.
        forward: ValueId,
        /// The closed backward translator.
        backward: ValueId,
        /// Untrusted dialogue data, never a formation verdict.
        evidence: alloc::sync::Arc<PathEvidence>,
    },
    /// The diagonal `here(a)`, inhabiting `Path(A, a, a)` and every identity
    /// whose endpoints convert with `a`.
    Here
    {
        /// The point `a`.
        point: ValueId,
        /// The dialogue relating the point to each endpoint, untrusted.
        dialogues: alloc::sync::Arc<crate::EndpointDialogues>,
    },
    /// A returned endpoint: the value the pure computation returns, standing
    /// where a value is read, such as `mul(neutral, x)` at a path endpoint.
    /// It inhabits `A` when the computation returns `A`, and reads as the
    /// value the computation reduces to `return` of.
    Returned(ComputationId),
    /// A guarded higher field: identity between two identities, observed to
    /// the program's stated depth.
    Higher
    {
        /// The guarded program, untrusted until replayed.
        program: alloc::sync::Arc<crate::HigherProgram>,
        /// One evidence value per guard layer, in layer order.
        evidence: alloc::boxed::Box<[ValueId]>,
    },
    /// Higher evaluation: identity at a thunk code, one replayed component per
    /// kernel-generated coverage pattern of the argument relation.
    HigherEvaluation
    {
        /// One pair of replay dialogues per component, untrusted.
        dialogues: alloc::sync::Arc<[crate::EvaluationDialogues]>,
        /// The returned values and output evidence of each component.
        components: alloc::boxed::Box<[crate::EvaluationComponent]>,
    },
    /// Quantified evaluation: identity at a thunk code whose argument relation
    /// binds a function, one pre-order tree of replayed steps per
    /// kernel-generated coverage pattern, each application step opening one
    /// branch per covering pattern of the applied function's result relation.
    QuantifiedEvaluation
    {
        /// The steps, in pre-order, untrusted.
        steps: alloc::sync::Arc<[crate::QuantifiedStep]>,
        /// Each step's value children in step order: three per return, two
        /// per application.
        children: alloc::boxed::Box<[ValueId]>,
    },
    /// A bound value variable.
    Variable(DeBruijnIndex),
    /// A reference to a prior declaration.
    Constant(ConstantIndex),
    /// A base-type literal.
    Literal(Literal),
    /// A tuple of its components, in order, introducing the product of their
    /// types: the empty tuple is the unique inhabitant of the unit type.
    Tuple(alloc::boxed::Box<[ValueId]>),
    /// A sum injection into the summand at the given position.
    Injection(Summand, ValueId),
    /// The empty native list; its element type comes from checking.
    ListNil,
    /// A native list cell, with its head and list tail.
    ListCons(ValueId, ValueId),
    /// A thunk, suspending a computation into the value type `U C`.
    Thunk(ComputationId),
    /// An explicit universe lift: given `body : A` with `A`'s level strictly
    /// below `target`, this value inhabits `Lift A target`.
    ///
    /// The lift is written, never inferred: a bare `body : A` does not inhabit
    /// `Lift A target` on its own, because there is no implicit cumulativity.
    Lift
    {
        /// The target universe level of the lift.
        target: Level,
        /// The value being lifted.
        body: ValueId,
    },
    /// The code of a value type: `⌜A⌝`, an inhabitant of the value universe at
    /// `A`'s level.
    Quote(ValueTypeId),
    /// The code of a computation type: `⌜C⌝`, an inhabitant of the
    /// computation universe at `C`'s level.
    QuoteComputation(CompTypeId),
    /// A static application `F a` of a type operator to a code: an inhabitant
    /// of the static Pi's codomain at the head's classifier.
    ///
    /// The vocabulary has no static lambda, so a static application is always
    /// neutral: its head is a constant or a variable, possibly under further
    /// static applications, and nothing reduces it. A static lambda a producer
    /// wrote is normalized away before export.
    StaticApplication(ValueId, ValueId),
}

impl Value
{
    /// The unit value: the tuple of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Tuple([])`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit built here and the one the arena mints are
    ///   the same node, and a tuple of two components is not the unit.
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| matches!(ret, Self::Tuple(ref components) if components.is_empty()))]
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self::Tuple(alloc::boxed::Box::default())
    }

    /// The components of a tuple, in order; nothing for any other former.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tuple's own component list for a tuple, and nothing for
    ///   every other former.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of two components, the empty tuple and an
    ///   injection separate the tuple reading from every other former.
    /// - witness: `arena::tests::the_unit_and_the_empty_type_are_zero_ary`
    #[spec(ensures: |ret| match *self { Self::Tuple(ref components) => ret == Some(&**components), Self::Constructor { .. } | Self::Record(_) | Self::SessionPath { .. } | Self::SessionFlow { .. } | Self::Stay { .. } | Self::ForwardFlow { .. } | Self::FunctionFlow { .. } | Self::Then { .. } | Self::FlowProduct(..) | Self::PathRefl(_) | Self::PathProduct(..) | Self::PathEquiv { .. } | Self::Here { .. } | Self::Returned(_) | Self::Higher { .. } | Self::HigherEvaluation { .. } | Self::QuantifiedEvaluation { .. } | Self::Variable(_) | Self::Constant(_) | Self::Literal(_) | Self::Injection(..) | Self::ListNil | Self::ListCons(..) | Self::Thunk(_) | Self::Lift { .. } | Self::Quote(_) | Self::QuoteComputation(_) | Self::StaticApplication(..) => ret.is_none() })]
    #[inline]
    #[must_use]
    pub fn components(&self) -> Option<&[ValueId]>
    {
        match *self {
            Self::Tuple(ref components) => Some(components),
            Self::Constructor { .. }
            | Self::Record(_)
            | Self::SessionPath { .. }
            | Self::SessionFlow { .. }
            | Self::Stay { .. }
            | Self::ForwardFlow { .. }
            | Self::FunctionFlow { .. }
            | Self::Then { .. }
            | Self::FlowProduct(..)
            | Self::PathRefl(_)
            | Self::PathProduct(..)
            | Self::PathEquiv { .. }
            | Self::Here { .. }
            | Self::Returned(_)
            | Self::Higher { .. }
            | Self::HigherEvaluation { .. }
            | Self::QuantifiedEvaluation { .. }
            | Self::Variable(_)
            | Self::Constant(_)
            | Self::Literal(_)
            | Self::Injection(..)
            | Self::ListNil
            | Self::ListCons(..)
            | Self::Thunk(_)
            | Self::Lift { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticApplication(..) => None,
        }
    }
}

/// A computation: the negative fragment of the term vocabulary.
///
/// The eliminators — application, force, bind, case — synthesize; the
/// introductions — lambda, return — check against an expected computation type.
///
/// # Specification
/// - requires: payload types are well formed; typing, live-child resolution and
///   scoping are external obligations.
/// - ensures: retains the selected negative former and its typed child ids;
///   derived equality compares child ordinals rather than recursively comparing
///   graphs.
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
pub enum Computation
{
    /// Eliminate a nominal datatype with a motive under one scrutinee binder.
    DataCase
    {
        /// The value whose datatype determines the constructor table.
        scrutinee: ValueId,
        /// Result classifier under the scrutinee binder.
        motive: CompTypeId,
        /// One branch per constructor, each binding its fields in order.
        branches: alloc::vec::Vec<ComputationId>,
    },
    /// Return one named field of a structural record.
    RecordProjection(ValueId, crate::FieldLabel),
    /// Return the component of a tuple at a position, counting from zero.
    TupleProjection(ValueId, Component),
    /// A lambda `λ. M`, binding one value variable; introduces `A → C`.
    Lambda(ComputationId),
    /// An application `M v` of a computation to a value argument.
    Application(ComputationId, ValueId),
    /// A returner `return v`, introducing `F A`.
    Return(ValueId),
    /// A sequencing bind `x ← M; N`, binding the value `M` returns into `N`.
    Bind(ComputationId, ComputationId),
    /// A force `force v` of a thunk value `v : U C`, running it as `C`.
    Force(ValueId),
    /// A sum elimination, binding the injected value into the branch of its
    /// summand. A case of no branches eliminates the empty sum: it checks
    /// against any computation type and has no beta rule.
    Case
    {
        /// The scrutinee value, of a sum type.
        scrutinee: ValueId,
        /// One branch per summand, in summand order, each checked with its
        /// summand bound.
        branches: alloc::boxed::Box<[ComputationId]>,
    },
    /// The dependent pair's eliminator: given a scrutinee of `Σ (x : A). B`
    /// and a motive `C` under one scrutinee binder, the body runs under the
    /// two components, the first outermost, against `C` at their pair; the
    /// split synthesizes `C` at the scrutinee.
    SigmaSplit
    {
        /// The dependent pair eliminated.
        scrutinee: ValueId,
        /// The result classifier under the scrutinee binder.
        motive: CompTypeId,
        /// The body, under the first and then the second component.
        body: ComputationId,
    },
    /// Pure right fold of a native list. The cons branch binds the head,
    /// then the folded tail result (index zero).
    ListFold
    {
        /// List element type.
        element: ValueTypeId,
        /// Fold result type.
        result: ValueTypeId,
        /// Native list to eliminate.
        list: ValueId,
        /// Empty-list branch, in the ambient context.
        on_nil: ComputationId,
        /// Cell branch, under the head and recursive result.
        on_cons: ComputationId,
    },
    /// Transport a value along a universe path.
    Transport(ValueId, ValueId),
    /// Dependent transport along an element path: given `path : Path(A, a,
    /// b)` and `value : P[a]`, computes `F P[b]`.
    PathTransport
    {
        /// The family `P`, a value type under one value binder: the endpoint.
        motive: ValueTypeId,
        /// The element path.
        path: ValueId,
        /// The value at the source endpoint.
        value: ValueId,
    },
    /// Transport over a two-entry telescope along a path in it: given the
    /// motive `Π (y : A). Π (z : B). F C`, `path : Path(A, a, b)`, `start :
    /// B[a]`, `over` a path from `start` carried along `path` in `B` to some
    /// `end : B[b]`, and `value : C[a, start]`, computes `F C[b, end]`.
    TelescopeTransport
    {
        /// The motive, the dependent arrow over the telescope `(y : A, z :
        /// B)` returning the family `C`.
        motive: CompTypeId,
        /// The path in the telescope's first entry.
        path: ValueId,
        /// The second entry's source point, in `B[a]`.
        start: ValueId,
        /// The path over `path` in the second entry.
        over: ValueId,
        /// The value at the source point of the telescope.
        value: ValueId,
    },
    /// Directed transport `ride`: given `flow` from `x` to `y` — a `Flow(A,
    /// x, y)`, or a `Flow_U(x, y)` over the level-zero universe — and `value :
    /// P[x]` for a motive `P` covariant in its binder, computes `F P[y]`.
    Ride
    {
        /// The family `P`, a value type under one value binder: the moving
        /// endpoint.
        motive: ValueTypeId,
        /// The flow ridden along.
        flow: ValueId,
        /// The value at the source endpoint.
        value: ValueId,
    },
    /// Directed transport over a two-entry telescope: given the motive `Π (y :
    /// A). Π (z : B). F C`, `flow` from `a` to `b` in `A`, `start : B[a]`,
    /// `over` a flow from `start` ridden along `flow` in `B` to some `end :
    /// B[b]`, and `value : C[a, start]`, computes `F C[b, end]`.
    TelescopeRide
    {
        /// The motive, the dependent arrow over the telescope `(y : A, z :
        /// B)` returning the family `C`, covariant in both entries.
        motive: CompTypeId,
        /// The flow in the telescope's first entry.
        flow: ValueId,
        /// The second entry's source point, in `B[a]`.
        start: ValueId,
        /// The flow over `flow` in the second entry.
        over: ValueId,
        /// The value at the source point of the telescope.
        value: ValueId,
    },
    /// Application of a function identity at related inputs: evaluates both
    /// functions and continues with both results and their identity bound.
    RelatedApplication
    {
        /// The identity between two functions of one thunk code.
        path: ValueId,
        /// The source function's argument.
        left: ValueId,
        /// The target function's argument.
        right: ValueId,
        /// The identity between the two arguments.
        evidence: ValueId,
        /// The continuation, under the left result, the right result and
        /// their identity, innermost last.
        body: ComputationId,
    },
    /// A lazy pairing `⟨M, N⟩` of two computations, introducing the lazy
    /// product `C & D` of their types. Neither component runs until a
    /// projection observes it.
    With(ComputationId, ComputationId),
    /// The projection of one side of a lazy pairing, running that component.
    Project(Side, ComputationId),
    /// A fixpoint `fix x. M`, checking at any computation type `B` with its
    /// body scoped under one value binder, the fixpoint's own thunk `U B`.
    /// It unfolds only at a constructor argument or under an observation of
    /// its result.
    Fixpoint
    {
        /// The body, under the self binder.
        body: ComputationId,
        /// What the fixpoint claims about its own termination.
        evidence: FixpointEvidence,
    },
}

/// What a fixpoint claims about its own termination; the claim participates
/// in content identity and never in conversion.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FixpointEvidence
{
    /// No claim: the fixpoint is partial, and conversion never unfolds it.
    Partial,
    /// Structural recursion on the fixpoint's first parameter: the stage
    /// typing at [`StagedPosition`] zero, the wire's first spelling of it.
    StructuralDescent,
    /// Structural recursion on the parameter at `position`: the stage typing
    /// refines that arrow's domain, and every self-reference's argument there
    /// stands strictly below the fixpoint's stage.
    Staged
    {
        /// The arrow of the fixpoint's type the stage refines.
        position: StagedPosition,
    },
}

/// A stage the recursion typing mints.
///
/// It is the class of the values one fixpoint's self-reference may take,
/// placed by the fixpoint and the cases that minted it. A stage names nothing
/// outside the judgement that minted it; no wire byte carries one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StageId(usize);

impl From<usize> for StageId
{
    /// Preserve the stage's mint ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<StageId> for usize
{
    /// Read the stage's mint ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(stage: StageId) -> Self
    {
        stage.0
    }
}

/// How many steps below its anchor a bound stage stands: at least one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StageDepth(core::num::NonZeroU32);

impl StageDepth
{
    /// One step below: the bound `<s` of every stage strictly below `s`.
    pub const ONE: Self = Self(core::num::NonZeroU32::MIN);

    /// One step further below, saturating at the widest depth.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn deeper(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

impl From<StageDepth> for u32
{
    /// Read the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(depth: StageDepth) -> Self
    {
        depth.0.get()
    }
}

impl From<core::num::NonZeroU32> for StageDepth
{
    /// Preserve the number of steps, which is never zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: core::num::NonZeroU32) -> Self
    {
        Self(steps)
    }
}

/// The stage a value type is refined at: a stage of a structural fixpoint's
/// typing, unrelated to the meta and object levels of
/// [`stage::Stage`](crate::stage::Stage).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage
{
    /// The stage itself.
    At(StageId),
    /// Some stage at least `depth` steps below `anchor`: `<ι` at one step,
    /// the domain a fixpoint's self-reference takes.
    Below
    {
        /// The stage the bound lies below.
        anchor: StageId,
        /// How many steps below it, at least one.
        depth: StageDepth,
    },
}

/// Where a value stands in a fixpoint's stage order, as a refusal names it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Standing
{
    /// At the type a stage would refine, below no stage: the order's top.
    Top,
    /// At a stage, or below one.
    Staged(Stage),
}

/// The parameter a structural fixpoint recurses on: the arrow of its type the
/// stage refines, counted from the outermost at zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StagedPosition(usize);

impl From<usize> for StagedPosition
{
    /// Preserve the arrow's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<StagedPosition> for usize
{
    /// Read the arrow's ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: StagedPosition) -> Self
    {
        position.0
    }
}

/// Portable round-trip dialogues for closed universe-path translators.
///
/// # Specification
/// - provides: source and target traces in constructor-pattern order. Unit
///   anchors carry no arena identity; the kernel reconstructs every boundary.
///   Evidence participates in content identity but not certificate conversion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — artifact framing retains both ordered dialogue lists,
///   including empty dialogues and the full portable decision alphabet.
/// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct PathEvidence
{
    /// Backward after forward, once for every source constructor pattern.
    pub source:
        alloc::vec::Vec<alloc::vec::Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>>,
    /// Forward after backward, once for every target constructor pattern.
    pub target:
        alloc::vec::Vec<alloc::vec::Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>>,
}

/// One canonical unsigned word of portable path evidence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvidenceWord(pub u64);

impl TryFrom<EvidenceWord> for gandr_kernel_conversion_trace::ConversionDecision<()>
{
    type Error = crate::MalformedSite;

    /// Decode the portable decision alphabet, rejecting oversized premises.
    ///
    /// # Specification
    /// - ensures: accepts exactly the tagged decision words produced by
    ///   `decision_word`.
    /// - fails: `PathEvidence` for an unknown tag or a premise exceeding u32.
    /// - panics: none.
    ///
    /// # Errors
    /// Malformed path evidence.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unknown tags and oversized premise positions are
    ///   refused.
    /// - witness: `term::tests::evidence_words_reject_unknown_and_oversized_premises`
    #[inline]
    #[spec(ensures: |ret| {
        ret.is_ok() == (word.0 <= 0x0B_u64 || (0x0D_u64 ..= 0x10_u64).contains(&word.0) ||
            (word.0 & 0xFF_u64 == 0x0C_u64 && u32::try_from(word.0 >> 8_u32).is_ok()))
    })]
    fn try_from(word: EvidenceWord) -> Result<Self, Self::Error>
    {
        use gandr_kernel_conversion_trace::ConversionSide;
        let invalid = crate::MalformedSite::PathEvidence;
        Ok(match word.0 {
            0 => Self::ReduceLeft { redex: () },
            1 => Self::ReduceRight { redex: () },
            2 => Self::ConstShortcut { constant: () },
            3 => Self::Unfold { constant: () },
            4 => Self::Postpone { constant: () },
            5 => Self::Freeze {
                constant: (),
                side: ConversionSide::Left,
            },
            6 => Self::Freeze {
                constant: (),
                side: ConversionSide::Right,
            },
            7 => Self::EtaExpand {
                variable: (),
                side: ConversionSide::Left,
            },
            8 => Self::EtaExpand {
                variable: (),
                side: ConversionSide::Right,
            },
            9 => Self::Force { thunk: () },
            10 => Self::ComparedShared {
                left: (),
                right: (),
            },
            11 => Self::Decompose,
            value if value & 0xFF_u64 == 0x0C_u64 => {
                let position = u32::try_from(value >> 8_u32).map_err(|_error| invalid)?;
                Self::NegativeSubgoal {
                    position: position.into(),
                }
            },
            0x0D => Self::ReturnEta {
                side: ConversionSide::Left,
            },
            0x0E => Self::ReturnEta {
                side: ConversionSide::Right,
            },
            0x0F => Self::Reassociate {
                side: ConversionSide::Left,
            },
            0x10 => Self::Reassociate {
                side: ConversionSide::Right,
            },
            _ => return Err(invalid),
        })
    }
}

impl PathEvidence
{
    /// Stream the canonical evidence payload without allocating an image.
    ///
    /// # Specification
    /// - requires: nothing; evidence is still untrusted.
    /// - ensures: source then target, each prefixed by its dialogue count; each
    ///   dialogue has its decision count followed by tagged words.
    /// - provides: identical evidence content for wire and memo encoders.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — framing is a law of subsequent iterator
    ///   consumption; checking the opaque iterator here would consume or
    ///   materialize it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — persisted evidence retains dialogue boundaries,
    ///   order, sides and negative premise positions.
    /// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
    #[inline]
    pub fn words(&self) -> impl Iterator<Item = EvidenceWord> + '_
    {
        [&self.source, &self.target]
            .into_iter()
            .flat_map(|direction| {
                core::iter::once(EvidenceWord(u64::from(crate::wire::WireU64::from(
                    crate::wire::WireUsize::from(direction.len()),
                ))))
                .chain(direction.iter().flat_map(|dialogue| {
                    core::iter::once(EvidenceWord(u64::from(crate::wire::WireU64::from(
                        crate::wire::WireUsize::from(dialogue.len()),
                    ))))
                    .chain(dialogue.iter().copied().map(decision_word))
                }))
            })
    }
}

/// Encode one decision; only negative premises carry an integer payload.
///
/// # Specification
/// - requires: nothing; every decision belongs to the portable alphabet.
/// - ensures: distinct decisions have distinct words; anchors are unit-valued.
/// - provides: a closed, arena-independent decision alphabet.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — wire decoding distinguishes sides and premise positions.
/// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
#[spec(ensures: |ret| gandr_kernel_conversion_trace::ConversionDecision::<()>::try_from(ret) == Ok(decision))]
pub fn decision_word(
    decision: gandr_kernel_conversion_trace::ConversionDecision<()>
) -> EvidenceWord
{
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    EvidenceWord(match decision {
        ConversionDecision::ReduceLeft { .. } => 0,
        ConversionDecision::ReduceRight { .. } => 1,
        ConversionDecision::ConstShortcut { .. } => 2,
        ConversionDecision::Unfold { .. } => 3,
        ConversionDecision::Postpone { .. } => 4,
        ConversionDecision::Freeze {
            side: ConversionSide::Left,
            ..
        } => 5,
        ConversionDecision::Freeze {
            side: ConversionSide::Right,
            ..
        } => 6,
        ConversionDecision::EtaExpand {
            side: ConversionSide::Left,
            ..
        } => 7,
        ConversionDecision::EtaExpand {
            side: ConversionSide::Right,
            ..
        } => 8,
        ConversionDecision::Force { .. } => 9,
        ConversionDecision::ComparedShared { .. } => 10,
        ConversionDecision::Decompose => 11,
        ConversionDecision::NegativeSubgoal { position } => {
            (u64::from(u32::from(position)) << 8_u32) | 0x0C_u64
        },
        ConversionDecision::ReturnEta {
            side: ConversionSide::Left,
        } => 0x0D,
        ConversionDecision::ReturnEta {
            side: ConversionSide::Right,
        } => 0x0E,
        ConversionDecision::Reassociate {
            side: ConversionSide::Left,
        } => 0x0F,
        ConversionDecision::Reassociate {
            side: ConversionSide::Right,
        } => 0x10,
    })
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;

    use super::EvidenceWord;

    #[test]
    fn evidence_words_reject_unknown_and_oversized_premises()
    {
        for position in [0_u32, u32::MAX] {
            let word = EvidenceWord((u64::from(position) << 8_u32) | 0x0C_u64);
            assert_eq!(
                Ok(ConversionDecision::NegativeSubgoal {
                    position: position.into()
                }),
                ConversionDecision::try_from(word)
            );
        }
        for side in [ConversionSide::Left, ConversionSide::Right] {
            for decision in [
                ConversionDecision::ReturnEta { side },
                ConversionDecision::Reassociate { side },
            ] {
                assert_eq!(
                    Ok(decision),
                    ConversionDecision::try_from(super::decision_word(decision)),
                    "each bind law keeps its side across the wire"
                );
            }
        }
        for word in [
            0x11_u64,
            0xFF_u64,
            0x100_u64,
            0x0100_0000_000C_u64,
            u64::MAX,
        ] {
            assert_eq!(
                Err(crate::MalformedSite::PathEvidence),
                ConversionDecision::try_from(EvidenceWord(word)),
                "unknown tags and overflowing premises cannot be truncated into accepted evidence"
            );
        }
    }
}

/// Position of a constructor within one nominal declaration.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstructorTag(usize);

impl From<usize> for ConstructorTag
{
    /// Preserve the constructor ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ConstructorTag> for usize
{
    /// Read the constructor ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: ConstructorTag) -> Self
    {
        tag.0
    }
}

/// Position of a component within one product type, counting from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Component(usize);

impl From<usize> for Component
{
    /// Preserve the component ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<Component> for usize
{
    /// Read the component ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: Component) -> Self
    {
        component.0
    }
}

/// Position of a summand within one sum type, counting from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Summand(usize);

impl From<usize> for Summand
{
    /// Preserve the summand ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<Summand> for usize
{
    /// Read the summand ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(summand: Summand) -> Self
    {
        summand.0
    }
}

impl From<Side> for Summand
{
    /// The summand a side names in a binary sum: the left summand first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(side: Side) -> Self
    {
        match side {
            Side::Left => Self(0),
            Side::Right => Self(1),
        }
    }
}

impl TryFrom<Summand> for Side
{
    type Error = Summand;

    /// The side that names a summand of a binary sum.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The summand itself, when it is neither the first nor the second.
    #[inline]
    fn try_from(summand: Summand) -> Result<Self, Self::Error>
    {
        match summand.0 {
            0 => Ok(Self::Left),
            1 => Ok(Self::Right),
            _ => Err(summand),
        }
    }
}

/// Position of a field within one constructor's field list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldPosition(usize);

impl From<usize> for FieldPosition
{
    /// Preserve the field ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<FieldPosition> for usize
{
    /// Read the field ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: FieldPosition) -> Self
    {
        position.0
    }
}

/// Position of a classifier within one declaration's parameter telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterPosition(usize);

impl From<usize> for ParameterPosition
{
    /// Preserve the parameter ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ParameterPosition> for usize
{
    /// Read the parameter ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: ParameterPosition) -> Self
    {
        position.0
    }
}

/// Where a data declaration's occurrence walk found a refused self
/// occurrence or a reference outside its block.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OccurrenceSite
{
    /// A classifier of the parameter telescope.
    Parameter(ParameterPosition),
    /// One field of one constructor.
    Field
    {
        /// The constructor.
        tag: ConstructorTag,
        /// The field within it.
        field: FieldPosition,
    },
}

/// An exact UTF-8 record label; ordering is lexical, without normalization.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldLabel(alloc::string::String);

impl From<alloc::string::String> for FieldLabel
{
    /// Preserve the label's exact text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: alloc::string::String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for FieldLabel
{
    /// Borrow the label text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}
