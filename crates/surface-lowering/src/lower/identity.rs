//! Element identity in the lowering: the path type `Path(A, a, b)`, its
//! reflexivity `here(a)`, function extensionality `funext(f, g)`, universe
//! equivalence `equiv(f, g)`, the product of two universe paths
//! `pathProduct(p, q)`, transport `transport(\X. T, p, v)` and its
//! dependent form `transport(M, p, z₀, q, v)`, and `back`, `then` and `cong`,
//! each unfolded to the transport it derives; and the native list's
//! constructors `nil` and `cons(h, t)`, the recursive motive transport first
//! moves along a universe path.
//!
//! # Endpoints are values, and a computation is the value it returns
//!
//! A path type's endpoints, and the point of `here`, are terms the grammar
//! parses as expressions, and the lowering reads them where a value is read.
//! A computation standing there, or anywhere under one where a value is read
//! — `mul(x, y)`, `n + 1`, the inner call of `mul(mul(x, y), z)` — is not
//! refused: it reaches the position as the value it returns, a compound
//! endpoint the checker compares by what it computes and admits only when
//! it is pure. The alternative, refusing every endpoint that is not a value,
//! is the reading that made `Path(Integer, mul(neutral, x), x)` unwritable; a
//! statement the author must name first, `run m <- mul(neutral, x)`, cannot
//! stand in a type. Reversal: an endpoint language with its own let, which
//! would bind the computation once and reuse it in both the type and the
//! body.
//!
//! An endpoint is a term inside a type, so a parameter it names is read at
//! its index in the type's telescope and makes the arrow binding it
//! dependent, as a parameter a later type decodes does. The point of `here`
//! is a term of the body and reads its parameters there.
//!
//! # The identity vocabulary is names nothing else binds
//!
//! `here`, `funext`, `equiv`, `pathProduct`, `transport`, `back`, `cong`,
//! `bisim`, `sim`, `stay`, `forward`, `arrow`, `flowProduct`, `ride` and
//! `recorded` are spelled as ordinary calls and resolved after every binder
//! and every earlier declaration, so a parameter or a definition of the same
//! name shadows them, as it shadows a prelude primitive; `then` is the
//! grammar's own infix tile, and `Flow` a type head resolved the same way.
//! Reserving the names outright was the alternative; it would break every
//! program that already binds one. Reversal: a namespace for the identity
//! vocabulary, `Path.here`, once the namespaces carry formers rather than
//! primitives. The native list's `nil` and `cons` resolve the same way, the
//! spellings the printer already writes them with; a list literal `[a, b]`,
//! which the grammar parses, was the alternative, declined because a cell over
//! a tail that is no literal has no literal spelling to print back.
//!
//! `funext(f, g)` and `equiv(f, g)` stand as values, as `here` does, and read
//! both functions as values; the checker synthesises the path type from the
//! first and decides it by computation (`gandr_core_checker`'s funext and
//! equiv rules). Univalence at a stratum, `ua[n, k](a, b, f, g)`, is the same
//! kind of name with its stratum in the head; [`super::ua`] lowers it.
//!
//! `pathProduct(p, q)` stands as a value over two paths read as values: the
//! kernel's native product of universe paths, which relates the eager pairs of
//! the two paths' endpoints, nested to the right as `ua[n, k]` nests its
//! telescope. Every name of the derived form then has a spelling, so the
//! degree-one derivation can be written by hand and compared with it.
//! `flowProduct(p, q)` is its directed twin over two universe flows, the
//! kernel's own former, so the degree-one universe flow over a telescope has a
//! spelling too.
//!
//! # `transport` states its motive
//!
//! `transport(\X. T, p, v)` moves `v : T[a/X]` along `p : Path(A, a, b)` to
//! `T[b/X]`. Its motive is written as a static abstraction whose body is the
//! family over the path's carrier, so `\X. List(X)` over a universe path is
//! `y. List(El y)`; the transport stands as a computation. A motive written
//! any other way is refused as unannotated. The alternative, inferring the
//! motive from the expected type, is higher-order unification, which the
//! checker does not do. Reversal: a checker that elaborates the motive from
//! the operand's and the answer's types.
//!
//! # A derived operation synthesises its path at the words
//!
//! `back(p)`, `p then q` and `cong(f, p)` are transports whose motive names
//! the carrier and the endpoint that stays fixed (`gandr_core_term::identity`).
//! Where the position answers a written path type — the function's result or
//! the match's answer, `-F Path(A, a, b)` or `Path(A, a, b)` — the lowering
//! reads both off it, relocated to where the operation stands. Anywhere else,
//! in a type, a constant's value, a call's argument or a thunk, the operation
//! synthesises them from its operands: the loop, a word of the loop's words,
//! or another derived operation stands at `Path(F, x, x)` or at the path type
//! recorded against it, `F` the family and `x` the point its words spell, so
//! `back(p)` at `p : Path(A, a, b)` stands at `Path(A, b, a)`, `p then q` at
//! `Path(A, a, c)` and `cong(f, p)` at `Path(B, ⟨f a⟩, ⟨f b⟩)`, `B` the result
//! type `f`'s definition writes under no binder of its telescope, or the
//! codomain of the map its signature states. An operation
//! whose motive's path — `back`'s and `cong`'s path, `then`'s first — is read
//! no such way, or whose function did not lower, is refused as unannotated,
//! and `cong` at a constructor as [`FragmentBoundary::NotAFunction`]. The
//! operation then stands as the value its pure transport returns, so it is an
//! endpoint, a constant's value or an operand without a run. No core node is
//! added: the transport is the one the answer would have given. The kernel
//! runs a returned path before transporting along it, as the evaluator reads
//! every returned value, so an operation over another replays. The
//! alternative, an annotated spelling only — the path type written where the
//! operation stands — repeats what the words already state, and is the
//! spelling a function answering its own path type still takes. Reversal: a
//! word whose endpoints are not spelled, a cell between distinct points,
//! gives no point to read, and its operations need the written answer again.
//!
//! # A dependent `transport` reads its motive as a thunked telescope
//!
//! Five operands, `transport(+U ((y : A) -> (z : B) -> -F C), p, z₀, q, v)`,
//! spell the transport whose motive depends on the path's endpoint `y` and on
//! an element `z` of the family over it (`gandr_core_term::identity`):
//! `p : Path(A, a, b)`, `z₀ : B[a]`, `q` an identity over `p` from `z₀`
//! transported along it to some `z₁ : B[b]`, and `v : C[a, z₀]`; it returns
//! `C[b, z₁]`. The motive is read as a value type, the thunk of the
//! computation type `Π (y : A). Π (z : B). -F C` that the telescope alias
//! `(y : A, z : B) => C` abbreviates, and the transport takes the computation
//! type under the thunk. The alias itself cannot stand as an argument, where
//! the grammar reads `(` as a tuple or an annotation, so the motive is written
//! in the spelling the alias stands for. An entry written as a plain arrow,
//! `+U (A -> B -> -F C)`, is made dependent, its codomain moved under the
//! binder it then stands under. Any other motive is minted as written, a value
//! type other than a thunk as the returner over it, and the checker refuses
//! its shape by name. The alternative, a binder form of its own for motives,
//! would duplicate the telescope the dependent arrow already reads; the one
//! binder transport's static abstraction, `\X. T`, binds a type, not a point
//! and an element. Reversal: a type-level lambda in argument position would
//! write the motive as the family it is. `J` is not a primitive: it is this
//! transport in the singleton,
//! `transport(+U ((y : A) -> (q : Path(A, a, y)) -> -F C), p, here(a),
//! here(p), d)`, written as an ordinary definition.
//!
//! # Reflexivity is not a pattern
//!
//! A path is used by transport and by nothing else. `here` written as a
//! pattern would be a second eliminator, and matching a path whose endpoints
//! are fixed against it is axiom K, which univalence refutes; it is refused
//! as [`LoweringRefusal::WithoutK`]. Reversal: none in this vocabulary — `J`
//! is derived as transport in the singleton, which is what a match on `here`
//! with a free endpoint would mean, and is written with `transport`.
//!
//! # Session identity names the engine's two relations
//!
//! `bisim(A, B)` and `sim(A, B)` read two session codes as values and stand
//! as values of `Path(Type, A, B)` and of the directed `Flow(Type, A, B)`;
//! `gandr_core_checker`'s flow rules decide both by the session engine and
//! record the decisions the kernel replays. `Flow(A, a, b)` is read as
//! `Path(A, a, b)` is. `stay(a)` is the identity flow, `f then g` composes
//! two flows where the position answers a written flow type, and
//! `ride(\X. T, f, v)` moves `v` along `f` in the family its static
//! abstraction states, as `transport` does. The alternatives — an infix
//! `A <: B`, statements over translators as `equiv` takes — are recorded with
//! the checker's rules.
//!
//! # A flow between data is one translator
//!
//! `forward(f)` reads one closed translator as a value and stands as a value
//! of `Flow(Type, A, B)`, `f : U(A → F B)`; the checker decides it by running
//! `f` at every input pattern of `A`. `arrow(d, c)` reads two flows, `d :
//! Flow(Type, A', A)` into the argument and `c : Flow(Type, B, B')` out of the
//! result, and stands as a value of `Flow(Type, ⌜U(A → F B)⌝, ⌜U(A' → F
//! B')⌝)`: the domain flow is written first and runs against the function, as
//! the arrow's own variance reads. The spelling follows `equiv(f, g)`, one call
//! per statement; the alternatives, `Flow_U(A, B)` taking a translator or an
//! infix `d -> c` over flows, would overload a type head or the arrow tile.
//! Reversal: a type-directed `forward` that reads its endpoints off the
//! position's answer, once the checker elaborates against expected types.
//!
//! `back(f)` where the position answers a written flow type is the symmetry
//! ride `ride(\y. Flow(A, y, b), f, stay(b))`
//! (`gandr_core_term::identity::back_flow`), which the checker refuses by
//! its motive; `cong` has no flow reading.
//!
//! A statement names its protocols bare, as type members of the module it is
//! written in, which a term position reads as the types they state: the term
//! grammar projects a module only onto a lowercase member, so a protocol
//! another module declares is aliased into the statement's own module first.
//! Reversal: a term projection onto a type member.
//!
//! `Run(S)` is a unary type former over a session code, which it reads as a
//! value, and `recorded(m₀, …, mₙ)` a run's literal: each move is `sent(v)`,
//! `received(v)`, `selected(l)`, `offered(l)` or `closed`, read by its shape
//! rather than resolved, a payload read as a value and a label as the name it
//! is written as. The moves are calls so a run prints back as written; a
//! nominal move type the prelude declares was the alternative, which needs a
//! constructor per payload type. Reversal: a run type whose moves are data
//! the program declares.
//!
//! # Three relations between types abbreviate a record or a flow
//!
//! Beside `Path(A, a, b)` and `Flow(Type, A, B)`, three infix formers relate
//! two types, in one band just above the arrow:
//!
//! - `A ≅ B`, also written `Iso(A, B)`, the quasi-inverse: the record `#{to :
//!   +U (A -> -F B), back : +U (B -> -F A), sect : (a : A) => Path(A,
//!   back(to(a)), a), retr : (b : B) => Path(B, to(back(b)), b)}`.
//! - `A ≃ B`, also written `A <~> B`, the equivalence as the bi-invertible map:
//!   `#{to : +U (A -> -F B), linv : #{g : +U (B -> -F A), sect : (a : A) =>
//!   Path(A, g(to(a)), a)}, rinv : #{h : +U (B -> -F A), retr : (b : B) =>
//!   Path(B, to(h(b)), b)}}`.
//! - `A ⇝ B`, also written `A ~~> B`, the flow `Flow(Type, A, B)` between two
//!   codes at the universe a bare `Type` names; `forward(f)` introduces it.
//!
//! Each mints exactly the core its written record or flow lowers to, so a
//! value of the one is a value of the other and the kernel gains no node. The
//! origin table records the relation against the type, and the printer
//! spells the type back as the relation. The type is located at the relation
//! as written; every node below it — the fields' types, the terms the round
//! trips read, the flow's universe — at the relation as an insertion, since
//! the source writes none of them, so a reader pointing at the relation is
//! answered with the relation. A pattern at a parameter of either record
//! type splits the record, by position or by label, the equivalence's two
//! inverses each a record of its own.
//!
//! The equivalence is the bi-invertible map (_Homotopy Type Theory_, § 4.3),
//! which is also the isomorphism simplicial homotopy type theory states for a
//! Segal type (`isIso`; Gratzer, Weinberger and Buchholtz, _Directed
//! univalence in simplicial homotopy type theory_, arXiv:2407.09146,
//! Definition 2.7 and Remark 2.9), so a directed reading takes the same
//! record. The alternative was contractible fibres, `#{to, fibres : (b : B)
//! => <the fibre over b is contractible>}`. From a quasi-inverse, its
//! contraction needs the half-adjoint coherence and path algebra under a
//! transport's motive, and the identity fragment reads neither: the motive's
//! composite refuses as needing a type annotation. Both records are
//! propositions, which the lowering does not check. Reversal: contractible
//! fibres once the h-level ladder supplies the coherence, the record changing
//! here and in the corpus's `isoToEquiv`.
//!
//! The quasi-inverse is no proposition, so it is a former of its own rather
//! than a second spelling of the equivalence; `isoToEquiv` and `equivToIso`
//! relate the two in the corpus. Each former has one glyph, and its ASCII
//! spelling is an alias the mold normalises, so the printer never chooses.
//! `A ⇝ B` has no record: under directed univalence the structure of a hom
//! between types is the function itself (op. cit., Definition 1.2).

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::identity::Relation;
use gandr_core_term::identity::bi_invertible;
use gandr_core_term::identity::quasi_inverse;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Carrier;
use super::Code;
use super::Former;
use super::Function;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::Stretch;
use super::Universe;
use super::arguments;
use super::arity::Dependent;
use super::arity::Place;
use super::closed;
use super::exhausted;
use super::exits::record_copies;
use super::lowered;
use super::native::Answer;
use super::native::record_since;
use super::native::rooted;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::Piece;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::module::Half;
use crate::module::Operand;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::Telescope;
use crate::resolve::TypeFormer;
use crate::resolve::type_former;

#[cfg(test)]
pub(super) mod tests;

/// Reflexivity's spelling, which no pattern may take.
pub(super) const HERE: &str = "here";

/// The inverse's spelling: of a path, and of a loop where a word's letter is
/// written.
pub(super) const BACK: &str = "back";

/// The empty native list's spelling, a name resolved after every binder and
/// earlier declaration.
pub(super) const NIL: &str = "nil";

/// The directed identity type's head, resolved after every binder and
/// earlier declaration at three arguments.
pub(super) const FLOW: &str = "Flow";

/// The quasi-inverse's head, `Iso(A, B)`, the spelling of `A ≅ B` as an
/// application, resolved after every binder and earlier declaration at two
/// arguments.
pub(super) const ISO: &str = "Iso";

/// A recorded run's close, a move written as a bare name.
const CLOSED: &str = "closed";

/// The record a relation between types abbreviates, or one of the records
/// nested in it, as a pattern splits it: its labels in written order and
/// whether each link binds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Layout
{
    /// `A ≅ B`: `#{to, back, sect, retr}`.
    Isomorphism,
    /// `A ≃ B`: `#{to, linv, rinv}`, `linv` and `rinv` records of their own.
    Equivalence,
    /// The equivalence's left inverse `linv`: `#{g, sect}`.
    LeftInverse,
    /// The equivalence's right inverse `rinv`: `#{h, retr}`.
    RightInverse,
}

impl Layout
{
    /// The record's labels, in written order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn fields(self) -> impl ExactSizeIterator<Item = SurfaceName<'static>>
    {
        let labels: &'static [&'static str] = match self {
            Self::Isomorphism => &["to", "back", "sect", "retr"],
            Self::Equivalence => &["to", "linv", "rinv"],
            Self::LeftInverse => &["g", "sect"],
            Self::RightInverse => &["h", "retr"],
        };
        labels.iter().map(|&label| SurfaceName::from(label))
    }

    /// Whether each field but the last binds a later one: every map does,
    /// a round trip and an inverse do not.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn links(self) -> &'static [Dependent]
    {
        match self {
            Self::Isomorphism => &[Dependent(true), Dependent(true), Dependent(false)],
            Self::Equivalence => &[Dependent(true), Dependent(false)],
            Self::LeftInverse | Self::RightInverse => &[Dependent(true)],
        }
    }

    /// The record nested at `place`, when the field there is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the equivalence's left inverse at its second field and its
    ///   right inverse at its third; the other-former absence for every other
    ///   field.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern at an equivalence splits both inverses.
    /// - witness: `lower::identity::tests::a_pattern_at_a_relation_splits_its_record`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || self == Self::Equivalence)]
    pub(super) fn inner(
        self,
        place: Place,
    ) -> Maybe<Self, related::Absent>
    {
        match (self, place.0) {
            (Self::Equivalence, 1_usize) => Maybe::Present(Self::LeftInverse),
            (Self::Equivalence, 2_usize) => Maybe::Present(Self::RightInverse),
            _ => Maybe::Absent(related::Absent::Otherwise),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a type states no relation's record.
    pub(super) mod related {
        /// The type is no equivalence or quasi-inverse.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The type is planned as another former, or as a flow.
            Otherwise,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a call's head names no identity operation.
    pub mod spelled {
        /// The head is not one of the identity operations' names, free.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The head is no bare name or `ua[n, k]` instantiation, spells
            /// another name, or names a binder or an earlier declaration that
            /// shadows the operation.
            Unspelled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a derived operation's path has no type read where it stands.
    pub mod synthesised {
        /// The path's type is not read off its form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The path is no word, no loop and no derived operation whose
            /// own path type is read: a variable, a call, a reflexivity.
            Unread,
        }
    }
}

/// An identity operation a call's head spells.
///
/// # Specification
/// - ensures: reflexivity, function and universe extensionality, the product of
///   two universe paths, transport in a one-binder motive or a telescope, the
///   two derived operations, the native list cell, the two session statements,
///   the identity flow, the forward flow of a translator, the function flow of
///   two boundary flows, a ride along a flow and a recorded run, spelled as
///   calls.
/// - executable: none — a tag holds no head to check its spelling against.
///
/// # Adequacy
/// - hypothesis: L3 — each spelling lowers to its own former.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
/// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
/// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
/// - witness: `lower::identity::tests::directed_statements_lower_to_their_formers`
/// - witness: `lower::identity::tests::a_path_product_lowers_to_its_former`
/// - witness: `lower::identity::tests::a_flow_product_lowers_to_its_former`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Operation
{
    /// `here(a)`.
    Here,
    /// `funext(f, g)`.
    Funext,
    /// `equiv(f, g)`.
    Equiv,
    /// `ua(e)`.
    Univalence,
    /// `pathProduct(p, q)`.
    PathProduct,
    /// `transport(\X. T, p, v)`.
    Transport,
    /// `back(p)`.
    Back,
    /// `cong(f, p)`.
    Cong,
    /// `cons(h, t)`.
    Cons,
    /// `bisim(A, B)`.
    Bisim,
    /// `sim(A, B)`.
    Sim,
    /// `stay(a)`.
    Stay,
    /// `forward(f)`.
    Forward,
    /// `arrow(d, c)`.
    Arrow,
    /// `flowProduct(p, q)`.
    FlowProduct,
    /// `ride(\X. T, f, v)`.
    Ride,
    /// `recorded(m₀, …, mₙ)`.
    Recorded,
}

/// The identity operations a call's head spells, by name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each operation once, under its surface name.
/// - provides: the table [`Lowerer::identity_head`] resolves against.
/// - fails: never.
/// - panics: none.
/// - executable: none — the specification attribute does not support const
///   items; the head's reader checks the spelling it resolved.
///
/// # Adequacy
/// - hypothesis: L3 — every row is spelled by a witness.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
/// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
/// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
/// - witness: `lower::identity::tests::directed_statements_lower_to_their_formers`
/// - witness: `lower::identity::tests::a_path_product_lowers_to_its_former`
/// - witness: `lower::identity::tests::a_flow_product_lowers_to_its_former`
const SPELLED: [(&str, Operation); 17] = [
    (HERE, Operation::Here),
    ("funext", Operation::Funext),
    ("equiv", Operation::Equiv),
    ("ua", Operation::Univalence),
    ("pathProduct", Operation::PathProduct),
    ("transport", Operation::Transport),
    (BACK, Operation::Back),
    ("cong", Operation::Cong),
    ("cons", Operation::Cons),
    ("bisim", Operation::Bisim),
    ("sim", Operation::Sim),
    ("stay", Operation::Stay),
    ("forward", Operation::Forward),
    ("arrow", Operation::Arrow),
    ("flowProduct", Operation::FlowProduct),
    ("ride", Operation::Ride),
    ("recorded", Operation::Recorded),
];

/// A derived operation's written operands.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation transports along its own path.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Derivation
{
    /// `back(path)`.
    Back
    {
        /// The path reversed.
        path: NodeIndex,
    },
    /// `first then second`.
    Then
    {
        /// The path composed first.
        first: NodeIndex,
        /// The path composed second, the one transported along.
        second: NodeIndex,
    },
    /// `cong(function, path)`.
    Cong
    {
        /// The map applied along the path.
        function: NodeIndex,
        /// The path mapped.
        path: NodeIndex,
    },
}

/// A derived operation as the classification planned it: its operands, how
/// its motive is read, and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the stance is a written path type, under a returner or not, or
///   the synthesis from the operands [`Lowerer::derive`] admitted.
/// - executable: none — the plan holds no tree to check its stance against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation's motive is read off its answer, or off
///   its operands where no answer is written.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Derived
{
    /// The operation and its operands.
    derivation: Derivation,
    /// Where the motive's carrier and fixed endpoint are read.
    stance: Stance,
    /// The frame the operation stands under.
    frame: Frame,
}

/// Where a derived operation reads its motive's carrier and fixed endpoint.
///
/// # Specification
/// - ensures: the path type the position answers, or the operands' own path
///   types.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — an answered and a synthesised operation each mint their
///   own motive.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
/// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Stance
{
    /// The path type the position answers.
    Answered(Answer),
    /// The operands' path types, the position answering none, with what the
    /// classification read them off where their own form spells none.
    Synthesised(Synthesis, Typings),
}

/// What a synthesised derived operation's two paths read their types off
/// where their own form spells none, as [`Lowerer::refuse_unsynthesised`]
/// read it: kept in the plan, because the mint sweep consumes the operands'
/// plans before it reaches the operation.
///
/// # Specification
/// - ensures: the motive's path — `back`'s and `cong`'s path, `then`'s first —
///   and `then`'s second, each a parameter or a call, or nothing.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — an operation over a parameter and over a call each mint
///   their path type.
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
struct Typings
{
    /// The motive's path.
    transported: Option<Typed>,
    /// `then`'s second path.
    onward: Option<Typed>,
}

/// What a synthesised derived operation reads besides its paths' types.
///
/// # Specification
/// - ensures: nothing for `back` and `then`; for `cong`, the written result
///   type of the function it maps by, or, for a parameter, its written type
///   until [`Lowerer::refuse_unsynthesised`] reads its arrow's codomain, and
///   then that codomain with the frame it is carried from.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — `cong` reads its codomain off its function, the others
///   off their paths alone.
/// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Synthesis
{
    /// The paths' types alone: `back` and `then`.
    Paths,
    /// The function's result type as its definition writes it, read under
    /// `frame`: `cong`.
    Mapped
    {
        /// The result type.
        codomain: Codomain,
        /// The frame the result type is read under.
        frame: Frame,
    },
    /// A parameter's written type, the thunk of the arrow whose codomain
    /// `cong` reads once every node is classified.
    Thunked
    {
        /// The binder's written type.
        declared: NodeIndex,
    },
    /// A declaration's written signature, which states the map whose
    /// codomain `cong` reads once every node is classified, as it reads a
    /// function definition's result.
    Stated
    {
        /// The signature's written type.
        declared: NodeIndex,
    },
    /// The codomain of the arrow a parameter's written type thunks, read under
    /// `frame`, the frame the parameter's type is read under: `cong` at a
    /// bound map. Every binder of `frame` is in scope where the operation
    /// stands, so the codomain is carried there.
    Bound
    {
        /// The codomain.
        codomain: Codomain,
        /// The frame the parameter's type, and so the codomain, is read
        /// under.
        frame: Frame,
        /// The frame the map's use stands under in a type; none in a body.
        in_type: Option<Frame>,
    },
}

/// Where a `cong` reads the type its function returns.
///
/// # Specification
/// - ensures: a computation type returns its returner's result; a value
///   function's codomain is that result itself, the alias `A => B` standing for
///   `+U (A -> -F B)`.
/// - executable: none — a tag holds no tree to check its reading against.
///
/// # Adequacy
/// - hypothesis: L3 — `cong` by a parameter stated as `+U (A -> -F B)` and as
///   `A => B` reads the same carrier.
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
/// - witness: `lower::identity::tests::cong_reads_a_map_stated_as_a_value_function_791`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Codomain
{
    /// A written computation type, `-F B`: a definition's result or a thunked
    /// arrow's codomain.
    Returner(NodeIndex),
    /// The codomain `B` of a value function `A => B`.
    Returned(NodeIndex),
}

impl Codomain
{
    /// The codomain's syntax node.
    ///
    /// # Specification
    /// trivial.
    const fn node(self) -> NodeIndex
    {
        match self {
            Self::Returner(node) | Self::Returned(node) => node,
        }
    }
}

/// The path type a derived operation minted at: its carrier and its two
/// endpoints, read where the operation stands.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the operation's transport returns an element of `Path(carrier,
///   left, right)`.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a synthesised operation over another reads the inner
///   one's path type.
/// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Identity
{
    /// The path's carrier.
    carrier: ValueTypeId,
    /// The path's left endpoint.
    left: ValueId,
    /// The path's right endpoint.
    right: ValueId,
}

/// What a derived operation's path operand reads its type off when its own
/// form spells none.
///
/// # Specification
/// - ensures: the node of the written type the path's type is read from.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter and a call each mint the path type they
///   state.
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Typed
{
    /// A parameter, by its binder's written type: named in a body, or in a
    /// type under the frame it is read from.
    Parameter
    {
        /// The binder's written type.
        declared: NodeIndex,
        /// The frame a type naming the binder reads it under; nothing in a
        /// body.
        in_type: Option<Frame>,
    },
    /// A call, by its function's written result.
    Called(Callee),
}

impl Typed
{
    /// The written type's node.
    ///
    /// # Specification
    /// trivial.
    const fn node(self) -> NodeIndex
    {
        match self {
            Self::Parameter { declared, .. } => declared,
            Self::Called(callee) => callee.result,
        }
    }
}

/// A call whose function writes its result: what the call's path type is
/// instantiated from.
///
/// # Specification
/// - ensures: the function's parameters, its arity, the parameter it stages
///   when it recurses, its written result and whether that is a returner, the
///   arguments the call applies, and whether it is a recursive call's descent.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — a call of a definition, of a signature and a recursive
///   call each mint their result at their arguments.
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Callee
{
    /// The function's binders, in the lowerer's parameter store: a tail's
    /// parameters or a telescope's entries; none for a plain value function.
    parameters: Stretch,
    /// How many arguments the function takes.
    arity: usize,
    /// The staged parameter's position, when a recursive tail binds its own
    /// name between that parameter and the ones before it.
    recursive: Option<usize>,
    /// The written result: a tail's computation type, or a signature's
    /// value type.
    result: NodeIndex,
    /// Whether the result is a computation type, a returner over the path.
    returned: bool,
    /// The arguments the call applies, in the lowerer's operand store: every
    /// one, or a descent's from the staged parameter's on.
    arguments: Stretch,
    /// Whether the head is a recursive call's descent claim, which passes
    /// the parameters before the staged one as themselves.
    descends: bool,
}

/// The carrier and the endpoints of the path type `ty`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the path type's carrier and endpoints.
/// - fails: [`synthesised::Absent::Unread`] for any other type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Lowerer::identity_of`].
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(read) => arena.value_type(ty) == Some(&ValueType::Path { carrier: read.carrier, left: read.left, right: read.right }),
    | Maybe::Absent(_) => true,
})]
fn path_identity(
    arena: &CoreArena,
    ty: ValueTypeId,
) -> Maybe<Identity, synthesised::Absent>
{
    match arena.value_type(ty) {
        Some(&ValueType::Path {
            carrier,
            left,
            right,
        }) => Maybe::Present(Identity {
            carrier,
            left,
            right,
        }),
        _ => Maybe::Absent(synthesised::Absent::Unread),
    }
}

/// A node of the spine [`as_endpoint`] rewrites.
///
/// # Specification
/// - ensures: a value or a computation of the arena.
/// - executable: none — an id holds no arena to check it against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`as_endpoint`].
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spine
{
    /// A value along the spine.
    Value(ValueId),
    /// A computation along the spine.
    Computation(ComputationId),
}

/// `value` as an endpoint: each computation written where a value is read,
/// along `value` and the spines of the computations it returns, read as the
/// value it returns.
///
/// # Specification
/// - requires: `value` is live in `arena`.
/// - ensures: `value` itself when it holds no nested computation along its
///   spine; otherwise a copy with each [`Value::Nested`] along the spine of
///   applications and forces read as [`Value::Returned`] over the same rewrite
///   of its computation, each node rebuilt only when a node under it changed.
/// - provides: a call's argument, which a body reads as a run, carried into the
///   path type the call answers, where it is an endpoint: the same node would
///   be a run the type cannot enclose.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: each node is pushed once unexpanded and once expanded, and an
///   unexpanded node pushes only the nodes directly under it, of a finite term.
/// - measure: twice the nodes along `value`'s spine, less the pops so far.
///
/// # Adequacy
/// - hypothesis: L3 — a call whose arguments are calls, its path type read at
///   those arguments.
/// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
#[spec(ensures: |ret| arena.value(ret).is_some() || ret == value)]
fn as_endpoint(
    arena: &mut CoreArena,
    value: ValueId,
) -> ValueId
{
    use alloc::collections::BTreeMap;
    let mut values: BTreeMap<ValueId, ValueId> = BTreeMap::new();
    let mut computations: BTreeMap<ComputationId, ComputationId> = BTreeMap::new();
    let mut pending = alloc::vec![(Spine::Value(value), false)];
    while let Some((node, expanded)) = pending.pop() {
        if !expanded {
            pending.push((node, true));
            match node {
                Spine::Value(at) => {
                    if let Some(&(Value::Nested(computation) | Value::Returned(computation))) =
                        arena.value(at)
                    {
                        pending.push((Spine::Computation(computation), false));
                    }
                },
                Spine::Computation(at) => match arena.computation(at) {
                    Some(&Computation::Application(head, argument)) => {
                        pending.push((Spine::Value(argument), false));
                        pending.push((Spine::Computation(head), false));
                    },
                    Some(&Computation::Force(forced)) => {
                        pending.push((Spine::Value(forced), false));
                    },
                    _ => {},
                },
            }
            continue;
        }
        match node {
            Spine::Value(at) => {
                let read = match arena.value(at) {
                    Some(&Value::Nested(computation)) => {
                        let spine = computations
                            .get(&computation)
                            .copied()
                            .unwrap_or(computation);
                        arena.value_returned(spine)
                    },
                    Some(&Value::Returned(computation)) => {
                        match computations.get(&computation).copied() {
                            Some(spine) if spine != computation => arena.value_returned(spine),
                            Some(_) | None => at,
                        }
                    },
                    _ => at,
                };
                let _held = values.insert(at, read);
            },
            Spine::Computation(at) => {
                let read = match arena.computation(at) {
                    Some(&Computation::Application(head, argument)) => {
                        let spine = computations.get(&head).copied().unwrap_or(head);
                        let read = values.get(&argument).copied().unwrap_or(argument);
                        if spine == head && read == argument {
                            at
                        }
                        else {
                            arena.computation_application(spine, read)
                        }
                    },
                    Some(&Computation::Force(forced)) => {
                        let read = values.get(&forced).copied().unwrap_or(forced);
                        if read == forced {
                            at
                        }
                        else {
                            arena.computation_force(read)
                        }
                    },
                    _ => at,
                };
                let _held = computations.insert(at, read);
            },
        }
    }
    values.get(&value).copied().unwrap_or(value)
}

/// The identity type a derived operation stands at where it is minted, as
/// far as it is read: the answer's whole, or what its operands give.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the right endpoint is absent only for a synthesised `then` whose
///   second path's type is not read.
/// - executable: none — the ids hold no arena to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Identity`].
/// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Stood
{
    /// A path type or a flow type.
    answered: Answered,
    /// The carrier.
    carrier: ValueTypeId,
    /// The left endpoint, a flow's source.
    left: ValueId,
    /// The right endpoint, a flow's target, when it is read.
    right: Maybe<ValueId, synthesised::Absent>,
}

/// The identity type a derived operation's position answers.
///
/// # Specification
/// - ensures: a written path type or a written flow type.
/// - executable: none — a tag holds no tree to check its answer against.
///
/// # Adequacy
/// - hypothesis: L3 — `then` under each answer plans its own former.
/// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Answered
{
    /// `Path(A, a, b)`.
    Path,
    /// `Flow(A, a, b)`.
    Flow,
}

/// A dependent transport's written operands and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each operand is the syntax node it was written as.
/// - executable: none — the coordinates hold no tree to check them against.
///
/// # Adequacy
/// - hypothesis: L3 — each operand reaches its own slot of the transport.
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Transported
{
    /// The motive, written as a telescope.
    motive: NodeIndex,
    /// The path transported along.
    path: NodeIndex,
    /// The family element at the path's source.
    start: NodeIndex,
    /// The identity over the path.
    over: NodeIndex,
    /// The value transported.
    value: NodeIndex,
    /// The frame the transport stands under.
    frame: Frame,
}

impl<'source> Lowerer<'_, 'source>
{
    /// Classify a path type, `Path(A, a, b)`, or `Path(Type, A, B)` at a
    /// universe its own tiles spell.
    ///
    /// # Specification
    /// - requires: `site` is a path type in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the form stands as a value type and is planned over its
    ///   carrier and its two endpoints, each endpoint read as a value standing
    ///   inside a type, all under the form's own frame. A written carrier is
    ///   read as a value type. A universe carrier is the universe its tiles
    ///   spell, and its endpoints, written at the type sort, are read as the
    ///   codes of the types they spell.
    /// - provides: element identity's type former.
    /// - fails: yields the wrong-sort refusal where no value type is read, and
    ///   a misplaced-tile or extra-operand fault for a form out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed path type and one whose endpoint is a
    ///   computation, each read back out of the arena; a path at a universe
    ///   between a sum and a session type reads each endpoint as its code.
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    /// - witness: `lower::identity::tests::a_path_at_a_universe_reads_its_endpoints_as_types_402`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Path(carrier, left, right))
                        if match carrier {
                            Carrier::Written(carrier) => self.reading(carrier) == Reading::ValueType(site.reading.frame()),
                            Carrier::Universe(_) => true,
                        }
                            && self.reading(left) == Reading::Value(site.reading.frame())
                            && self.reading(right) == Reading::Value(site.reading.frame())
                            && self.in_type.contains(&left)
                            && self.in_type.contains(&right)
                            && self.at_endpoint.contains(&left)
                            && self.at_endpoint.contains(&right)
                )
        },
    )]
    pub(super) fn path_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        closed(site, &mut cursor, TileName::PATH)?;
        closed(site, &mut cursor, TileName::PAREN_OPEN)?;
        let carrier = if let Maybe::Present(_) = cursor.at(TileName::UNIVERSE) {
            Carrier::Universe(self.universe_tiles(site, &mut cursor)?)
        }
        else {
            let carrier = site.one(cursor.operands())?;
            self.read(carrier.node, Reading::ValueType(frame));
            Carrier::Written(carrier.node)
        };
        closed(site, &mut cursor, TileName::COMMA)?;
        let left = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::COMMA)?;
        let right = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(left.node, Reading::Value(frame));
        self.read(right.node, Reading::Value(frame));
        self.in_type.extend([left.node, right.node]);
        self.at_endpoint.extend([left.node, right.node]);
        self.plan(site, Plan::Path(carrier, left.node, right.node));

        Ok(())
    }

    /// Classify a path type written as a call, `Path(A, a, b)` where a value
    /// is read, its three operands already read off the call.
    ///
    /// # Specification
    /// - requires: `site` is a call headed `Path`, which nothing the scope
    ///   binds answers, written over `carrier`, `left` and `right`.
    /// - ensures: the form stands as a value type, reads its carrier as a value
    ///   type and its two endpoints as endpoints standing inside a type, all
    ///   under its own frame, and is planned over the three, the carrier as
    ///   written; where a value is read the type is quoted.
    /// - provides: the path type an argument of a parameter `t : Type` spells.
    /// - fails: yields the wrong-sort refusal where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path type written as a declaration's body, read
    ///   back out of the arena as the quote of the path type over its carrier
    ///   and endpoints.
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Path(Carrier::Written(carrier), left, right))
                        if [carrier, left, right] == written
                            && self.reading(carrier) == Reading::ValueType(site.reading.frame())
                            && self.reading(left) == Reading::Value(site.reading.frame())
                            && self.reading(right) == Reading::Value(site.reading.frame())
                            && self.in_type.contains(&left)
                            && self.in_type.contains(&right)
                            && self.at_endpoint.contains(&left)
                            && self.at_endpoint.contains(&right)
                )
        },
    )]
    pub(super) fn written_path(
        &mut self,
        site: Site,
        written: [NodeIndex; 3],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let [carrier, left, right] = written;
        self.read(carrier, Reading::ValueType(frame));
        self.read(left, Reading::Value(frame));
        self.read(right, Reading::Value(frame));
        self.in_type.extend([left, right]);
        self.at_endpoint.extend([left, right]);
        self.plan(site, Plan::Path(Carrier::Written(carrier), left, right));

        Ok(())
    }

    /// Classify a directed identity type, `Flow(A, a, b)`, its three operands
    /// already read off the application.
    ///
    /// # Specification
    /// - requires: `site` is a type application headed `Flow`, which nothing
    ///   the scope binds answers, written over `carrier`, `left` and `right`.
    /// - ensures: the form stands as a value type, reads its carrier as a value
    ///   type and its two endpoints as endpoints standing inside a type, all
    ///   under its own frame, and is planned over the three.
    /// - provides: directed identity's type former.
    /// - fails: yields the wrong-sort refusal where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a flow between two session codes read back out of the
    ///   arena with its carrier and endpoints in order.
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Flow(carrier, left, right))
                        if [carrier, left, right] == written
                            && self.reading(carrier) == Reading::ValueType(site.reading.frame())
                            && self.reading(left) == Reading::Value(site.reading.frame())
                            && self.reading(right) == Reading::Value(site.reading.frame())
                            && self.at_endpoint.contains(&left)
                            && self.at_endpoint.contains(&right)
                )
        },
    )]
    pub(super) fn flow_type(
        &mut self,
        site: Site,
        written: [NodeIndex; 3],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let [carrier, left, right] = written;
        self.read(carrier, Reading::ValueType(frame));
        self.read(left, Reading::Value(frame));
        self.read(right, Reading::Value(frame));
        self.in_type.extend([left, right]);
        self.at_endpoint.extend([left, right]);
        self.plan(site, Plan::Flow(carrier, left, right));

        Ok(())
    }

    /// Classify a relation between two types written infix: `A ≃ B` or its
    /// ASCII spelling `A <~> B`, `A ≅ B`, and `A ⇝ B` or `A ~~> B`.
    ///
    /// # Specification
    /// - requires: `site` is a relation in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the relation its tile spells, over its two operands in order,
    ///   as [`Self::relation_of`] plans it.
    /// - fails: yields the misplaced-tile or extra-operand fault for a form out
    ///   of shape, and the relation's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each relation, by its glyph and by its ASCII
    ///   spelling, read back as the exact core type the written record or flow
    ///   lowers to.
    /// - witness: `lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    #[spec(ensures: |ret| ret.is_err() || matches!(self.plans.get(usize::from(site.at.node)), Some(&Plan::Relation(..))))]
    pub(super) fn relation_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let left = site.one(cursor.operands())?;
        let (relation, tile) = [
            (Relation::Equivalence, TileName::EQUIVALENCE),
            (Relation::Isomorphism, TileName::ISOMORPHISM),
            (Relation::Flow, TileName::UNIVERSE_FLOW),
        ]
        .into_iter()
        .find(|&(_, tile)| matches!(cursor.at(tile), Maybe::Present(_)))
        .unwrap_or((Relation::Flow, TileName::UNIVERSE_FLOW));
        closed(site, &mut cursor, tile)?;
        let right = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.relation_of(site, relation, [left.node, right.node])
    }

    /// Classify the relation `relation` between the two types written at
    /// `written`, infix or, for the quasi-inverse, as `Iso(A, B)`.
    ///
    /// # Specification
    /// - requires: `written` holds the relation's two operands, in order.
    /// - ensures: the form stands as a value type and is planned over its two
    ///   operands. The equivalence and the quasi-inverse read both as value
    ///   types under the form's frame; the flow reads both as endpoints
    ///   standing inside a type, the codes of the types they spell, as
    ///   `Flow(Type, A, B)` reads its endpoints.
    /// - provides: the one planning step both spellings of a relation share.
    /// - fails: yields the wrong-sort refusal where no value type is read.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::relation_type`], and `Iso(A, B)` read back
    ///   as the type `A ≅ B` lowers to.
    /// - witness: `lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Relation(planned, left, right))
                        if planned == relation && [left, right] == written
                            && match relation {
                                Relation::Flow => self.reading(left) == Reading::Value(site.reading.frame())
                                    && self.reading(right) == Reading::Value(site.reading.frame())
                                    && self.at_endpoint.contains(&left)
                                    && self.at_endpoint.contains(&right),
                                Relation::Isomorphism | Relation::Equivalence => self.reading(left) == Reading::ValueType(site.reading.frame())
                                    && self.reading(right) == Reading::ValueType(site.reading.frame()),
                            }
                )
        },
    )]
    pub(super) fn relation_of(
        &mut self,
        site: Site,
        relation: Relation,
        written: [NodeIndex; 2],
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::ValueType)?;
        let [left, right] = written;
        match relation {
            Relation::Isomorphism | Relation::Equivalence => {
                self.read(left, Reading::ValueType(frame));
                self.read(right, Reading::ValueType(frame));
            },
            Relation::Flow => {
                self.read(left, Reading::Value(frame));
                self.read(right, Reading::Value(frame));
                self.in_type.extend([left, right]);
                self.at_endpoint.extend([left, right]);
            },
        }
        self.plan(site, Plan::Relation(relation, left, right));

        Ok(())
    }

    /// The record the type at `stated` abbreviates when it is written as an
    /// equivalence or a quasi-inverse.
    ///
    /// # Specification
    /// - requires: `stated` is a type's syntax node, already classified.
    /// - ensures: through the transparent plans of parentheses,
    ///   [`Layout::Isomorphism`] for `A ≅ B` or `Iso(A, B)` and
    ///   [`Layout::Equivalence`] for `A ≃ B`; at a node the mint sweep has
    ///   already spent, as an earlier declaration's signature is, the same by
    ///   the relation's glyph, read through parentheses; the other-former
    ///   absence for a flow and for every other type.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] reading a spent node's forms.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Termination
    /// Each step follows a transparent plan to the child it stands for,
    /// strictly deeper in the finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern at a parameter written with each relation
    ///   splits its record, positionally and by label, and so does one at a
    ///   `run` binder whose callee's result is written with one.
    /// - witness: `lower::identity::tests::a_pattern_at_a_relation_splits_its_record`
    /// - witness: `lower::identity::tests::a_run_binder_splits_the_relation_its_call_returns_656`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Maybe::Absent(_) | Maybe::Present(Layout::Isomorphism | Layout::Equivalence))))]
    pub(super) fn stated_relation(
        &mut self,
        stated: NodeIndex,
    ) -> Result<Maybe<Layout, related::Absent>, LoweringRefusal<'source>>
    {
        let otherwise = Maybe::Absent(related::Absent::Otherwise);
        let mut at = stated;
        loop {
            match self.plans.get(usize::from(at)) {
                Some(&Plan::Transparent(inner)) => at = inner,
                Some(&Plan::Relation(Relation::Isomorphism, ..)) => {
                    return Ok(Maybe::Present(Layout::Isomorphism));
                },
                Some(&Plan::Relation(Relation::Equivalence, ..)) => {
                    return Ok(Maybe::Present(Layout::Equivalence));
                },
                Some(&Plan::Unplanned) => break,
                _ => return Ok(otherwise),
            }
        }
        let Maybe::Present(written) = self.unwrapped(at)?
        else {
            return Ok(otherwise);
        };
        if written.former != Former::RelationType {
            return Ok(otherwise);
        }
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, written.node, &mut scratch);
        let layout = scratch.pieces.iter().find_map(|piece| match *piece {
            Piece::Tile { label, .. } if label == TileName::ISOMORPHISM => {
                Some(Layout::Isomorphism)
            },
            Piece::Tile { label, .. } if label == TileName::EQUIVALENCE => {
                Some(Layout::Equivalence)
            },
            Piece::Tile { .. } | Piece::Operand(_) => None,
        });
        self.scratch = scratch;
        read?;

        Ok(layout.map_or(otherwise, Maybe::Present))
    }

    /// Mint the relation `relation` over its two lowered operands: the record
    /// type the equivalence or the quasi-inverse abbreviates, or the flow
    /// between two codes at the universe a bare `Type` names.
    ///
    /// # Specification
    /// - requires: both operands are already minted or absent.
    /// - ensures: the quasi-inverse as [`quasi_inverse`] mints it, the
    ///   equivalence as [`bi_invertible`] mints it, and the flow as `Flow(Type,
    ///   A, B)` lowers; the type carries the written origin and every node
    ///   minted below it the same origin as [`Insertion::Relation`], and the
    ///   origin table records the relation against the type. Nothing when an
    ///   operand did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::relation_type`].
    /// - witness: `lower::identity::tests::a_relation_lowers_to_the_type_it_abbreviates`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(Lowered::ValueType(id)) => sink.origins.relations().last() == Some(&(id, relation)),
        Maybe::Present(_) => false,
        Maybe::Absent(_) => true,
    })]
    pub(super) fn mint_relation(
        &self,
        relation: Relation,
        written: [NodeIndex; 2],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let [left, right] = written;
        let mark = sink.arena.watermark();
        let minted = match relation {
            Relation::Isomorphism => self.value_type_at(left).and_then(|from| {
                self.value_type_at(right)
                    .map(|to| quasi_inverse(sink.arena, from, to))
            }),
            Relation::Equivalence => self.value_type_at(left).and_then(|from| {
                self.value_type_at(right)
                    .map(|to| bi_invertible(sink.arena, from, to))
            }),
            Relation::Flow => self.value_at(left).and_then(|source| {
                self.value_at(right).map(|target| {
                    let universe = Universe::FUSS_FREE;
                    let carrier = sink.arena.value_type_universe(
                        Sort::Ground(universe.sort),
                        Level::constant(universe.level),
                    );
                    sink.arena.value_type_flow(carrier, source, target)
                })
            }),
        };
        let below = origin.inserted(Insertion::Relation);
        for id in sink.arena.values_since(mark) {
            sink.origins.record_value(id, below);
        }
        for id in sink.arena.computations_since(mark) {
            sink.origins.record_computation(id, below);
        }
        for id in sink.arena.value_types_since(mark) {
            let at = if minted == Maybe::Present(id) {
                origin
            }
            else {
                below
            };
            sink.origins.record_value_type(id, at);
        }
        for id in sink.arena.comp_types_since(mark) {
            sink.origins.record_comp_type(id, below);
        }
        minted.map(|id| {
            sink.origins.record_relation(id, relation);
            Lowered::ValueType(id)
        })
    }

    /// The identity operation `head`, the head of a call written at `site`,
    /// names.
    ///
    /// # Specification
    /// - requires: `head` is the first operand of the call at `site`.
    /// - ensures: the operation a bare name spells when no binder and no
    ///   earlier declaration carries that name; the unspelled absence for any
    ///   other head.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a mold the grammar does
    ///   not hold; the refusals the name's resolution yields.
    /// - panics: none.
    ///
    /// # Errors
    /// The resolution's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a free spelling and a bound one take their own
    ///   readings.
    /// - witness: `lower::identity::tests::a_bound_name_shadows_an_identity_operation`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `tests::modules::a_forward_member_reference_is_refused_by_position`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body searches the fixed spelling table for the head's name once; the check searches it once more"
        )
    )]
    #[spec(
        ensures: |ret| match ret {
            | Ok(Maybe::Present(operation)) => SPELLED
                .iter()
                .any(|&(spelling, spelled)| spelled == operation && self.text_at(head).as_ref() == spelling),
            | _ => true,
        },
    )]
    pub(super) fn identity_head(
        &mut self,
        site: Site,
        head: Placed,
    ) -> Result<Maybe<Operation, spelled::Absent>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(head.node)
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let Shape::Form {
            former: Former::Name,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let name = self.name_at(head);
        let Some(&(_spelling, operation)) = SPELLED
            .iter()
            .find(|&&(spelling, _operation)| name.as_ref() == spelling)
        else {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        };
        let named = Site { at: head, ..site };
        if let Maybe::Present(_shadowed) = self.resolve_name(named, site.reading.frame(), name)? {
            return Ok(Maybe::Absent(spelled::Absent::Unspelled));
        }

        Ok(Maybe::Present(operation))
    }

    /// Classify the call of `operation` at `site`, its head read, the cursor
    /// at its arguments.
    ///
    /// # Specification
    /// - requires: `operation` is what the call's head spells.
    /// - ensures: `here(a)` and `stay(a)` stand as values reading their point
    ///   as a value at an endpoint, but `here(a)` at the point of a family's
    ///   loops is the empty word of their words, as [`Self::looped_point`]
    ///   reads it; `funext(f, g)`, `equiv(f, g)`, `pathProduct(p, q)`,
    ///   `flowProduct(p, q)`, `cons(h, t)`, `bisim(A, B)` and `sim(A, B)` stand
    ///   as values reading both operands as values; `ua(e)` stands as a value
    ///   reading its record as a value, its forward map derived from it;
    ///   `transport(\X. T, p, v)` and `ride(\X. T, f, v)` stand as computations
    ///   reading their motive, path or flow and value as values, and
    ///   `transport(M, p, z₀, q, v)` as a computation reading its motive as a
    ///   value type and the other four as values; `back(p)` and `cong(f, p)`
    ///   stand as computations derived as [`Self::derive`] does; `recorded(m₀,
    ///   …, mₙ)` stands as a value over its moves, each read as
    ///   [`Self::recorded_move`] reads it. Every operand is read under the
    ///   site's frame.
    /// - fails: the wrong-sort refusal where the operation's sort is not read;
    ///   the arity refusal for other than one argument to `here`, `stay`,
    ///   `forward`, `ua` or `back`, two to `funext`, `equiv`, `pathProduct`,
    ///   `flowProduct`, `cons`, `cong`, `bisim`, `sim` or `arrow`, three to
    ///   `ride`, and three or five to `transport`; the unannotated refusal for
    ///   a three-operand transport or a ride whose motive is no static
    ///   abstraction; [`Self::derive`]'s refusal; a move's refusal; the
    ///   argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation at its own arity, and `here` at two,
    ///   each asserted as the planned former or the exact refusal.
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::funext_lowers_to_its_former`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    /// - witness: `lower::identity::tests::a_move_out_of_shape_is_refused`
    /// - witness: `lower::identity::tests::a_path_product_lowers_to_its_former`
    /// - witness: `lower::identity::tests::a_flow_product_lowers_to_its_former`
    /// - witness: `lower::native::tests::a_word_conses_its_letters_and_matches_them`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| {
            self.operands.len() == start
                && (ret.is_err()
                    || match (operation, self.plans.get(usize::from(site.at.node))) {
                        | (Operation::Here, Some(&Plan::Here(point)))
                        | (Operation::Stay, Some(&Plan::Stay(point))) => self.at_endpoint.contains(&point),
                        | (Operation::Funext, Some(&Plan::Funext(..)))
                        | (Operation::Equiv, Some(&Plan::Equiv(..)))
                        | (Operation::Univalence, Some(&Plan::Univalence(_)))
                        | (Operation::PathProduct, Some(&Plan::PathProduct(..)))
                        | (Operation::FlowProduct, Some(&Plan::FlowProduct(..)))
                        | (Operation::Cons, Some(&Plan::ListCons(..)))
                        | (Operation::Bisim, Some(&Plan::SessionRelated(SessionRelation::Equivalence, ..)))
                        | (Operation::Sim, Some(&Plan::SessionRelated(SessionRelation::Subtyping, ..)))
                        | (Operation::Ride, Some(&Plan::Ride(..)))
                        | (Operation::Forward, Some(&Plan::Forward(_)))
                        | (Operation::Arrow, Some(&Plan::FunctionFlow(..)))
                        | (Operation::Recorded, Some(&Plan::Recorded(_)))
                        | (Operation::Transport, Some(&(Plan::Transport(..) | Plan::TelescopeTransport(_))))
                        | (Operation::Back | Operation::Cong, Some(&Plan::Derived(_)))
                        | (Operation::Here, Some(&Plan::Constructor(_))) => true,
                        | _ => false,
                    })
        },
    )]
    pub(super) fn identity_call(
        &mut self,
        site: Site,
        operation: Operation,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match operation {
            Operation::Here
            | Operation::Funext
            | Operation::Equiv
            | Operation::Univalence
            | Operation::PathProduct
            | Operation::FlowProduct
            | Operation::Cons
            | Operation::Bisim
            | Operation::Sim
            | Operation::Stay
            | Operation::Forward
            | Operation::Arrow
            | Operation::Recorded => Produced::Value,
            Operation::Back | Operation::Cong | Operation::Transport | Operation::Ride => {
                Produced::Computation
            },
        };
        let frame = self.require(site, produced)?;
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let count = self.operands.len().saturating_sub(start);
        let first = self.operands.get(start).copied();
        let second = self.operands.get(start.saturating_add(1_usize)).copied();
        let third = self.operands.get(start.saturating_add(2_usize)).copied();
        let written = self
            .operands
            .get(start ..)
            .and_then(|written| <[NodeIndex; 5]>::try_from(written).ok());
        let moves = match operation {
            Operation::Recorded => self.operands.get(start ..).map(<[NodeIndex]>::to_vec),
            Operation::Here
            | Operation::Funext
            | Operation::Equiv
            | Operation::Univalence
            | Operation::PathProduct
            | Operation::FlowProduct
            | Operation::Cons
            | Operation::Bisim
            | Operation::Sim
            | Operation::Stay
            | Operation::Forward
            | Operation::Arrow
            | Operation::Back
            | Operation::Cong
            | Operation::Transport
            | Operation::Ride => None,
        };
        self.operands.truncate(start);
        read?;
        match (operation, count, first, second, third) {
            (Operation::Here | Operation::Stay, 1_usize, Some(point), ..) => {
                if operation == Operation::Here
                    && let Some(node) = self.tree.node(point)
                    && let Maybe::Present(empty) = self.looped_point(Placed::of(point, node))?
                {
                    let none = Stretch {
                        start: self.operands.len(),
                        end: self.operands.len(),
                    };
                    return self.construct(site, empty, none);
                }
                self.read(point, Reading::Value(frame));
                let _marked = self.at_endpoint.insert(point);
                let plan = match operation {
                    Operation::Stay => Plan::Stay(point),
                    Operation::Here
                    | Operation::Funext
                    | Operation::Equiv
                    | Operation::Univalence
                    | Operation::PathProduct
                    | Operation::Transport
                    | Operation::Back
                    | Operation::Cong
                    | Operation::Cons
                    | Operation::Bisim
                    | Operation::Sim
                    | Operation::Forward
                    | Operation::Arrow
                    | Operation::FlowProduct
                    | Operation::Ride
                    | Operation::Recorded => Plan::Here(point),
                };
                self.plan(site, plan);
                Ok(())
            },
            (
                Operation::Funext
                | Operation::Equiv
                | Operation::PathProduct
                | Operation::FlowProduct
                | Operation::Cons
                | Operation::Bisim
                | Operation::Sim
                | Operation::Arrow,
                2_usize,
                Some(left),
                Some(right),
                _,
            ) => {
                self.read(left, Reading::Value(frame));
                self.read(right, Reading::Value(frame));
                let plan = match operation {
                    Operation::Equiv => Plan::Equiv(left, right),
                    Operation::PathProduct => Plan::PathProduct(left, right),
                    Operation::FlowProduct => Plan::FlowProduct(left, right),
                    Operation::Cons => Plan::ListCons(left, right),
                    Operation::Bisim => {
                        Plan::SessionRelated(SessionRelation::Equivalence, left, right)
                    },
                    Operation::Sim => Plan::SessionRelated(SessionRelation::Subtyping, left, right),
                    Operation::Arrow => Plan::FunctionFlow(left, right),
                    Operation::Here
                    | Operation::Funext
                    | Operation::Univalence
                    | Operation::Transport
                    | Operation::Back
                    | Operation::Cong
                    | Operation::Stay
                    | Operation::Forward
                    | Operation::Ride
                    | Operation::Recorded => Plan::Funext(left, right),
                };
                self.plan(site, plan);
                Ok(())
            },
            (
                Operation::Transport | Operation::Ride,
                3_usize,
                Some(motive),
                Some(path),
                Some(value),
            ) => {
                self.stated_motive(site, motive)?;
                for operand in [motive, path, value] {
                    self.read(operand, Reading::Value(frame));
                }
                let plan = match operation {
                    Operation::Ride => Plan::Ride(motive, path, value),
                    Operation::Here
                    | Operation::Funext
                    | Operation::Equiv
                    | Operation::Univalence
                    | Operation::PathProduct
                    | Operation::Transport
                    | Operation::Back
                    | Operation::Cong
                    | Operation::Cons
                    | Operation::Bisim
                    | Operation::Sim
                    | Operation::Stay
                    | Operation::Forward
                    | Operation::Arrow
                    | Operation::FlowProduct
                    | Operation::Recorded => Plan::Transport(motive, path, value),
                };
                self.plan(site, plan);
                Ok(())
            },
            (Operation::Recorded, ..) => {
                let written = moves.unwrap_or_default();
                let mut planned = Vec::with_capacity(written.len());
                for movement in written {
                    planned.push(self.recorded_move(site, frame, movement)?);
                }
                self.plan(site, Plan::Recorded(Arc::from(planned)));
                Ok(())
            },
            (Operation::Transport, 5_usize, ..) => match written {
                Some([motive, path, departure, over, value]) => {
                    self.read(motive, Reading::ValueType(frame));
                    for operand in [path, departure, over, value] {
                        self.read(operand, Reading::Value(frame));
                    }
                    self.plan(
                        site,
                        Plan::TelescopeTransport(Transported {
                            motive,
                            path,
                            start: departure,
                            over,
                            value,
                            frame,
                        }),
                    );
                    Ok(())
                },
                None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
            },
            (Operation::Back, 1_usize, Some(path), ..) => {
                self.derive(site, frame, Derivation::Back { path })
            },
            (Operation::Forward, 1_usize, Some(translator), ..) => {
                self.read(translator, Reading::Value(frame));
                self.plan(site, Plan::Forward(translator));
                Ok(())
            },
            (Operation::Univalence, 1_usize, Some(record), ..) => {
                self.read(record, Reading::Value(frame));
                self.plan(site, Plan::Univalence(record));
                Ok(())
            },
            (Operation::Cong, 2_usize, Some(function), Some(path), _) => {
                self.derive(site, frame, Derivation::Cong { function, path })
            },
            _ => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
        }
    }

    /// Require a transport's or a ride's motive to be written as a static
    /// abstraction.
    ///
    /// # Specification
    /// - requires: `motive` is the first operand of the transport or the ride
    ///   at `site`.
    /// - ensures: `Ok` exactly when the operand is a static abstraction, `\X.
    ///   T`, whose body is the family the operation moves its value in.
    /// - fails: the unannotated refusal at `site` for any other operand; the
    ///   refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The motive's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an abstraction motive lowers and a named one is
    ///   refused.
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    #[spec(ensures: |ret| ret.is_err() || matches!(
        self.tree.node(motive).map(|node| shape_of(self.pbg, node)),
        Some(Ok(Shape::Form { former: Former::StaticAbstraction, .. }))
    ))]
    fn stated_motive(
        &self,
        site: Site,
        motive: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let unannotated = site.out(FragmentBoundary::Unannotated);
        let Some(node) = self.tree.node(motive)
        else {
            return Err(unannotated);
        };
        match shape_of(self.pbg, node)? {
            Shape::Form {
                former: Former::StaticAbstraction,
                ..
            } => Ok(()),
            Shape::Root | Shape::Form { .. } | Shape::Repair(_) | Shape::Layout => Err(unannotated),
        }
    }

    /// Classify one move of the recorded run at `site`, written at
    /// `movement`.
    ///
    /// # Specification
    /// - requires: `movement` is an argument of the `recorded` call at `site`,
    ///   which stands under `frame`.
    /// - ensures: a bare `closed` is the close; `sent(v)` and `received(v)`
    ///   read `v` as a value under `frame` and carry it; `selected(l)` and
    ///   `offered(l)` carry the label the bare name `l` spells. The move's own
    ///   head and a label are read by their shape, never resolved, so no binder
    ///   shadows them.
    /// - fails: the unadmitted boundary for a move of any other shape or
    ///   spelling, or a label that is no bare name; the arity boundary for a
    ///   move written with other than one argument; the refusals the tree's
    ///   molds yield and the argument list's fault.
    /// - panics: none.
    ///
    /// # Errors
    /// The move's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run of every move kind read back out of the arena,
    ///   and an unknown move, a payload-less send and a label that is a call
    ///   each refused by their boundary.
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    /// - witness: `lower::identity::tests::a_move_out_of_shape_is_refused`
    #[spec(
        captures: start = self.operands.len(),
        ensures: |ret| self.operands.len() == start && match ret {
            | Ok(RecordedMove::Sent(payload) | RecordedMove::Received(payload)) => {
                self.reading(payload) == Reading::Value(frame)
            },
            | Ok(RecordedMove::Selected(_) | RecordedMove::Offered(_) | RecordedMove::Closed)
            | Err(_) => true,
        },
    )]
    fn recorded_move(
        &mut self,
        site: Site,
        frame: Frame,
        movement: NodeIndex,
    ) -> Result<RecordedMove<NodeIndex>, LoweringRefusal<'source>>
    {
        let unadmitted = site.out(FragmentBoundary::Unadmitted);
        let Some(node) = self.tree.node(movement)
        else {
            return Err(unadmitted);
        };
        let written = Placed::of(movement, node);
        let former = match shape_of(self.pbg, node)? {
            Shape::Form { former, .. } => former,
            Shape::Root | Shape::Repair(_) | Shape::Layout => return Err(unadmitted),
        };
        if matches!(former, Former::Name) {
            return if self.name_at(written).as_ref() == CLOSED {
                Ok(RecordedMove::Closed)
            }
            else {
                Err(unadmitted)
            };
        }
        if !matches!(former, Former::Call) {
            return Err(unadmitted);
        }
        let at = Site {
            at: written,
            ..site
        };
        let start = self.operands.len();
        let mut scratch = core::mem::take(&mut self.scratch);
        let read = read_pieces(self.pbg, self.tree, movement, &mut scratch).and_then(|()| {
            let mut cursor = Cursor::new(&scratch.pieces, written.span);
            let head = at.one(cursor.operands())?;
            arguments(at, &mut cursor, &mut self.operands)?;
            Ok(head)
        });
        self.scratch = scratch;
        let count = self.operands.len().saturating_sub(start);
        let argument = match self.operands.get(start ..) {
            Some(&[argument]) => Some(argument),
            Some(_) | None => None,
        };
        self.operands.truncate(start);
        let head = read?;
        let Some(argument) = argument
        else {
            return Err(at.out(FragmentBoundary::Arity(OperandCount::from(count))));
        };
        let spelled = self.name_at(head);
        match spelled.as_ref() {
            "sent" | "received" => {
                self.read(argument, Reading::Value(frame));
                Ok(if spelled.as_ref() == "sent" {
                    RecordedMove::Sent(argument)
                }
                else {
                    RecordedMove::Received(argument)
                })
            },
            "selected" | "offered" => {
                let label = self
                    .tree
                    .node(argument)
                    .and_then(|labelled| match shape_of(self.pbg, labelled) {
                        Ok(Shape::Form {
                            former: Former::Name,
                            ..
                        }) => Some(Placed::of(argument, labelled)),
                        Ok(_) | Err(_) => None,
                    })
                    .map(|named| FieldLabel::from(String::from(self.name_at(named).as_ref())))
                    .ok_or(unadmitted)?;
                Ok(if spelled.as_ref() == "selected" {
                    RecordedMove::Selected(label)
                }
                else {
                    RecordedMove::Offered(label)
                })
            },
            _ => Err(unadmitted),
        }
    }

    /// Classify the derived operation `derivation`, standing as a computation
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - requires: `site` stands as a computation under `frame`, or as a value
    ///   bridged to one.
    /// - ensures: every operand is read as a value under `frame`. Where the
    ///   position answers a type, the operation is planned against that path
    ///   type; `f then g` where it answers a written flow type is planned as
    ///   the returned composite of the two flows, and `back(f)` there against
    ///   the flow type, as the symmetry ride the checker refuses. Where it
    ///   answers none, the operation is planned as synthesised from its
    ///   operands, `cong` reading its codomain off the written result of the
    ///   function definition its first operand names, and recorded for
    ///   [`Self::refuse_unsynthesised`]. An operation read where a value is
    ///   read is the value its transport returns.
    /// - fails: [`FragmentBoundary::NotAFunction`] for `cong` at a constructor;
    ///   the unannotated refusal where the position answers a type that is not
    ///   a written path type, or for `then` and `back` a written flow type,
    ///   under at most a returner and parentheses, and for a synthesised `cong`
    ///   whose first operand names no function definition with a written
    ///   result; the allowance refusal from that walk; the function name's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The operation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation under a path answer, one under an
    ///   answer that is no path type, and each synthesised at the words.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_needs_a_written_path_answer`
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Derived(planned)) if planned.derivation == derivation && planned.frame == frame
                ) || matches!(
                    (self.plans.get(usize::from(site.at.node)), derivation),
                    (Some(&Plan::FlowThen(left, right)), Derivation::Then { first, second }) if left == first && right == second
                )
        },
    )]
    pub(super) fn derive(
        &mut self,
        site: Site,
        frame: Frame,
        derivation: Derivation,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Derivation::Cong { function, .. } = derivation
            && let Some(node) = self.tree.node(function)
            && let Maybe::Present(_) = self.constructor_head(site, Placed::of(function, node))?
        {
            return Err(site.out(FragmentBoundary::NotAFunction));
        }
        let stance = match self.answers.get(&site.at.node) {
            Some(&answer) => Stance::Answered(answer),
            None => Stance::Synthesised(
                match derivation {
                    Derivation::Cong { function, .. } => self.mapped(site, frame, function)?,
                    Derivation::Back { .. } | Derivation::Then { .. } => Synthesis::Paths,
                },
                Typings::default(),
            ),
        };
        if let Stance::Answered(answer) = stance {
            // A loop arm answers the path over its loop, whatever its case
            // answers.
            let answered = match answer.over {
                super::native::Over::Written
                | super::native::Over::Returning
                | super::native::Over::Valued { .. } => self.answers_path(site, answer.node)?,
                super::native::Over::Loop { .. } => Answered::Path,
            };
            if answered == Answered::Flow {
                match derivation {
                    Derivation::Then { first, second } => {
                        self.read(first, Reading::Value(frame));
                        self.read(second, Reading::Value(frame));
                        self.plan(site, Plan::FlowThen(first, second));
                        return Ok(());
                    },
                    Derivation::Cong { .. } => {
                        return Err(site.out(FragmentBoundary::Unannotated));
                    },
                    Derivation::Back { .. } => {},
                }
            }
        }
        match derivation {
            Derivation::Back { path } => self.read(path, Reading::Value(frame)),
            Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => {
                self.read(first, Reading::Value(frame));
                self.read(second, Reading::Value(frame));
            },
        }
        if let Stance::Synthesised(..) = stance {
            self.synthesised.push(site);
        }
        // The operation is the path its transport returns: pure, so where a
        // value is read it is that value, as an endpoint's computation is.
        if let Reading::Value(_) = site.reading
            && let Some(held) = self.bridges.get_mut(usize::from(site.at.node))
        {
            *held = super::Bridge::Inserted(Insertion::Endpoint);
        }
        self.plan(
            site,
            Plan::Derived(Derived {
                derivation,
                stance,
                frame,
            }),
        );

        Ok(())
    }

    /// What a synthesised `cong` reads its codomain off: the written result
    /// of the function definition `function` names, the codomain of the map
    /// a declaration's signature states, or the codomain of the arrow a
    /// parameter's written type thunks.
    ///
    /// # Specification
    /// - requires: `function` is the first operand of the `cong` at `site`,
    ///   which stands under `frame`.
    /// - ensures: the result type node and the frame it is read under, when
    ///   `function` is a bare name resolving to an earlier declaration written
    ///   as a function tail with a result type, or to one whose signature
    ///   states a map, `+U (A -> C)` or `A => B`, or to a binder whose written
    ///   type is the thunk of an arrow, `+U (A -> C)`, under any parentheses.
    /// - fails: the unannotated refusal for any other operand; the name's own
    ///   refusal from its resolution.
    /// - panics: none.
    ///
    /// # Errors
    /// The operand's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function definition gives its codomain, a parameter
    ///   thunking an arrow gives the arrow's, and a parameter of another type
    ///   gives none; a declaration whose signature states a map gives the map's
    ///   codomain.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    /// - witness: `lower::identity::tests::cong_reads_a_map_its_signature_states_778`
    #[spec(ensures: |ret| match ret {
        | Ok(Synthesis::Mapped { codomain, frame: read }) => self.reading(codomain.node()).frame() == read,
        | Ok(Synthesis::Thunked { .. } | Synthesis::Stated { .. }) | Err(_) => true,
        | Ok(Synthesis::Paths | Synthesis::Bound { .. }) => false,
    })]
    fn mapped(
        &mut self,
        site: Site,
        frame: Frame,
        function: NodeIndex,
    ) -> Result<Synthesis, LoweringRefusal<'source>>
    {
        let unannotated = site.out(FragmentBoundary::Unannotated);
        let Some(node) = self.tree.node(function)
        else {
            return Err(unannotated);
        };
        let named = Placed::of(function, node);
        let Shape::Form {
            former: Former::Name,
            ..
        } = shape_of(self.pbg, node)?
        else {
            return Err(unannotated);
        };
        let name = self.name_at(named);
        match self.resolve_name(Site { at: named, ..site }, frame, name)? {
            Maybe::Present(super::Resolved::Declaration { constant, .. }) => {
                match self.function_of(constant) {
                    Some(Function {
                        result: Maybe::Present(codomain),
                        ..
                    }) => Ok(Synthesis::Mapped {
                        codomain: Codomain::Returner(codomain),
                        frame: self.reading(codomain).frame(),
                    }),
                    Some(_) => Err(unannotated),
                    // The signature's written type may be classified after
                    // this operation, so its map is read once the sweep is
                    // done.
                    None => self.stated(constant).map_or(Err(unannotated), |declared| {
                        Ok(Synthesis::Stated { declared })
                    }),
                }
            },
            // The binder's written type may be classified after this
            // operation, so its arrow is read once the sweep is done.
            Maybe::Present(super::Resolved::Binder(bound)) => {
                match self.scope.declared(bound.binder) {
                    Maybe::Present(declared) => Ok(Synthesis::Thunked { declared }),
                    Maybe::Absent(_) => Err(unannotated),
                }
            },
            Maybe::Absent(_) => Err(unannotated),
        }
    }

    /// The function tail the declaration at `constant` is written with, by
    /// its signature or its definition.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified the declaration.
    /// - ensures: the tail's plan when either half of the slot is written as a
    ///   function tail; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function definition answers its tail, a value
    ///   declaration none.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    #[spec(ensures: |ret| ret.is_none() || usize::from(constant) < self.collected.slots.len())]
    pub(super) fn function_of(
        &self,
        constant: ConstantIndex,
    ) -> Option<Function>
    {
        let slot = self.collected.slots.get(usize::from(constant))?;
        let tail = [slot.signature, slot.definition]
            .into_iter()
            .find_map(|half| match half {
                Maybe::Present(Half {
                    declaration,
                    operand: Operand::Function,
                    ..
                }) => Some(declaration.node),
                Maybe::Present(_) | Maybe::Absent(_) => None,
            })?;
        match self.plans.get(usize::from(tail)) {
            Some(&Plan::Function(function)) => Some(function),
            _ => None,
        }
    }

    /// The written type of the declaration at `constant`'s signature, when
    /// it is written as `def f : T ;`: the map whose codomain a `cong` by `f`
    /// reads once every node is classified.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the written type's node when the declaration's signature is
    ///   written as `def f : T ;`; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a signature at a thunked arrow and one at a value
    ///   function give their codomain.
    /// - witness: `lower::identity::tests::cong_reads_a_map_its_signature_states_778`
    #[spec(ensures: |ret| ret.is_none() || usize::from(constant) < self.collected.slots.len())]
    fn stated(
        &self,
        constant: ConstantIndex,
    ) -> Option<NodeIndex>
    {
        let slot = self.collected.slots.get(usize::from(constant))?;
        match slot.signature {
            Maybe::Present(Half {
                operand: Operand::Written(written),
                ..
            }) => Some(written.node),
            Maybe::Present(_) | Maybe::Absent(_) => None,
        }
    }

    /// The codomain of the map the value type at `declared` states: `C` of
    /// `+U (A -> C)`, or `B` of `A => B`, through parentheses.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified `declared`.
    /// - ensures: the returner codomain when the walk through transparent plans
    ///   meets one thunk and then an arrow; the returned codomain when it meets
    ///   a value function of one domain; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn steps to an operand of the node it read, strictly deeper in
    /// a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter at a thunked arrow and one at a value
    ///   function each give their codomain, one at a path type none.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    /// - witness: `lower::identity::tests::cong_reads_a_map_stated_as_a_value_function_791`
    #[spec(ensures: |ret| ret.is_none_or(|codomain| codomain.node() != declared))]
    fn thunked_codomain(
        &self,
        declared: NodeIndex,
    ) -> Option<Codomain>
    {
        let mut at = declared;
        let mut thunked = false;
        loop {
            match self.plans.get(usize::from(at)) {
                Some(&Plan::Transparent(inner)) => at = inner,
                Some(&Plan::Former(TypeFormer::Thunk, inner)) if !thunked => {
                    thunked = true;
                    at = inner;
                },
                Some(&Plan::Arrow(_, codomain)) if thunked => {
                    return Some(Codomain::Returner(codomain));
                },
                Some(&Plan::ValueFunction(domains, codomain))
                    if !thunked && domains.end.checked_sub(domains.start) == Some(1_usize) =>
                {
                    return Some(Codomain::Returned(codomain));
                },
                _ => return None,
            }
        }
    }

    /// The frame a bound map's use at `function` stands under in a type,
    /// through parentheses: the use site a static application of the bound
    /// binder records.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified `function`.
    /// - ensures: the use site's frame when `function` is planned as the bare
    ///   static application of a binder; nothing for a body's variable and
    ///   every other plan.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn steps to the child a transparent plan stands for, strictly
    /// deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `cong` at a bound map in a body and in a type.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| ret.is_none() || !matches!(self.plans.get(usize::from(function)), Some(&Plan::Variable(..))))]
    fn used_in_type(
        &self,
        function: NodeIndex,
    ) -> Option<Frame>
    {
        let mut at = function;
        loop {
            match self.plans.get(usize::from(at)) {
                Some(&Plan::Transparent(inner)) => at = inner,
                Some(&Plan::StaticApplication(Code::Bound { from, .. }, arguments))
                    if arguments.start == arguments.end =>
                {
                    return Some(from);
                },
                _ => return None,
            }
        }
    }

    /// Refuse every synthesised derived operation whose path's type is not
    /// read where it stands, the innermost first.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified every node.
    /// - ensures: each operation [`Self::derive`] recorded as synthesised,
    ///   under a declaration not yet refused, is offered the unannotated
    ///   refusal unless the path its motive is read off — `back`'s and `cong`'s
    ///   path, `then`'s first — reads its type as [`Self::reads_path`] does,
    ///   and `cong`'s codomain is read in a declaration that lowers: a declared
    ///   function's, or a map's a signature states, under no binder of its
    ///   telescope, a parameter's arrow's under the frame its written type is
    ///   read under, whose binders all stand where the operation does. An
    ///   admitted operation reads its own type when every path it reads does,
    ///   `then`'s second included. The record keeps every site, the innermost
    ///   first, for the mint sweep to read `cong`'s codomain.
    /// - provides: the classification-time guarantee that a synthesised
    ///   operation mints its motive.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Termination
    /// One pass over the recorded operations, each path walk spending the
    /// allowance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a word, a composite of words and an operation over
    ///   one admitted, an operation over a parameter or a call stating its path
    ///   admitted, one over a parameter stating none refused, `cong` over a
    ///   refused function refused, and `cong` at a parameter whose map type
    ///   reads an earlier parameter admitted in a body and in a type (#546).
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(captures: before = self.synthesised.len(), ensures: |ret| ret.is_err() || self.synthesised.len() == before)]
    pub(super) fn refuse_unsynthesised(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let first = self.current.synthesised;
        if let Some(own) = self.synthesised.get_mut(first ..) {
            own.sort_unstable_by_key(|site| core::cmp::Reverse(site.at.node));
        }
        let mut read = alloc::collections::BTreeSet::new();
        for index in first .. self.synthesised.len() {
            let Some(&site) = self.synthesised.get(index)
            else {
                break;
            };
            self.fuel.spend()?;
            let at = site.at.node;
            if self.collected.refused(at).0 {
                continue;
            }
            let Some(&Plan::Derived(Derived {
                derivation,
                stance: Stance::Synthesised(synthesis, _),
                ..
            })) = self.plans.get(usize::from(at))
            else {
                continue;
            };
            let (path, rest, function) = match derivation {
                Derivation::Back { path } => (path, None, None),
                Derivation::Cong { path, function } => (path, None, Some(function)),
                Derivation::Then { first, second } => (first, Some(second), None),
            };
            let synthesis = match (synthesis, function) {
                (Synthesis::Thunked { declared }, Some(function)) => {
                    match self.thunked_codomain(declared) {
                        Some(codomain)
                            if self.reading(codomain.node()).frame()
                                == self.reading(declared).frame() =>
                        {
                            Synthesis::Bound {
                                codomain,
                                frame: self.reading(codomain.node()).frame(),
                                in_type: self.used_in_type(function),
                            }
                        },
                        Some(codomain) => Synthesis::Mapped {
                            codomain,
                            frame: self.reading(codomain.node()).frame(),
                        },
                        None => synthesis,
                    }
                },
                (Synthesis::Stated { declared }, Some(_)) => self
                    .thunked_codomain(declared)
                    .map_or(synthesis, |codomain| Synthesis::Mapped {
                        codomain,
                        frame: self.reading(codomain.node()).frame(),
                    }),
                (
                    Synthesis::Thunked { .. }
                    | Synthesis::Stated { .. }
                    | Synthesis::Paths
                    | Synthesis::Mapped { .. }
                    | Synthesis::Bound { .. },
                    _,
                ) => synthesis,
            };
            let closed = match synthesis {
                Synthesis::Paths => true,
                Synthesis::Mapped { codomain, frame } => {
                    !self.collected.refused(codomain.node()).0
                        && self.scope.telescope_binders(frame).all(|binds| !binds)
                },
                Synthesis::Bound { codomain, .. } => !self.collected.refused(codomain.node()).0,
                Synthesis::Thunked { .. } | Synthesis::Stated { .. } => false,
            };
            let transported = self.reads_path(path, &read)?;
            if !closed || matches!(transported, Maybe::Absent(_)) {
                self.collected
                    .offer(at, site.out(FragmentBoundary::Unannotated));
                continue;
            }
            let whole = match rest {
                Some(second) => self.reads_path(second, &read)?,
                None => transported,
            };
            if let Maybe::Present(_) = whole {
                let _first = read.insert(at);
            }
            let typed = |path| match self.typed(path) {
                Maybe::Present(typed) => Some(typed),
                Maybe::Absent(_) => None,
            };
            let typings = Typings {
                transported: typed(path),
                onward: rest.and_then(typed),
            };
            if let Some(&mut Plan::Derived(Derived {
                stance: Stance::Synthesised(ref mut held_synthesis, ref mut held_typings),
                ..
            })) = self.plans.get_mut(usize::from(at))
            {
                *held_synthesis = synthesis;
                *held_typings = typings;
            }
        }

        Ok(())
    }

    /// The types the synthesised operations read off other declarations and
    /// binders — each `cong`'s codomain, and the written type of each
    /// parameter and the written result of each call a path operand is — for
    /// the mint sweep to mint before any operation over them.
    ///
    /// # Specification
    /// - ensures: for every recorded site still planned as a synthesised
    ///   operation, its codomain when it is a `cong` and the node each of its
    ///   [`Typings`] reads its path's type at, each once, in source order: a
    ///   type a synthesised operation inside another such type reads — an
    ///   earlier declaration's result, or a parameter written before it — is
    ///   minted before the type that holds it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `cong` in a type finds its function's result
    ///   minted, and an operation over a parameter or a call its type.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| ret.len() <= self.synthesised.len().saturating_mul(3)
        && ret.is_sorted_by_key(|&node| (self.tree.node(node).map(|held| held.span().start()), node)))]
    pub(super) fn synthesised_types(&self) -> Vec<NodeIndex>
    {
        let mut types = Vec::new();
        for site in self.synthesised.iter().skip(self.current.synthesised) {
            let Some(&Plan::Derived(Derived {
                stance: Stance::Synthesised(synthesis, typings),
                ..
            })) = self.plans.get(usize::from(site.at.node))
            else {
                continue;
            };
            if let Synthesis::Mapped { codomain, .. } | Synthesis::Bound { codomain, .. } =
                synthesis
            {
                types.push(codomain.node());
            }
            types.extend(
                [typings.transported, typings.onward]
                    .into_iter()
                    .flatten()
                    .map(Typed::node),
            );
        }
        // Source order, not the tree's level order: a parameter's type sits
        // deeper than the result written after it, so a later index, yet an
        // operation inside that result reads it.
        types.sort_unstable_by_key(|&node| {
            (self.tree.node(node).map(|held| held.span().start()), node)
        });
        types.dedup();
        types
    }

    /// What the path operand `path` is read at when its own form does not
    /// spell its type: a parameter by its binder's written type, a call by
    /// its function's written result.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified every node.
    /// - ensures: through transparent plans, a variable, or a binder named in a
    ///   type, whose binder's written type is a path type under any
    ///   parentheses, as [`Typed::Parameter`]; a call whose head is a
    ///   declaration whose tail or signature writes a path result, or a
    ///   recursive call's descent claim, as [`Typed::Called`].
    /// - fails: [`synthesised::Absent::Unread`] for any other path.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn steps to the operand of a transparent node, strictly deeper
    /// in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path parameter in a body and in a type, a call of a
    ///   definition, of a signature and a recursive call each read, a parameter
    ///   of no path type not.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(typed) => self.path_written(typed.node()).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn typed(
        &self,
        path: NodeIndex,
    ) -> Maybe<Typed, synthesised::Absent>
    {
        let unread = Maybe::Absent(synthesised::Absent::Unread);
        let mut at = path;
        while let Some(&Plan::Transparent(inner)) = self.plans.get(usize::from(at)) {
            at = inner;
        }
        let parameter = |binder: ScopeId, in_type: Option<Frame>| match self.scope.declared(binder)
        {
            Maybe::Present(declared) if self.path_written(declared).is_some() => {
                Maybe::Present(Typed::Parameter { declared, in_type })
            },
            Maybe::Present(_) | Maybe::Absent(_) => unread,
        };
        match self.plans.get(usize::from(at)) {
            Some(&Plan::Variable(_, binder)) => parameter(binder, None),
            Some(&Plan::StaticApplication(Code::Bound { from, binder, .. }, arguments))
                if arguments.start == arguments.end =>
            {
                parameter(binder, Some(from))
            },
            Some(&Plan::Application(head, arguments)) => {
                let mut head = head;
                while let Some(&Plan::Transparent(inner)) = self.plans.get(usize::from(head)) {
                    head = inner;
                }
                let (callee, descends) = match self.plans.get(usize::from(head)) {
                    Some(&Plan::Constant(constant)) => (self.callee_of(constant), false),
                    Some(&Plan::Variable(_, binder)) if self.recursions.contains_key(&binder) => {
                        let tail = match self.scope.declared(binder) {
                            Maybe::Present(tail) => match self.plans.get(usize::from(tail)) {
                                Some(&Plan::Function(function)) => self.tail_callee(function),
                                _ => None,
                            },
                            Maybe::Absent(_) => None,
                        };
                        (tail, true)
                    },
                    _ => (None, false),
                };
                // A descent passes the parameters before the staged one as the
                // variables they are in the body, which a type never binds.
                let descends_in_type = descends && self.in_type.contains(&at);
                match callee {
                    Some(callee)
                        if self.path_written(callee.result).is_some() && !descends_in_type =>
                    {
                        Maybe::Present(Typed::Called(Callee {
                            arguments,
                            descends,
                            ..callee
                        }))
                    },
                    Some(_) | None => unread,
                }
            },
            _ => unread,
        }
    }

    /// What a call of the declaration at `constant` reads its result off: a
    /// function tail's written result, the codomain of the telescope or the
    /// value function its signature writes, or the returner the arrows of
    /// its thunked signature end in.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified the declaration.
    /// - ensures: the tail's parameters and result when either half is a tail
    ///   writing a result; otherwise, when the signature is written as `(x : A,
    ///   …) => B` through parentheses, its entries and `B`, and as `A => B`, no
    ///   binders, the domains' count and `B`; when it is written as the thunk
    ///   that alias stands for, `+U (A1 -> … -> An -> -F B)`, the arrows every
    ///   one dependent, `(x : A) -> C`, or none, the binders the dependent
    ///   arrows' entries hold, the arrows' count and the returner `-F B`; the
    ///   call's own fields left empty.
    /// - fails: none otherwise, a chain mixing dependent and plain arrows among
    ///   them.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn steps to the operand of a transparent node or to an arrow's
    /// codomain, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of a definition and of a signature each read
    ///   their result, and a signature written as the alias and as the thunk it
    ///   stands for read the same dependent result.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    /// - witness: `lower::identity::tests::a_call_reads_a_dependent_result_through_either_spelling_812`
    #[spec(ensures: |ret| ret.is_none_or(|callee| callee.arguments.start == callee.arguments.end))]
    fn callee_of(
        &self,
        constant: ConstantIndex,
    ) -> Option<Callee>
    {
        if let Some(callee) = self
            .function_of(constant)
            .and_then(|function| self.tail_callee(function))
        {
            return Some(callee);
        }
        let Maybe::Present(Half {
            operand: Operand::Written(written),
            ..
        }) = self.collected.slots.get(usize::from(constant))?.signature
        else {
            return None;
        };
        let through = |mut at: NodeIndex| {
            while let Some(&Plan::Transparent(inner)) = self.plans.get(usize::from(at)) {
                at = inner;
            }
            at
        };
        let none = Stretch { start: 0, end: 0 };
        let (parameters, arity, result, returned) =
            match self.plans.get(usize::from(through(written.node))) {
                Some(&Plan::Telescope(entries, codomain)) => (
                    entries,
                    entries.end.saturating_sub(entries.start),
                    codomain,
                    false,
                ),
                Some(&Plan::ValueFunction(domains, codomain)) => (
                    none,
                    domains.end.saturating_sub(domains.start),
                    codomain,
                    false,
                ),
                Some(&Plan::Former(TypeFormer::Thunk, held)) => {
                    let mut at = through(held);
                    let mut arity = 0_usize;
                    let mut plain = false;
                    let mut bound: Option<Stretch> = None;
                    loop {
                        match self.plans.get(usize::from(at)) {
                            Some(&Plan::Arrow(_, codomain)) => {
                                plain = true;
                                arity = arity.saturating_add(1);
                                at = through(codomain);
                            },
                            Some(&Plan::DependentArrow(entries, codomain)) => {
                                bound = match bound {
                                    None => Some(entries),
                                    Some(held) if held.end == entries.start => Some(Stretch {
                                        start: held.start,
                                        end: entries.end,
                                    }),
                                    Some(_) => return None,
                                };
                                arity =
                                    arity.saturating_add(entries.end.saturating_sub(entries.start));
                                at = through(codomain);
                            },
                            Some(&Plan::Former(TypeFormer::Returner, _)) => break,
                            _ => return None,
                        }
                    }
                    if plain && bound.is_some() {
                        return None;
                    }
                    (bound.unwrap_or(none), arity, at, true)
                },
                _ => return None,
            };
        Some(Callee {
            parameters,
            arity,
            recursive: None,
            result,
            returned,
            arguments: none,
            descends: false,
        })
    }

    /// What a call of the function tail `function` reads its result off.
    ///
    /// # Specification
    /// - ensures: the tail's parameters, the parameter it stages when it
    ///   recurses and its written result, a returner, when it writes one; the
    ///   call's own fields left empty.
    /// - fails: none for a tail with no written result.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::callee_of`].
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| ret.is_none_or(|callee| callee.returned))]
    fn tail_callee(
        &self,
        function: Function,
    ) -> Option<Callee>
    {
        let Maybe::Present(result) = function.result
        else {
            return None;
        };
        let none = Stretch { start: 0, end: 0 };
        Some(Callee {
            parameters: function.parameters,
            arity: function
                .parameters
                .end
                .saturating_sub(function.parameters.start),
            recursive: match function.recursion {
                Maybe::Present(scope) => Some(self.recursions.get(&scope).map_or(0, |recursion| {
                    super::stretch(&self.parameters, recursion.uniform).len()
                })),
                Maybe::Absent(_) => None,
            },
            result,
            returned: true,
            arguments: none,
            descends: false,
        })
    }

    /// The path type the type at `written` writes, under at most one returner
    /// and any parentheses.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified `written`.
    /// - ensures: the path type's node exactly when the walk through
    ///   transparent plans and at most one returner meets one.
    /// - fails: none for any other type.
    /// - panics: none.
    ///
    /// # Termination
    /// Every turn steps to an operand of the node it read, strictly deeper in
    /// a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::typed`].
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| ret.is_none_or(|path| matches!(self.plans.get(usize::from(path)), Some(&Plan::Path(..)))))]
    fn path_written(
        &self,
        written: NodeIndex,
    ) -> Option<NodeIndex>
    {
        let mut at = written;
        let mut returned = false;
        loop {
            match self.plans.get(usize::from(at)) {
                Some(&Plan::Transparent(inner)) => at = inner,
                Some(&Plan::Former(TypeFormer::Returner, inner)) if !returned => {
                    returned = true;
                    at = inner;
                },
                Some(&Plan::Path(..)) => return Some(at),
                _ => return None,
            }
        }
    }

    /// The node a derived operation's path operand `path` reads its type at.
    ///
    /// # Specification
    /// - requires: the ascending sweep has classified every node; `read` holds
    ///   the synthesised operations whose own type is read.
    /// - ensures: through parentheses, the node itself when it is a loop, a
    ///   word of a loop's words, an answered derived operation, one in `read`,
    ///   or a parameter or a call [`Self::typed`] reads in a declaration that
    ///   lowers.
    /// - fails: [`synthesised::Absent::Unread`] for any other path;
    ///   [`LoweringRefusal::BudgetExceeded`] when the walk outruns the
    ///   allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Termination
    /// Every turn spends one unit of the allowance and steps to the operand of
    /// a transparent node, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::refuse_unsynthesised`].
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(captures: before = self.fuel.remaining, ensures: self.fuel.remaining <= before)]
    fn reads_path(
        &mut self,
        path: NodeIndex,
        read: &alloc::collections::BTreeSet<NodeIndex>,
    ) -> Result<Maybe<NodeIndex, synthesised::Absent>, LoweringRefusal<'source>>
    {
        let mut at = path;
        loop {
            self.fuel.spend()?;
            let worded = match self.plans.get(usize::from(at)) {
                Some(&Plan::Transparent(inner)) => {
                    at = inner;
                    continue;
                },
                Some(&Plan::Constant(constant)) => {
                    matches!(self.words_at(constant), Maybe::Present(_))
                },
                Some(&Plan::Constructor(constructed)) => {
                    matches!(self.words_at(constructed.family), Maybe::Present(_))
                },
                Some(&Plan::Derived(Derived {
                    stance: Stance::Answered(_),
                    ..
                })) => true,
                Some(&Plan::Derived(_)) => read.contains(&at),
                _ => match self.typed(at) {
                    Maybe::Present(typed) => !self.collected.refused(typed.node()).0,
                    Maybe::Absent(_) => false,
                },
            };
            return Ok(if worded {
                Maybe::Present(at)
            }
            else {
                Maybe::Absent(synthesised::Absent::Unread)
            });
        }
    }

    /// Read the identity type written at `answer`: a path type or a flow type,
    /// under at most a returner and any parentheses.
    ///
    /// # Specification
    /// - requires: `answer` is a node read where a result is read.
    /// - ensures: the path answer exactly when the walk from `answer` through
    ///   parenthesised types and one `-F` reaches a path type, and the flow
    ///   answer when it reaches a type application headed `Flow` at three
    ///   arguments or a flow between types written `A ⇝ B`.
    /// - provides: the classification-time guarantee that a derived operation's
    ///   answer mints as `F (Path(A, a, b))` or `F (Flow(A, a, b))`.
    /// - fails: the unannotated refusal at `site` when the walk reaches another
    ///   form; [`LoweringRefusal::BudgetExceeded`] when it outruns the
    ///   allowance; the refusals the tree's molds yield.
    /// - panics: none.
    ///
    /// # Errors
    /// The walk's refusal.
    ///
    /// # Termination
    /// Every turn spends one unit of the lowerer's allowance and steps to the
    /// operand of the node it read, strictly deeper in a finite tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `-F Path(…)`, a parenthesised `-F(Path(…))`, a flow
    ///   answer written either way, and an integer answer.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_needs_a_written_path_answer`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    #[spec(captures: before = self.fuel.remaining, ensures: self.fuel.remaining <= before)]
    fn answers_path(
        &mut self,
        site: Site,
        answer: NodeIndex,
    ) -> Result<Answered, LoweringRefusal<'source>>
    {
        let mut position = answer;
        let mut returned = false;
        let unannotated = site.out(FragmentBoundary::Unannotated);
        loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(position)
            else {
                return Err(unannotated);
            };
            let Shape::Form { former, .. } = shape_of(self.pbg, node)?
            else {
                return Err(unannotated);
            };
            let (wrapped, applied) = match former {
                Former::PathType => return Ok(Answered::Path),
                Former::ReturnerType if !returned => {
                    returned = true;
                    (true, false)
                },
                Former::ParenthesizedType | Former::RelationType => (false, false),
                Former::TypeApplication => (false, true),
                Former::Name
                | Former::Constructor
                | Former::Hole
                | Former::Number
                | Former::Text
                | Former::Parenthesized
                | Former::Unit
                | Former::Thunk
                | Former::Lambda
                | Former::Block
                | Former::Return
                | Former::Exit
                | Former::Become
                | Former::Loop
                | Former::While
                | Former::For
                | Former::Break
                | Former::Continue
                | Former::Force
                | Former::Run
                | Former::Call
                | Former::Case
                | Former::Telescope
                | Former::Injection
                | Former::LazyRecord
                | Former::Binary
                | Former::Unary
                | Former::Projection
                | Former::TypeHead
                | Former::TypePath
                | Former::Universe
                | Former::ThunkType
                | Former::ReturnerType
                | Former::ArrowType
                | Former::ProductType
                | Former::SumType
                | Former::LazyProductType
                | Former::TelescopeType
                | Former::LabelledSumType
                | Former::LazyRecordType
                | Former::ValueFunctionType
                | Former::StaticAbstraction
                | Former::CapabilityType
                | Former::AtType
                | Former::Scope
                | Former::Declaration
                | Former::AttributeBlock
                | Former::Import
                | Former::Module
                | Former::Data
                | Former::Mutual
                | Former::Instantiation
                | Former::SessionType
                | Former::Action
                | Former::Offer
                | Former::Access
                | Former::World
                | Former::WorldDeclaration
                | Former::Reserved
                | Former::Unadmitted => return Err(unannotated),
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let written = scratch
                .pieces
                .iter()
                .filter(|piece| matches!(**piece, Piece::Operand(_)))
                .count();
            let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                Piece::Operand(operand) => Some(operand.node),
                Piece::Tile { .. } => None,
            });
            let inner = match (operands.next(), operands.next()) {
                (Some(inner), None) => Some(inner),
                _ => None,
            };
            let keyword = scratch.pieces.iter().find_map(|piece| match *piece {
                Piece::Tile { at, .. } => Some(at),
                Piece::Operand(_) => None,
            });
            let flows = scratch.pieces.iter().any(|piece| {
                matches!(*piece, Piece::Tile { label, .. } if label == TileName::UNIVERSE_FLOW)
            });
            self.scratch = scratch;
            read?;
            if former == Former::RelationType {
                return if flows {
                    Ok(Answered::Flow)
                }
                else {
                    Err(unannotated)
                };
            }
            if applied {
                let flow = written == 3_usize
                    && keyword.is_some_and(|at| self.name_at(at).as_ref() == FLOW);
                return if flow {
                    Ok(Answered::Flow)
                }
                else {
                    Err(unannotated)
                };
            }
            let returner = !wrapped
                || keyword.is_some_and(|at| {
                    type_former(self.name_at(at)) == Maybe::Present(TypeFormer::Returner)
                });
            match inner {
                Some(inner) if returner => position = inner,
                _ => return Err(unannotated),
            }
        }
    }

    /// Mint the derived operation `derived`: the transport it unfolds to.
    ///
    /// # Specification
    /// - requires: the operands, the answer and a synthesised `cong`'s codomain
    ///   are already minted or absent.
    /// - ensures: the carrier and the endpoints are the answer's, a returner
    ///   over `Path(A, a, b)` or `Flow(A, a, b)` relocated to the operation's
    ///   frame, or, synthesised, the path's own as [`Self::identity_of`] reads
    ///   it: `back(p)` at `p : Path(A, a, b)` stands at `Path(A, b, a)`, `p
    ///   then q` at `Path(A, a, c)` for `q : Path(A, b, c)`, and `cong(f, p)`
    ///   at `Path(B, ⟨f a⟩, ⟨f b⟩)`, `B` the result type `f`'s definition
    ///   writes. `back(p)` is `tr(y. Path(A, y, b), p, here(b))`, `p then q` is
    ///   `tr(y. Path(A, a, y), q, p)` and `cong(f, p)` is `tr(y. Path(A, a,
    ///   ⟨force f y⟩), p, here(a))`; `back(f)` under a flow answer is the
    ///   symmetry ride `ride(y. Flow(A, y, b), f, stay(b))`. The path type an
    ///   operation stands at is recorded against its transport when both its
    ///   endpoints are read. The operation carries the written origin, the lift
    ///   of `cong`'s map under the motive's binder the map's own, as the copy
    ///   of the one the transport reads, and every other node minted for it the
    ///   inserted identity origin. Nothing when an operand, the answer or the
    ///   codomain did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation read back out of the arena and
    ///   checked, answered and synthesised.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_parameter_map_under_cong_answers_at_its_bytes_443`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_derived(
        &self,
        derived: Derived,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let (first, second) = match derived.derivation {
            Derivation::Back { path } => match self.value_at(path) {
                Maybe::Present(path) => (path, path),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => match (self.value_at(first), self.value_at(second)) {
                (Maybe::Present(first), Maybe::Present(second)) => (first, second),
                (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                    return Maybe::Absent(reason);
                },
            },
        };
        let mut mark = sink.arena.watermark();
        let inserted = origin.inserted(Insertion::Identity);
        let stood = match derived.stance {
            Stance::Answered(answer) => self.answered_at(answer, derived.frame, sink),
            Stance::Synthesised(synthesis, typings) => self.synthesised_at(
                (derived.derivation, synthesis, typings),
                first,
                derived.frame,
                sink,
            ),
        };
        let Stood {
            answered,
            carrier,
            left,
            right,
        } = match stood {
            Maybe::Present(stood) => stood,
            Maybe::Absent(reason) => {
                record_since(
                    sink,
                    mark,
                    inserted,
                    Maybe::Absent(rooted::Absent::Unminted),
                );
                return Maybe::Absent(reason);
            },
        };
        let root = match (answered, derived.derivation, right) {
            (Answered::Path, Derivation::Back { .. }, Maybe::Present(right)) => {
                // Reflexivity at a looped point is its empty word, as a
                // written `here` there reads.
                match self.looped_reflexivity(right, sink) {
                    Some(empty) => gandr_core_term::identity::back_from(
                        sink.arena, carrier, right, empty, first,
                    ),
                    None => gandr_core_term::identity::back(sink.arena, carrier, right, first),
                }
            },
            (Answered::Flow, Derivation::Back { .. }, Maybe::Present(right)) => {
                gandr_core_term::identity::back_flow(sink.arena, carrier, right, first)
            },
            (Answered::Path, Derivation::Then { .. }, _) => {
                gandr_core_term::identity::then(sink.arena, carrier, left, first, second)
            },
            (Answered::Path, Derivation::Cong { .. }, _) => {
                // The transport reads the map only lifted under its motive's
                // binder: the lift is the written map's copy, so it answers
                // at the map's bytes.
                let lifted = gandr_core_term::shift_value(sink.arena, first, Binders::ONE)
                    .settle(sink.arena);
                record_copies(sink, mark, &[Carried::Value(first, lifted)], inserted);
                mark = sink.arena.watermark();
                gandr_core_term::identity::cong_lifted(sink.arena, carrier, lifted, left, second)
            },
            (Answered::Path | Answered::Flow, Derivation::Back { .. }, Maybe::Absent(_))
            | (Answered::Flow, Derivation::Then { .. } | Derivation::Cong { .. }, _) => {
                record_since(
                    sink,
                    mark,
                    inserted,
                    Maybe::Absent(rooted::Absent::Unminted),
                );
                return Maybe::Absent(lowered::Absent::OtherSort);
            },
        };
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));
        if answered == Answered::Path
            && let Maybe::Present(right) = right
        {
            let _first = sink.identities.insert(root, Identity {
                carrier,
                left,
                right,
            });
        }

        Maybe::Present(Lowered::Computation(root))
    }

    /// The empty word at `point` when `point` is a looped point: the
    /// reflexivity a written `here(point)` lowers to there.
    ///
    /// # Specification
    /// - requires: `point` is minted in `sink`'s arena.
    /// - ensures: for the first words whose point `point` spells — a closed
    ///   constructor term of the words' family, unapplied, whose tags in
    ///   pre-order are the point's — that words' empty word, minted as a
    ///   written `here` at the point mints it; none for any other value.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is minted, and the words it matches are
    ///   read off the collection a predicate would read again.
    /// - intension: one pre-order walk of `point` per words, cut at the point's
    ///   length; recursion-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `back(loop)` at the circle's point moves the empty
    ///   word, and `back(p)` over a parameter's point moves `here`.
    /// - witness: `lower::identity::tests::back_at_a_looped_point_moves_its_empty_word_1003`
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    fn looped_reflexivity(
        &self,
        point: ValueId,
        sink: &mut Sink<'_>,
    ) -> Option<ValueId>
    {
        let constant = |slot: crate::module::SlotIndex| {
            self.collected
                .slots
                .get(usize::from(slot))
                .map(|entry| entry.constant)
        };
        let mut tags = Vec::new();
        let mut pending = Vec::new();
        let words = self.collected.words.iter().find(|words| {
            let Some(family) = self
                .collected
                .data
                .get(words.family)
                .and_then(|form| constant(form.slot))
            else {
                return false;
            };
            tags.clear();
            pending.clear();
            pending.push(point);
            while let Some(at) = pending.pop() {
                let Some(&Value::Constructor {
                    datatype,
                    tag,
                    ref fields,
                }) = sink.arena.value(at)
                else {
                    return false;
                };
                let unapplied = matches!(
                    sink.arena.value_type(datatype),
                    Some(&ValueType::Data { declaration, ref arguments })
                        if declaration == family && arguments.is_empty()
                );
                if !unapplied || tags.len() >= words.point.len() {
                    return false;
                }
                tags.push(gandr_core_term::RuleNode::Constructor(tag));
                pending.extend(fields.iter().rev());
            }
            *tags == *words.point
        })?;
        let own = constant(words.slot)?;
        let word = sink.arena.value_type_data(own, Vec::new());
        Some(
            sink.arena
                .value_constructor(word, gandr_core_term::FreeCells::nil(), Vec::new()),
        )
    }

    /// The identity type `answer` writes, relocated to `frame` where the
    /// derived operation answering it stands.
    ///
    /// # Specification
    /// - requires: the answer is already minted or absent.
    /// - ensures: the carrier and the endpoints of the returner over `Path(A,
    ///   a, b)` or `Flow(A, a, b)` the answer mints, relocated from its frame
    ///   to `frame`; a loop arm's answer is `Path(B, y, y)`, `y` the answer at
    ///   the loop's point its arm binds innermost.
    /// - fails: the answer's absence when it did not lower; the other-sort
    ///   absence when it mints no such returner.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path answer, a flow answer and a loop arm's.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(stood) => matches!(stood.right, Maybe::Present(_)),
        | Maybe::Absent(_) => true,
    })]
    fn answered_at(
        &self,
        answer: Answer,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<Stood, lowered::Absent>
    {
        let written = match self.answered_type(answer, sink) {
            Maybe::Present(written) => written,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let gap = self
            .scope
            .telescope_binders(frame)
            .count()
            .saturating_sub(self.scope.telescope_binders(answer.frame).count());
        let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
        let answered = self.relocate(
            sink.arena,
            written,
            answer.frame,
            Telescope::Signature,
            lift,
            None,
        );
        let Some(&CompType::Returner { result, .. }) = sink.arena.comp_type(answered)
        else {
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let (answered, carrier, left, right) = match (answer.over, sink.arena.value_type(result)) {
            (super::native::Over::Loop { arm }, Some(_)) => {
                let gap = self
                    .scope
                    .telescope_binders(frame)
                    .count()
                    .saturating_sub(self.scope.telescope_binders(arm).count());
                let index = u32::try_from(gap).unwrap_or(u32::MAX);
                let point = sink.arena.value_variable(
                    gandr_core_term::Zone::Intuitionistic,
                    gandr_kernel_term::DeBruijnIndex::from(index),
                );
                (Answered::Path, result, point, point)
            },
            (
                super::native::Over::Written | super::native::Over::Returning,
                Some(&ValueType::Path {
                    carrier,
                    left,
                    right,
                }),
            ) => (Answered::Path, carrier, left, right),
            (
                super::native::Over::Written | super::native::Over::Returning,
                Some(&ValueType::Flow {
                    carrier,
                    source,
                    target,
                }),
            ) => (Answered::Flow, carrier, source, target),
            (..) => return Maybe::Absent(lowered::Absent::OtherSort),
        };

        Maybe::Present(Stood {
            answered,
            carrier,
            left,
            right: Maybe::Present(right),
        })
    }

    /// The path type a synthesised derived operation stands at, read off its
    /// operands, `function` the first operand's value, the operation standing
    /// under `frame`.
    ///
    /// # Specification
    /// - requires: the operands, a `cong`'s codomain and the types
    ///   [`Self::synthesised_types`] lists are already minted or absent;
    ///   [`Self::refuse_unsynthesised`] admitted the operation.
    /// - ensures: for `back(p)` at `p : Path(A, a, b)`, `Path(A, b, a)`; for `p
    ///   then q`, `Path(A, a, c)` with `c` read when `q : Path(A, b, c)` is,
    ///   absent otherwise; for `cong(f, p)`, `Path(B, ⟨force f a⟩, ⟨force f
    ///   b⟩)` with `B` the returner's result the codomain mints: closed for a
    ///   declared function, carried as [`Self::carried`] carries it for a bound
    ///   map. Each path's type is read as [`Self::identity_of`] reads it under
    ///   `frame`.
    /// - fails: the unminted absence when the motive's path's type is not read;
    ///   the codomain's absence, or the other-sort absence when it mints no
    ///   returner.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation over a word, over another, over a
    ///   parameter and over a call, and `cong` at a bound map.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(stood) => stood.answered == Answered::Path,
        | Maybe::Absent(_) => true,
    })]
    fn synthesised_at(
        &self,
        (derivation, synthesis, typings): (Derivation, Synthesis, Typings),
        function: ValueId,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<Stood, lowered::Absent>
    {
        let transported = match derivation {
            Derivation::Back { path } | Derivation::Cong { path, .. } => path,
            Derivation::Then { first, .. } => first,
        };
        let Maybe::Present(read) = self.identity_of(transported, typings.transported, frame, sink)
        else {
            return Maybe::Absent(lowered::Absent::Unminted);
        };
        let stood = match (derivation, synthesis) {
            (Derivation::Back { .. }, _) => Stood {
                answered: Answered::Path,
                carrier: read.carrier,
                left: read.right,
                right: Maybe::Present(read.left),
            },
            (Derivation::Then { second, .. }, _) => Stood {
                answered: Answered::Path,
                carrier: read.carrier,
                left: read.left,
                right: self
                    .identity_of(second, typings.onward, frame, sink)
                    .map(|onward| onward.right),
            },
            (
                Derivation::Cong { .. },
                Synthesis::Mapped { codomain, .. } | Synthesis::Bound { codomain, .. },
            ) => {
                let result = match codomain {
                    Codomain::Returner(codomain) => {
                        let written = match self.comp_type_at(codomain) {
                            Maybe::Present(written) => written,
                            Maybe::Absent(reason) => return Maybe::Absent(reason),
                        };
                        let Some(&CompType::Returner { result, .. }) =
                            sink.arena.comp_type(written)
                        else {
                            return Maybe::Absent(lowered::Absent::OtherSort);
                        };
                        result
                    },
                    Codomain::Returned(codomain) => match self.value_type_at(codomain) {
                        Maybe::Present(result) => result,
                        Maybe::Absent(reason) => return Maybe::Absent(reason),
                    },
                };
                let carrier = match synthesis {
                    Synthesis::Bound {
                        frame: from,
                        in_type,
                        ..
                    } => match self.carried(result, from, in_type, frame, sink) {
                        Maybe::Present(carried) => carried,
                        Maybe::Absent(_) => return Maybe::Absent(lowered::Absent::Unminted),
                    },
                    Synthesis::Paths
                    | Synthesis::Mapped { .. }
                    | Synthesis::Thunked { .. }
                    | Synthesis::Stated { .. } => result,
                };
                let mut image = |point| {
                    let forced = sink.arena.computation_force(function);
                    let applied = sink.arena.computation_application(forced, point);
                    sink.arena.value_returned(applied)
                };
                let left = image(read.left);
                let right = image(read.right);
                Stood {
                    answered: Answered::Path,
                    carrier,
                    left,
                    right: Maybe::Present(right),
                }
            },
            (
                Derivation::Cong { .. },
                Synthesis::Paths | Synthesis::Thunked { .. } | Synthesis::Stated { .. },
            ) => {
                return Maybe::Absent(lowered::Absent::Unminted);
            },
        };

        Maybe::Present(stood)
    }

    /// The path type the derived operation's operand `path` stands at, read
    /// off `typed` when the classification recorded one, the operation
    /// standing under `frame`.
    ///
    /// # Specification
    /// - requires: `path` and the type `typed` names are already minted or
    ///   absent.
    /// - ensures: a parameter at its binder's written type and a call at its
    ///   function's written result at its arguments, each carried to where the
    ///   operation stands; otherwise a loop, or a word of a loop's words,
    ///   stands at `Path(F, x, x)`, `F` its family and `x` the point the words
    ///   spell, minted as [`Self::words_point`] mints them, and a derived
    ///   operation's returned transport at the path type recorded against it.
    /// - fails: [`synthesised::Absent::Unread`] for any other value, and for a
    ///   path or a type that did not lower.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loop, the empty word, an operation over a word, a
    ///   parameter and a call.
    /// - witness: `lower::identity::tests::a_derived_operation_synthesises_its_path_at_the_words`
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(read) => sink.arena.value_type(read.carrier).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn identity_of(
        &self,
        path: NodeIndex,
        typed: Option<Typed>,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<Identity, synthesised::Absent>
    {
        let unread = Maybe::Absent(synthesised::Absent::Unread);
        match typed {
            Some(Typed::Parameter { declared, in_type }) => {
                return self.parameter_identity(declared, in_type, frame, sink);
            },
            Some(Typed::Called(callee)) => return self.called_identity(callee, frame, sink),
            None => {},
        }
        let Maybe::Present(value) = self.value_at(path)
        else {
            return unread;
        };
        let worded = match sink.arena.value(value) {
            Some(&Value::Returned(transport)) => {
                return sink
                    .identities
                    .get(&transport)
                    .copied()
                    .map_or(unread, Maybe::Present);
            },
            Some(&Value::Constant(constant)) => self.words_at(constant),
            Some(&Value::Constructor { datatype, .. }) => match sink.arena.value_type(datatype) {
                Some(&ValueType::Data { declaration, .. }) => self.words_at(declaration),
                _ => return unread,
            },
            _ => return unread,
        };
        let Maybe::Present(words) = worded
        else {
            return unread;
        };
        match self.words_point(sink.arena, words) {
            Maybe::Present((carrier, point)) => Maybe::Present(Identity {
                carrier,
                left: point,
                right: point,
            }),
            Maybe::Absent(_) => unread,
        }
    }

    /// The path type a parameter's binder writes, `declared`, carried to the
    /// parameter's use: a body under `frame`, or a type under `in_type`.
    ///
    /// # Specification
    /// - requires: `declared` is minted or absent, read where a value type is
    ///   read under the frame its binder extends.
    /// - ensures: the written path type, carried as [`Self::carried`] carries
    ///   it from the frame its binder extends.
    /// - fails: [`synthesised::Absent::Unread`] when the type did not lower or
    ///   is no path type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path parameter in a body and in a type.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(read) => sink.arena.value_type(read.carrier).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn parameter_identity(
        &self,
        declared: NodeIndex,
        in_type: Option<Frame>,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<Identity, synthesised::Absent>
    {
        let unread = Maybe::Absent(synthesised::Absent::Unread);
        let (Maybe::Present(written), super::Reading::ValueType(from)) =
            (self.value_type_at(declared), self.reading(declared))
        else {
            return unread;
        };
        match self.carried(written, from, in_type, frame, sink) {
            Maybe::Present(carried) => path_identity(sink.arena, carried),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The value type `written`, read under `from`, carried to a use whose
    /// binders extend `from`: a body under `frame`, or a type under `in_type`.
    ///
    /// # Specification
    /// - requires: `written` is minted in `sink`, read under `from`, and every
    ///   binder of `from` stands where the use does.
    /// - ensures: `written` with a binder inserted at each frame of its chain
    ///   no telescope counts and every index raised past the frames between it
    ///   and `frame`, for a use in a body; raised past the telescope's binders
    ///   between it and `in_type`, for a use in a type.
    /// - fails: [`synthesised::Absent::Unread`] when the relocation mints no
    ///   returner.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path parameter and a bound map's codomain, each in
    ///   a body and in a type.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(carried) => sink.arena.value_type(carried).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn carried(
        &self,
        written: ValueTypeId,
        from: Frame,
        in_type: Option<Frame>,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<ValueTypeId, synthesised::Absent>
    {
        let between = |inner: Frame, outer: Frame, counted: fn(bool) -> bool| {
            let depth = |at: Frame| {
                self.scope
                    .telescope_binders(at)
                    .filter(|&binds| counted(binds))
                    .count()
            };
            Binders::from(
                u32::try_from(depth(inner).saturating_sub(depth(outer))).unwrap_or(u32::MAX),
            )
        };
        if let Some(read) = in_type {
            let lift = between(read, from, |binds| binds);
            let lifted = gandr_core_term::shift_value_type(sink.arena, written, lift);
            return Maybe::Present(lifted.settle(sink.arena));
        }
        let lift = between(frame, from, |_| true);
        let wrapped = sink.arena.comp_type_returner(written);
        let relocated = self.relocate(sink.arena, wrapped, from, Telescope::Signature, lift, None);
        match sink.arena.comp_type(relocated) {
            Some(&CompType::Returner { result, .. }) => Maybe::Present(result),
            _ => Maybe::Absent(synthesised::Absent::Unread),
        }
    }

    /// The path type a call's function writes as its result, at the call's
    /// arguments, the call standing under `frame`.
    ///
    /// # Specification
    /// - requires: the result and every argument the call applies are minted or
    ///   absent; the function is declared at the outermost frame, so its result
    ///   is closed but for its binders.
    /// - ensures: the written path type, under its returner for a tail, with
    ///   each binder the result's telescope counts replaced by its argument,
    ///   the innermost first: the applied arguments in order, and for a descent
    ///   the parameters before the staged one as the variables they are where
    ///   the call stands.
    /// - fails: [`synthesised::Absent::Unread`] when the result or an argument
    ///   did not lower, the arguments do not match the arity, a frame other
    ///   than a binder of the function counts in the result's telescope, a
    ///   descent stands in a type, or the result is no path type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call of a definition whose result names its
    ///   parameter, in a body and in a type, a call of a signature, and a
    ///   recursive call over a uniform leading parameter.
    /// - witness: `lower::identity::tests::a_derived_operation_reads_a_parameter_or_a_call`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present(read) => sink.arena.value_type(read.carrier).is_some(),
        | Maybe::Absent(_) => true,
    })]
    fn called_identity(
        &self,
        callee: Callee,
        frame: Frame,
        sink: &mut Sink<'_>,
    ) -> Maybe<Identity, synthesised::Absent>
    {
        let unread = Maybe::Absent(synthesised::Absent::Unread);
        let written = if callee.returned {
            self.comp_type_at(callee.result)
        }
        else {
            self.value_type_at(callee.result)
                .map(|written| sink.arena.comp_type_returner(written))
        };
        let Maybe::Present(written) = written
        else {
            return unread;
        };
        let from = self.reading(callee.result).frame();
        let parameters = super::stretch(&self.parameters, callee.parameters);
        let applied = super::stretch(&self.operands, callee.arguments);
        let mut arguments = Vec::with_capacity(callee.arity);
        if callee.descends {
            let staged = callee.recursive.unwrap_or(0);
            let (Some(leading), true) = (
                parameters.get(.. staged),
                applied.len() == parameters.len().saturating_sub(staged),
            )
            else {
                return unread;
            };
            let depth = |at: Frame| self.scope.telescope_binders(at).count();
            for parameter in leading {
                let index = depth(frame).saturating_sub(depth(Frame::Inner(parameter.frame)));
                arguments.push(sink.arena.value_variable(
                    gandr_core_term::Zone::Intuitionistic,
                    gandr_kernel_term::DeBruijnIndex::from(
                        u32::try_from(index).unwrap_or(u32::MAX),
                    ),
                ));
            }
        }
        else if applied.len() != callee.arity {
            return unread;
        }
        for &argument in applied {
            let Maybe::Present(value) = self.value_at(argument)
            else {
                return unread;
            };
            arguments.push(as_endpoint(sink.arena, value));
        }
        // The result's chain, innermost first: the binders from the last,
        // the frame a recursive tail binds its own name at between the staged
        // parameter and the ones before it.
        let mut chain: Vec<Option<usize>> = (0 .. parameters.len()).rev().map(Some).collect();
        if let Some(staged) = callee.recursive {
            let at = parameters.len().saturating_sub(staged).min(chain.len());
            chain.insert(at, None);
        }
        let binds: Vec<bool> = self.scope.telescope_binders(from).collect();
        if binds.len() != chain.len() {
            return unread;
        }
        let mut bound = Vec::with_capacity(chain.len());
        for (position, binds) in chain.into_iter().zip(binds) {
            match (binds, position) {
                (false, _) => {},
                (true, Some(position)) => bound.push(position),
                (true, None) => return unread,
            }
        }
        let mut instantiated = written;
        for (depth, &position) in bound.iter().enumerate() {
            let Some(&argument) = arguments.get(position)
            else {
                return unread;
            };
            let outside = bound.len().saturating_sub(depth).saturating_sub(1);
            let carried = gandr_core_term::shift_value(
                sink.arena,
                argument,
                Binders::from(u32::try_from(outside).unwrap_or(u32::MAX)),
            )
            .settle(sink.arena);
            instantiated =
                gandr_core_term::instantiate_comp_type(sink.arena, instantiated, carried);
        }
        match sink.arena.comp_type(instantiated) {
            Some(&CompType::Returner { result, .. }) => path_identity(sink.arena, result),
            _ => unread,
        }
    }

    /// Mint `transport(\X. T, p, v)`: the element transport in the family the
    /// abstraction's body denotes under its binder.
    ///
    /// # Specification
    /// - requires: the three operands are already minted or absent.
    /// - ensures: the transport of the value along the path in the decode of
    ///   the motive's body at the fuss-free level — the quoted type itself when
    ///   the body quotes one, so `\X. List(X)` is `y. List(El y)`. The
    ///   transport carries the written origin, every other node minted for it
    ///   the inserted identity origin, and the motive's written origin is
    ///   recorded against the transport, so a face answers each written motive
    ///   at its family's universe even where two motives denote one family.
    ///   Nothing when an operand did not lower or the motive minted as no
    ///   static abstraction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list motive over a universe path, read back out of
    ///   the arena.
    /// - witness: `lower::identity::tests::a_list_moves_along_a_universe_equivalence`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_transport(
        &self,
        (abstraction, path, value): (NodeIndex, NodeIndex, NodeIndex),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let (motive, path, value) = match (
            self.value_at(abstraction),
            self.value_at(path),
            self.value_at(value),
        ) {
            (Maybe::Present(motive), Maybe::Present(path), Maybe::Present(value)) => {
                (motive, path, value)
            },
            (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), _)
            | (_, _, Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let Some(&Value::StaticLambda(body)) = sink.arena.value(motive)
        else {
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let mark = sink.arena.watermark();
        let family = sink.arena.value_type_element(body, Level::zero());
        let inserted = origin.inserted(Insertion::Identity);
        let root = sink.arena.computation_path_transport(family, path, value);
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));
        if let Maybe::Present(written) = sink.origins.value(motive) {
            sink.origins.record_motive(root, written);
        }

        Maybe::Present(Lowered::Computation(root))
    }

    /// Mint `ride(\X. T, f, v)`: the ride of the value along the flow in the
    /// family the abstraction's body denotes under its binder.
    ///
    /// # Specification
    /// - requires: the three operands are already minted or absent.
    /// - ensures: the ride of the value along the flow in the decode of the
    ///   motive's body at the fuss-free level — the quoted type itself when the
    ///   body quotes one, so `\X. Run(X)` is `y. Run(y)`. The ride carries the
    ///   written origin and the family the inserted identity origin, and the
    ///   motive's written origin is recorded against the ride, as a transport's
    ///   is. Nothing when an operand did not lower or the motive minted as no
    ///   static abstraction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run motive over a session flow, read back out of
    ///   the arena.
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin)
                && matches!(sink.arena.computation(id), Some(&gandr_core_term::Computation::Ride { .. })),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_ride(
        &self,
        (abstraction, flow, value): (NodeIndex, NodeIndex, NodeIndex),
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let (motive, flow, value) = match (
            self.value_at(abstraction),
            self.value_at(flow),
            self.value_at(value),
        ) {
            (Maybe::Present(motive), Maybe::Present(flow), Maybe::Present(value)) => {
                (motive, flow, value)
            },
            (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), _)
            | (_, _, Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let Some(&Value::StaticLambda(body)) = sink.arena.value(motive)
        else {
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let mark = sink.arena.watermark();
        let family = sink.arena.value_type_element(body, Level::zero());
        let root = sink.arena.computation_ride(family, flow, value);
        let inserted = origin.inserted(Insertion::Identity);
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));
        if let Maybe::Present(written) = sink.origins.value(motive) {
            sink.origins.record_motive(root, written);
        }

        Maybe::Present(Lowered::Computation(root))
    }

    /// Mint `f then g` where a flow is answered: the returned composite.
    ///
    /// # Specification
    /// - requires: both operands are already minted or absent.
    /// - ensures: the return of the composite of the two flows in order, the
    ///   return carrying the written origin and the composite the inserted
    ///   identity origin. Nothing when an operand did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a composite of two statements read back out of the
    ///   arena in order.
    /// - witness: `lower::identity::tests::session_statements_lower_to_their_formers`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin)
                && matches!(sink.arena.computation(id), Some(&gandr_core_term::Computation::Return(composite))
                    if matches!(sink.arena.value(composite), Some(&Value::Then(..)))),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_flow_then(
        &self,
        first: NodeIndex,
        second: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let (first, second) = match (self.value_at(first), self.value_at(second)) {
            (Maybe::Present(first), Maybe::Present(second)) => (first, second),
            (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                return Maybe::Absent(reason);
            },
        };
        let mark = sink.arena.watermark();
        let composite = sink.arena.value_then(first, second);
        let root = sink.arena.computation_return(composite);
        record_since(
            sink,
            mark,
            origin.inserted(Insertion::Identity),
            Maybe::Present((root, origin)),
        );

        Maybe::Present(Lowered::Computation(root))
    }

    /// Mint `recorded(m₀, …, mₙ)`: the run over its moves in order.
    ///
    /// # Specification
    /// - requires: every payload is already minted or absent.
    /// - ensures: the recorded run whose moves are the planned moves in order,
    ///   each payload its minted value and each label kept, carrying the
    ///   written origin. Nothing when a payload did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Termination
    /// The loop runs once per planned move.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run of every move kind read back out of the arena.
    /// - witness: `lower::identity::tests::a_run_rides_a_flow_between_sessions`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Value(id)) => sink.origins.value(id) == Maybe::Present(origin)
                && matches!(sink.arena.value(id), Some(Value::Recorded(minted))
                    if minted.len() == moves.len()
                        && minted.iter().zip(moves.iter()).all(|(made, planned)| made.kind() == planned.kind())),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_recorded(
        &self,
        moves: &[RecordedMove<NodeIndex>],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut minted = Vec::with_capacity(moves.len());
        for planned in moves {
            match planned.try_map(|payload| match self.value_at(payload) {
                Maybe::Present(value) => Ok(value),
                Maybe::Absent(reason) => Err(reason),
            }) {
                Ok(made) => minted.push(made),
                Err(reason) => return Maybe::Absent(reason),
            }
        }
        let id = sink.arena.value_recorded(Arc::from(minted));

        Maybe::Present(sink.value(id, origin))
    }

    /// Mint the dependent transport `transported`.
    ///
    /// # Specification
    /// - requires: the operands are already minted or absent.
    /// - ensures: the transport over the motive's computation type, its two
    ///   entries made dependent by [`telescope`] and relocated to the
    ///   transport's frame, and the four values in order. The transport carries
    ///   the written origin and every other node minted for it the inserted
    ///   identity origin. Nothing when an operand did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a motive whose body ignores its element and one that
    ///   names both entries, each read back out of the arena.
    /// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(Lowered::Computation(id)) => sink.origins.computation(id) == Maybe::Present(origin)
                && matches!(sink.arena.computation(id), Some(&gandr_core_term::Computation::TelescopeTransport { .. })),
            | Maybe::Present(_) => false,
            | Maybe::Absent(_) => true,
        },
    )]
    pub(super) fn mint_telescope_transport(
        &self,
        transported: Transported,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let motive = match self.value_type_at(transported.motive) {
            Maybe::Present(motive) => motive,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let (path, start, over, value) = match (
            self.value_at(transported.path),
            self.value_at(transported.start),
            self.value_at(transported.over),
            self.value_at(transported.value),
        ) {
            (
                Maybe::Present(path),
                Maybe::Present(start),
                Maybe::Present(over),
                Maybe::Present(value),
            ) => (path, start, over, value),
            (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), ..)
            | (_, _, Maybe::Absent(reason), _)
            | (.., Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let mark = sink.arena.watermark();
        let written = match sink.arena.value_type(motive) {
            Some(&ValueType::Thunk(computation)) => computation,
            _ => sink.arena.comp_type_returner(motive),
        };
        let inserted = origin.inserted(Insertion::Identity);
        let mut copies = Vec::new();
        let dependent = telescope(sink.arena, written, &mut copies);
        let carried = self.relocate(
            sink.arena,
            dependent,
            transported.frame,
            Telescope::Signature,
            Binders::NONE,
            Some(&mut copies),
        );
        record_copies(sink, mark, &copies, inserted);
        let mark = sink.arena.watermark();
        let root = sink
            .arena
            .computation_telescope_transport(carried, path, start, over, value);
        record_since(sink, mark, inserted, Maybe::Present((root, origin)));

        Maybe::Present(Lowered::Computation(root))
    }
}

/// `written`, a motive's computation type, with both entries of a two-entry
/// telescope dependent, each node a shift rewrote reported into `copies`.
///
/// # Specification
/// - requires: `written` names a computation type of `arena`.
/// - ensures: for `A ⋆ (B ⋆ C)`, each `⋆` an arrow or a dependent arrow, the
///   two-entry telescope `Π (y : A). Π (z : B). C` with every arrow's codomain
///   shifted under the binder it now stands under; `written` itself when both
///   entries are already dependent or it is no two-entry telescope. `copies`
///   gains each shifted node beside its source.
/// - provides: the one reading of the telescope alias as a dependent
///   transport's motive.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a motive whose body ignores its element and one that
///   names both entries.
/// - witness: `lower::identity::tests::a_dependent_transport_lowers_to_its_telescope`
/// - witness: `lower::identity::tests::a_motive_telescope_rebuilds_exactly_when_an_entry_is_an_arrow`
#[spec(ensures: |ret| ret == written || matches!(arena.comp_type(ret), Some(&CompType::Pi { .. })))]
fn telescope(
    arena: &mut CoreArena,
    written: CompTypeId,
    copies: &mut Vec<Carried>,
) -> CompTypeId
{
    let (outer, rest, outer_arrow) = match arena.comp_type(written) {
        Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        _ => return written,
    };
    let rest = if outer_arrow {
        gandr_core_term::shift_comp_type_under(arena, rest, Binders::NONE, Binders::ONE)
            .settle_traced(arena, copies)
    }
    else {
        rest
    };
    let (inner, body, inner_arrow) = match arena.comp_type(rest) {
        Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        _ => return written,
    };
    if !outer_arrow && !inner_arrow {
        return written;
    }
    let body = if inner_arrow {
        gandr_core_term::shift_comp_type_under(arena, body, Binders::NONE, Binders::ONE)
            .settle_traced(arena, copies)
    }
    else {
        body
    };
    let entry = arena.comp_type_pi(inner, body);
    arena.comp_type_pi(outer, entry)
}
