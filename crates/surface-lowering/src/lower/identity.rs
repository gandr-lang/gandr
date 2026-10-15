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
//! # A derived operation reads its motive off the path type it answers
//!
//! `back(p)`, `p then q` and `cong(f, p)` are transports whose motive names
//! the carrier and the endpoint that stays fixed (`gandr_core_term::identity`).
//! The lowering reads both off the path type the position answers — the
//! function's result or the match's answer, written `-F Path(A, a, b)` or
//! `Path(A, a, b)` — relocated to where the operation stands. An operation
//! standing where no written path type is answered is refused as
//! unannotated. The alternative, synthesising the path's own type in the
//! lowering, duplicates the checker's work. Reversal: a checker that
//! elaborates a derived operation against its expected type makes the
//! written answer optional.
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

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::Carried;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_kernel_strata::Level;
use gandr_kernel_term::FieldLabel;
use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Former;
use super::Lowered;
use super::Lowerer;
use super::Plan;
use super::Produced;
use super::Reading;
use super::Sink;
use super::Site;
use super::Stretch;
use super::arguments;
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
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::resolve::Frame;
use crate::resolve::OperandCount;
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

/// A recorded run's close, a move written as a bare name.
const CLOSED: &str = "closed";

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
const SPELLED: [(&str, Operation); 16] = [
    (HERE, Operation::Here),
    ("funext", Operation::Funext),
    ("equiv", Operation::Equiv),
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

/// A derived operation as the classification planned it: its operands, the
/// path type its position answers, and the frame it stands under.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: the answer is a written path type, under a returner or not.
/// - executable: none — the plan holds no tree to check its answer against.
///
/// # Adequacy
/// - hypothesis: L3 — each operation's motive is read off its answer.
/// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Derived
{
    /// The operation and its operands.
    derivation: Derivation,
    /// The path type the position answers.
    answer: Answer,
    /// The frame the operation stands under.
    frame: Frame,
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
    /// Classify a path type, `Path(A, a, b)`.
    ///
    /// # Specification
    /// - requires: `site` is a path type in type position, or in value position
    ///   where a type is quoted.
    /// - ensures: the form stands as a value type, reads its carrier as a value
    ///   type and its two endpoints as endpoints standing inside a type, all
    ///   under its own frame, and is planned over the three.
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
    ///   computation, each read back out of the arena.
    /// - witness: `lower::identity::tests::a_path_type_and_reflexivity_lower_to_their_formers`
    /// - witness: `lower::identity::tests::a_computation_endpoint_is_the_value_it_returns`
    #[spec(
        ensures: |ret| {
            ret.is_err()
                || matches!(
                    self.plans.get(usize::from(site.at.node)),
                    Some(&Plan::Path(carrier, left, right))
                        if self.reading(carrier) == Reading::ValueType(site.reading.frame())
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
        let carrier = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::COMMA)?;
        let left = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::COMMA)?;
        let right = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        exhausted(site, &cursor)?;
        self.read(carrier.node, Reading::ValueType(frame));
        self.read(left.node, Reading::Value(frame));
        self.read(right.node, Reading::Value(frame));
        self.in_type.extend([left.node, right.node]);
        self.at_endpoint.extend([left.node, right.node]);
        self.plan(site, Plan::Path(carrier.node, left.node, right.node));

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
    ///   as values reading both operands as values; `transport(\X. T, p, v)`
    ///   and `ride(\X. T, f, v)` stand as computations reading their motive,
    ///   path or flow and value as values, and `transport(M, p, z₀, q, v)` as a
    ///   computation reading its motive as a value type and the other four as
    ///   values; `back(p)` and `cong(f, p)` stand as computations derived as
    ///   [`Self::derive`] does; `recorded(m₀, …, mₙ)` stands as a value over
    ///   its moves, each read as [`Self::recorded_move`] reads it. Every
    ///   operand is read under the site's frame.
    /// - fails: the wrong-sort refusal where the operation's sort is not read;
    ///   the arity refusal for other than one argument to `here`, `stay`,
    ///   `forward` or `back`, two to `funext`, `equiv`, `pathProduct`,
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
            | Operation::Here
            | Operation::Funext
            | Operation::Equiv
            | Operation::PathProduct
            | Operation::FlowProduct
            | Operation::Cons
            | Operation::Bisim
            | Operation::Sim
            | Operation::Stay
            | Operation::Forward
            | Operation::Arrow
            | Operation::Recorded => Produced::Value,
            | Operation::Back | Operation::Cong | Operation::Transport | Operation::Ride => {
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
            | Operation::Recorded => self.operands.get(start ..).map(<[NodeIndex]>::to_vec),
            | Operation::Here
            | Operation::Funext
            | Operation::Equiv
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
            | (Operation::Here | Operation::Stay, 1_usize, Some(point), ..) => {
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
                    | Operation::Stay => Plan::Stay(point),
                    | _ => Plan::Here(point),
                };
                self.plan(site, plan);
                Ok(())
            },
            | (
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
                    | Operation::Equiv => Plan::Equiv(left, right),
                    | Operation::PathProduct => Plan::PathProduct(left, right),
                    | Operation::FlowProduct => Plan::FlowProduct(left, right),
                    | Operation::Cons => Plan::ListCons(left, right),
                    | Operation::Bisim => {
                        Plan::SessionRelated(SessionRelation::Equivalence, left, right)
                    },
                    | Operation::Sim => {
                        Plan::SessionRelated(SessionRelation::Subtyping, left, right)
                    },
                    | Operation::Arrow => Plan::FunctionFlow(left, right),
                    | _ => Plan::Funext(left, right),
                };
                self.plan(site, plan);
                Ok(())
            },
            | (
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
                    | Operation::Ride => Plan::Ride(motive, path, value),
                    | _ => Plan::Transport(motive, path, value),
                };
                self.plan(site, plan);
                Ok(())
            },
            | (Operation::Recorded, ..) => {
                let written = moves.unwrap_or_default();
                let mut planned = Vec::with_capacity(written.len());
                for movement in written {
                    planned.push(self.recorded_move(site, frame, movement)?);
                }
                self.plan(site, Plan::Recorded(Arc::from(planned)));
                Ok(())
            },
            | (Operation::Transport, 5_usize, ..) => match written {
                | Some([motive, path, departure, over, value]) => {
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
                | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
            },
            | (Operation::Back, 1_usize, Some(path), ..) => {
                self.derive(site, frame, Derivation::Back { path })
            },
            | (Operation::Forward, 1_usize, Some(translator), ..) => {
                self.read(translator, Reading::Value(frame));
                self.plan(site, Plan::Forward(translator));
                Ok(())
            },
            | (Operation::Cong, 2_usize, Some(function), Some(path), _) => {
                self.derive(site, frame, Derivation::Cong { function, path })
            },
            | _ => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
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
            | Shape::Form {
                former: Former::StaticAbstraction,
                ..
            } => Ok(()),
            | _ => Err(unannotated),
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
            | Shape::Form { former, .. } => former,
            | Shape::Root | Shape::Repair(_) | Shape::Layout => return Err(unadmitted),
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
            | Some(&[argument]) => Some(argument),
            | Some(_) | None => None,
        };
        self.operands.truncate(start);
        let head = read?;
        let Some(argument) = argument
        else {
            return Err(at.out(FragmentBoundary::Arity(OperandCount::from(count))));
        };
        let spelled = self.name_at(head);
        match spelled.as_ref() {
            | "sent" | "received" => {
                self.read(argument, Reading::Value(frame));
                Ok(if spelled.as_ref() == "sent" {
                    RecordedMove::Sent(argument)
                }
                else {
                    RecordedMove::Received(argument)
                })
            },
            | "selected" | "offered" => {
                let label = self
                    .tree
                    .node(argument)
                    .and_then(|labelled| match shape_of(self.pbg, labelled) {
                        | Ok(Shape::Form {
                            former: Former::Name,
                            ..
                        }) => Some(Placed::of(argument, labelled)),
                        | Ok(_) | Err(_) => None,
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
            | _ => Err(unadmitted),
        }
    }

    /// Classify the derived operation `derivation`, standing as a computation
    /// at `site` under `frame`.
    ///
    /// # Specification
    /// - requires: `site` stands as a computation under `frame`.
    /// - ensures: every operand is read as a value under `frame`, and the
    ///   operation is planned against the path type its position answers; `f
    ///   then g` where the position answers a written flow type is planned as
    ///   the returned composite of the two flows, and `back(f)` there against
    ///   the flow type, as the symmetry ride the checker refuses.
    /// - fails: the unannotated refusal where the position answers no type, or
    ///   one that is not a written path type, or for `then` and `back` a
    ///   written flow type, under at most a returner and parentheses; the
    ///   allowance refusal from that walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The operation's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation under a path answer, and one under an
    ///   answer that is no path type.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
    /// - witness: `lower::identity::tests::a_derived_operation_needs_a_written_path_answer`
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
        let Some(&answer) = self.answers.get(&site.at.node)
        else {
            return Err(site.out(FragmentBoundary::Unannotated));
        };
        // A loop arm answers the path over its loop, whatever its case answers.
        let answered = match answer.over {
            | super::native::Over::Written => self.answers_path(site, answer.node)?,
            | super::native::Over::Loop { .. } => Answered::Path,
        };
        if answered == Answered::Flow {
            match derivation {
                | Derivation::Then { first, second } => {
                    self.read(first, Reading::Value(frame));
                    self.read(second, Reading::Value(frame));
                    self.plan(site, Plan::FlowThen(first, second));
                    return Ok(());
                },
                | Derivation::Cong { .. } => return Err(site.out(FragmentBoundary::Unannotated)),
                | Derivation::Back { .. } => {},
            }
        }
        match derivation {
            | Derivation::Back { path } => self.read(path, Reading::Value(frame)),
            | Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => {
                self.read(first, Reading::Value(frame));
                self.read(second, Reading::Value(frame));
            },
        }
        self.plan(
            site,
            Plan::Derived(Derived {
                derivation,
                answer,
                frame,
            }),
        );

        Ok(())
    }

    /// Read the identity type written at `answer`: a path type or a flow type,
    /// under at most a returner and any parentheses.
    ///
    /// # Specification
    /// - requires: `answer` is a node read where a result is read.
    /// - ensures: the path answer exactly when the walk from `answer` through
    ///   parenthesised types and one `-F` reaches a path type, and the flow
    ///   answer when it reaches a type application headed `Flow` at three
    ///   arguments.
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
    ///   answer, and an integer answer.
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
                | Former::PathType => return Ok(Answered::Path),
                | Former::ReturnerType if !returned => {
                    returned = true;
                    (true, false)
                },
                | Former::ParenthesizedType => (false, false),
                | Former::TypeApplication => (false, true),
                | _ => return Err(unannotated),
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let written = scratch
                .pieces
                .iter()
                .filter(|piece| matches!(**piece, Piece::Operand(_)))
                .count();
            let mut operands = scratch.pieces.iter().filter_map(|piece| match *piece {
                | Piece::Operand(operand) => Some(operand.node),
                | Piece::Tile { .. } => None,
            });
            let inner = match (operands.next(), operands.next()) {
                | (Some(inner), None) => Some(inner),
                | _ => None,
            };
            let keyword = scratch.pieces.iter().find_map(|piece| match *piece {
                | Piece::Tile { at, .. } => Some(at),
                | Piece::Operand(_) => None,
            });
            self.scratch = scratch;
            read?;
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
                | Some(inner) if returner => position = inner,
                | _ => return Err(unannotated),
            }
        }
    }

    /// Mint the derived operation `derived`: the transport it unfolds to.
    ///
    /// # Specification
    /// - requires: the operands and the answer are already minted or absent.
    /// - ensures: the answer, a returner over `Path(A, a, b)` or `Flow(A, a,
    ///   b)` relocated to the operation's frame, gives the carrier and the
    ///   endpoints: `back(p)` is `tr(y. Path(A, y, b), p, here(b))`, `p then q`
    ///   is `tr(y. Path(A, a, y), q, p)` and `cong(f, p)` is `tr(y. Path(A, a,
    ///   ⟨force f y⟩), p, here(a))`; `back(f)` under a flow answer is the
    ///   symmetry ride `ride(y. Flow(A, y, b), f, stay(b))`. The operation
    ///   carries the written origin and every other node minted for it the
    ///   inserted identity origin. Nothing when an operand or the answer did
    ///   not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each operation read back out of the arena and
    ///   checked.
    /// - witness: `lower::identity::tests::back_then_and_cong_unfold_to_transports`
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
        let written = match self.comp_type_at(derived.answer.node) {
            | Maybe::Present(written) => written,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let (first, second) = match derived.derivation {
            | Derivation::Back { path } => match self.value_at(path) {
                | Maybe::Present(path) => (path, path),
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            },
            | Derivation::Then { first, second }
            | Derivation::Cong {
                function: first,
                path: second,
            } => match (self.value_at(first), self.value_at(second)) {
                | (Maybe::Present(first), Maybe::Present(second)) => (first, second),
                | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
                    return Maybe::Absent(reason);
                },
            },
        };
        let mark = sink.arena.watermark();
        let gap = self
            .scope
            .telescope_binders(derived.frame)
            .count()
            .saturating_sub(self.scope.telescope_binders(derived.answer.frame).count());
        let lift = Binders::from(u32::try_from(gap).unwrap_or(u32::MAX));
        let answered = self.relocate(sink.arena, written, derived.answer.frame, lift, None);
        let identity = match sink.arena.comp_type(answered) {
            | Some(&CompType::Returner { result, .. }) => {
                match (derived.answer.over, sink.arena.value_type(result)) {
                    // A loop arm's operation stands at `Path(B, y, y)`, `y` the
                    // answer at the loop's point its arm binds innermost.
                    | (super::native::Over::Loop { arm }, Some(_)) => {
                        let gap = self
                            .scope
                            .telescope_binders(derived.frame)
                            .count()
                            .saturating_sub(self.scope.telescope_binders(arm).count());
                        let index = u32::try_from(gap).unwrap_or(u32::MAX);
                        let point = sink.arena.value_variable(
                            gandr_core_term::Zone::Intuitionistic,
                            gandr_kernel_term::DeBruijnIndex::from(index),
                        );
                        Some((Answered::Path, result, point, point))
                    },
                    | (
                        super::native::Over::Written,
                        Some(&ValueType::Path {
                            carrier,
                            left,
                            right,
                        }),
                    ) => Some((Answered::Path, carrier, left, right)),
                    | (
                        super::native::Over::Written,
                        Some(&ValueType::Flow {
                            carrier,
                            source,
                            target,
                        }),
                    ) => Some((Answered::Flow, carrier, source, target)),
                    | (..) => None,
                }
            },
            | _ => None,
        };
        let inserted = origin.inserted(Insertion::Identity);
        let Some((answered_as, carrier, left, right)) = identity
        else {
            record_since(
                sink,
                mark,
                inserted,
                Maybe::Absent(rooted::Absent::Unminted),
            );
            return Maybe::Absent(lowered::Absent::OtherSort);
        };
        let root = match (answered_as, derived.derivation) {
            | (Answered::Path, Derivation::Back { .. }) => {
                gandr_core_term::identity::back(sink.arena, carrier, right, first)
            },
            | (Answered::Flow, Derivation::Back { .. }) => {
                gandr_core_term::identity::back_flow(sink.arena, carrier, right, first)
            },
            | (Answered::Path, Derivation::Then { .. }) => {
                gandr_core_term::identity::then(sink.arena, carrier, left, first, second)
            },
            | (Answered::Path, Derivation::Cong { .. }) => {
                gandr_core_term::identity::cong(sink.arena, carrier, first, left, second)
            },
            | (Answered::Flow, Derivation::Then { .. } | Derivation::Cong { .. }) => {
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

        Maybe::Present(Lowered::Computation(root))
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
            | (Maybe::Present(motive), Maybe::Present(path), Maybe::Present(value)) => {
                (motive, path, value)
            },
            | (Maybe::Absent(reason), ..)
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
            | (Maybe::Present(motive), Maybe::Present(flow), Maybe::Present(value)) => {
                (motive, flow, value)
            },
            | (Maybe::Absent(reason), ..)
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
            | (Maybe::Present(first), Maybe::Present(second)) => (first, second),
            | (Maybe::Absent(reason), _) | (_, Maybe::Absent(reason)) => {
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
                | Maybe::Present(value) => Ok(value),
                | Maybe::Absent(reason) => Err(reason),
            }) {
                | Ok(made) => minted.push(made),
                | Err(reason) => return Maybe::Absent(reason),
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
            | Maybe::Present(motive) => motive,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let (path, start, over, value) = match (
            self.value_at(transported.path),
            self.value_at(transported.start),
            self.value_at(transported.over),
            self.value_at(transported.value),
        ) {
            | (
                Maybe::Present(path),
                Maybe::Present(start),
                Maybe::Present(over),
                Maybe::Present(value),
            ) => (path, start, over, value),
            | (Maybe::Absent(reason), ..)
            | (_, Maybe::Absent(reason), ..)
            | (_, _, Maybe::Absent(reason), _)
            | (.., Maybe::Absent(reason)) => return Maybe::Absent(reason),
        };
        let mark = sink.arena.watermark();
        let written = match sink.arena.value_type(motive) {
            | Some(&ValueType::Thunk(computation)) => computation,
            | _ => sink.arena.comp_type_returner(motive),
        };
        let inserted = origin.inserted(Insertion::Identity);
        let mut copies = Vec::new();
        let dependent = telescope(sink.arena, written, &mut copies);
        let carried = self.relocate(
            sink.arena,
            dependent,
            transported.frame,
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
#[spec(ensures: |ret| ret == written || matches!(arena.comp_type(ret), Some(&CompType::Pi { .. })))]
fn telescope(
    arena: &mut CoreArena,
    written: CompTypeId,
    copies: &mut Vec<Carried>,
) -> CompTypeId
{
    let (outer, rest, outer_arrow) = match arena.comp_type(written) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        | Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        | _ => return written,
    };
    let rest = if outer_arrow {
        gandr_core_term::shift_comp_type_under_traced(
            arena,
            rest,
            Binders::NONE,
            Binders::ONE,
            copies,
        )
    }
    else {
        rest
    };
    let (inner, body, inner_arrow) = match arena.comp_type(rest) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain, false),
        | Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, true),
        | _ => return written,
    };
    if !outer_arrow && !inner_arrow {
        return written;
    }
    let body = if inner_arrow {
        gandr_core_term::shift_comp_type_under_traced(
            arena,
            body,
            Binders::NONE,
            Binders::ONE,
            copies,
        )
    }
    else {
        body
    };
    let entry = arena.comp_type_pi(inner, body);
    arena.comp_type_pi(outer, entry)
}
