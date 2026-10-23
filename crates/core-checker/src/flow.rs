//! Directed identity: `Flow(A, a, b)`, the session statements that inhabit it
//! and its path counterpart, `stay` and `then`, the ride and the table it
//! computes by, and the recorded runs that ride it.
//!
//! # The statements
//!
//! `bisim(A, B)` synthesises `Path(Type, A, B)` and `sim(A, B)` synthesises
//! `Flow(Type, A, B)` when both operands are closed codes of session types at
//! their protocols' roots. `gandr-core-session`'s engine decides each:
//! bisimilarity for the path, Gay and Hole's subtyping for the flow — the
//! source has no more selections and no fewer offers than the target — and
//! the judgement's own conversion compares the payload types of every send
//! and receive pair the engine visited, invariantly. Two sessions the engine
//! does not relate are [`CheckRefusal::SessionNotEquivalent`] and
//! [`CheckRefusal::SessionNotSubtype`], by the engine's own relation; an
//! operand that is no session code is [`CheckRefusal::SessionCodeExpected`].
//!
//! The judgement records, for each statement it accepts, the engine's pairs:
//! the kernel's session evidence over the protocols erased node for node. The
//! bridge erases a bisimilarity to the kernel's `SessionPath` at `Path_U` and
//! a simulation to its `SessionFlow` at `Flow_U`; admission replays the pairs
//! against the erased graphs and trusts nothing the engine decided.
//!
//! `stay(a)` synthesises `Flow(A, a, a)` from the type `a` synthesises, and
//! checked against `Flow(A, x, y)` meets `a` with both endpoints; `f then g`
//! synthesises `Flow(A, a, c)` from `f : Flow(A, a, b)` and `g` checked
//! against `Flow(A, b, c)`. When the carrier is the value universe and the
//! endpoints are session codes, the engine decides the composite's own
//! simulation and the judgement records it as it records `sim`, so the kernel
//! replays a stay or a composite as one simulation. Over any other carrier or
//! codes the bridge erases a stay to the kernel's own stay and a composite to
//! its sequence, which admission checks by conversion.
//!
//! # Payload paths
//!
//! `bisim(A, B, p)` owes a path for each pair of payload slots whose types
//! do not convert, once, in the engine's pair order: `p` checks against
//! `Path(Type, P, Q)` for one, the tuple of the paths for several. Each is
//! read as its native certificate, as [`crate::product`] reads a component
//! ([`CheckRefusal::ShapeMismatch`] for a path naming none), and the bridge
//! passes them as the `SessionPath`'s payload paths, which admission checks
//! against the owed slot pairs the evidence lists. Unpaid, the statement is
//! [`CheckRefusal::SessionNotEquivalent`].
//!
//! # The run type
//!
//! `Run(S)` classifies the complete recorded runs of the session code `S`: a
//! finite trace `recorded(m₀, …, mₙ)` of the endpoint's moves — `sent(v)`,
//! `received(v)`, `selected(l)`, `offered(l)` and `closed` — that the
//! protocol's monitor accepts from the root to its close. A literal checks
//! against `Run(S)` by the engine's replay of its skeleton, every payload
//! then checked against the payload type the protocol names at its move; a
//! move the monitor refuses is [`CheckRefusal::RunNotAdmitted`] with the
//! move's position and the monitor's reason. A run is data: it evaluates to
//! itself and prints as the literal it is.
//!
//! `Prefix(S)` classifies the recorded prefixes of `S`: the same literal,
//! checked by the same replay, admitted when the monitor accepts every move
//! it holds, whether it reaches `closed` or stops with a move still owed. A
//! prefix the monitor refuses at a move is refused at that move as a run is;
//! only the incomplete end is admitted. A run type stays complete-only:
//! riding and transporting move complete runs, and an open play neither
//! rides nor transports.
//!
//! # Riding a flow
//!
//! `ride(\X. T, f, v)` moves `v : T[a]` along `f : Flow(A, a, b)` and
//! synthesises `F T[b]`. The motive is closed but for `X` and reads `X` only
//! covariantly: a flow's source and an arrow's or a dependent arrow's domain
//! reverse the variance, and every other position a code stands at — a path,
//! a data argument, a session payload — is invariant. A motive that reads `X`
//! elsewhere is [`CheckRefusal::NonCovariantMotive`], which is how symmetry
//! is refused: `ride(\X. Flow(Type, X, a), f, stay(a))` would turn `f` into
//! its reverse.
//!
//! A motive that does not read `X`, and a flow whose two endpoints convert,
//! ride as the identity, as does any ride along a flow whose carrier is no
//! universe: such a flow is a stay or a composite of stays, and a stay
//! returns what it rides. Between two distinct session codes the motive must
//! be `Run(X)` or `Prefix(X)` ([`CheckRefusal::RideUnsupported`] otherwise):
//! the record moves by `gandr-core-session`'s recorded-run consumer along the
//! engine's simulation, never by the kernel's lowering of a flow, which
//! refuses a session flow as `RecordedRunRequired`. A literal record is
//! advanced move by move at check time — a run complete, a prefix complete or
//! still open — and one the target does not admit — one that takes an offer
//! the target has dropped — is [`CheckRefusal::RunNotAdmitted`] at the move.
//! An open value is admitted when the simulation narrows no offer, so every
//! record of the source is a record of the target. An admitted ride returns
//! the record unchanged: its skeleton is the target's, labels and payloads
//! kept.
//!
//! Between codes that are not both sessions — the forward and function flows
//! of [`crate::forward`] and their products in [`crate::product`] — the
//! motive must be one the directed computation table moves:
//!
//! | motive position reading `X` | the ride |
//! |---|---|
//! | `X` decoded, `El X` | a forward flow applies its translator; a function flow wraps the function in its two boundaries; a flow product rides a pair's components along its two flows |
//! | a product, a sum or a list of such positions | constructorwise, `nil` unchanged |
//! | `Flow(Type, l, X)`, the singleton | `stay(l)` becomes the flow; any other flow composes with it |
//!
//! Any other position reading `X` — a record of it, a thunk of an arrow into
//! it — is [`CheckRefusal::RideUnsupported`]. The kernel's ride reduction,
//! the normaliser and the runtime compute the same rows, so a ride the
//! judgement admits computes in all three.
//!
//! # Decisions
//!
//! - **Spelling.** `bisim(A, B)` and `sim(A, B)` name the engine's two
//!   relations, beside `equiv(f, g)` and `ua[n, k](…)` in the lowering's
//!   identity region; `Flow(A, a, b)`, `stay`, `then` and `ride` follow the
//!   directed-identity record, `then` the grammar's infix tile read at a
//!   written flow answer. The alternatives were `equiv`-style statements over
//!   translators, which a session code has none of, and an infix `A <: B`,
//!   which reads as a judgement rather than a term inhabiting a type. Reversal:
//!   a surface that writes subtyping as a judgement would elaborate it to
//!   `sim`.
//! - **The engine decides, the kernel replays.** The engine's coinductive pairs
//!   are the certificate; the kernel checks every local obligation and
//!   membership and searches nothing. The alternative was a checker-side
//!   bisimulation proof the kernel would trust. Reversal: none while the kernel
//!   replays supplied pairs.
//! - **A run is a value of its own type.** `Run(S)` is a value type with a
//!   literal, not an endpoint: the endpoint is linear and moves, a run is the
//!   finished record of one and can be stored, compared and printed. The
//!   alternative was reading a run off a live endpoint, which no former binds
//!   outside the linear zone. Reversal: receipts recorded by a running fork.
//! - **Runs ride, the kernel does not run them.** The kernel holds no run type,
//!   so a declaration that names a run, a literal or a ride stays on the
//!   checker's side. The alternative, a kernel run former, would duplicate the
//!   consumer the kernel already defers to. Reversal: a kernel run type with
//!   its own monitor.
//! - **Closed motives.** A motive reads no binder but its own, which keeps the
//!   covariance check a reach count. Reversal: an occurrence walk that tracks
//!   each binder's polarity.
//! - **Walking the wrong family is a shape mismatch.** `transport` along a flow
//!   wants a path and `ride` along a path wants a flow; each is
//!   [`CheckRefusal::ShapeMismatch`] naming the shape the eliminator expects.
//!   The alternative, a refusal of its own for crossing families, would name
//!   the same fact twice. Reversal: a derived coercion from paths to flows,
//!   which would let a path ride.
//!
//! # What a consumer may assume
//!
//! A protocol's receipts are runs: `Run(S)` is a complete trace the monitor
//! of `S` accepts. Compatibility of an old protocol with a new one is a
//! `Flow(Type, Old, New)` the engine decides and the kernel replays; riding
//! it moves every old receipt the new protocol admits and refuses, by move,
//! every one it does not. Equivalence is a `Path(Type, A, B)`, replayed the
//! same way; without payload paths it identifies the two codes, so every run
//! of one is a run of the other by conversion alone.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::CoreTerm;
use gandr_core_nbe::FreeFault;
use gandr_core_nbe::FreeIndices;
use gandr_core_nbe::MachineVerdict;
use gandr_core_session::DialogueRefusal;
use gandr_core_session::Event;
use gandr_core_session::Label;
use gandr_core_session::Move;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Relation;
use gandr_core_session::ReplayError;
use gandr_core_session::Turn;
use gandr_core_session::certified::TransportError;
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
use gandr_core_term::Zone;
use gandr_core_term::instantiate_value_type;
use gandr_core_term::relevel_value_type;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::ProtocolNode;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_core_term::session::Step as ProtocolStep;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::session::Evidence;
use quenchant_shape::shape::Maybe;

use crate::code::loose_reach;
use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::conversion::equivalent;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::RunFault;
use crate::refusal::RunStep;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::session::PayloadPair;
use crate::session::engine;
use crate::session::related;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

#[cfg(test)]
mod tests;

quenchant_shape::reason_enum! {
    /// Why a code names no session.
    pub mod session_code {
        /// The reason a code is no session code.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The code reduces to no quote of a session type at its
            /// protocol's root.
            Elsewhere,
        }
    }
}

/// A session statement the judgement decided: the relation, the two quotes,
/// the classifier the bridge erases it at, the engine's evidence and the
/// payload pairs its paths are owed for.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Statement
{
    /// Bisimilarity or simulation.
    relation: SessionRelation,
    /// The native classifier: `Path_U(⌜A⌝, ⌜B⌝)` for a bisimilarity, the
    /// universe's `Flow(Type, ⌜A⌝, ⌜B⌝)` for a simulation.
    classifier: ValueTypeId,
    /// The engine's pairs over the two protocols' node positions, with the
    /// slot pairs the payload paths cover.
    evidence: Arc<Evidence>,
    /// The two payload types of each slot pair `evidence` lists, in its
    /// order: what the payload paths relate.
    owed: Arc<[(ValueTypeId, ValueTypeId)]>,
}

impl Statement
{
    /// Bisimilarity or simulation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relation(&self) -> SessionRelation
    {
        self.relation
    }

    /// The classifier the bridge erases the statement at, over the two
    /// quotes the operands reduce to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn classifier(&self) -> ValueTypeId
    {
        self.classifier
    }

    /// The engine's pairs: the kernel's session evidence over the protocols
    /// erased node for node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn evidence(&self) -> &Arc<Evidence>
    {
        &self.evidence
    }

    /// The payload type pairs the statement's paths relate, one per slot
    /// pair the evidence lists, in its order; empty when every pair
    /// converts.
    ///
    /// # Specification
    /// - ensures: the pairs [`decide`] collected, the evidence's payload slot
    ///   pairs read at the two protocols' payload types.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bisimilarity whose protocols receive `Unit * Unit`
    ///   and `Unit` owes exactly that pair.
    /// - witness: `flow::tests::a_bisimulation_owes_a_path_per_differing_payload_pair`
    #[spec(ensures: |ret| ret.len() == self.owed.len())]
    #[inline]
    #[must_use]
    pub fn owed(&self) -> &[(ValueTypeId, ValueTypeId)]
    {
        &self.owed
    }
}

/// Whether a ride moves a recorded run or prefix between distinct sessions,
/// or rides as the identity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Moving
{
    /// The motive ignores its code, or the flow's endpoints convert.
    Fixed,
    /// A run moves between two distinct session codes.
    Run,
    /// A prefix, complete or still open, moves between two distinct session
    /// codes.
    Prefix,
}

/// What a ride's classification hands the judgement: the fibre the value
/// checks at, the returner the ride synthesises, and whether a run moves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Ride
{
    /// The ridden value.
    pub value: ValueId,
    /// The motive at the flow's source.
    pub source: ValueTypeId,
    /// `F` of the motive at the flow's target.
    pub result: CompTypeId,
    /// Whether the recorded-run consumer must admit the value.
    pub moving: Moving,
}

/// A variance a motive's position reads its code at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Polarity
{
    /// Along the flow.
    Positive,
    /// Against it: a flow's source, an arrow's domain.
    Negative,
    /// Neither: a position whose occurrence no flow moves.
    Invariant,
}

impl Polarity
{
    /// The variance beneath a position that reverses it.
    ///
    /// # Specification
    /// trivial.
    const fn flipped(self) -> Self
    {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
            Self::Invariant => Self::Invariant,
        }
    }
}

/// A node of a motive awaiting the covariance walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Position
{
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
    /// A value standing at a type.
    Value(ValueId),
}

/// The value universe at level zero, which classifies session codes.
///
/// # Specification
/// trivial.
#[inline]
pub fn universe(arena: &mut CoreArena) -> ValueTypeId
{
    arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero())
}

/// The session type the code `code` names, read at its weak head.
///
/// # Specification
/// - requires: `code` is formed under the judgement's binders.
/// - ensures: the session type of the quote `code` reduces to, when that quote
///   is of a session type standing at its protocol's root; absent for any other
///   code, an open one included.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a named session code, a quoted integer and a session past
///   its root separate the readings.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
/// - witness: `flow::tests::each_refusal_is_named`
/// - witness: `flow::tests::a_session_is_a_code_only_at_its_root`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref session)) => session.state() == session.protocol().root(),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
pub fn session_code(
    context: &mut CheckingContext<'_>,
    code: ValueId,
) -> Result<Maybe<SessionType, session_code::Absent>, CheckRefusal>
{
    let elsewhere = Ok(Maybe::Absent(session_code::Absent::Elsewhere));
    let head = context.whnf_code(code)?;
    let Some(&Value::Quote(quoted)) = context.arena().value(head)
    else {
        return elsewhere;
    };
    let quoted = context.whnf_value_type(quoted)?;
    match value_type_view(context.arena(), quoted)? {
        ValueTypeView::Session(session) if session.state() == session.protocol().root() => {
            Ok(Maybe::Present(session.clone()))
        },
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => elsewhere,
    }
}

/// The quote of the session type `code` reduces to, for a classifier.
///
/// # Specification
/// - requires: [`session_code()`] found a session at `code`.
/// - ensures: a quote of a session type at its root.
/// - fails: [`CheckRefusal::MachineInvariant`] when `code` reduces to no quote.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a named code crosses as the quote it unfolds to, which
///   the kernel decodes as a session graph.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&quote| matches!(context.arena().value(quote), Some(&Value::Quote(_)))) == ret.is_ok())]
fn quoted(
    context: &mut CheckingContext<'_>,
    code: ValueId,
) -> Result<ValueId, CheckRefusal>
{
    let head = context.whnf_code(code)?;
    match context.arena().value(head) {
        Some(&Value::Quote(quoted)) => {
            let quoted = context.whnf_value_type(quoted)?;
            Ok(context.arena_mut().value_quote(quoted))
        },
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// The two session types of `(source, target)`, or the operand that names
/// none.
///
/// # Specification
/// - requires: both are formed under the judgement's binders.
/// - ensures: both sessions, source first.
/// - fails: [`CheckRefusal::SessionCodeExpected`] at the first operand that is
///   no session code; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`session_code()`].
/// - witness: `flow::tests::each_refusal_is_named`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::SessionCodeExpected { at }) => at == source || at == target,
    | Ok(_) | Err(_) => true,
})]
fn sessions(
    context: &mut CheckingContext<'_>,
    (source, target): (ValueId, ValueId),
) -> Result<(SessionType, SessionType), CheckRefusal>
{
    let mut read = |code| match session_code(context, code)? {
        Maybe::Present(session) => Ok(session),
        Maybe::Absent(_) => Err(CheckRefusal::SessionCodeExpected { at: code }),
    };
    let left = read(source)?;
    let right = read(target)?;
    Ok((left, right))
}

/// Two related sessions: the engine's evidence, and the payload pairs whose
/// types do not convert, each pair of slots once, in the order of the
/// engine's pairs.
struct Owing
{
    /// The engine's pairs.
    evidence: Evidence,
    /// The pairs conversion does not close.
    owed: Vec<PayloadPair>,
}

/// Relate two sessions by `relation`, payload pairs compared by conversion.
///
/// # Specification
/// - requires: both are session types of the context's arena.
/// - ensures: the engine's evidence exactly when the engine relates the two
///   protocols, with every payload pair it visited whose types do not convert,
///   each pair of slots once; absent otherwise.
/// - fails: as the engine and conversion raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a widened selection relates by subtyping, not by
///   equivalence; a reversed pair does not relate; a pair of differing payloads
///   is owed once however often the engine meets it.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
/// - witness: `flow::tests::a_bisimulation_owes_a_path_per_differing_payload_pair`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref related)) => !related.evidence.pairs.is_empty(),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
fn relation_evidence(
    context: &mut CheckingContext<'_>,
    (left, right): (&SessionType, &SessionType),
    relation: Relation,
) -> Result<Maybe<Owing, crate::session::related::Absent>, CheckRefusal>
{
    let Maybe::Present(decided) = related(left, right, relation)?
    else {
        return Ok(Maybe::Absent(crate::session::related::Absent::Unrelated));
    };
    let mut met = BTreeSet::new();
    let mut owed = Vec::new();
    for pair in decided.payloads {
        if !met.insert(pair.slots) {
            continue;
        }
        let (first, second) = pair.types;
        if equivalent(context, first, second)? != Agreement::Convertible {
            owed.push(pair);
        }
    }
    Ok(Maybe::Present(Owing {
        evidence: decided.evidence,
        owed,
    }))
}

/// Relate two sessions by `relation` with every payload pair converting: the
/// relation a simulation, a stay or a composite stands for.
///
/// # Specification
/// - requires: both are session types of the context's arena.
/// - ensures: the engine's evidence exactly when the engine relates the two
///   protocols and every payload pair it visited converts; absent otherwise.
/// - fails: as [`relation_evidence`].
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`relation_evidence`].
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref evidence)) => !evidence.pairs.is_empty(),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
fn converting_evidence(
    context: &mut CheckingContext<'_>,
    sessions: (&SessionType, &SessionType),
    relation: Relation,
) -> Result<Maybe<Evidence, crate::session::related::Absent>, CheckRefusal>
{
    Ok(match relation_evidence(context, sessions, relation)? {
        Maybe::Present(related) if related.owed.is_empty() => Maybe::Present(related.evidence),
        Maybe::Present(_) | Maybe::Absent(_) => {
            Maybe::Absent(crate::session::related::Absent::Unrelated)
        },
    })
}

/// Decide the session statement `at` relating `(source, target)` by
/// `relation`.
///
/// # Specification
/// - requires: both operands checked against the value universe.
/// - ensures: the engine's evidence and the native classifier over the quotes
///   the operands reduce to, exactly when both are session codes the engine
///   relates; a bisimilarity owes a path for each payload pair whose types do
///   not convert, its slots listed in the evidence and its types in
///   [`Statement::owed`], and a simulation owes none.
/// - provides: the decision `bisim`, `sim`, `stay` and `then` record.
/// - fails: [`CheckRefusal::SessionCodeExpected`] at an operand that is no
///   session code; [`CheckRefusal::SessionNotEquivalent`] or
///   [`CheckRefusal::SessionNotSubtype`] at `at` for sessions the engine does
///   not relate, or for a simulation whose payloads do not convert; the
///   unfolding's and the engine's refusals.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a protocol and its renamed unfolding are bisimilar, a
///   widened selection is a supertype and not an equivalent, the reverse
///   simulation is refused, and a protocol over a type and over another is
///   bisimilar owing a path between the two.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
/// - witness: `flow::tests::each_refusal_is_named`
/// - witness: `flow::tests::a_bisimulation_owes_a_path_per_differing_payload_pair`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::SessionNotEquivalent { at: site } | CheckRefusal::SessionNotSubtype { at: site }) => site == at,
    | Ok(ref statement) => statement.relation == relation
        && statement.owed.len() == statement.evidence.payloads.len()
        && (relation == SessionRelation::Equivalence || statement.owed.is_empty()),
    | Err(_) => true,
})]
pub fn decide(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    relation: SessionRelation,
    (source, target): (ValueId, ValueId),
) -> Result<Statement, CheckRefusal>
{
    let (left, right) = sessions(context, (source, target))?;
    let (engine_relation, unrelated) = match relation {
        SessionRelation::Equivalence => {
            (Relation::Equivalent, CheckRefusal::SessionNotEquivalent {
                at,
            })
        },
        SessionRelation::Subtyping => (Relation::Subtype, CheckRefusal::SessionNotSubtype { at }),
    };
    let Maybe::Present(Owing { mut evidence, owed }) =
        relation_evidence(context, (&left, &right), engine_relation)?
    else {
        return Err(unrelated);
    };
    if relation == SessionRelation::Subtyping && !owed.is_empty() {
        return Err(unrelated);
    }
    evidence.payloads = owed.iter().map(|pair| pair.slots).collect();
    let owed = owed.iter().map(|pair| pair.types).collect();
    let source = quoted(context, source)?;
    let target = quoted(context, target)?;
    let arena = context.arena_mut();
    let classifier = match relation {
        SessionRelation::Equivalence => arena.value_type_path_universe(source, target),
        SessionRelation::Subtyping => {
            let universe = universe(arena);
            arena.value_type_flow(universe, source, target)
        },
    };
    Ok(Statement {
        relation,
        classifier,
        evidence: Arc::new(evidence),
        owed,
    })
}

/// The identity a session statement inhabits over its operands as written:
/// `Path(Type, A, B)` for a bisimilarity, `Flow(Type, A, B)` for a
/// simulation.
///
/// # Specification
/// trivial.
#[inline]
pub fn identity(
    arena: &mut CoreArena,
    relation: SessionRelation,
    (source, target): (ValueId, ValueId),
) -> ValueTypeId
{
    let universe = universe(arena);
    match relation {
        SessionRelation::Equivalence => arena.value_type_path(universe, source, target),
        SessionRelation::Subtyping => arena.value_type_flow(universe, source, target),
    }
}

/// The paths a bisimilarity owes: `Path(Type, ⌜P⌝, ⌜Q⌝)` for each owed pair of
/// payload types, in the statement's order.
///
/// # Specification
/// - requires: every type in `owed` lives in `arena`.
/// - ensures: one universe path per pair of `owed`, from the pair's first
///   type's code to its second's, in the pairs' order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one owed pair yields its path, two yield both paths in
///   order, and none yields no path.
/// - witness: `flow::tests::payload_paths_check_as_unit_one_path_or_a_tuple_in_order`
#[spec(ensures: |ret| ret.len() == owed.len())]
fn owed_paths(
    arena: &mut CoreArena,
    owed: &[(ValueTypeId, ValueTypeId)],
) -> Vec<ValueTypeId>
{
    let universe = universe(arena);
    owed.iter()
        .map(|&(left, right)| {
            let (left, right) = (arena.value_quote(left), arena.value_quote(right));
            arena.value_type_path(universe, left, right)
        })
        .collect()
}

/// The type a bisimilarity's payload paths check against: the unit type when
/// it owes none, the one path it owes alone, and the tuple of the paths in the
/// statement's order for several.
///
/// # Specification
/// - requires: every type in `owed` lives in `arena`.
/// - ensures: the empty product for no pair; the pair's universe path, as
///   [`owed_paths`] forms it, for one; the product of those paths in the pairs'
///   order for several.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one owed pair checks against its path, two against the
///   tuple of both paths in order, and none against the unit type.
/// - witness: `flow::tests::payload_paths_check_as_unit_one_path_or_a_tuple_in_order`
#[spec(ensures: |ret| arena.value_type(ret).is_some())]
#[inline]
pub fn payload_paths(
    arena: &mut CoreArena,
    owed: &[(ValueTypeId, ValueTypeId)],
) -> ValueTypeId
{
    match *owed_paths(arena, owed).as_slice() {
        [one] => one,
        ref several => arena.value_type_product(several),
    }
}

/// Elaborate the payload paths of the bisimilarity at `at` to the native
/// certificates the kernel checks, and record their tuple at the paths' node.
///
/// # Specification
/// - requires: the statement at `at` was decided and recorded, and its payload
///   paths checked against [`payload_paths`] of what it owes.
/// - ensures: when the statement owes a path, the paths' node records a tuple
///   of one native certificate per owed pair, in order, as
///   [`payload_certificate`] reads each path; nothing is recorded when it owes
///   none.
/// - fails: [`CheckRefusal::ShapeMismatch`] at a path that names no closed
///   certificate, wanting a universe path, as [`crate::product`] reads one; at
///   several paths that read as no tuple through constants' definitions,
///   wanting a product.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above; [`CheckRefusal::MachineInvariant`] for a node
///   that is no recorded bisimilarity.
///
/// # Termination
/// - reason: one `while` that only continues through a constant's definition.
/// - measure: the admission position of the constant read; a definition only
///   names constants admitted before its own.
///
/// # Adequacy
/// - hypothesis: L3 — one owed pair elaborates its path, a module-level
///   equivalence read through its constant, to the native certificate the
///   kernel replays, and a path a parameter binds is refused.
/// - witness: `flow::tests::a_bisimulation_owes_a_path_per_differing_payload_pair`
#[spec(ensures: |ret| ret.is_err() || match (context.arena().value(at), context.flows().get(&at)) {
    | (Some(&Value::SessionRelated { payloads, .. }), Some(statement)) => statement.owed.is_empty()
        || matches!(
            context.natives().get(&payloads).and_then(|&native| context.arena().value(native)),
            Some(Value::Tuple(natives)) if natives.len() == statement.owed.len()
        ),
    | _ => false,
})]
pub fn elaborate(
    context: &mut CheckingContext<'_>,
    at: ValueId,
) -> Result<(), CheckRefusal>
{
    let (Some(&Value::SessionRelated { payloads, .. }), Some(statement)) =
        (context.arena().value(at), context.flows().get(&at))
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let owed = Arc::clone(&statement.owed);
    let paths = owed_paths(context.arena_mut(), &owed);
    let natives = match *paths.as_slice() {
        [] => return Ok(()),
        [one] => alloc::vec![payload_certificate(context, payloads, one)?],
        ref several => {
            let mut read = payloads;
            while let Some(&Value::Constant(constant)) = context.arena().value(read)
                && let Maybe::Present(body) = context.definitions().body(constant)
            {
                read = body;
            }
            let Some(&Value::Tuple(ref components)) = context.arena().value(read)
            else {
                let found = context.arena_mut().value_type_product(several);
                return Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(payloads),
                    wanted: ExpectedShape::Product,
                    found: TypeNode::Value(found),
                });
            };
            let components = components.to_vec();
            components
                .into_iter()
                .zip(several)
                .map(|(component, &path)| payload_certificate(context, component, path))
                .collect::<Result<Vec<_>, _>>()?
        },
    };
    let tuple = context.arena_mut().value_tuple(&natives);
    context.record_native(payloads, tuple);
    Ok(())
}

/// The native certificate one payload path stands for: a closed univalence,
/// read through constants' definitions, stands for itself, the kernel checking
/// its record at the native identity the pair owes; any other path as
/// [`crate::product::certificate`] reads it.
///
/// # Specification
/// - requires: `at` was judged at `classifier`, an owed pair's universe path.
/// - ensures: the univalence `at` reads to through constants' definitions when
///   it reads no variable, for the kernel checks payload paths in the empty
///   context; otherwise [`crate::product::certificate`] of `at`, which refuses
///   a univalence.
/// - fails: as [`crate::product::certificate`]; [`CheckRefusal::DanglingNode`]
///   at a univalence whose free-variable walk reaches no node.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: one `while` that only continues through a constant's definition.
/// - measure: the admission position of the constant read; a definition only
///   names constants admitted before its own.
///
/// # Adequacy
/// - hypothesis: L3 — a univalence through its constant pays a pair whose
///   payloads are differing types, one over a record a parameter binds is
///   refused, and a parameter-bound path is refused as before.
/// - witness: `flow::tests::a_univalence_pays_a_payload_pair_when_closed`
#[spec(ensures: |ret| match ret {
    | Ok(native) => matches!(context.arena().value(native), Some(Value::Univalence(..) | Value::PathRefl(_) | Value::PathEquiv { .. } | Value::PathProduct(..))),
    | Err(_) => true,
})]
fn payload_certificate(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    classifier: ValueTypeId,
) -> Result<ValueId, CheckRefusal>
{
    let mut read = at;
    while let Some(&Value::Constant(constant)) = context.arena().value(read)
        && let Maybe::Present(body) = context.definitions().body(constant)
    {
        read = body;
    }
    if matches!(context.arena().value(read), Some(&Value::Univalence(..))) {
        let refused = |fault| match fault {
            FreeFault::Dangling => CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(read)),
            },
            FreeFault::MachineInvariant => CheckRefusal::MachineInvariant,
        };
        let mut free = FreeIndices::default();
        let term = CoreTerm::Value(read);
        let closed = free
            .intuitionistic(context.arena(), term)
            .map_err(refused)?
            .is_empty()
            && free
                .linear(context.arena(), term)
                .map_err(refused)?
                .is_empty();
        if closed {
            return Ok(read);
        }
    }
    crate::product::certificate(context, at, classifier)
}

/// Decide and record the simulation a stay or a composite over session codes
/// stands for.
///
/// # Specification
/// - requires: `carrier` is the flow's formed carrier; both endpoints checked
///   against it.
/// - ensures: when the carrier is the value universe at level zero and both
///   endpoints are session codes, the engine's simulation from `source` to
///   `target` is recorded at `at`; otherwise nothing is recorded, and the
///   bridge keeps the flow on the checker's side.
/// - fails: [`CheckRefusal::SessionNotSubtype`] at `at` when the engine does
///   not relate them; the unfolding's and the engine's refusals.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a stay at a session code and a composite of two
///   simulations are recorded and replay; a stay at a boolean records nothing.
/// - witness: `flow::tests::stays_and_composites_record_their_simulation`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::SessionNotSubtype { at: site }) => site == at,
    | Ok(()) | Err(_) => true,
})]
pub fn record_simulation(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    carrier: ValueTypeId,
    (source, target): (ValueId, ValueId),
) -> Result<(), CheckRefusal>
{
    let head = context.whnf_value_type(carrier)?;
    let ValueTypeView::Universe {
        sort: GroundSort::Value,
        level,
    } = value_type_view(context.arena(), head)?
    else {
        return Ok(());
    };
    if *level != Level::zero() {
        return Ok(());
    }
    for code in [source, target] {
        if let Maybe::Absent(_) = session_code(context, code)? {
            return Ok(());
        }
    }
    let statement = decide(context, at, SessionRelation::Subtyping, (source, target))?;
    context.record_flow(at, statement);
    Ok(())
}

/// The carrier and endpoints of the flow type `classifier`.
///
/// # Specification
/// - requires: nothing; a classifier of another former is refused.
/// - ensures: the carrier, the source and the target of the flow type
///   `classifier` reads as at its weak head.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a flow type, for
///   any other former; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a ride along a path is refused by its shape.
/// - witness: `flow::tests::each_refusal_is_named`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::Flow && found == TypeNode::Value(classifier),
    | Ok(_) | Err(_) => true,
})]
pub fn endpoints(
    context: &mut CheckingContext<'_>,
    at: TermNode,
    classifier: ValueTypeId,
) -> Result<(ValueTypeId, ValueId, ValueId), CheckRefusal>
{
    let head = context.whnf_value_type(classifier)?;
    match value_type_view(context.arena(), head)? {
        ValueTypeView::Flow {
            carrier,
            source,
            target,
        } => Ok((carrier, source, target)),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => Err(CheckRefusal::ShapeMismatch {
            at,
            wanted: ExpectedShape::Flow,
            found: TypeNode::Value(classifier),
        }),
    }
}

/// Whether the two values convert: the same node, the same syntax, or the
/// normaliser's conversion with every admitted definition unfolding.
///
/// # Specification
/// - requires: both stand under the judgement's binders.
/// - ensures: true exactly when they are one node, equal certificate syntax, or
///   the normaliser relates them.
/// - fails: a dangling node or a machine invariant as the conversion raises it;
///   an undecided conversion answers false.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a stay rides as the identity at any motive.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
#[spec(ensures: |ret| left != right || ret == Ok(Agreement::Convertible))]
fn convertible(
    context: &CheckingContext<'_>,
    left: ValueId,
    right: ValueId,
) -> Result<Agreement, CheckRefusal>
{
    let arena = context.arena();
    if left == right
        || gandr_core_term::equal_certificate_syntax(arena, left, right)
            == gandr_core_term::CertificateEquality::Equal
    {
        return Ok(Agreement::Convertible);
    }
    match context.definitions().relate_terms(arena, left, right, &[]) {
        Ok(Maybe::Present(_)) => Ok(Agreement::Convertible),
        Ok(Maybe::Absent(_)) | Err(CheckRefusal::Undecided { .. }) => Ok(Agreement::Apart),
        Err(fault) => Err(fault),
    }
}

/// Whether the motive reads its code only covariantly, and closed but for it.
///
/// # Specification
/// - requires: `motive` stands under one binder, its code.
/// - ensures: success exactly when the motive reads no binder past its own and
///   every occurrence of its code is the code itself at a covariant position:
///   beneath products, sums, records, lists, thunks, lifts, returners and lazy
///   pairs, an arrow's or a dependent arrow's codomain, a flow's target, a
///   run's protocol and a decode; a flow's source and a domain reverse the
///   variance; a path, a dependent pair, a data argument, a session payload, a
///   capability, a stack and any compound value are invariant.
/// - fails: [`CheckRefusal::RideUnsupported`] at `at` for a motive reading an
///   outer binder; [`CheckRefusal::NonCovariantMotive`] at `at` for an
///   occurrence elsewhere; a dangling node.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the motive's finite tree, not
///   recursion.
/// - measure: the positions left, each replaced by its strictly smaller
///   children.
///
/// # Adequacy
/// - hypothesis: L3 — a run motive passes, a flow motive with the code at its
///   source is refused, a code under an arrow's domain is refused and one under
///   its codomain passes.
/// - witness: `flow::tests::motives_ride_only_covariantly`
/// - witness: `flow::tests::a_code_rides_beneath_exactly_the_covariant_formers`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::NonCovariantMotive { at: site } | CheckRefusal::RideUnsupported { at: site }) => site == at,
    | Ok(()) | Err(_) => true,
})]
pub fn covariant(
    arena: &CoreArena,
    at: ComputationId,
    motive: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let reach = |node| loose_reach(arena, node).map(usize::from);
    match reach(CoreNode::Type(TypeNode::Value(motive)))? {
        0 => return Ok(()),
        1 => {},
        _ => return Err(CheckRefusal::RideUnsupported { at }),
    }
    let refused = CheckRefusal::NonCovariantMotive { at };
    let dangling = |node| CheckRefusal::DanglingNode { node };
    let mut work = Vec::from([(Position::ValueType(motive), Polarity::Positive, 0_usize)]);
    while let Some((position, polarity, depth)) = work.pop() {
        let under = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        let node = match position {
            Position::ValueType(id) => CoreNode::Type(TypeNode::Value(id)),
            Position::CompType(id) => CoreNode::Type(TypeNode::Computation(id)),
            Position::Value(id) => CoreNode::Term(TermNode::Value(id)),
        };
        if reach(node)? <= depth {
            continue;
        }
        if polarity == Polarity::Invariant {
            return Err(refused);
        }
        let flipped = polarity.flipped();
        match position {
            Position::Value(id) => match *arena.value(id).ok_or_else(|| dangling(node))? {
                Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                } if polarity == Polarity::Positive
                    && usize::try_from(u32::from(index)).ok() == Some(depth) => {},
                Value::Primitive { .. }
                | Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::PathEquiv { .. }
                | Value::Here(_)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Univalence(..)
                | Value::Ua { .. }
                | Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..)
                | Value::Recorded(_)
                | Value::Dialogue(_)
                | Value::Web(_)
                | Value::Returned(_)
                | Value::Nested(_)
                | Value::Run(_)
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Tuple(_)
                | Value::Injection(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Thunk(_)
                | Value::Ascribe { .. }
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticLambda(_)
                | Value::StaticApplication(..)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::Reify(_) => return Err(refused),
            },
            Position::ValueType(id) => match *arena.value_type(id).ok_or_else(|| dangling(node))? {
                ValueType::Run(code)
                | ValueType::Prefix(code)
                | ValueType::Element { code, .. } => {
                    work.push((Position::Value(code), polarity, depth));
                },
                ValueType::Flow {
                    carrier,
                    source,
                    target,
                } => {
                    work.push((Position::ValueType(carrier), Polarity::Invariant, depth));
                    work.push((Position::Value(source), flipped, depth));
                    work.push((Position::Value(target), polarity, depth));
                },
                ValueType::Record(ref fields) => work.extend(
                    fields
                        .values()
                        .map(|&field| (Position::ValueType(field), polarity, depth)),
                ),
                ValueType::Product(ref parts) | ValueType::Sum(ref parts) => work.extend(
                    parts
                        .iter()
                        .map(|&part| (Position::ValueType(part), polarity, depth)),
                ),
                ValueType::List(inner)
                | ValueType::Lift { inner, .. }
                | ValueType::Staged { base: inner, .. }
                | ValueType::Kept { value: inner, .. } => {
                    work.push((Position::ValueType(inner), polarity, depth));
                },
                ValueType::Thunk(body) => work.push((Position::CompType(body), polarity, depth)),
                ValueType::StaticPi { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::ValueType(codomain), polarity, depth));
                },
                ValueType::Data { .. }
                | ValueType::Sigma { .. }
                | ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Abstract(_)
                | ValueType::Unknown
                | ValueType::Stack { .. }
                | ValueType::Session(_)
                | ValueType::Capability { .. }
                | ValueType::Buffer
                | ValueType::Dialogue(_)
                | ValueType::Web
                | ValueType::World(_) => return Err(refused),
            },
            Position::CompType(id) => match *arena.comp_type(id).ok_or_else(|| dangling(node))? {
                CompType::Returner { result, .. } => {
                    work.push((Position::ValueType(result), polarity, depth));
                },
                CompType::Arrow { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::CompType(codomain), polarity, depth));
                },
                CompType::Pi { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::CompType(codomain), polarity, under));
                },
                CompType::Element { code, .. } => {
                    work.push((Position::Value(code), polarity, depth));
                },
                CompType::With(ref components) => {
                    work.extend(
                        components
                            .iter()
                            .map(|&component| (Position::CompType(component), polarity, depth)),
                    );
                },
                CompType::Codata { .. } | CompType::Unknown => return Err(refused),
            },
        }
    }
    Ok(())
}

/// The family a transport or a ride at `at` forms its motive as: `written`
/// with its binder's decodes read at the level of `carrier`, the universe its
/// path or flow lives in.
///
/// # Specification
/// - requires: `written` is `at`'s motive, standing under one binder of
///   `carrier`.
/// - ensures: `written` where `carrier` is no universe or the universe at level
///   zero, with nothing recorded; otherwise `written` with every decode of its
///   binder at the carrier's level, recorded at `at` where that moves a decode.
///   The level is the carrier's, read, never solved.
/// - fails: as the head-normal form of `carrier` fails.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a ride and a transport along a level-one universe form
///   their motives at level one and the kernel replays both, while a ride at
///   level zero records nothing.
/// - witness: `flow::tests::a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&family| family == written || context.motives().get(&at) == Some(&family)))]
pub fn levelled(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    written: ValueTypeId,
    carrier: ValueTypeId,
) -> Result<ValueTypeId, CheckRefusal>
{
    let carrier = context.whnf_value_type(carrier)?;
    let level = match context.arena().value_type(carrier) {
        Some(&ValueType::Universe { ref level, .. }) if !bool::from(level.is_zero()) => {
            level.clone()
        },
        _ => return Ok(written),
    };
    let family = relevel_value_type(context.arena_mut(), written, level);
    if family != written {
        context.record_motive(at, family);
    }
    Ok(family)
}

/// Classify the ride `at` along a flow of type `flow`, its motive formed.
///
/// # Specification
/// - requires: `at` is a ride whose flow synthesised `flow` and whose motive
///   formed under a binder of the flow's carrier.
/// - ensures: the motive at the flow's source, the returner of the motive at
///   its target, and whether a run moves: fixed for a motive that ignores its
///   code, a flow whose endpoints convert, a flow at an element carrier, or a
///   motive the directed computation table moves ([`computed`]) along a flow
///   between codes that are not both session codes; moving for a run or prefix
///   motive between two session codes the engine relates by subtyping.
/// - fails: [`CheckRefusal::NonCovariantMotive`] and
///   [`CheckRefusal::RideUnsupported`] as [`covariant`] raises them;
///   [`CheckRefusal::RideUnsupported`] at `at` for a motive other than `Run(X)`
///   or `Prefix(X)` between distinct session codes, and for a motive the
///   computation table does not move between distinct codes;
///   [`CheckRefusal::SessionCodeExpected`] at an endpoint of a run or prefix
///   motive that is no session code; [`CheckRefusal::SessionNotSubtype`] at the
///   flow for sessions the engine does not relate; a shape mismatch for a
///   classifier that is no flow type.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a run or prefix motive moves between a session and its
///   widening, a list motive between them is unsupported, a stay rides fixed, a
///   decode of the code rides a migration fixed while a record of it is
///   unsupported, and the symmetry motive along a migration is refused.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::a_prefix_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::motives_ride_only_covariantly`
/// - witness: `forward::tests::a_migration_is_decided_at_every_covering_input`
/// - witness: `forward::tests::the_symmetry_ride_along_a_migration_is_refused`
/// - witness: `flow::tests::a_ride_between_session_codes_is_fixed_only_for_a_constant_motive`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::NonCovariantMotive { at: site } | CheckRefusal::RideUnsupported { at: site }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn ride(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    flow: ValueTypeId,
) -> Result<Ride, CheckRefusal>
{
    let Some(&Computation::Ride {
        motive: written,
        flow: along,
        value,
    }) = context.arena().computation(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let motive = context.motive(at, written);
    let (carrier, source, target) = endpoints(context, TermNode::Computation(at), flow)?;
    covariant(context.arena(), at, motive)?;
    let constant = usize::from(loose_reach(
        context.arena(),
        CoreNode::Type(TypeNode::Value(motive)),
    )?) == 0;
    let arena = context.arena_mut();
    let from = instantiate_value_type(arena, motive, source);
    let to = instantiate_value_type(arena, motive, target);
    let result = arena.comp_type_returner(to);
    let fixed = Ride {
        value,
        source: from,
        result,
        moving: Moving::Fixed,
    };
    if constant || convertible(context, source, target)? == Agreement::Convertible {
        return Ok(fixed);
    }
    // A complete or open play over the motive's own binder: the code a ride
    // moves.
    let played = match context.arena().value_type(motive) {
        Some(&ValueType::Run(code)) => Some((Moving::Run, code)),
        Some(&ValueType::Prefix(code)) => Some((Moving::Prefix, code)),
        _ => None,
    }
    .filter(|&(_, code)| {
        matches!(
            context.arena().value(code),
            Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0
        )
    })
    .map(|(moving, _)| moving);
    let Some(moving) = played
    else {
        let carrier = context.whnf_value_type(carrier)?;
        if !matches!(
            value_type_view(context.arena(), carrier)?,
            ValueTypeView::Universe {
                sort: GroundSort::Value,
                ..
            }
        ) {
            return Ok(fixed);
        }
        if let (Maybe::Present(_), Maybe::Present(_)) = (
            session_code(context, source)?,
            session_code(context, target)?,
        ) {
            return Err(CheckRefusal::RideUnsupported { at });
        }
        let arena = context.arena();
        let ValueTypeView::Universe { level, .. } = value_type_view(arena, carrier)?
        else {
            return Ok(fixed);
        };
        computed(arena, at, motive, level)?;
        return Ok(fixed);
    };
    let (left, right) = sessions(context, (source, target))?;
    if let Maybe::Absent(_) = converting_evidence(context, (&left, &right), Relation::Subtype)? {
        return Err(CheckRefusal::SessionNotSubtype { at: along });
    }
    Ok(Ride { moving, ..fixed })
}

/// Check that the directed computation table moves `motive`: each position
/// that reads the code is the decode of the code itself at `level`, the level
/// of the universe the flow lives in, a product, a sum or a list of such
/// positions, or a flow singleton `Flow(Type, l, X)` whose source ignores the
/// code.
///
/// # Specification
/// - requires: `motive` stands under one binder, its code, and passed
///   [`covariant`]; `level` is the level of the universe that binder ranges
///   over.
/// - ensures: success exactly when every position the walk meets that reads the
///   code is one of the rows above; a position ignoring the code is returned
///   unchanged by every row.
/// - provides: the rows the kernel's ride reduction, the normaliser and the
///   runtime share, so a ride the judgement accepts computes in all three.
/// - fails: [`CheckRefusal::RideUnsupported`] at `at` for any other position
///   reading the code; a dangling node.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a `while let` worklist over the motive's finite tree, not
///   recursion.
/// - measure: the positions left, each replaced by its strictly smaller parts.
///
/// # Adequacy
/// - hypothesis: L3 — a decode of the code at the flow's level and a pair of it
///   pass; a record of it, a thunk of an arrow into it and a decode at another
///   level are refused.
/// - witness: `flow::tests::motives_ride_only_covariantly`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::RideUnsupported { at: site }) => site == at,
    | Ok(()) | Err(_) => true,
})]
fn computed(
    arena: &CoreArena,
    at: ComputationId,
    motive: ValueTypeId,
    level: &Level,
) -> Result<(), CheckRefusal>
{
    let unsupported = CheckRefusal::RideUnsupported { at };
    let reads = |node| loose_reach(arena, node).map(|reach| usize::from(reach) != 0);
    let code = |id| {
        matches!(
            arena.value(id),
            Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0
        )
    };
    let mut pending = Vec::from([motive]);
    while let Some(position) = pending.pop() {
        if !reads(CoreNode::Type(TypeNode::Value(position)))? {
            continue;
        }
        let node = CoreNode::Type(TypeNode::Value(position));
        match *arena
            .value_type(position)
            .ok_or(CheckRefusal::DanglingNode { node })?
        {
            ValueType::Element {
                code: decoded,
                ref target,
            } if code(decoded) && target == level => {},
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                pending.extend(parts.iter().copied());
            },
            ValueType::List(element) => pending.push(element),
            ValueType::Flow {
                carrier,
                source,
                target,
            } if code(target)
                && !reads(CoreNode::Type(TypeNode::Value(carrier)))?
                && !reads(CoreNode::Term(TermNode::Value(source)))? => {},
            ValueType::Data { .. }
            | ValueType::Record(_)
            | ValueType::PathUniverse(..)
            | ValueType::Path { .. }
            | ValueType::Flow { .. }
            | ValueType::Run(_)
            | ValueType::Prefix(_)
            | ValueType::Dialogue(_)
            | ValueType::Web
            | ValueType::Base(_)
            | ValueType::Sigma { .. }
            | ValueType::Thunk(_)
            | ValueType::Universe { .. }
            | ValueType::Lift { .. }
            | ValueType::Element { .. }
            | ValueType::Abstract(_)
            | ValueType::StaticPi { .. }
            | ValueType::Unknown
            | ValueType::Stack { .. }
            | ValueType::Session(_)
            | ValueType::Capability { .. }
            | ValueType::Buffer
            | ValueType::Staged { .. }
            | ValueType::Kept { .. }
            | ValueType::World(_) => return Err(unsupported),
        }
    }
    Ok(())
}

/// Admit the ridden value `value` at the flow's target.
///
/// # Specification
/// - requires: [`ride`] classified the ride `at` along `flow` as `moving`, and
///   `value` checked at the motive's source fibre.
/// - ensures: success for a fixed ride; for a moving one, success exactly when
///   the recorded-run consumer advances the literal `value` reduces to along
///   the engine's simulation — complete for a run, complete or open for a
///   prefix — or, for an open value, when the simulation narrows no offer.
/// - fails: [`CheckRefusal::RunNotAdmitted`] at `value` with the first move the
///   target refuses, or [`RunFault::OfferNarrowed`] for an open value; the
///   engine's and the unfolding's refusals.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a run through a report moves to the widened protocol, a
///   run taking a dropped offer is refused at that move, and an open run along
///   an offer-narrowing flow is refused as such; an open prefix moves and stays
///   open, and one that took a dropped offer is refused at that move.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::a_prefix_rides_forward_and_refuses_by_move`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::RunNotAdmitted { at: site, .. }) => site == value && moving != Moving::Fixed,
    | Ok(()) | Err(_) => true,
})]
pub fn admit(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    value: ValueId,
    flow: ValueTypeId,
    moving: Moving,
) -> Result<(), CheckRefusal>
{
    if moving == Moving::Fixed {
        return Ok(());
    }
    let (_, source, target) = endpoints(context, TermNode::Computation(at), flow)?;
    let (left, right) = sessions(context, (source, target))?;
    let Maybe::Present(evidence) =
        converting_evidence(context, (&left, &right), Relation::Subtype)?
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let head = context.whnf_code(value)?;
    if let Some(found) = context.arena().value(head)
        && let Value::Recorded(ref moves) = *found
    {
        let moves: Vec<Move> = moves.iter().map(skeleton_move).collect();
        let protocols = (&engine(&left)?, &engine(&right)?);
        let advanced = if moving == Moving::Prefix {
            gandr_core_session::certified::advance_prefix(protocols, &evidence, &moves)
        }
        else {
            gandr_core_session::certified::advance(protocols, &evidence, &moves)
        };
        return advanced
            .map(|_moved| ())
            .map_err(|error| transport_refusal(value, &error));
    }
    for pair in &evidence.pairs {
        let offers = |session: &SessionType, position: usize| match session
            .protocol()
            .node(ProtocolState::from(position))
        {
            Ok(&ProtocolNode::Offer(ref branches)) => Ok(Some(branches.len())),
            Ok(_) => Ok(None),
            Err(_) => Err(CheckRefusal::MachineInvariant),
        };
        if let (Some(wide), Some(narrow)) = (
            offers(&left, pair.source.0)?,
            offers(&right, pair.target.0)?,
        ) && wide != narrow
        {
            return Err(CheckRefusal::RunNotAdmitted {
                at: value,
                fault: RunFault::OfferNarrowed,
            });
        }
    }
    Ok(())
}

/// The payloads of the recorded run `at` and the types its protocol names
/// for them, once the monitor of the run or prefix type `expected` accepts
/// its skeleton.
///
/// # Specification
/// - requires: `at` is a recorded run checked against `expected`.
/// - ensures: one premise per payload move, in move order, at the payload type
///   the protocol names at that move; none against the unknown type. A run type
///   admits a run the monitor closes; a prefix type admits one it closes or
///   leaves open.
/// - fails: [`CheckRefusal::ShapeMismatch`] wanting a run or prefix type for
///   any other former; [`CheckRefusal::SessionCodeExpected`] at a protocol that
///   is no session code; [`CheckRefusal::RunNotAdmitted`] at `at` with the
///   first move the monitor refuses, or, against a run type, the incomplete
///   run's length.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a complete seat run checks with its three payloads, a
///   paused run is refused at its pause and a truncated one at its end; the
///   truncated run checks as a prefix, which still refuses a move the protocol
///   does not offer.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::a_prefix_admits_an_open_run_and_refuses_by_move`
/// - witness: `flow::tests::each_refusal_is_named`
/// - witness: `judgement::tests::each_former_refuses_a_classifier_of_another_shape_by_name`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::RunNotAdmitted { at: site, .. }) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn run_premises(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    expected: ValueTypeId,
) -> Result<Vec<(ValueId, ValueTypeId)>, CheckRefusal>
{
    let head = context.whnf_value_type(expected)?;
    let (protocol, open_admitted) = match value_type_view(context.arena(), head)? {
        ValueTypeView::Run(protocol) => (protocol, false),
        ValueTypeView::Prefix(protocol) => (protocol, true),
        ValueTypeView::Unknown => return Ok(Vec::new()),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Session(_)
        | ValueTypeView::World(_) => {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Run,
                found: TypeNode::Value(expected),
            });
        },
    };
    let Maybe::Present(session) = session_code(context, protocol)?
    else {
        return Err(CheckRefusal::SessionCodeExpected { at: protocol });
    };
    let Some(found) = context.arena().value(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let Value::Recorded(ref recorded) = *found
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let moves = Arc::clone(recorded);
    let skeleton: Vec<Move> = moves.iter().map(skeleton_move).collect();
    match gandr_core_session::replay(&engine(&session)?, &skeleton) {
        Ok(_) => {},
        Err(ReplayError::IncompleteRun { .. }) if open_admitted => {},
        Err(ref error) => return Err(replay_refusal(at, error)),
    }
    payload_premises(session, moves.iter())
}

/// The payloads of the dialogue `at` and the types its endpoints' protocols
/// name for them, once the dialogue type `expected` admits it.
///
/// A dialogue logs both endpoints' moves on one channel; `Dialogue(S)` holds
/// those whose left endpoint runs `S` to its close and whose right runs the
/// dual. Admission is [`gandr_core_session::admit`] over the moves'
/// skeletons: each endpoint replays against its protocol, the `k`-th move out
/// of one endpoint meets the `k`-th move into the other under the same label,
/// and no move is logged before one the dialogue's causal web orders first.
/// Every receipt then converts with the payload sent. A refusal names its
/// move by its position in the log.
///
/// # Specification
/// - requires: `at` is a dialogue checked against `expected`.
/// - ensures: one premise per payload move, the left endpoint's in its own
///   order and then the right's, each at the payload type its endpoint's
///   protocol names at that move; none against the unknown type.
/// - fails: [`CheckRefusal::ShapeMismatch`] wanting a dialogue type for any
///   other former; [`CheckRefusal::SessionCodeExpected`] at a protocol that is
///   no session code; [`CheckRefusal::RunNotAdmitted`] at `at` with the log
///   position of the first move an endpoint's monitor refuses, the left
///   endpoint's first, or the log's length for an endpoint that stops before
///   its close; [`CheckRefusal::DialogueUnmatched`] at the first send or
///   selection the other endpoint does not receive or offer alike, at the first
///   receipt or offer past every send, or at a receipt whose payload does not
///   convert with the one sent; [`CheckRefusal::DialogueInverted`] at a move
///   logged before one its web orders first.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a seat's dialogue checks in two interleavings; a receipt
///   logged before its send is inverted; a receipt of another payload and an
///   offer of another label are unmatched; a move off the seat's protocol is
///   refused at its log position, and a dialogue that stops short at the log's
///   end.
/// - witness: `flow::tests::a_dialogue_checks_by_its_web_and_refuses_by_move`
#[spec(ensures: |ret| match ret {
    | Err(
        CheckRefusal::RunNotAdmitted { at: site, .. }
        | CheckRefusal::DialogueUnmatched { at: site, .. }
        | CheckRefusal::DialogueInverted { at: site, .. },
    ) => site == at,
    | Ok(_) | Err(_) => true,
})]
pub fn dialogue_premises(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    expected: ValueTypeId,
) -> Result<Vec<(ValueId, ValueTypeId)>, CheckRefusal>
{
    let head = context.whnf_value_type(expected)?;
    let protocol = match value_type_view(context.arena(), head)? {
        ValueTypeView::Dialogue(protocol) => protocol,
        ValueTypeView::Unknown => return Ok(Vec::new()),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_)
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::World(_) => {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::Dialogue,
                found: TypeNode::Value(expected),
            });
        },
    };
    let Maybe::Present(left) = session_code(context, protocol)?
    else {
        return Err(CheckRefusal::SessionCodeExpected { at: protocol });
    };
    let right = left.dual();
    let Some(found) = context.arena().value(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let Value::Dialogue(ref logged) = *found
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let dialogue = Arc::clone(logged);
    let turns: Vec<Turn> = dialogue
        .iter()
        .map(|turn| Turn {
            side: turn.endpoint,
            movement: skeleton_move(&turn.movement),
        })
        .collect();
    let log = Log::of(&dialogue);
    match gandr_core_session::admit((&engine(&left)?, &engine(&right)?), &turns) {
        Ok(_web) => {},
        Err(DialogueRefusal::Replay { side, ref error }) => {
            return Err(
                replay_fault(error).map_or(CheckRefusal::MachineInvariant, |fault| {
                    CheckRefusal::RunNotAdmitted {
                        at,
                        fault: log.fault(side, fault),
                    }
                }),
            );
        },
        Err(DialogueRefusal::Unmatched { event }) => {
            return Err(CheckRefusal::DialogueUnmatched {
                at,
                step: log.event(event),
            });
        },
        Err(DialogueRefusal::Inverted { earlier, later }) => {
            return Err(CheckRefusal::DialogueInverted {
                at,
                earlier: log.event(earlier),
                later: log.event(later),
            });
        },
        Err(DialogueRefusal::Uncovered(_)) => return Err(CheckRefusal::MachineInvariant),
    }
    for sender in [Endpoint::Left, Endpoint::Right] {
        let sent = dialogue
            .iter()
            .filter(|turn| turn.endpoint == sender)
            .filter_map(|turn| sent_payload(&turn.movement));
        let received = dialogue
            .iter()
            .zip(0_u32 ..)
            .filter(|&(turn, _)| turn.endpoint != sender)
            .filter_map(|(turn, position)| {
                received_payload(&turn.movement).map(|payload| (payload, position))
            });
        for (sent, (received, position)) in sent.zip(received) {
            let verdict = context
                .definitions()
                .convert_terms(context.arena(), sent, received)?;
            if verdict != MachineVerdict::Convertible {
                return Err(CheckRefusal::DialogueUnmatched {
                    at,
                    step: RunStep::from(position),
                });
            }
        }
    }
    let moves_of = |side: Endpoint| {
        dialogue
            .iter()
            .filter(move |turn| turn.endpoint == side)
            .map(|turn| &turn.movement)
    };
    let mut premises = payload_premises(left, moves_of(Endpoint::Left))?;
    premises.extend(payload_premises(right, moves_of(Endpoint::Right))?);
    Ok(premises)
}

/// The payload a move sends, if it sends one.
///
/// # Specification
/// trivial.
fn sent_payload(movement: &RecordedMove) -> Option<ValueId>
{
    match *movement {
        RecordedMove::Sent(payload) => Some(payload),
        RecordedMove::Received(_)
        | RecordedMove::Selected(_)
        | RecordedMove::Offered(_)
        | RecordedMove::Closed => None,
    }
}

/// The payload a move receives, if it receives one.
///
/// # Specification
/// trivial.
fn received_payload(movement: &RecordedMove) -> Option<ValueId>
{
    match *movement {
        RecordedMove::Received(payload) => Some(payload),
        RecordedMove::Sent(_)
        | RecordedMove::Selected(_)
        | RecordedMove::Offered(_)
        | RecordedMove::Closed => None,
    }
}

/// Where each endpoint's moves sit in a dialogue's log.
///
/// # Specification
/// trivial.
struct Log
{
    /// The log position of each of the left endpoint's moves, in its order.
    left: Vec<RunStep>,
    /// The log position of each of the right endpoint's moves, in its order.
    right: Vec<RunStep>,
    /// The log's length: where an endpoint that stops short is refused.
    end: RunStep,
}

impl Log
{
    /// The positions of `dialogue`'s moves.
    ///
    /// # Specification
    /// trivial.
    fn of(dialogue: &[DialogueMove]) -> Self
    {
        let (mut left, mut right) = (Vec::new(), Vec::new());
        let mut end = 0_u32;
        for turn in dialogue {
            match turn.endpoint {
                Endpoint::Left => left.push(RunStep::from(end)),
                Endpoint::Right => right.push(RunStep::from(end)),
            }
            end = end.saturating_add(1);
        }
        Self {
            left,
            right,
            end: RunStep::from(end),
        }
    }

    /// The log position of the move `own` among the endpoint `side`'s own,
    /// the log's end past its last.
    ///
    /// # Specification
    /// trivial.
    fn position(
        &self,
        side: Endpoint,
        own: RunStep,
    ) -> RunStep
    {
        let positions = match side {
            Endpoint::Left => &self.left,
            Endpoint::Right => &self.right,
        };
        usize::try_from(u32::from(own))
            .ok()
            .and_then(|own| positions.get(own))
            .copied()
            .unwrap_or(self.end)
    }

    /// The log position of the engine's event.
    ///
    /// # Specification
    /// trivial.
    fn event(
        &self,
        event: Event,
    ) -> RunStep
    {
        self.position(event.side, step(event.at))
    }

    /// The endpoint `side`'s replay fault, its step moved to the log.
    ///
    /// # Specification
    /// trivial.
    fn fault(
        &self,
        side: Endpoint,
        fault: RunFault,
    ) -> RunFault
    {
        match fault {
            RunFault::WrongDirection(own) => RunFault::WrongDirection(self.position(side, own)),
            RunFault::WrongLabel(own) => RunFault::WrongLabel(self.position(side, own)),
            RunFault::ResumeAfterEnd(own) => RunFault::ResumeAfterEnd(self.position(side, own)),
            RunFault::Incomplete(own) => RunFault::Incomplete(self.position(side, own)),
            RunFault::OfferNarrowed => RunFault::OfferNarrowed,
        }
    }
}

/// The payloads of the moves `moves` and the types the session `session`
/// names for them, stepping the session once per move.
///
/// # Specification
/// - requires: `moves` replays against `session`.
/// - ensures: one premise per payload move, in move order, at the payload type
///   the session names at that move; the walk stops at the close.
/// - fails: [`CheckRefusal::MachineInvariant`] at a move the session does not
///   step by, which a replayed run never holds.
/// - panics: none.
/// - executable: none — the premises are the stepped session's own payload
///   types; a predicate restating them would step it again.
///
/// # Errors
/// - [`CheckRefusal::MachineInvariant`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a complete seat run checks with its three payloads, and
///   each endpoint of a dialogue checks its own payloads at its protocol.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::a_dialogue_checks_by_its_web_and_refuses_by_move`
pub fn payload_premises<'moves, Moves>(
    session: SessionType,
    moves: Moves,
) -> Result<Vec<(ValueId, ValueTypeId)>, CheckRefusal>
where
    Moves: IntoIterator<Item = &'moves RecordedMove>,
{
    let mut premises = Vec::new();
    let mut current = session;
    for movement in moves {
        let next = match (current.step(), movement) {
            (Ok(ProtocolStep::Send { payload, next }), &RecordedMove::Sent(value))
            | (Ok(ProtocolStep::Receive { payload, next }), &RecordedMove::Received(value)) => {
                premises.push((value, payload));
                next
            },
            (Ok(ProtocolStep::Select(branches)), &RecordedMove::Selected(ref label))
            | (Ok(ProtocolStep::Offer(branches)), &RecordedMove::Offered(ref label)) => {
                match branches.get(label) {
                    Ok(Maybe::Present(next)) => next,
                    Ok(Maybe::Absent(_)) | Err(_) => return Err(CheckRefusal::MachineInvariant),
                }
            },
            (Ok(ProtocolStep::End), &RecordedMove::Closed) => break,
            _ => return Err(CheckRefusal::MachineInvariant),
        };
        current = next;
    }
    Ok(premises)
}

/// The engine's skeleton of one recorded move: a payload of one identity and
/// one opaque digest, a label as written.
///
/// # Specification
/// trivial.
pub fn skeleton_move(movement: &RecordedMove) -> Move
{
    let payload = Payload {
        identity: gandr_core_session::ValueTypeId([0_u8; 32]),
        digest: PayloadDigest([0_u8; 32]),
    };
    match *movement {
        RecordedMove::Sent(_) => Move::Send(payload),
        RecordedMove::Received(_) => Move::Receive(payload),
        RecordedMove::Selected(ref label) => Move::Select(Label::from(label.as_ref())),
        RecordedMove::Offered(ref label) => Move::Offer(Label::from(label.as_ref())),
        RecordedMove::Closed => Move::End,
    }
}

/// The move position of an engine index, saturating past `u32`.
///
/// # Specification
/// trivial.
fn step(index: gandr_core_session::MoveIndex) -> RunStep
{
    RunStep::from(u32::try_from(index.0).unwrap_or(u32::MAX))
}

/// The refusal of the run `at` for the monitor's replay error.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`CheckRefusal::RunNotAdmitted`] at `at` with the fault
///   [`replay_fault`] reads, or a machine invariant where it reads none.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a paused run, a truncated one, one moving the wrong way
///   and one moving past its close name distinct faults.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::each_refusal_is_named`
#[spec(ensures: |ret| matches!(ret, CheckRefusal::RunNotAdmitted { at: site, .. } if site == at)
    || ret == CheckRefusal::MachineInvariant)]
fn replay_refusal(
    at: ValueId,
    error: &ReplayError,
) -> CheckRefusal
{
    replay_fault(error).map_or(CheckRefusal::MachineInvariant, |fault| {
        CheckRefusal::RunNotAdmitted { at, fault }
    })
}

/// The fault the monitor's replay error names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a refused move keeps its position and its kind — a wrong label, a
///   wrong direction, a move after the close; an incomplete run keeps its
///   length; a payload identity, which the skeleton never varies, and a broken
///   protocol name none.
/// - panics: none.
/// - executable: none — each fault is the error's own position under another
///   name; a predicate restating the match would be the match.
///
/// # Adequacy
/// - hypothesis: L3 — a paused run, a truncated one, one moving the wrong way
///   and one moving past its close name distinct faults.
/// - witness: `flow::tests::each_refusal_is_named`
pub fn replay_fault(error: &ReplayError) -> Option<RunFault>
{
    match *error {
        ReplayError::Refused {
            at: index, reason, ..
        } => match reason {
            gandr_core_session::Refusal::WrongLabel => Some(RunFault::WrongLabel(step(index))),
            gandr_core_session::Refusal::WrongDirection => {
                Some(RunFault::WrongDirection(step(index)))
            },
            gandr_core_session::Refusal::ResumeAfterEnd => {
                Some(RunFault::ResumeAfterEnd(step(index)))
            },
            gandr_core_session::Refusal::WrongPayloadIdentity => None,
        },
        ReplayError::IncompleteRun { at: index, .. } => Some(RunFault::Incomplete(step(index))),
        ReplayError::InvalidType(_) => None,
    }
}

/// The refusal of the run `at` for the consumer's transport error.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a source replay error as [`replay_refusal`]; a move the target or
///   the relation refuses keeps its position and kind; every other error, which
///   a decided simulation never gives, is a machine invariant.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a run taking a dropped offer is refused at that move.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
#[spec(ensures: |ret| matches!(ret, CheckRefusal::RunNotAdmitted { at: site, .. } if site == at)
    || ret == CheckRefusal::MachineInvariant)]
fn transport_refusal(
    at: ValueId,
    error: &TransportError,
) -> CheckRefusal
{
    match *error {
        TransportError::Replay(ref replayed) => replay_refusal(at, replayed),
        TransportError::Move {
            at: index,
            ref reason,
        } => {
            let fault = match *reason {
                gandr_core_session::Refusal::WrongLabel => RunFault::WrongLabel(step(index)),
                gandr_core_session::Refusal::WrongDirection => {
                    RunFault::WrongDirection(step(index))
                },
                gandr_core_session::Refusal::ResumeAfterEnd => {
                    RunFault::ResumeAfterEnd(step(index))
                },
                gandr_core_session::Refusal::WrongPayloadIdentity => {
                    return CheckRefusal::MachineInvariant;
                },
            };
            CheckRefusal::RunNotAdmitted { at, fault }
        },
        TransportError::MissingPayload(_)
        | TransportError::CodeBinding
        | TransportError::Direction
        | TransportError::ExpectedSessionFlow
        | TransportError::Flow(_)
        | TransportError::Type(_)
        | TransportError::Session(_) => CheckRefusal::MachineInvariant,
    }
}
