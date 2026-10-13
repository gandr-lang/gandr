//! Directed identity over sessions: `Flow(A, a, b)`, the statements that
//! inhabit it and its path counterpart, and the recorded runs that ride it.
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
//! `f then g` synthesises `Flow(A, a, c)` from `f : Flow(A, a, b)` and `g`
//! checked against `Flow(A, b, c)`. When the carrier is the value universe
//! and the endpoints are session codes, the engine decides the composite's
//! own simulation and the judgement records it as it records `sim`, so the
//! kernel replays a stay or a composite as one simulation.
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
//! ride as the identity. Between two distinct session codes the motive must be
//! `Run(X)` ([`CheckRefusal::RideUnsupported`] otherwise): the run moves by
//! `gandr-core-session`'s recorded-run consumer along the engine's simulation,
//! never by the kernel's lowering of a flow, which refuses a session flow as
//! `RecordedRunRequired`. A literal run is advanced move by move at check
//! time, and a run the target does not admit — one that takes an offer the
//! target has dropped — is [`CheckRefusal::RunNotAdmitted`] at the move. An
//! open run is admitted when the simulation narrows no offer, so every run of
//! the source is a run of the target. An admitted ride returns the run
//! unchanged: its skeleton is the target's, labels and payloads kept.
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
//!
//! # What a consumer may assume
//!
//! A protocol's receipts are runs: `Run(S)` is a complete trace the monitor
//! of `S` accepts. Compatibility of an old protocol with a new one is a
//! `Flow(Type, Old, New)` the engine decides and the kernel replays; riding
//! it moves every old receipt the new protocol admits and refuses, by move,
//! every one it does not. Equivalence is a `Path(Type, A, B)`, replayed the
//! same way; it identifies the two codes, so every run of one is a run of the
//! other by conversion alone.

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_session::Label;
use gandr_core_session::Move;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Relation;
use gandr_core_session::ReplayError;
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
/// the classifier the bridge erases it at and the engine's evidence.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Statement
{
    /// Bisimilarity or simulation.
    relation: SessionRelation,
    /// The native classifier: `Path_U(⌜A⌝, ⌜B⌝)` for a bisimilarity, the
    /// universe's `Flow(Type, ⌜A⌝, ⌜B⌝)` for a simulation.
    classifier: ValueTypeId,
    /// The engine's pairs over the two protocols' node positions.
    evidence: Arc<Evidence>,
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
}

/// Whether a ride moves a run between distinct sessions, or rides as the
/// identity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Moving
{
    /// The motive ignores its code, or the flow's endpoints convert.
    Fixed,
    /// A run moves between two distinct session codes.
    Run,
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
            | Self::Positive => Self::Negative,
            | Self::Negative => Self::Positive,
            | Self::Invariant => Self::Invariant,
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
        | ValueTypeView::Session(session) if session.state() == session.protocol().root() => {
            Ok(Maybe::Present(session.clone()))
        },
        | _ => elsewhere,
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
        | Some(&Value::Quote(quoted)) => {
            let quoted = context.whnf_value_type(quoted)?;
            Ok(context.arena_mut().value_quote(quoted))
        },
        | _ => Err(CheckRefusal::MachineInvariant),
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
        | Maybe::Present(session) => Ok(session),
        | Maybe::Absent(_) => Err(CheckRefusal::SessionCodeExpected { at: code }),
    };
    let left = read(source)?;
    let right = read(target)?;
    Ok((left, right))
}

/// Relate two sessions by `relation`, payload pairs compared by conversion.
///
/// # Specification
/// - requires: both are session types of the context's arena.
/// - ensures: the engine's evidence exactly when the engine relates the two
///   protocols and every payload pair it visited converts; absent otherwise.
/// - fails: as the engine and conversion raise it.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a widened selection relates by subtyping, not by
///   equivalence; a reversed pair does not relate.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref evidence)) => !evidence.pairs.is_empty(),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
fn relation_evidence(
    context: &mut CheckingContext<'_>,
    (left, right): (&SessionType, &SessionType),
    relation: Relation,
) -> Result<Maybe<Evidence, crate::session::related::Absent>, CheckRefusal>
{
    let Maybe::Present(decided) = related(left, right, relation)?
    else {
        return Ok(Maybe::Absent(crate::session::related::Absent::Unrelated));
    };
    for (first, second) in decided.payloads {
        if equivalent(context, first, second)? != Agreement::Convertible {
            return Ok(Maybe::Absent(crate::session::related::Absent::Unrelated));
        }
    }
    Ok(Maybe::Present(decided.evidence))
}

/// Decide the session statement `at` relating `(source, target)` by
/// `relation`.
///
/// # Specification
/// - requires: both operands checked against the value universe.
/// - ensures: the engine's evidence and the native classifier over the quotes
///   the operands reduce to, exactly when both are session codes the engine
///   relates with convertible payloads.
/// - provides: the decision `bisim`, `sim`, `stay` and `then` record.
/// - fails: [`CheckRefusal::SessionCodeExpected`] at an operand that is no
///   session code; [`CheckRefusal::SessionNotEquivalent`] or
///   [`CheckRefusal::SessionNotSubtype`] at `at` for sessions the engine does
///   not relate; the unfolding's and the engine's refusals.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a protocol and its renamed unfolding are bisimilar, a
///   widened selection is a supertype and not an equivalent, and the reverse
///   simulation is refused.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
/// - witness: `flow::tests::each_refusal_is_named`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::SessionNotEquivalent { at: site } | CheckRefusal::SessionNotSubtype { at: site }) => site == at,
    | Ok(ref statement) => statement.relation == relation,
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
        | SessionRelation::Equivalence => {
            (Relation::Equivalent, CheckRefusal::SessionNotEquivalent {
                at,
            })
        },
        | SessionRelation::Subtyping => (Relation::Subtype, CheckRefusal::SessionNotSubtype { at }),
    };
    let Maybe::Present(evidence) = relation_evidence(context, (&left, &right), engine_relation)?
    else {
        return Err(unrelated);
    };
    let source = quoted(context, source)?;
    let target = quoted(context, target)?;
    let arena = context.arena_mut();
    let classifier = match relation {
        | SessionRelation::Equivalence => arena.value_type_path_universe(source, target),
        | SessionRelation::Subtyping => {
            let universe = universe(arena);
            arena.value_type_flow(universe, source, target)
        },
    };
    Ok(Statement {
        relation,
        classifier,
        evidence: Arc::new(evidence),
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
        | SessionRelation::Equivalence => arena.value_type_path(universe, source, target),
        | SessionRelation::Subtyping => arena.value_type_flow(universe, source, target),
    }
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
        | ValueTypeView::Flow {
            carrier,
            source,
            target,
        } => Ok((carrier, source, target)),
        | _ => Err(CheckRefusal::ShapeMismatch {
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
    match context.definitions().relate_terms(arena, left, right) {
        | Ok(Maybe::Present(_)) => Ok(Agreement::Convertible),
        | Ok(Maybe::Absent(_)) | Err(CheckRefusal::Undecided { .. }) => Ok(Agreement::Apart),
        | Err(fault) => Err(fault),
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
///   variance; a path, a data argument, a session payload, a capability, a
///   stack and any compound value are invariant.
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
        | 0 => return Ok(()),
        | 1 => {},
        | _ => return Err(CheckRefusal::RideUnsupported { at }),
    }
    let refused = CheckRefusal::NonCovariantMotive { at };
    let dangling = |node| CheckRefusal::DanglingNode { node };
    let mut work = Vec::from([(Position::ValueType(motive), Polarity::Positive, 0_usize)]);
    while let Some((position, polarity, depth)) = work.pop() {
        let under = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        let node = match position {
            | Position::ValueType(id) => CoreNode::Type(TypeNode::Value(id)),
            | Position::CompType(id) => CoreNode::Type(TypeNode::Computation(id)),
            | Position::Value(id) => CoreNode::Term(TermNode::Value(id)),
        };
        if reach(node)? <= depth {
            continue;
        }
        if polarity == Polarity::Invariant {
            return Err(refused);
        }
        let flipped = polarity.flipped();
        match position {
            | Position::Value(id) => match *arena.value(id).ok_or_else(|| dangling(node))? {
                | Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                } if polarity == Polarity::Positive
                    && usize::try_from(u32::from(index)).ok() == Some(depth) => {},
                | _ => return Err(refused),
            },
            | Position::ValueType(id) => match *arena
                .value_type(id)
                .ok_or_else(|| dangling(node))?
            {
                | ValueType::Run(code) | ValueType::Element { code, .. } => {
                    work.push((Position::Value(code), polarity, depth));
                },
                | ValueType::Flow {
                    carrier,
                    source,
                    target,
                } => {
                    work.push((Position::ValueType(carrier), Polarity::Invariant, depth));
                    work.push((Position::Value(source), flipped, depth));
                    work.push((Position::Value(target), polarity, depth));
                },
                | ValueType::Record(ref fields) => work.extend(
                    fields
                        .values()
                        .map(|&field| (Position::ValueType(field), polarity, depth)),
                ),
                | ValueType::Product(ref parts) | ValueType::Sum(ref parts) => work.extend(
                    parts
                        .iter()
                        .map(|&part| (Position::ValueType(part), polarity, depth)),
                ),
                | ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                    work.push((Position::ValueType(inner), polarity, depth));
                },
                | ValueType::Thunk(body) => work.push((Position::CompType(body), polarity, depth)),
                | ValueType::StaticPi { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::ValueType(codomain), polarity, depth));
                },
                | ValueType::Data { .. }
                | ValueType::PathUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Abstract(_)
                | ValueType::Unknown
                | ValueType::Stack { .. }
                | ValueType::Session(_)
                | ValueType::Capability { .. } => return Err(refused),
            },
            | Position::CompType(id) => match *arena.comp_type(id).ok_or_else(|| dangling(node))? {
                | CompType::Returner { result, .. } => {
                    work.push((Position::ValueType(result), polarity, depth));
                },
                | CompType::Arrow { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::CompType(codomain), polarity, depth));
                },
                | CompType::Pi { domain, codomain } => {
                    work.push((Position::ValueType(domain), flipped, depth));
                    work.push((Position::CompType(codomain), polarity, under));
                },
                | CompType::Element { code, .. } => {
                    work.push((Position::Value(code), polarity, depth));
                },
                | CompType::With(first, second) => {
                    work.push((Position::CompType(first), polarity, depth));
                    work.push((Position::CompType(second), polarity, depth));
                },
                | CompType::Unknown => return Err(refused),
            },
        }
    }
    Ok(())
}

/// Classify the ride `at` along a flow of type `flow`, its motive formed.
///
/// # Specification
/// - requires: `at` is a ride whose flow synthesised `flow` and whose motive
///   formed under a binder of the flow's carrier.
/// - ensures: the motive at the flow's source, the returner of the motive at
///   its target, and whether a run moves: fixed for a motive that ignores its
///   code or a flow whose endpoints convert; moving for a run motive between
///   two session codes the engine relates by subtyping.
/// - fails: [`CheckRefusal::NonCovariantMotive`] and
///   [`CheckRefusal::RideUnsupported`] as [`covariant`] raises them;
///   [`CheckRefusal::RideUnsupported`] at `at` for a motive other than `Run(X)`
///   between distinct endpoints; [`CheckRefusal::SessionCodeExpected`] at an
///   endpoint that is no session code; [`CheckRefusal::SessionNotSubtype`] at
///   the flow for sessions the engine does not relate; a shape mismatch for a
///   classifier that is no flow type.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a run motive moves between a session and its widening, a
///   list motive between them is unsupported, and a stay rides fixed.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::motives_ride_only_covariantly`
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
        motive,
        flow: along,
        value,
    }) = context.arena().computation(at)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let (_, source, target) = endpoints(context, TermNode::Computation(at), flow)?;
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
    let run_motive = matches!(
        context.arena().value_type(motive),
        Some(&ValueType::Run(code)) if matches!(
            context.arena().value(code),
            Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if u32::from(index) == 0
        )
    );
    if !run_motive {
        return Err(CheckRefusal::RideUnsupported { at });
    }
    let (left, right) = sessions(context, (source, target))?;
    if let Maybe::Absent(_) = relation_evidence(context, (&left, &right), Relation::Subtype)? {
        return Err(CheckRefusal::SessionNotSubtype { at: along });
    }
    Ok(Ride {
        moving: Moving::Run,
        ..fixed
    })
}

/// Admit the ridden value `value` at the flow's target.
///
/// # Specification
/// - requires: [`ride`] classified the ride `at` along `flow` as `moving`, and
///   `value` checked at the motive's source fibre.
/// - ensures: success for a fixed ride; for a moving one, success exactly when
///   the recorded-run consumer advances the literal `value` reduces to along
///   the engine's simulation, or, for an open run, when the simulation narrows
///   no offer.
/// - fails: [`CheckRefusal::RunNotAdmitted`] at `value` with the first move the
///   target refuses, or [`RunFault::OfferNarrowed`] for an open run; the
///   engine's and the unfolding's refusals.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a run through a report moves to the widened protocol, a
///   run taking a dropped offer is refused at that move, and an open run along
///   an offer-narrowing flow is refused as such.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::RunNotAdmitted { at: site, .. }) => site == value && moving == Moving::Run,
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
    let Maybe::Present(evidence) = relation_evidence(context, (&left, &right), Relation::Subtype)?
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let head = context.whnf_code(value)?;
    if let Some(found) = context.arena().value(head)
        && let Value::Recorded(ref moves) = *found
    {
        let moves = skeleton(moves);
        return gandr_core_session::certified::advance(
            (&engine(&left)?, &engine(&right)?),
            &evidence,
            &moves,
        )
        .map(|_moved| ())
        .map_err(|error| transport_refusal(value, &error));
    }
    for pair in &evidence.pairs {
        let offers = |session: &SessionType, position: usize| match session
            .protocol()
            .node(ProtocolState::from(position))
        {
            | Ok(&ProtocolNode::Offer(ref branches)) => Ok(Some(branches.len())),
            | Ok(_) => Ok(None),
            | Err(_) => Err(CheckRefusal::MachineInvariant),
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
/// for them, once the monitor of the run type `expected` accepts its
/// skeleton.
///
/// # Specification
/// - requires: `at` is a recorded run checked against `expected`.
/// - ensures: one premise per payload move, in move order, at the payload type
///   the protocol names at that move; none against the unknown type.
/// - fails: [`CheckRefusal::ShapeMismatch`] wanting a run type for any other
///   former; [`CheckRefusal::SessionCodeExpected`] at a protocol that is no
///   session code; [`CheckRefusal::RunNotAdmitted`] at `at` with the first move
///   the monitor refuses, or the incomplete run's length.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a complete seat run checks with its three payloads, a
///   paused run is refused at its pause and a truncated one at its end.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
/// - witness: `flow::tests::each_refusal_is_named`
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
    let protocol = match value_type_view(context.arena(), head)? {
        | ValueTypeView::Run(protocol) => protocol,
        | ValueTypeView::Unknown => return Ok(Vec::new()),
        | _ => {
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
    gandr_core_session::replay(&engine(&session)?, &skeleton(&moves))
        .map_err(|error| replay_refusal(at, &error))?;
    let mut premises = Vec::new();
    let mut current = session;
    for movement in moves.iter() {
        let next = match (current.step(), movement) {
            | (Ok(ProtocolStep::Send { payload, next }), &RecordedMove::Sent(value))
            | (Ok(ProtocolStep::Receive { payload, next }), &RecordedMove::Received(value)) => {
                premises.push((value, payload));
                next
            },
            | (Ok(ProtocolStep::Select(branches)), &RecordedMove::Selected(ref label))
            | (Ok(ProtocolStep::Offer(branches)), &RecordedMove::Offered(ref label)) => {
                match branches.get(label) {
                    | Ok(Maybe::Present(next)) => next,
                    | Ok(Maybe::Absent(_)) | Err(_) => return Err(CheckRefusal::MachineInvariant),
                }
            },
            | (Ok(ProtocolStep::End), &RecordedMove::Closed) => break,
            | _ => return Err(CheckRefusal::MachineInvariant),
        };
        current = next;
    }
    Ok(premises)
}

/// The engine's skeleton of a recorded run: every payload of one identity and
/// one opaque digest, every label as written.
///
/// # Specification
/// trivial.
fn skeleton(moves: &[RecordedMove]) -> Vec<Move>
{
    let payload = Payload {
        identity: gandr_core_session::ValueTypeId([0_u8; 32]),
        digest: PayloadDigest([0_u8; 32]),
    };
    moves
        .iter()
        .map(|movement| match *movement {
            | RecordedMove::Sent(_) => Move::Send(payload),
            | RecordedMove::Received(_) => Move::Receive(payload),
            | RecordedMove::Selected(ref label) => Move::Select(Label::from(label.as_ref())),
            | RecordedMove::Offered(ref label) => Move::Offer(Label::from(label.as_ref())),
            | RecordedMove::Closed => Move::End,
        })
        .collect()
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
/// - ensures: a refused move keeps its position and its kind — a wrong label, a
///   wrong direction, a move after the close; an incomplete run keeps its
///   length; a payload identity, which the skeleton never varies, and a broken
///   protocol are machine invariants.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a paused run and a truncated one name distinct faults.
/// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
#[spec(ensures: |ret| matches!(ret, CheckRefusal::RunNotAdmitted { at: site, .. } if site == at)
    || ret == CheckRefusal::MachineInvariant)]
fn replay_refusal(
    at: ValueId,
    error: &ReplayError,
) -> CheckRefusal
{
    let fault = match *error {
        | ReplayError::Refused {
            at: index, reason, ..
        } => match reason {
            | gandr_core_session::Refusal::WrongLabel => RunFault::WrongLabel(step(index)),
            | gandr_core_session::Refusal::WrongDirection => RunFault::WrongDirection(step(index)),
            | gandr_core_session::Refusal::ResumeAfterEnd => RunFault::ResumeAfterEnd(step(index)),
            | gandr_core_session::Refusal::WrongPayloadIdentity => {
                return CheckRefusal::MachineInvariant;
            },
        },
        | ReplayError::IncompleteRun { at: index, .. } => RunFault::Incomplete(step(index)),
        | ReplayError::InvalidType(_) => return CheckRefusal::MachineInvariant,
    };
    CheckRefusal::RunNotAdmitted { at, fault }
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
        | TransportError::Replay(ref replayed) => replay_refusal(at, replayed),
        | TransportError::Move {
            at: index,
            ref reason,
        } => {
            let fault = match *reason {
                | gandr_core_session::Refusal::WrongLabel => RunFault::WrongLabel(step(index)),
                | gandr_core_session::Refusal::WrongDirection => {
                    RunFault::WrongDirection(step(index))
                },
                | gandr_core_session::Refusal::ResumeAfterEnd => {
                    RunFault::ResumeAfterEnd(step(index))
                },
                | gandr_core_session::Refusal::WrongPayloadIdentity => {
                    return CheckRefusal::MachineInvariant;
                },
            };
            CheckRefusal::RunNotAdmitted { at, fault }
        },
        | TransportError::MissingPayload(_)
        | TransportError::CodeBinding
        | TransportError::Direction
        | TransportError::ExpectedSessionFlow
        | TransportError::Flow(_)
        | TransportError::Type(_)
        | TransportError::Session(_) => CheckRefusal::MachineInvariant,
    }
}
