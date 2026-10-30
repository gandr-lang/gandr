//! Total elaboration: the judgement's machine run so that a refusal marks the
//! term it stands at and the run goes on.
//!
//! # A refusal becomes a mark where it stands
//!
//! A strict run ends at its first refusal. A total run ends only at an engine
//! fault or the allowance: every other refusal is recorded against the term
//! under judgement and that term is given what its judgement would have
//! produced — checked, in checking position; the unknown type of its family,
//! in synthesis. The elaborated term wraps each marked node in a mark former
//! naming its entry, so every incomplete or ill-typed program comes out of
//! the run with a type and its errors located (Hazelnut, Omar et al., POPL
//! 2017, doi:10.1145/3009837.3009900; total type error localization and
//! recovery, Zhao et al., POPL 2024, doi:10.1145/3632910).
//!
//! # A run recovers at the innermost term under judgement
//!
//! Each value or computation goal the run descends into is an anchor: the
//! frame height, binder depth and record-field height it began at. A refusal
//! drops the frames, binders and field types the anchor's term had opened and
//! answers the anchor's goal in its place. A rule that refuses on resuming one
//! of its own frames is the anchor's own term, so the elimination that met a
//! wrong former is marked, not its operand. Formation goals are never anchors:
//! a malformed type marks the term whose rule asked for it.
//!
//! A rule refusing on its own frame marks the elimination where the marked
//! lambda calculus marks the operand.
//!
//! # A term that cannot synthesise is checked against the unknown type
//!
//! An introduction in synthesis position is marked and then checked against
//! the unknown type, so its parts are judged and their own errors located; it
//! synthesises the unknown type.
//!
//! # The strict judgement is the oracle
//!
//! A total run takes the strict run's steps until the strict run would refuse,
//! so it marks nothing exactly when the strict judgement accepts, and its
//! first mark carries the strict refusal. A mark stands on a node, so a node
//! shared by two positions is marked at both.
//!
//! A property test drives both runs over the free term generator. Total
//! elaboration is an entry beside the strict faces: `check_module` reports the
//! strict verdicts. The alternative was a marking `check_module`, which changes
//! every caller's verdicts; it is chosen when an editor face needs the marked
//! declarations in the module report. Witnesses:
//! `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`,
//! `judgement::elaboration::tests::a_term_that_cannot_synthesise_is_checked_against_the_unknown_type`,
//! `judgement::elaboration::tests::an_unfilled_hole_elaborates_to_a_type_and_evaluates_indeterminate`
//! and
//! `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`.
//!
//! A total run ends only at an engine fault or the allowance, so the failure
//! it hands back is the strict run's: the frames pending at that fault.
//!
//! # A typed run keeps the type of every term it judged
//!
//! A typed run anchors and recovers as a total run does, and as each term
//! judgement finishes it keeps the term with the type it was judged at: the
//! type it was checked against, or the type it synthesised — the unknown type
//! where its synthesis was marked. A term judged twice — checked, then
//! synthesised to cross a bridge — is kept twice, the inner judgement first.
//! As each type formation finishes it keeps the type with the level it formed
//! at, under the binders it was formed under. These are what a face shows for
//! a position inside the term: the editor's hover. No other run keeps them, so
//! a strict or total judgement pays nothing for them; a face that wants them
//! judges the declaration again in a typed run. The alternative was keeping
//! the type of every term in every run's report, which charges each judgement
//! of every revision for a table a face reads only at a hover. The choice
//! reverses when a face reads the table on every revision, as an inlay of
//! every binder's type would. Witness:
//! `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`.
//!
//! The record lives in the checking context, not in the machine: the context
//! records from the typed run's start to its finish, and every judgement run
//! inside it — a strict sub-judgement, a formation, a signature, a `ua`'s
//! translator records — keeps into the same log without knowing it. The
//! earlier design kept the record on the typed run's own machine, and every
//! nested run was a gap no hover could answer; a recording point per run
//! kind would have to be found again for each new judgement. Reversal: none
//! while a nested run can judge a term the source wrote.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Carried;
use gandr_core_term::ComputationId;
use gandr_core_term::FailureClass;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::hole::TermId;
use gandr_core_term::wrap_marks;
use gandr_kernel_strata::Level;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use crate::context::CheckingContext;
use crate::context::Recording;
use crate::conversion::ConversionCount;
use crate::failure::Failure;
use crate::formation::FormedCompType;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;

/// Whether a refusal ends a run or marks the term it stands at. Whether the
/// run keeps the type of each term it judges is the context's, not the
/// run's: every run inside a typed run keeps them.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Marking
{
    /// The first refusal ends the run.
    Strict,
    /// A refusal other than an engine fault marks the term under judgement.
    Total,
}

/// A term judgement under way in a total run, where a refusal is recovered.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Anchor
{
    /// The value or computation goal under way.
    goal: Goal,
    /// How many frames stood when the goal began.
    frames: usize,
    /// The binder depth the goal began at.
    depth: BinderDepth,
    /// How many inferred record-field types stood when the goal began.
    native: usize,
    /// Where the linear zone and the offers' zones stood when the goal
    /// began.
    sessions: super::session::Scope,
}

/// One refusal a total run marked, at the term it stands on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MarkEntry
{
    /// The marked term.
    at: TermId,
    /// The refusal the term's judgement gave.
    refusal: CheckRefusal,
}

impl MarkEntry
{
    /// The marked term, as it stood before elaboration wrapped it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(&self) -> TermId
    {
        self.at
    }

    /// The refusal the marked term's judgement gave.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refusal(&self) -> CheckRefusal
    {
        self.refusal
    }
}

/// A term judgement a typed run finished: the term, the type it was judged
/// at, and how many intuitionistic binders were open where it was judged.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Typing
{
    /// The term judged.
    pub term: TermNode,
    /// The type the term was checked against, or the type it synthesised.
    pub ty: TypeNode,
    /// The intuitionistic binders open where the judgement began: the context
    /// [`Self::ty`] is read under.
    pub depth: BinderDepth,
}

/// A type formation a typed run finished: the type and the level it formed
/// at, read under the binders it was formed under.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Formed
{
    /// The type formed.
    pub ty: TypeNode,
    /// The level it formed at.
    pub level: Level,
}

/// What a recording context kept: the term judgements, the type formations,
/// the endpoints' standings, the world register's moves, and the nodes the
/// kept types were copied to, each in the order finished.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Kept
{
    /// The term judgements finished.
    pub typings: Vec<Typing>,
    /// The type formations finished.
    pub formed: Vec<Formed>,
    /// The session type each action's endpoint stood at, keyed by the action.
    pub endpoints: Vec<Typing>,
    /// The world register's moves, in the order made.
    pub moves: Vec<crate::worlds::WorldMove>,
    /// Each node a kept type was copied to when it was settled, beside the
    /// node it copies, in the order minted.
    pub copies: Vec<Carried>,
}

/// A typed run's record of what it judged.
///
/// Every term judgement it finished, with its type; every type formation it
/// finished, with its level; the session type each action's endpoint stood
/// at; every move of the world register, with the linear zone around each
/// spent capability; the refusals it marked; and each value the value bridge
/// carried by a map between models, with the map.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Typings
{
    /// The term judgements finished, in the order finished: a term after
    /// every term inside it.
    judged: Vec<Typing>,
    /// The type formations finished, in the order finished.
    formed: Vec<Formed>,
    /// The session type each action's endpoint stood at, read where the
    /// action stands, keyed by the action, in the order met.
    endpoints: Vec<Typing>,
    /// The world register's moves, in the order made.
    moves: Vec<crate::worlds::WorldMove>,
    /// The refusals marked, in the order met.
    marks: Vec<MarkEntry>,
    /// Each value the value bridge carried by a map between models — a
    /// theory's reduct to one it includes, or a theory's forgetting map — by
    /// the value, with the map.
    crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
    /// Each node a kept type was copied to when it was settled, beside the
    /// node it copies, in the order minted: a variable's type read past the
    /// binders between it and its slot, among them.
    copies: Vec<Carried>,
}

impl Typings
{
    /// The term judgements finished, in the order finished: a term after
    /// every term inside it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn typings(&self) -> &[Typing]
    {
        &self.judged
    }

    /// The type formations finished, in the order finished, each at the
    /// level it formed at under the binders it was formed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn formed(&self) -> &[Formed]
    {
        &self.formed
    }

    /// The session type each action's endpoint stood at, read where the
    /// action stands and keyed by the action, in the order met.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn endpoints(&self) -> &[Typing]
    {
        &self.endpoints
    }

    /// The world register's moves, in the order made: each migration's spent
    /// capability, with the linear zone before and after, and its return.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn moves(&self) -> &[crate::worlds::WorldMove]
    {
        &self.moves
    }

    /// The refusals marked, in the order met.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn marks(&self) -> &[MarkEntry]
    {
        &self.marks
    }

    /// Each value the value bridge carried by a map between models, by the
    /// value, with the map: the reduct the checker applies where a model of
    /// a theory stands at a model of one it includes, or the forgetting map
    /// where a model with manifest sorts stands at its theory's models.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn crossings(&self) -> &BTreeMap<ValueId, gandr_core_term::Crossing>
    {
        &self.crossings
    }

    /// Each node a kept type was copied to when it was settled, beside the
    /// node it copies, in the order minted: a variable's type read past the
    /// binders between it and its slot, among them. A reader that names nodes
    /// by where the source writes them names each copy as its source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn copies(&self) -> &[Carried]
    {
        &self.copies
    }

    /// This record with `crossings`, the crossings the run that typed it
    /// recorded.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn crossed(
        mut self,
        crossings: BTreeMap<ValueId, gandr_core_term::Crossing>,
    ) -> Self
    {
        self.crossings = crossings;
        self
    }

    /// `body`'s record, after what `signature`'s formation kept: what a
    /// typed declaration keeps for its written type and its body, the type's
    /// first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the typings, the formations, the endpoints, the moves and the
    ///   copies are `signature`'s then `body`'s, in order; the marks and the
    ///   crossings are `body`'s.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration whose written type holds a path's
    ///   endpoints keeps them before its body's terms.
    /// - witness: `module::tests::a_typed_module_keeps_the_terms_its_signature_judges`
    #[spec(
        captures: [count = signature.typings.len().saturating_add(body.judged.len()), marked = body.marks.len()],
        ensures: |ret| ret.judged.len() == count && ret.marks.len() == marked,
    )]
    pub(crate) fn after(
        signature: Kept,
        body: Self,
    ) -> Self
    {
        let Kept {
            mut typings,
            mut formed,
            mut endpoints,
            mut moves,
            mut copies,
        } = signature;
        typings.extend(body.judged);
        formed.extend(body.formed);
        endpoints.extend(body.endpoints);
        moves.extend(body.moves);
        copies.extend(body.copies);
        Self {
            judged: typings,
            formed,
            endpoints,
            moves,
            marks: body.marks,
            crossings: body.crossings,
            copies,
        }
    }

    /// This record with each judgement's and each endpoint's type read through
    /// `retype`, given the binders it was recorded under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same judgements, formations, endpoints, moves and marks,
    ///   in order, each judgement's and endpoint's type replaced by what
    ///   `retype` answers for it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a body whose call omits an implicit keeps the type of
    ///   the call's head at the solved implicit.
    /// - witness: `module::tests::an_omitted_implicit_is_typed_at_its_solution_1216`
    #[spec(
        captures: [count = self.judged.len(), standing = self.endpoints.len()],
        ensures: |ret| ret.judged.len() == count && ret.endpoints.len() == standing,
    )]
    pub(crate) fn retyped(
        mut self,
        mut retype: impl FnMut(TypeNode, BinderDepth) -> TypeNode,
    ) -> Self
    {
        for typing in self.judged.iter_mut().chain(self.endpoints.iter_mut()) {
            typing.ty = retype(typing.ty, typing.depth);
        }
        self
    }
}

/// A total run's result: the term with its marks, its type and the marks'
/// refusals.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Elaboration<Term, Type>
{
    /// The elaborated term: the input with every marked node wrapped.
    root: Term,
    /// The type the run produced.
    produced: Type,
    /// The marks, indexed by the mark former's index.
    marks: Vec<MarkEntry>,
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl<Term: Copy, Type: Copy> Elaboration<Term, Type>
{
    /// The elaborated term; the input itself when nothing was marked.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> Term
    {
        self.root
    }

    /// The synthesised type, the unknown type where synthesis was marked, or
    /// the expected type of a check.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn produced(&self) -> Type
    {
        self.produced
    }

    /// The marks in the order met; a mark former's index names its entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn marks(&self) -> &[MarkEntry]
    {
        &self.marks
    }

    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// Elaborate `value` totally: judge it in `direction`, marking every refusal
/// short of an engine fault where it stands.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: the marks are empty exactly when the strict face of the same
///   direction accepts, and then the root is `value`; otherwise the first mark
///   carries the strict refusal and the root is `value` with each marked node
///   wrapped in a mark naming its entry.
/// - provides: the synthesised type (the unknown type where synthesis itself
///   was marked) or `expected`, and the conversions made.
/// - fails: engine faults only — the allowance, a dangling id, an unbound index
///   or a machine invariant.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — an engine fault; no source error is refused.
///
/// # Adequacy
/// - hypothesis: L3 — a check with one mismatching component, an introduction
///   in synthesis position with an ill-typed body, and the free generator
///   compared against the strict faces separate marking, recovery and the
///   oracle.
/// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
/// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
/// - witness: `judgement::elaboration::tests::an_unfilled_hole_elaborates_to_a_type_and_evaluates_indeterminate`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret.as_ref() {
        | Ok(elaboration) => elaboration.marks().iter().all(|mark| mark.refusal().classify() != FailureClass::EngineFault)
            && (!elaboration.marks().is_empty() || elaboration.root() == value),
        | Err(refusal) => refusal.classify() == FailureClass::EngineFault,
    },
)]
#[inline]
pub fn elaborate_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    direction: Direction<FormedValueType>,
) -> Result<Elaboration<ValueId, FormedValueType>, CheckRefusal>
{
    let (produced, conversions, marks) = Machine::execute(
        context,
        Goal::Value {
            term: value,
            direction: match direction {
                Direction::Synthesise => Direction::Synthesise,
                Direction::Check(expected) => Direction::Check(expected.id()),
            },
        },
        Marking::Total,
    )
    .map_err(|failure: Failure| failure.refusal())?;
    let produced = match (direction, produced) {
        (Direction::Synthesise, Produced::ValueType(found)) => {
            FormedValueType::derived(found.settle(context.arena_mut()))
        },
        (Direction::Check(expected), Produced::Checked) => expected,
        (Direction::Synthesise, Produced::CompType(_) | Produced::Checked)
        | (Direction::Check(_), Produced::ValueType(_) | Produced::CompType(_)) => {
            return Err(CheckRefusal::MachineInvariant);
        },
    };
    let root = match marked(context, TermId::Value(value), &marks)? {
        TermId::Value(root) => root,
        TermId::Computation(_) => return Err(CheckRefusal::MachineInvariant),
    };
    Ok(Elaboration {
        root,
        produced,
        marks,
        conversions,
    })
}

/// Elaborate `computation` totally: judge it in `direction`, marking every
/// refusal short of an engine fault where it stands.
///
/// # Specification
/// - requires: `computation` is closed over the context's binders, which are
///   empty between judgements.
/// - ensures: the marks are empty exactly when the strict face of the same
///   direction accepts, and then the root is `computation`; otherwise the first
///   mark carries the strict refusal and the root is `computation` with each
///   marked node wrapped in a mark naming its entry.
/// - provides: the synthesised type (the unknown type where synthesis itself
///   was marked) or `expected`, and the conversions made.
/// - fails: engine faults only — the allowance, a dangling id, an unbound index
///   or a machine invariant.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — an engine fault; no source error is refused.
///
/// # Adequacy
/// - hypothesis: L3 — as for [`elaborate_value`], over computations: a lambda
///   in synthesis position with an ill-typed body is marked at both.
/// - witness: `judgement::elaboration::tests::a_term_that_cannot_synthesise_is_checked_against_the_unknown_type`
/// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret.as_ref() {
        | Ok(elaboration) => elaboration.marks().iter().all(|mark| mark.refusal().classify() != FailureClass::EngineFault)
            && (!elaboration.marks().is_empty() || elaboration.root() == computation),
        | Err(refusal) => refusal.classify() == FailureClass::EngineFault,
    },
)]
#[inline]
pub fn elaborate_comp(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
    direction: Direction<FormedCompType>,
) -> Result<Elaboration<ComputationId, FormedCompType>, CheckRefusal>
{
    let (produced, conversions, marks) = Machine::execute(
        context,
        Goal::Computation {
            term: computation,
            direction: match direction {
                Direction::Synthesise => Direction::Synthesise,
                Direction::Check(expected) => Direction::Check(expected.id()),
            },
        },
        Marking::Total,
    )
    .map_err(|failure: Failure| failure.refusal())?;
    let produced = match (direction, produced) {
        (Direction::Synthesise, Produced::CompType(found)) => FormedCompType::derived(found),
        (Direction::Check(expected), Produced::Checked) => expected,
        (Direction::Synthesise, Produced::ValueType(_) | Produced::Checked)
        | (Direction::Check(_), Produced::ValueType(_) | Produced::CompType(_)) => {
            return Err(CheckRefusal::MachineInvariant);
        },
    };
    let root = match marked(context, TermId::Computation(computation), &marks)? {
        TermId::Computation(root) => root,
        TermId::Value(_) => return Err(CheckRefusal::MachineInvariant),
    };
    Ok(Elaboration {
        root,
        produced,
        marks,
        conversions,
    })
}

/// Every term judgement the judgement of `value` in `direction` finishes, with
/// the type it was judged at, and the refusals it marks.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: the binders stand where they stood; the run anchors and recovers
///   as [`elaborate_value`]'s does, and keeps one entry each time a value or
///   computation judgement finishes — recovered or not — in the order finished,
///   with the type it was checked against or the type it synthesised, and one
///   for a computation nested where no thunk stands, which is no judgement of
///   its own, at what it returns, when its run ends; `value`'s own judgement is
///   the last entry when the run reaches its end. The marks are the total
///   run's. An engine fault ends the run with what it kept so far.
/// - provides: the type of every term a declaration's body judges, for a face
///   answering a position inside it.
/// - fails: never; an engine fault cuts the record short.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an accepted application, a checked pair with an ill-typed
///   component and a variable read under a binder separate the synthesised and
///   checked types, the inner-first order, the recovered judgement and the type
///   a variable occurrence reads.
/// - witness: `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`
/// - witness: `module::tests::a_computation_written_as_a_scrutinee_runs_1141`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.marks().iter().all(|mark| mark.refusal().classify() != FailureClass::EngineFault),
)]
#[inline]
#[must_use]
pub fn type_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    direction: Direction<FormedValueType>,
) -> Typings
{
    let entry = context.binders().depth(Zone::Intuitionistic);
    let base = context.depth(Zone::Linear);
    let remaining = usize::from(context.budget());
    let goal = Goal::Value {
        term: value,
        direction: match direction {
            Direction::Synthesise => Direction::Synthesise,
            Direction::Check(expected) => Direction::Check(expected.id()),
        },
    };
    let outer = context.start_typings();
    let abstracted = super::abstracted_by(context.arena(), goal);
    let mut machine = Machine {
        context,
        frames: Vec::new(),
        owner: goal,
        native_types: Vec::new(),
        conversions: ConversionCount::default(),
        remaining,
        marking: Marking::Total,
        anchors: Vec::new(),
        marks: Vec::new(),
        sessions: super::Sessions::new(base, abstracted),
        root: quenchant_shape::shape::Maybe::Absent(crate::respect::root::Absent::Unmarked),
        staged_motives: Vec::new(),
        images: super::worlds::Images::default(),
    };
    let register = machine.context.binders().world();
    let scope = machine.session_scope();
    let _entered = machine.open_entry();
    let _outcome = machine.drive(goal);
    machine.unwind(entry);
    machine.close_sessions(scope);
    let _moved = machine.context.binders().relocate(register);
    let marks = machine.marks;
    let Kept {
        typings,
        formed,
        endpoints,
        moves,
        copies,
    } = context.finish_typings(outer);
    Typings {
        judged: typings,
        formed,
        endpoints,
        moves,
        marks,
        crossings: BTreeMap::new(),
        copies,
    }
}

/// Wrap every marked node beneath `root` in a mark naming its first entry.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `root` itself when `marks` is empty; otherwise the rewrite of
///   `root` with each marked node wrapped once, in `root`'s family.
/// - fails: [`CheckRefusal::MachineInvariant`] when the marks outnumber the
///   mark index.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal::MachineInvariant`] — more marks than an index names.
///
/// # Adequacy
/// - hypothesis: L3 — no marks, one mark and a term marked twice separate the
///   identity, the wrapping and the first-entry choice.
/// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
/// - witness: `judgement::elaboration::tests::a_term_that_cannot_synthesise_is_checked_against_the_unknown_type`
#[spec(ensures: |ret| !marks.is_empty() || ret == Ok(root))]
fn marked(
    context: &mut CheckingContext<'_>,
    root: TermId,
    marks: &[MarkEntry],
) -> Result<TermId, CheckRefusal>
{
    if marks.is_empty() {
        return Ok(root);
    }
    let mut sites = BTreeMap::new();
    for (index, entry) in marks.iter().enumerate() {
        let index = u32::try_from(index).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        sites
            .entry(entry.at)
            .or_insert_with(|| MarkIndex::from(index));
    }
    Ok(wrap_marks(context.arena_mut(), root, &sites))
}

impl Machine<'_, '_>
{
    /// Record a term goal as where a total run recovers, and, in any run while
    /// the context records typings, a term goal, or a formation goal the
    /// context keeps, as where its judgement finishes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a value or computation goal in a total run or while the
    ///   context records, and a formation goal while it records that formation,
    ///   is pushed with the frame height, binder depth and field-type height it
    ///   began at; nothing changes otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict run, a total run and a formation goal
    ///   separate the three answers; a wrong height recovers at the wrong term
    ///   and changes the marks.
    /// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
    /// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
    #[spec(
        captures: before = self.anchors.len(),
        ensures: self.anchors.len() == before.saturating_add(usize::from(match goal {
            Goal::Value { .. } | Goal::Computation { .. } =>
                self.marking == Marking::Total || self.context.recording() == Recording::On,
            Goal::Form(ty) => self.context.forming(ty) == Recording::On,
            Goal::Stack { .. } => false,
        })),
    )]
    pub(super) fn anchor(
        &mut self,
        goal: Goal,
    )
    {
        let recording = self.context.recording() == Recording::On;
        let anchored = match goal {
            Goal::Value { .. } | Goal::Computation { .. } => {
                self.marking == Marking::Total || recording
            },
            Goal::Form(ty) => self.context.forming(ty) == Recording::On,
            Goal::Stack { .. } => false,
        };
        if anchored {
            let depth = self.context.depth(Zone::Intuitionistic);
            let sessions = self.session_scope();
            self.anchors.push(Anchor {
                goal,
                frames: self.frames.len(),
                depth,
                native: self.native_types.len(),
                sessions,
            });
        }
    }

    /// Retire the anchors of every goal the ascent finished, `produced` the
    /// result each finished with; while the context records typings, each
    /// one's type is kept.
    ///
    /// # Specification
    /// - requires: `produced` is the result the ascent hands up.
    /// - ensures: every anchor left began below the current frame height; each
    ///   anchor retired is kept as [`Self::keep`] keeps it, innermost first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finished goal whose anchor stayed would take the
    ///   next recovery away from its parent; the oracle property recovers after
    ///   finished siblings. Anchors are pushed in nesting order, so their frame
    ///   heights rise toward the top of the stack and the predicate reads only
    ///   the top anchor.
    /// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
    /// - witness: `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`
    #[spec(ensures: self.anchors.last().is_none_or(|anchor| anchor.frames < self.frames.len()))]
    pub(super) fn settle(
        &mut self,
        produced: Produced,
    )
    {
        let height = self.frames.len();
        while let Some(&anchor) = self.anchors.last().filter(|anchor| anchor.frames >= height) {
            self.anchors.pop();
            self.keep(anchor, produced);
        }
    }

    /// While the context records typings, keep `anchor`'s term with the type
    /// it finished at — `produced` for a synthesis, the expected type for a
    /// check — and the binder depth its goal began at.
    ///
    /// # Specification
    /// - ensures: while the context records, a value or computation goal
    ///   checked against a type is kept with that type, and one synthesised is
    ///   kept with the type it produced in its own family, each at the depth
    ///   the goal began at, every node settling the produced type mints kept
    ///   beside the node it copies; nothing is kept for any other goal or
    ///   result, or while the context does not record.
    /// - panics: none.
    /// - executable: none — the context's log has no observer short of the
    ///   typed run's result, which the witness reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checked and a synthesised judgement, and a strict
    ///   run of the same term, separate the expected side, the produced side
    ///   and the empty record; a term judged under its binders and again under
    ///   more separates the depths.
    /// - witness: `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`
    fn keep(
        &mut self,
        anchor: Anchor,
        produced: Produced,
    )
    {
        if self.context.recording() == Recording::Off {
            return;
        }
        let depth = anchor.depth;
        let typing = match (anchor.goal, produced) {
            (
                Goal::Value {
                    term,
                    direction: Direction::Check(expected),
                },
                _,
            ) => Typing {
                term: TermNode::Value(term),
                ty: TypeNode::Value(expected),
                depth,
            },
            (
                Goal::Computation {
                    term,
                    direction: Direction::Check(expected),
                },
                _,
            ) => Typing {
                term: TermNode::Computation(term),
                ty: TypeNode::Computation(expected),
                depth,
            },
            (
                Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                },
                Produced::ValueType(found),
            ) => Typing {
                term: TermNode::Value(term),
                ty: TypeNode::Value(self.context.settle_value_type(found)),
                depth,
            },
            (
                Goal::Computation {
                    term,
                    direction: Direction::Synthesise,
                },
                Produced::CompType(found),
            ) => Typing {
                term: TermNode::Computation(term),
                ty: TypeNode::Computation(found),
                depth,
            },
            (
                Goal::Value {
                    direction: Direction::Synthesise,
                    ..
                },
                Produced::CompType(_) | Produced::Checked,
            )
            | (
                Goal::Computation {
                    direction: Direction::Synthesise,
                    ..
                },
                Produced::ValueType(_) | Produced::Checked,
            )
            | (Goal::Stack { .. }, _) => return,
            (Goal::Form(node), _) => {
                self.context.keep_formed(node);
                return;
            },
        };
        self.context.keep_typing(typing);
    }

    /// Answer a refusal: end a strict run, or mark the innermost term under
    /// judgement and give its goal the answer its judgement would have made.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a strict run, an engine fault or a run with no anchor is
    ///   refused with `refusal` unchanged; otherwise the innermost anchor is
    ///   retired, the frames, binders, field types and forming thunk images
    ///   fall back to where its goal began, one mark is recorded at its term,
    ///   the goal is the running one again, and it is answered — checked, the
    ///   unknown type, or, for a term that cannot synthesise, a check against
    ///   the unknown type. While the context records typings, an answered goal
    ///   is kept as [`Self::keep`] keeps it.
    /// - fails: `refusal` itself, as above.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — `refusal`, when the run cannot go on.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict run, a check-position refusal, a
    ///   synthesis-position shape refusal and an introduction in synthesis
    ///   position separate the four answers.
    /// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
    /// - witness: `judgement::elaboration::tests::a_term_that_cannot_synthesise_is_checked_against_the_unknown_type`
    /// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
    /// - witness: `judgement::elaboration::tests::a_typed_run_keeps_the_type_of_every_term_it_judged`
    #[spec(
        captures: before = self.marks.len(),
        ensures: |ret| match ret {
            | Ok(_) => self.marks.len() == before.saturating_add(1),
            | Err(returned) => returned == refusal && self.marks.len() == before,
        },
    )]
    pub(super) fn recover(
        &mut self,
        refusal: CheckRefusal,
    ) -> Result<Step, CheckRefusal>
    {
        let recoverable = match (self.marking, refusal.classify()) {
            (Marking::Strict, _) | (Marking::Total, FailureClass::EngineFault) => false,
            (
                Marking::Total,
                FailureClass::MalformedSource
                | FailureClass::Unimplemented(_)
                | FailureClass::UserAbsence,
            ) => true,
        };
        if !recoverable {
            return Err(refusal);
        }
        let anchor = loop {
            let Some(anchor) = self.anchors.pop()
            else {
                return Err(refusal);
            };
            if let Goal::Value { .. } | Goal::Computation { .. } = anchor.goal {
                break anchor;
            }
        };
        // A migration the recovery drops puts the register back where the
        // outermost of them found it.
        if let Some(from) = self.frames.get(anchor.frames ..).and_then(|dropped| {
            dropped.iter().find_map(|waiting| {
                if let super::Frame::MigrateBody { from, .. } = waiting.frame {
                    Some(from)
                }
                else {
                    None
                }
            })
        }) {
            let _moved = self.context.binders().relocate(from);
        }
        self.frames.truncate(anchor.frames);
        self.abandon_forming();
        self.native_types.truncate(anchor.native);
        self.unwind(anchor.depth);
        self.close_sessions(anchor.sessions);
        self.owner = anchor.goal;
        let (at, node) = match anchor.goal {
            Goal::Value { term, .. } => (TermId::Value(term), TermNode::Value(term)),
            Goal::Computation { term, .. } => {
                (TermId::Computation(term), TermNode::Computation(term))
            },
            Goal::Form(_) | Goal::Stack { .. } => return Err(CheckRefusal::MachineInvariant),
        };
        self.marks.push(MarkEntry { at, refusal });
        let unsynthesisable = matches!(refusal, CheckRefusal::NotSynthesisable { .. });
        let step = match anchor.goal {
            Goal::Value {
                direction: Direction::Check(_),
                ..
            }
            | Goal::Computation {
                direction: Direction::Check(_),
                ..
            } => Ok(Step::Ascend(Produced::Checked)),
            Goal::Value {
                term,
                direction: Direction::Synthesise,
            } => {
                let unknown = self.context.arena_mut().value_type_unknown();
                if unsynthesisable {
                    self.wait(Frame::Unknowing(node));
                    Ok(Step::Descend(Goal::Value {
                        term,
                        direction: Direction::Check(unknown),
                    }))
                }
                else {
                    Ok(Step::Ascend(Produced::ValueType(unknown.into())))
                }
            },
            Goal::Computation {
                term,
                direction: Direction::Synthesise,
            } => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                if unsynthesisable {
                    self.wait(Frame::Unknowing(node));
                    Ok(Step::Descend(Goal::Computation {
                        term,
                        direction: Direction::Check(unknown),
                    }))
                }
                else {
                    Ok(Step::Ascend(Produced::CompType(unknown)))
                }
            },
            Goal::Form(_) | Goal::Stack { .. } => Err(CheckRefusal::MachineInvariant),
        };
        if let Ok(Step::Ascend(produced)) = step {
            self.keep(anchor, produced);
        }
        step
    }
}

#[cfg(test)]
mod tests;
