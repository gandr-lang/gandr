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
//! # A traced run keeps the judgements a refusal stood in
//!
//! A traced run anchors every term goal as a total run does and refuses as a
//! strict run does, so at its refusal the anchors still standing are the
//! value and computation judgements the refusal stood inside, outermost first.
//! They are the nested reasons a face renders beside the refusal: the
//! enclosing terms and the types they were checked against. The strict run
//! keeps no anchors, so a refused declaration is traced again rather than
//! every judgement paying for the trail; the trace is deterministic, so it
//! meets the refusal the strict run met.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::ComputationId;
use gandr_core_term::FailureClass;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::hole::TermId;
use gandr_core_term::wrap_marks;
use quenchant_shape::shape::Maybe;

use super::Direction;
use super::Frame;
use super::Goal;
use super::Machine;
use super::Produced;
use super::Step;
use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::formation::FormedCompType;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;

/// Whether a refusal ends a run or marks the term it stands at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Marking
{
    /// The first refusal ends the run.
    Strict,
    /// A refusal other than an engine fault marks the term under judgement.
    Total,
    /// The first refusal ends the run, with the term judgements it stood
    /// inside still anchored.
    Traced,
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

quenchant_shape::reason_enum! {
    /// Why a judgement under way was checked against no type.
    pub mod pending {
        /// The reason the expected type is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The judgement synthesised its term's type.
            Synthesised,
        }
    }
}

/// A term judgement under way when a refusal was met: the term and the type it
/// was checked against.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pending
{
    /// The term under judgement.
    pub term: TermNode,
    /// The type the term was checked against; absent when it was synthesised.
    pub expected: Maybe<TypeNode, pending::Absent>,
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
                | Direction::Synthesise => Direction::Synthesise,
                | Direction::Check(expected) => Direction::Check(expected.id()),
            },
        },
        Marking::Total,
    )?;
    let produced = match (direction, produced) {
        | (Direction::Synthesise, Produced::ValueType(found)) => FormedValueType::derived(found),
        | (Direction::Check(expected), Produced::Checked) => expected,
        | (Direction::Synthesise, Produced::CompType(_) | Produced::Checked)
        | (Direction::Check(_), Produced::ValueType(_) | Produced::CompType(_)) => {
            return Err(CheckRefusal::MachineInvariant);
        },
    };
    let root = match marked(context, TermId::Value(value), &marks)? {
        | TermId::Value(root) => root,
        | TermId::Computation(_) => return Err(CheckRefusal::MachineInvariant),
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
                | Direction::Synthesise => Direction::Synthesise,
                | Direction::Check(expected) => Direction::Check(expected.id()),
            },
        },
        Marking::Total,
    )?;
    let produced = match (direction, produced) {
        | (Direction::Synthesise, Produced::CompType(found)) => FormedCompType::derived(found),
        | (Direction::Check(expected), Produced::Checked) => expected,
        | (Direction::Synthesise, Produced::ValueType(_) | Produced::Checked)
        | (Direction::Check(_), Produced::ValueType(_) | Produced::CompType(_)) => {
            return Err(CheckRefusal::MachineInvariant);
        },
    };
    let root = match marked(context, TermId::Computation(computation), &marks)? {
        | TermId::Computation(root) => root,
        | TermId::Value(_) => return Err(CheckRefusal::MachineInvariant),
    };
    Ok(Elaboration {
        root,
        produced,
        marks,
        conversions,
    })
}

/// The term judgements under way when the strict judgement of `value` in
/// `direction` refuses, outermost first.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: the binders stand where they stood; nothing when the strict
///   judgement accepts; otherwise one entry per value and computation judgement
///   the refusal stood inside, outermost first and `value` itself first, a term
///   judged twice in a row (checked, then synthesised to cross a bridge)
///   entered once, at its outer judgement.
/// - provides: the nested reasons a face renders beside the strict refusal.
/// - fails: never; an engine fault is traced as any refusal is.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an accepted term, a pair and a thunk each checked and
///   refused one judgement deep, and a pair synthesised and refused at its
///   component, separate the empty trail, the outermost-first order, the
///   expected and synthesised sides and the collapsed bridge.
/// - witness: `judgement::elaboration::tests::a_traced_run_keeps_the_judgements_a_refusal_stood_in`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.first().is_none_or(|first| first.term == TermNode::Value(value))
        && ret.iter().zip(ret.iter().skip(1)).all(|(outer, inner)| outer.term != inner.term),
)]
#[inline]
#[must_use]
pub fn trace_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    direction: Direction<FormedValueType>,
) -> Vec<Pending>
{
    let entry = context.binders().depth(Zone::Intuitionistic);
    let remaining = usize::from(context.budget());
    let mut machine = Machine {
        context,
        frames: Vec::new(),
        native_types: Vec::new(),
        conversions: ConversionCount::default(),
        remaining,
        marking: Marking::Traced,
        anchors: Vec::new(),
        marks: Vec::new(),
    };
    let outcome = machine.drive(Goal::Value {
        term: value,
        direction: match direction {
            | Direction::Synthesise => Direction::Synthesise,
            | Direction::Check(expected) => Direction::Check(expected.id()),
        },
    });
    machine.unwind(entry);
    match outcome {
        | Ok(_) => Vec::new(),
        | Err(_) => trail(&machine.anchors),
    }
}

/// The term judgements `anchors` stand for, outermost first, a term anchored
/// twice in a row entered once.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per value or computation anchor, in order, except an
///   anchor on the same term as the entry before it; each entry carries the
///   anchor's term and the type it was checked against, absent when it was
///   synthesised.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a bridged term anchored as a check and then as a
///   synthesis, beside terms anchored once in each direction, separates the
///   collapse, the order and the expected side.
/// - witness: `judgement::elaboration::tests::a_traced_run_keeps_the_judgements_a_refusal_stood_in`
#[spec(ensures: |ret| ret.len() <= anchors.len()
    && ret.iter().zip(ret.iter().skip(1)).all(|(outer, inner)| outer.term != inner.term))]
fn trail(anchors: &[Anchor]) -> Vec<Pending>
{
    let mut trail: Vec<Pending> = Vec::with_capacity(anchors.len());
    for anchor in anchors {
        let pending = match anchor.goal {
            | Goal::Value { term, direction } => Pending {
                term: TermNode::Value(term),
                expected: match direction {
                    | Direction::Check(expected) => Maybe::Present(TypeNode::Value(expected)),
                    | Direction::Synthesise => Maybe::Absent(pending::Absent::Synthesised),
                },
            },
            | Goal::Computation { term, direction } => Pending {
                term: TermNode::Computation(term),
                expected: match direction {
                    | Direction::Check(expected) => Maybe::Present(TypeNode::Computation(expected)),
                    | Direction::Synthesise => Maybe::Absent(pending::Absent::Synthesised),
                },
            },
            | Goal::Form(_) | Goal::Stack { .. } => continue,
        };
        if trail.last().is_some_and(|outer| outer.term == pending.term) {
            continue;
        }
        trail.push(pending);
    }
    trail
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
    /// Record a term goal as where a total run recovers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: in a total or traced run, a value or computation goal is
    ///   pushed with the frame height, binder depth and field-type height it
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
        ensures: self.anchors.len() == before.saturating_add(usize::from(
            self.marking != Marking::Strict && !matches!(goal, Goal::Form(_) | Goal::Stack { .. }),
        )),
    )]
    pub(super) fn anchor(
        &mut self,
        goal: Goal,
    )
    {
        match (self.marking, goal) {
            | (Marking::Total | Marking::Traced, Goal::Value { .. } | Goal::Computation { .. }) => {
                let depth = self.context.depth(Zone::Intuitionistic);
                self.anchors.push(Anchor {
                    goal,
                    frames: self.frames.len(),
                    depth,
                    native: self.native_types.len(),
                });
            },
            | (Marking::Strict, _)
            | (Marking::Total | Marking::Traced, Goal::Form(_) | Goal::Stack { .. }) => {},
        }
    }

    /// Retire the anchors of every goal the ascent finished.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every anchor left began below the current frame height.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finished goal whose anchor stayed would take the
    ///   next recovery away from its parent; the oracle property recovers after
    ///   finished siblings.
    /// - witness: `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`
    #[spec(ensures: self.anchors.iter().all(|anchor| anchor.frames < self.frames.len()))]
    pub(super) fn settle(&mut self)
    {
        let height = self.frames.len();
        while self
            .anchors
            .last()
            .is_some_and(|anchor| anchor.frames >= height)
        {
            self.anchors.pop();
        }
    }

    /// Answer a refusal: end a strict run, or mark the innermost term under
    /// judgement and give its goal the answer its judgement would have made.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a strict or traced run, an engine fault or a run with no
    ///   anchor is refused with `refusal` unchanged; otherwise the innermost
    ///   anchor is retired, the frames, binders and field types fall back to
    ///   where its goal began, one mark is recorded at its term, and its goal
    ///   is answered — checked, the unknown type, or, for a term that cannot
    ///   synthesise, a check against the unknown type.
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
            | (Marking::Strict | Marking::Traced, _)
            | (Marking::Total, FailureClass::EngineFault) => false,
            | (
                Marking::Total,
                FailureClass::MalformedSource
                | FailureClass::Unrepresentable
                | FailureClass::UserAbsence,
            ) => true,
        };
        if !recoverable {
            return Err(refusal);
        }
        let Some(anchor) = self.anchors.pop()
        else {
            return Err(refusal);
        };
        self.frames.truncate(anchor.frames);
        self.native_types.truncate(anchor.native);
        self.unwind(anchor.depth);
        let (at, node) = match anchor.goal {
            | Goal::Value { term, .. } => (TermId::Value(term), TermNode::Value(term)),
            | Goal::Computation { term, .. } => {
                (TermId::Computation(term), TermNode::Computation(term))
            },
            | Goal::Form(_) | Goal::Stack { .. } => return Err(CheckRefusal::MachineInvariant),
        };
        self.marks.push(MarkEntry { at, refusal });
        let unsynthesisable = matches!(refusal, CheckRefusal::NotSynthesisable { .. });
        match anchor.goal {
            | Goal::Value {
                direction: Direction::Check(_),
                ..
            }
            | Goal::Computation {
                direction: Direction::Check(_),
                ..
            } => Ok(Step::Ascend(Produced::Checked)),
            | Goal::Value {
                term,
                direction: Direction::Synthesise,
            } => {
                let unknown = self.context.arena_mut().value_type_unknown();
                if unsynthesisable {
                    self.frames.push(Frame::Unknowing(node));
                    Ok(Step::Descend(Goal::Value {
                        term,
                        direction: Direction::Check(unknown),
                    }))
                }
                else {
                    Ok(Step::Ascend(Produced::ValueType(unknown)))
                }
            },
            | Goal::Computation {
                term,
                direction: Direction::Synthesise,
            } => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                if unsynthesisable {
                    self.frames.push(Frame::Unknowing(node));
                    Ok(Step::Descend(Goal::Computation {
                        term,
                        direction: Direction::Check(unknown),
                    }))
                }
                else {
                    Ok(Step::Ascend(Produced::CompType(unknown)))
                }
            },
            | Goal::Form(_) | Goal::Stack { .. } => Err(CheckRefusal::MachineInvariant),
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_nbe::Definitions;
    use gandr_core_nbe::DomainArena;
    use gandr_core_nbe::DomainValue;
    use gandr_core_nbe::Fuel;
    use gandr_core_nbe::LoweredChain;
    use gandr_core_nbe::NeutralHead;
    use gandr_core_nbe::eval_value;
    use gandr_core_term::CompType;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::MarkIndex;
    use gandr_core_term::hole::TermId;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use quenchant_shape::shape::Maybe;

    use super::MarkEntry;
    use super::Pending;
    use super::elaborate_comp;
    use super::elaborate_value;
    use super::pending;
    use super::trace_value;
    use crate::CheckBudget;
    use crate::CheckingContext;
    use crate::Declaration;
    use crate::OriginToken;
    use crate::Verdict;
    use crate::check_module;
    use crate::fixture::integer_literal;
    use crate::fixture::seed;
    use crate::fixture::term_recipe;
    use crate::fixture::type_recipe;
    use crate::formation::form_comp_type;
    use crate::formation::form_value_type;
    use crate::judgement::Direction;
    use crate::judgement::check_comp;
    use crate::judgement::check_value;
    use crate::judgement::synthesise_comp;
    use crate::judgement::synthesise_value;
    use crate::refusal::CheckRefusal;
    use crate::refusal::TermNode;
    use crate::refusal::TypeNode;
    use crate::signature;

    #[test]
    fn a_total_run_marks_where_a_strict_run_refuses()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(&[integer, integer]);
        let zero = arena.value_literal(integer_literal());
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[zero, unit]);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_value_type(&mut context, product).unwrap();

        let strict = check_value(&mut context, pair, expected).unwrap_err();
        let elaboration = elaborate_value(&mut context, pair, Direction::Check(expected)).unwrap();
        assert_eq!(
            elaboration.marks(),
            [MarkEntry {
                at: TermId::Value(unit),
                refusal: strict,
            }],
            "the unit is marked with the strict refusal, and the run goes on"
        );
        assert_eq!(
            elaboration.produced(),
            expected,
            "a check produces its expected type"
        );
        let Some(&[first, second]) = context
            .arena()
            .value(elaboration.root())
            .and_then(Value::components)
        else {
            panic!("the elaborated root is still the pair");
        };
        assert_eq!(first, zero, "the well-typed component is untouched");
        assert_eq!(
            context.arena().value(second),
            Some(&Value::Mark {
                mark: MarkIndex::from(0_u32),
                body: unit,
            }),
            "the mismatched component is wrapped in the first mark"
        );
        assert!(
            check_value(&mut context, elaboration.root(), expected).is_ok(),
            "the marked term is well typed"
        );
    }

    #[test]
    fn a_traced_run_keeps_the_judgements_a_refusal_stood_in()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(&[integer, integer]);
        let zero = arena.value_literal(integer_literal());
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[zero, unit]);
        let forced = arena.computation_force(zero);
        let thunk = arena.value_thunk(forced);
        let unsynthesisable = arena.value_tuple(&[zero, thunk]);
        let returns_integer = arena.comp_type_returner(integer);
        let suspended = arena.value_type_thunk(returns_integer);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = form_value_type(&mut context, product).unwrap();
        let formed_integer = form_value_type(&mut context, integer).unwrap();
        let formed_suspended = form_value_type(&mut context, suspended).unwrap();
        let depth = context.depth(Zone::Intuitionistic);

        assert_eq!(
            trace_value(&mut context, zero, Direction::Check(formed_integer)),
            Vec::new(),
            "an accepted judgement leaves no trail"
        );
        let checked = trace_value(&mut context, pair, Direction::Check(expected));
        let &[outer, inner] = checked.as_slice()
        else {
            panic!("the pair and its mismatched component, the bridge collapsed: {checked:?}");
        };
        assert_eq!(
            outer,
            Pending {
                term: TermNode::Value(pair),
                expected: Maybe::Present(TypeNode::Value(expected.id())),
            },
            "the outermost judgement comes first, at the type it was checked against"
        );
        assert_eq!(
            inner.term,
            TermNode::Value(unit),
            "the component comes last"
        );
        assert!(
            matches!(inner.expected, Maybe::Present(TypeNode::Value(_))),
            "the component was checked against its factor"
        );
        let forcing = trace_value(&mut context, thunk, Direction::Check(formed_suspended));
        let &[outer, inner] = forcing.as_slice()
        else {
            panic!("the thunk and the force inside it, the bridge collapsed: {forcing:?}");
        };
        assert_eq!(
            outer,
            Pending {
                term: TermNode::Value(thunk),
                expected: Maybe::Present(TypeNode::Value(formed_suspended.id())),
            },
            "the thunk was checked against its declared type"
        );
        assert_eq!(
            inner.term,
            TermNode::Computation(forced),
            "a force of an integer stands inside the thunk; the integer finished"
        );
        assert!(
            matches!(inner.expected, Maybe::Present(TypeNode::Computation(_))),
            "the body was checked against the thunk's computation type"
        );
        let synthesised = Maybe::Absent(pending::Absent::Synthesised);
        assert_eq!(
            trace_value(&mut context, unsynthesisable, Direction::Synthesise),
            [
                Pending {
                    term: TermNode::Value(unsynthesisable),
                    expected: synthesised,
                },
                Pending {
                    term: TermNode::Value(thunk),
                    expected: synthesised,
                },
            ],
            "a thunk cannot synthesise, and stands inside the synthesised pair"
        );
        assert_eq!(
            context.depth(Zone::Intuitionistic),
            depth,
            "the trace leaves the binders as found"
        );
    }

    #[test]
    fn a_term_that_cannot_synthesise_is_checked_against_the_unknown_type()
    {
        let mut arena = CoreArena::new();
        let zero = arena.value_literal(integer_literal());
        let forced = arena.computation_force(zero);
        let lambda = arena.computation_lambda(forced);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

        let strict = synthesise_comp(&mut context, lambda).unwrap_err();
        let elaboration = elaborate_comp(&mut context, lambda, Direction::Synthesise).unwrap();
        assert_eq!(
            context.arena().comp_type(elaboration.produced().id()),
            Some(&CompType::Unknown),
            "a marked synthesis produces the unknown type"
        );
        let &[lambda_mark, force_mark] = elaboration.marks()
        else {
            panic!("the lambda and the force inside it are both marked");
        };
        assert_eq!(
            lambda_mark,
            MarkEntry {
                at: TermId::Computation(lambda),
                refusal: strict,
            },
            "the lambda is marked first, with the strict refusal"
        );
        assert_eq!(
            force_mark.at(),
            TermId::Computation(forced),
            "the body is judged against the unknown arrow and its force is marked"
        );
        assert!(
            matches!(force_mark.refusal(), CheckRefusal::ShapeMismatch { .. }),
            "a force of an integer is a shape mismatch"
        );
        let Some(&Computation::Mark { mark, body }) =
            context.arena().computation(elaboration.root())
        else {
            panic!("the root is marked");
        };
        assert_eq!(mark, MarkIndex::from(0_u32));
        let Some(&Computation::Lambda(inner)) = context.arena().computation(body)
        else {
            panic!("the mark wraps the lambda");
        };
        assert_eq!(
            context.arena().computation(inner),
            Some(&Computation::Mark {
                mark: MarkIndex::from(1_u32),
                body: forced,
            }),
            "the force inside is wrapped in the second mark"
        );
        assert!(
            synthesise_comp(&mut context, elaboration.root()).is_ok(),
            "the marked term synthesises"
        );
    }

    #[test]
    fn an_unfilled_hole_elaborates_to_a_type_and_evaluates_indeterminate()
    {
        let mut arena = CoreArena::new();
        let hole = HoleId::from(0_u32);
        let standing = arena.value_hole(hole);
        let zero = arena.value_literal(integer_literal());
        let program = arena.value_tuple(&[standing, zero]);
        let declarations = [Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(program),
            OriginToken::from(0_usize),
        )];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

        let report = check_module(&mut context, &declarations);
        let [ref judged] = *report.judged()
        else {
            panic!("one verdict per declaration");
        };
        let Verdict::Synthesised { synthesised, .. } = judged.verdict()
        else {
            panic!("a program with an unfilled hole gets a type");
        };
        let Some(held) = context.arena().value_type(synthesised.produced().id())
        else {
            panic!("the pair synthesises a product");
        };
        let ValueType::Product(ref parts) = *held
        else {
            panic!("the pair synthesises a product");
        };
        let [first, second] = **parts
        else {
            panic!("the pair's product is binary");
        };
        assert_eq!(
            context.arena().value_type(first),
            Some(&ValueType::Unknown),
            "the hole's component is the unknown type"
        );
        assert_eq!(
            context.arena().value_type(second),
            Some(&ValueType::Base(BaseType::Integer)),
            "the literal's component is known"
        );
        let elaboration = elaborate_value(&mut context, program, Direction::Synthesise).unwrap();
        assert!(
            elaboration.marks().is_empty(),
            "an unfilled hole is no error"
        );

        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let evaluated = eval_value(
            context.arena(),
            &mut domain,
            definitions,
            Fuel::from(10_000_u32),
            program,
        )
        .unwrap();
        let Some(&[first, _]) = domain
            .value(evaluated)
            .and_then(|held| domain.components(held))
        else {
            panic!("the pair evaluates around the hole");
        };
        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(first)
        else {
            panic!("the hole's component is indeterminate");
        };
        assert!(
            matches!(
                domain.neutral(neutral).unwrap().head(),
                NeutralHead::Hole { hole: named, .. } if named == hole
            ),
            "the indeterminate result stands on the unfilled hole"
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn the_strict_judgement_is_the_total_runs_oracle(
            recipe in term_recipe(),
            constants in vec(type_recipe(), 4),
            expected in type_recipe(),
        )
        {
            let mut arena = CoreArena::new();
            let terms = recipe.build(&mut arena);
            let constant_types: Vec<_> = constants.iter().map(|constant| constant.build(&mut arena)).collect();
            let (expected_value, expected_comp) = expected.build_both(&mut arena);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            seed(&mut context, &constant_types);
            let expected_value = form_value_type(&mut context, expected_value).unwrap();
            let expected_comp = form_comp_type(&mut context, expected_comp).unwrap();
            for &term in &terms.values {
                for direction in [Direction::Synthesise, Direction::Check(expected_value)] {
                    let strict = match direction {
                        | Direction::Synthesise => synthesise_value(&mut context, term).map(|_| ()),
                        | Direction::Check(expected) => check_value(&mut context, term, expected).map(|_| ()),
                    };
                    let total = elaborate_value(&mut context, term, direction);
                    match (strict, &total) {
                        | (Ok(()), &Ok(ref elaboration)) => prop_assert!(elaboration.marks().is_empty(), "an accepted term is not marked"),
                        | (Err(refusal), &Ok(ref elaboration)) => prop_assert_eq!(
                            elaboration.marks().first().map(MarkEntry::refusal),
                            Some(refusal),
                            "the first mark is the strict refusal"
                        ),
                        | (Ok(()), &Err(ref fault)) => prop_assert!(false, "an accepted term faults in a total run: {:?}", fault),
                        | (Err(_), &Err(ref fault)) => prop_assert_eq!(fault.classify(), FailureClass::EngineFault, "only an engine fault ends a total run"),
                    }
                    if let Ok(elaboration) = total {
                        let rechecked = check_value(&mut context, elaboration.root(), elaboration.produced());
                        prop_assert!(rechecked.is_ok(), "the marked term has the type the run produced: {:?}", rechecked);
                    }
                }
            }
            for &term in &terms.comps {
                for direction in [Direction::Synthesise, Direction::Check(expected_comp)] {
                    let strict = match direction {
                        | Direction::Synthesise => synthesise_comp(&mut context, term).map(|_| ()),
                        | Direction::Check(expected) => check_comp(&mut context, term, expected).map(|_| ()),
                    };
                    let total = elaborate_comp(&mut context, term, direction);
                    match (strict, &total) {
                        | (Ok(()), &Ok(ref elaboration)) => prop_assert!(elaboration.marks().is_empty(), "an accepted term is not marked"),
                        | (Err(refusal), &Ok(ref elaboration)) => prop_assert_eq!(
                            elaboration.marks().first().map(MarkEntry::refusal),
                            Some(refusal),
                            "the first mark is the strict refusal"
                        ),
                        | (Ok(()), &Err(ref fault)) => prop_assert!(false, "an accepted term faults in a total run: {:?}", fault),
                        | (Err(_), &Err(ref fault)) => prop_assert_eq!(fault.classify(), FailureClass::EngineFault, "only an engine fault ends a total run"),
                    }
                    if let Ok(elaboration) = total {
                        let rechecked = check_comp(&mut context, elaboration.root(), elaboration.produced());
                        prop_assert!(rechecked.is_ok(), "the marked term has the type the run produced: {:?}", rechecked);
                    }
                }
            }
        }
    }
}
