//! The conversion machine's rule table: what one goal does next, read off the
//! shapes of its two weak heads.
//!
//! # One table, two readers
//!
//! The table is the convertibility judgement's rules for this language —
//! Courant and Leroy's figure 4 extended to call-by-push-value formers, the
//! frozen-constant rules of their §6.1 and the two η-rules of §6.2 — stated
//! once over shapes. The machine reads it to decide which processes to start;
//! the kernel's sequential replay reads the same rules over its own terms, and
//! the subgoal order fixed here ([`spine_subgoals`]) is the order a recorded
//! subgoal position counts in.
//!
//! # A plan, not an action
//!
//! [`plan`] mints nothing and starts nothing. It answers which rule applies —
//! a closure on the two nodes as they stand, a leaf, a forced decomposition, a
//! forced single-premise step, or a choice point — and leaves channels,
//! processes and decisions to the machine, so the table stays a pure reading
//! of the domain.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_term::ConstantIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::code::CodeComparison;
use crate::code::ConstantReading;
use crate::code::compare_codes;
use crate::conv::ConversionFault;
use crate::conv::Early;
use crate::conv::early_comps;
use crate::conv::early_values;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::machine::DeclineReason;

/// A two-valued answer a rule gives on its own.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Settled
{
    /// The two sides are convertible.
    Convertible,
    /// The two sides are not.
    NotConvertible,
}

/// Whether a constant is held frozen on one side.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Membership
{
    /// The constant is frozen on that side.
    Held,
    /// It is not.
    Absent,
}

/// The constants one goal has frozen, per side.
///
/// A frozen constant behaves like a free variable: the goal may not unfold it,
/// and it meets an application of itself through its arguments alone. The set
/// belongs to the goal's head occurrences rather than to the constant, which is
/// why a decomposition's subgoals start with none.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Frozen
{
    /// Frozen on the left.
    left: Vec<ConstantIndex>,
    /// Frozen on the right.
    right: Vec<ConstantIndex>,
}

impl Frozen
{
    /// Whether `constant` is frozen on `side`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn holds(
        &self,
        side: ConversionSide,
        constant: ConstantIndex,
    ) -> Membership
    {
        let held = match side {
            | ConversionSide::Left => &self.left,
            | ConversionSide::Right => &self.right,
        };
        if held.contains(&constant) {
            Membership::Held
        }
        else {
            Membership::Absent
        }
    }

    /// Freeze `constant` on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Frozen::holds`] answers [`Membership::Held`] for the pair
    ///   afterwards, and the set holds each constant once.
    /// - provides: the freezing half of the §6.1 branch.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — repeating a freeze leaves the goal state unchanged,
    ///   distinct constants can be frozen on different sides, and head
    ///   classification reads only its own side; duplicating a member or
    ///   freezing both sides changes the state or permitted unfolding.
    /// - witness: `rules::tests::freezing_is_idempotent_and_local_to_one_side`
    // economy: membership is a linear scan, and a goal's frozen set grows by
    // one per freezing branch on its chain — a handful in practice. Upgrade
    // path: a sorted vector with a binary search when a chain freezes enough
    // constants to show in a profile.
    #[spec(
        captures: other_length = match side { ConversionSide::Left => self.right.len(), ConversionSide::Right => self.left.len() },
        ensures: match side {
            ConversionSide::Left => self.left.iter().filter(|&&held| held == constant).count() == 1 && self.right.len() == other_length,
            ConversionSide::Right => self.right.iter().filter(|&&held| held == constant).count() == 1 && self.left.len() == other_length,
        },
    )]
    pub(crate) fn freeze(
        &mut self,
        side: ConversionSide,
        constant: ConstantIndex,
    )
    {
        let held = match side {
            | ConversionSide::Left => &mut self.left,
            | ConversionSide::Right => &mut self.right,
        };
        if !held.contains(&constant) {
            held.push(constant);
        }
    }
}

/// What a neutral's head is to the goal comparing it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Head
{
    /// Nothing unfolds it here: a variable, a module form, an opaque
    /// declaration.
    Rigid,
    /// A defined constant the goal has frozen on this side.
    Frozen(ConstantIndex),
    /// A defined constant the goal may unfold.
    Defined(ConstantIndex),
}

/// One subgoal of a decomposition, as the rule names it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Subgoal
{
    /// Two values, compared as they stand.
    Values(DomainValueId, DomainValueId),
    /// Two closures, compared once both are opened under one fresh variable.
    Opened(CompClosureId, CompClosureId),
    /// The complete nominal classifiers captured by two constructor values.
    Classifiers(crate::arena::ValueClosureId, crate::arena::ValueClosureId),
    /// Two case motives, quoted under the same fresh scrutinee variable.
    CaseMotives(CompClosureId, CompClosureId),
    /// Two ordinary branch functions at one constructor ordinal.
    CaseBranch
    {
        /// The left case closure, retaining its lexical environment.
        left: CompClosureId,
        /// The right case closure under the same comparison scope.
        right: CompClosureId,
        /// The constructor ordinal selecting one branch from each case.
        tag: gandr_core_term::ConstructorTag,
    },
}

/// A forced rule with one premise.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Step
{
    /// Unfold the defined head on this side: no other rule applies.
    Unfold(ConversionSide),
    /// Force both sides: two thunks, or a thunk against a stuck value.
    Force,
    /// Apply the neutral on this side to a fresh variable and open the lambda
    /// on the other under it: the safe and profitable η case.
    Eta(ConversionSide),
}

/// A choice point: the alternatives a goal runs as concurrent processes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Choice
{
    /// One defined constant on both sides over spines of one length.
    Same,
    /// Two defined heads that differ, or one constant over spines of different
    /// lengths.
    Different,
    /// A defined constant against the same constant frozen on the other side.
    Frozen
    {
        /// The side whose head is unfrozen.
        defined: ConversionSide,
    },
    /// A lambda against a defined computation on the other side.
    Lambda
    {
        /// The side whose head is defined.
        defined: ConversionSide,
    },
}

/// How a choice's alternatives combine.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Combination
{
    /// Biased: a convertible answer from any alternative wins; otherwise the
    /// last alternative, the only authoritative one, decides.
    Biased,
    /// Either: a convertible answer from either wins; both must refute.
    Either,
}

/// The move one alternative of a choice starts with.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Move
{
    /// Compare the two spines argument by argument without unfolding: the
    /// `const` rule.
    Shortcut,
    /// Unfold the head on this side.
    Unfold(ConversionSide),
    /// Freeze the head on this side and unfold the other.
    FreezeUnfold(ConversionSide),
    /// Unfold the head on this side and leave the other for a later choice.
    PostponeUnfold(ConversionSide),
    /// Freeze the defined head on this side and η-expand it against the lambda
    /// on the other.
    FreezeEta(ConversionSide),
}

impl Choice
{
    /// The alternatives this choice runs and how they combine, the
    /// authoritative alternative last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the §6.1 and §6.2 rules: one constant on both sides runs the
    ///   shortcut, then the left-frozen unfolding of the right, then the
    ///   authoritative unfolding of the left, biased; two different heads drop
    ///   the shortcut; a frozen constant against itself unfrozen runs the
    ///   shortcut or the unfolding of the unfrozen side; a lambda against a
    ///   defined computation runs the frozen η-expansion, then the
    ///   authoritative unfolding, biased.
    /// - provides: the one place the machine reads which alternatives a choice
    ///   point has, and the replay reads which a recorded branch may name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four arms, each separated by a conversion whose
    ///   winning branch is the alternative that arm alone offers. Reordering
    ///   the authoritative alternative or freezing the wrong side changes the
    ///   selected trace or makes replay refuse it.
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    #[spec(ensures: |ret| match self {
        Self::Same => ret.0 == Combination::Biased && ret.1.as_slice() == [Move::Shortcut,
            Move::FreezeUnfold(ConversionSide::Left), Move::PostponeUnfold(ConversionSide::Left)],
        Self::Different => ret.0 == Combination::Biased && ret.1.as_slice() == [
            Move::FreezeUnfold(ConversionSide::Left), Move::PostponeUnfold(ConversionSide::Left)],
        Self::Frozen { defined } => ret.0 == Combination::Either
            && ret.1.as_slice() == [Move::Shortcut, Move::Unfold(defined)],
        Self::Lambda { defined } => ret.0 == Combination::Biased
            && ret.1.as_slice() == [Move::FreezeEta(defined), Move::Unfold(defined)],
    })]
    pub(crate) fn alternatives(self) -> (Combination, Vec<Move>)
    {
        match self {
            | Self::Same => (
                Combination::Biased,
                Vec::from([
                    Move::Shortcut,
                    Move::FreezeUnfold(ConversionSide::Left),
                    Move::PostponeUnfold(ConversionSide::Left),
                ]),
            ),
            | Self::Different => (
                Combination::Biased,
                Vec::from([
                    Move::FreezeUnfold(ConversionSide::Left),
                    Move::PostponeUnfold(ConversionSide::Left),
                ]),
            ),
            | Self::Frozen { defined } => (
                Combination::Either,
                Vec::from([Move::Shortcut, Move::Unfold(defined)]),
            ),
            | Self::Lambda { defined } => (
                Combination::Biased,
                Vec::from([Move::FreezeEta(defined), Move::Unfold(defined)]),
            ),
        }
    }
}

/// What a goal does next.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Plan
{
    /// Steps 1 or 2 of the pipeline answered on the two nodes as they stand.
    Shared(Settled),
    /// A rule with no premise answered.
    Leaf(Settled),
    /// A forced decomposition into subgoals, in the order positions count.
    Decompose(Vec<Subgoal>),
    /// A forced rule with one premise.
    Step(Step),
    /// A choice point.
    Choose(Choice),
    /// No rule applies at this rung: the goal declines.
    Decline(DeclineReason),
}

/// Metadata that must agree before two eliminations expose their premises.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EliminationShape<'core>
{
    /// An existing fixed-arity elimination kind.
    Ordinary(core::mem::Discriminant<Elimination>),
    /// A nominal case with this many ordinary branch functions.
    DataCase(usize),
    /// An exact record label.
    Projection(&'core gandr_core_term::FieldLabel),
}

/// Resolve the motive and branch functions retained by a native case capture.
///
/// # Specification
/// - requires: nothing; stale and ill-shaped captures are refused.
/// - ensures: returns the source case's motive and complete ordered branch
///   slice.
/// - fails: a dangling closure or a body that is not a source data case.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — open cases preserve their motive scope and every branch
///   function.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret,Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)))]
pub fn case_source<'core>(
    core: &'core CoreArena,
    domain: &DomainArena,
    closure: CompClosureId,
) -> Result<
    (
        gandr_core_term::CompTypeId,
        &'core [gandr_core_term::ComputationId],
    ),
    ConversionFault,
>
{
    let closure = domain
        .comp_closure(closure)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    let crate::closure::CompBody::Source(source) = closure.body()
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    let Some(matched_native_node) = core.computation(source)
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    let gandr_core_term::Computation::DataCase {
        ref motive,
        ref branches,
        ..
    } = *matched_native_node
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    Ok((*motive, branches))
}

/// Read the exact source label of a native projection.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the projection's label, with no spelling normalization.
/// - fails: a missing source or a non-projection body.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unlike labels remain unlike even on one neutral record.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
#[spec(ensures:|ret| core.computation(source).map_or_else(|| ret == Err(ConversionFault::MachineInvariant), |matched_native_node| match *matched_native_node {
gandr_core_term::Computation::RecordProjection(_,ref label) => ret == Ok(label),
_ => ret == Err(ConversionFault::MachineInvariant),
}))]
pub fn projection_label(
    core: &CoreArena,
    source: gandr_core_term::ComputationId,
) -> Result<&gandr_core_term::FieldLabel, ConversionFault>
{
    let Some(matched_native_node) = core.computation(source)
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    let gandr_core_term::Computation::RecordProjection(_, ref label) = *matched_native_node
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    Ok(label)
}

/// Read only metadata that controls a neutral elimination's premise shape.
///
/// # Specification
/// - requires: nothing.
/// - ensures: nominal arity and exact labels remain part of shape equality.
/// - fails: malformed native captures, as the source readers report.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — equal-length spines can still differ by labels or case
///   arity.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
#[spec(ensures:|ret| match elimination {
    Elimination::DataCase(closure) => ret == case_source(core,domain,closure).map(|(_,branches)| EliminationShape::DataCase(branches.len())),
    Elimination::RecordProjection(source) => ret == projection_label(core,source).map(EliminationShape::Projection),
    _ => ret == Ok(EliminationShape::Ordinary(core::mem::discriminant(&elimination))),
})]
fn elimination_shape<'core>(
    core: &'core CoreArena,
    domain: &DomainArena,
    elimination: Elimination,
) -> Result<EliminationShape<'core>, ConversionFault>
{
    match elimination {
        | Elimination::DataCase(closure) => case_source(core, domain, closure)
            .map(|(_, branches)| EliminationShape::DataCase(branches.len())),
        | Elimination::RecordProjection(source) => {
            projection_label(core, source).map(EliminationShape::Projection)
        },
        | _ => Ok(EliminationShape::Ordinary(core::mem::discriminant(
            &elimination,
        ))),
    }
}

/// The other side.
///
/// # Specification
/// trivial.
pub const fn other(side: ConversionSide) -> ConversionSide
{
    match side {
        | ConversionSide::Left => ConversionSide::Right,
        | ConversionSide::Right => ConversionSide::Left,
    }
}

/// What a neutral's head is to a goal with `frozen` on `side`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Head::Rigid`] for a variable, a module form, or a constant with
///   a rigid unfolding face; otherwise [`Head::Frozen`] when the goal froze the
///   constant on `side` and [`Head::Defined`] when it did not.
/// - provides: the one reading of "may this goal unfold this head".
/// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — the neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — a loaded constant is defined on one side and frozen on
///   the other; an opaque occurrence of the same constant remains rigid, and
///   truncation refuses the head. Confusing side-local freezing with the
///   unfolding face changes classification.
/// - witness: `rules::tests::freezing_is_idempotent_and_local_to_one_side`
#[spec(ensures: |ret| domain.neutral(neutral).map_or_else(
    || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
    |node| match (node.head(), node.unfolding()) {
        (NeutralHead::Constant(constant), Unfolding::Unforced(_) | Unfolding::Forced(_)) =>
            ret == Ok(if frozen.holds(side, constant) == Membership::Held {
                Head::Frozen(constant)
            } else { Head::Defined(constant) }),
        _ => ret == Ok(Head::Rigid),
    },
))]
pub fn head(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    neutral: NeutralId,
) -> Result<Head, ConversionFault>
{
    let held = domain
        .neutral(neutral)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    Ok(match (held.head(), held.unfolding()) {
        | (NeutralHead::Constant(constant), Unfolding::Unforced(_) | Unfolding::Forced(_)) => {
            match frozen.holds(side, constant) {
                | Membership::Held => Head::Frozen(constant),
                | Membership::Absent => Head::Defined(constant),
            }
        },
        | (NeutralHead::Constant(_), Unfolding::Rigid)
        | (NeutralHead::Variable { .. } | NeutralHead::Module(_), _) => Head::Rigid,
    })
}

/// What two spines compared elimination by elimination give.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Spines
{
    /// One shape: the subgoals, in the order positions count.
    Agree(Vec<Subgoal>),
    /// A length or an elimination kind differs.
    Disagree,
}

/// The subgoals of two spines compared elimination by elimination.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Spines::Agree`] when the spines have one length and one
///   elimination kind at every position: application and transport arguments as
///   value pairs, a bind's continuations as an opened pair, a case's branches
///   as two opened pairs left first, and a force as nothing, in spine order
///   innermost first; [`Spines::Disagree`] when a length or a kind differs. The
///   heads are not compared.
/// - provides: the premises of `var-1` and `const`, in the order a recorded
///   subgoal position counts.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — native cases and projections retain their ordered
///   operands in replayable traces; distinct family heads, indices and arities
///   remain distinguishable. These are consumer paths, not an exhaustive table
///   of private spine shapes or dangling ids.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
/// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(ensures: |ret| match (domain.neutral(left),domain.neutral(right)) {
    (Some(one),Some(other)) if one.spine().len() != other.spine().len() => ret == Ok(Spines::Disagree),
    (Some(one),Some(other)) => {
        let expected = one.spine().iter().zip(other.spine()).try_fold((true,0_usize),|(same,count),(&a,&b)| -> Result<_,ConversionFault> {
            if !same { return Ok((false,count)); }
            let shape = elimination_shape(core,domain,a)?;
            if shape != elimination_shape(core,domain,b)? { return Ok((false,count)); }
            let added = match shape {
                EliminationShape::DataCase(branches) => branches.saturating_add(1_usize),
                EliminationShape::Projection(_) => 0_usize,
                EliminationShape::Ordinary(_) => match a { Elimination::Force => 0_usize,Elimination::Case { .. } => 2_usize,_ => 1_usize },
            };
            Ok((true,count.saturating_add(added)))
        });
        match expected {
            Err(fault) => ret == Err(fault),
            Ok((false,_)) => ret == Ok(Spines::Disagree),
            Ok((true,count)) => matches!(ret,Ok(Spines::Agree(ref subgoals)) if subgoals.len() == count),
        }
    },
    _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
})]
pub fn spine_subgoals(
    core: &CoreArena,
    domain: &DomainArena,
    left: NeutralId,
    right: NeutralId,
) -> Result<Spines, ConversionFault>
{
    let (Some(one), Some(other)) = (domain.neutral(left), domain.neutral(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if one.spine().len() != other.spine().len() {
        return Ok(Spines::Disagree);
    }
    let mut subgoals = Vec::new();
    for (&left_elimination, &right_elimination) in one.spine().iter().zip(other.spine()) {
        let shape = elimination_shape(core, domain, left_elimination)?;
        if shape != elimination_shape(core, domain, right_elimination)? {
            return Ok(Spines::Disagree);
        }
        match (left_elimination, right_elimination) {
            | (Elimination::DataCase(left), Elimination::DataCase(right)) => {
                let EliminationShape::DataCase(count) = shape
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                subgoals.push(Subgoal::CaseMotives(left, right));
                subgoals.extend((0_usize .. count).map(|index| Subgoal::CaseBranch {
                    left,
                    right,
                    tag: gandr_core_term::ConstructorTag::from(index),
                }));
            },
            | (Elimination::RecordProjection(_), Elimination::RecordProjection(_))
            | (Elimination::Force, Elimination::Force) => {},
            | (Elimination::Transport(left_argument), Elimination::Transport(right_argument))
            | (
                Elimination::ProductTransport(left_argument),
                Elimination::ProductTransport(right_argument),
            )
            | (Elimination::Apply(left_argument), Elimination::Apply(right_argument))
            | (
                Elimination::StaticApply(left_argument),
                Elimination::StaticApply(right_argument),
            ) => {
                subgoals.push(Subgoal::Values(left_argument, right_argument));
            },
            | (Elimination::Bind(left_body), Elimination::Bind(right_body)) => {
                subgoals.push(Subgoal::Opened(left_body, right_body));
            },
            | (
                Elimination::Case {
                    on_left: left_on_left,
                    on_right: left_on_right,
                },
                Elimination::Case {
                    on_left: right_on_left,
                    on_right: right_on_right,
                },
            ) => {
                subgoals.push(Subgoal::Opened(left_on_left, right_on_left));
                subgoals.push(Subgoal::Opened(left_on_right, right_on_right));
            },
            | (
                Elimination::Transport(_)
                | Elimination::DataCase(_)
                | Elimination::RecordProjection(_)
                | Elimination::ProductTransport(_)
                | Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Bind(_)
                | Elimination::Case { .. }
                | Elimination::StaticApply(_),
                _,
            ) => return Ok(Spines::Disagree),
        }
    }
    Ok(Spines::Agree(subgoals))
}

/// Whether two neutrals stand over spines of one length.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Arity::Same`] exactly when both resolve and their spines have
///   one length.
/// - provides: the arity condition the §6.1 rules state as `|s| = |s'|`.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — catalogue and generated ladder comparisons retain their
///   verdicts under independent replay. An incorrect arity choice changes the
///   selected constant rule on those comparisons.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(ensures: |ret| match (domain.neutral(left), domain.neutral(right)) {
    (Some(one), Some(other)) => ret == Ok(if one.spine().len() == other.spine().len() {
        Arity::Same
    } else { Arity::Different }),
    _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
})]
fn same_arity(
    domain: &DomainArena,
    left: NeutralId,
    right: NeutralId,
) -> Result<Arity, ConversionFault>
{
    let (Some(one), Some(other)) = (domain.neutral(left), domain.neutral(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    Ok(if one.spine().len() == other.spine().len() {
        Arity::Same
    }
    else {
        Arity::Different
    })
}

/// Whether two spines have one length.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Arity
{
    /// One length.
    Same,
    /// Two lengths.
    Different,
}

/// What a goal over two weak heads does next.
///
/// # Specification
/// - requires: both sides resolve in `domain` and are of one polarity.
/// - ensures: [`Plan::Shared`] when steps 1 or 2 answer; otherwise the rule the
///   shapes select — a choice point or a forced unfolding whenever a side's
///   head is a defined constant the goal has not frozen, else the structural
///   rule: a leaf for units, literals and mismatched formers, a decomposition
///   for agreeing formers and for two rigid neutrals of one head and spine
///   shape, a forcing step for thunks against thunks or stuck values, an η-step
///   for a lambda against a rigid or frozen neutral, and for two codes a shared
///   answer when they are α-equal or rigidly apart and a decline otherwise.
/// - provides: the machine's whole rule table, read once per goal turn.
/// - fails: [`ConversionFault::Polarity`] when the sides differ in polarity,
///   [`ConversionFault::Domain`] for a node that does not resolve, and
///   [`ConversionFault::LiteralPayload`] for a literal naming no core literal.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Polarity`] — a value met a computation.
/// - [`ConversionFault::Domain`] — a node does not resolve.
/// - [`ConversionFault::LiteralPayload`] — a literal names no core literal.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces include the constant and structural
///   arms, separated by conversions the machine answers through those arms
///   alone. Opposite polarities refuse in both orders; changing precedence, the
///   selected side or the subgoal order changes a verdict or replay result.
/// - witness: `rules::tests::opposite_polarities_are_refused_in_both_orders`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
/// - witness: `machine::tests::a_code_constant_unfolds_to_its_quote`
/// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
#[spec(ensures: |ret| matches!(ret, Err(ConversionFault::Polarity)) == matches!((left, right),
    (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_))))]
pub fn plan(
    core: &CoreArena,
    domain: &DomainArena,
    definitions: Definitions<'_>,
    frozen: &Frozen,
    left: Glued,
    right: Glued,
) -> Result<Plan, ConversionFault>
{
    match (left, right) {
        | (Glued::Value(one), Glued::Value(other)) => {
            plan_values(core, domain, definitions, frozen, one, other)
        },
        | (Glued::Computation(one), Glued::Computation(other)) => {
            plan_comps(core, domain, frozen, one, other)
        },
        | (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => {
            Err(ConversionFault::Polarity)
        },
    }
}

/// What the constant arms of the table make of a pair.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Constants
{
    /// A side's head is defined, and this is the rule.
    Planned(Plan),
    /// Neither side's head is defined; the structural arms decide.
    NoneDefined,
}

/// The plan for a defined head on at least one side.
///
/// # Specification
/// - requires: `lambda` names the side holding a lambda when the pair is a
///   computation pair with one; [`Lambda::Neither`] otherwise.
/// - ensures: [`Constants::Planned`] with the §6.1 rule for the two heads when
///   either is [`Head::Defined`], the §6.2 choice for a lambda against a
///   defined computation, and a forced unfolding of the defined side against
///   anything else; [`Constants::NoneDefined`] when neither head is defined.
/// - provides: the constant half of the table, shared by both polarities.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — equal and different defined heads select different
///   unfolding choices, a defined head meets a lambda through frozen eta, and a
///   defined head against a former must unfold; ignoring a defined side or
///   choosing the wrong side changes the winning trace.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |planned|
    matches!(planned, Constants::NoneDefined) != matches!(heads,
        (Neutrality::Neutral(_, Head::Defined(_)), _) | (_, Neutrality::Neutral(_, Head::Defined(_))))))]
fn plan_constants(
    domain: &DomainArena,
    heads: (Neutrality, Neutrality),
    lambda: Lambda,
) -> Result<Constants, ConversionFault>
{
    let (left, right) = heads;
    let mut arity = Arity::Different;
    if let (Neutrality::Neutral(left_neutral, _), Neutrality::Neutral(right_neutral, _)) =
        (left, right)
    {
        arity = same_arity(domain, left_neutral, right_neutral)?;
    }
    let planned = match (left, right) {
        | (
            Neutrality::Neutral(_, Head::Defined(one)),
            Neutrality::Neutral(_, Head::Defined(other)),
        ) => {
            if one == other && arity == Arity::Same {
                Plan::Choose(Choice::Same)
            }
            else {
                Plan::Choose(Choice::Different)
            }
        },
        | (
            Neutrality::Neutral(_, Head::Defined(one)),
            Neutrality::Neutral(_, Head::Frozen(other)),
        ) if one == other && arity == Arity::Same => Plan::Choose(Choice::Frozen {
            defined: ConversionSide::Left,
        }),
        | (
            Neutrality::Neutral(_, Head::Frozen(one)),
            Neutrality::Neutral(_, Head::Defined(other)),
        ) if one == other && arity == Arity::Same => Plan::Choose(Choice::Frozen {
            defined: ConversionSide::Right,
        }),
        | (Neutrality::Neutral(_, Head::Defined(_)), _) => match lambda {
            | Lambda::Right => Plan::Choose(Choice::Lambda {
                defined: ConversionSide::Left,
            }),
            | Lambda::Left | Lambda::Neither => Plan::Step(Step::Unfold(ConversionSide::Left)),
        },
        | (_, Neutrality::Neutral(_, Head::Defined(_))) => match lambda {
            | Lambda::Left => Plan::Choose(Choice::Lambda {
                defined: ConversionSide::Right,
            }),
            | Lambda::Right | Lambda::Neither => Plan::Step(Step::Unfold(ConversionSide::Right)),
        },
        | (
            Neutrality::Former | Neutrality::Neutral(_, Head::Rigid | Head::Frozen(_)),
            Neutrality::Former | Neutrality::Neutral(_, Head::Rigid | Head::Frozen(_)),
        ) => return Ok(Constants::NoneDefined),
    };
    Ok(Constants::Planned(planned))
}

/// Whether a side is a neutral, and how its head reads.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Neutrality
{
    /// A former: not stuck on anything.
    Former,
    /// A neutral, with its head as the goal reads it.
    Neutral(NeutralId, Head),
}

/// Which side of a computation pair holds a lambda.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Lambda
{
    /// The left.
    Left,
    /// The right.
    Right,
    /// Neither, or both.
    Neither,
}

/// The decomposition of two rigid neutrals: their spines when the heads and
/// shapes agree, a refutation otherwise.
///
/// # Specification
/// - requires: neither head is [`Head::Defined`].
/// - ensures: [`Plan::Decompose`] over [`spine_subgoals`] when the heads are
///   one head and the spines one shape — `var-1`; [`Plan::Leaf`] refuting
///   otherwise — `var-2`.
/// - provides: the rigid-head arm of the table.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — a differing argument refutes a rigid spine; native case
///   and projection comparisons preserve their operands and labels in
///   independently replayable traces.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
#[spec(ensures: |ret| match (domain.neutral(left),domain.neutral(right)) {
    (Some(one),Some(other)) if one.head() != other.head() => ret == Ok(Plan::Leaf(Settled::NotConvertible)),
    (Some(_),Some(_)) => match spine_subgoals(core,domain,left,right) {
        Ok(Spines::Agree(subgoals)) => ret == Ok(Plan::Decompose(subgoals)),
        Ok(Spines::Disagree) => ret == Ok(Plan::Leaf(Settled::NotConvertible)),
        Err(fault) => ret == Err(fault),
    },
    _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
})]
fn plan_rigid(
    core: &CoreArena,
    domain: &DomainArena,
    left: NeutralId,
    right: NeutralId,
) -> Result<Plan, ConversionFault>
{
    let (Some(one), Some(other)) = (domain.neutral(left), domain.neutral(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if one.head() != other.head() {
        return Ok(Plan::Leaf(Settled::NotConvertible));
    }
    let spines = spine_subgoals(core, domain, left, right)?;
    Ok(match spines {
        | Spines::Agree(subgoals) => Plan::Decompose(subgoals),
        | Spines::Disagree => Plan::Leaf(Settled::NotConvertible),
    })
}

/// How a value side reads as a neutral.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Neutrality::Neutral`] with the head as [`head`] reads it for a
///   neutral value; [`Neutrality::Former`] for every other value, a static
///   lambda among them.
/// - provides: the neutral projection the constant arms match on.
/// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — the neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — a defined neutral against a former unfolds, while a
///   lambda against a defined computation offers frozen eta and a rigid stuck
///   function offers ordinary eta; projecting a former as a neutral or dropping
///   its frozen side changes the rule and trace.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
/// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(ensures: |ret| match value {
    DomainValue::Neutral { neutral, .. } => ret == head(domain, frozen, side, neutral)
        .map(|read| Neutrality::Neutral(neutral, read)),
    _ => ret == Ok(Neutrality::Former),
})]
fn value_neutrality(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    value: DomainValue,
) -> Result<Neutrality, ConversionFault>
{
    Ok(match value {
        | DomainValue::Neutral { neutral, .. } => {
            let read = head(domain, frozen, side, neutral)?;
            Neutrality::Neutral(neutral, read)
        },
        | DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Neutrality::Former,
    })
}

/// How a computation side reads as a neutral.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Neutrality::Neutral`] with the head as [`head`] reads it for a
///   neutral computation; [`Neutrality::Former`] for a lambda or a returner.
/// - provides: the neutral projection the constant arms match on.
/// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — the neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — a defined neutral against a former unfolds, while a
///   lambda against a defined computation offers frozen eta and a rigid stuck
///   function offers ordinary eta; projecting a former as a neutral or dropping
///   its frozen side changes the rule and trace.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
#[spec(ensures: |ret| match comp {
    DomainComp::Neutral { neutral, .. } => ret == head(domain, frozen, side, neutral)
        .map(|read| Neutrality::Neutral(neutral, read)),
    _ => ret == Ok(Neutrality::Former),
})]
fn comp_neutrality(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    comp: DomainComp,
) -> Result<Neutrality, ConversionFault>
{
    Ok(match comp {
        | DomainComp::Neutral { neutral, .. } => {
            let read = head(domain, frozen, side, neutral)?;
            Neutrality::Neutral(neutral, read)
        },
        | DomainComp::Lambda { .. } | DomainComp::Return { .. } => Neutrality::Former,
    })
}

/// The literal a domain literal's core id names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the payload the core node holds.
/// - provides: the one core read the table makes.
/// - fails: [`ConversionFault::LiteralPayload`] when the node is missing or is
///   not a literal.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::LiteralPayload`] — no core literal at `literal`.
///
/// # Adequacy
/// - hypothesis: L2 — literal nodes resolve as payloads, but a unit and an id
///   removed by truncation report the offending id; treating a live nonliteral
///   as a valid payload or dropping the id changes the named refusal.
/// - witness: `rules::tests::payloads_refuse_nonliteral_and_missing_nodes`
#[spec(ensures: |ret| ret.is_ok() == matches!(core.value(literal), Some(Value::Literal(_)))
    && ret.as_ref().err().is_none_or(|fault| *fault == ConversionFault::LiteralPayload { literal }))]
fn payload(
    core: &CoreArena,
    literal: ValueId,
) -> Result<&gandr_kernel_term::Literal, ConversionFault>
{
    match core.value(literal) {
        | Some(&Value::Literal(ref held)) => Ok(held),
        | Some(_) | None => Err(ConversionFault::LiteralPayload { literal }),
    }
}

/// [`plan`] over two values.
///
/// # Specification
/// - requires: nothing — dangling ids are admissible input and refused.
/// - ensures: as [`plan`], over the value formers.
/// - provides: the value half of the table.
/// - fails: as [`plan`].
/// - panics: none.
///
/// # Errors
/// As [`plan`].
///
/// # Adequacy
/// - hypothesis: L2 — rigid spines identify the differing argument, and
///   closures meet through forcing or eta rather than immediate refutation;
///   selecting the wrong structural rule changes the verdict or its trace.
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
/// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(ensures: |ret| (match early_values(domain, left, right) {
    Ok(Early::Identical) => ret == Ok(Plan::Shared(Settled::Convertible)),
    Ok(Early::Apart) => ret == Ok(Plan::Shared(Settled::NotConvertible)),
    Ok(Early::Open) => true,
    Err(fault) => ret == Err(fault),
}) && match (domain.value(left), domain.value(right)) {
    (Some(&DomainValue::PathCertificate { .. }), Some(&DomainValue::PathProduct { .. })) | (Some(&DomainValue::PathProduct { .. }), Some(&DomainValue::PathCertificate { .. })) => ret == Ok(Plan::Shared(Settled::NotConvertible)),
    (Some(&DomainValue::PathCertificate { certificate: a, .. }), Some(&DomainValue::PathCertificate { certificate: b, .. })) if a == b => ret == Ok(Plan::Shared(Settled::Convertible)),
    _ => true,
})]
fn plan_values(
    core: &CoreArena,
    domain: &DomainArena,
    definitions: Definitions<'_>,
    frozen: &Frozen,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<Plan, ConversionFault>
{
    let early = early_values(domain, left, right)?;
    match early {
        | Early::Identical => return Ok(Plan::Shared(Settled::Convertible)),
        | Early::Apart => return Ok(Plan::Shared(Settled::NotConvertible)),
        | Early::Open => {},
    }
    let (Some(&one), Some(&other)) = (domain.value(left), domain.value(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let left_head = value_neutrality(domain, frozen, ConversionSide::Left, one)?;
    let right_head = value_neutrality(domain, frozen, ConversionSide::Right, other)?;
    let constants = plan_constants(domain, (left_head, right_head), Lambda::Neither)?;
    if let Constants::Planned(planned) = constants {
        return Ok(planned);
    }
    let planned = match (one, other) {
        | (
            DomainValue::Constructor {
                datatype: left_source,
                tag: left_tag,
                fields: left_fields,
                ..
            },
            DomainValue::Constructor {
                datatype: right_source,
                tag: right_tag,
                fields: right_fields,
                ..
            },
        ) => {
            let left_fields = domain
                .fields(left_fields)
                .map_err(ConversionFault::Domain)?;
            let right_fields = domain
                .fields(right_fields)
                .map_err(ConversionFault::Domain)?;
            if left_tag != right_tag || left_fields.len() != right_fields.len() {
                return Ok(Plan::Leaf(Settled::NotConvertible));
            }
            let mut subgoals = Vec::with_capacity(left_fields.len().saturating_add(1_usize));
            subgoals.push(Subgoal::Classifiers(left_source, right_source));
            subgoals.extend(
                left_fields
                    .iter()
                    .zip(right_fields)
                    .map(|(a, b)| Subgoal::Values(*a, *b)),
            );
            Plan::Decompose(subgoals)
        },
        | (
            DomainValue::Record {
                source: left_source,
                fields: left_fields,
                ..
            },
            DomainValue::Record {
                source: right_source,
                fields: right_fields,
                ..
            },
        ) => {
            let (Some(left_node), Some(right_node)) =
                (core.value(left_source), core.value(right_source))
            else {
                return Err(ConversionFault::MachineInvariant);
            };
            let gandr_core_term::Value::Record(ref left_labels) = *left_node
            else {
                return Err(ConversionFault::MachineInvariant);
            };
            let gandr_core_term::Value::Record(ref right_labels) = *right_node
            else {
                return Err(ConversionFault::MachineInvariant);
            };
            let left_fields = domain
                .fields(left_fields)
                .map_err(ConversionFault::Domain)?;
            let right_fields = domain
                .fields(right_fields)
                .map_err(ConversionFault::Domain)?;
            if left_labels.len() != left_fields.len() || right_labels.len() != right_fields.len() {
                return Err(ConversionFault::MachineInvariant);
            }
            if !left_labels.keys().eq(right_labels.keys()) {
                return Ok(Plan::Leaf(Settled::NotConvertible));
            }
            Plan::Decompose(
                left_fields
                    .iter()
                    .zip(right_fields)
                    .map(|(a, b)| Subgoal::Values(*a, *b))
                    .collect(),
            )
        },
        | (
            DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. },
            DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. },
        ) => Plan::Shared(
            if crate::conv::equal_paths(core, domain, left, right)?
                == gandr_core_term::CertificateEquality::Equal
            {
                Settled::Convertible
            }
            else {
                Settled::NotConvertible
            },
        ),
        | (DomainValue::Unit { .. }, DomainValue::Unit { .. }) => Plan::Leaf(Settled::Convertible),
        | (
            DomainValue::Literal { literal: first, .. },
            DomainValue::Literal {
                literal: second, ..
            },
        ) => {
            if first == second {
                return Ok(Plan::Leaf(Settled::Convertible));
            }
            let first = payload(core, first)?;
            let second = payload(core, second)?;
            Plan::Leaf(if first == second {
                Settled::Convertible
            }
            else {
                Settled::NotConvertible
            })
        },
        | (
            DomainValue::Pair {
                first: left_first,
                second: left_second,
                ..
            },
            DomainValue::Pair {
                first: right_first,
                second: right_second,
                ..
            },
        ) => Plan::Decompose(Vec::from([
            Subgoal::Values(left_first, right_first),
            Subgoal::Values(left_second, right_second),
        ])),
        | (
            DomainValue::Injection {
                side: left_side,
                body: left_body,
                ..
            },
            DomainValue::Injection {
                side: right_side,
                body: right_body,
                ..
            },
        ) => {
            if left_side == right_side {
                Plan::Decompose(Vec::from([Subgoal::Values(left_body, right_body)]))
            }
            else {
                Plan::Leaf(Settled::NotConvertible)
            }
        },
        | (
            DomainValue::Lift {
                target: left_target,
                body: left_body,
                ..
            },
            DomainValue::Lift {
                target: right_target,
                body: right_body,
                ..
            },
        ) => {
            let (Some(left_level), Some(right_level)) =
                (domain.level(left_target), domain.level(right_target))
            else {
                return Err(ConversionFault::Domain(DomainFault::Dangling));
            };
            if left_level.level() == right_level.level() {
                Plan::Decompose(Vec::from([Subgoal::Values(left_body, right_body)]))
            }
            else {
                Plan::Leaf(Settled::NotConvertible)
            }
        },
        | (DomainValue::Thunk { .. }, DomainValue::Thunk { .. } | DomainValue::Neutral { .. })
        | (DomainValue::Neutral { .. }, DomainValue::Thunk { .. }) => Plan::Step(Step::Force),
        | (
            DomainValue::Neutral {
                neutral: left_neutral,
                ..
            },
            DomainValue::Neutral {
                neutral: right_neutral,
                ..
            },
        ) => return plan_rigid(core, domain, left_neutral, right_neutral),
        // Two codes compare whole: α-equal closes them as shared, rigid and
        // α-distinct separates them as shared, and anything that could still
        // unfold inside a type is declined rather than answered.
        | (
            DomainValue::Code {
                code: left_code, ..
            },
            DomainValue::Code {
                code: right_code, ..
            },
        ) => {
            match compare_codes(
                core,
                domain,
                ConstantReading::Read(definitions),
                left_code,
                right_code,
            )? {
                | CodeComparison::Equal => Plan::Shared(Settled::Convertible),
                | CodeComparison::Apart => Plan::Shared(Settled::NotConvertible),
                | CodeComparison::Undecided => Plan::Decline(DeclineReason::UndecidedCodes),
            }
        },
        // Two static lambdas compare whole by the same α-walk, and a static
        // lambda against a stuck operator is declined: η could relate them,
        // and this rung does not expand an operator.
        | (
            DomainValue::StaticLambda {
                lambda: left_lambda,
                ..
            },
            DomainValue::StaticLambda {
                lambda: right_lambda,
                ..
            },
        ) => {
            match compare_codes(
                core,
                domain,
                ConstantReading::Read(definitions),
                left_lambda,
                right_lambda,
            )? {
                | CodeComparison::Equal => Plan::Shared(Settled::Convertible),
                | CodeComparison::Apart => Plan::Shared(Settled::NotConvertible),
                | CodeComparison::Undecided => Plan::Decline(DeclineReason::UndecidedCodes),
            }
        },
        | (DomainValue::StaticLambda { .. }, DomainValue::Neutral { .. })
        | (DomainValue::Neutral { .. }, DomainValue::StaticLambda { .. }) => {
            Plan::Decline(DeclineReason::UndecidedCodes)
        },
        | (
            DomainValue::PathCertificate { .. }
            | DomainValue::Constructor { .. }
            | DomainValue::Record { .. }
            | DomainValue::PathProduct { .. }
            | DomainValue::Unit { .. }
            | DomainValue::Literal { .. }
            | DomainValue::Pair { .. }
            | DomainValue::Injection { .. }
            | DomainValue::Thunk { .. }
            | DomainValue::Lift { .. }
            | DomainValue::Neutral { .. }
            | DomainValue::Code { .. }
            | DomainValue::StaticLambda { .. },
            _,
        ) => Plan::Leaf(Settled::NotConvertible),
    };
    Ok(planned)
}

/// [`plan`] over two weak-head computations.
///
/// # Specification
/// - requires: nothing — dangling ids are admissible input and refused.
/// - ensures: as [`plan`], over the computation formers.
/// - provides: the computation half of the table.
/// - fails: as [`plan`].
/// - panics: none.
///
/// # Errors
/// As [`plan`].
///
/// # Adequacy
/// - hypothesis: L2 — rigid spines identify the differing argument, and
///   closures meet through forcing or eta rather than immediate refutation;
///   selecting the wrong structural rule changes the verdict or its trace.
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
#[spec(ensures: |ret| match early_comps(domain, left, right) {
    Ok(Early::Identical) => ret == Ok(Plan::Shared(Settled::Convertible)),
    Ok(Early::Apart) => ret == Ok(Plan::Shared(Settled::NotConvertible)),
    Ok(Early::Open) => true,
    Err(fault) => ret == Err(fault),
})]
fn plan_comps(
    core: &CoreArena,
    domain: &DomainArena,
    frozen: &Frozen,
    left: DomainCompId,
    right: DomainCompId,
) -> Result<Plan, ConversionFault>
{
    let early = early_comps(domain, left, right)?;
    match early {
        | Early::Identical => return Ok(Plan::Shared(Settled::Convertible)),
        | Early::Apart => return Ok(Plan::Shared(Settled::NotConvertible)),
        | Early::Open => {},
    }
    let (Some(&one), Some(&other)) = (domain.computation(left), domain.computation(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let left_head = comp_neutrality(domain, frozen, ConversionSide::Left, one)?;
    let right_head = comp_neutrality(domain, frozen, ConversionSide::Right, other)?;
    let lambda = match (one, other) {
        | (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => Lambda::Left,
        | (DomainComp::Neutral { .. }, DomainComp::Lambda { .. }) => Lambda::Right,
        | (
            DomainComp::Lambda { .. } | DomainComp::Return { .. } | DomainComp::Neutral { .. },
            _,
        ) => Lambda::Neither,
    };
    let constants = plan_constants(domain, (left_head, right_head), lambda)?;
    if let Constants::Planned(planned) = constants {
        return Ok(planned);
    }
    let planned = match (one, other) {
        | (
            DomainComp::Lambda {
                body: left_body, ..
            },
            DomainComp::Lambda {
                body: right_body, ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Opened(left_body, right_body)])),
        | (
            DomainComp::Return {
                value: left_value, ..
            },
            DomainComp::Return {
                value: right_value, ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Values(left_value, right_value)])),
        | (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => {
            Plan::Step(Step::Eta(ConversionSide::Right))
        },
        | (DomainComp::Neutral { .. }, DomainComp::Lambda { .. }) => {
            Plan::Step(Step::Eta(ConversionSide::Left))
        },
        | (
            DomainComp::Neutral {
                neutral: left_neutral,
                ..
            },
            DomainComp::Neutral {
                neutral: right_neutral,
                ..
            },
        ) => return plan_rigid(core, domain, left_neutral, right_neutral),
        | (
            DomainComp::Lambda { .. } | DomainComp::Return { .. } | DomainComp::Neutral { .. },
            _,
        ) => Plan::Leaf(Settled::NotConvertible),
    };
    Ok(planned)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;

    use super::DomainArena;
    use super::Frozen;
    use super::Glued;
    use super::Head;
    use super::NeutralHead;
    use super::Unfolding;
    use crate::TermFace;

    #[test]
    fn freezing_is_idempotent_and_local_to_one_side()
    {
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let first = ConstantIndex::from(0_usize);
        let second = ConstantIndex::from(1_usize);
        let loaded = domain
            .neutral_node(
                NeutralHead::Constant(first),
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a declaration can unfold");
        let opaque = domain
            .neutral_node(NeutralHead::Constant(first), Vec::new(), Unfolding::Rigid)
            .expect("the same name can stand opaque");
        let mut frozen = Frozen::default();
        frozen.freeze(ConversionSide::Left, first);
        let once = frozen.clone();
        frozen.freeze(ConversionSide::Left, first);
        assert_eq!(once, frozen, "freezing is idempotent in the goal key");
        frozen.freeze(ConversionSide::Right, second);
        assert_eq!(
            super::Membership::Absent,
            frozen.holds(ConversionSide::Left, second)
        );
        assert_eq!(
            super::Membership::Held,
            frozen.holds(ConversionSide::Right, second)
        );
        assert_eq!(
            Ok(Head::Frozen(first)),
            super::head(&domain, &frozen, ConversionSide::Left, loaded)
        );
        assert_eq!(
            Ok(Head::Defined(first)),
            super::head(&domain, &frozen, ConversionSide::Right, loaded)
        );
        assert_eq!(
            Ok(Head::Rigid),
            super::head(&domain, &frozen, ConversionSide::Left, opaque)
        );
        let value = domain.value_unit(TermFace::Reduced);
        domain
            .force_neutral(loaded, Glued::Value(value))
            .expect("the face is initially unforced");
        assert_eq!(
            Ok(Head::Defined(first)),
            super::head(&domain, &frozen, ConversionSide::Right, loaded)
        );
        domain.truncate_to(floor);
        assert_eq!(
            Err(super::ConversionFault::Domain(super::DomainFault::Dangling)),
            super::head(&domain, &frozen, ConversionSide::Left, loaded)
        );
    }

    #[test]
    fn payloads_refuse_nonliteral_and_missing_nodes()
    {
        let mut core = CoreArena::new();
        let floor = core.watermark();
        let unit = core.value_unit();
        let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        assert!(matches!(
            super::payload(&core, literal),
            Ok(Literal::Integer(_))
        ));
        assert_eq!(
            Err(super::ConversionFault::LiteralPayload { literal: unit }),
            super::payload(&core, unit)
        );
        core.truncate_to(floor);
        assert_eq!(
            Err(super::ConversionFault::LiteralPayload { literal }),
            super::payload(&core, literal)
        );
    }

    #[test]
    fn opposite_polarities_are_refused_in_both_orders()
    {
        let core = CoreArena::new();
        let mut domain = DomainArena::new();
        let value = domain.value_unit(TermFace::Reduced);
        let computation = domain.comp_return(value, crate::CompTermFace::Reduced);
        let chain = crate::LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = crate::Definitions::new(&chain, &environment, environment.root());
        for (left, right) in [
            (Glued::Value(value), Glued::Computation(computation)),
            (Glued::Computation(computation), Glued::Value(value)),
        ] {
            assert_eq!(
                Err(super::ConversionFault::Polarity),
                super::plan(&core, &domain, definitions, &Frozen::default(), left, right)
            );
        }
    }
}
