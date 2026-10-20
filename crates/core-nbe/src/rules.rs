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
use crate::domain::Projector;
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
            ConversionSide::Left => &self.left,
            ConversionSide::Right => &self.right,
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body scans the side's frozen set for the constant once; the check counts it once"
        )
    )]
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
            ConversionSide::Left => &mut self.left,
            ConversionSide::Right => &mut self.right,
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
    /// A held endpoint whose computation is stuck on a defined constant the
    /// goal may unfold: the endpoint's only rule is that unfolding.
    Endpoint(ConstantIndex),
    /// A held endpoint whose computation is stuck on a call no unfolding
    /// reaches — a variable, a module form, an opaque declaration — so it
    /// compares whole, as the kernel compares two α-equal sides.
    Held,
    /// A hole or a mark, or an endpoint with no unfolding left to the goal:
    /// what it stands for is not decided here, so nothing the goal finds is a
    /// verdict.
    Indeterminate,
}

/// One subgoal of a decomposition, as the rule names it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Subgoal
{
    /// Two values, compared as they stand.
    Values(DomainValueId, DomainValueId),
    /// Two closures, compared once both are opened under one fresh variable.
    Opened(CompClosureId, CompClosureId),
    /// Two closed types quoted as codes at the goal's depth: the complete
    /// nominal classifiers captured by two constructor values, or two
    /// telescope motives, whose arrows bind their own entries.
    Classifiers(crate::arena::ValueClosureId, crate::arena::ValueClosureId),
    /// Two case motives, quoted under the same fresh scrutinee variable.
    CaseMotives(CompClosureId, CompClosureId),
    /// Two transport motives, quoted under the same fresh endpoint variable.
    Motives(crate::arena::ValueClosureId, crate::arena::ValueClosureId),
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
    /// Two fixpoints, each its own source closed over its environment,
    /// compared as weak heads: a stuck fixpoint's place in a spine.
    Fixpoints(CompClosureId, CompClosureId),
    /// The bodies of two fixpoints, opened under one fresh self variable.
    FixpointBodies(CompClosureId, CompClosureId),
    /// The bodies of two splits of one arity, opened under one fresh variable
    /// per component.
    SplitBodies(CompClosureId, CompClosureId),
    /// Two branch bodies entered without adding a binder.
    Entered(CompClosureId, CompClosureId),
    /// Two closures opened under this many fresh variables, outermost first:
    /// List cell branches under head then folded-result binders.
    OpenedUnder(
        CompClosureId,
        CompClosureId,
        gandr_core_term::ComponentCount,
    ),
    /// The first eliminations of two neutrals headed by returned endpoints,
    /// each applied to one fresh variable: the continuations of the binds the
    /// kernel reads over the endpoints' calls.
    Continued(NeutralId, NeutralId),
    /// A tuple's component or a record's field against the same projection
    /// of a neutral: η, the neutral read as the tuple or record of its own
    /// projections.
    Projected
    {
        /// The side the neutral stands on.
        side: ConversionSide,
        /// The neutral, in value position.
        neutral: NeutralId,
        /// What the projection selects.
        projector: Projector,
        /// The component or field on the other side.
        field: DomainValueId,
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
    /// Bind the neutral on this side, one bind short of the other, into
    /// `return`: the η law of `F`.
    ReturnEta(ConversionSide),
    /// Make the two binds in a row nearest the head on this side one: bind
    /// associativity.
    Reassociate(ConversionSide),
    /// Read two held endpoints as the computations they hold: the kernel's
    /// replay reads a returned endpoint so before any rule, recording
    /// nothing.
    Returned,
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
            Self::Same => (
                Combination::Biased,
                Vec::from([
                    Move::Shortcut,
                    Move::FreezeUnfold(ConversionSide::Left),
                    Move::PostponeUnfold(ConversionSide::Left),
                ]),
            ),
            Self::Different => (
                Combination::Biased,
                Vec::from([
                    Move::FreezeUnfold(ConversionSide::Left),
                    Move::PostponeUnfold(ConversionSide::Left),
                ]),
            ),
            Self::Frozen { defined } => (
                Combination::Either,
                Vec::from([Move::Shortcut, Move::Unfold(defined)]),
            ),
            Self::Lambda { defined } => (
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
    /// A sum case with this many branches.
    Case(usize),
    /// A split binding this many components.
    Split(gandr_core_term::ComponentCount),
    /// An exact record label or tuple component.
    Projection(ProjectionKey<'core>),
    /// A stuck fixpoint holding this many leading arguments.
    Fixpoint(usize),
}

/// The selector a native projection retains: a record's exact label or a
/// tuple's component.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectionKey<'core>
{
    /// A record projection's exact label.
    Label(&'core gandr_core_term::FieldLabel),
    /// A tuple projection's component.
    Component(gandr_core_term::Component),
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

/// Resolve the arity and body a split capture closes over.
///
/// # Specification
/// - requires: nothing; stale and ill-shaped captures are refused.
/// - ensures: returns the source split's arity and its body, scoped under one
///   binder per component.
/// - fails: a dangling closure or a body that is not a source split.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two stuck splits compare by their arities and their
///   bodies opened under one variable per component.
/// - witness: `machine::tests::stuck_splits_compare_by_arity_and_body`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)))]
pub fn split_source(
    core: &CoreArena,
    domain: &DomainArena,
    closure: CompClosureId,
) -> Result<
    (
        gandr_core_term::ComponentCount,
        gandr_core_term::ComputationId,
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
    let Some(&gandr_core_term::Computation::Split { arity, body, .. }) = core.computation(source)
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    Ok((arity, body))
}

/// Resolve the body a fixpoint capture closes over.
///
/// # Specification
/// - requires: nothing; stale and ill-shaped captures are refused.
/// - ensures: returns the source fixpoint's body, scoped under its self binder.
/// - fails: a dangling closure or a body that is not a source fixpoint.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two stuck fixpoints compare by their bodies opened under
///   one self variable, and the trace replays.
/// - witness: `machine::tests::stuck_fixpoints_compare_by_their_bodies`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(ConversionFault::Domain(DomainFault::Dangling) | ConversionFault::MachineInvariant)))]
pub fn fixpoint_source(
    core: &CoreArena,
    domain: &DomainArena,
    closure: CompClosureId,
) -> Result<gandr_core_term::ComputationId, ConversionFault>
{
    let closure = domain
        .comp_closure(closure)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    let crate::closure::CompBody::Source(source) = closure.body()
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    let Some(&gandr_core_term::Computation::Fixpoint { body, .. }) = core.computation(source)
    else {
        return Err(ConversionFault::MachineInvariant);
    };
    Ok(body)
}

/// Read the exact selector of a native projection: a record's label or a
/// tuple's component.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the label the source projection names, with no spelling
///   normalization, or its component; a minted component as it stands; a minted
///   field's label at its position among the record's labels.
/// - fails: a missing source, a non-projection body, a record source that is no
///   record, or a position past the record's last label.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unlike labels remain unlike even on one neutral record,
///   and unlike components on one neutral tuple; a minted selector names the
///   label or component a written one would.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
/// - witness: `machine::tests::tuple_projections_of_one_neutral_compare_by_component`
/// - witness: `machine::tests::a_tuple_of_a_neutrals_projections_is_the_neutral_715`
#[spec(ensures: |ret| match projector {
    Projector::Source(source) => match core.computation(source) {
        Some(&gandr_core_term::Computation::RecordProjection(_, ref label)) => ret == Ok(ProjectionKey::Label(label)),
        Some(&gandr_core_term::Computation::TupleProjection(_, component)) => ret == Ok(ProjectionKey::Component(component)),
        Some(_) | None => ret == Err(ConversionFault::MachineInvariant),
    },
    Projector::Component(component) => ret == Ok(ProjectionKey::Component(component)),
    Projector::Field { record, at } => match core.value(record) {
        Some(&Value::Record(ref labels)) => labels.keys().nth(usize::from(at))
            .map_or_else(|| ret == Err(ConversionFault::MachineInvariant), |label| ret == Ok(ProjectionKey::Label(label))),
        Some(_) | None => ret == Err(ConversionFault::MachineInvariant),
    },
})]
pub fn projection_key(
    core: &CoreArena,
    projector: Projector,
) -> Result<ProjectionKey<'_>, ConversionFault>
{
    match projector {
        Projector::Source(source) => match core.computation(source) {
            Some(&gandr_core_term::Computation::RecordProjection(_, ref label)) => {
                Ok(ProjectionKey::Label(label))
            },
            Some(&gandr_core_term::Computation::TupleProjection(_, component)) => {
                Ok(ProjectionKey::Component(component))
            },
            _ => Err(ConversionFault::MachineInvariant),
        },
        Projector::Component(component) => Ok(ProjectionKey::Component(component)),
        Projector::Field { record, at } => match core.value(record) {
            Some(&Value::Record(ref labels)) => labels
                .keys()
                .nth(usize::from(at))
                .map(ProjectionKey::Label)
                .ok_or(ConversionFault::MachineInvariant),
            Some(_) | None => Err(ConversionFault::MachineInvariant),
        },
    }
}

/// Read only metadata that controls a neutral elimination's premise shape.
///
/// # Specification
/// - requires: nothing.
/// - ensures: nominal and sum-case arity and exact labels remain part of shape
///   equality.
/// - fails: malformed native captures, as the source readers report.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — equal-length spines can still differ by labels or case
///   arity.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
#[spec(ensures:|ret| match elimination {
    Elimination::DataCase(closure) => ret == case_source(core,domain,closure).map(|(_,branches)| EliminationShape::DataCase(branches.len())),
    Elimination::Projection(source) => ret == projection_key(core,source).map(EliminationShape::Projection),
    Elimination::Split(closure) => ret == split_source(core,domain,closure).map(|(arity,_)| EliminationShape::Split(arity)),
    Elimination::Case(branches) => ret == domain.branches(branches).map(|held| EliminationShape::Case(held.len())).map_err(ConversionFault::Domain),
    Elimination::Fixpoint { leading, .. } => ret == domain.fields(leading).map(|held| EliminationShape::Fixpoint(held.len())).map_err(ConversionFault::Domain),
    Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::PathTransport { .. } | Elimination::Ride { .. } | Elimination::TelescopeTransport { .. } | Elimination::Apply(_) | Elimination::Force | Elimination::Bind(_) | Elimination::ListFold { .. } | Elimination::StaticApply(_) => ret == Ok(EliminationShape::Ordinary(core::mem::discriminant(&elimination))),
})]
fn elimination_shape<'core>(
    core: &'core CoreArena,
    domain: &DomainArena,
    elimination: Elimination,
) -> Result<EliminationShape<'core>, ConversionFault>
{
    match elimination {
        Elimination::DataCase(closure) => case_source(core, domain, closure)
            .map(|(_, branches)| EliminationShape::DataCase(branches.len())),
        Elimination::Projection(source) => {
            projection_key(core, source).map(EliminationShape::Projection)
        },
        Elimination::Split(closure) => {
            split_source(core, domain, closure).map(|(arity, _)| EliminationShape::Split(arity))
        },
        Elimination::Case(branches) => domain
            .branches(branches)
            .map(|held| EliminationShape::Case(held.len()))
            .map_err(ConversionFault::Domain),
        Elimination::Fixpoint { leading, .. } => domain
            .fields(leading)
            .map(|held| EliminationShape::Fixpoint(held.len()))
            .map_err(ConversionFault::Domain),
        Elimination::Transport(_)
        | Elimination::ProductTransport(_)
        | Elimination::PathTransport { .. }
        | Elimination::Ride { .. }
        | Elimination::TelescopeTransport { .. }
        | Elimination::Apply(_)
        | Elimination::Force
        | Elimination::Bind(_)
        | Elimination::ListFold { .. }
        | Elimination::StaticApply(_) => Ok(EliminationShape::Ordinary(core::mem::discriminant(
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
        ConversionSide::Left => ConversionSide::Right,
        ConversionSide::Right => ConversionSide::Left,
    }
}

/// What a neutral's head is to a goal with `frozen` on `side`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Head::Indeterminate`] for a hole or a mark; [`Head::Rigid`] for
///   a variable, a module form, or a constant with a rigid unfolding face;
///   [`Head::Frozen`] when the goal froze the constant on `side` and
///   [`Head::Defined`] when it did not; for a returned endpoint, the reading
///   [`endpoint_head`] gives its computation.
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
///   unfolding face changes classification. A hole head reads as indeterminate,
///   never rigid, and a held endpoint reads as the definition it is stuck on.
/// - witness: `rules::tests::freezing_is_idempotent_and_local_to_one_side`
/// - witness: `live::tests::a_comparison_that_meets_a_hole_declines`
/// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
#[spec(ensures: |ret| domain.neutral(neutral).map_or_else(
    || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
    |node| match (node.head(), node.unfolding()) {
        (NeutralHead::Constant(constant), Unfolding::Unforced(_) | Unfolding::Forced(_)) =>
            ret == Ok(if frozen.holds(side, constant) == Membership::Held {
                Head::Frozen(constant)
            } else { Head::Defined(constant) }),
        (NeutralHead::Hole { .. } | NeutralHead::Mark { .. }, _) => ret == Ok(Head::Indeterminate),
        (NeutralHead::Returned(computation), _) => ret == endpoint_head(domain, frozen, side, computation),
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
        (NeutralHead::Constant(constant), Unfolding::Unforced(_) | Unfolding::Forced(_)) => {
            match frozen.holds(side, constant) {
                Membership::Held => Head::Frozen(constant),
                Membership::Absent => Head::Defined(constant),
            }
        },
        (NeutralHead::Constant(_), Unfolding::Rigid)
        | (NeutralHead::Variable { .. } | NeutralHead::Module(_), _) => Head::Rigid,
        (NeutralHead::Hole { .. } | NeutralHead::Mark { .. }, _) => Head::Indeterminate,
        (NeutralHead::Returned(computation), _) => {
            return endpoint_head(domain, frozen, side, computation);
        },
    })
}

/// What a returned endpoint over `computation` is to a goal with `frozen` on
/// `side`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Head::Endpoint`] when the neutral [`held_call`] reaches from
///   `computation` is headed by a constant whose body is at hand — unforced, or
///   forced to a value — and the goal has not frozen it on `side`;
///   [`Head::Held`] when that neutral is headed by a variable, a module form,
///   or a constant with no body; [`Head::Indeterminate`] otherwise.
/// - provides: the held endpoint's reading: only a [`crate::Endpoints::Hold`]
///   run leaves a computation stuck on a definition it could unfold, and the
///   goal's one rule there is that unfolding. An endpoint stuck where no
///   unfolding reaches is the call it stands for, and compares whole.
/// - fails: [`ConversionFault::Domain`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint held at a definition unfolds by a recorded
///   step the kernel replays, also when the definition is held inside another
///   held endpoint's elimination; an endpoint held at a fixpoint stuck on a
///   variable converts with the same call; an endpoint stuck on a hole still
///   declines. Reading the first or the second as indeterminate declines the
///   conversion, and reading the third as held compares what has no meaning
///   yet.
/// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
/// - witness: `machine::tests::a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on_361`
/// - witness: `machine::tests::a_bind_over_a_stuck_call_reads_through_its_continuation_369`
/// - witness: `live::tests::a_comparison_that_meets_a_hole_declines`
/// - witness: `rules::tests::a_returned_endpoint_over_a_frozen_call_is_indeterminate_on_that_side`
#[spec(ensures: |ret| match held_call(domain, computation) {
    | Err(fault) => ret == Err(fault),
    | Ok(None) => ret == Ok(Head::Indeterminate),
    | Ok(Some(neutral)) => match domain.neutral(neutral) {
        | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        | Some(node) => match (node.head(), node.unfolding()) {
            (NeutralHead::Constant(constant), Unfolding::Unforced(_) | Unfolding::Forced(Glued::Value(_)))
                if frozen.holds(side, constant) == Membership::Absent => ret == Ok(Head::Endpoint(constant)),
            (NeutralHead::Constant(_), Unfolding::Rigid) | (NeutralHead::Variable { .. } | NeutralHead::Module(_), _) =>
                ret == Ok(Head::Held),
            _ => ret == Ok(Head::Indeterminate),
        },
    },
})]
fn endpoint_head(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    computation: DomainCompId,
) -> Result<Head, ConversionFault>
{
    let Some(neutral) = held_call(domain, computation)?
    else {
        return Ok(Head::Indeterminate);
    };
    let held = domain
        .neutral(neutral)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    Ok(match (held.head(), held.unfolding()) {
        (
            NeutralHead::Constant(constant),
            Unfolding::Unforced(_) | Unfolding::Forced(Glued::Value(_)),
        ) if frozen.holds(side, constant) == Membership::Absent => Head::Endpoint(constant),
        (NeutralHead::Constant(_), Unfolding::Rigid)
        | (NeutralHead::Variable { .. } | NeutralHead::Module(_), _) => Head::Held,
        _ => Head::Indeterminate,
    })
}

/// The neutral a returned endpoint over `computation` waits on: the
/// computation's own neutral, or, when that neutral eliminates another
/// returned endpoint, the neutral that one waits on, and so on inward.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` of the first neutral, read inward from `computation`
///   through each returned head, whose head is not a returned endpoint; in
///   particular `computation`'s own neutral when its head is not one; `None`
///   when the walk meets a computation that is not neutral.
/// - provides: the call a nested endpoint is stuck on. `f(g(x))` with both
///   calls held unfolds `f` first; `f`'s body then eliminates the endpoint
///   `g(x)` and sticks on it, and the call that unsticks the whole is `g`.
/// - fails: [`ConversionFault::Domain`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
///
/// # Termination
/// - reason: the `loop` below, reading one returned head per turn, not
///   recursion.
/// - measure: the allocation position of the node read. A neutral names its
///   returned head's computation, and a computation its neutral, only once that
///   node is minted, and the arena only appends, so each turn reads a node
///   minted before the last.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint whose elimination waits on another held
///   endpoint unfolds the inner call and the kernel replays it; stopping at the
///   first returned head reads the endpoint as indeterminate and declines the
///   conversion.
/// - witness: `machine::tests::a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on_361`
/// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
#[spec(ensures: |ret| match domain.computation(computation) {
    | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
    | Some(&DomainComp::Neutral { neutral, .. }) => match domain.neutral(neutral) {
        | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        | Some(node) if !matches!(node.head(), NeutralHead::Returned(_)) => ret == Ok(Some(neutral)),
        | Some(_) => ret.as_ref().is_ok_and(|found| found.is_none_or(|inner| domain.neutral(inner)
            .is_some_and(|node| !matches!(node.head(), NeutralHead::Returned(_)))))
            || matches!(ret, Err(ConversionFault::Domain(DomainFault::Dangling))),
    },
    | Some(_) => ret == Ok(None),
})]
pub fn held_call(
    domain: &DomainArena,
    computation: DomainCompId,
) -> Result<Option<NeutralId>, ConversionFault>
{
    let mut focus = computation;
    loop {
        let DomainComp::Neutral { neutral, .. } = *domain
            .computation(focus)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?
        else {
            return Ok(None);
        };
        let held = domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        match held.head() {
            NeutralHead::Returned(inner) => focus = inner,
            NeutralHead::Constant(_)
            | NeutralHead::Variable { .. }
            | NeutralHead::Module(_)
            | NeutralHead::Hole { .. }
            | NeutralHead::Mark { .. } => return Ok(Some(neutral)),
        }
    }
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
///   as two opened pairs left first, a stuck fixpoint as its two fixpoints, and
///   a force as nothing, in spine order innermost first; [`Spines::Disagree`]
///   when a length or a kind differs. The heads are not compared.
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
                EliminationShape::Case(branches) => branches,
                EliminationShape::Split(_) => 1_usize,
                EliminationShape::Fixpoint(leading) => leading.saturating_add(1_usize),
                EliminationShape::Ordinary(_) => match a { Elimination::Force => 0_usize,Elimination::ListFold { .. } | Elimination::PathTransport { .. } | Elimination::Ride { .. } => 2_usize,Elimination::TelescopeTransport { .. } => 4_usize,Elimination::DataCase(_) | Elimination::Split(_) | Elimination::Projection(_) | Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::Apply(_) | Elimination::Bind(_) | Elimination::Case(_) | Elimination::StaticApply(_) | Elimination::Fixpoint { .. } => 1_usize },
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
    eliminations_subgoals(core, domain, one.spine(), other.spine())
}

/// The subgoals of two runs of eliminations compared one by one, as
/// [`spine_subgoals`] compares two whole spines.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Spines::Disagree`] when the runs differ in length; otherwise as
///   [`spine_subgoals`], over the runs given rather than a neutral's spine.
/// - provides: the premises of a spine and of the part of one past its first
///   elimination.
/// - fails: [`ConversionFault::Domain`] when an operand does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — an operand does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — as [`spine_subgoals`], whose whole spines it compares;
///   two held eliminations of one held call compare the eliminations past their
///   first by it.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
/// - witness: `machine::tests::two_held_eliminations_of_one_call_compare_by_their_parts_879`
#[spec(ensures: |ret| ret.is_err() || ret == Ok(Spines::Disagree) || left.len() == right.len())]
fn eliminations_subgoals(
    core: &CoreArena,
    domain: &DomainArena,
    left: &[Elimination],
    right: &[Elimination],
) -> Result<Spines, ConversionFault>
{
    if left.len() != right.len() {
        return Ok(Spines::Disagree);
    }
    let mut subgoals = Vec::new();
    for (&left_elimination, &right_elimination) in left.iter().zip(right) {
        let shape = elimination_shape(core, domain, left_elimination)?;
        if shape != elimination_shape(core, domain, right_elimination)? {
            return Ok(Spines::Disagree);
        }
        match (left_elimination, right_elimination) {
            (Elimination::DataCase(left), Elimination::DataCase(right)) => {
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
            (Elimination::Projection(_), Elimination::Projection(_))
            | (Elimination::Force, Elimination::Force) => {},
            (Elimination::Transport(left_argument), Elimination::Transport(right_argument))
            | (
                Elimination::ProductTransport(left_argument),
                Elimination::ProductTransport(right_argument),
            )
            | (Elimination::Apply(left_argument), Elimination::Apply(right_argument))
            | (Elimination::StaticApply(left_argument), Elimination::StaticApply(right_argument)) =>
            {
                subgoals.push(Subgoal::Values(left_argument, right_argument));
            },
            (
                Elimination::PathTransport {
                    motive: left_motive,
                    value: left_value,
                },
                Elimination::PathTransport {
                    motive: right_motive,
                    value: right_value,
                },
            )
            | (
                Elimination::Ride {
                    motive: left_motive,
                    value: left_value,
                },
                Elimination::Ride {
                    motive: right_motive,
                    value: right_value,
                },
            ) => {
                subgoals.push(Subgoal::Motives(left_motive, right_motive));
                subgoals.push(Subgoal::Values(left_value, right_value));
            },
            // A telescope motive binds through its own arrows, so it compares
            // as a code at the spine's depth, the way captured classifiers do.
            (
                Elimination::TelescopeTransport {
                    motive: left_motive,
                    start: left_start,
                    over: left_over,
                    value: left_value,
                },
                Elimination::TelescopeTransport {
                    motive: right_motive,
                    start: right_start,
                    over: right_over,
                    value: right_value,
                },
            ) => {
                subgoals.extend([
                    Subgoal::Classifiers(left_motive, right_motive),
                    Subgoal::Values(left_start, right_start),
                    Subgoal::Values(left_over, right_over),
                    Subgoal::Values(left_value, right_value),
                ]);
            },
            (Elimination::Bind(left_body), Elimination::Bind(right_body)) => {
                subgoals.push(Subgoal::Opened(left_body, right_body));
            },
            (Elimination::Split(left_split), Elimination::Split(right_split)) => {
                subgoals.push(Subgoal::SplitBodies(left_split, right_split));
            },
            (
                Elimination::Fixpoint {
                    recursive: left_fixpoint,
                    leading: left_leading,
                },
                Elimination::Fixpoint {
                    recursive: right_fixpoint,
                    leading: right_leading,
                },
            ) => {
                subgoals.push(Subgoal::Fixpoints(left_fixpoint, right_fixpoint));
                let right_leading = domain
                    .fields(right_leading)
                    .map_err(ConversionFault::Domain)?;
                subgoals.extend(
                    domain
                        .fields(left_leading)
                        .map_err(ConversionFault::Domain)?
                        .iter()
                        .zip(right_leading)
                        .map(|(&one, &other)| Subgoal::Values(one, other)),
                );
            },
            (
                Elimination::ListFold {
                    on_nil: ln,
                    on_cons: lc,
                    ..
                },
                Elimination::ListFold {
                    on_nil: rn,
                    on_cons: rc,
                    ..
                },
            ) => {
                subgoals.push(Subgoal::Entered(ln, rn));
                subgoals.push(Subgoal::OpenedUnder(
                    lc,
                    rc,
                    gandr_core_term::ComponentCount::from(2_usize),
                ));
            },
            (Elimination::Case(left_branches), Elimination::Case(right_branches)) => {
                let left_branches = domain
                    .branches(left_branches)
                    .map_err(ConversionFault::Domain)?;
                let right_branches = domain
                    .branches(right_branches)
                    .map_err(ConversionFault::Domain)?;
                subgoals.extend(left_branches.iter().zip(right_branches).map(
                    |(&left_branch, &right_branch)| Subgoal::Opened(left_branch, right_branch),
                ));
            },
            (
                Elimination::Transport(_)
                | Elimination::DataCase(_)
                | Elimination::Split(_)
                | Elimination::Projection(_)
                | Elimination::ProductTransport(_)
                | Elimination::PathTransport { .. }
                | Elimination::Ride { .. }
                | Elimination::TelescopeTransport { .. }
                | Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Bind(_)
                | Elimination::Case(_)
                | Elimination::ListFold { .. }
                | Elimination::StaticApply(_)
                | Elimination::Fixpoint { .. },
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
        (Glued::Value(one), Glued::Value(other)) => {
            plan_values(core, domain, definitions, frozen, one, other)
        },
        (Glued::Computation(one), Glued::Computation(other)) => {
            plan_comps(core, domain, frozen, one, other)
        },
        (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => {
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
/// - ensures: [`Constants::Planned`] with a forced unfolding of a held
///   endpoint's definition, the left before the right, when either head is
///   [`Head::Endpoint`]; otherwise the §6.1 rule for the two heads when either
///   is [`Head::Defined`], the §6.2 choice for a lambda against a defined
///   computation, and a forced unfolding of the defined side against anything
///   else; [`Constants::NoneDefined`] when neither head is defined or held.
/// - provides: the constant half of the table, shared by both polarities. A
///   held endpoint offers no choice: its computation runs only by that
///   unfolding, so the step is forced and recorded as one.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — equal and different defined heads select different
///   unfolding choices, a defined head meets a lambda through frozen eta, a
///   defined head against a former must unfold, and a held endpoint unfolds
///   before any choice; ignoring a defined side or choosing the wrong side
///   changes the winning trace.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
/// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
/// - witness: `rules::tests::a_defined_head_meets_its_frozen_twin_only_at_one_constant_and_arity`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |planned|
    matches!(planned, Constants::NoneDefined) != matches!(heads,
        (Neutrality::Neutral(_, Head::Defined(_) | Head::Endpoint(_)), _)
        | (_, Neutrality::Neutral(_, Head::Defined(_) | Head::Endpoint(_))))
    && match heads {
        (Neutrality::Neutral(_, Head::Endpoint(_)), _) => *planned == Constants::Planned(Plan::Step(Step::Unfold(ConversionSide::Left))),
        (_, Neutrality::Neutral(_, Head::Endpoint(_))) => *planned == Constants::Planned(Plan::Step(Step::Unfold(ConversionSide::Right))),
        _ => true,
    }))]
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
        (Neutrality::Neutral(_, Head::Endpoint(_)), _) => {
            Plan::Step(Step::Unfold(ConversionSide::Left))
        },
        (_, Neutrality::Neutral(_, Head::Endpoint(_))) => {
            Plan::Step(Step::Unfold(ConversionSide::Right))
        },
        (
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
        (
            Neutrality::Neutral(_, Head::Defined(one)),
            Neutrality::Neutral(_, Head::Frozen(other)),
        ) if one == other && arity == Arity::Same => Plan::Choose(Choice::Frozen {
            defined: ConversionSide::Left,
        }),
        (
            Neutrality::Neutral(_, Head::Frozen(one)),
            Neutrality::Neutral(_, Head::Defined(other)),
        ) if one == other && arity == Arity::Same => Plan::Choose(Choice::Frozen {
            defined: ConversionSide::Right,
        }),
        (Neutrality::Neutral(_, Head::Defined(_)), _) => match lambda {
            Lambda::Right => Plan::Choose(Choice::Lambda {
                defined: ConversionSide::Left,
            }),
            Lambda::Left | Lambda::Neither => Plan::Step(Step::Unfold(ConversionSide::Left)),
        },
        (_, Neutrality::Neutral(_, Head::Defined(_))) => match lambda {
            Lambda::Left => Plan::Choose(Choice::Lambda {
                defined: ConversionSide::Right,
            }),
            Lambda::Right | Lambda::Neither => Plan::Step(Step::Unfold(ConversionSide::Right)),
        },
        (
            Neutrality::Former
            | Neutrality::Neutral(
                _,
                Head::Rigid | Head::Frozen(_) | Head::Held | Head::Indeterminate,
            ),
            Neutrality::Former
            | Neutrality::Neutral(
                _,
                Head::Rigid | Head::Frozen(_) | Head::Held | Head::Indeterminate,
            ),
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
/// - ensures: when the heads are one head, the commuting conversion of `F`
///   [`bind_step`] names first, as [`Step::Reassociate`] or
///   [`Step::ReturnEta`]; else [`Plan::Decompose`] over [`spine_subgoals`] when
///   the spines are one shape — `var-1`; [`Plan::Leaf`] refuting otherwise —
///   `var-2`.
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
///   independently replayable traces; a neutral against its bind into `return`
///   and two binds against their reassociation convert only by the bind steps,
///   never by a positional refutation.
/// - witness: `machine::tests::native_records_cases_and_traces_agree`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
#[spec(ensures: |ret| match (domain.neutral(left),domain.neutral(right)) {
    (Some(one),Some(other)) if one.head() != other.head() => ret == Ok(Plan::Leaf(Settled::NotConvertible)),
    (Some(one),Some(other)) => match bind_step(one.spine(), other.spine()) {
        BindStep::Reassociate(side) => ret == Ok(Plan::Step(Step::Reassociate(side))),
        BindStep::ReturnEta(side) => ret == Ok(Plan::Step(Step::ReturnEta(side))),
        BindStep::Normal => match spine_subgoals(core,domain,left,right) {
            Ok(Spines::Agree(subgoals)) => ret == Ok(Plan::Decompose(subgoals)),
            Ok(Spines::Disagree) => ret == Ok(Plan::Leaf(Settled::NotConvertible)),
            Err(fault) => ret == Err(fault),
        },
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
    match bind_step(one.spine(), other.spine()) {
        BindStep::Reassociate(side) => return Ok(Plan::Step(Step::Reassociate(side))),
        BindStep::ReturnEta(side) => return Ok(Plan::Step(Step::ReturnEta(side))),
        BindStep::Normal => {},
    }
    let spines = spine_subgoals(core, domain, left, right)?;
    Ok(match spines {
        Spines::Agree(subgoals) => Plan::Decompose(subgoals),
        Spines::Disagree => Plan::Leaf(Settled::NotConvertible),
    })
}

/// The commuting conversion of `F` two spines over one head owe before they
/// compare position by position.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BindStep
{
    /// Neither law applies: the spines compare position by position.
    Normal,
    /// The side stacks two binds in a row: make them one.
    Reassociate(ConversionSide),
    /// The side is one bind short of the other: bind it into `return`.
    ReturnEta(ConversionSide),
}

/// The commuting conversion of `F` two spines over one head owe first.
///
/// # Specification
/// - requires: the spines hang off one head.
/// - ensures: [`BindStep::Reassociate`] naming the first side whose spine
///   stacks two binds in a row, the left before the right; else
///   [`BindStep::ReturnEta`] naming the side whose spine is one elimination
///   shorter than the other's when the other's ends in a bind; else
///   [`BindStep::Normal`].
/// - provides: the order the engine normalizes a pair's binds in, which is the
///   kernel replay's `bind_rule`, so every rewrite is recorded where the replay
///   meets it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a stacked pair on either side, and a side one bind short
///   on either side, each select their own step, and the kernel replays the
///   engine's trace only when both read the same order.
/// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
#[spec(ensures: |ret| {
    let stacked = |spine: &[Elimination]| spine.windows(2).any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]));
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    ret == if stacked(left) {
        BindStep::Reassociate(ConversionSide::Left)
    } else if stacked(right) {
        BindStep::Reassociate(ConversionSide::Right)
    } else if left.len().checked_add(1) == Some(right.len()) && ends(right) {
        BindStep::ReturnEta(ConversionSide::Left)
    } else if right.len().checked_add(1) == Some(left.len()) && ends(left) {
        BindStep::ReturnEta(ConversionSide::Right)
    } else {
        BindStep::Normal
    }
})]
pub fn bind_step(
    left: &[Elimination],
    right: &[Elimination],
) -> BindStep
{
    let stacked = |spine: &[Elimination]| {
        spine
            .windows(2)
            .any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
    };
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    if stacked(left) {
        return BindStep::Reassociate(ConversionSide::Left);
    }
    if stacked(right) {
        return BindStep::Reassociate(ConversionSide::Right);
    }
    if left.len().checked_add(1) == Some(right.len()) && ends(right) {
        return BindStep::ReturnEta(ConversionSide::Left);
    }
    if right.len().checked_add(1) == Some(left.len()) && ends(left) {
        return BindStep::ReturnEta(ConversionSide::Right);
    }
    BindStep::Normal
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
    DomainValue::Constructor { .. } | DomainValue::Record { .. } | DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. } | DomainValue::Here { .. } | DomainValue::Univalence { .. } | DomainValue::HeldTransport { .. } | DomainValue::Flow { .. } | DomainValue::Literal { .. } | DomainValue::Tuple { .. } | DomainValue::ListNil { .. } | DomainValue::ListCons { .. } | DomainValue::Injection { .. } | DomainValue::Thunk { .. } | DomainValue::Lift { .. } | DomainValue::Code { .. } | DomainValue::StaticLambda { .. } => ret == Ok(Neutrality::Former),
})]
fn value_neutrality(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    value: DomainValue,
) -> Result<Neutrality, ConversionFault>
{
    Ok(match value {
        DomainValue::Neutral { neutral, .. } => {
            let read = head(domain, frozen, side, neutral)?;
            Neutrality::Neutral(neutral, read)
        },
        DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Univalence { .. }
        | DomainValue::HeldTransport { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
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
///   neutral computation; [`Neutrality::Former`] for a lambda, a returner or a
///   fixpoint.
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
    DomainComp::Lambda { .. } | DomainComp::Return { .. } | DomainComp::Fixpoint { .. } => ret == Ok(Neutrality::Former),
})]
fn comp_neutrality(
    domain: &DomainArena,
    frozen: &Frozen,
    side: ConversionSide,
    comp: DomainComp,
) -> Result<Neutrality, ConversionFault>
{
    Ok(match comp {
        DomainComp::Neutral { neutral, .. } => {
            let read = head(domain, frozen, side, neutral)?;
            Neutrality::Neutral(neutral, read)
        },
        DomainComp::Lambda { .. } | DomainComp::Return { .. } | DomainComp::Fixpoint { .. } => {
            Neutrality::Former
        },
    })
}

/// Whether a comparison may answer: neither side stands on a hole or a mark.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Determinacy
{
    /// Neither side is indeterminate; the table decides.
    Determinate,
    /// A side stands on a hole or a mark: no verdict is the table's to give.
    Indeterminate,
}

/// Whether either side of a goal stands on a hole or a mark.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Determinacy::Indeterminate`] exactly when either side is a
///   neutral whose head reads [`Head::Indeterminate`].
/// - provides: the rule a goal over a hole takes before any other: a fill may
///   still make the two sides agree or differ, so the goal declines.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hole against a literal, a hole against itself and a
///   pair holding a hole against a pair differing elsewhere separate the
///   decline from a verdict reached past it.
/// - witness: `live::tests::a_comparison_that_meets_a_hole_declines`
#[spec(ensures: |ret| matches!(ret, Determinacy::Indeterminate)
    == (matches!(left, Neutrality::Neutral(_, Head::Indeterminate)) || matches!(right, Neutrality::Neutral(_, Head::Indeterminate))))]
const fn determinacy(
    left: Neutrality,
    right: Neutrality,
) -> Determinacy
{
    match (left, right) {
        (Neutrality::Neutral(_, Head::Indeterminate), _)
        | (_, Neutrality::Neutral(_, Head::Indeterminate)) => Determinacy::Indeterminate,
        (
            Neutrality::Former
            | Neutrality::Neutral(
                _,
                Head::Rigid | Head::Frozen(_) | Head::Defined(_) | Head::Endpoint(_) | Head::Held,
            ),
            Neutrality::Former
            | Neutrality::Neutral(
                _,
                Head::Rigid | Head::Frozen(_) | Head::Defined(_) | Head::Endpoint(_) | Head::Held,
            ),
        ) => Determinacy::Determinate,
    }
}

/// The two sides of a goal a held endpoint stands in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Term
{
    /// A value pair.
    Values(DomainValueId, DomainValueId),
    /// A computation pair.
    Comps(DomainCompId, DomainCompId),
}

/// The plan for a pair with a [`Head::Held`] side: the whole sides compared
/// by [`crate::conv`]'s walk.
///
/// A held endpoint stuck where no unfolding reaches is the call it stands
/// for: two such endpoints over one call are one endpoint, and the kernel
/// closes the shared comparison on the sides the walk found, reading each
/// returned endpoint inside them as the walk did. Two
/// returned endpoints the walk does not equate compare as the computations
/// they hold, as the kernel's replay reads them: the walk compares captured
/// closures by their environments, where the machine opens them under one
/// fresh variable. Two computations that eliminate held endpoints over calls
/// of one head decompose as the kernel reads them, a bind over each call:
/// the calls' spines, the first eliminations under one fresh variable, then
/// the eliminations past them. A held endpoint against any other side
/// declines, since its spine is a computation's, which a decomposition would
/// compare against the other side's term rather than its call.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `None` when neither side is [`Head::Held`]; a shared
///   [`Settled::Convertible`] when the walk finds the sides identical or
///   structurally equal; otherwise [`Step::Returned`] when both sides are
///   values that are returned endpoints with empty spines, the decomposition
///   [`held_eliminations`] gives for two computations it answers, and an
///   [`DeclineReason::Indeterminate`] decline for the rest.
/// - provides: the comparison of a held endpoint against its own call, of two
///   held endpoints whose calls differ only beneath a binder, and of two held
///   eliminations of one call whose operands differ.
/// - fails: as the walk.
/// - panics: none.
///
/// # Errors
/// [`ConversionFault`], as the walk raises.
///
/// # Adequacy
/// - hypothesis: L3 — two endpoints over one fixpoint stuck on a variable
///   convert and the kernel replays the shared comparison; two endpoints over
///   transports whose motives close over different environments convert by
///   their computations; two applications of one fixpoint at one held call, one
///   argument unfolded on one side only, convert by their parts; an endpoint
///   and a different value decline rather than settle apart.
/// - witness: `machine::tests::a_bind_over_a_stuck_call_reads_through_its_continuation_369`
/// - witness: `machine::tests::a_continuation_casing_on_a_stuck_call_stays_whole`
/// - witness: `machine::tests::two_held_transports_convert_by_their_computations`
/// - witness: `machine::tests::two_held_eliminations_of_one_call_compare_by_their_parts_879`
#[spec(ensures: |ret| match ret.as_ref().map(Option::as_ref) {
    Ok(None) => !matches!(heads, (Neutrality::Neutral(_, Head::Held), _) | (_, Neutrality::Neutral(_, Head::Held))),
    Ok(Some(plan)) => matches!(*plan, Plan::Shared(Settled::Convertible) | Plan::Decline(DeclineReason::Indeterminate))
        || (*plan == Plan::Step(Step::Returned) && matches!(term, Term::Values(left, right)
            if matches!((returned(domain, left), returned(domain, right)), (Ok(Some(_)), Ok(Some(_))))))
        || matches!((plan, term), (Plan::Decompose(subgoals), Term::Comps(left, right))
            if held_eliminations(core, domain, left, right).is_ok_and(|held| held.as_ref() == Some(subgoals))),
    Err(_) => true,
})]
fn whole(
    core: &CoreArena,
    domain: &DomainArena,
    heads: (Neutrality, Neutrality),
    term: Term,
) -> Result<Option<Plan>, ConversionFault>
{
    if !matches!(
        heads,
        (Neutrality::Neutral(_, Head::Held), _) | (_, Neutrality::Neutral(_, Head::Held))
    ) {
        return Ok(None);
    }
    let settled = match term {
        Term::Values(left, right) => crate::conv::convert_values(core, domain, left, right)?,
        Term::Comps(left, right) => crate::conv::convert_computations(core, domain, left, right)?,
    };
    Ok(Some(match settled {
        crate::conv::Settlement::Identical | crate::conv::Settlement::StructurallyEqual => {
            Plan::Shared(Settled::Convertible)
        },
        crate::conv::Settlement::GuardedApart
        | crate::conv::Settlement::StructurallyApart
        | crate::conv::Settlement::Deferred(_) => match term {
            Term::Values(left, right)
                if returned(domain, left)?.is_some() && returned(domain, right)?.is_some() =>
            {
                Plan::Step(Step::Returned)
            },
            Term::Comps(left, right) => held_eliminations(core, domain, left, right)?
                .map_or(Plan::Decline(DeclineReason::Indeterminate), Plan::Decompose),
            Term::Values(..) => Plan::Decline(DeclineReason::Indeterminate),
        },
    }))
}

/// The decomposition of two computations that eliminate held endpoints over
/// calls of one head, in the order the kernel's replay reads each as a bind
/// over its call.
///
/// The kernel runs a returned endpoint an elimination inspects first, `E[c]
/// ⇝ c to x. E[x]`, so each side reads as its call's spine, a bind whose
/// continuation is the first elimination over the bound variable, and the
/// eliminations past it. The decomposition compares the calls' spines, the
/// first eliminations under one fresh variable, and the eliminations past
/// them, in that order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when both sides are neutrals headed by returned
///   endpoints, each spine's first elimination is one that inspects its operand
///   (a fixpoint's gate, a case, a split, a fold, a projection, a force) and of
///   one kind on both sides, both endpoints' computations are neutrals over one
///   head that is no returned endpoint, and the calls' spines and the
///   eliminations past the first agree by [`eliminations_subgoals`]; the
///   subgoals are the calls', then [`Subgoal::Continued`], then the rest's.
/// - provides: the premises of two held eliminations of one call.
/// - fails: [`ConversionFault::Domain`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — two applications of one fixpoint at one held call whose
///   second arguments differ by an unfolding convert, and the kernel replays
///   the decomposition; a held bind against a former still declines.
/// - witness: `machine::tests::two_held_eliminations_of_one_call_compare_by_their_parts_879`
/// - witness: `machine::tests::a_continuation_casing_on_a_stuck_call_stays_whole`
#[spec(ensures: |ret| ret.as_ref().ok().and_then(Option::as_ref).is_none_or(|subgoals|
    subgoals.iter().filter(|subgoal| matches!(**subgoal, Subgoal::Continued(..))).count() == 1))]
fn held_eliminations(
    core: &CoreArena,
    domain: &DomainArena,
    left: DomainCompId,
    right: DomainCompId,
) -> Result<Option<Vec<Subgoal>>, ConversionFault>
{
    let (Some(left_held), Some(right_held)) = (
        held_elimination(domain, left)?,
        held_elimination(domain, right)?,
    )
    else {
        return Ok(None);
    };
    let (Some(left_node), Some(right_node)) = (
        domain.neutral(left_held.elimination),
        domain.neutral(right_held.elimination),
    )
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let (Some(left_call), Some(right_call)) = (
        domain.neutral(left_held.call),
        domain.neutral(right_held.call),
    )
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let (Some((&left_first, left_past)), Some((&right_first, right_past))) = (
        left_node.spine().split_first(),
        right_node.spine().split_first(),
    )
    else {
        return Ok(None);
    };
    if left_call.head() != right_call.head()
        || elimination_shape(core, domain, left_first)?
            != elimination_shape(core, domain, right_first)?
    {
        return Ok(None);
    }
    let Spines::Agree(mut subgoals) =
        eliminations_subgoals(core, domain, left_call.spine(), right_call.spine())?
    else {
        return Ok(None);
    };
    let Spines::Agree(past) = eliminations_subgoals(core, domain, left_past, right_past)?
    else {
        return Ok(None);
    };
    subgoals.push(Subgoal::Continued(
        left_held.elimination,
        right_held.elimination,
    ));
    subgoals.extend(past);
    Ok(Some(subgoals))
}

/// A computation that eliminates a held endpoint: its neutral, and the call
/// the endpoint's computation stands at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct HeldElimination
{
    /// The neutral whose head is the returned endpoint.
    elimination: NeutralId,
    /// The neutral the endpoint's computation is.
    call: NeutralId,
}

/// The held elimination `computation` is, when it is one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when `computation` is a neutral headed by a
///   returned endpoint whose first elimination inspects its operand, and the
///   endpoint's computation is a neutral headed by no returned endpoint.
/// - provides: one side of [`held_eliminations`].
/// - fails: [`ConversionFault::Domain`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — as [`held_eliminations`]: an application whose head is a
///   returned endpoint is no elimination the kernel binds over.
/// - witness: `machine::tests::two_held_eliminations_of_one_call_compare_by_their_parts_879`
#[spec(ensures: |ret| ret.as_ref().ok().and_then(Option::as_ref).is_none_or(|held|
    domain.neutral(held.elimination).is_some_and(|node| matches!(node.head(), NeutralHead::Returned(_)))
        && domain.neutral(held.call).is_some_and(|node| !matches!(node.head(), NeutralHead::Returned(_)))))]
fn held_elimination(
    domain: &DomainArena,
    computation: DomainCompId,
) -> Result<Option<HeldElimination>, ConversionFault>
{
    let DomainComp::Neutral {
        neutral: elimination,
        ..
    } = *domain
        .computation(computation)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?
    else {
        return Ok(None);
    };
    let node = domain
        .neutral(elimination)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    let NeutralHead::Returned(inner) = node.head()
    else {
        return Ok(None);
    };
    if !matches!(
        node.spine().first(),
        Some(
            Elimination::Fixpoint { .. }
                | Elimination::DataCase(_)
                | Elimination::Case(_)
                | Elimination::Split(_)
                | Elimination::ListFold { .. }
                | Elimination::Projection(_)
                | Elimination::Force
        )
    ) {
        return Ok(None);
    }
    let DomainComp::Neutral { neutral: call, .. } = *domain
        .computation(inner)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?
    else {
        return Ok(None);
    };
    let held = domain
        .neutral(call)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    if matches!(held.head(), NeutralHead::Returned(_)) {
        return Ok(None);
    }
    Ok(Some(HeldElimination { elimination, call }))
}

/// The computation a value holds when it is a returned endpoint with an empty
/// spine.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` of the computation when `value` is a neutral headed by a
///   returned endpoint and eliminated by nothing; `None` for every other value.
/// - provides: the side [`Step::Returned`] reads as its computation.
/// - fails: [`ConversionFault::Domain`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a node does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — two endpoints over transports whose motives close over
///   different environments read as their computations and convert; reading a
///   neutral with a spine as its head's computation drops the spine.
/// - witness: `machine::tests::two_held_transports_convert_by_their_computations`
#[spec(ensures: |ret| match domain.value(value) {
    | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
    | Some(&DomainValue::Neutral { neutral, .. }) => match domain.neutral(neutral) {
        | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        | Some(node) => match node.head() {
            | NeutralHead::Returned(computation) if node.spine().is_empty() => ret == Ok(Some(computation)),
            | _ => ret == Ok(None),
        },
    },
    | Some(_) => ret == Ok(None),
})]
pub fn returned(
    domain: &DomainArena,
    value: DomainValueId,
) -> Result<Option<DomainCompId>, ConversionFault>
{
    let DomainValue::Neutral { neutral, .. } = *domain
        .value(value)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?
    else {
        return Ok(None);
    };
    let held = domain
        .neutral(neutral)
        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
    Ok(match held.head() {
        NeutralHead::Returned(computation) if held.spine().is_empty() => Some(computation),
        NeutralHead::Returned(_)
        | NeutralHead::Constant(_)
        | NeutralHead::Variable { .. }
        | NeutralHead::Module(_)
        | NeutralHead::Hole { .. }
        | NeutralHead::Mark { .. } => None,
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
        Some(&Value::Literal(ref held)) => Ok(held),
        Some(_) | None => Err(ConversionFault::LiteralPayload { literal }),
    }
}

/// [`plan`] over two values.
///
/// # Specification
/// - requires: nothing — dangling ids are admissible input and refused.
/// - ensures: as [`plan`], over the value formers; two reflexivities that
///   neither share nor separate decompose to their points, and two univalences
///   to their records, the forward map each carries being derived from its
///   record.
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
///   selecting the wrong structural rule changes the verdict or its trace. Two
///   reflexivities whose points are one unfolding apart convert only by the
///   congruence on their points, and stay apart when that unfolding is
///   unavailable.
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
/// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
/// - witness: `identity::tests::reflexivities_convert_by_points_a_definition_relates_345`
/// - witness: `rules::tests::each_former_decomposes_against_its_twin_at_another_id`
/// - witness: `rules::tests::two_flows_of_different_formers_are_planned_apart`
/// - witness: `rules::tests::a_record_with_more_labels_than_fields_is_refused_by_the_plan_on_either_side`
/// - witness: `rules::tests::two_path_products_of_one_path_share_a_convertible_plan`
/// - witness: `rules::tests::two_literals_held_apart_with_one_payload_are_convertible`
#[spec(ensures: |ret| (match early_values(domain, left, right) {
    Ok(Early::Identical) => ret == Ok(Plan::Shared(Settled::Convertible)),
    Ok(Early::Apart) => ret == Ok(Plan::Shared(Settled::NotConvertible)),
    Ok(Early::Open) => true,
    Err(fault) => ret == Err(fault),
}) && match (domain.value(left), domain.value(right)) {
    (Some(&DomainValue::PathCertificate { .. }), Some(&DomainValue::PathProduct { .. })) | (Some(&DomainValue::PathProduct { .. }), Some(&DomainValue::PathCertificate { .. })) => ret == Ok(Plan::Shared(Settled::NotConvertible)),
    (Some(&DomainValue::PathCertificate { certificate: a, .. }), Some(&DomainValue::PathCertificate { certificate: b, .. })) if a == b => ret == Ok(Plan::Shared(Settled::Convertible)),
    (Some(&DomainValue::Here { point: a, .. }), Some(&DomainValue::Here { point: b, .. }))
    | (Some(&DomainValue::Univalence { record: a, .. }), Some(&DomainValue::Univalence { record: b, .. })) => early_values(domain, left, right) != Ok(Early::Open)
        || ret == Ok(Plan::Decompose(Vec::from([Subgoal::Values(a, b)]))),
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
        Early::Identical => return Ok(Plan::Shared(Settled::Convertible)),
        Early::Apart => return Ok(Plan::Shared(Settled::NotConvertible)),
        Early::Open => {},
    }
    let (Some(&one), Some(&other)) = (domain.value(left), domain.value(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let left_head = value_neutrality(domain, frozen, ConversionSide::Left, one)?;
    let right_head = value_neutrality(domain, frozen, ConversionSide::Right, other)?;
    if determinacy(left_head, right_head) == Determinacy::Indeterminate {
        return Ok(Plan::Decline(DeclineReason::Indeterminate));
    }
    let constants = plan_constants(domain, (left_head, right_head), Lambda::Neither)?;
    if let Constants::Planned(planned) = constants {
        return Ok(planned);
    }
    if let Some(planned) = whole(
        core,
        domain,
        (left_head, right_head),
        Term::Values(left, right),
    )? {
        return Ok(planned);
    }
    let planned = match (one, other) {
        (
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
        (
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
        (
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
        (
            DomainValue::Tuple {
                fields: left_fields,
                ..
            },
            DomainValue::Tuple {
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
            if left_fields.len() != right_fields.len() {
                Plan::Leaf(Settled::NotConvertible)
            }
            else if left_fields.is_empty() {
                Plan::Leaf(Settled::Convertible)
            }
            else {
                Plan::Decompose(
                    left_fields
                        .iter()
                        .zip(right_fields)
                        .map(|(a, b)| Subgoal::Values(*a, *b))
                        .collect(),
                )
            }
        },
        (DomainValue::ListNil { .. }, DomainValue::ListNil { .. }) => {
            Plan::Leaf(Settled::Convertible)
        },
        (
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
        (
            DomainValue::ListCons {
                first: left_first,
                second: left_second,
                ..
            },
            DomainValue::ListCons {
                first: right_first,
                second: right_second,
                ..
            },
        ) => Plan::Decompose(Vec::from([
            Subgoal::Values(left_first, right_first),
            Subgoal::Values(left_second, right_second),
        ])),
        (
            DomainValue::Flow {
                former: left_former,
                parts: left_parts,
                ..
            },
            DomainValue::Flow {
                former: right_former,
                parts: right_parts,
                ..
            },
        ) => {
            let left_parts = domain.fields(left_parts).map_err(ConversionFault::Domain)?;
            let right_parts = domain
                .fields(right_parts)
                .map_err(ConversionFault::Domain)?;
            if left_former == right_former && left_parts.len() == right_parts.len() {
                Plan::Decompose(
                    left_parts
                        .iter()
                        .zip(right_parts)
                        .map(|(a, b)| Subgoal::Values(*a, *b))
                        .collect(),
                )
            }
            else {
                Plan::Leaf(Settled::NotConvertible)
            }
        },
        (
            DomainValue::Injection {
                summand: left_summand,
                body: left_body,
                ..
            },
            DomainValue::Injection {
                summand: right_summand,
                body: right_body,
                ..
            },
        ) => {
            if left_summand == right_summand {
                Plan::Decompose(Vec::from([Subgoal::Values(left_body, right_body)]))
            }
            else {
                Plan::Leaf(Settled::NotConvertible)
            }
        },
        (
            DomainValue::Here {
                point: left_point, ..
            },
            DomainValue::Here {
                point: right_point, ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Values(left_point, right_point)])),
        (
            DomainValue::Univalence {
                record: left_record,
                ..
            },
            DomainValue::Univalence {
                record: right_record,
                ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Values(left_record, right_record)])),
        // A held `back` or `then` meets another in the transport that formed
        // each: its family, the path it moved along, then what it moved.
        (
            DomainValue::HeldTransport {
                motive: left_motive,
                path: left_path,
                value: left_value,
                ..
            },
            DomainValue::HeldTransport {
                motive: right_motive,
                path: right_path,
                value: right_value,
                ..
            },
        ) => Plan::Decompose(Vec::from([
            Subgoal::Motives(left_motive, right_motive),
            Subgoal::Values(left_path, right_path),
            Subgoal::Values(left_value, right_value),
        ])),
        (
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
        (DomainValue::Thunk { .. }, DomainValue::Thunk { .. } | DomainValue::Neutral { .. })
        | (DomainValue::Neutral { .. }, DomainValue::Thunk { .. }) => Plan::Step(Step::Force),
        (
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
        (
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
                CodeComparison::Equal => Plan::Shared(Settled::Convertible),
                CodeComparison::Apart => Plan::Shared(Settled::NotConvertible),
                CodeComparison::Undecided => Plan::Decline(DeclineReason::UndecidedCodes),
            }
        },
        // Two static lambdas compare whole by the same α-walk, and a static
        // lambda against a stuck operator is declined: η could relate them,
        // and this rung does not expand an operator.
        (
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
                CodeComparison::Equal => Plan::Shared(Settled::Convertible),
                CodeComparison::Apart => Plan::Shared(Settled::NotConvertible),
                CodeComparison::Undecided => Plan::Decline(DeclineReason::UndecidedCodes),
            }
        },
        (DomainValue::StaticLambda { .. }, DomainValue::Neutral { .. })
        | (DomainValue::Neutral { .. }, DomainValue::StaticLambda { .. }) => {
            Plan::Decline(DeclineReason::UndecidedCodes)
        },
        // A tuple or a record against a rigid neutral compares part by part
        // with the neutral's own projections: η for products and records. A
        // frozen constant meets a former apart here, as the goal's unfolding
        // branch relates them: its projections stay frozen on the same head,
        // and η along them would never reach a verdict.
        (
            former @ (DomainValue::Tuple { .. } | DomainValue::Record { .. }),
            DomainValue::Neutral { neutral, .. },
        ) if matches!(right_head, Neutrality::Neutral(_, Head::Rigid)) => {
            projected(domain, former, neutral, ConversionSide::Right)?
        },
        (
            DomainValue::Neutral { neutral, .. },
            former @ (DomainValue::Tuple { .. } | DomainValue::Record { .. }),
        ) if matches!(left_head, Neutrality::Neutral(_, Head::Rigid)) => {
            projected(domain, former, neutral, ConversionSide::Left)?
        },
        (
            DomainValue::PathCertificate { .. }
            | DomainValue::Constructor { .. }
            | DomainValue::Record { .. }
            | DomainValue::PathProduct { .. }
            | DomainValue::Here { .. }
            | DomainValue::Univalence { .. }
            | DomainValue::HeldTransport { .. }
            | DomainValue::Flow { .. }
            | DomainValue::Tuple { .. }
            | DomainValue::Literal { .. }
            | DomainValue::ListNil { .. }
            | DomainValue::ListCons { .. }
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

/// The η decomposition of a tuple or a record against a rigid neutral: each
/// component or field against the neutral's projection at it, in the order
/// the tuple or the record's labels hold them.
///
/// # Specification
/// - requires: `neutral` stands in value position on `side`, `former` on the
///   other.
/// - ensures: one [`Subgoal::Projected`] per component of a tuple, by
///   [`Projector::Component`], or per field of a record, by
///   [`Projector::Field`] over the record's source labels, in order; a leaf
///   apart for an empty tuple or record and for any other former.
/// - provides: η for products and records.
/// - fails: [`ConversionFault::Domain`] when the fields do not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — the fields do not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — a tuple or record of a neutral's own projections converts
///   to it on either side, and the kernel replays the same premises; swapped
///   components and a different neutral stay apart. A frozen constant against a
///   former is never expanded, so a goal that unfolds back into itself declines
///   on the cycle instead of projecting without end.
/// - witness: `machine::tests::a_tuple_of_a_neutrals_projections_is_the_neutral_715`
/// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
#[spec(ensures: |ret| if let DomainValue::Tuple { fields, .. } | DomainValue::Record { fields, .. } = former {
    domain.fields(fields).map_or_else(|_| ret.is_err(), |held| match ret {
        Ok(Plan::Decompose(ref subgoals)) => !held.is_empty() && subgoals.len() == held.len()
            && subgoals.iter().zip(held).all(|(subgoal, &component)| matches!(*subgoal,
                Subgoal::Projected { side: at, neutral: projected, field, .. } if at == side && projected == neutral && field == component)),
        Ok(Plan::Leaf(Settled::NotConvertible)) => held.is_empty(),
        Ok(_) | Err(_) => false,
    })
} else {
    ret == Ok(Plan::Leaf(Settled::NotConvertible))
})]
fn projected(
    domain: &DomainArena,
    former: DomainValue,
    neutral: NeutralId,
    side: ConversionSide,
) -> Result<Plan, ConversionFault>
{
    let (fields, record) = if let DomainValue::Tuple { fields, .. } = former {
        (fields, None)
    }
    else if let DomainValue::Record { source, fields, .. } = former {
        (fields, Some(source))
    }
    else {
        return Ok(Plan::Leaf(Settled::NotConvertible));
    };
    let fields = domain.fields(fields).map_err(ConversionFault::Domain)?;
    if fields.is_empty() {
        return Ok(Plan::Leaf(Settled::NotConvertible));
    }
    Ok(Plan::Decompose(
        fields
            .iter()
            .enumerate()
            .map(|(position, &field)| {
                let at = gandr_core_term::Component::from(position);
                Subgoal::Projected {
                    side,
                    neutral,
                    projector: record.map_or(Projector::Component(at), |record| Projector::Field {
                        record,
                        at,
                    }),
                    field,
                }
            })
            .collect(),
    ))
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
        Early::Identical => return Ok(Plan::Shared(Settled::Convertible)),
        Early::Apart => return Ok(Plan::Shared(Settled::NotConvertible)),
        Early::Open => {},
    }
    let (Some(&one), Some(&other)) = (domain.computation(left), domain.computation(right))
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    let left_head = comp_neutrality(domain, frozen, ConversionSide::Left, one)?;
    let right_head = comp_neutrality(domain, frozen, ConversionSide::Right, other)?;
    let lambda = match (one, other) {
        (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => Lambda::Left,
        (DomainComp::Neutral { .. }, DomainComp::Lambda { .. }) => Lambda::Right,
        (
            DomainComp::Lambda { .. }
            | DomainComp::Return { .. }
            | DomainComp::Neutral { .. }
            | DomainComp::Fixpoint { .. },
            _,
        ) => Lambda::Neither,
    };
    if determinacy(left_head, right_head) == Determinacy::Indeterminate {
        return Ok(Plan::Decline(DeclineReason::Indeterminate));
    }
    let constants = plan_constants(domain, (left_head, right_head), lambda)?;
    if let Constants::Planned(planned) = constants {
        return Ok(planned);
    }
    if let Some(planned) = whole(
        core,
        domain,
        (left_head, right_head),
        Term::Comps(left, right),
    )? {
        return Ok(planned);
    }
    let planned = match (one, other) {
        (
            DomainComp::Lambda {
                body: left_body, ..
            },
            DomainComp::Lambda {
                body: right_body, ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Opened(left_body, right_body)])),
        (
            DomainComp::Return {
                value: left_value, ..
            },
            DomainComp::Return {
                value: right_value, ..
            },
        ) => Plan::Decompose(Vec::from([Subgoal::Values(left_value, right_value)])),
        // Congruence only: two fixpoints compare by their bodies under one
        // self variable, whatever claims they carry, then by the leading
        // arguments each holds, pairwise; a different count is apart.
        (
            DomainComp::Fixpoint {
                recursive: left_recursive,
                leading: left_leading,
                ..
            },
            DomainComp::Fixpoint {
                recursive: right_recursive,
                leading: right_leading,
                ..
            },
        ) => {
            let left_leading = domain
                .fields(left_leading)
                .map_err(ConversionFault::Domain)?;
            let right_leading = domain
                .fields(right_leading)
                .map_err(ConversionFault::Domain)?;
            if left_leading.len() == right_leading.len() {
                let mut subgoals = Vec::with_capacity(left_leading.len().saturating_add(1));
                subgoals.push(Subgoal::FixpointBodies(left_recursive, right_recursive));
                subgoals.extend(
                    left_leading
                        .iter()
                        .zip(right_leading)
                        .map(|(&one, &other)| Subgoal::Values(one, other)),
                );
                Plan::Decompose(subgoals)
            }
            else {
                Plan::Leaf(Settled::NotConvertible)
            }
        },
        (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => {
            Plan::Step(Step::Eta(ConversionSide::Right))
        },
        (DomainComp::Neutral { .. }, DomainComp::Lambda { .. }) => {
            Plan::Step(Step::Eta(ConversionSide::Left))
        },
        (
            DomainComp::Neutral {
                neutral: left_neutral,
                ..
            },
            DomainComp::Neutral {
                neutral: right_neutral,
                ..
            },
        ) => return plan_rigid(core, domain, left_neutral, right_neutral),
        (
            DomainComp::Lambda { .. }
            | DomainComp::Return { .. }
            | DomainComp::Neutral { .. }
            | DomainComp::Fixpoint { .. },
            _,
        ) => Plan::Leaf(Settled::NotConvertible),
    };
    Ok(planned)
}

#[cfg(test)]
mod tests;
