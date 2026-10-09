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
    // economy: membership is a linear scan, and a goal's frozen set grows by
    // one per freezing branch on its chain — a handful in practice. Upgrade
    // path: a sorted vector with a binary search when a chain freezes enough
    // constants to show in a profile.
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
    ///   winning branch is the alternative that arm alone offers.
    /// - witness: `machine::tests::the_const_shortcut_wins_without_unfolding`
    /// - witness: `machine::tests::two_defined_heads_meet_by_unfolding`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
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
///   elimination kind at every position: an application's arguments as a value
///   pair, a bind's continuations as an opened pair, a case's branches as two
///   opened pairs left first, a force as nothing, in spine order innermost
///   first; [`Spines::Disagree`] when a length or a kind differs. The heads are
///   not compared.
/// - provides: the premises of `var-1` and `const`, in the order a recorded
///   subgoal position counts.
/// - fails: [`ConversionFault::Domain`] when a neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a neutral does not resolve.
pub fn spine_subgoals(
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
        match (left_elimination, right_elimination) {
            | (Elimination::Apply(left_argument), Elimination::Apply(right_argument)) => {
                subgoals.push(Subgoal::Values(left_argument, right_argument));
            },
            | (Elimination::Force, Elimination::Force) => {},
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
                Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Bind(_)
                | Elimination::Case { .. },
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
///   for a lambda against a rigid or frozen neutral.
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
/// - hypothesis: L3 — the decision surfaces are the early steps, the constant
///   arms and the structural arms; each is separated by a conversion the
///   machine answers through that arm alone.
/// - witness: `machine::tests::identity_closes_a_goal_on_shared_nodes`
/// - witness: `machine::tests::a_forced_unfolding_meets_a_former`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::thunks_meet_by_forcing`
/// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
pub fn plan(
    core: &CoreArena,
    domain: &DomainArena,
    frozen: &Frozen,
    left: Glued,
    right: Glued,
) -> Result<Plan, ConversionFault>
{
    match (left, right) {
        | (Glued::Value(one), Glued::Value(other)) => plan_values(core, domain, frozen, one, other),
        | (Glued::Computation(one), Glued::Computation(other)) => {
            plan_comps(domain, frozen, one, other)
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
fn plan_rigid(
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
    let spines = spine_subgoals(domain, left, right)?;
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
///   neutral value; [`Neutrality::Former`] for every other value.
/// - provides: the neutral projection the constant arms match on.
/// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — the neutral does not resolve.
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
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. } => Neutrality::Former,
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
fn plan_values(
    core: &CoreArena,
    domain: &DomainArena,
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
        ) => return plan_rigid(domain, left_neutral, right_neutral),
        | (
            DomainValue::Unit { .. }
            | DomainValue::Literal { .. }
            | DomainValue::Pair { .. }
            | DomainValue::Injection { .. }
            | DomainValue::Thunk { .. }
            | DomainValue::Lift { .. }
            | DomainValue::Neutral { .. },
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
fn plan_comps(
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
        ) => return plan_rigid(domain, left_neutral, right_neutral),
        | (
            DomainComp::Lambda { .. } | DomainComp::Return { .. } | DomainComp::Neutral { .. },
            _,
        ) => Plan::Leaf(Settled::NotConvertible),
    };
    Ok(planned)
}
