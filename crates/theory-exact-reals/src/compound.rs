//! The compound chain of the refinement machine: the enclosure of a real made
//! of constants, registered cuts, sums, differences, products, π, cosines,
//! sines and angles.
//!
//! A [`Compound`] settles an enclosure of such a real to a width, or a strict
//! comparison of two such reals. It works in attempts. Each attempt encloses
//! each node below the obligation's node, operands first, at the precision of
//! the attempt: a constant by its point, an operation by its exact result on
//! the enclosures of its operands, a builtin by its rule at the precision, and
//! a registered cut by two witnesses at the precision. Each enclosure is one
//! step, and so one unit of work. A node that reads no builtin and no cut
//! keeps its enclosure from the first attempt.
//!
//! |Asked|After an attempt|Then|
//! |---|---|---|
//! |an enclosure to `2^w`|the enclosure is at most `2^w` wide|the obligation settles|
//! |a comparison holds|the first operand lies below the second|a `Below` step settles it|
//! |a comparison fails|the first operand lies at or above the second|a `NotBelow` step settles it|
//! |a comparison|the operands separate on the other side|the obligation stops, opposed|
//! |any|none of these|the next attempt doubles the precision|
//!
//! The first attempt works at 64 bits. The checker's width quota bounds the
//! precision of a builtin's step and of a cut's step, and so the attempts: an
//! attempt past it stops at the quota. A bound variable, a forged cut, a
//! quotient or a power has no rule here, so a real that reads one stops with
//! [`SuspendReason::NoRule`].

use alloc::vec::Vec;
use core::ops::Add as _;
use core::ops::Shl as _;
use core::ops::Shr as _;
use core::ops::Sub as _;

use num_bigint::BigInt;

use crate::bisection::Turn;
use crate::certificate::CheckerQuotas;
use crate::certificate::Operation;
use crate::certificate::Step;
use crate::certificate::StepId;
use crate::certificate::combined;
use crate::certificate::separated_below;
use crate::dyadic::Dyadic;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::elementary::angle;
use crate::elementary::cosine;
use crate::elementary::pi;
use crate::elementary::sine;
use crate::elementary::width;
use crate::interval::Bound;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::Real;
use crate::plan::RealId;
use crate::schema::Membership;
use crate::schema::membership;
use crate::schema::radicand;
use crate::semidecision::Demand;
use crate::semidecision::SuspendReason;
use crate::semidecision::gap;
use crate::semidecision::suspension;

/// The bits of the first attempt.
const FIRST: u32 = 64;

/// The place of a node in the order of the walk.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Place(usize);

/// The cosine or the sine.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Wave
{
    /// The cosine.
    Cosine,
    /// The sine.
    Sine,
}

/// The rule of one node, with the places of its operands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Form
{
    /// A constant.
    Constant,
    /// A registered cut: the square root of a positive dyadic.
    Cut,
    /// A sum, a difference or a product.
    Arithmetic(Operation, Place, Place),
    /// π.
    Pi,
    /// A cosine or a sine.
    Wave(Wave, Place),
    /// An angle, of the point whose coordinates stand at the two places.
    Angle(Place, Place),
}

/// Whether the enclosure of a node reads the precision of the attempt.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Reads
{
    /// The node reads a builtin or a cut, so each attempt encloses it again.
    Precision,
    /// The node reads no builtin and no cut, so one enclosure serves every
    /// attempt.
    Nothing,
}

/// One node, at its place in the order.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Member
{
    /// The node.
    node: NodeId,
    /// Its rule.
    form: Form,
    /// Whether it reads the precision.
    reads: Reads,
}

/// The enclosure of one node, and the step that concludes it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Enclosed
{
    /// The step that concludes the enclosure.
    step: StepId,
    /// The enclosure.
    interval: NumericInterval,
}

/// What a compound settles.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Goal
{
    /// An enclosure of the node at `root`, no wider than `2^width`.
    Encloses
    {
        /// The place of the node.
        root: Place,
        /// The exponent of the widest enclosure asked for.
        width: Exponent,
    },
    /// The comparison `less` of the nodes at two places.
    Less
    {
        /// The comparison.
        less: NodeId,
        /// The place of the first operand.
        left: Place,
        /// The place of the second operand.
        right: Place,
        /// The pole asked of the comparison.
        asked: Demand,
    },
}

/// The compound chain of one obligation.
///
/// # Specification
/// - invariant: each member stands after the members of its operands, and each
///   enclosure concludes the node at its place: at the current precision for a
///   node that reads it, before the cursor.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Compound
{
    /// What the chain settles.
    goal: Goal,
    /// The nodes below the obligation's node, each after its operands.
    order: Vec<Member>,
    /// The current enclosure of each member, at its place.
    enclosed: Vec<Option<Enclosed>>,
    /// The absolute bits of the current attempt.
    precision: Precision,
    /// The place of the next member of the attempt.
    cursor: Place,
}

impl Compound
{
    /// The chain that settles `demand` of the node at `node` of `plan`.
    ///
    /// # Specification
    /// - ensures: the node is a real whose enclosure is asked for, or a strict
    ///   comparison whose holding or failing is asked for. Each real below it
    ///   is a constant, a registered cut, a sum, a difference, a product, π, a
    ///   cosine, a sine or an angle. The sweep does not go into a cut.
    /// - fails: suspends with [`SuspendReason::NoRule`] for any other form.
    /// - panics: none.
    /// - executable: none — the clause speaks of the form of the plan.
    /// - intension: one sweep down the plan from the obligation's node, and one
    ///   sweep up over the nodes that it reaches.
    ///
    /// # Errors
    /// - [`SuspendReason::NoRule`]: the machine has no rule for the form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an enclosure and each pole of a comparison of
    ///   builtins, and a builtin over a cut.
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    pub(crate) fn new(
        plan: &Plan,
        node: NodeId,
        demand: Demand,
    ) -> Result<Self, SuspendReason>
    {
        let place = |places: &[Option<Place>], id: NodeId| {
            return places
                .get(usize::from(id))
                .copied()
                .flatten()
                .ok_or(SuspendReason::NoRule);
        };
        let (order, goal) = match (plan.node(node), demand) {
            (Ok(&Node::Real(_)), Demand::Encloses { width }) => {
                let (order, places) = order(plan, &[node])?;
                let root = place(&places, node)?;
                (order, Goal::Encloses { root, width })
            },
            (Ok(&Node::Open(Open::Less(first, second))), Demand::Holds | Demand::Fails) => {
                let (order, places) = order(plan, &[first.node(), second.node()])?;
                let goal = Goal::Less {
                    less: node,
                    left: place(&places, first.node())?,
                    right: place(&places, second.node())?,
                    asked: demand,
                };
                (order, goal)
            },
            (Ok(_) | Err(_), _) => return Err(SuspendReason::NoRule),
        };
        let enclosed = alloc::vec![None; order.len()];
        return Ok(Self {
            goal,
            order,
            enclosed,
            precision: Precision::try_from(FIRST).map_err(|_wide| SuspendReason::Quota)?,
            cursor: Place(0),
        });
    }

    /// One unit of work: write the next step of the attempt, or conclude a
    /// comparison after a complete attempt.
    ///
    /// # Specification
    /// - ensures: one step is added to `steps`. [`Turn::Concluded`] marks the
    ///   step that concludes the evidence asked for. The steps stay a prefix of
    ///   a certificate that [`crate::certificate::check`] replays.
    /// - fails: suspends with [`SuspendReason::Opposed`] when the operands of a
    ///   comparison separate on the other side, with [`SuspendReason::Quota`]
    ///   past a quota, and with [`SuspendReason::NoRule`] when no member reads
    ///   the precision and the attempt settles nothing.
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    /// - intension: one exact operation of dyadics within the width quota, or
    ///   the series of one builtin at the precision of the attempt.
    ///
    /// # Errors
    /// - [`SuspendReason`]: the chain stops for the reason above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the builtins' obligations, each certificate replayed
    ///   to its evidence, and each checkpoint resumed. L3 — each row of the
    ///   module's table.
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    pub(crate) fn unit(
        &mut self,
        plan: &Plan,
        steps: &mut Vec<Step>,
        quotas: &CheckerQuotas,
    ) -> Result<Turn, SuspendReason>
    {
        loop {
            let Some(&member) = self.order.get(self.cursor.0)
            else {
                if let Some(turn) = self.compared(steps, quotas)? {
                    return Ok(turn);
                }
                self.attempt(quotas)?;
                continue;
            };
            let known = self
                .enclosed
                .get(self.cursor.0)
                .is_some_and(Option::is_some);
            if member.reads == Reads::Nothing && known {
                self.cursor = Place(self.cursor.0.saturating_add(1));
                continue;
            }
            self.write(plan, member, steps, quotas)?;
            self.cursor = Place(self.cursor.0.saturating_add(1));
            return self.reached();
        }
    }

    /// The enclosure at `place`, once its step is written.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        place: Place,
    ) -> Result<&Enclosed, SuspendReason>
    {
        return self
            .enclosed
            .get(place.0)
            .and_then(Option::as_ref)
            .ok_or(SuspendReason::NoRule);
    }

    /// Write the step that encloses `member` at the current precision.
    ///
    /// # Specification
    /// - requires: the enclosures of the member's operands are written.
    /// - ensures: one step is added, and the member's place holds its
    ///   enclosure.
    /// - fails: as [`Self::unit`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    ///
    /// # Errors
    /// - [`SuspendReason`]: as [`Self::unit`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::unit`].
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    fn write(
        &mut self,
        plan: &Plan,
        member: Member,
        steps: &mut Vec<Step>,
        quotas: &CheckerQuotas,
    ) -> Result<(), SuspendReason>
    {
        if steps.len() >= usize::from(quotas.steps) {
            return Err(SuspendReason::Quota);
        }
        let id = StepId::try_from(steps.len()).map_err(|_wide| SuspendReason::Quota)?;
        let (real, precision) = (member.node, self.precision);
        // The checker refuses a builtin's step whose rule works past its
        // width quota.
        let builtin = || {
            if width(precision) > quotas.width {
                return Err(SuspendReason::Quota);
            }
            return Ok(());
        };
        let (step, interval) = match member.form {
            Form::Constant => {
                let Ok(&Node::Real(Real::Constant(ref value))) = plan.node(real)
                else {
                    return Err(SuspendReason::NoRule);
                };
                if value.width() > quotas.width {
                    return Err(SuspendReason::Quota);
                }
                (
                    Step::Constant { real },
                    NumericInterval::point(value.clone()),
                )
            },
            Form::Cut => {
                builtin()?;
                let radicand = radicand(plan, real).map_err(suspension)?;
                let (lower, upper) = witnesses(&radicand, precision)?;
                // A point of the lower cut lies below a point of the upper cut,
                // so the open interval between them is proper.
                let interval = NumericInterval::new(
                    Bound::open(Endpoint::Finite(lower.clone())),
                    Bound::open(Endpoint::Finite(upper.clone())),
                    Orientation::Proper,
                )
                .map_err(|_reversed| SuspendReason::NoRule)?;
                (
                    Step::Witnesses {
                        cut: real,
                        lower,
                        upper,
                    },
                    interval,
                )
            },
            Form::Arithmetic(operation, first, second) => {
                let (first, second) = (self.at(first)?, self.at(second)?);
                let interval = combined(operation, &first.interval, &second.interval, quotas)
                    .map_err(suspension)?;
                let (left, right) = (first.step, second.step);
                let step = match operation {
                    Operation::Sum => Step::Sum { real, left, right },
                    Operation::Difference => Step::Difference { real, left, right },
                    Operation::Product => Step::Product { real, left, right },
                };
                (step, interval)
            },
            Form::Pi => {
                builtin()?;
                (
                    Step::Pi { real, precision },
                    pi(precision).map_err(suspension)?,
                )
            },
            Form::Wave(wave, argument) => {
                builtin()?;
                let operand = self.at(argument)?;
                let argument = operand.step;
                match wave {
                    Wave::Cosine => (
                        Step::Cosine {
                            real,
                            argument,
                            precision,
                        },
                        cosine(&operand.interval, precision).map_err(suspension)?,
                    ),
                    Wave::Sine => (
                        Step::Sine {
                            real,
                            argument,
                            precision,
                        },
                        sine(&operand.interval, precision).map_err(suspension)?,
                    ),
                }
            },
            Form::Angle(first, second) => {
                builtin()?;
                let (first, second) = (self.at(first)?, self.at(second)?);
                let interval =
                    angle(&first.interval, &second.interval, precision).map_err(suspension)?;
                let step = Step::Angle {
                    real,
                    x: first.step,
                    y: second.step,
                    precision,
                };
                (step, interval)
            },
        };
        steps.push(step);
        let slot = self
            .enclosed
            .get_mut(self.cursor.0)
            .ok_or(SuspendReason::NoRule)?;
        *slot = Some(Enclosed { step: id, interval });
        return Ok(());
    }

    /// The turn after a member's step: [`Turn::Concluded`] when a complete
    /// attempt meets the width of an enclosure asked for, and
    /// [`Turn::Stepped`] otherwise.
    ///
    /// # Specification
    /// trivial.
    fn reached(&self) -> Result<Turn, SuspendReason>
    {
        let Goal::Encloses { root, width } = self.goal
        else {
            return Ok(Turn::Stepped);
        };
        if self.cursor.0 < self.order.len() {
            return Ok(Turn::Stepped);
        }
        let target = Dyadic::new(num_bigint::BigInt::from(1_u8), width)
            .map_err(|_overflow| SuspendReason::Quota)?;
        if gap(&self.at(root)?.interval).is_some_and(|gap| gap <= target) {
            return Ok(Turn::Concluded);
        }
        return Ok(Turn::Stepped);
    }

    /// The step that concludes a comparison after a complete attempt, or
    /// `None` when its operands do not separate yet.
    ///
    /// # Specification
    /// - ensures: writes a `Below` step when the comparison holds is asked and
    ///   the first operand lies below the second, and a `NotBelow` step when
    ///   its failure is asked and the first operand lies at or above the
    ///   second. Writes nothing for an enclosure.
    /// - fails: suspends with [`SuspendReason::Opposed`] when the operands
    ///   separate on the other side, and with [`SuspendReason::Quota`] past the
    ///   step quota.
    /// - panics: none.
    /// - executable: none — the clause restates the table of the module.
    ///
    /// # Errors
    /// - [`SuspendReason`]: as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each pole of a comparison of builtins that holds, and
    ///   one that fails.
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    fn compared(
        &self,
        steps: &mut Vec<Step>,
        quotas: &CheckerQuotas,
    ) -> Result<Option<Turn>, SuspendReason>
    {
        let Goal::Less {
            less,
            left,
            right,
            asked,
        } = self.goal
        else {
            return Ok(None);
        };
        let (first, second) = (self.at(left)?, self.at(right)?);
        let below = separated_below(&first.interval, &second.interval).is_ok();
        let above = first.interval.lower().endpoint >= second.interval.upper().endpoint;
        let (left, right) = (first.step, second.step);
        let (step, opposed) = match asked {
            Demand::Holds => (below.then_some(Step::Below { less, left, right }), above),
            Demand::Fails => (above.then_some(Step::NotBelow { less, left, right }), below),
            Demand::Encloses { .. } => return Err(SuspendReason::NoRule),
        };
        if let Some(step) = step {
            if steps.len() >= usize::from(quotas.steps) {
                return Err(SuspendReason::Quota);
            }
            steps.push(step);
            return Ok(Some(Turn::Concluded));
        }
        if opposed {
            return Err(SuspendReason::Opposed);
        }
        return Ok(None);
    }

    /// Start the next attempt at twice the precision.
    ///
    /// # Specification
    /// - ensures: the cursor stands at the first member, and the precision
    ///   doubles.
    /// - fails: suspends with [`SuspendReason::NoRule`] when no member reads
    ///   the precision, and with [`SuspendReason::Quota`] when the doubled
    ///   precision leaves its range.
    /// - panics: none.
    /// - executable: none — the clause restates the fields.
    ///
    /// # Errors
    /// - [`SuspendReason`]: as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an enclosure that needs several attempts.
    /// - witness: `tests::elementary::the_machine_certifies_the_builtins`
    fn attempt(
        &mut self,
        quotas: &CheckerQuotas,
    ) -> Result<(), SuspendReason>
    {
        if self
            .order
            .iter()
            .all(|member| member.reads == Reads::Nothing)
        {
            return Err(SuspendReason::NoRule);
        }
        let doubled = u32::from(self.precision).saturating_mul(2);
        let precision = Precision::try_from(doubled).map_err(|_wide| SuspendReason::Quota)?;
        if width(precision) > quotas.width {
            return Err(SuspendReason::Quota);
        }
        self.precision = precision;
        self.cursor = Place(0);
        return Ok(());
    }
}

/// The nodes below `roots`, each after its operands, and the place of each
/// node of the plan in that order.
///
/// # Specification
/// - ensures: the order holds each node that a root reaches, once, in the order
///   of its position in the plan. Each member names the places of its operands.
///   A cut is a leaf: the order holds no node of its body unless another path
///   reaches it.
/// - fails: suspends with [`SuspendReason::NoRule`] for a node that has no rule
///   here, for a cut that is not registered, and for a root that is not a real.
/// - panics: none.
/// - executable: none — the clause speaks of the plan's reach.
/// - intension: one sweep down from the highest root and one sweep up, each
///   over the positions at or below it.
///
/// # Errors
/// - [`SuspendReason::NoRule`]: the machine has no rule for a node.
///
/// # Adequacy
/// - hypothesis: L3 — a comparison whose operands share a node, a builtin over
///   a cut, and a sum of cuts.
/// - witness: `tests::elementary::the_machine_certifies_the_builtins`
fn order(
    plan: &Plan,
    roots: &[NodeId],
) -> Result<(Vec<Member>, Vec<Option<Place>>), SuspendReason>
{
    let top = roots
        .iter()
        .map(|&root| usize::from(root))
        .max()
        .ok_or(SuspendReason::NoRule)?;
    let size = top.checked_add(1).ok_or(SuspendReason::NoRule)?;
    let mut reached = alloc::vec![false; size];
    for &root in roots {
        let slot = reached
            .get_mut(usize::from(root))
            .ok_or(SuspendReason::NoRule)?;
        *slot = true;
    }
    // A node stands after each node that it reads, so one sweep down from the
    // highest root reaches each node below the roots. Its witnesses enclose a
    // cut, so the sweep does not go into the cut's body.
    for index in (0 .. size).rev() {
        if reached.get(index) != Some(&true) {
            continue;
        }
        let id = NodeId::try_from(index).map_err(|_wide| SuspendReason::NoRule)?;
        let node = plan.node(id).map_err(|_unknown| SuspendReason::NoRule)?;
        if matches!(*node, Node::Real(Real::Cut(_))) {
            continue;
        }
        for edge in node.edges() {
            let slot = reached
                .get_mut(usize::from(edge.node))
                .ok_or(SuspendReason::NoRule)?;
            *slot = true;
        }
    }
    let mut places: Vec<Option<Place>> = alloc::vec![None; size];
    let mut order: Vec<Member> = Vec::new();
    for (index, &hit) in reached.iter().enumerate() {
        if !hit {
            continue;
        }
        let id = NodeId::try_from(index).map_err(|_wide| SuspendReason::NoRule)?;
        let place = |operand: RealId| {
            return places
                .get(usize::from(operand.node()))
                .copied()
                .flatten()
                .ok_or(SuspendReason::NoRule);
        };
        let reads = |operand: Place| {
            return order
                .get(operand.0)
                .map_or(Reads::Nothing, |member| member.reads);
        };
        let arithmetic = |operation: Operation, first: RealId, second: RealId| {
            let (first, second) = (place(first)?, place(second)?);
            let read = if reads(first) == Reads::Precision || reads(second) == Reads::Precision {
                Reads::Precision
            }
            else {
                Reads::Nothing
            };
            return Ok((Form::Arithmetic(operation, first, second), read));
        };
        let (form, reads) = match *plan.node(id).map_err(|_unknown| SuspendReason::NoRule)? {
            Node::Real(Real::Constant(_)) => (Form::Constant, Reads::Nothing),
            Node::Real(Real::Add(first, second)) => arithmetic(Operation::Sum, first, second)?,
            Node::Real(Real::Sub(first, second)) => {
                arithmetic(Operation::Difference, first, second)?
            },
            Node::Real(Real::Mul(first, second)) => arithmetic(Operation::Product, first, second)?,
            Node::Real(Real::Pi) => (Form::Pi, Reads::Precision),
            Node::Real(Real::Cos(argument)) => {
                (Form::Wave(Wave::Cosine, place(argument)?), Reads::Precision)
            },
            Node::Real(Real::Sin(argument)) => {
                (Form::Wave(Wave::Sine, place(argument)?), Reads::Precision)
            },
            Node::Real(Real::Arg(x, y)) => (Form::Angle(place(x)?, place(y)?), Reads::Precision),
            Node::Real(Real::Cut(_)) => {
                radicand(plan, id).map_err(|_forged| SuspendReason::NoRule)?;
                (Form::Cut, Reads::Precision)
            },
            Node::Real(Real::Bound(_) | Real::Div { .. } | Real::Power(..))
            | Node::Open(_)
            | Node::Domain(_) => return Err(SuspendReason::NoRule),
        };
        let slot = places.get_mut(index).ok_or(SuspendReason::NoRule)?;
        *slot = Some(Place(order.len()));
        order.push(Member {
            node: id,
            form,
            reads,
        });
    }
    return Ok((order, places));
}

/// Two witnesses of the square root of `radicand` at `precision`: a point of
/// its lower cut and a point of its upper cut, `2^(1 - precision)` apart.
///
/// # Specification
/// - requires: `radicand` is positive, as a registered cut's radicand is.
/// - ensures: with `s` the integer square root of `radicand · 4^p` rounded
///   down, the points are `(s - 1) · 2^-p` and `(s + 1) · 2^-p`. Since `s²` is
///   at most the radicand's scaled value and `(s + 1)²` lies above it, the
///   first point lies in the lower cut and the second in the upper cut.
/// - fails: suspends with [`SuspendReason::Quota`] when a point or its exact
///   square leaves the checker's range, and with [`SuspendReason::NoRule`] when
///   a point is not a witness of its side.
/// - panics: none.
/// - executable: none — the clause restates the arithmetic.
/// - intension: one integer square root of `2p` bits and the radicand's width,
///   and two exact squares.
///
/// # Errors
/// - [`SuspendReason`]: as above.
///
/// # Adequacy
/// - hypothesis: L2 — the code of each set of height at most 3, enclosed and
///   replayed. L3 — the cosine of the square root of two.
/// - witness: `tests::ackermann::each_code_encloses_and_replays`
/// - witness: `tests::elementary::the_machine_certifies_the_builtins`
fn witnesses(
    radicand: &Dyadic,
    precision: Precision,
) -> Result<(Dyadic, Dyadic), SuspendReason>
{
    let bits = i32::try_from(u32::from(precision)).map_err(|_wide| SuspendReason::Quota)?;
    let scale = bits.checked_mul(2_i32).ok_or(SuspendReason::Quota)?;
    let scaled = i32::from(radicand.exponent())
        .checked_add(scale)
        .ok_or(SuspendReason::Quota)?;
    // The radicand times `4^p`, rounded down to an integer.
    let mantissa = radicand.mantissa();
    let floor = if scaled >= 0_i32 {
        mantissa.shl(scaled.unsigned_abs())
    }
    else {
        mantissa.shr(scaled.unsigned_abs())
    };
    let root = BigInt::from(floor.magnitude().sqrt());
    let ulp = Exponent::from(bits.checked_neg().ok_or(SuspendReason::Quota)?);
    let lower = Dyadic::new(root.clone().sub(1_u8), ulp).map_err(|_range| SuspendReason::Quota)?;
    let upper = Dyadic::new(root.add(1_u8), ulp).map_err(|_range| SuspendReason::Quota)?;
    if membership(&lower, radicand).map_err(suspension)? != Membership::Lower
        || membership(&upper, radicand).map_err(suspension)? != Membership::Upper
    {
        return Err(SuspendReason::NoRule);
    }
    return Ok((lower, upper));
}
