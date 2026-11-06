//! Dual approximation of validated plans at one precision.
//!
//! A finite computation cannot decide a question about the reals with a
//! boolean. [`approximate`] gives each node of a [`ValidatedPlan`] an
//! approximation at one [`Precision`]. A real node gets an enclosure: a
//! proper [`NumericInterval`] that holds the node's value, rounded outward. An
//! open node gets a [`BilateralApprox`]: a positive approximant that can
//! prove the proposition true, and a negative approximant that can prove it
//! false. Each approximant is sound on its own. When neither proves its side,
//! the proposition stays undecided at this precision. The pass never reports
//! an undecided proposition as false.
//!
//! # Boundaries
//!
//! |Node|Approximation|
//! |---|---|
//! |constant|the constant, rounded outward|
//! |sum, difference, product|the interval operation, rounded outward|
//! |quotient|the interval quotient, or the whole line when the divisor's enclosure holds zero|
//! |power|repeated squaring of the base's enclosure|
//! |cut|its hull|
//! |bound variable|the whole line|
//! |`Less(a, b)`|true when every point of `a` lies below every point of `b`, false when every point of `a` lies at or above every point of `b`|
//! |meet|true when both are true, false when one is false|
//! |join|true when one is true, false when both are false|
//! |top, bottom|true, false|
//! |quantifier|undecided: stage B of the exact-reals programme decides quantifiers|
//!
//! The pass is total and never panics. An endpoint operation that fails gives
//! the whole line for a real and the undecided pair for an open proposition.
//! The pass visits each distinct node once, children before parents, and it
//! keeps one approximation per node.
//!
//! A finer precision decides only a strict separation. The comparison
//! `1/3 + 1/3 < 683/1024` stays undecided up to nine bits and decides at
//! ten, because `683/1024` lies `1/3072` above `2/3`. The comparison
//! `1/3 · 3 < 1` stays undecided at every precision, because its two sides
//! are equal.
//!
//! # Items
//!
//! - [`approximate`] — the pass.
//! - [`Approximation`] — its result, read by node.
//! - [`BilateralApprox`], [`PositiveApprox`], [`NegativeApprox`] — the
//!   approximants of an open proposition.

use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;

use crate::dyadic::Dyadic;
use crate::dyadic::Exactness;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::interval::Bound;
use crate::interval::Closure;
use crate::interval::Containment;
use crate::interval::Endpoint;
use crate::interval::IntervalError;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::OpenId;
use crate::plan::PlanError;
use crate::plan::Power;
use crate::plan::Real;
use crate::plan::RealId;
use crate::validate::ValidatedPlan;

/// The positive approximant of an open proposition.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PositiveApprox
{
    /// The approximation proves the proposition true.
    ProvenTrue,
    /// The approximation proves nothing about truth.
    Unknown,
}

/// The negative approximant of an open proposition.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum NegativeApprox
{
    /// The approximation proves the proposition false.
    ProvenFalse,
    /// The approximation proves nothing about falsehood.
    Unknown,
}

/// The two approximants of an open proposition. Each is sound on its own,
/// and neither is inferred from the other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BilateralApprox
{
    /// Whether the approximation proves the proposition true.
    pub positive: PositiveApprox,
    /// Whether the approximation proves the proposition false.
    pub negative: NegativeApprox,
}

impl BilateralApprox
{
    /// The approximants of a proposition proven false.
    pub const FALSE: Self = Self {
        positive: PositiveApprox::Unknown,
        negative: NegativeApprox::ProvenFalse,
    };
    /// The approximants of a proposition proven true.
    pub const TRUE: Self = Self {
        positive: PositiveApprox::ProvenTrue,
        negative: NegativeApprox::Unknown,
    };
    /// The approximants of an undecided proposition.
    pub const UNDECIDED: Self = Self {
        positive: PositiveApprox::Unknown,
        negative: NegativeApprox::Unknown,
    };

    /// The approximants of the meet of two propositions.
    ///
    /// # Specification
    /// - ensures: the positive approximant proves truth exactly when both
    ///   operands' positive approximants do. The negative approximant proves
    ///   falsehood exactly when either operand's negative approximant does.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all nine pairs of the three approximant pairs.
    /// - witness: `tests::approx::meet_and_join_follow_their_tables`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret.positive, PositiveApprox::ProvenTrue) == (matches!(self.positive, PositiveApprox::ProvenTrue) && matches!(other.positive, PositiveApprox::ProvenTrue)) && matches!(ret.negative, NegativeApprox::ProvenFalse) == (matches!(self.negative, NegativeApprox::ProvenFalse) || matches!(other.negative, NegativeApprox::ProvenFalse)))]
    pub const fn meet(
        self,
        other: Self,
    ) -> Self
    {
        let positive = match (self.positive, other.positive) {
            (PositiveApprox::ProvenTrue, PositiveApprox::ProvenTrue) => PositiveApprox::ProvenTrue,
            (PositiveApprox::Unknown, PositiveApprox::ProvenTrue | PositiveApprox::Unknown)
            | (PositiveApprox::ProvenTrue, PositiveApprox::Unknown) => PositiveApprox::Unknown,
        };
        let negative = match (self.negative, other.negative) {
            (
                NegativeApprox::ProvenFalse,
                NegativeApprox::ProvenFalse | NegativeApprox::Unknown,
            )
            | (NegativeApprox::Unknown, NegativeApprox::ProvenFalse) => NegativeApprox::ProvenFalse,
            (NegativeApprox::Unknown, NegativeApprox::Unknown) => NegativeApprox::Unknown,
        };
        return Self { positive, negative };
    }

    /// The approximants of the join of two propositions.
    ///
    /// # Specification
    /// - ensures: the positive approximant proves truth exactly when either
    ///   operand's positive approximant does. The negative approximant proves
    ///   falsehood exactly when both operands' negative approximants do.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all nine pairs of the three approximant pairs.
    /// - witness: `tests::approx::meet_and_join_follow_their_tables`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret.positive, PositiveApprox::ProvenTrue) == (matches!(self.positive, PositiveApprox::ProvenTrue) || matches!(other.positive, PositiveApprox::ProvenTrue)) && matches!(ret.negative, NegativeApprox::ProvenFalse) == (matches!(self.negative, NegativeApprox::ProvenFalse) && matches!(other.negative, NegativeApprox::ProvenFalse)))]
    pub const fn join(
        self,
        other: Self,
    ) -> Self
    {
        let positive = match (self.positive, other.positive) {
            (PositiveApprox::ProvenTrue, PositiveApprox::ProvenTrue | PositiveApprox::Unknown)
            | (PositiveApprox::Unknown, PositiveApprox::ProvenTrue) => PositiveApprox::ProvenTrue,
            (PositiveApprox::Unknown, PositiveApprox::Unknown) => PositiveApprox::Unknown,
        };
        let negative = match (self.negative, other.negative) {
            (NegativeApprox::ProvenFalse, NegativeApprox::ProvenFalse) => {
                NegativeApprox::ProvenFalse
            },
            (NegativeApprox::Unknown, NegativeApprox::ProvenFalse | NegativeApprox::Unknown)
            | (NegativeApprox::ProvenFalse, NegativeApprox::Unknown) => NegativeApprox::Unknown,
        };
        return Self { positive, negative };
    }
}

/// The approximation of one node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Slot
{
    /// The enclosure of a real node.
    Real(NumericInterval),
    /// The approximants of an open node.
    Open(BilateralApprox),
    /// A domain node, which stage A does not approximate.
    Domain,
}

/// The approximation of every node of one plan at one precision.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Approximation
{
    /// The precision of every enclosure.
    precision: Precision,
    /// One approximation per node, at the node's position.
    slots: Vec<Slot>,
}

impl Approximation
{
    /// The precision of every enclosure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn precision(&self) -> Precision
    {
        return self.precision;
    }

    /// The enclosure of the real node at `node`.
    ///
    /// # Specification
    /// - ensures: returns a proper interval that holds the node's value.
    /// - fails: returns [`PlanError::UnknownNode`] when no node stands at
    ///   `node`, and [`PlanError::WrongSort`] when the node there is not a
    ///   real.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node stands at `node`.
    /// - [`PlanError::WrongSort`]: the node is not a real.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position past the plan, and the position of an open
    ///   node.
    /// - witness: `tests::approx::lookups_refuse_a_foreign_node`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == matches!(self.slots.get(usize::from(node)), Some(&Slot::Real(_))))]
    pub fn enclosure(
        &self,
        node: NodeId,
    ) -> Result<&NumericInterval, PlanError>
    {
        return match self.slots.get(usize::from(node)) {
            Some(&Slot::Real(ref enclosure)) => Ok(enclosure),
            Some(&(Slot::Open(_) | Slot::Domain)) => Err(PlanError::WrongSort),
            None => Err(PlanError::UnknownNode),
        };
    }

    /// The approximants of the open node at `node`.
    ///
    /// # Specification
    /// - ensures: returns the node's approximants, each sound on its own.
    /// - fails: returns [`PlanError::UnknownNode`] when no node stands at
    ///   `node`, and [`PlanError::WrongSort`] when the node there is not an
    ///   open proposition.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node stands at `node`.
    /// - [`PlanError::WrongSort`]: the node is not an open proposition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position past the plan, and the position of a real
    ///   node.
    /// - witness: `tests::approx::lookups_refuse_a_foreign_node`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == matches!(self.slots.get(usize::from(node)), Some(&Slot::Open(_))))]
    pub fn approximants(
        &self,
        node: NodeId,
    ) -> Result<BilateralApprox, PlanError>
    {
        return match self.slots.get(usize::from(node)) {
            Some(&Slot::Open(approximants)) => Ok(approximants),
            Some(&(Slot::Real(_) | Slot::Domain)) => Err(PlanError::WrongSort),
            None => Err(PlanError::UnknownNode),
        };
    }
}

/// Approximate every node of `plan` at `precision`.
///
/// # Specification
/// - ensures: each real node's enclosure holds the node's value, and each open
///   node's positive approximant proves truth only of a true proposition, its
///   negative approximant falsehood only of a false one. The result holds one
///   approximation per node.
/// - panics: none.
/// - intension: one pass over the nodes in their canonical order, which places
///   each child before its parents. Each node costs at most one interval
///   operation, or one per bit of a power. The pass allocates the table of
///   approximations once, and the carrier allocates only for endpoints wider
///   than 64 bits.
///
/// # Adequacy
/// - hypothesis: L2 — the slow rational oracle evaluates generated closed plans
///   of every stage-A node kind at several precisions. Each oracle value lies
///   in its enclosure, each proven approximant agrees with the oracle's truth,
///   and no proposition is proven both true and false. L3 — the hand example
///   `1/3 + 1/3 < 1`, a comparison of equal values that never decides, and a
///   divisor whose enclosure holds zero.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
/// - witness: `tests::approx::a_third_twice_decides_below_one_at_a_finer_precision`
/// - witness: `tests::approx::an_undecided_comparison_is_never_false`
/// - witness: `tests::approx::a_divisor_enclosing_zero_gives_the_whole_line`
#[inline]
#[must_use]
#[spec(ensures: |ref result| result.slots.len() == usize::from(plan.plan().node_count()))]
pub fn approximate(
    plan: &ValidatedPlan,
    precision: Precision,
) -> Approximation
{
    let plan = plan.plan();
    let mut slots = Vec::with_capacity(usize::from(plan.node_count()));
    for (_, node) in plan.nodes() {
        let slot = match *node {
            Node::Real(ref real) => Slot::Real(enclose(real, &slots, precision)),
            Node::Open(ref open) => Slot::Open(decide(open, &slots)),
            Node::Domain(_) => Slot::Domain,
        };
        slots.push(slot);
    }
    return Approximation { precision, slots };
}

/// The whole line, which every real lies in.
static WHOLE: NumericInterval = NumericInterval::whole();

/// The enclosure of the real child `id`, read from the approximations made so
/// far.
///
/// # Specification
/// - ensures: returns the child's enclosure, or the whole line when no real
///   approximation stands at `id`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every real operand of the oracle's plans.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |result| matches!(slots.get(usize::from(id.node())), Some(&Slot::Real(_))) || *result == WHOLE)]
fn real_at(
    slots: &[Slot],
    id: RealId,
) -> &NumericInterval
{
    return match slots.get(usize::from(id.node())) {
        Some(&Slot::Real(ref enclosure)) => enclosure,
        Some(&(Slot::Open(_) | Slot::Domain)) | None => &WHOLE,
    };
}

/// The approximants of the open child `id`, read from the approximations
/// made so far.
///
/// # Specification
/// - ensures: returns the child's approximants, or the undecided pair when no
///   open approximation stands at `id`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every open operand of the oracle's plans.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |ref result| matches!(slots.get(usize::from(id.node())), Some(&Slot::Open(_))) || *result == BilateralApprox::UNDECIDED)]
fn open_at(
    slots: &[Slot],
    id: OpenId,
) -> BilateralApprox
{
    return match slots.get(usize::from(id.node())) {
        Some(&Slot::Open(approximants)) => approximants,
        Some(&(Slot::Real(_) | Slot::Domain)) | None => BilateralApprox::UNDECIDED,
    };
}

/// The enclosure of one real node.
///
/// # Specification
/// - ensures: returns a proper interval that holds the node's value, given
///   enclosures of its children that hold theirs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — each real node kind under the oracle.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |ref result| result.orientation() == Orientation::Proper)]
fn enclose(
    real: &Real,
    slots: &[Slot],
    precision: Precision,
) -> NumericInterval
{
    let enclosure = match *real {
        Real::Bound(_) => Ok(NumericInterval::whole()),
        Real::Constant(ref value) => constant(value, precision),
        Real::Add(left, right) => real_at(slots, left).add(real_at(slots, right), precision),
        Real::Sub(left, right) => real_at(slots, left).sub(real_at(slots, right), precision),
        Real::Mul(left, right) => real_at(slots, left).mul(real_at(slots, right), precision),
        Real::Div {
            numerator,
            denominator,
            ..
        } => real_at(slots, numerator).div(real_at(slots, denominator), precision),
        Real::Power(base, power) => raised(real_at(slots, base), power, precision),
        Real::Cut(ref cut) => Ok(cut.hull.clone()),
    };
    return enclosure.unwrap_or_else(|_failure| NumericInterval::whole());
}

/// The enclosure of a constant at `precision`.
///
/// # Specification
/// - ensures: returns the closed point when the constant fits `precision` bits,
///   else the open interval between its floor and its ceiling.
/// - fails: returns [`IntervalError::Arithmetic`] when a rounding's exponent
///   leaves its range.
/// - panics: none.
///
/// # Errors
/// - [`IntervalError::Arithmetic`]: a rounding failed.
///
/// # Adequacy
/// - hypothesis: L2 — constants wider than the precision under the oracle.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |enclosure| enclosure.contains(value) == Containment::Contains))]
fn constant(
    value: &Dyadic,
    precision: Precision,
) -> Result<NumericInterval, IntervalError>
{
    let floor = value.round(precision, Rounding::Floor)?;
    if floor.exactness() == Exactness::Exact {
        return Ok(NumericInterval::point(floor.into_value()));
    }
    let ceiling = value.round(precision, Rounding::Ceiling)?;
    return NumericInterval::new(
        Bound::open(Endpoint::Finite(floor.into_value())),
        Bound::open(Endpoint::Finite(ceiling.into_value())),
        Orientation::Proper,
    );
}

/// The enclosure of `base` raised to `power`, by repeated squaring.
///
/// # Specification
/// - ensures: returns a proper interval that holds `x^power` for every `x` in
///   `base`. The zeroth power is the closed point one.
/// - fails: returns the first failed interval product.
/// - panics: none.
/// - intension: one squaring per bit of `power` and one product per set bit.
///
/// # Errors
/// - [`IntervalError::Arithmetic`]: a product's exponent left its range.
/// - [`IntervalError::DualOperand`]: `base` is dual.
///
/// # Adequacy
/// - hypothesis: L2 — powers up to the generator's bound under the oracle, on
///   bases of both signs.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |enclosure| enclosure.orientation() == Orientation::Proper))]
fn raised(
    base: &NumericInterval,
    power: Power,
    precision: Precision,
) -> Result<NumericInterval, IntervalError>
{
    let power = u32::from(power);
    let mut result = NumericInterval::point(Dyadic::ONE);
    for bit in (0 .. u32::BITS.saturating_sub(power.leading_zeros())).rev() {
        result = result.mul(&result, precision)?;
        if power
            .checked_shr(bit)
            .is_some_and(|shifted| shifted & 1 == 1)
        {
            result = result.mul(base, precision)?;
        }
    }
    return Ok(result);
}

/// The approximants of one open node.
///
/// # Specification
/// - ensures: returns approximants that are each sound, given sound
///   approximations of the children.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — each open node kind of stage A under the oracle.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
#[spec(ensures: |ref result| !(result.positive == PositiveApprox::ProvenTrue && result.negative == NegativeApprox::ProvenFalse))]
fn decide(
    open: &Open,
    slots: &[Slot],
) -> BilateralApprox
{
    return match *open {
        Open::Top => BilateralApprox::TRUE,
        Open::Bottom => BilateralApprox::FALSE,
        Open::Less(left, right) => compared(real_at(slots, left), real_at(slots, right)),
        // A point lies in the lower cut of a cut exactly when it lies below the
        // cut's value, so the enclosures approximate the cut as a comparison.
        Open::LowerCut(cut, point) => compared(real_at(slots, point), real_at(slots, cut)),
        Open::UpperCut(cut, point) => compared(real_at(slots, cut), real_at(slots, point)),
        Open::Meet(left, right) => open_at(slots, left).meet(open_at(slots, right)),
        Open::Join(left, right) => open_at(slots, left).join(open_at(slots, right)),
        Open::Exists(_) | Open::Forall(_) => BilateralApprox::UNDECIDED,
    };
}

/// The approximants of `a < b` for `a` in `left` and `b` in `right`.
///
/// # Specification
/// - requires: both intervals are proper.
/// - ensures: proves truth when every point of `left` lies strictly below every
///   point of `right`, and falsehood when every point of `left` lies at or
///   above every point of `right`. Otherwise both approximants are unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated comparisons under the oracle. L3 — equal
///   points, touching endpoints of each closure, and overlaps.
/// - witness: `tests::approx::approximants_agree_with_the_rational_oracle`
/// - witness: `tests::approx::an_undecided_comparison_is_never_false`
#[spec(requires: left.orientation() == Orientation::Proper && right.orientation() == Orientation::Proper)]
fn compared(
    left: &NumericInterval,
    right: &NumericInterval,
) -> BilateralApprox
{
    // Equal endpoints are finite, because a proper interval is not empty.
    let below = match left.upper().endpoint.cmp(&right.lower().endpoint) {
        Ordering::Less => true,
        Ordering::Equal => {
            left.upper().closure == Closure::Open || right.lower().closure == Closure::Open
        },
        Ordering::Greater => false,
    };
    if below {
        return BilateralApprox::TRUE;
    }
    if left.lower().endpoint >= right.upper().endpoint {
        return BilateralApprox::FALSE;
    }
    return BilateralApprox::UNDECIDED;
}
