//! Registered cuts: the cut schema that the checker knows, and the
//! refinement of such a cut to a requested width.
//!
//! A cut defines a real by its lower and its upper cut. A certificate can use
//! a cut only when the checker knows the theorem that gives the cut's laws.
//! Stage A knows one schema: the square root of a positive dyadic `c`. Its
//! lower cut holds of `x` when `x < 0` or `x · x < c`, and its upper cut
//! holds of `x` when `0 < x` and `c < x · x`. Exact arithmetic decides both
//! cuts at a dyadic, so the checker checks a dyadic witness of either side
//! with no search.
//!
//! [`square_root`] builds the cut, and [`radicand`] recognises it in a plan.
//! A cut of any other shape is a forged cut. Its laws evidence names a
//! theorem that no schema states, and the checker refuses it. [`refine`]
//! halves an enclosure of a registered cut until the enclosure is no wider
//! than a requested power of two, and it writes one certificate step for
//! each halving.
//!
//! # Items
//!
//! - [`square_root`], [`square_root_of_two`] — the builders of the cut.
//! - [`radicand`] — the recognition of the schema in a plan.
//! - [`refine`] — the refinement and its certificate.

use alloc::vec;
use core::cmp::Ordering;

use num_bigint::BigInt;

use crate::certificate::Certificate;
use crate::certificate::CertificateCheck;
use crate::certificate::CheckerQuotas;
use crate::certificate::FormatVersion;
use crate::certificate::Side;
use crate::certificate::Step;
use crate::certificate::StepId;
use crate::dyadic::Dyadic;
use crate::dyadic::DyadicError;
use crate::dyadic::Exactness;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::dyadic::Rounded;
use crate::dyadic::Rounding;
use crate::dyadic::Sign;
use crate::interval::Bound;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Cut;
use crate::plan::DeBruijn;
use crate::plan::Evidence;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::OpenId;
use crate::plan::Plan;
use crate::plan::PlanBuilder;
use crate::plan::PlanError;
use crate::plan::Real;
use crate::plan::RealId;
use crate::validate::ValidatedPlan;

/// Where a dyadic lies against the square root of a radicand.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Membership
{
    /// The dyadic lies in the lower cut.
    Lower,
    /// The dyadic lies in the upper cut.
    Upper,
    /// The dyadic is the root itself, in neither cut.
    Root,
}

/// Build the registered cut of the square root of `radicand`.
///
/// # Specification
/// - ensures: appends the bound variable, zero, the radicand, the square of the
///   variable, the four comparisons, the join, the meet and the cut, and
///   returns the cut.
/// - fails: returns the builder's failure, which only a full builder gives.
/// - panics: none.
/// - executable: none — the clause restates the construction.
///
/// # Errors
/// - [`PlanError::TooManyNodes`]: the builder holds no more nodes.
///
/// # Adequacy
/// - hypothesis: L2 — every plan of the certificate tests builds its cut here,
///   and [`radicand`] recognises each one.
/// - witness: `tests::certificate::the_square_root_of_two_refines_and_replays_at_each_width`
/// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
#[inline]
pub fn square_root(
    builder: &mut PlanBuilder,
    radicand: Dyadic,
    hull: NumericInterval,
    laws: Evidence,
) -> Result<RealId, PlanError>
{
    let x = builder.real(Real::Bound(DeBruijn::from(0_u32)))?;
    let zero = builder.real(Real::Constant(Dyadic::ZERO))?;
    let radicand = builder.real(Real::Constant(radicand))?;
    let square = builder.real(Real::Mul(x, x))?;
    let negative = builder.open(Open::Less(x, zero))?;
    let small = builder.open(Open::Less(square, radicand))?;
    let lower = builder.open(Open::Join(negative, small))?;
    let positive = builder.open(Open::Less(zero, x))?;
    let large = builder.open(Open::Less(radicand, square))?;
    let upper = builder.open(Open::Meet(positive, large))?;
    return builder.real(Real::Cut(Cut {
        hull,
        lower,
        upper,
        laws,
    }));
}

/// Build the registered cut of the square root of two, whose hull is the
/// closed interval from one to two.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`PlanError::TooManyNodes`]: the builder holds no more nodes.
#[inline]
pub fn square_root_of_two(
    builder: &mut PlanBuilder,
    laws: Evidence,
) -> Result<RealId, PlanError>
{
    let hull = NumericInterval::new(
        Bound::closed(Dyadic::ONE),
        Bound::closed(Dyadic::from(2_i64)),
        Orientation::Proper,
    )
    .map_err(|_unreachable| PlanError::WrongSort)?;
    return square_root(builder, Dyadic::from(2_i64), hull, laws);
}

/// The radicand of the registered cut at `node`.
///
/// # Specification
/// - ensures: returns the radicand `c` of a cut whose lower cut is the join of
///   `x < 0` and `x · x < c`, and whose upper cut is the meet of `0 < x` and `c
///   < x · x`. Here `c` is a positive constant and `x` is the cut's own
///   variable.
/// - fails: refuses a position past the plan as
///   [`CertificateCheck::UnknownNode`], a node that is not a cut as
///   [`CertificateCheck::WrongNode`], and a cut of any other shape as
///   [`CertificateCheck::ForgedCut`].
/// - panics: none.
/// - executable: none — the clause restates the match.
///
/// # Errors
/// - [`CertificateCheck::UnknownNode`]: no node stands at `node`.
/// - [`CertificateCheck::WrongNode`]: the node is not a cut.
/// - [`CertificateCheck::ForgedCut`]: the cut has another shape.
///
/// # Adequacy
/// - hypothesis: L3 — the registered cut, a cut whose upper cut names another
///   constant, and a node that is not a cut.
/// - witness: `tests::certificate::a_forged_cut_is_refused`
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
#[inline]
pub fn radicand(
    plan: &Plan,
    node: NodeId,
) -> Result<Dyadic, CertificateCheck>
{
    let cut = match *plan
        .node(node)
        .map_err(|_unknown| CertificateCheck::UnknownNode)?
    {
        Node::Real(Real::Cut(ref cut)) => cut,
        Node::Real(_) | Node::Open(_) | Node::Domain(_) => return Err(CertificateCheck::WrongNode),
    };
    let real = |id: RealId| match plan.node(id.node()) {
        Ok(&Node::Real(ref real)) => Ok(real),
        Ok(&(Node::Open(_) | Node::Domain(_))) | Err(_) => Err(CertificateCheck::ForgedCut),
    };
    let open = |id: OpenId| match plan.node(id.node()) {
        Ok(&Node::Open(ref open)) => Ok(open),
        Ok(&(Node::Real(_) | Node::Domain(_))) | Err(_) => Err(CertificateCheck::ForgedCut),
    };
    let (&Open::Join(negative, small), &Open::Meet(positive, large)) =
        (open(cut.lower)?, open(cut.upper)?)
    else {
        return Err(CertificateCheck::ForgedCut);
    };
    let (
        &Open::Less(x, zero),
        &Open::Less(square, radicand),
        &Open::Less(zero_again, x_again),
        &Open::Less(radicand_again, square_again),
    ) = (open(negative)?, open(small)?, open(positive)?, open(large)?)
    else {
        return Err(CertificateCheck::ForgedCut);
    };
    let shared =
        x == x_again && zero == zero_again && square == square_again && radicand == radicand_again;
    let variable = *real(x)? == Real::Bound(DeBruijn::from(0_u32));
    let origin = *real(zero)? == Real::Constant(Dyadic::ZERO);
    let squared = *real(square)? == Real::Mul(x, x);
    let Real::Constant(ref value) = *real(radicand)?
    else {
        return Err(CertificateCheck::ForgedCut);
    };
    if !(shared && variable && origin && squared && value.sign() == Sign::Positive) {
        return Err(CertificateCheck::ForgedCut);
    }
    return Ok(value.clone());
}

/// Where `point` lies against the square root of `radicand`.
///
/// # Specification
/// - requires: `radicand` is positive.
/// - ensures: [`Membership::Lower`] when `point < 0` or `point · point <
///   radicand`, [`Membership::Upper`] when `0 < point` and `radicand < point ·
///   point`, and [`Membership::Root`] otherwise.
/// - fails: refuses a point whose exact square does not fit the precision quota
///   as [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the comparison.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: the exact square is too wide.
///
/// # Adequacy
/// - hypothesis: L2 — every witness and split point of the generated
///   refinements, held to the rational oracle. L3 — a point of each side.
/// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
pub(crate) fn membership(
    point: &Dyadic,
    radicand: &Dyadic,
) -> Result<Membership, CertificateCheck>
{
    let square = point
        .mul(point, Precision::MAX, Rounding::Floor)
        .map_err(|_overflow| CertificateCheck::WidthQuota)?;
    if square.exactness() != Exactness::Exact {
        return Err(CertificateCheck::WidthQuota);
    }
    let square = square.value();
    return Ok(match (point.sign(), square.cmp(radicand)) {
        (Sign::Negative, _) | (Sign::Zero | Sign::Positive, Ordering::Less) => Membership::Lower,
        (Sign::Positive, Ordering::Greater) => Membership::Upper,
        (Sign::Zero, Ordering::Greater) | (Sign::Positive | Sign::Zero, Ordering::Equal) => {
            Membership::Root
        },
    });
}

/// The finite dyadic of a bound, or [`CertificateCheck::WrongNode`] for an
/// infinity.
///
/// # Specification
/// trivial.
fn finite(bound: &Bound) -> Result<Dyadic, CertificateCheck>
{
    return match bound.endpoint {
        Endpoint::Finite(ref value) => Ok(value.clone()),
        Endpoint::NegInf | Endpoint::PosInf => Err(CertificateCheck::WrongNode),
    };
}

/// An enclosure of a registered cut as halvings narrow it: the cut's radicand
/// and the two ends, each a witness of its side.
///
/// # Specification
/// - invariant: `lower` lies in the lower cut and `upper` in the upper cut of
///   the square root of `radicand`, so `lower < upper`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Refinement
{
    /// The radicand of the cut.
    radicand: Dyadic,
    /// A point of the lower cut, the lower end of the enclosure.
    lower: Dyadic,
    /// A point of the upper cut, the upper end of the enclosure.
    upper: Dyadic,
}

impl Refinement
{
    /// The refinement of the registered cut at `cut`, from the ends of its
    /// hull, and the step that states them.
    ///
    /// # Specification
    /// - ensures: the step is [`Step::Witnesses`] with the ends of the cut's
    ///   hull, which [`crate::certificate::check`] accepts as the first step of
    ///   an enclosure.
    /// - fails: refuses a node that is not a registered cut as [`radicand`]
    ///   does, and a hull end that is not a witness of its side as
    ///   [`CertificateCheck::NotLower`] or [`CertificateCheck::NotUpper`].
    /// - panics: none.
    /// - executable: none — the checker's replay is the clause.
    ///
    /// # Errors
    /// - [`CertificateCheck::UnknownNode`], [`CertificateCheck::WrongNode`],
    ///   [`CertificateCheck::ForgedCut`]: as [`radicand`].
    /// - [`CertificateCheck::NotLower`], [`CertificateCheck::NotUpper`]: a hull
    ///   end is not a witness.
    /// - [`CertificateCheck::WidthQuota`]: a hull end is too wide to square.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`refine`], which starts each refinement here.
    /// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
    pub(crate) fn start(
        plan: &Plan,
        cut: NodeId,
    ) -> Result<(Self, Step), CertificateCheck>
    {
        let radicand = radicand(plan, cut)?;
        let Ok(&Node::Real(Real::Cut(ref registered))) = plan.node(cut)
        else {
            return Err(CertificateCheck::WrongNode);
        };
        let (lower, upper) = (
            finite(registered.hull.lower())?,
            finite(registered.hull.upper())?,
        );
        if membership(&lower, &radicand)? != Membership::Lower {
            return Err(CertificateCheck::NotLower);
        }
        if membership(&upper, &radicand)? != Membership::Upper {
            return Err(CertificateCheck::NotUpper);
        }
        let step = Step::Witnesses {
            cut,
            lower: lower.clone(),
            upper: upper.clone(),
        };
        return Ok((
            Self {
                radicand,
                lower,
                upper,
            },
            step,
        ));
    }

    /// The refinement of the registered cut at `cut` whose enclosure has the
    /// ends `lower` and `upper`, as a replayed `Witnesses` step states them.
    ///
    /// # Specification
    /// - requires: [`crate::certificate::check`] accepts a `Witnesses` step of
    ///   `cut` with these ends, so each end is a witness of its side.
    /// - ensures: the enclosure has these ends.
    /// - fails: refuses a node that is not a registered cut as [`radicand`]
    ///   does.
    /// - panics: none.
    /// - executable: none — the requirement speaks of the replay of a step.
    ///
    /// # Errors
    /// - [`CertificateCheck::UnknownNode`], [`CertificateCheck::WrongNode`],
    ///   [`CertificateCheck::ForgedCut`]: as [`radicand`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`crate::dovetail::Dovetail::resume`], which
    ///   rebuilds each enclosure here.
    /// - witness: `tests::checkpoint::a_resumed_run_certifies_as_an_unbroken_one`
    pub(crate) fn witnessed(
        plan: &Plan,
        cut: NodeId,
        (lower, upper): (Dyadic, Dyadic),
    ) -> Result<Self, CertificateCheck>
    {
        let radicand = radicand(plan, cut)?;
        return Ok(Self {
            radicand,
            lower,
            upper,
        });
    }

    /// Narrow the enclosure as a replayed `Split` step states: `point`
    /// replaces the end of `side`.
    ///
    /// # Specification
    /// - requires: [`crate::certificate::check`] accepts the split of this
    ///   enclosure at `point` on `side`.
    /// - ensures: the end of `side` is `point`.
    /// - panics: none.
    /// - executable: none — the requirement speaks of the replay of a step.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`crate::dovetail::Dovetail::resume`], which
    ///   narrows each rebuilt enclosure here.
    /// - witness: `tests::checkpoint::every_checkpoint_resumes_to_the_unbroken_run`
    pub(crate) fn split(
        &mut self,
        point: Dyadic,
        side: Side,
    )
    {
        match side {
            Side::Lower => self.lower = point,
            Side::Upper => self.upper = point,
        }
    }

    /// The lower end of the enclosure.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lower(&self) -> &Dyadic
    {
        return &self.lower;
    }

    /// The upper end of the enclosure.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn upper(&self) -> &Dyadic
    {
        return &self.upper;
    }

    /// The width of the enclosure.
    ///
    /// # Specification
    /// - ensures: `upper - lower`, computed exactly.
    /// - fails: refuses a difference too wide to compute as
    ///   [`CertificateCheck::WidthQuota`].
    /// - panics: none.
    /// - executable: none — the clause restates the subtraction.
    ///
    /// # Errors
    /// - [`CertificateCheck::WidthQuota`]: the difference is too wide.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each enclosure that generated obligations ask for
    ///   meets its width, and its certificate replays to it.
    /// - witness: `tests::dovetail::every_certificate_replays_to_its_evidence`
    pub(crate) fn gap(&self) -> Result<Dyadic, CertificateCheck>
    {
        return exact(self.upper.sub(&self.lower, Precision::MAX, Rounding::Floor));
    }

    /// Halve the enclosure at its midpoint, and the step that states the
    /// halving of the enclosure that the step `premise` concludes.
    ///
    /// # Specification
    /// - requires: the step `premise` concludes the current enclosure.
    /// - ensures: the step is [`Step::Split`] at the midpoint, on the side its
    ///   cut holds of. A midpoint that is the root itself gives way to the
    ///   midpoint of the lower half. The new end replaces the old end of its
    ///   side, so the enclosure holds half its width or less.
    /// - fails: refuses a midpoint wider than the quota as
    ///   [`CertificateCheck::WidthQuota`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the cut that the step replays
    ///   against.
    /// - intension: two exact additions, two exact halvings and at most two
    ///   exact squares.
    ///
    /// # Errors
    /// - [`CertificateCheck::WidthQuota`]: a midpoint is too wide.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`refine`], which halves each refinement here.
    /// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
    pub(crate) fn halve(
        &mut self,
        premise: StepId,
        quotas: &CheckerQuotas,
    ) -> Result<Step, CertificateCheck>
    {
        let middle = midpoint(&self.lower, &self.upper)?;
        if middle.width() > quotas.width {
            return Err(CertificateCheck::WidthQuota);
        }
        let (point, side) = match membership(&middle, &self.radicand)? {
            Membership::Lower => (middle, Side::Lower),
            Membership::Upper => (middle, Side::Upper),
            Membership::Root => (midpoint(&self.lower, &middle)?, Side::Lower),
        };
        match side {
            Side::Lower => self.lower = point.clone(),
            Side::Upper => self.upper = point.clone(),
        }
        return Ok(Step::Split {
            premise,
            point,
            side,
        });
    }
}

/// The exact value of `result`, or [`CertificateCheck::WidthQuota`] when the
/// operation overflows.
///
/// # Specification
/// trivial.
pub(crate) fn exact(result: Result<Rounded, DyadicError>) -> Result<Dyadic, CertificateCheck>
{
    return result
        .map_err(|_overflow| CertificateCheck::WidthQuota)
        .map(Rounded::into_value);
}

/// The midpoint of `low` and `high`, computed exactly.
///
/// # Specification
/// trivial.
pub(crate) fn midpoint(
    low: &Dyadic,
    high: &Dyadic,
) -> Result<Dyadic, CertificateCheck>
{
    let half = Dyadic::new(BigInt::from(1_u8), Exponent::from(-1_i32))
        .map_err(|_overflow| CertificateCheck::WidthQuota)?;
    let sum = exact(low.add(high, Precision::MAX, Rounding::Floor))?;
    return exact(sum.mul(&half, Precision::MAX, Rounding::Floor));
}

/// The certificate of an enclosure of the registered cut at `cut` no wider
/// than `2^width`.
///
/// # Specification
/// - ensures: the certificate's first step names the ends of the cut's hull as
///   witnesses, and each later step splits the previous enclosure at its
///   midpoint. A midpoint that is the root itself gives way to the midpoint of
///   the lower half. [`crate::certificate::check`] accepts the certificate, and
///   its last enclosure is no wider than `2^width`.
/// - fails: refuses a node that is not a registered cut as [`radicand`] does, a
///   hull end that is not a witness of its side as
///   [`CertificateCheck::NotLower`] or [`CertificateCheck::NotUpper`], and a
///   refinement that needs more steps than the quota as
///   [`CertificateCheck::StepQuota`].
/// - panics: none.
/// - executable: none — the checker's replay is the clause.
/// - intension: one step for each halving, so a hull of width one takes one
///   step for each bit of the requested width.
///
/// # Errors
/// - [`CertificateCheck::UnknownNode`], [`CertificateCheck::WrongNode`],
///   [`CertificateCheck::ForgedCut`]: as [`radicand`].
/// - [`CertificateCheck::NotLower`], [`CertificateCheck::NotUpper`]: a hull end
///   is not a witness.
/// - [`CertificateCheck::StepQuota`]: the refinement needs too many steps.
/// - [`CertificateCheck::WidthQuota`]: a midpoint is too wide.
///
/// # Adequacy
/// - hypothesis: L2 — generated radicands refined to generated widths, each
///   certificate replayed and its enclosure held to the rational oracle. L3 —
///   the square root of two at each width from `2^-8` to `2^-256`, and a step
///   quota one below what a width needs.
/// - witness: `tests::certificate::the_square_root_of_two_refines_and_replays_at_each_width`
/// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
/// - witness: `tests::certificate::quotas_bound_the_checker`
#[inline]
pub fn refine(
    plan: &ValidatedPlan,
    cut: NodeId,
    width: Exponent,
    quotas: &CheckerQuotas,
) -> Result<Certificate, CertificateCheck>
{
    let (mut refinement, first) = Refinement::start(plan.plan(), cut)?;
    let target =
        Dyadic::new(BigInt::from(1_u8), width).map_err(|_overflow| CertificateCheck::WidthQuota)?;
    let mut steps = vec![first];
    while refinement.gap()? > target {
        if steps.len() >= usize::from(quotas.steps) {
            return Err(CertificateCheck::StepQuota);
        }
        let premise = StepId::try_from(steps.len().saturating_sub(1))
            .map_err(|_wide| CertificateCheck::StepQuota)?;
        steps.push(refinement.halve(premise, quotas)?);
    }
    return Ok(Certificate::new(FormatVersion::CURRENT, steps));
}
