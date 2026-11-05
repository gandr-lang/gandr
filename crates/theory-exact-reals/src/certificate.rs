//! First-order certificates and their replay.
//!
//! An approximation is computed, and a computation is not evidence. A
//! [`Certificate`] records why an approximation holds: a finite list of
//! steps, each a primitive rule over the nodes of a plan and over earlier
//! steps. [`check`] replays a certificate against a validated plan with no
//! search. It derives each step's conclusion from the rule's evidence and
//! the premises' conclusions, with exact dyadic comparison and exact squares
//! alone. It never calls the interval arithmetic of the approximation pass.
//! It returns the last step's conclusion as [`Checked`], or a
//! [`CertificateRefusal`] that names the step and the check that fails.
//!
//! # Boundaries
//!
//! |Rule|Evidence|Conclusion|
//! |---|---|---|
//! |`Witnesses`|a registered cut, a point of its lower cut and a point of its upper cut|the cut's value lies strictly between the two points|
//! |`Split`|an earlier enclosure of a registered cut, a point strictly inside it, and the side whose cut holds of the point|the enclosure with that side's end moved to the point|
//! |`Constant`|a constant node|the constant's closed point|
//! |`Below`|a comparison and earlier enclosures of its two operands, the first strictly below the second|the comparison holds|
//! |`NotBelow`|a comparison and earlier enclosures of its two operands, the first at or above the second|the comparison fails|
//!
//! The checker's work is bounded. [`CheckerQuotas`] bounds the steps of a
//! certificate and the width of each dyadic in it, and the checker refuses a
//! certificate past a bound. Replay is linear in the steps, and each step
//! costs at most one exact square of a dyadic within the width bound. A
//! certificate states its [`FormatVersion`], and the checker refuses another
//! format.
//!
//! # Items
//!
//! - [`Certificate`], [`Step`], [`Side`], [`StepId`] — the certificate.
//! - [`check`], [`Checked`], [`Conclusion`] — the replay and what it proves.
//! - [`CheckerQuotas`], [`StepCount`] — the bounds of the replay.
//! - [`CertificateRefusal`], [`CertificateCheck`], [`StepSite`] — a refusal.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;

use crate::dyadic::BitWidth;
use crate::dyadic::Dyadic;
use crate::interval::Bound;
use crate::interval::Closure;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::Real;
use crate::schema::Membership;
use crate::schema::membership;
use crate::schema::radicand;
use crate::validate::ValidatedPlan;

/// The layout version of a certificate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormatVersion(u16);

impl FormatVersion
{
    /// The version that this build writes and replays.
    pub const CURRENT: Self = Self(1);
}

impl From<u16> for FormatVersion
{
    /// The version `version`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: u16) -> Self
    {
        return Self(version);
    }
}

impl From<FormatVersion> for u16
{
    /// The version as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: FormatVersion) -> Self
    {
        return version.0;
    }
}

/// The position of a step in a certificate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StepId(u32);

impl TryFrom<usize> for StepId
{
    type Error = CertificateCheck;

    /// The step at position `index`.
    ///
    /// # Specification
    /// - ensures: returns the position when it fits 32 bits.
    /// - fails: returns [`CertificateCheck::StepQuota`] past 32 bits.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CertificateCheck::StepQuota`]: the position does not fit 32 bits.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every step of every replayed certificate.
    /// - witness: `tests::certificate::the_square_root_of_two_refines_and_replays_at_each_width`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == u32::try_from(index).is_ok())]
    fn try_from(index: usize) -> Result<Self, CertificateCheck>
    {
        return u32::try_from(index)
            .map(Self)
            .map_err(|_wide| CertificateCheck::StepQuota);
    }
}

impl From<u32> for StepId
{
    /// The step at position `index`, as the codec reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        return Self(index);
    }
}

impl From<StepId> for u32
{
    /// The position as the codec writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: StepId) -> Self
    {
        return id.0;
    }
}

impl From<StepId> for usize
{
    /// The position as an index into the steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: StepId) -> Self
    {
        // A 32-bit position fits every target's `usize` that holds the steps.
        return Self::try_from(id.0).unwrap_or(Self::MAX);
    }
}

/// A count of certificate steps.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StepCount(usize);

impl From<usize> for StepCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        return Self(count);
    }
}

impl From<StepCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: StepCount) -> Self
    {
        return count.0;
    }
}

/// A side of a cut.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side
{
    /// The lower cut: the reals below the cut's value.
    Lower,
    /// The upper cut: the reals above the cut's value.
    Upper,
}

/// One step of a certificate: a primitive rule with its evidence.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Step
{
    /// The registered cut's value lies strictly between a point of its lower
    /// cut and a point of its upper cut.
    Witnesses
    {
        /// The registered cut.
        cut: NodeId,
        /// A point of the lower cut.
        lower: Dyadic,
        /// A point of the upper cut.
        upper: Dyadic,
    },
    /// A point strictly inside an earlier enclosure of a registered cut lies
    /// in the cut of `side`, so it replaces that side's end of the
    /// enclosure.
    Split
    {
        /// The step whose enclosure the split narrows.
        premise: StepId,
        /// The point.
        point: Dyadic,
        /// The side whose cut holds of the point.
        side: Side,
    },
    /// A constant node's value is its constant.
    Constant
    {
        /// The constant node.
        real: NodeId,
    },
    /// Every point of the first operand's enclosure lies strictly below every
    /// point of the second operand's, so the comparison holds.
    Below
    {
        /// The comparison.
        less: NodeId,
        /// The step that encloses the first operand.
        left: StepId,
        /// The step that encloses the second operand.
        right: StepId,
    },
    /// Every point of the first operand's enclosure lies at or above every
    /// point of the second operand's, so the comparison fails.
    NotBelow
    {
        /// The comparison.
        less: NodeId,
        /// The step that encloses the first operand.
        left: StepId,
        /// The step that encloses the second operand.
        right: StepId,
    },
}

/// What a step proves.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Conclusion
{
    /// The real node's value lies in the interval.
    Encloses
    {
        /// The real node.
        real: NodeId,
        /// A proper interval that holds the value.
        interval: NumericInterval,
    },
    /// The open node holds.
    Holds
    {
        /// The open node.
        open: NodeId,
    },
    /// The open node fails.
    Fails
    {
        /// The open node.
        open: NodeId,
    },
}

/// A certificate: its format and its steps, the last step its conclusion.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Certificate
{
    /// The layout version.
    format: FormatVersion,
    /// The steps, each after the steps it names.
    steps: Vec<Step>,
}

impl Certificate
{
    /// The certificate of `steps` in `format`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        format: FormatVersion,
        steps: Vec<Step>,
    ) -> Self
    {
        return Self { format, steps };
    }

    /// The layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn format(&self) -> FormatVersion
    {
        return self.format;
    }

    /// The steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[Step]
    {
        return &self.steps;
    }

    /// The number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn step_count(&self) -> StepCount
    {
        return StepCount(self.steps.len());
    }

    /// The steps, taken out of the certificate.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn into_steps(self) -> Vec<Step>
    {
        return self.steps;
    }
}

/// The bounds of a replay.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CheckerQuotas
{
    /// The most steps that a certificate may hold.
    pub steps: StepCount,
    /// The widest mantissa that a dyadic of a certificate may have.
    pub width: BitWidth,
}

impl Default for CheckerQuotas
{
    /// The default bounds: 65,536 steps and 65,536 bits a dyadic.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        return Self {
            steps: StepCount(1 << 16_u32),
            width: BitWidth::from(1_u64 << 16_u32),
        };
    }
}

/// The check that a certificate fails.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CertificateCheck
{
    /// The certificate states another format than this build replays.
    Format,
    /// The certificate holds no step.
    Empty,
    /// The certificate holds more steps than the step quota.
    StepQuota,
    /// A dyadic is wider than the width quota.
    WidthQuota,
    /// A step names a node that the plan does not hold.
    UnknownNode,
    /// A step names a node of another kind than its rule takes.
    WrongNode,
    /// A cut matches no registered schema.
    ForgedCut,
    /// A premise is not an earlier step.
    ForwardPremise,
    /// A premise proves another judgement than the rule takes.
    PremiseConclusion,
    /// A point does not lie in the lower cut.
    NotLower,
    /// A point does not lie in the upper cut.
    NotUpper,
    /// A split point does not lie strictly inside its enclosure.
    OutsideEnclosure,
    /// Two enclosures do not separate as the rule states.
    NotSeparated,
}

impl fmt::Display for CertificateCheck
{
    /// Write the check as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed line per variant.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::certificate::failures_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return f.write_str(match *self {
            Self::Format => "the certificate states another format",
            Self::Empty => "the certificate holds no step",
            Self::StepQuota => "the certificate holds more steps than the step quota",
            Self::WidthQuota => "a dyadic is wider than the width quota",
            Self::UnknownNode => "a step names a node that the plan does not hold",
            Self::WrongNode => "a step names a node of another kind than its rule takes",
            Self::ForgedCut => "the cut matches no registered schema",
            Self::ForwardPremise => "a premise is not an earlier step",
            Self::PremiseConclusion => "a premise proves another judgement than the rule takes",
            Self::NotLower => "a point does not lie in the lower cut",
            Self::NotUpper => "a point does not lie in the upper cut",
            Self::OutsideEnclosure => "a split point does not lie strictly inside its enclosure",
            Self::NotSeparated => "the enclosures do not separate as the rule states",
        });
    }
}

/// Where a certificate fails.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StepSite
{
    /// The certificate as a whole: its format, its length, or its absence of
    /// steps.
    Certificate,
    /// The step at this position.
    Step(StepId),
}

/// A refused certificate: where it fails and the check that fails there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CertificateRefusal
{
    /// Where the certificate fails.
    pub site: StepSite,
    /// The check that fails.
    pub check: CertificateCheck,
}

impl fmt::Display for CertificateRefusal
{
    /// Write the refusal as one line: the check, then the step.
    ///
    /// # Specification
    /// - ensures: writes the check's phrase, and the step's position for a
    ///   refusal at a step.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal of the whole certificate and one at a step.
    /// - witness: `tests::certificate::failures_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match self.site {
            StepSite::Certificate => write!(f, "{}", self.check),
            StepSite::Step(id) => write!(f, "{} at step {}", self.check, id.0),
        };
    }
}

impl core::error::Error for CertificateRefusal
{
}

/// A replayed certificate's conclusion. Only [`check`] constructs one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Checked
{
    /// What the certificate proves.
    conclusion: Conclusion,
}

impl Checked
{
    /// What the certificate proves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conclusion(&self) -> &Conclusion
    {
        return &self.conclusion;
    }
}

/// Replay `certificate` against `plan` within `quotas`.
///
/// # Specification
/// - ensures: returns the last step's conclusion when every step derives its
///   conclusion from its rule's evidence and its premises by the table of the
///   module. A positive conclusion then holds of the plan's semantics.
/// - fails: refuses another format ([`CertificateCheck::Format`]), no step
///   ([`CertificateCheck::Empty`]) and more steps than the quota
///   ([`CertificateCheck::StepQuota`]) for the whole certificate. It refuses
///   the first failing step with the check that fails there.
/// - panics: none.
/// - executable: none — the clause restates the replay.
/// - intension: one derivation per step, each at most one exact square of a
///   dyadic within the width quota. The replay holds one conclusion per step.
///
/// # Errors
/// The first [`CertificateRefusal`], at the certificate or at its step.
///
/// # Adequacy
/// - hypothesis: L2 — every refinement of generated radicands replays. L3 —
///   each check on its smallest corruption of a sound certificate, a forged
///   cut, and each quota at its bound and past it.
/// - witness: `tests::certificate::the_square_root_of_two_refines_and_replays_at_each_width`
/// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
/// - witness: `tests::certificate::a_forged_cut_is_refused`
/// - witness: `tests::certificate::quotas_bound_the_checker`
/// - witness: `tests::certificate::comparisons_with_the_cut_are_certified`
#[inline]
pub fn check(
    plan: &ValidatedPlan,
    certificate: &Certificate,
    quotas: &CheckerQuotas,
) -> Result<Checked, CertificateRefusal>
{
    let whole = |check: CertificateCheck| CertificateRefusal {
        site: StepSite::Certificate,
        check,
    };
    if certificate.format != FormatVersion::CURRENT {
        return Err(whole(CertificateCheck::Format));
    }
    if certificate.steps.len() > quotas.steps.0 {
        return Err(whole(CertificateCheck::StepQuota));
    }
    let plan = plan.plan();
    let mut conclusions: Vec<Conclusion> = Vec::with_capacity(certificate.steps.len());
    for (index, step) in certificate.steps.iter().enumerate() {
        let id = StepId::try_from(index).map_err(whole)?;
        let conclusion =
            derive(plan, step, &conclusions, quotas).map_err(|check| CertificateRefusal {
                site: StepSite::Step(id),
                check,
            })?;
        conclusions.push(conclusion);
    }
    let conclusion = conclusions
        .pop()
        .ok_or_else(|| whole(CertificateCheck::Empty))?;
    return Ok(Checked { conclusion });
}

/// The conclusion of one step, derived from its evidence and the conclusions
/// of the steps before it.
///
/// # Specification
/// - ensures: returns the conclusion of the module's table for the step's rule.
/// - fails: returns the first check of the rule that fails.
/// - panics: none.
/// - executable: none — the clause restates the table.
///
/// # Errors
/// The first failing [`CertificateCheck`] of the rule.
///
/// # Adequacy
/// - hypothesis: L3 — each rule's sound step and each of its corruptions.
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
/// - witness: `tests::certificate::comparisons_with_the_cut_are_certified`
fn derive(
    plan: &Plan,
    step: &Step,
    earlier: &[Conclusion],
    quotas: &CheckerQuotas,
) -> Result<Conclusion, CertificateCheck>
{
    let bounded = |value: &Dyadic| {
        if value.width() > quotas.width {
            return Err(CertificateCheck::WidthQuota);
        }
        return Ok(());
    };
    let premise = |id: StepId| {
        earlier
            .get(usize::from(id))
            .ok_or(CertificateCheck::ForwardPremise)
    };
    return match *step {
        Step::Witnesses {
            cut,
            ref lower,
            ref upper,
        } => {
            let radicand = radicand(plan, cut)?;
            bounded(lower)?;
            bounded(upper)?;
            if membership(lower, &radicand)? != Membership::Lower {
                return Err(CertificateCheck::NotLower);
            }
            if membership(upper, &radicand)? != Membership::Upper {
                return Err(CertificateCheck::NotUpper);
            }
            // A point of the lower cut lies below a point of the upper cut, so
            // the open interval between them is proper and not empty.
            let interval = NumericInterval::new(
                Bound::open(Endpoint::Finite(lower.clone())),
                Bound::open(Endpoint::Finite(upper.clone())),
                Orientation::Proper,
            )
            .map_err(|_reversed| CertificateCheck::NotUpper)?;
            Ok(Conclusion::Encloses {
                real: cut,
                interval,
            })
        },
        Step::Split {
            premise: id,
            ref point,
            side,
        } => {
            let Conclusion::Encloses { real, ref interval } = *premise(id)?
            else {
                return Err(CertificateCheck::PremiseConclusion);
            };
            let radicand =
                radicand(plan, real).map_err(|_other| CertificateCheck::PremiseConclusion)?;
            bounded(point)?;
            let inside = Endpoint::Finite(point.clone());
            if !(interval.lower().endpoint < inside && inside < interval.upper().endpoint) {
                return Err(CertificateCheck::OutsideEnclosure);
            }
            let (lower, upper) = match (side, membership(point, &radicand)?) {
                (Side::Lower, Membership::Lower) => (Bound::open(inside), interval.upper().clone()),
                (Side::Upper, Membership::Upper) => (interval.lower().clone(), Bound::open(inside)),
                (Side::Lower, Membership::Upper | Membership::Root) => {
                    return Err(CertificateCheck::NotLower);
                },
                (Side::Upper, Membership::Lower | Membership::Root) => {
                    return Err(CertificateCheck::NotUpper);
                },
            };
            let interval = NumericInterval::new(lower, upper, Orientation::Proper)
                .map_err(|_reversed| CertificateCheck::OutsideEnclosure)?;
            Ok(Conclusion::Encloses { real, interval })
        },
        Step::Constant { real } => {
            let Node::Real(Real::Constant(ref value)) = *plan
                .node(real)
                .map_err(|_unknown| CertificateCheck::UnknownNode)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            bounded(value)?;
            Ok(Conclusion::Encloses {
                real,
                interval: NumericInterval::point(value.clone()),
            })
        },
        Step::Below { less, left, right } | Step::NotBelow { less, left, right } => {
            let Node::Open(Open::Less(first, second)) = *plan
                .node(less)
                .map_err(|_unknown| CertificateCheck::UnknownNode)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            let enclosure = |id: StepId, operand: NodeId| match *premise(id)? {
                Conclusion::Encloses { real, ref interval } if real == operand => Ok(interval),
                Conclusion::Encloses { .. }
                | Conclusion::Holds { .. }
                | Conclusion::Fails { .. } => Err(CertificateCheck::PremiseConclusion),
            };
            let (first, second) = (
                enclosure(left, first.node())?,
                enclosure(right, second.node())?,
            );
            if matches!(*step, Step::Below { .. }) {
                separated_below(first, second)?;
                Ok(Conclusion::Holds { open: less })
            }
            else {
                if first.lower().endpoint < second.upper().endpoint {
                    return Err(CertificateCheck::NotSeparated);
                }
                Ok(Conclusion::Fails { open: less })
            }
        },
    };
}

/// Check that every point of `first` lies strictly below every point of
/// `second`.
///
/// # Specification
/// - requires: both intervals are proper.
/// - ensures: succeeds when the upper end of `first` lies below the lower end
///   of `second`, or equals it with either end open.
/// - fails: returns [`CertificateCheck::NotSeparated`] otherwise.
/// - panics: none.
///
/// # Errors
/// - [`CertificateCheck::NotSeparated`]: the enclosures touch at closed ends or
///   overlap.
///
/// # Adequacy
/// - hypothesis: L3 — separated enclosures, touching ends of each closure, and
///   overlapping enclosures.
/// - witness: `tests::certificate::comparisons_with_the_cut_are_certified`
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
#[spec(
    requires: first.orientation() == Orientation::Proper && second.orientation() == Orientation::Proper,
    ensures: |ref result| result.is_ok() == (first.upper().endpoint < second.lower().endpoint || (first.upper().endpoint == second.lower().endpoint && (first.upper().closure == Closure::Open || second.lower().closure == Closure::Open))),
)]
fn separated_below(
    first: &NumericInterval,
    second: &NumericInterval,
) -> Result<(), CertificateCheck>
{
    let separated = match first.upper().endpoint.cmp(&second.lower().endpoint) {
        Ordering::Less => true,
        Ordering::Equal => {
            first.upper().closure == Closure::Open || second.lower().closure == Closure::Open
        },
        Ordering::Greater => false,
    };
    if separated {
        return Ok(());
    }
    return Err(CertificateCheck::NotSeparated);
}
