//! First-order certificates and their replay.
//!
//! An approximation is computed, and a computation is not evidence. A
//! [`Certificate`] records why an approximation holds: a finite list of
//! steps, each a primitive rule over the nodes of a plan and over earlier
//! steps. [`check`] replays a certificate against a validated plan with no
//! search. It derives each step's conclusion from the rule's evidence and
//! the premises' conclusions, with exact dyadic arithmetic and comparison
//! alone. It never calls the interval arithmetic of the approximation pass.
//! It returns the last step's conclusion as [`Checked`], or a
//! [`CertificateRefusal`] that names the step and the check that fails.
//!
//! A step can hold under a hypothesis: the variable at de Bruijn index zero
//! lies in a closed interval. `Variable` states the hypothesis. A rule with
//! two premises refuses premises under two different hypotheses. A
//! premise with no hypothesis holds under every hypothesis. `Witness`,
//! `Cover`, `Counterexample` and `Refutation` discharge the hypothesis at the
//! quantifier that binds the variable. The last step of a certificate holds
//! under no hypothesis.
//!
//! # Boundaries
//!
//! |Rule|Evidence|Conclusion|
//! |---|---|---|
//! |`Witnesses`|a registered cut and a point of each of its two cuts|the cut's value lies strictly between the points|
//! |`Split`|an enclosure of a cut, a point inside it, and the side whose cut holds of it|the enclosure with that side's end at the point|
//! |`Constant`|a constant node|the constant's closed point|
//! |`Below`|a comparison and enclosures of its operands, the first strictly below the second|the comparison holds|
//! |`NotBelow`|a comparison and enclosures of its operands, the first at or above the second|the comparison fails|
//! |`Inside`|a lower or an upper cut at a point, or the comparison it replaces, and an enclosure of the point whose end toward the cut's value lies in that cut|the open node holds|
//! |`Outside`|the same node, and an enclosure of the point whose end toward the cut's value lies outside that cut|the open node fails|
//! |`Variable`|the variable at index zero and a closed interval|the variable lies in it, under that hypothesis|
//! |`Sum`, `Difference`, `Product`|the node, and enclosures of its operands|the exact result on them|
//! |`Quotient`, `Power`|as above, and a precision|the result, rounded outward at that precision|
//! |`Pi`|the π node and a precision|the enclosure of π by its rule at that precision|
//! |`Cosine`, `Sine`, `Recurrence`|the node, an enclosure of its argument, and a precision|the enclosure of the rule over that enclosure|
//! |`Angle`|the node, enclosures of its two coordinates, and a precision|the enclosure of the rule over their box|
//! |`Witness`|an existential over an interval, and its body holding under a hypothesis inside it|the existential holds|
//! |`Cover`|a universal over a closed interval, and its body holding under hypotheses that tile it in order|the universal holds|
//! |`Counterexample`|an overt universal, and its body failing under a hypothesis inside its domain|the universal fails|
//! |`Refutation`|a compact existential, and its body failing under hypotheses that tile its domain in order|the existential fails|
//!
//! # Items
//!
//! - [`Certificate`], [`Step`], [`Side`], [`StepId`] — the certificate.
//! - [`check`], [`Checked`], [`Conclusion`] — the replay and what it proves.
//! - [`CheckerQuotas`], [`StepCount`] — the bounds of the replay.
//! - [`CertificateRefusal`], [`CertificateCheck`], [`StepSite`] — a refusal.
//!
//! The checker's work is bounded. [`CheckerQuotas`] bounds the steps of a
//! certificate and the width of each dyadic in it, and the checker refuses a
//! certificate past a bound. Replay is linear in the steps and in the
//! premises of each cover. An arithmetic step costs at most one exact square
//! or four exact products of dyadics within the width bound. A quotient step
//! costs eight rounded quotients, and a power step eight rounded products for
//! each bit of its power. A builtin's step sums the series of its rule at its
//! precision `p`: at most `4p + 64` terms each, and each term costs one
//! rounded product or division within the width bound. A recurrence step sums
//! its count of terms, at most 65,536. A certificate states its
//! [`FormatVersion`], and the checker refuses another format.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;

use crate::dyadic::BitWidth;
use crate::dyadic::Dyadic;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::dyadic::Sign;
use crate::elementary::angle;
use crate::elementary::cosine;
use crate::elementary::pi;
use crate::elementary::sine;
use crate::elementary::width;
use crate::interval::Bound;
use crate::interval::Closure;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::DeBruijn;
use crate::plan::Domain;
use crate::plan::EvidenceSlot;
use crate::plan::Node;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::Power;
use crate::plan::Quantifier;
use crate::plan::Real;
use crate::recurrence::Terms;
use crate::recurrence::series_after;
use crate::schema::Membership;
use crate::schema::exact;
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
    /// The variable at de Bruijn index zero lies in the closed interval from
    /// `lower` to `upper`. Each step that rests on this one holds under that
    /// hypothesis.
    Variable
    {
        /// The variable's node.
        real: NodeId,
        /// The lower end of the interval.
        lower: Dyadic,
        /// The upper end of the interval.
        upper: Dyadic,
    },
    /// A sum lies in the exact sum of its operands' enclosures.
    Sum
    {
        /// The sum.
        real: NodeId,
        /// The step that encloses the first operand.
        left: StepId,
        /// The step that encloses the second operand.
        right: StepId,
    },
    /// A difference lies in the exact difference of its operands'
    /// enclosures.
    Difference
    {
        /// The difference.
        real: NodeId,
        /// The step that encloses the first operand.
        left: StepId,
        /// The step that encloses the second operand.
        right: StepId,
    },
    /// A product lies between the least and the greatest exact product of
    /// its operands' ends.
    Product
    {
        /// The product.
        real: NodeId,
        /// The step that encloses the first operand.
        left: StepId,
        /// The step that encloses the second operand.
        right: StepId,
    },
    /// The body of an existential holds under a hypothesis inside its domain,
    /// so the existential holds.
    Witness
    {
        /// The existential.
        exists: NodeId,
        /// The step that concludes the body under the hypothesis.
        premise: StepId,
    },
    /// The body of a universal holds under each of a list of hypotheses that
    /// tile its domain in order, so the universal holds.
    Cover
    {
        /// The universal.
        forall: NodeId,
        /// The steps that conclude the body, one for each piece of the
        /// domain, from its lower end to its upper end.
        premises: Vec<StepId>,
    },
    /// The body of a universal fails under a hypothesis inside its domain, so
    /// the universal fails.
    Counterexample
    {
        /// The universal.
        forall: NodeId,
        /// The step that concludes the failure of the body under the
        /// hypothesis.
        premise: StepId,
    },
    /// The body of an existential fails under each of a list of hypotheses
    /// that tile its domain in order, so the existential fails.
    Refutation
    {
        /// The existential.
        exists: NodeId,
        /// The steps that conclude the failure of the body, one for each piece
        /// of the domain, from its lower end to its upper end.
        premises: Vec<StepId>,
    },
    /// The end of a point's enclosure lies in the cut of `side` of a
    /// registered cut, so the point lies in that cut and the open node holds.
    Inside
    {
        /// The cut node of `side` at the point, or the comparison of the point
        /// with the cut that it replaces.
        open: NodeId,
        /// The step that encloses the point.
        point: StepId,
        /// The cut that the point lies in.
        side: Side,
    },
    /// The end of a point's enclosure lies outside the cut of `side` of a
    /// registered cut, so the point lies outside that cut and the open node
    /// fails.
    Outside
    {
        /// The cut node of `side` at the point, or the comparison of the point
        /// with the cut that it replaces.
        open: NodeId,
        /// The step that encloses the point.
        point: StepId,
        /// The cut that the point lies outside.
        side: Side,
    },
    /// π lies in the enclosure of its rule at a precision.
    Pi
    {
        /// The π node.
        real: NodeId,
        /// The absolute bits of the rule.
        precision: Precision,
    },
    /// A cosine lies in the enclosure of its rule over its argument's
    /// enclosure at a precision.
    Cosine
    {
        /// The cosine.
        real: NodeId,
        /// The step that encloses the argument.
        argument: StepId,
        /// The absolute bits of the rule.
        precision: Precision,
    },
    /// A sine lies in the enclosure of its rule over its argument's enclosure
    /// at a precision.
    Sine
    {
        /// The sine.
        real: NodeId,
        /// The step that encloses the argument.
        argument: StepId,
        /// The absolute bits of the rule.
        precision: Precision,
    },
    /// An angle lies in the enclosure of its rule over the box of its
    /// coordinates' enclosures at a precision.
    Angle
    {
        /// The angle.
        real: NodeId,
        /// The step that encloses the first coordinate.
        x: StepId,
        /// The step that encloses the second coordinate.
        y: StepId,
        /// The absolute bits of the rule.
        precision: Precision,
    },
    /// A recurrence lies in the enclosure of its rule over its argument's
    /// enclosure at a precision: the partial sum of its count of terms,
    /// widened by the tail bound after them.
    Recurrence
    {
        /// The recurrence.
        real: NodeId,
        /// The step that encloses the argument.
        argument: StepId,
        /// The count of terms in the partial sum.
        terms: Terms,
        /// The absolute bits of the rule.
        precision: Precision,
    },
    /// A quotient lies in the quotient of its operands' enclosures, rounded
    /// outward at a precision, when the divisor's enclosure is apart from
    /// zero.
    Quotient
    {
        /// The quotient.
        real: NodeId,
        /// The step that encloses the dividend.
        numerator: StepId,
        /// The step that encloses the divisor.
        denominator: StepId,
        /// The significant bits of the rounding.
        precision: Precision,
    },
    /// A power lies in the power of its base's enclosure, by repeated
    /// squaring, each product rounded outward at a precision.
    Power
    {
        /// The power.
        real: NodeId,
        /// The step that encloses the base.
        base: StepId,
        /// The significant bits of each rounding.
        precision: Precision,
    },
}

impl Step
{
    /// The step with each node that it names moved by `rename`, or `None`
    /// when `rename` has no place for one of them. Premises keep their
    /// positions.
    ///
    /// # Specification
    /// - ensures: the step of the same rule, with the same points and premises,
    ///   whose nodes are the places that `rename` gives.
    /// - fails: returns `None` when `rename` answers `None` for a node.
    /// - panics: none.
    /// - executable: none — the clause restates the step's fields.
    /// - intension: one call of `rename`, and one copy of the step's points and
    ///   premises.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every certificate of the generated corpus moves into
    ///   the plan that its node roots and back to itself.
    /// - witness: `tests::cache::a_certificate_moves_to_the_rooted_plan_and_back`
    pub(crate) fn renamed<Rename>(
        &self,
        rename: Rename,
    ) -> Option<Self>
    where
        Rename: Fn(NodeId) -> Option<NodeId>,
    {
        return Some(match *self {
            Self::Witnesses {
                cut,
                ref lower,
                ref upper,
            } => Self::Witnesses {
                cut: rename(cut)?,
                lower: lower.clone(),
                upper: upper.clone(),
            },
            Self::Split {
                premise,
                ref point,
                side,
            } => Self::Split {
                premise,
                point: point.clone(),
                side,
            },
            Self::Constant { real } => Self::Constant {
                real: rename(real)?,
            },
            Self::Below { less, left, right } => Self::Below {
                less: rename(less)?,
                left,
                right,
            },
            Self::NotBelow { less, left, right } => Self::NotBelow {
                less: rename(less)?,
                left,
                right,
            },
            Self::Variable {
                real,
                ref lower,
                ref upper,
            } => Self::Variable {
                real: rename(real)?,
                lower: lower.clone(),
                upper: upper.clone(),
            },
            Self::Sum { real, left, right } => Self::Sum {
                real: rename(real)?,
                left,
                right,
            },
            Self::Difference { real, left, right } => Self::Difference {
                real: rename(real)?,
                left,
                right,
            },
            Self::Product { real, left, right } => Self::Product {
                real: rename(real)?,
                left,
                right,
            },
            Self::Witness { exists, premise } => Self::Witness {
                exists: rename(exists)?,
                premise,
            },
            Self::Cover {
                forall,
                ref premises,
            } => Self::Cover {
                forall: rename(forall)?,
                premises: premises.clone(),
            },
            Self::Counterexample { forall, premise } => Self::Counterexample {
                forall: rename(forall)?,
                premise,
            },
            Self::Refutation {
                exists,
                ref premises,
            } => Self::Refutation {
                exists: rename(exists)?,
                premises: premises.clone(),
            },
            Self::Inside { open, point, side } => Self::Inside {
                open: rename(open)?,
                point,
                side,
            },
            Self::Outside { open, point, side } => Self::Outside {
                open: rename(open)?,
                point,
                side,
            },
            Self::Pi { real, precision } => Self::Pi {
                real: rename(real)?,
                precision,
            },
            Self::Cosine {
                real,
                argument,
                precision,
            } => Self::Cosine {
                real: rename(real)?,
                argument,
                precision,
            },
            Self::Sine {
                real,
                argument,
                precision,
            } => Self::Sine {
                real: rename(real)?,
                argument,
                precision,
            },
            Self::Angle {
                real,
                x,
                y,
                precision,
            } => Self::Angle {
                real: rename(real)?,
                x,
                y,
                precision,
            },
            Self::Recurrence {
                real,
                argument,
                terms,
                precision,
            } => Self::Recurrence {
                real: rename(real)?,
                argument,
                terms,
                precision,
            },
            Self::Quotient {
                real,
                numerator,
                denominator,
                precision,
            } => Self::Quotient {
                real: rename(real)?,
                numerator,
                denominator,
                precision,
            },
            Self::Power {
                real,
                base,
                precision,
            } => Self::Power {
                real: rename(real)?,
                base,
                precision,
            },
        });
    }
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
    /// An end of an enclosure lies in the cut that the rule states the point
    /// lies outside.
    InsideCut,
    /// A split point does not lie strictly inside its enclosure.
    OutsideEnclosure,
    /// Two enclosures do not separate as the rule states.
    NotSeparated,
    /// A hypothesis has its lower end above its upper end.
    Reversed,
    /// Two premises hold under two different hypotheses.
    Hypothesis,
    /// The last step holds only under a hypothesis.
    Hypothetical,
    /// A hypothesis does not lie inside the quantifier's domain.
    OutsideDomain,
    /// The hypotheses of a cover do not tile the quantifier's domain in
    /// order.
    Gap,
    /// A negative answer names a quantifier with no evidence of the other
    /// modality.
    Modality,
    /// A recurrence step sums more terms than the term quota.
    TermQuota,
    /// No tail bound holds after the terms of a recurrence step: the bound on
    /// the term ratio past them does not lie below one.
    Tail,
    /// The enclosure of a divisor reaches zero.
    ZeroDivisor,
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
            Self::InsideCut => "an enclosure reaches into the cut that the point lies outside",
            Self::OutsideEnclosure => "a split point does not lie strictly inside its enclosure",
            Self::NotSeparated => "the enclosures do not separate as the rule states",
            Self::Reversed => "a hypothesis has its lower end above its upper end",
            Self::Hypothesis => "two premises hold under different hypotheses",
            Self::Hypothetical => "the last step holds only under a hypothesis",
            Self::OutsideDomain => "a hypothesis does not lie inside the quantifier's domain",
            Self::Gap => "the hypotheses of a cover do not tile the domain in order",
            Self::Modality => "a negative answer has no evidence of the other modality",
            Self::TermQuota => "a recurrence step sums more terms than the term quota",
            Self::Tail => "no tail bound holds after the terms of a recurrence step",
            Self::ZeroDivisor => "the enclosure of a divisor reaches zero",
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

/// What a step proves, and the hypothesis that it proves it under.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Derived
{
    /// What the step proves.
    conclusion: Conclusion,
    /// The closed interval that the variable at de Bruijn index zero ranges
    /// over, or `None` when the conclusion holds for every value of it.
    hypothesis: Option<NumericInterval>,
}

impl Derived
{
    /// A conclusion that holds under no hypothesis.
    ///
    /// # Specification
    /// trivial.
    const fn closed(conclusion: Conclusion) -> Self
    {
        return Self {
            conclusion,
            hypothesis: None,
        };
    }
}

/// The arithmetic of an enclosure step.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Operation
{
    /// The sum of two enclosures.
    Sum,
    /// The difference of two enclosures.
    Difference,
    /// The product of two enclosures.
    Product,
}

/// Replay `certificate` against `plan` within `quotas`.
///
/// # Specification
/// - ensures: returns the last step's conclusion when every step derives its
///   conclusion from its rule's evidence and its premises by the table of the
///   module, and the last step holds under no hypothesis. A positive conclusion
///   then holds of the plan's semantics.
/// - fails: refuses another format ([`CertificateCheck::Format`]), no step
///   ([`CertificateCheck::Empty`]) and more steps than the quota
///   ([`CertificateCheck::StepQuota`]) for the whole certificate. It refuses
///   the first failing step with the check that fails there, and a last step
///   under a hypothesis as [`CertificateCheck::Hypothetical`].
/// - panics: none.
/// - executable: none — the clause restates the replay.
/// - intension: one derivation per step, each at most one exact square or four
///   exact products of dyadics within the width quota, and one comparison for
///   each premise of a cover. The replay holds one conclusion per step.
///
/// # Errors
/// The first [`CertificateRefusal`], at the certificate or at its step.
///
/// # Adequacy
/// - hypothesis: L2 — every refinement of generated radicands replays, and so
///   does every certificate of generated quantified formulas. L3 — each check
///   on its smallest corruption of a sound certificate, a forged cut, and each
///   quota at its bound and past it.
/// - witness: `tests::certificate::the_square_root_of_two_refines_and_replays_at_each_width`
/// - witness: `tests::certificate::refinement_holds_for_generated_radicands`
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
/// - witness: `tests::certificate::a_forged_cut_is_refused`
/// - witness: `tests::certificate::quotas_bound_the_checker`
/// - witness: `tests::certificate::comparisons_with_the_cut_are_certified`
/// - witness: `tests::quantifier::a_cover_of_two_pieces_certifies_the_universal`
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
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
    let mut derived = replay(plan.plan(), &certificate.steps, quotas)?;
    let last = derived
        .pop()
        .ok_or_else(|| whole(CertificateCheck::Empty))?;
    if last.hypothesis.is_some() {
        return Err(CertificateRefusal {
            site: StepSite::Step(StepId::try_from(derived.len()).map_err(whole)?),
            check: CertificateCheck::Hypothetical,
        });
    }
    return Ok(Checked {
        conclusion: last.conclusion,
    });
}

/// Replay `steps` as the prefix of a certificate that a live obligation has
/// written so far: as [`check`], but its last step may hold under a
/// hypothesis.
///
/// # Specification
/// - ensures: succeeds when every step derives its conclusion by the table of
///   the module.
/// - fails: refuses more steps than the quota, and the first failing step, as
///   [`check`] does.
/// - panics: none.
/// - executable: none — the clause restates the replay.
///
/// # Errors
/// The first [`CertificateRefusal`], at the steps or at a step.
///
/// # Adequacy
/// - hypothesis: L2 — every checkpoint of a generated search resumes. L3 — a
///   prefix that ends under a hypothesis.
/// - witness: `tests::quantifier::a_search_resumes_from_its_checkpoint`
/// - witness: `tests::checkpoint::a_corrupt_checkpoint_is_refused_by_name`
pub(crate) fn replay_prefix(
    plan: &ValidatedPlan,
    steps: &[Step],
    quotas: &CheckerQuotas,
) -> Result<(), CertificateRefusal>
{
    return replay(plan.plan(), steps, quotas).map(|_derived| ());
}

/// Derive the conclusion of each of `steps` in order.
///
/// # Specification
/// - ensures: one conclusion with its hypothesis for each step, each derived
///   from the steps before it.
/// - fails: refuses more steps than the quota as
///   [`CertificateCheck::StepQuota`], and the first failing step with the check
///   that fails there.
/// - panics: none.
/// - executable: none — the clause restates the replay.
/// - intension: one derivation per step, and one allocation of the conclusions.
///
/// # Errors
/// The first [`CertificateRefusal`], at the steps or at a step.
///
/// # Adequacy
/// - hypothesis: L2 — as [`check`], which replays each certificate here.
/// - witness: `tests::certificate::corrupted_certificates_are_refused_by_name`
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
fn replay(
    plan: &Plan,
    steps: &[Step],
    quotas: &CheckerQuotas,
) -> Result<Vec<Derived>, CertificateRefusal>
{
    let whole = |check: CertificateCheck| CertificateRefusal {
        site: StepSite::Certificate,
        check,
    };
    if steps.len() > quotas.steps.0 {
        return Err(whole(CertificateCheck::StepQuota));
    }
    let mut derived: Vec<Derived> = Vec::with_capacity(steps.len());
    for (index, step) in steps.iter().enumerate() {
        let id = StepId::try_from(index).map_err(whole)?;
        let next = derive(plan, step, &derived, quotas).map_err(|check| CertificateRefusal {
            site: StepSite::Step(id),
            check,
        })?;
        derived.push(next);
    }
    return Ok(derived);
}

/// The conclusion of one step and its hypothesis, derived from its evidence
/// and the steps before it.
///
/// # Specification
/// - ensures: returns the conclusion of the module's table for the step's rule,
///   under the hypothesis of its premises, or under the hypothesis that a
///   `Variable` step states.
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
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
fn derive(
    plan: &Plan,
    step: &Step,
    earlier: &[Derived],
    quotas: &CheckerQuotas,
) -> Result<Derived, CertificateCheck>
{
    let bounded = |value: &Dyadic| {
        if value.width() > quotas.width {
            return Err(CertificateCheck::WidthQuota);
        }
        return Ok(());
    };
    // A builtin's rule works at its precision plus guard bits, which the
    // width quota bounds as it bounds a dyadic.
    let within = |precision: Precision| {
        if width(precision) > quotas.width {
            return Err(CertificateCheck::WidthQuota);
        }
        return Ok(());
    };
    let premise = |id: StepId| {
        earlier
            .get(usize::from(id))
            .ok_or(CertificateCheck::ForwardPremise)
    };
    let node = |id: NodeId| {
        plan.node(id)
            .map_err(|_unknown| CertificateCheck::UnknownNode)
    };
    let enclosure = |id: StepId, operand: NodeId| match *premise(id)? {
        Derived {
            conclusion: Conclusion::Encloses { real, ref interval },
            ref hypothesis,
        } if real == operand => Ok((interval, hypothesis.as_ref())),
        Derived { .. } => Err(CertificateCheck::PremiseConclusion),
    };
    let body = |id: StepId, open: NodeId, pole: Pole| {
        let instance = premise(id)?;
        return match (&instance.conclusion, pole) {
            (&Conclusion::Holds { open: concluded }, Pole::Holds)
            | (&Conclusion::Fails { open: concluded }, Pole::Fails)
                if concluded == open =>
            {
                Ok(instance.hypothesis.as_ref())
            },
            (
                &(Conclusion::Encloses { .. }
                | Conclusion::Holds { .. }
                | Conclusion::Fails { .. }),
                Pole::Holds | Pole::Fails,
            ) => Err(CertificateCheck::PremiseConclusion),
        };
    };
    let arithmetic = |operation: Operation, real: NodeId, (left, right): (StepId, StepId)| {
        let (first, second) = match (node(real)?, operation) {
            (&Node::Real(Real::Add(first, second)), Operation::Sum)
            | (&Node::Real(Real::Sub(first, second)), Operation::Difference)
            | (&Node::Real(Real::Mul(first, second)), Operation::Product) => (first, second),
            (&Node::Real(_) | &Node::Open(_) | &Node::Domain(_), _) => {
                return Err(CertificateCheck::WrongNode);
            },
        };
        let (first, first_hypothesis) = enclosure(left, first.node())?;
        let (second, second_hypothesis) = enclosure(right, second.node())?;
        let hypothesis = joint(first_hypothesis, second_hypothesis)?;
        let interval = combined(operation, first, second, quotas)?;
        return Ok(Derived {
            conclusion: Conclusion::Encloses { real, interval },
            hypothesis,
        });
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
            Ok(Derived::closed(Conclusion::Encloses {
                real: cut,
                interval,
            }))
        },
        Step::Split {
            premise: id,
            ref point,
            side,
        } => {
            let Derived {
                conclusion: Conclusion::Encloses { real, ref interval },
                ref hypothesis,
            } = *premise(id)?
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
            Ok(Derived {
                conclusion: Conclusion::Encloses { real, interval },
                hypothesis: hypothesis.clone(),
            })
        },
        Step::Constant { real } => {
            let Node::Real(Real::Constant(ref value)) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            bounded(value)?;
            Ok(Derived::closed(Conclusion::Encloses {
                real,
                interval: NumericInterval::point(value.clone()),
            }))
        },
        Step::Below { less, left, right } | Step::NotBelow { less, left, right } => {
            let Node::Open(Open::Less(first, second)) = *node(less)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            let (first, first_hypothesis) = enclosure(left, first.node())?;
            let (second, second_hypothesis) = enclosure(right, second.node())?;
            let hypothesis = joint(first_hypothesis, second_hypothesis)?;
            let conclusion = if matches!(*step, Step::Below { .. }) {
                separated_below(first, second)?;
                Conclusion::Holds { open: less }
            }
            else {
                if first.lower().endpoint < second.upper().endpoint {
                    return Err(CertificateCheck::NotSeparated);
                }
                Conclusion::Fails { open: less }
            };
            Ok(Derived {
                conclusion,
                hypothesis,
            })
        },
        Step::Inside { open, point, side } | Step::Outside { open, point, side } => {
            let (cut, operand) = match (node(open)?, side) {
                (
                    &Node::Open(Open::LowerCut(cut, operand) | Open::Less(operand, cut)),
                    Side::Lower,
                )
                | (
                    &Node::Open(Open::UpperCut(cut, operand) | Open::Less(cut, operand)),
                    Side::Upper,
                ) => (cut, operand),
                (&(Node::Real(_) | Node::Open(_) | Node::Domain(_)), Side::Lower | Side::Upper) => {
                    return Err(CertificateCheck::WrongNode);
                },
            };
            let radicand = radicand(plan, cut.node())?;
            let (interval, hypothesis) = enclosure(point, operand.node())?;
            let inside = matches!(*step, Step::Inside { .. });
            // The lower cut holds of every point below a point of it, and the
            // upper cut of every point above a point of it. So each rule reads
            // the end of the enclosure toward the cut's value.
            let (end, wanted) = match (side, inside) {
                (Side::Lower, true) => (interval.upper(), Membership::Lower),
                (Side::Lower, false) => (interval.lower(), Membership::Lower),
                (Side::Upper, true) => (interval.lower(), Membership::Upper),
                (Side::Upper, false) => (interval.upper(), Membership::Upper),
            };
            let found = match end.endpoint {
                Endpoint::Finite(ref value) => {
                    bounded(value)?;
                    membership(value, &radicand)?
                },
                Endpoint::NegInf => Membership::Lower,
                Endpoint::PosInf => Membership::Upper,
            };
            let conclusion = match (inside, found == wanted, side) {
                (true, true, _) => Conclusion::Holds { open },
                (false, false, _) => Conclusion::Fails { open },
                (true, false, Side::Lower) => return Err(CertificateCheck::NotLower),
                (true, false, Side::Upper) => return Err(CertificateCheck::NotUpper),
                (false, true, _) => return Err(CertificateCheck::InsideCut),
            };
            Ok(Derived {
                conclusion,
                hypothesis: hypothesis.cloned(),
            })
        },
        Step::Variable {
            real,
            ref lower,
            ref upper,
        } => {
            let Node::Real(Real::Bound(index)) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            if index != DeBruijn::default() {
                return Err(CertificateCheck::WrongNode);
            }
            bounded(lower)?;
            bounded(upper)?;
            let interval = NumericInterval::new(
                Bound::closed(lower.clone()),
                Bound::closed(upper.clone()),
                Orientation::Proper,
            )
            .map_err(|_reversed| CertificateCheck::Reversed)?;
            Ok(Derived {
                conclusion: Conclusion::Encloses {
                    real,
                    interval: interval.clone(),
                },
                hypothesis: Some(interval),
            })
        },
        Step::Sum { real, left, right } => arithmetic(Operation::Sum, real, (left, right)),
        Step::Difference { real, left, right } => {
            arithmetic(Operation::Difference, real, (left, right))
        },
        Step::Product { real, left, right } => arithmetic(Operation::Product, real, (left, right)),
        Step::Witness {
            exists,
            premise: id,
        } => {
            let (&Open::Exists(quantifier), hull) = quantified(plan, exists)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            inside(body(id, quantifier.body.node(), Pole::Holds)?, hull)?;
            Ok(Derived::closed(Conclusion::Holds { open: exists }))
        },
        Step::Counterexample {
            forall,
            premise: id,
        } => {
            let (&Open::Forall(quantifier), hull) = quantified(plan, forall)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            dual(quantifier)?;
            inside(body(id, quantifier.body.node(), Pole::Fails)?, hull)?;
            Ok(Derived::closed(Conclusion::Fails { open: forall }))
        },
        Step::Cover {
            forall,
            ref premises,
        } => {
            let (&Open::Forall(quantifier), hull) = quantified(plan, forall)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            tiled(
                hull,
                premises
                    .iter()
                    .map(|&id| body(id, quantifier.body.node(), Pole::Holds)),
            )?;
            Ok(Derived::closed(Conclusion::Holds { open: forall }))
        },
        Step::Refutation {
            exists,
            ref premises,
        } => {
            let (&Open::Exists(quantifier), hull) = quantified(plan, exists)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            dual(quantifier)?;
            tiled(
                hull,
                premises
                    .iter()
                    .map(|&id| body(id, quantifier.body.node(), Pole::Fails)),
            )?;
            Ok(Derived::closed(Conclusion::Fails { open: exists }))
        },
        Step::Pi { real, precision } => {
            let Node::Real(Real::Pi) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            within(precision)?;
            Ok(Derived::closed(Conclusion::Encloses {
                real,
                interval: pi(precision)?,
            }))
        },
        Step::Cosine {
            real,
            argument,
            precision,
        }
        | Step::Sine {
            real,
            argument,
            precision,
        } => {
            let wave = matches!(*step, Step::Cosine { .. });
            let operand = match (node(real)?, wave) {
                (&Node::Real(Real::Cos(operand)), true)
                | (&Node::Real(Real::Sin(operand)), false) => operand,
                (&(Node::Real(_) | Node::Open(_) | Node::Domain(_)), true | false) => {
                    return Err(CertificateCheck::WrongNode);
                },
            };
            within(precision)?;
            let (interval, hypothesis) = enclosure(argument, operand.node())?;
            let interval = if wave {
                cosine(interval, precision)?
            }
            else {
                sine(interval, precision)?
            };
            Ok(Derived {
                conclusion: Conclusion::Encloses { real, interval },
                hypothesis: hypothesis.cloned(),
            })
        },
        Step::Angle {
            real,
            x,
            y,
            precision,
        } => {
            let Node::Real(Real::Arg(first, second)) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            within(precision)?;
            let (first, first_hypothesis) = enclosure(x, first.node())?;
            let (second, second_hypothesis) = enclosure(y, second.node())?;
            let hypothesis = joint(first_hypothesis, second_hypothesis)?;
            Ok(Derived {
                conclusion: Conclusion::Encloses {
                    real,
                    interval: angle(first, second, precision)?,
                },
                hypothesis,
            })
        },
        Step::Recurrence {
            real,
            argument,
            terms,
            precision,
        } => {
            let Node::Real(Real::Recurrence(ref recurrence)) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            within(precision)?;
            let (interval, hypothesis) = enclosure(argument, recurrence.argument.node())?;
            let ratio = (&recurrence.numerator, &recurrence.denominator);
            Ok(Derived {
                conclusion: Conclusion::Encloses {
                    real,
                    interval: series_after(interval, ratio, terms, precision)?,
                },
                hypothesis: hypothesis.cloned(),
            })
        },
        Step::Quotient {
            real,
            numerator,
            denominator,
            precision,
        } => {
            let Node::Real(Real::Div {
                numerator: dividend,
                denominator: divisor,
                ..
            }) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            within(precision)?;
            let (first, first_hypothesis) = enclosure(numerator, dividend.node())?;
            let (second, second_hypothesis) = enclosure(denominator, divisor.node())?;
            let hypothesis = joint(first_hypothesis, second_hypothesis)?;
            Ok(Derived {
                conclusion: Conclusion::Encloses {
                    real,
                    interval: quotient(first, second, precision)?,
                },
                hypothesis,
            })
        },
        Step::Power {
            real,
            base,
            precision,
        } => {
            let Node::Real(Real::Power(operand, power)) = *node(real)?
            else {
                return Err(CertificateCheck::WrongNode);
            };
            within(precision)?;
            let (interval, hypothesis) = enclosure(base, operand.node())?;
            Ok(Derived {
                conclusion: Conclusion::Encloses {
                    real,
                    interval: raised(interval, power, precision)?,
                },
                hypothesis: hypothesis.cloned(),
            })
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
pub(crate) fn separated_below(
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

/// Whether a quantifier rule asks its body to hold or to fail.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Pole
{
    /// The body holds.
    Holds,
    /// The body fails.
    Fails,
}

/// The hypothesis of a step whose two premises hold under `first` and
/// `second`.
///
/// # Specification
/// - ensures: no hypothesis when neither premise has one. Otherwise the one
///   hypothesis that one premise or both premises hold under.
/// - fails: refuses two different hypotheses as
///   [`CertificateCheck::Hypothesis`].
/// - panics: none.
///
/// # Errors
/// - [`CertificateCheck::Hypothesis`]: the premises hold under different
///   hypotheses.
///
/// # Adequacy
/// - hypothesis: L3 — premises under no hypothesis, under one, under the same
///   one, and under two different ones.
/// - witness: `tests::quantifier::a_cover_of_two_pieces_certifies_the_universal`
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |joint| joint.is_none() == (first.is_none() && second.is_none())))]
fn joint(
    first: Option<&NumericInterval>,
    second: Option<&NumericInterval>,
) -> Result<Option<NumericInterval>, CertificateCheck>
{
    return match (first, second) {
        (None, None) => Ok(None),
        (Some(one), None) | (None, Some(one)) => Ok(Some(one.clone())),
        (Some(one), Some(other)) if one == other => Ok(Some(one.clone())),
        (Some(_), Some(_)) => Err(CertificateCheck::Hypothesis),
    };
}

/// One finite end of an interval and its closure.
type End<'interval> = (&'interval Dyadic, Closure);

/// The finite ends of `interval`, each with its closure.
///
/// # Specification
/// - ensures: the lower end and the upper end, each a dyadic.
/// - fails: refuses an infinite end as [`CertificateCheck::PremiseConclusion`].
/// - panics: none.
///
/// # Errors
/// - [`CertificateCheck::PremiseConclusion`]: an end is infinite.
///
/// # Adequacy
/// - hypothesis: L2 — the ends of every enclosure of generated quantified
///   formulas.
/// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
#[spec(ensures: |ref result| result.is_ok() == (matches!(interval.lower().endpoint, Endpoint::Finite(_)) && matches!(interval.upper().endpoint, Endpoint::Finite(_))))]
fn ends(interval: &NumericInterval) -> Result<(End<'_>, End<'_>), CertificateCheck>
{
    let (&Endpoint::Finite(ref low), &Endpoint::Finite(ref high)) =
        (&interval.lower().endpoint, &interval.upper().endpoint)
    else {
        return Err(CertificateCheck::PremiseConclusion);
    };
    return Ok((
        (low, interval.lower().closure),
        (high, interval.upper().closure),
    ));
}

/// The enclosure of `operation` on `first` and `second`, computed exactly.
///
/// # Specification
/// - ensures: a sum or a difference takes the exact sums or differences of the
///   ends. Each of its ends is open when an end that it comes from is open. A
///   product takes the least and the greatest of the four exact products of the
///   ends, both ends closed.
/// - fails: refuses an infinite end as [`CertificateCheck::PremiseConclusion`],
///   and an end wider than the quota as [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the arithmetic.
/// - intension: at most four exact products of dyadics within the width quota,
///   and no allocation past the ends.
///
/// # Errors
/// - [`CertificateCheck::PremiseConclusion`]: an end is infinite.
/// - [`CertificateCheck::WidthQuota`]: an end is wider than the quota.
///
/// # Adequacy
/// - hypothesis: L2 — every enclosure of generated quantified formulas replays.
///   L3 — each operation, and a product past the width quota.
/// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
pub(crate) fn combined(
    operation: Operation,
    first: &NumericInterval,
    second: &NumericInterval,
    quotas: &CheckerQuotas,
) -> Result<NumericInterval, CertificateCheck>
{
    let ((first_low, first_low_closure), (first_high, first_high_closure)) = ends(first)?;
    let ((second_low, second_low_closure), (second_high, second_high_closure)) = ends(second)?;
    let exactly = |value| {
        let value: Dyadic = exact(value)?;
        if value.width() > quotas.width {
            return Err(CertificateCheck::WidthQuota);
        }
        return Ok(value);
    };
    let attained = |one: Closure, other: Closure| {
        if one == Closure::Closed && other == Closure::Closed {
            Closure::Closed
        }
        else {
            Closure::Open
        }
    };
    let (lower, upper) = match operation {
        Operation::Sum => (
            Bound::new(
                Endpoint::Finite(exactly(first_low.add(
                    second_low,
                    Precision::MAX,
                    Rounding::Floor,
                ))?),
                attained(first_low_closure, second_low_closure),
            ),
            Bound::new(
                Endpoint::Finite(exactly(first_high.add(
                    second_high,
                    Precision::MAX,
                    Rounding::Floor,
                ))?),
                attained(first_high_closure, second_high_closure),
            ),
        ),
        Operation::Difference => (
            Bound::new(
                Endpoint::Finite(exactly(first_low.sub(
                    second_high,
                    Precision::MAX,
                    Rounding::Floor,
                ))?),
                attained(first_low_closure, second_high_closure),
            ),
            Bound::new(
                Endpoint::Finite(exactly(first_high.sub(
                    second_low,
                    Precision::MAX,
                    Rounding::Floor,
                ))?),
                attained(first_high_closure, second_low_closure),
            ),
        ),
        Operation::Product => {
            let mut products = [
                exactly(first_low.mul(second_low, Precision::MAX, Rounding::Floor))?,
                exactly(first_low.mul(second_high, Precision::MAX, Rounding::Floor))?,
                exactly(first_high.mul(second_low, Precision::MAX, Rounding::Floor))?,
                exactly(first_high.mul(second_high, Precision::MAX, Rounding::Floor))?,
            ];
            products.sort_unstable();
            let [least, _, _, greatest] = products;
            (Bound::closed(least), Bound::closed(greatest))
        },
    };
    return NumericInterval::new(lower, upper, Orientation::Proper)
        .map_err(|_reversed| CertificateCheck::PremiseConclusion);
}

/// The quotient of `first` by `second`, rounded outward at `precision`
/// significant bits.
///
/// # Specification
/// - ensures: the least and the greatest of the four quotients of the ends,
///   rounded down and up at `precision` significant bits, both ends closed.
/// - fails: refuses a divisor whose closed hull holds zero as
///   [`CertificateCheck::ZeroDivisor`], an infinite end as
///   [`CertificateCheck::PremiseConclusion`], and an exponent past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the arithmetic.
/// - intension: eight rounded quotients of dyadics.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2 — the quotient of the plan of `log` against the digits of
///   `log 2`. L3 — a divisor that reaches zero.
/// - witness: `tests::recurrence::log_of_two_encloses_its_digits_and_its_certificate_replays`
/// - witness: `tests::recurrence::a_divisor_that_reaches_zero_is_refused_by_name`
pub(crate) fn quotient(
    first: &NumericInterval,
    second: &NumericInterval,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    let ((first_low, _), (first_high, _)) = ends(first)?;
    let ((second_low, _), (second_high, _)) = ends(second)?;
    if second_low.sign() != Sign::Positive && second_high.sign() != Sign::Negative {
        return Err(CertificateCheck::ZeroDivisor);
    }
    let corners = [
        (first_low, second_low),
        (first_low, second_high),
        (first_high, second_low),
        (first_high, second_high),
    ];
    return extremes(corners, |(dividend, divisor), rounding| {
        return exact(dividend.div(divisor, precision, rounding));
    });
}

/// The power of `base` by repeated squaring, each product rounded outward at
/// `precision` significant bits.
///
/// # Specification
/// - ensures: the zeroth power is the closed point one. Each squaring, and each
///   product with the base for a set bit, takes the least and the greatest of
///   the four products of the ends, rounded down and up at `precision`
///   significant bits, both ends closed.
/// - fails: refuses an infinite end as [`CertificateCheck::PremiseConclusion`],
///   and an exponent past its range as [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the arithmetic.
/// - intension: eight rounded products for each squaring and each set bit.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2 — the power of the plan of `exp` against `e` and against
///   `exp (log 3) = 3`.
/// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
pub(crate) fn raised(
    base: &NumericInterval,
    power: Power,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    let ((low, _), (high, _)) = ends(base)?;
    let product = |first: (&Dyadic, &Dyadic), second: (&Dyadic, &Dyadic)| {
        let corners = [
            (first.0, second.0),
            (first.0, second.1),
            (first.1, second.0),
            (first.1, second.1),
        ];
        return extremes(corners, |(left, right), rounding| {
            return exact(left.mul(right, precision, rounding));
        });
    };
    let power = u32::from(power);
    let mut result = NumericInterval::point(Dyadic::ONE);
    for bit in (0 .. u32::BITS.saturating_sub(power.leading_zeros())).rev() {
        let ((lower, _), (upper, _)) = ends(&result)?;
        result = product((lower, upper), (lower, upper))?;
        if power
            .checked_shr(bit)
            .is_some_and(|shifted| shifted & 1 == 1)
        {
            let ((lower, _), (upper, _)) = ends(&result)?;
            result = product((lower, upper), (low, high))?;
        }
    }
    return Ok(result);
}

/// The closed interval from the least corner rounded down to the greatest
/// corner rounded up.
///
/// # Specification
/// trivial.
fn extremes<'value, Operation>(
    corners: [(&'value Dyadic, &'value Dyadic); 4],
    operation: Operation,
) -> Result<NumericInterval, CertificateCheck>
where
    Operation: Fn((&'value Dyadic, &'value Dyadic), Rounding) -> Result<Dyadic, CertificateCheck>,
{
    let mut lower: Option<Dyadic> = None;
    let mut upper: Option<Dyadic> = None;
    for corner in corners {
        let down = operation(corner, Rounding::Floor)?;
        let up = operation(corner, Rounding::Ceiling)?;
        lower =
            Some(lower.map_or_else(|| down.clone(), |known| core::cmp::min(known, down.clone())));
        upper = Some(upper.map_or_else(|| up.clone(), |known| core::cmp::max(known, up.clone())));
    }
    let (Some(lower), Some(upper)) = (lower, upper)
    else {
        return Err(CertificateCheck::PremiseConclusion);
    };
    return NumericInterval::new(
        Bound::closed(lower),
        Bound::closed(upper),
        Orientation::Proper,
    )
    .map_err(|_reversed| CertificateCheck::PremiseConclusion);
}

/// The quantifier at `node` and the hull of its interval domain.
///
/// # Specification
/// - ensures: the node is an existential or a universal over an interval.
/// - fails: refuses a node that the plan does not hold as
///   [`CertificateCheck::UnknownNode`], and another node or another domain as
///   [`CertificateCheck::WrongNode`].
/// - panics: none.
///
/// # Errors
/// - [`CertificateCheck::UnknownNode`]: no node is at `node`.
/// - [`CertificateCheck::WrongNode`]: the node is no quantifier over an
///   interval.
///
/// # Adequacy
/// - hypothesis: L3 — each quantifier rule on its quantifier and on another
///   node.
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |&(open, _)| matches!(*open, Open::Exists(_) | Open::Forall(_))))]
fn quantified(
    plan: &Plan,
    node: NodeId,
) -> Result<(&Open, &NumericInterval), CertificateCheck>
{
    let fetch = |id: NodeId| {
        plan.node(id)
            .map_err(|_unknown| CertificateCheck::UnknownNode)
    };
    let Node::Open(ref open) = *fetch(node)?
    else {
        return Err(CertificateCheck::WrongNode);
    };
    let (Open::Exists(quantifier) | Open::Forall(quantifier)) = *open
    else {
        return Err(CertificateCheck::WrongNode);
    };
    let Node::Domain(Domain::Interval { ref hull, .. }) = *fetch(quantifier.domain.node())?
    else {
        return Err(CertificateCheck::WrongNode);
    };
    return Ok((open, hull));
}

/// Check that `hypothesis` lies inside `hull`.
///
/// # Specification
/// - ensures: succeeds for no hypothesis, since a proper hull is not empty.
///   Succeeds for a closed hypothesis whose ends lie inside the hull, an end of
///   the hull itself only when the hull holds it.
/// - fails: returns [`CertificateCheck::OutsideDomain`] otherwise.
/// - panics: none.
/// - executable: none — the clause compares ends of each closure.
///
/// # Errors
/// - [`CertificateCheck::OutsideDomain`]: the hypothesis reaches past the hull.
///
/// # Adequacy
/// - hypothesis: L3 — a hypothesis inside the hull, at its closed end, at its
///   open end, and past it.
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
/// - witness: `tests::quantifier::a_witness_at_an_open_end_is_refused`
fn inside(
    hypothesis: Option<&NumericInterval>,
    hull: &NumericInterval,
) -> Result<(), CertificateCheck>
{
    let Some(interval) = hypothesis
    else {
        return Ok(());
    };
    let from = match hull.lower().endpoint.cmp(&interval.lower().endpoint) {
        Ordering::Less => true,
        Ordering::Equal => hull.lower().closure == Closure::Closed,
        Ordering::Greater => false,
    };
    let to = match interval.upper().endpoint.cmp(&hull.upper().endpoint) {
        Ordering::Less => true,
        Ordering::Equal => hull.upper().closure == Closure::Closed,
        Ordering::Greater => false,
    };
    if from && to {
        return Ok(());
    }
    return Err(CertificateCheck::OutsideDomain);
}

/// Check that the hypotheses of `pieces` tile `hull` in order: the first
/// starts at the hull's lower end, each next one starts where the one before
/// it ends, and the last ends at the hull's upper end.
///
/// # Specification
/// - ensures: succeeds when the pieces tile the hull's closure. A piece under
///   no hypothesis covers the whole hull.
/// - fails: passes a piece's own refusal on, and returns
///   [`CertificateCheck::Gap`] for an unbounded hull, no piece, a gap, an
///   overlap, or a last piece short of the hull's upper end.
/// - panics: none.
/// - executable: none — the clause speaks of the order of the pieces.
/// - intension: one comparison for each piece, and no allocation.
///
/// # Errors
/// - [`CertificateCheck::Gap`]: the pieces do not tile the hull.
///
/// # Adequacy
/// - hypothesis: L2 — every cover of generated quantified formulas tiles its
///   domain. L3 — no piece, a gap, an overlap, and a short cover.
/// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
/// - witness: `tests::quantifier::each_corruption_of_a_quantifier_certificate_is_refused_by_name`
fn tiled<'premise, Pieces>(
    hull: &NumericInterval,
    pieces: Pieces,
) -> Result<(), CertificateCheck>
where
    Pieces: Iterator<Item = Result<Option<&'premise NumericInterval>, CertificateCheck>>,
{
    let (&Endpoint::Finite(ref low), &Endpoint::Finite(ref high)) =
        (&hull.lower().endpoint, &hull.upper().endpoint)
    else {
        return Err(CertificateCheck::Gap);
    };
    let mut reached: Option<&Dyadic> = None;
    for piece in pieces {
        let Some(interval) = piece?
        else {
            reached = Some(high);
            continue;
        };
        let ((lower, _), (upper, _)) =
            ends(interval).map_err(|_unbounded| CertificateCheck::Gap)?;
        if lower != reached.unwrap_or(low) {
            return Err(CertificateCheck::Gap);
        }
        reached = Some(upper);
    }
    if reached == Some(high) {
        return Ok(());
    }
    return Err(CertificateCheck::Gap);
}

/// Check that `quantifier` has evidence of the other modality, which a
/// negative answer needs.
///
/// # Specification
/// trivial.
const fn dual(quantifier: Quantifier) -> Result<(), CertificateCheck>
{
    return match quantifier.dual {
        EvidenceSlot::Given(_) => Ok(()),
        EvidenceSlot::Absent => Err(CertificateCheck::Modality),
    };
}
