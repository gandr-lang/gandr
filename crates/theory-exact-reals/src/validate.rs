//! Total validation of a plan: the one gate through which a plan reaches
//! approximation, the machine and the checker.
//!
//! A plan is untrusted input. [`validate`] reads its bytes and [`admit`]
//! takes a plan already in memory. Each pass either yields a
//! [`ValidatedPlan`] or refuses with a [`Refusal`]. A refusal names the
//! [`Site`] where the plan fails and the [`Check`] that fails there. The
//! pass never panics, and a refused plan never constructs a
//! [`ValidatedPlan`].
//!
//! # Boundaries
//!
//! | Check | What it refuses |
//! | ----- | --------------- |
//! | [`Check::ByteQuota`], [`Check::NodeQuota`] | an input longer than the byte quota, or with more nodes than the node quota, before a node is read |
//! | [`Check::Decode`] | bytes that are not the canonical bytes of a plan: a dangling or forward child, which also excludes a cycle, a child of the wrong sort, a malformed interval or constant |
//! | [`Check::HeightQuota`], [`Check::BinderQuota`] | a path from the root longer than the height quota, or under more binders than the binder quota |
//! | [`Check::WidthQuota`], [`Check::PowerQuota`] | a dyadic wider than the width quota, or a power above the power quota |
//! | [`Check::EscapedBinder`] | a bound variable whose index reaches past its binders on some path from the root |
//! | [`Check::CutHull`] | a cut whose hull is dual or unbounded |
//! | [`Check::DomainHull`] | an interval domain that is dual or unbounded, or compact evidence on a hull that is not closed |
//! | [`Check::UnknownEvidence`], [`Check::EvidenceKind`] | an evidence reference that the [`EvidenceTable`] does not register, or registers for another judgement |
//! | [`Check::DomainEvidence`] | a quantifier whose evidence differs from the evidence its interval domain states |
//! | [`Check::CutOperand`] | a lower or an upper cut whose first operand is not a cut |
//!
//! # Items
//!
//! The plan is canonical, so each node stands after its children. A
//! forward walk computes each node's height and binder nesting from its
//! children and checks its payload. A backward walk from the root then
//! carries the fewest binders over any path to each node, and a bound
//! variable must stay below that count. The pass holds one mark of three
//! counts per node and is linear in the nodes and edges, with one search of
//! the evidence table for each evidence reference. A quota excess is a
//! refusal, and the pass never cuts a plan short.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::codec::DecodeError;
use crate::codec::EncodedPlan;
use crate::codec::read;
use crate::dyadic::BitWidth;
use crate::dyadic::Dyadic;
use crate::interval::Bound;
use crate::interval::Closure;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Domain;
use crate::plan::Evidence;
use crate::plan::EvidenceSlot;
use crate::plan::Node;
use crate::plan::NodeCount;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::Power;
use crate::plan::Quantifier;
use crate::plan::Real;
use crate::plan::Scope;
use crate::plan::Site;

/// A count of nested nodes or of nested binders.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Height(u32);

impl From<u32> for Height
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        return Self(count);
    }
}

impl From<Height> for u32
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(height: Height) -> Self
    {
        return height.0;
    }
}

/// A length of input, in bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteLength(usize);

impl From<usize> for ByteLength
{
    /// The length `length`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: usize) -> Self
    {
        return Self(length);
    }
}

impl From<ByteLength> for usize
{
    /// The length as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: ByteLength) -> Self
    {
        return length.0;
    }
}

/// The limits that a plan must keep. A plan past a limit is refused, never
/// cut short.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Quotas
{
    /// The longest input.
    pub bytes: ByteLength,
    /// The most distinct nodes.
    pub nodes: NodeCount,
    /// The longest path from the root, counted in nodes.
    pub height: Height,
    /// The most binders around a node.
    pub binders: Height,
    /// The widest mantissa of a constant or an endpoint.
    pub width: BitWidth,
    /// The greatest natural power.
    pub power: Power,
}

impl Default for Quotas
{
    /// The quotas of stage A: 16 MiB of input, 2^20 nodes, a height of
    /// 2^16, 256 binders, mantissas of 2^24 bits and powers up to 1024.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        return Self {
            bytes: ByteLength(0x0100_0000),
            nodes: NodeCount::from(0x0010_0000_usize),
            height: Height(0x0001_0000),
            binders: Height(256),
            width: BitWidth::from(0x0100_0000_u64),
            power: Power::from(1024),
        };
    }
}

/// The judgement that an evidence reference names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Judgement
{
    /// The laws of a registered cut.
    CutLaws,
    /// A divisor is not zero.
    NonZero,
    /// A domain is overt: an existential over it can be confirmed.
    Overt,
    /// A domain is compact: a universal over it can be confirmed.
    Compact,
    /// The modality of a product of domains.
    Product,
    /// The modality of a subdomain.
    Subdomain,
}

impl fmt::Display for Judgement
{
    /// Write the judgement as a noun phrase.
    ///
    /// # Specification
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::validate::refusals_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return f.write_str(match *self {
            Self::CutLaws => "the laws of a cut",
            Self::NonZero => "a divisor apart from zero",
            Self::Overt => "an overt domain",
            Self::Compact => "a compact domain",
            Self::Product => "the modality of a product",
            Self::Subdomain => "the modality of a subdomain",
        });
    }
}

/// A second, different judgement for an evidence reference that the table
/// already registers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Conflict
{
    /// The judgement that the table holds.
    pub held: Judgement,
}

/// The evidence that a plan may reference: each reference with the
/// judgement it names. A later unit fills it from checked certificates, and
/// the registered cuts of stage A stand in it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EvidenceTable
{
    /// The registered references.
    entries: BTreeMap<Evidence, Judgement>,
}

impl EvidenceTable
{
    /// An empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        return Self {
            entries: BTreeMap::new(),
        };
    }

    /// Register `evidence` as naming `judgement`.
    ///
    /// # Specification
    /// - ensures: the table maps `evidence` to `judgement`; registering the
    ///   same pair again changes nothing.
    /// - fails: returns [`Conflict`], the table unchanged, when it maps
    ///   `evidence` to another judgement.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Conflict`]: the reference already names another judgement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh reference, the same pair twice, and a second
    ///   judgement for one reference.
    /// - witness: `tests::validate::the_table_refuses_a_second_judgement`
    #[inline]
    #[spec(ensures: |ref result| result.is_err() || self.entries.get(&evidence) == Some(&judgement))]
    pub fn register(
        &mut self,
        evidence: Evidence,
        judgement: Judgement,
    ) -> Result<(), Conflict>
    {
        if let Some(&held) = self.entries.get(&evidence) {
            return if held == judgement {
                Ok(())
            }
            else {
                Err(Conflict { held })
            };
        }
        let _absent = self.entries.insert(evidence, judgement);
        return Ok(());
    }

    /// The judgement that `evidence` names.
    ///
    /// # Specification
    /// - ensures: returns the judgement that the table maps `evidence` to.
    /// - fails: returns [`Check::UnknownEvidence`] when the table does not
    ///   register `evidence`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Check::UnknownEvidence`]: the table does not register the reference.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a registered and an unregistered reference.
    /// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == self.entries.contains_key(&evidence))]
    pub fn judgement(
        &self,
        evidence: Evidence,
    ) -> Result<Judgement, Check>
    {
        return self
            .entries
            .get(&evidence)
            .copied()
            .ok_or(Check::UnknownEvidence);
    }
}

/// A check that a plan fails.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Check
{
    /// The bytes are not the canonical bytes of a plan.
    Decode(DecodeError),
    /// The input is longer than the byte quota.
    ByteQuota,
    /// The plan holds more nodes than the node quota.
    NodeQuota,
    /// A path from the root is longer than the height quota.
    HeightQuota,
    /// A node stands under more binders than the binder quota.
    BinderQuota,
    /// A constant or an endpoint is wider than the width quota.
    WidthQuota,
    /// A power is above the power quota.
    PowerQuota,
    /// A bound variable reaches past its binders.
    EscapedBinder,
    /// A cut's hull is dual or unbounded.
    CutHull,
    /// An interval domain is dual or unbounded, or its compact evidence
    /// stands on a hull that is not closed.
    DomainHull,
    /// An evidence reference that the table does not register.
    UnknownEvidence,
    /// An evidence reference that names another judgement than its slot
    /// takes.
    EvidenceKind
    {
        /// The judgement that the slot takes.
        expected: Judgement,
        /// The judgement that the reference names.
        found: Judgement,
    },
    /// A quantifier's evidence differs from its interval domain's.
    DomainEvidence,
    /// The first operand of a lower cut or an upper cut is not a cut.
    CutOperand,
}

impl fmt::Display for Check
{
    /// Write the check as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed phrase per variant, no two alike, with the
    ///   wrapped decoding failure's own line after its phrase.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::validate::refusals_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match *self {
            Self::Decode(error) => write!(f, "the bytes are not a plan: {error}"),
            Self::ByteQuota => f.write_str("the input is longer than the byte quota"),
            Self::NodeQuota => f.write_str("the plan holds more nodes than the node quota"),
            Self::HeightQuota => {
                f.write_str("a path from the root is longer than the height quota")
            },
            Self::BinderQuota => {
                f.write_str("a node stands under more binders than the binder quota")
            },
            Self::WidthQuota => f.write_str("a dyadic is wider than the width quota"),
            Self::PowerQuota => f.write_str("a power is above the power quota"),
            Self::EscapedBinder => f.write_str("a bound variable reaches past its binders"),
            Self::CutHull => f.write_str("a cut's hull is dual or unbounded"),
            Self::DomainHull => f.write_str(
                "an interval domain is dual or unbounded, or compact on a hull that is not closed",
            ),
            Self::UnknownEvidence => {
                f.write_str("the evidence table does not register a reference")
            },
            Self::EvidenceKind { expected, found } => {
                write!(
                    f,
                    "a reference names {found} where its slot takes {expected}"
                )
            },
            Self::DomainEvidence => f.write_str(
                "a quantifier's evidence differs from the evidence of its interval domain",
            ),
            Self::CutOperand => {
                f.write_str("the first operand of a lower or an upper cut is not a cut")
            },
        };
    }
}

/// A refused plan: where it fails and which check fails there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Refusal
{
    /// The node that fails, or the input as a whole.
    pub site: Site,
    /// The check that fails.
    pub check: Check,
}

impl fmt::Display for Refusal
{
    /// Write the refusal as one line: its site, then its check.
    ///
    /// # Specification
    /// - ensures: writes the site and the check's own line.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal at the input and one at a node.
    /// - witness: `tests::validate::refusals_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match self.site {
            Site::Input => write!(f, "the input: {}", self.check),
            Site::Node(node) => write!(f, "node {}: {}", u32::from(node), self.check),
        };
    }
}

impl core::error::Error for Refusal
{
}

/// A plan that the validation pass admitted. Only [`validate`] and
/// [`admit`] construct one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ValidatedPlan
{
    /// The admitted plan.
    plan: Plan,
}

impl ValidatedPlan
{
    /// The admitted plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plan(&self) -> &Plan
    {
        return &self.plan;
    }

    /// Take the admitted plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_plan(self) -> Plan
    {
        return self.plan;
    }
}

/// What the pass knows of one node.
#[derive(Clone, Copy, Debug)]
struct Mark
{
    /// The longest path from the node down, counted in nodes.
    height: Height,
    /// The most binders on a path from the node down.
    nesting: Height,
    /// The fewest binders on a path from the root to the node.
    context: Height,
}

/// Read untrusted bytes as a plan and validate it.
///
/// # Specification
/// - ensures: returns the validated plan that `bytes` hold.
/// - fails: refuses an input longer than `quotas.bytes` ([`Check::ByteQuota`])
///   or with more nodes than `quotas.nodes` ([`Check::NodeQuota`]) at the input
///   before it reads a node; refuses bytes that are not the canonical bytes of
///   a plan with [`Check::Decode`] at the node it read, or at the input; and
///   then refuses as [`admit`] does.
/// - panics: none.
/// - executable: none — the clause restates the pass.
///
/// # Errors
/// The first [`Refusal`] of the checks in the module's table.
///
/// # Adequacy
/// - hypothesis: L2 — every well-formed generated plan is admitted from its
///   bytes, and each one-fault edit of it is refused by name at its site; L3 —
///   each quota at its bound and one past it.
/// - witness: `tests::validate::well_formed_generated_plans_are_admitted`
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
/// - witness: `tests::validate::quotas_admit_at_the_bound_and_refuse_past_it`
#[inline]
pub fn validate(
    bytes: EncodedPlan<'_>,
    quotas: &Quotas,
    table: &EvidenceTable,
) -> Result<ValidatedPlan, Refusal>
{
    if bytes.as_ref().len() > quotas.bytes.0 {
        return Err(Refusal {
            site: Site::Input,
            check: Check::ByteQuota,
        });
    }
    let plan = read(bytes, quotas.nodes).map_err(|fault| {
        let check = match (fault.site(), fault.error()) {
            (Site::Input, DecodeError::TooManyNodes) => Check::NodeQuota,
            (_, error) => Check::Decode(error),
        };
        return Refusal {
            site: fault.site(),
            check,
        };
    })?;
    return admit(plan, quotas, table);
}

/// Validate a plan already in memory.
///
/// # Specification
/// - ensures: returns the plan, admitted, when every check of the module's
///   table holds.
/// - fails: refuses a plan with more nodes than `quotas.nodes` at the input;
///   then, in the plan's order, the first node whose payload, height or binder
///   nesting fails a check; then, from the root down, the first bound variable
///   that reaches past its binders.
/// - panics: none.
/// - executable: none — the clause restates the pass.
///
/// # Errors
/// The first [`Refusal`] in that order.
///
/// # Adequacy
/// - hypothesis: L2 — as [`validate`], on plans in memory: every well-formed
///   generated plan is admitted, and each one-fault edit of it is refused by
///   name at its site.
/// - witness: `tests::validate::well_formed_generated_plans_are_admitted`
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
/// - witness: `tests::validate::the_square_root_of_two_is_admitted`
#[inline]
pub fn admit(
    plan: Plan,
    quotas: &Quotas,
    table: &EvidenceTable,
) -> Result<ValidatedPlan, Refusal>
{
    if plan.node_count() > quotas.nodes {
        return Err(Refusal {
            site: Site::Input,
            check: Check::NodeQuota,
        });
    }
    let mut marks: Vec<Mark> = Vec::with_capacity(usize::from(plan.node_count()));
    // Children stand before their parents, so each child's mark is final
    // when its parent reads it.
    for (id, node) in plan.nodes() {
        let at = |check: Check| Refusal {
            site: Site::Node(id),
            check,
        };
        payload(&plan, node, quotas, table).map_err(at)?;
        let mut height = Height(1);
        let mut nesting = Height(0);
        for edge in node.edges() {
            let child = marks
                .get(usize::from(edge.node))
                .ok_or_else(|| at(Check::Decode(DecodeError::ForwardReference)))?;
            height = height.max(Height(child.height.0.saturating_add(1)));
            let inner = match edge.scope {
                Scope::Same => child.nesting,
                Scope::Inner => Height(child.nesting.0.saturating_add(1)),
            };
            nesting = nesting.max(inner);
        }
        if height > quotas.height {
            return Err(at(Check::HeightQuota));
        }
        if nesting > quotas.binders {
            return Err(at(Check::BinderQuota));
        }
        marks.push(Mark {
            height,
            nesting,
            context: Height(u32::MAX),
        });
    }
    // From the root down: each node takes the fewest binders over the paths
    // that reach it, and a bound variable must stay below that count.
    let root = usize::from(plan.root().node());
    if let Some(mark) = marks.get_mut(root) {
        mark.context = Height(0);
    }
    for index in (0 .. usize::from(plan.node_count())).rev() {
        let Ok(id) = NodeId::try_from(index)
        else {
            continue;
        };
        let Ok(node) = plan.node(id)
        else {
            continue;
        };
        let context = marks
            .get(usize::from(id))
            .map_or(Height(0), |mark| mark.context);
        if let Node::Real(Real::Bound(index)) = *node
            && u32::from(index) >= context.0
        {
            return Err(Refusal {
                site: Site::Node(id),
                check: Check::EscapedBinder,
            });
        }
        for edge in node.edges() {
            let inner = match edge.scope {
                Scope::Same => context,
                Scope::Inner => Height(context.0.saturating_add(1)),
            };
            if let Some(child) = marks.get_mut(usize::from(edge.node)) {
                child.context = child.context.min(inner);
            }
        }
    }
    return Ok(ValidatedPlan { plan });
}

/// Check one node's payload: its widths, its power, its hulls and its
/// evidence.
///
/// # Specification
/// - ensures: answers `Ok` exactly when each dyadic of the node keeps the width
///   quota, a power keeps the power quota, a cut's hull is proper and bounded,
///   an interval domain is proper and bounded and its compact evidence stands
///   on a closed hull, each evidence reference names the judgement its slot
///   takes, and a quantifier over an interval domain names the evidence that
///   the domain states.
/// - fails: returns the first check that fails, in that order.
/// - panics: none.
/// - executable: none — the clause restates the checks.
///
/// # Errors
/// The first failing [`Check`].
///
/// # Adequacy
/// - hypothesis: L3 — each payload fault on its smallest trigger, and every
///   payload of the well-formed generated plans.
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
/// - witness: `tests::validate::well_formed_generated_plans_are_admitted`
fn payload(
    plan: &Plan,
    node: &Node,
    quotas: &Quotas,
    table: &EvidenceTable,
) -> Result<(), Check>
{
    let expect = |evidence: Evidence, expected: Judgement| {
        let found = table.judgement(evidence)?;
        if found != expected {
            return Err(Check::EvidenceKind { expected, found });
        }
        return Ok(());
    };
    let slot = |slot: EvidenceSlot, expected: Judgement| {
        return match slot {
            EvidenceSlot::Absent => Ok(()),
            EvidenceSlot::Given(evidence) => expect(evidence, expected),
        };
    };
    match *node {
        Node::Real(ref real) => match *real {
            Real::Bound(_)
            | Real::Add(..)
            | Real::Sub(..)
            | Real::Mul(..)
            | Real::Pi
            | Real::Cos(_)
            | Real::Sin(_)
            | Real::Arg(..) => {},
            Real::Constant(ref value) => narrow(value, quotas)?,
            Real::Div { nonzero, .. } => expect(nonzero, Judgement::NonZero)?,
            Real::Power(_, power) => {
                if power > quotas.power {
                    return Err(Check::PowerQuota);
                }
            },
            Real::Cut(ref cut) => {
                hull(&cut.hull, quotas)?;
                if !bool::from(Shape::of(&cut.hull).bounded) {
                    return Err(Check::CutHull);
                }
                expect(cut.laws, Judgement::CutLaws)?;
            },
        },
        Node::Open(ref open) => match *open {
            Open::Top | Open::Bottom | Open::Less(..) | Open::Meet(..) | Open::Join(..) => {},
            Open::LowerCut(cut, _) | Open::UpperCut(cut, _) => {
                if !matches!(plan.node(cut.node()), Ok(&Node::Real(Real::Cut(_)))) {
                    return Err(Check::CutOperand);
                }
            },
            Open::Exists(quantifier) => {
                expect(quantifier.evidence, Judgement::Overt)?;
                slot(quantifier.dual, Judgement::Compact)?;
                stated(plan, quantifier, Modality::Overt)?;
            },
            Open::Forall(quantifier) => {
                expect(quantifier.evidence, Judgement::Compact)?;
                slot(quantifier.dual, Judgement::Overt)?;
                stated(plan, quantifier, Modality::Compact)?;
            },
        },
        Node::Domain(ref domain) => match *domain {
            Domain::Interval {
                ref hull,
                overt,
                compact,
            } => {
                self::hull(hull, quotas).map_err(|check| {
                    return if check == Check::CutHull {
                        Check::DomainHull
                    }
                    else {
                        check
                    };
                })?;
                // A quantifier ranges over a bounded domain alone, so its
                // search splits a finite interval.
                if !bool::from(Shape::of(hull).bounded) {
                    return Err(Check::DomainHull);
                }
                if matches!(compact, EvidenceSlot::Given(_))
                    && !bool::from(Shape::of(hull).closed_and_bounded)
                {
                    return Err(Check::DomainHull);
                }
                slot(overt, Judgement::Overt)?;
                slot(compact, Judgement::Compact)?;
            },
            Domain::Product { evidence, .. } => expect(evidence, Judgement::Product)?,
            Domain::Subdomain { evidence, .. } => expect(evidence, Judgement::Subdomain)?,
        },
    }
    return Ok(());
}

/// Whether a dyadic keeps the width quota.
///
/// # Specification
/// - ensures: answers `Ok` exactly when the value's width is at most the width
///   quota.
/// - fails: returns [`Check::WidthQuota`] otherwise.
/// - panics: none.
///
/// # Errors
/// - [`Check::WidthQuota`]: the value is wider than the quota.
///
/// # Adequacy
/// - hypothesis: L3 — a constant at the quota and one bit past it.
/// - witness: `tests::validate::quotas_admit_at_the_bound_and_refuse_past_it`
#[inline]
#[spec(ensures: |ref result| result.is_ok() == (value.width() <= quotas.width))]
fn narrow(
    value: &Dyadic,
    quotas: &Quotas,
) -> Result<(), Check>
{
    if value.width() > quotas.width {
        return Err(Check::WidthQuota);
    }
    return Ok(());
}

/// Whether a hull is proper and its finite endpoints keep the width quota.
///
/// # Specification
/// - ensures: answers `Ok` exactly when the hull is proper and each finite
///   endpoint keeps the width quota.
/// - fails: returns [`Check::CutHull`] for a dual hull and
///   [`Check::WidthQuota`] for a wide endpoint.
/// - panics: none.
/// - executable: none — the clause restates the checks.
///
/// # Errors
/// - [`Check::CutHull`]: the hull is dual.
/// - [`Check::WidthQuota`]: an endpoint is wider than the quota.
///
/// # Adequacy
/// - hypothesis: L3 — a dual hull of a cut and of a domain, and a wide
///   endpoint.
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
fn hull(
    interval: &NumericInterval,
    quotas: &Quotas,
) -> Result<(), Check>
{
    if interval.orientation() != Orientation::Proper {
        return Err(Check::CutHull);
    }
    for bound in [interval.lower(), interval.upper()] {
        if let Endpoint::Finite(ref value) = bound.endpoint {
            narrow(value, quotas)?;
        }
    }
    return Ok(());
}

/// Whether a value is so.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Holds(bool);

impl From<Holds> for bool
{
    /// The answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(holds: Holds) -> Self
    {
        return holds.0;
    }
}

/// The shape of a hull: whether both endpoints are finite, and whether both
/// are also closed.
#[derive(Clone, Copy, Debug)]
struct Shape
{
    /// Both endpoints are finite.
    bounded: Holds,
    /// Both endpoints are finite and closed.
    closed_and_bounded: Holds,
}

impl Shape
{
    /// The shape of `interval`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn of(interval: &NumericInterval) -> Self
    {
        let finite = |bound: &Bound| matches!(bound.endpoint, Endpoint::Finite(_));
        let closed = |bound: &Bound| finite(bound) && bound.closure == Closure::Closed;
        return Self {
            bounded: Holds(finite(interval.lower()) && finite(interval.upper())),
            closed_and_bounded: Holds(closed(interval.lower()) && closed(interval.upper())),
        };
    }
}

/// The modality that a quantifier needs of its domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Modality
{
    /// An existential needs an overt domain.
    Overt,
    /// A universal needs a compact domain.
    Compact,
}

/// Whether a quantifier over an interval domain names the evidence that the
/// domain states: its own evidence in the slot of its modality, its dual
/// evidence, when given, in the other slot.
///
/// # Specification
/// - ensures: answers `Ok` for a domain that is not an interval, and for an
///   interval domain whose slot of `modality` gives the quantifier's evidence
///   and whose other slot gives the quantifier's dual evidence when the
///   quantifier gives one.
/// - fails: returns [`Check::DomainEvidence`] otherwise, and [`Check::Decode`]
///   when the domain names no node.
/// - panics: none.
/// - executable: none — the clause restates the check.
///
/// # Errors
/// - [`Check::DomainEvidence`]: the quantifier and its interval domain
///   disagree.
///
/// # Adequacy
/// - hypothesis: L3 — an existential over an interval whose overt slot is
///   absent, one whose slot gives other evidence, and the well-formed
///   quantifiers of the generated plans.
/// - witness: `tests::validate::each_fault_is_refused_by_name_at_its_node`
/// - witness: `tests::validate::well_formed_generated_plans_are_admitted`
fn stated(
    plan: &Plan,
    quantifier: Quantifier,
    modality: Modality,
) -> Result<(), Check>
{
    let domain = plan
        .node(quantifier.domain.node())
        .map_err(|_unknown| Check::Decode(DecodeError::ForwardReference))?;
    let Node::Domain(Domain::Interval { overt, compact, .. }) = *domain
    else {
        return Ok(());
    };
    let (own, other) = match modality {
        Modality::Overt => (overt, compact),
        Modality::Compact => (compact, overt),
    };
    if own != EvidenceSlot::Given(quantifier.evidence) {
        return Err(Check::DomainEvidence);
    }
    if let EvidenceSlot::Given(dual) = quantifier.dual
        && other != EvidenceSlot::Given(dual)
    {
        return Err(Check::DomainEvidence);
    }
    return Ok(());
}
