//! Cut elimination: a strict comparison that reads a cut on one side becomes
//! the lower or the upper cut of that cut at the other side.
//!
//! A formula can read the real of a cut only through a strict comparison. Such
//! a comparison needs no enclosure of the cut's real: the cut decides each
//! dyadic itself. So the elimination rewrites `p < c`, for a cut `c` and a real
//! `p` that does not read `c`, to the lower cut of `c` at `p`. It rewrites
//! `c < p` to the upper cut of `c` at `p`. The machine then encloses `p` alone,
//! and the step that concludes reads the cut's membership at an end of that
//! enclosure.
//!
//! | Comparison | Condition | Becomes |
//! | --- | --- | --- |
//! | `p < c` | `c` is a cut, and `p` does not read `c` | [`Open::LowerCut`] of `c` at `p` |
//! | `c < p` | `c` is a cut, `p` does not read `c`, and the row above does not apply | [`Open::UpperCut`] of `c` at `p` |
//! | `c < c`, and every other comparison | none | itself |
//!
//! The elimination rewrites a validated plan to a validated plan. Each node
//! keeps a place in the rewritten plan, so an obligation on a comparison moves
//! to its rewritten node. A certificate of the rewritten plan moves back to the
//! original plan, where the checker replays it as a certificate of the
//! comparison that its node replaces. A plan with no comparison to rewrite
//! comes back as it is, with no copy.
//!
//! # Items
//!
//! - [`eliminate`] — the rewrite of a validated plan.
//! - [`Elimination`] — the rewritten plan, and the places that move obligations
//!   to it and certificates back from it.
//! - [`EliminationError`] — why a plan does not rewrite.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::certificate::Certificate;
use crate::plan::Node;
use crate::plan::NodeCount;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::PlanBuilder;
use crate::plan::PlanError;
use crate::plan::Real;
use crate::plan::RealId;
use crate::semidecision::Obligation;
use crate::validate::EvidenceTable;
use crate::validate::Quotas;
use crate::validate::Refusal;
use crate::validate::ValidatedPlan;
use crate::validate::admit;

/// Why a plan does not rewrite.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EliminationError
{
    /// The builder refuses a node of the rewritten plan.
    Plan(PlanError),
    /// The validation pass refuses the rewritten plan.
    Refused(Refusal),
}

impl fmt::Display for EliminationError
{
    /// Write the error as one line.
    ///
    /// # Specification
    /// - ensures: writes one line per variant, the wrapped error after its
    ///   phrase.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::elimination::errors_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return match *self {
            Self::Plan(error) => write!(f, "the rewritten plan does not build: {error}"),
            Self::Refused(refusal) => write!(f, "the rewritten plan is refused: {refusal}"),
        };
    }
}

impl core::error::Error for EliminationError
{
}

/// Where the nodes of the original plan stand in the rewritten plan.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Places
{
    /// No comparison is rewritten: each node keeps its position.
    Kept,
    /// The rewritten plan moves the nodes.
    Moved
    {
        /// The place of each node of the original plan, by its position.
        forward: Vec<NodeId>,
        /// A node of the original plan for each node of the rewritten plan, by
        /// its position.
        back: Vec<NodeId>,
    },
}

/// A validated plan with each comparison that reads a cut on one side
/// rewritten, and the places of its nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Elimination
{
    /// The rewritten plan.
    plan: ValidatedPlan,
    /// The comparisons rewritten.
    rewritten: NodeCount,
    /// The places of the nodes.
    places: Places,
}

impl Elimination
{
    /// The rewritten plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plan(&self) -> &ValidatedPlan
    {
        return &self.plan;
    }

    /// Take the rewritten plan.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_plan(self) -> ValidatedPlan
    {
        return self.plan;
    }

    /// The number of comparisons rewritten.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rewritten(&self) -> NodeCount
    {
        return self.rewritten;
    }

    /// The place in the rewritten plan of the node at `node` of the original
    /// plan, or `None` when the original plan holds no node there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn place(
        &self,
        node: NodeId,
    ) -> Option<NodeId>
    {
        return match self.places {
            Places::Kept => {
                (usize::from(node) < usize::from(self.plan.plan().node_count())).then_some(node)
            },
            Places::Moved { ref forward, .. } => forward.get(usize::from(node)).copied(),
        };
    }

    /// The obligation on the rewritten plan that asks what `original` asks of
    /// the original plan.
    ///
    /// # Specification
    /// - ensures: the obligation names the place of the original node, with the
    ///   same demand.
    /// - fails: refuses a node that the original plan does not hold as
    ///   [`PlanError::UnknownNode`], and a demand of the other sort as
    ///   [`PlanError::WrongSort`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: the original plan holds no node there.
    /// - [`PlanError::WrongSort`]: the node's sort does not take the demand.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every comparison of the generated plans keeps its
    ///   place, and the moved obligation settles as the original does.
    /// - witness: `tests::elimination::generated_plans_answer_alike_after_the_elimination`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |moved| moved.demand() == original.demand() && Some(moved.node()) == self.place(original.node())))]
    pub fn obligation(
        &self,
        original: Obligation,
    ) -> Result<Obligation, PlanError>
    {
        let node = self.place(original.node()).ok_or(PlanError::UnknownNode)?;
        return Obligation::new(&self.plan, node, original.demand());
    }

    /// The certificate of the original plan that `certificate`, a certificate
    /// of the rewritten plan, moves back to, or `None` when a step names a
    /// node that the rewritten plan does not hold.
    ///
    /// # Specification
    /// - ensures: each step names the original node that its rewritten node
    ///   stands for. A step on a lower or an upper cut names the comparison it
    ///   replaces, which the checker reads with the same rule.
    /// - fails: returns `None` for a step whose node the rewritten plan does
    ///   not hold.
    /// - panics: none.
    /// - intension: one copy of the certificate's steps.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every certificate of the rewritten generated plans
    ///   replays on the original plan to the same conclusion at the original
    ///   node.
    /// - witness: `tests::elimination::generated_plans_answer_alike_after_the_elimination`
    /// - witness: `tests::elimination::the_square_root_of_two_above_45_32_is_its_lower_cut`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().is_none_or(|moved| moved.step_count() == certificate.step_count() && moved.format() == certificate.format()))]
    #[must_use]
    pub fn restored(
        &self,
        certificate: &Certificate,
    ) -> Option<Certificate>
    {
        let Places::Moved { ref back, .. } = self.places
        else {
            return Some(certificate.clone());
        };
        let rename = |node: NodeId| back.get(usize::from(node)).copied();
        let mut steps = Vec::with_capacity(certificate.steps().len());
        for step in certificate.steps() {
            steps.push(step.renamed(rename)?);
        }
        return Some(Certificate::new(certificate.format(), steps));
    }
}

/// The cuts that a node reads: one bit for each cut node of the plan, in
/// rows of words, one row per node.
struct Reads
{
    /// The words of one row.
    width: usize,
    /// The rows, by the node's position.
    bits: Vec<u64>,
}

impl Reads
{
    /// Whether the node at `node` reads the cut whose bit is `bit`.
    ///
    /// # Specification
    /// trivial.
    fn reads(
        &self,
        node: NodeId,
        bit: CutBit,
    ) -> Reading
    {
        let slot = bit.slot();
        let word = usize::from(node)
            .saturating_mul(self.width)
            .saturating_add(slot.word);
        let set = self
            .bits
            .get(word)
            .is_some_and(|&held| held & slot.mask != 0);
        return if set { Reading::Reads } else { Reading::Apart };
    }
}

/// A cut node's bit among the cuts of a plan.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CutBit(usize);

/// Where a cut's bit stands in a row: its word, and its mask in that word.
#[derive(Clone, Copy, Debug)]
struct Slot
{
    /// The word of the row.
    word: usize,
    /// The bit in that word.
    mask: u64,
}

impl CutBit
{
    /// Where the bit stands in a row of 64-bit words.
    ///
    /// # Specification
    /// trivial.
    fn slot(self) -> Slot
    {
        let shift = u32::try_from(self.0.checked_rem(64).unwrap_or_default()).unwrap_or_default();
        return Slot {
            word: self.0.checked_div(64).unwrap_or_default(),
            mask: 1_u64.checked_shl(shift).unwrap_or_default(),
        };
    }
}

/// Whether a real reads a cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The cut is the real, or a node below it.
    Reads,
    /// The real does not reach the cut.
    Apart,
}

/// Rewrite each strict comparison of `plan` that reads a cut on one side, as
/// the module's table states.
///
/// # Specification
/// - ensures: the rewritten plan holds the original plan's nodes, each
///   comparison of the table's first two rows rewritten. It passes the
///   validation of `quotas` and `table`. Each node of the original plan has a
///   place in it. A plan with no comparison to rewrite comes back unchanged.
/// - fails: returns [`EliminationError::Plan`] when the builder refuses a node,
///   and [`EliminationError::Refused`] when the validation pass refuses the
///   rewritten plan. Neither happens to a plan that `quotas` and `table` admit,
///   because the rewrite keeps each payload and each edge.
/// - panics: none.
/// - executable: none — the clause restates the table.
/// - intension: one walk of the plan's nodes, one row of `⌈k / 64⌉` words for
///   each node with `k` cuts in the plan, one builder of the rewritten plan,
///   its canonical walk, and one validation pass.
///
/// # Errors
/// - [`EliminationError::Plan`]: the builder refuses a node.
/// - [`EliminationError::Refused`]: the validation pass refuses the plan.
///
/// # Adequacy
/// - hypothesis: L2 — every generated plan rewrites, and each obligation on it
///   settles alike before and after. L3 — `p < c`, `c < p`, `c < c`, a point
///   that reads its cut, two cuts, and a plan with no cut.
/// - witness: `tests::elimination::generated_plans_answer_alike_after_the_elimination`
/// - witness: `tests::elimination::each_comparison_rewrites_as_the_table_states`
#[inline]
pub fn eliminate(
    plan: ValidatedPlan,
    quotas: &Quotas,
    table: &EvidenceTable,
) -> Result<Elimination, EliminationError>
{
    let original = plan.plan();
    let count = usize::from(original.node_count());
    // A plan with no cut needs no rewrite, so the scan allocates nothing for
    // it.
    let is_cut = |node: &Node| matches!(*node, Node::Real(Real::Cut(_)));
    if !original.nodes().any(|(_, node)| is_cut(node)) {
        return Ok(Elimination {
            plan,
            rewritten: NodeCount::default(),
            places: Places::Kept,
        });
    }
    // The bit of each cut node, by its position.
    let mut bits: Vec<Option<CutBit>> = vec![None; count];
    let mut cuts = 0_usize;
    for (id, node) in original.nodes() {
        if is_cut(node)
            && let Some(slot) = bits.get_mut(usize::from(id))
        {
            *slot = Some(CutBit(cuts));
            cuts = cuts.saturating_add(1);
        }
    }
    // Children stand before their parents, so each child's row is final when
    // its parent reads it.
    let width = cuts.div_ceil(64);
    let mut reads = Reads {
        width,
        bits: vec![0; count.saturating_mul(width)],
    };
    for (id, node) in original.nodes() {
        let row = usize::from(id).saturating_mul(width);
        for edge in node.edges() {
            let from = usize::from(edge.node).saturating_mul(width);
            for offset in 0 .. width {
                let below = reads
                    .bits
                    .get(from.saturating_add(offset))
                    .copied()
                    .unwrap_or_default();
                if let Some(word) = reads.bits.get_mut(row.saturating_add(offset)) {
                    *word |= below;
                }
            }
        }
        if let Some(&Some(bit)) = bits.get(usize::from(id)) {
            let slot = bit.slot();
            if let Some(word) = reads.bits.get_mut(row.saturating_add(slot.word)) {
                *word |= slot.mask;
            }
        }
    }
    // A comparison is rewritten when one side is a cut that the other side
    // does not read. The cut on the right comes first.
    let cut_apart = |cut: RealId, point: RealId| {
        return match bits.get(usize::from(cut.node())) {
            Some(&Some(bit)) => reads.reads(point.node(), bit) == Reading::Apart,
            Some(&None) | None => false,
        };
    };
    let mut builder = PlanBuilder::default();
    let mut rewritten = 0_usize;
    for (_, node) in original.nodes() {
        let next = match *node {
            Node::Open(Open::Less(left, right)) if cut_apart(right, left) => {
                rewritten = rewritten.saturating_add(1);
                Node::Open(Open::LowerCut(right, left))
            },
            Node::Open(Open::Less(left, right)) if cut_apart(left, right) => {
                rewritten = rewritten.saturating_add(1);
                Node::Open(Open::UpperCut(left, right))
            },
            Node::Real(_) | Node::Open(_) | Node::Domain(_) => node.clone(),
        };
        let _position = builder.push(next).map_err(EliminationError::Plan)?;
    }
    if rewritten == 0 {
        return Ok(Elimination {
            plan,
            rewritten: NodeCount::default(),
            places: Places::Kept,
        });
    }
    // The builder holds each node at its original position, so the original
    // root names the rewritten root.
    let (moved, placed) = builder
        .finish_placed(original.root())
        .map_err(EliminationError::Plan)?;
    let mut forward = Vec::with_capacity(placed.len());
    let mut back: Vec<Option<NodeId>> = vec![None; usize::from(moved.node_count())];
    for (position, place) in placed.into_iter().enumerate() {
        let place = place.ok_or(EliminationError::Plan(PlanError::UnknownNode))?;
        let origin = NodeId::try_from(position).map_err(EliminationError::Plan)?;
        if let Some(slot) = back.get_mut(usize::from(place))
            && slot.is_none()
        {
            *slot = Some(origin);
        }
        forward.push(place);
    }
    let back = back
        .into_iter()
        .map(|origin| origin.ok_or(EliminationError::Plan(PlanError::UnknownNode)))
        .collect::<Result<Vec<NodeId>, EliminationError>>()?;
    let moved = admit(moved, quotas, table).map_err(EliminationError::Refused)?;
    return Ok(Elimination {
        plan: moved,
        rewritten: NodeCount::from(rewritten),
        places: Places::Moved { forward, back },
    });
}
