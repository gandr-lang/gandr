//! The bisection search of a bounded quantifier over a dyadic interval.
//!
//! A [`Search`] settles an existential or a universal whose body compares two
//! polynomials in the bound variable: sums, differences and products of
//! constants and the variable. The search splits the quantifier's domain into
//! pieces and visits them breadth first: each piece before the halves of any
//! piece that splits after it. So a piece that never settles, as one that
//! touches a root of the body, keeps no later piece from its turn. On each
//! piece it writes the enclosure of each operand under the hypothesis that the
//! variable lies in the piece. The operands of a piece separate on one side,
//! or the piece splits at the point of its [`Split`]. A part of an operand
//! that does not read the variable is enclosed once, and each piece reads its
//! step.
//!
//! |Quantifier|Asked|A piece where the body holds|A piece where the body fails|
//! |---|---|---|---|
//! |`exists`|holds|a `Witness`|the search goes on|
//! |`exists`|fails|the search stops, opposed|a premise of the `Refutation`|
//! |`forall`|holds|a premise of the `Cover`|the search stops, opposed|
//! |`forall`|fails|the search goes on|a `Counterexample`|
//!
//! A search that runs out of pieces before it settles stops as opposed. An
//! existential's piece that touches an open end of its domain is no witness,
//! so that piece splits again. Each written step is one unit of work, so the
//! run's budget bounds the pieces that the search visits, and the checker's
//! width quota bounds how often a piece splits.

use alloc::collections::VecDeque;
use alloc::vec::Vec;

use crate::certificate::CheckerQuotas;
use crate::certificate::Operation;
use crate::certificate::Step;
use crate::certificate::StepCount;
use crate::certificate::StepId;
use crate::certificate::combined;
use crate::certificate::separated_below;
use crate::dyadic::Dyadic;
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
use crate::plan::Real;
use crate::schema::Split;
use crate::semidecision::Demand;
use crate::semidecision::SuspendReason;
use crate::semidecision::suspension;

/// The quantifier that a search settles.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Form
{
    /// An existential.
    Exists,
    /// A universal.
    Forall,
}

/// Whether a node of an operand reads the variable.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Reads
{
    /// The node reads the variable, so each piece encloses it again.
    Variable,
    /// The node reads no variable, so one enclosure serves every piece.
    Nothing,
}

/// Whether the last step of the queue concludes the search.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Ending
{
    /// The search goes on after the queue.
    Open,
    /// The last step of the queue concludes the evidence asked for.
    Concludes,
}

/// What one unit of a search did.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Turn
{
    /// The unit wrote one step, and the search goes on.
    Stepped,
    /// The unit wrote the step that concludes the evidence asked for.
    Concluded,
}

/// What a piece settles.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Settles
{
    /// The piece concludes the evidence asked for.
    Conclude,
    /// The piece is one premise of a cover.
    Premise,
    /// The piece settles on the side that the search does not ask for, which
    /// a later piece can outweigh.
    Nothing,
    /// The piece settles on no side, so it splits.
    Split,
}

/// One node of the operands, at its place in the order of the walk.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Visited
{
    /// The node.
    node: NodeId,
    /// Whether it reads the variable.
    reads: Reads,
    /// The places in the order of the two nodes that it reads, for a sum, a
    /// difference or a product.
    operands: Option<(Place, Place)>,
}

/// The place of a node in the order of the walk.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Place(usize);

/// The enclosure of one node, and the step that concludes it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Enclosed
{
    /// The step that concludes the enclosure.
    step: StepId,
    /// The enclosure.
    interval: NumericInterval,
}

/// A count of the pieces of a domain that a search holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PieceCount(usize);

impl PieceCount
{
    /// No piece.
    pub const ZERO: Self = Self(0);
}

impl From<usize> for PieceCount
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

impl From<PieceCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: PieceCount) -> Self
    {
        return count.0;
    }
}

/// The search for the evidence of one quantified formula.
///
/// # Specification
/// - invariant: the pending pieces and the pieces of the premises lie inside
///   the domain's closure, and together with the pieces that settled nothing
///   they partition it. Each premise concludes the body on its piece. Each
///   enclosure stands at the place of its node in the order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Search
{
    /// The quantifier.
    quantifier: NodeId,
    /// Its form.
    form: Form,
    /// The pole asked of it.
    asked: Demand,
    /// The comparison that its body is.
    less: NodeId,
    /// The places in the order of the first and the second operand.
    operands: (Place, Place),
    /// The nodes of the operands, each after the nodes that it reads.
    order: Vec<Visited>,
    /// The current enclosure of each node of the order: under no hypothesis
    /// for a node that reads no variable, and under the current piece for one
    /// that reads it.
    enclosed: Vec<Option<Enclosed>>,
    /// The ends of the domain, each with its closure.
    hull: ((Dyadic, Closure), (Dyadic, Closure)),
    /// The pieces not yet visited, the next one first.
    pieces: VecDeque<(Dyadic, Dyadic)>,
    /// The steps that conclude the body on each piece of a cover, each with
    /// the lower end of its piece.
    premises: Vec<(Dyadic, StepId)>,
    /// The steps of the current piece not yet written, the next one last.
    queue: Vec<Step>,
    /// Whether the queue's last step concludes.
    ending: Ending,
}

/// A visit of the walk over an operand's nodes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Visit
{
    /// The walk reaches the node: its operands come first.
    Enter(NodeId),
    /// The walk leaves the node: its operands are in the order.
    Leave(NodeId),
}

impl Search
{
    /// The search that settles `demand` of the quantifier at `node` of `plan`.
    ///
    /// # Specification
    /// - ensures: the node is an existential or a universal over an interval
    ///   with finite ends, and its body is a comparison of two operands made of
    ///   constants, the variable at index zero, sums, differences and products.
    ///   A failure asked of it needs evidence of the other modality.
    /// - fails: suspends with [`SuspendReason::NoRule`] for any other form.
    /// - panics: none.
    /// - executable: none — the clause speaks of the form of the plan.
    /// - intension: one walk of the operands' nodes, and one table of the
    ///   plan's nodes for the walk.
    ///
    /// # Errors
    /// - [`SuspendReason::NoRule`]: the machine has no rule for the form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each quantifier and pole, a body that reads a cut,
    ///   and a failure with no evidence of the other modality.
    /// - witness: `tests::quantifier::each_quantified_form_settles_or_suspends_by_name`
    pub(crate) fn new(
        plan: &Plan,
        node: NodeId,
        demand: Demand,
    ) -> Result<Self, SuspendReason>
    {
        let fetch = |id: NodeId| plan.node(id).map_err(|_unknown| SuspendReason::NoRule);
        let (form, quantifier) = match *fetch(node)? {
            Node::Open(Open::Exists(quantifier)) => (Form::Exists, quantifier),
            Node::Open(Open::Forall(quantifier)) => (Form::Forall, quantifier),
            Node::Real(_) | Node::Open(_) | Node::Domain(_) => return Err(SuspendReason::NoRule),
        };
        if demand == Demand::Fails && quantifier.dual == EvidenceSlot::Absent {
            return Err(SuspendReason::NoRule);
        }
        let Node::Domain(Domain::Interval { ref hull, .. }) = *fetch(quantifier.domain.node())?
        else {
            return Err(SuspendReason::NoRule);
        };
        let (&Endpoint::Finite(ref low), &Endpoint::Finite(ref high)) =
            (&hull.lower().endpoint, &hull.upper().endpoint)
        else {
            return Err(SuspendReason::NoRule);
        };
        let Node::Open(Open::Less(first, second)) = *fetch(quantifier.body.node())?
        else {
            return Err(SuspendReason::NoRule);
        };
        let (order, operands) = order(plan, (first.node(), second.node()))?;
        let enclosed = alloc::vec![None; order.len()];
        return Ok(Self {
            quantifier: node,
            form,
            asked: demand,
            less: quantifier.body.node(),
            operands,
            order,
            enclosed,
            hull: (
                (low.clone(), hull.lower().closure),
                (high.clone(), hull.upper().closure),
            ),
            pieces: VecDeque::from([(low.clone(), high.clone())]),
            premises: Vec::new(),
            queue: Vec::new(),
            ending: Ending::Open,
        });
    }

    /// The pieces that the search holds: the piece whose steps it writes, and
    /// the pieces that it has yet to visit.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn held(&self) -> PieceCount
    {
        return PieceCount(
            self.pieces
                .len()
                .saturating_add(usize::from(!self.queue.is_empty())),
        );
    }

    /// One unit of work: write the next step of the current piece, after the
    /// plan of the next piece when the current one has no step left.
    ///
    /// # Specification
    /// - ensures: one step is added to `steps`. [`Turn::Concluded`] marks the
    ///   step that concludes the evidence asked for. The steps stay a prefix of
    ///   a certificate that [`crate::certificate::check`] replays.
    /// - fails: suspends with [`SuspendReason::Opposed`] when a piece settles
    ///   on the other side or the pieces run out, with [`SuspendReason::Quota`]
    ///   past a quota, and with [`SuspendReason::NoRule`] when a piece needs no
    ///   step and settles nothing.
    /// - panics: none.
    /// - executable: none — the clause speaks of the certificate's replay.
    /// - intension: the plan of a piece is one pass over the operands' nodes,
    ///   at most four exact products of dyadics each. Writing a planned step
    ///   moves it and copies nothing.
    ///
    /// # Errors
    /// - [`SuspendReason`]: the search stops for the reason above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated quantified formulas, each certificate
    ///   replayed to its evidence. L3 — each row of the module's table, and a
    ///   search that its budget stops.
    /// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
    /// - witness: `tests::quantifier::each_quantified_form_settles_or_suspends_by_name`
    pub(crate) fn unit(
        &mut self,
        plan: &Plan,
        steps: &mut Vec<Step>,
        quotas: &CheckerQuotas,
        split: Split,
    ) -> Result<Turn, SuspendReason>
    {
        if self.queue.is_empty() {
            self.next_piece(plan, StepCount::from(steps.len()), (quotas, split))?;
        }
        if steps.len() >= usize::from(quotas.steps) {
            return Err(SuspendReason::Quota);
        }
        let step = self.queue.pop().ok_or(SuspendReason::NoRule)?;
        steps.push(step);
        if self.queue.is_empty() && self.ending == Ending::Concludes {
            return Ok(Turn::Concluded);
        }
        return Ok(Turn::Stepped);
    }

    /// Plan the steps of the next piece, the first of them after the `base`
    /// steps written so far.
    ///
    /// # Specification
    /// - ensures: the queue holds the steps of one piece, and the ending states
    ///   whether its last step concludes. A piece that settles nothing splits
    ///   at the point of `split`, and both halves wait behind the pieces before
    ///   them. A cover lists its premises by the lower ends of their pieces.
    /// - fails: as [`Self::unit`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the pieces' order.
    ///
    /// # Errors
    /// - [`SuspendReason`]: as [`Self::unit`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::unit`].
    /// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
    fn next_piece(
        &mut self,
        plan: &Plan,
        base: StepCount,
        (quotas, split): (&CheckerQuotas, Split),
    ) -> Result<(), SuspendReason>
    {
        let (lower, upper) = self.pieces.pop_front().ok_or(SuspendReason::Opposed)?;
        let base = usize::from(base);
        let at = |offset: usize| {
            StepId::try_from(base.saturating_add(offset)).map_err(|_wide| SuspendReason::Quota)
        };
        let mut written: Vec<Step> = Vec::new();
        for (place, visited) in self.order.iter().enumerate() {
            let known = self.enclosed.get(place).and_then(Option::as_ref);
            if visited.reads == Reads::Nothing && known.is_some() {
                continue;
            }
            let operand = |place: Place| {
                self.enclosed
                    .get(place.0)
                    .and_then(Option::as_ref)
                    .ok_or(SuspendReason::NoRule)
            };
            let node = visited.node;
            let (step, interval) = match (
                plan.node(node).map_err(|_unknown| SuspendReason::NoRule)?,
                visited.operands,
            ) {
                (&Node::Real(Real::Bound(_)), None) => {
                    if lower.width() > quotas.width || upper.width() > quotas.width {
                        return Err(SuspendReason::Quota);
                    }
                    (
                        Step::Variable {
                            real: node,
                            lower: lower.clone(),
                            upper: upper.clone(),
                        },
                        NumericInterval::new(
                            Bound::closed(lower.clone()),
                            Bound::closed(upper.clone()),
                            Orientation::Proper,
                        )
                        .map_err(|_reversed| SuspendReason::NoRule)?,
                    )
                },
                (&Node::Real(Real::Constant(ref value)), None) => {
                    if value.width() > quotas.width {
                        return Err(SuspendReason::Quota);
                    }
                    (
                        Step::Constant { real: node },
                        NumericInterval::point(value.clone()),
                    )
                },
                (
                    &Node::Real(ref real @ (Real::Add(..) | Real::Sub(..) | Real::Mul(..))),
                    Some((left, right)),
                ) => {
                    let (first, second) = (operand(left)?, operand(right)?);
                    let operation = match *real {
                        Real::Add(..) => Operation::Sum,
                        Real::Sub(..) => Operation::Difference,
                        Real::Bound(_)
                        | Real::Constant(_)
                        | Real::Mul(..)
                        | Real::Div { .. }
                        | Real::Power(..)
                        | Real::Cut(_)
                        | Real::Pi
                        | Real::Cos(_)
                        | Real::Sin(_)
                        | Real::Arg(..) => Operation::Product,
                    };
                    let interval = combined(operation, &first.interval, &second.interval, quotas)
                        .map_err(suspension)?;
                    let (left, right) = (first.step, second.step);
                    let step = match operation {
                        Operation::Sum => Step::Sum {
                            real: node,
                            left,
                            right,
                        },
                        Operation::Difference => Step::Difference {
                            real: node,
                            left,
                            right,
                        },
                        Operation::Product => Step::Product {
                            real: node,
                            left,
                            right,
                        },
                    };
                    (step, interval)
                },
                (&(Node::Real(_) | Node::Open(_) | Node::Domain(_)), _) => {
                    return Err(SuspendReason::NoRule);
                },
            };
            let slot = self.enclosed.get_mut(place).ok_or(SuspendReason::NoRule)?;
            *slot = Some(Enclosed {
                step: at(written.len())?,
                interval,
            });
            written.push(step);
        }
        let operand = |place: Place| {
            self.enclosed
                .get(place.0)
                .and_then(Option::as_ref)
                .ok_or(SuspendReason::NoRule)
        };
        let (first, second) = (operand(self.operands.0)?, operand(self.operands.1)?);
        let holds = separated_below(&first.interval, &second.interval).is_ok();
        let fails = first.interval.lower().endpoint >= second.interval.upper().endpoint;
        let (left, right) = (first.step, second.step);
        let comparison = if holds {
            Some(Step::Below {
                less: self.less,
                left,
                right,
            })
        }
        else if fails {
            Some(Step::NotBelow {
                less: self.less,
                left,
                right,
            })
        }
        else {
            None
        };
        // A body that reads no variable holds under no hypothesis, so any piece
        // is a witness. Otherwise a witness's piece lies inside the domain.
        let hypothetical = self
            .order
            .iter()
            .any(|visited| visited.reads == Reads::Variable);
        let at_open_end = (lower == self.hull.0.0 && self.hull.0.1 == Closure::Open)
            || (upper == self.hull.1.0 && self.hull.1.1 == Closure::Open);
        let inside = !hypothetical || !at_open_end;
        let settles = match (self.form, self.asked, holds, fails) {
            (Form::Exists, Demand::Holds, true, _) if inside => Settles::Conclude,
            (Form::Forall, Demand::Fails, _, true) => Settles::Conclude,
            (Form::Forall, Demand::Holds, true, _) | (Form::Exists, Demand::Fails, _, true) => {
                Settles::Premise
            },
            (Form::Forall, Demand::Holds, false, true) | (Form::Exists, Demand::Fails, true, _) => {
                return Err(SuspendReason::Opposed);
            },
            (Form::Exists, Demand::Holds, _, true) | (Form::Forall, Demand::Fails, true, _) => {
                Settles::Nothing
            },
            (..) => Settles::Split,
        };
        let mut ending = Ending::Open;
        match settles {
            Settles::Conclude => {
                let premise = at(written.len())?;
                written.extend(comparison);
                written.push(match self.form {
                    Form::Exists => Step::Witness {
                        exists: self.quantifier,
                        premise,
                    },
                    Form::Forall => Step::Counterexample {
                        forall: self.quantifier,
                        premise,
                    },
                });
                ending = Ending::Concludes;
            },
            Settles::Premise => {
                self.premises.push((lower, at(written.len())?));
                written.extend(comparison);
                if self.pieces.is_empty() {
                    // The pieces settle in breadth-first order, so the cover
                    // sorts them from the domain's lower end to its upper end.
                    let mut pieces = core::mem::take(&mut self.premises);
                    pieces.sort_unstable_by(|first, second| first.0.cmp(&second.0));
                    let premises: Vec<StepId> = pieces.into_iter().map(|(_, id)| id).collect();
                    written.push(match self.form {
                        Form::Forall => Step::Cover {
                            forall: self.quantifier,
                            premises,
                        },
                        Form::Exists => Step::Refutation {
                            exists: self.quantifier,
                            premises,
                        },
                    });
                    ending = Ending::Concludes;
                }
            },
            Settles::Nothing => {},
            Settles::Split => {
                let middle = split.point(&lower, &upper).map_err(suspension)?;
                if middle.width() > quotas.width || middle == lower || middle == upper {
                    return Err(SuspendReason::Quota);
                }
                self.pieces.push_back((lower, middle.clone()));
                self.pieces.push_back((middle, upper));
            },
        }
        if written.is_empty() {
            return Err(SuspendReason::NoRule);
        }
        written.reverse();
        self.queue = written;
        self.ending = ending;
        return Ok(());
    }
}

/// The nodes of the two `operands`, each after the nodes that it reads, and
/// the places of the two operands in that order.
///
/// # Specification
/// - ensures: each node of the operands once, after its own operands, with the
///   places of the nodes that it reads.
/// - fails: suspends with [`SuspendReason::NoRule`] for a node that is no
///   constant, no variable at index zero, and no sum, difference or product.
/// - panics: none.
/// - executable: none — the clause speaks of the order of the nodes.
/// - intension: one walk with an explicit stack, and one table of the plan's
///   nodes that answers the place of a node in constant time.
///
/// # Errors
/// - [`SuspendReason::NoRule`]: an operand holds a node with no rule.
///
/// # Adequacy
/// - hypothesis: L3 — operands that share a node, an operand with a cut, and
///   operands of generated polynomials.
/// - witness: `tests::quantifier::each_quantified_form_settles_or_suspends_by_name`
/// - witness: `tests::quantifier::quantified_formulas_settle_to_certificates_that_replay`
fn order(
    plan: &Plan,
    (first, second): (NodeId, NodeId),
) -> Result<(Vec<Visited>, (Place, Place)), SuspendReason>
{
    let mut order: Vec<Visited> = Vec::new();
    let mut place: Vec<Option<usize>> = alloc::vec![None; usize::from(plan.node_count())];
    let placed = |place: &[Option<usize>], id: NodeId| {
        place
            .get(usize::from(id))
            .copied()
            .flatten()
            .map(Place)
            .ok_or(SuspendReason::NoRule)
    };
    let mut work = alloc::vec![Visit::Enter(second), Visit::Enter(first)];
    while let Some(visit) = work.pop() {
        let node = match visit {
            Visit::Enter(node) | Visit::Leave(node) => node,
        };
        let seen = place.get(usize::from(node)).ok_or(SuspendReason::NoRule)?;
        if visit == Visit::Enter(node) && seen.is_some() {
            continue;
        }
        let visited = match (
            visit,
            plan.node(node).map_err(|_unknown| SuspendReason::NoRule)?,
        ) {
            (Visit::Enter(_), &Node::Real(Real::Bound(index))) if index == DeBruijn::default() => {
                Visited {
                    node,
                    reads: Reads::Variable,
                    operands: None,
                }
            },
            (Visit::Enter(_), &Node::Real(Real::Constant(_))) => Visited {
                node,
                reads: Reads::Nothing,
                operands: None,
            },
            (
                Visit::Enter(_),
                &Node::Real(
                    Real::Add(left, right) | Real::Sub(left, right) | Real::Mul(left, right),
                ),
            ) => {
                work.push(Visit::Leave(node));
                work.push(Visit::Enter(right.node()));
                work.push(Visit::Enter(left.node()));
                continue;
            },
            (
                Visit::Leave(_),
                &Node::Real(
                    Real::Add(left, right) | Real::Sub(left, right) | Real::Mul(left, right),
                ),
            ) => {
                let (left, right) = (placed(&place, left.node())?, placed(&place, right.node())?);
                let reads = order
                    .get(left.0)
                    .zip(order.get(right.0))
                    .map(|(first, second)| {
                        if first.reads == Reads::Nothing && second.reads == Reads::Nothing {
                            Reads::Nothing
                        }
                        else {
                            Reads::Variable
                        }
                    })
                    .ok_or(SuspendReason::NoRule)?;
                Visited {
                    node,
                    reads,
                    operands: Some((left, right)),
                }
            },
            (
                Visit::Enter(_) | Visit::Leave(_),
                &(Node::Real(_) | Node::Open(_) | Node::Domain(_)),
            ) => {
                return Err(SuspendReason::NoRule);
            },
        };
        let slot = place
            .get_mut(usize::from(node))
            .ok_or(SuspendReason::NoRule)?;
        *slot = Some(order.len());
        order.push(visited);
    }
    let operands = (placed(&place, first)?, placed(&place, second)?);
    return Ok((order, operands));
}
