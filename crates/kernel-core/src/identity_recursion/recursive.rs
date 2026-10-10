//! Finite observations of the strictly positive code `List A = μX. Unit + A ×
//! X`.
//!
//! Inhabitants reuse the higher field's flat `Codata`: a Guard exposes `inl ()`
//! for Nil or `inr head` for Cons, whose recursive coordinate is the guarded
//! tail edge. A Nil never observes its tail. Redirect consumes work without
//! exposing a constructor. No infinite observation enters native conversion.

use alloc::collections::BTreeSet;
use core::fmt;

use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use super::Clause;
use super::Inhabitation;
use super::Relation;
use super::RelationError;
use super::RelationId;
use super::check_value;
use crate::higher_field::Codata;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::higher_field::HigherId;
use crate::higher_field::Layer;
use crate::replay::ReplayBudget;

#[cfg(test)]
pub(crate) mod tests;
mod transport;

pub use transport::ListEquivalence;
pub use transport::TransportEvidence;

/// Visited Guard and Redirect instructions across both input graphs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Steps(pub u64);

/// The exact observed prefix, including a terminal or distinguishing
/// constructor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Progress
{
    /// Constructors checked on both sides.
    pub depth: Depth,
    /// Instructions visited, including redirects.
    pub steps: Steps,
}

/// A decided finite list fibre; unobserved tails carry no certification.
///
/// # Specification
/// - provides: Unit only after matching constructors reach Nil on both sides;
///   Empty after the first differing constructor or empty element fibre.
/// - ensures: progress names the prefix actually checked, never infinite depth.
///
/// # Adequacy
/// - hypothesis: L3 — equal, differing-head and differing-length observations
///   distinguish a complete identity from a refuting prefix.
/// - witness: `identity_recursion::recursive::tests::list_identity_is_lazy`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ListFiber
{
    /// Inhabitation of the observed recursive relation.
    pub fiber: Inhabitation,
    /// Checked depth and instruction count.
    pub progress: Progress,
}

/// A refusal with the exact completed prefix and charged work.
#[derive(Debug)]
pub struct Refusal
{
    /// Preserve the existing named verdict, including NonProductive/DepthBound.
    pub reason: HigherError,
    /// Progress before the refused observation.
    pub progress: Progress,
}

impl fmt::Display for Refusal
{
    /// Render the verdict together with its finite observation boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} at depth {} after {} steps",
            self.reason, self.progress.depth.0, self.progress.steps.0
        )
    }
}

impl core::error::Error for Refusal
{
}

/// One shared instruction allowance for an entire pairwise observation.
struct Meter
{
    /// The instruction ceiling.
    limit: ReplayBudget,
    /// Observed constructors and charged instructions.
    progress: Progress,
}

impl Meter
{
    /// Start a fresh finite observation.
    ///
    /// # Specification
    /// trivial.
    fn new(limit: ReplayBudget) -> Self
    {
        Self {
            limit,
            progress: Progress {
                depth: Depth(0),
                steps: Steps(0),
            },
        }
    }

    /// Attach current depth and work to a refusal.
    ///
    /// # Specification
    /// trivial.
    fn refuse(
        &self,
        reason: HigherError,
    ) -> Refusal
    {
        Refusal {
            reason,
            progress: self.progress,
        }
    }

    /// Charge an instruction before reading it.
    ///
    /// # Specification
    /// - ensures: one charged instruction, without exceeding the ceiling.
    /// - fails: `DepthBound` at the exact exhausted allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// `DepthBound` with completed progress.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a productive cycle stops at its finite allowance.
    /// - witness: `identity_recursion::recursive::tests::uncertified_stratum_refuses`
    fn charge(&mut self) -> Result<(), Refusal>
    {
        if self.progress.steps.0 == u64::from(self.limit) {
            return Err(self.refuse(HigherError::DepthBound));
        }
        self.progress.steps.0 = self.progress.steps.0.saturating_add(1);
        Ok(())
    }
}

/// An observed constructor; the recursive coordinate stays in the cursor.
#[derive(Clone, Copy)]
enum Constructor
{
    /// The terminal Unit summand.
    Nil,
    /// The head coordinate of the non-terminal product.
    Cons(ValueId),
}

/// A lazy reader with a per-constructor redirect-cycle detector.
struct Cursor<'graph>
{
    /// Borrowed raw graph, never a cached checking verdict.
    graph: &'graph Codata,
    /// Next edge to observe.
    current: HigherId,
    /// Edges followed since the last constructor.
    unguarded: BTreeSet<HigherId>,
}

impl<'graph> Cursor<'graph>
{
    /// Retain the root without traversing the graph.
    ///
    /// # Specification
    /// trivial.
    fn new(graph: &'graph Codata) -> Self
    {
        Self {
            graph,
            current: graph.root,
            unguarded: BTreeSet::new(),
        }
    }

    /// Check precisely the next constructor, leaving its tail untouched.
    ///
    /// # Specification
    /// - ensures: only a typed Unit or element payload advances the cursor.
    /// - fails: `NonProductive` for a redirect cycle, `DepthBound` on
    ///   exhaustion, `UnknownLayer` for a missing observed edge, Relation for
    ///   malformed heads.
    /// - panics: none.
    /// - intension: each graph instruction charges one shared replay unit.
    ///
    /// # Errors
    /// Refusal preserves the higher verdict and the observed depth.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed or looping unobserved tails remain lazy;
    ///   requesting them refuses without claiming inequality.
    /// - witness: `identity_recursion::recursive::tests::uncertified_stratum_refuses`
    fn next(
        &mut self,
        arena: &mut TermArena,
        element: ValueTypeId,
        meter: &mut Meter,
    ) -> Result<Constructor, Refusal>
    {
        loop {
            if self.unguarded.contains(&self.current) {
                return Err(meter.refuse(HigherError::NonProductive(self.current)));
            }
            meter.charge()?;
            let layer = self
                .graph
                .nodes
                .get(self.current.0)
                .ok_or_else(|| meter.refuse(HigherError::UnknownLayer(self.current)))?;
            match *layer {
                | Layer::Redirect(next) => {
                    let _fresh = self.unguarded.insert(self.current);
                    self.current = next;
                },
                | Layer::Guard { evidence, tail } => {
                    let Some(&Value::Injection(side, payload)) = arena.value(evidence)
                    else {
                        return Err(meter.refuse(HigherError::Relation(RelationError::Evidence)));
                    };
                    let ty = match side {
                        | Side::Left => arena.value_type_unit(),
                        | Side::Right => element,
                    };
                    check_value(arena, &[], payload, ty)
                        .map_err(|error| meter.refuse(HigherError::Relation(error)))?;
                    self.current = tail;
                    self.unguarded.clear();
                    return Ok(match side {
                        | Side::Left => Constructor::Nil,
                        | Side::Right => Constructor::Cons(payload),
                    });
                },
            }
        }
    }
}

impl Relation
{
    /// Select the element clause already built by the single code fold.
    ///
    /// # Specification
    /// - ensures: no second interpretation or comparison of native types.
    /// - fails: Classifier outside List.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Classifier` or Arena.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — only the recursive clause supplies list observations.
    /// - witness: `identity_recursion::recursive::tests::list_identity_is_lazy`
    fn list_element(&self) -> Result<RelationId, RelationError>
    {
        match self.node(self.root)?.clause {
            | Clause::List(element) => Ok(element),
            | _ => Err(RelationError::Classifier),
        }
    }

    /// Observe a List relation one constructor at a time under a replay budget.
    ///
    /// # Specification
    /// - requires: arena roots remain live, without address reuse.
    /// - ensures: Unit exactly when both finite spines reach Nil with inhabited
    ///   head fibres; Empty at the first differing constructor or head fibre.
    ///   Neither result asserts typing or productivity of an unobserved tail.
    /// - fails: named higher/element refusals with completed depth; exhaustion
    ///   and non-productivity never become Empty or Unit.
    /// - panics: none.
    /// - intension: two Guard instructions per compared constructor, plus every
    ///   visited Redirect; the element fold's finite structural work is
    ///   separate.
    ///
    /// # Errors
    /// Refusal with the existing higher verdict and exact progress.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal lists, head and length mismatches, dead tails,
    ///   direct and delayed loops, and exact allowance boundaries separate
    ///   finite decision from productivity and infinite certification.
    /// - witness: `identity_recursion::recursive::tests::list_identity_is_lazy`
    /// - witness: `identity_recursion::recursive::tests::uncertified_stratum_refuses`
    #[inline]
    pub fn observe_lists(
        &self,
        arena: &mut TermArena,
        left: &Codata,
        right: &Codata,
        budget: ReplayBudget,
    ) -> Result<ListFiber, Refusal>
    {
        let mut meter = Meter::new(budget);
        let element = self
            .list_element()
            .map_err(|error| meter.refuse(error.into()))?;
        let node = self
            .node(element)
            .map_err(|error| meter.refuse(error.into()))?;
        let mut left = Cursor::new(left);
        let mut right = Cursor::new(right);
        loop {
            let first = left.next(arena, node.source, &mut meter)?;
            let second = right.next(arena, node.target, &mut meter)?;
            meter.progress.depth.0 = meter.progress.depth.0.saturating_add(1);
            let fiber = match (first, second) {
                | (Constructor::Nil, Constructor::Nil) => Inhabitation::Unit,
                | (Constructor::Cons(a), Constructor::Cons(b)) => {
                    let fiber = self
                        .fiber_at(arena, element, &[], a, b)
                        .map_err(|error| meter.refuse(error.into()))?;
                    match fiber.inhabitant(arena) {
                        | Ok(_) => continue,
                        | Err(RelationError::Evidence) => Inhabitation::Empty,
                        | Err(error) => return Err(meter.refuse(error.into())),
                    }
                },
                | _ => Inhabitation::Empty,
            };
            return Ok(ListFiber {
                fiber,
                progress: meter.progress,
            });
        }
    }
}
