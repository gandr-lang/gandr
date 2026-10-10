//! Memoized, iterative resolution over the finalized document DAG.
//!
//! Resolution owns the frontier, taint, plan-retention, and render-meter
//! accounting because those representations are inseparable. The work machine
//! below uses one explicit vector and never calls itself.
//!
//! A state is a node entered at a column under an indentation. An in-bound
//! state — column and indentation both within the computation width — is
//! memoized and answers a Pareto frontier of measures, sorted by cost, none
//! dominated in cost and ending column. An out-of-bound state is not entered:
//! it answers a deferred promise carrying its exact context, which is forced
//! only when nothing in-bound competes with it. The memo table is an ordered
//! map, bounded by the memo-state ceiling charged before each insertion.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::arena::DocArena;
use crate::arena::DocHandleStatus;
use crate::arena::DocId;
use crate::arena::DocNode;
use crate::arena::NodeId;
use crate::arena::TextId;
use crate::arena::VerbatimId;
use crate::error::RenderAllocationSite;
use crate::error::RenderArithmetic;
use crate::error::RenderError;
use crate::error::RenderInvariant;
use crate::limits::RenderMeter;
use crate::measure::LayoutCost;
use crate::measure::LayoutOptions;
use crate::measure::Measure;
use crate::measure::WidthTaint;
use crate::measure::absolute_overflow;
use crate::measure::add_cost;
use crate::measure::add_output_bytes;
use crate::measure::incoming_overflow;
use crate::measure::line_cost;
use crate::plan::PlanArena;
use crate::plan::PlanId;
use crate::plan::PlanNode;
use crate::plan::Released;
use crate::taint::MeasureSet;
use crate::taint::TaintPromise;
use crate::taint::deferred;
use crate::taint::first;
use crate::taint::merge;
use crate::taint::taint;
use crate::units::Column;
use crate::units::Indentation;
use crate::units::LineBreaks;
use crate::units::OutputBytes;
use crate::units::PeakResolverStack;
use crate::units::SquaredOverflow;

/// The public summary of one winning layout.
///
/// # Specification
/// - requires: the result came from [`resolve`] and its plan store remains
///   owned by this value.
/// - ensures: cost, taint, output bytes, and plan identity describe one winner.
/// - provides: the observable resolution surface.
/// - panics: none.
/// - executable: none — this owned summary is a data carrier; resolution and
///   rendering construct and consume its coherent plan and metadata.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[derive(Debug)]
pub struct Resolved
{
    /// The retained plan arena.
    plans: PlanArena,
    /// The selected winning plan identity.
    plan: PlanId,
    /// The selected plan's cost.
    cost: LayoutCost,
    /// Whether the root required a taint promise.
    width_taint: WidthTaint,
    /// Exact bytes the winning plan emits.
    output_bytes: OutputBytes,
}

impl Resolved
{
    /// Returns the winning plan identity.
    ///
    /// # Specification
    /// - requires: this result remains alive.
    /// - ensures: the identity remains valid in this result's retained arena.
    /// - provides: the handoff to the render machine.
    /// - panics: none.
    /// - executable: none — `PlanId` hides its slot and generation in the plan
    ///   module and exposes no const value observer; derived equality produces
    ///   E0015 here. A const identity observer in that module is the missing
    ///   API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[inline]
    #[must_use]
    pub const fn plan(&self) -> PlanId
    {
        self.plan
    }

    /// Borrows the retained plan arena for the render machine.
    ///
    /// # Specification
    /// - requires: this result remains alive.
    /// - ensures: every returned plan identity is validated against this arena.
    /// - provides: read-only plan-node access without copying the arena.
    /// - panics: none.
    /// - executable: none — the borrowed arena has no const identity observer;
    ///   `core::ptr::eq` produces E0015, and its private stores cannot be
    ///   inspected here. Runtime consumers check this borrow against the
    ///   selected plan.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[inline]
    pub(crate) const fn plan_arena(&self) -> &PlanArena
    {
        &self.plans
    }

    /// Returns the winning lexicographic cost.
    ///
    /// # Specification
    /// - requires: this result came from successful resolution.
    /// - ensures: the cost is the direct projection of the selected measure.
    /// - provides: observable optimality metadata.
    /// - panics: none.
    /// - executable: none — the cost components are opaque quantity types with
    ///   no const numeric observers; their derived equality produces E0015.
    ///   Const quantity projections are the missing API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[inline]
    #[must_use]
    pub const fn cost(&self) -> LayoutCost
    {
        self.cost
    }

    /// Returns whether width taint was required.
    ///
    /// # Specification
    /// - requires: this result came from successful resolution.
    /// - ensures: taint is reported without truncating output.
    /// - provides: the root theorem-status projection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        ensures: |ret| matches!((ret, self.width_taint), (WidthTaint::Untainted, WidthTaint::Untainted) | (WidthTaint::Tainted, WidthTaint::Tainted))
    )]
    #[inline]
    #[must_use]
    pub const fn width_taint(&self) -> WidthTaint
    {
        self.width_taint
    }

    /// Returns the exact selected output byte count.
    ///
    /// # Specification
    /// - requires: this result came from successful resolution.
    /// - ensures: the count includes stored bytes and layout-owned endings.
    /// - provides: the size the render machine reserves once.
    /// - panics: none.
    /// - executable: none — `OutputBytes` hides its integer in the units module
    ///   and exposes no const numeric observer; derived equality produces
    ///   E0015. A const numeric projection is the missing API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[inline]
    #[must_use]
    pub const fn output_bytes(&self) -> OutputBytes
    {
        self.output_bytes
    }
}

/// Evaluation mode for one document context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolutionMode
{
    /// Use and populate the in-bound memo table.
    Memoized,
    /// Evaluate the exact tainted context without memoization.
    Forced,
}

/// Selects the phase that charges the selected output bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputAccounting
{
    /// Charge the selected measure while resolving.
    AtResolve,
    /// Charge each concrete append while executing the render machine.
    AtAppend,
}

/// Strict Pareto dominance result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Dominance
{
    /// The left measure strictly dominates the right measure.
    Strict,
    /// The left measure does not strictly dominate the right measure.
    None,
}

/// What one machine step left for the loop: a finished result for the
/// continuation on top of the work stack, or nothing because the step pushed
/// work of its own.
///
/// # Specification
/// - requires: the value comes from an enter or resume operation.
/// - ensures: a result owns its measure set; a scheduled step has put its
///   continuation and child work on the resolver stack.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary; enter,
///   resume, retention and release operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[derive(Debug)]
enum Step
{
    /// A finished measure set.
    Result(MeasureSet),
    /// The step pushed its continuation and children.
    Scheduled,
}

/// Memoization key for one in-bound context.
///
/// # Specification
/// - requires: the fields describe one finalized document context.
/// - ensures: node, incoming column and indentation all participate in memo
///   identity and ordering.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary; enter,
///   resume, retention and release operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct MemoKey
{
    /// Finalized document node.
    node: NodeId,
    /// Incoming output column.
    column: Column,
    /// Active indentation.
    indentation: Indentation,
}

/// Continuation state for one left measure in concatenation.
///
/// # Specification
/// - requires: each retained measure owns its plan reference.
/// - ensures: the active left measure, remaining left frontier, accumulated
///   products and right context remain distinct across suspension.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary; enter,
///   resume, retention and release operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[derive(Debug)]
struct ConcatState
{
    /// Right document node to evaluate.
    right: NodeId,
    /// Indentation passed to the right child.
    indentation: Indentation,
    /// Whether deferred children must be forced.
    force: ResolutionMode,
    /// Current left-side measure.
    left: Measure,
    /// Remaining left-side frontier measures.
    remaining: Vec<Measure>,
    /// Products accumulated from completed right evaluations.
    results: Vec<Measure>,
    /// Whether any product came from a tainted state.
    taint: WidthTaint,
}

/// One explicit resolver work entry.
///
/// # Specification
/// - requires: the work belongs to one resolver invocation.
/// - ensures: each variant carries the context or owned state required by its
///   enter, resume or release transition.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary; enter,
///   resume, retention and release operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[derive(Debug)]
enum WorkItem
{
    /// Enter one document state.
    Eval
    {
        /// Document node to enter.
        node: NodeId,
        /// Incoming output column.
        column: Column,
        /// Active indentation.
        indentation: Indentation,
        /// Whether this state bypasses memoization.
        force: ResolutionMode,
    },
    /// Store the completed in-bound state.
    StoreMemo
    {
        /// Memoization key for the completed state.
        key: MemoKey,
    },
    /// Release one plan reference and any newly unreachable children.
    ReleasePlan
    {
        /// Plan identity whose reference is released.
        plan: PlanId,
    },
    /// Resume a single-child nesting operation.
    AfterNest,
    /// Resume a single-child alignment operation.
    AfterAlign,
    /// Resume a flattened-image operation.
    AfterFlatten,
    /// Resume the left branch of a choice.
    AfterChoiceLeft
    {
        /// Right branch to evaluate next.
        right: NodeId,
        /// Incoming output column.
        column: Column,
        /// Active indentation.
        indentation: Indentation,
        /// Whether the right state bypasses memoization.
        force: ResolutionMode,
    },
    /// Resume the right branch of a choice.
    AfterChoiceRight
    {
        /// Completed left branch result.
        left: MeasureSet,
    },
    /// Resume the left branch of a concatenation.
    AfterConcatLeft
    {
        /// Right branch to evaluate next.
        right: NodeId,
        /// Active indentation.
        indentation: Indentation,
        /// Whether the right state bypasses memoization.
        force: ResolutionMode,
    },
    /// Force an exact deferred left concatenation state.
    ForceConcatLeft
    {
        /// Right branch to evaluate next.
        right: NodeId,
        /// Active indentation.
        indentation: Indentation,
        /// Whether the right state bypasses memoization.
        force: ResolutionMode,
    },
    /// Resume one right-side concatenation state.
    ConcatNext(ConcatState),
    /// Force an exact deferred right-side state.
    ForceConcatRight(ConcatState),
}

/// The iterative resolver and its one private work vector.
///
/// # Specification
/// - requires: the document arena is finalized and the meter belongs to this
///   invocation.
/// - ensures: memo keys preserve exact contexts; work and plan ownership are
///   managed by the same metered state machine.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary; enter,
///   resume, retention and release operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
struct Resolver<'arena, 'meter>
{
    /// Finalized document arena being resolved.
    arena: &'arena DocArena,
    /// Constant width and ending policy for this invocation.
    options: LayoutOptions,
    /// Shared render budget meter.
    meter: &'meter mut RenderMeter,
    /// Generational plan store.
    plans: PlanArena,
    /// In-bound memoized measure sets.
    memo: BTreeMap<MemoKey, MeasureSet>,
    /// One explicit enter/resume work vector.
    work: Vec<WorkItem>,
}

/// The error an internal invariant reports when it does not hold.
///
/// # Specification
/// trivial.
const fn broken(invariant: RenderInvariant) -> RenderError
{
    RenderError::Invariant { invariant }
}

impl<'arena, 'meter> Resolver<'arena, 'meter>
{
    /// Creates a resolver with empty memo, plan, and work stores.
    ///
    /// # Specification
    /// - requires: the document arena and meter remain borrowed for this
    ///   resolver.
    /// - ensures: the resolver preserves the arena, options and meter and
    ///   begins with empty memo and work stores.
    /// - provides: one isolated resolution state.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: meter_identity = &raw const *meter,
        ensures: |ret| core::ptr::eq(&raw const *ret.arena, &raw const *arena)
                && core::ptr::eq(&raw const *ret.meter, meter_identity)
                && ret.options == options
                && ret.memo.is_empty()
                && ret.work.is_empty()
    )]
    fn new(
        arena: &'arena DocArena,
        options: LayoutOptions,
        meter: &'meter mut RenderMeter,
    ) -> Self
    {
        Self {
            arena,
            options,
            meter,
            plans: PlanArena::new(),
            memo: BTreeMap::new(),
            work: Vec::new(),
        }
    }

    /// Pushes one work item through the shared cumulative and peak checks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cumulative work count and the peak depth are charged
    ///   before the vector grows.
    /// - provides: the only way work enters the machine.
    /// - fails: a work or depth ceiling, a depth that cannot be counted, or a
    ///   vector that cannot grow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::LimitExceeded`] at a resolver ceiling,
    /// [`RenderError::ArithmeticOverflow`] for an uncountable depth, and
    /// [`RenderError::AllocationFailed`] when the vector cannot grow.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.work.len(), self.meter.usage(), core::mem::discriminant(&item)),
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.work.len() == before.0,
            |&()| before.0.checked_add(1) == Some(self.work.len())
                && self.work.last().map(core::mem::discriminant) == Some(before.2)
                && u64::from(before.1.resolver_work_entries).checked_add(1) == Some(u64::from(self.meter.usage().resolver_work_entries))
                && u64::try_from(self.work.len()).is_ok_and(|depth| u64::from(self.meter.usage().peak_resolver_stack) == u64::from(before.1.peak_resolver_stack).max(depth)))
    )]
    fn push(
        &mut self,
        item: WorkItem,
    ) -> Result<(), RenderError>
    {
        let depth = u64::try_from(self.work.len())
            .ok()
            .and_then(|depth| depth.checked_add(1u64))
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::StackDepth,
            })?;
        self.meter
            .push_resolver_work(PeakResolverStack::from(depth))?;
        self.work
            .try_reserve(1usize)
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::ResolverStack,
            })?;
        self.work.push(item);
        Ok(())
    }

    /// Retains every plan owned by a copied measure set.
    ///
    /// # Specification
    /// - requires: every plan `set` names is live.
    /// - ensures: each plan gains exactly one reference.
    /// - provides: the retention a memo copy needs.
    /// - fails: a plan that is not live, or a count that cannot advance.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error [`PlanArena::retain`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    /// - witness: `resolve::tests::retained_aliases_release_without_consuming_pending_continuations`
    #[anodized::spec(
        captures: before = (self.meter.usage(), self.work.len(), self.memo.len()),
        ensures: |ret| self.meter.usage() == before.0
                && self.work.len() == before.1
                && self.memo.len() == before.2
                && ret.as_ref().map_or(true,
            |&()| match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(TaintPromise::Ready(measure)) => matches!(self.plans.get(measure.plan), Maybe::Present(_)), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => true })
    )]
    fn retain_set(
        &mut self,
        set: &MeasureSet,
    ) -> Result<(), RenderError>
    {
        match *set {
            | MeasureSet::Frontier(ref frontier) => {
                for measure in frontier {
                    self.plans.retain(measure.plan)?;
                }
            },
            | MeasureSet::Tainted(TaintPromise::Ready(measure)) => {
                self.plans.retain(measure.plan)?;
            },
            | MeasureSet::Tainted(TaintPromise::Deferred { .. }) => {},
        }
        Ok(())
    }

    /// Releases every plan reference owned by a measure set.
    ///
    /// # Specification
    /// - requires: `set` owns one reference to each plan it names.
    /// - ensures: each reference is released, children freed in turn.
    /// - provides: the release of a consumed set.
    /// - fails: as [`Self::release_plan`].
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error [`Self::release_plan`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    /// - witness: `resolve::tests::retained_aliases_release_without_consuming_pending_continuations`
    #[anodized::spec(
        captures: before = (match set { MeasureSet::Frontier(ref frontier) => frontier.len(), MeasureSet::Tainted(TaintPromise::Ready(_)) => 1, MeasureSet::Tainted(TaintPromise::Deferred { .. }) => 0 }, self.work.len(), self.work.iter().rposition(|item| !matches!(*item, WorkItem::ReleasePlan { .. })).map_or(0,
            |index| index.saturating_add(1)), self.meter.usage()),
        ensures: |ret| if before.0 == 0 { ret.is_ok()
                && self.work.len() == before.1
                && self.meter.usage() == before.3 }
            else { ret.as_ref().map_or(true,
            |&()| self.work.len() == before.2
                && u64::try_from(before.0).ok().and_then(|count| u64::from(before.3.resolver_work_entries).checked_add(count)).is_some_and(|minimum| u64::from(self.meter.usage().resolver_work_entries) >= minimum)) }
    )]
    fn release_set(
        &mut self,
        set: MeasureSet,
    ) -> Result<(), RenderError>
    {
        match set {
            | MeasureSet::Frontier(frontier) => {
                for measure in frontier {
                    self.release_plan(measure.plan)?;
                }
            },
            | MeasureSet::Tainted(TaintPromise::Ready(measure)) => {
                self.release_plan(measure.plan)?;
            },
            | MeasureSet::Tainted(TaintPromise::Deferred { .. }) => {},
        }
        Ok(())
    }

    /// Drains plan-release records on the resolver's shared work vector.
    ///
    /// # Specification
    /// - requires: `plan` is live and its reference is the caller's.
    /// - ensures: every node the release leaves unreferenced is freed, its
    ///   children pushed as release records on the metered work vector.
    /// - provides: release without a second, unmetered stack.
    /// - fails: a plan that is not live, or a work ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error [`Self::push`] or [`PlanArena::release_one`]
    /// returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    /// - witness: `resolve::tests::retained_aliases_release_without_consuming_pending_continuations`
    #[anodized::spec(
        captures: before = (self.work.iter().rposition(|item| !matches!(*item, WorkItem::ReleasePlan { .. })).map_or(0,
            |index| index.saturating_add(1)), self.meter.usage().resolver_work_entries, self.plans.get(plan)),
        ensures: |ret| ret.as_ref().map_or(true,
            |&()| matches!(before.2, Maybe::Present(_))
                && self.work.len() == before.0
                && u64::from(before.1).checked_add(1).is_some_and(|minimum| u64::from(self.meter.usage().resolver_work_entries) >= minimum)
                && (self.plans.get(plan) == before.2 || self.plans.get(plan) == Maybe::Absent(crate::plan::lookup::Absent::Released)))
    )]
    fn release_plan(
        &mut self,
        plan: PlanId,
    ) -> Result<(), RenderError>
    {
        self.push(WorkItem::ReleasePlan { plan })?;
        while matches!(self.work.last(), Some(&WorkItem::ReleasePlan { .. })) {
            let Some(WorkItem::ReleasePlan { plan }) = self.work.pop()
            else {
                break;
            };
            if let Released::FreedSequence { left, right } =
                self.plans.release_one(plan, self.meter)?
            {
                self.push(WorkItem::ReleasePlan { plan: right })?;
                self.push(WorkItem::ReleasePlan { plan: left })?;
            }
        }
        Ok(())
    }

    /// Releases a ready promise whose owning set has been discarded.
    ///
    /// # Specification
    /// - requires: a ready promise owns one reference to its plan.
    /// - ensures: that reference is released; a deferred promise owns nothing.
    /// - provides: the release callback of a merge.
    /// - fails: as [`Self::release_plan`].
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error [`Self::release_plan`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.work.len(), self.work.iter().rposition(|item| !matches!(*item, WorkItem::ReleasePlan { .. })).map_or(0,
            |index| index.saturating_add(1)), self.meter.usage()),
        ensures: |ret| match promise { TaintPromise::Deferred { .. } => ret.is_ok()
                && self.work.len() == before.0
                && self.meter.usage() == before.2, TaintPromise::Ready(_) => ret.as_ref().map_or(true,
            |&()| self.work.len() == before.1
                && u64::from(before.2.resolver_work_entries).checked_add(1).is_some_and(|minimum| u64::from(self.meter.usage().resolver_work_entries) >= minimum)) }
    )]
    fn release_promise(
        &mut self,
        promise: TaintPromise,
    ) -> Result<(), RenderError>
    {
        if let TaintPromise::Ready(measure) = promise {
            self.release_plan(measure.plan)?;
        }
        Ok(())
    }

    /// Keeps only the least-cost measure while releasing discarded plans.
    ///
    /// # Specification
    /// - requires: `set` owns its plans.
    /// - ensures: as [`taint`], each discarded measure's plan released.
    /// - provides: taint over the resolver's own plans.
    /// - fails: as [`Self::release_plan`].
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error a release returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = match set { MeasureSet::Frontier(ref frontier) => (frontier.first().copied().map(TaintPromise::Ready), frontier.len() > 1), MeasureSet::Tainted(promise) => (Some(promise), false) },
    ensures: |ret| ret.as_ref().map_or_else(|_error| before.1,
        |set| match *set { MeasureSet::Frontier(ref frontier) => before.0.is_none()

                && frontier.is_empty(), MeasureSet::Tainted(promise) => before.0 == Some(promise) })
    )]
    fn taint_set(
        &mut self,
        set: MeasureSet,
    ) -> Result<MeasureSet, RenderError>
    {
        taint(set, |measure| self.release_plan(measure.plan))
    }

    /// Merges choices while releasing tainted plans discarded by the bias.
    ///
    /// # Specification
    /// - requires: both sets own their plans.
    /// - ensures: as [`merge`], each discarded promise's plan released.
    /// - provides: the choice merge over the resolver's own plans.
    /// - fails: a frontier that cannot grow, or a release error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::AllocationFailed`] or the first release error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (match left { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }, match right { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }),
    ensures: |ret| ret.as_ref().map_or_else(|error| before.0.3.is_some() || before.1.3.is_some() || *error == RenderError::AllocationFailed { site: crate::error::RenderAllocationSite::Frontier },
        |set| match (before.0.3, before.1.3) { (None, None) => matches!(*set, MeasureSet::Frontier(ref frontier) if before.0.0.checked_add(before.1.0) == Some(frontier.len())

                && (before.0.0 == 0 || (frontier.first() == before.0.1.as_ref()

                && frontier.get(before.0.0.saturating_sub(1)) == before.0.2.as_ref()))

                && (before.1.0 == 0 || (frontier.get(before.0.0) == before.1.1.as_ref()

                && frontier.last() == before.1.2.as_ref()))), (None, Some(_)) => matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == before.0.0

                && frontier.first() == before.0.1.as_ref()

                && frontier.last() == before.0.2.as_ref()), (Some(_), None) => matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == before.1.0

                && frontier.first() == before.1.1.as_ref()

                && frontier.last() == before.1.2.as_ref()), (Some(left), Some(_)) => matches!(*set, MeasureSet::Tainted(actual) if left == actual) })
    )]
    fn merge_sets(
        &mut self,
        left: MeasureSet,
        right: MeasureSet,
    ) -> Result<MeasureSet, RenderError>
    {
        merge(left, right, |promise| self.release_promise(promise))
    }

    /// Runs the work machine from one root context.
    ///
    /// # Specification
    /// - requires: `root` names a node of the arena.
    /// - ensures: the root's least measure, its taint, and the plan arena that
    ///   retains it; a deferred root is forced rather than returned; every memo
    ///   entry's plans are released before return.
    /// - provides: the machine every resolution runs.
    /// - fails: any error a step returns, or an invariant the machine finds
    ///   broken.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] a step returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: bound = self.options.computation_width,
        ensures: |ret| ret.as_ref().map_or(true,
            |winner| matches!(winner.2.get(winner.0.plan), Maybe::Present(_))
                && (winner.1 == WidthTaint::Tainted || u32::from(winner.0.last_column) <= u32::from(bound)))
    )]
    fn run(
        mut self,
        root: NodeId,
    ) -> Result<(Measure, WidthTaint, PlanArena), RenderError>
    {
        self.push(WorkItem::Eval {
            node: root,
            column: Column::from(0u32),
            indentation: Indentation::from(0u32),
            force: ResolutionMode::Memoized,
        })?;
        let mut pending = Step::Scheduled;
        loop {
            if let Step::Result(set) = core::mem::replace(&mut pending, Step::Scheduled) {
                if let Some(item) = self.work.pop() {
                    pending = self.resume(item, set)?;
                    continue;
                }
                if let MeasureSet::Tainted(TaintPromise::Deferred {
                    doc,
                    column,
                    indentation,
                }) = set
                {
                    self.push(WorkItem::Eval {
                        node: doc,
                        column,
                        indentation,
                        force: ResolutionMode::Forced,
                    })?;
                    continue;
                }
                return self.finish(&set);
            }
            let Some(item) = self.work.pop()
            else {
                return Err(broken(RenderInvariant::Continuation));
            };
            pending = match item {
                | WorkItem::ReleasePlan { plan } => {
                    self.release_plan(plan)?;
                    Step::Scheduled
                },
                | WorkItem::Eval {
                    node,
                    column,
                    indentation,
                    force,
                } => self.begin_eval(node, column, indentation, force)?,
                | WorkItem::StoreMemo { .. }
                | WorkItem::AfterNest
                | WorkItem::AfterAlign
                | WorkItem::AfterFlatten
                | WorkItem::AfterChoiceLeft { .. }
                | WorkItem::AfterChoiceRight { .. }
                | WorkItem::AfterConcatLeft { .. }
                | WorkItem::ForceConcatLeft { .. }
                | WorkItem::ConcatNext(_)
                | WorkItem::ForceConcatRight(_) => {
                    return Err(broken(RenderInvariant::Continuation));
                },
            };
        }
    }

    /// The root's answer, once the work stack is empty.
    ///
    /// # Specification
    /// - requires: the work stack is empty and `set` is the root's result, not
    ///   a deferred promise.
    /// - ensures: the least measure with its taint, every memo entry released
    ///   first.
    /// - provides: the end of [`Self::run`].
    /// - fails: a set with no measure, or a release error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for a set offering no measure, and
    /// the first release error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (first(set), matches!(*set, MeasureSet::Tainted(_))),
        ensures: |ret| match before.0 { Maybe::Absent(_) => matches!(ret, Err(RenderError::Invariant { invariant: RenderInvariant::MissingMeasure })), Maybe::Present(expected) => ret.as_ref().map_or(true,
            |winner| winner.0 == expected
                && (winner.1 == WidthTaint::Tainted) == before.1
                && matches!(winner.2.get(winner.0.plan), Maybe::Present(_))) }
    )]
    fn finish(
        mut self,
        set: &MeasureSet,
    ) -> Result<(Measure, WidthTaint, PlanArena), RenderError>
    {
        let taint = match *set {
            | MeasureSet::Tainted(_) => WidthTaint::Tainted,
            | MeasureSet::Frontier(_) => WidthTaint::Untainted,
        };
        let Maybe::Present(measure) = first(set)
        else {
            return Err(broken(RenderInvariant::MissingMeasure));
        };
        let memo = core::mem::take(&mut self.memo);
        for (_key, memo_set) in memo {
            self.release_set(memo_set)?;
        }
        Ok((measure, taint, self.plans))
    }

    /// Hands a finished result to the continuation popped for it.
    ///
    /// # Specification
    /// - requires: `item` was on top of the work stack when `set` finished.
    /// - ensures: the continuation's next step: a result for the continuation
    ///   below it, or work pushed.
    /// - provides: the resume half of the machine.
    /// - fails: any error the continuation's step returns, or an `Eval` entry
    ///   where a continuation belongs.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the step returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.work.len(), matches!(item, WorkItem::StoreMemo { .. } | WorkItem::ReleasePlan { .. } | WorkItem::AfterNest | WorkItem::AfterAlign | WorkItem::AfterFlatten), match set { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }, matches!(item, WorkItem::Eval { .. })),
        ensures: |ret| if before.3 { matches!(ret, Err(RenderError::Invariant { invariant: RenderInvariant::Continuation })) }
            else { ret.as_ref().map_or(true,
            |step| match *step { Step::Scheduled => before.0.checked_add(2) == Some(self.work.len())
                && self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { .. })), Step::Result(ref set) => self.work.len() <= before.0
                && (match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(TaintPromise::Ready(measure)) => matches!(self.plans.get(measure.plan), Maybe::Present(_)), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => true })
                && if before.1 { (match *set { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }) == before.2 }
            else { match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().zip(frontier.iter().skip(1)).all(|(left, right)| left.cost < right.cost
                && left.last_column > right.last_column)
                && frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(_) => true } } }) }
    )]
    fn resume(
        &mut self,
        item: WorkItem,
        set: MeasureSet,
    ) -> Result<Step, RenderError>
    {
        match item {
            | WorkItem::StoreMemo { key } => {
                self.retain_set(&set)?;
                let _previous = self.memo.insert(key, set.clone());
                Ok(Step::Result(set))
            },
            | WorkItem::ReleasePlan { plan } => {
                self.release_plan(plan)?;
                Ok(Step::Result(set))
            },
            | WorkItem::AfterNest | WorkItem::AfterAlign | WorkItem::AfterFlatten => {
                Ok(Step::Result(set))
            },
            | WorkItem::AfterChoiceLeft {
                right,
                column,
                indentation,
                force,
            } => {
                self.push(WorkItem::AfterChoiceRight { left: set })?;
                self.push(WorkItem::Eval {
                    node: right,
                    column,
                    indentation,
                    force,
                })?;
                Ok(Step::Scheduled)
            },
            | WorkItem::AfterChoiceRight { left } => {
                let combined = self.merge_sets(left, set)?;
                Ok(Step::Result(self.normalize_set(combined)?))
            },
            | WorkItem::AfterConcatLeft {
                right,
                indentation,
                force,
            } => {
                if let MeasureSet::Tainted(TaintPromise::Deferred {
                    doc,
                    column,
                    indentation: deferred_indentation,
                }) = set
                {
                    self.push(WorkItem::ForceConcatLeft {
                        right,
                        indentation,
                        force,
                    })?;
                    self.push(WorkItem::Eval {
                        node: doc,
                        column,
                        indentation: deferred_indentation,
                        force: ResolutionMode::Forced,
                    })?;
                }
                else {
                    self.start_concat(right, indentation, force, set)?;
                }
                Ok(Step::Scheduled)
            },
            | WorkItem::ForceConcatLeft {
                right,
                indentation,
                force,
            } => {
                self.start_concat(right, indentation, force, set)?;
                Ok(Step::Scheduled)
            },
            | WorkItem::ConcatNext(state) | WorkItem::ForceConcatRight(state) => {
                self.resume_concat(state, set)
            },
            | WorkItem::Eval { .. } => Err(broken(RenderInvariant::Continuation)),
        }
    }

    /// Starts one state, either returning a leaf result or pushing its
    /// continuation and child states.
    ///
    /// # Specification
    /// - requires: `node` names a node of the arena.
    /// - ensures: an out-of-bound memoized state answers a deferred promise
    ///   carrying exactly `node`, `column` and `indentation`; a memoized state
    ///   seen before answers its memo entry, retained; otherwise a leaf answers
    ///   its measure and an inner node pushes its continuation and children.
    /// - provides: the enter half of the machine.
    /// - fails: a layout or memo ceiling, a node the arena does not hold, an
    ///   indentation that cannot advance, or a push error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the step meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.meter.usage(), self.work.len(), self.memo.len(), self.memo.get(&MemoKey { node, column, indentation }).map(|set| match *set { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) })),
        ensures: |ret| ret.as_ref().map_or(true,
            |step| { if u64::from(before.0.layout_steps).checked_add(1) != Some(u64::from(self.meter.usage().layout_steps)) || self.memo.len() != before.2 { return false }
        if force == ResolutionMode::Memoized

                && (u32::from(column) > u32::from(self.options.computation_width) || u32::from(indentation) > u32::from(self.options.computation_width)) { return self.work.len() == before.1

                && self.meter.usage().memo_states == before.0.memo_states

                && matches!(*step, Step::Result(MeasureSet::Tainted(TaintPromise::Deferred { doc, column: actual_column, indentation: actual_indentation })) if doc == node

                && actual_column == column

                && actual_indentation == indentation) }
        if force == ResolutionMode::Memoized

                && before.3.is_some() { return self.work.len() == before.1

                && self.meter.usage().memo_states == before.0.memo_states

                && matches!(*step, Step::Result(ref set) if Some(match *set { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }) == before.3

                && (match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(TaintPromise::Ready(measure)) => matches!(self.plans.get(measure.plan), Maybe::Present(_)), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => true })) } let memo_work = usize::from(force == ResolutionMode::Memoized);
            if u64::from(before.0.memo_states).checked_add(u64::from(force == ResolutionMode::Memoized)) != Some(u64::from(self.meter.usage().memo_states)) { return false } match *step { Step::Scheduled => before.1.checked_add(memo_work).and_then(|depth| depth.checked_add(2)) == Some(self.work.len())

                && (match self.arena.node(node) { Maybe::Present(DocNode::Nest { amount, doc }) => u32::from(indentation).checked_add(amount).is_some_and(|raised| self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == doc

                && actual_column == column

                && actual_indentation == Indentation::from(raised)

                && actual_force == force))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::AfterNest))), Maybe::Present(DocNode::Align { doc }) => self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == doc

                && actual_column == column

                && actual_indentation == Indentation::from(u32::from(column))

                && actual_force == force))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::AfterAlign)), Maybe::Present(DocNode::Flatten { .. }) => match self.arena.flattened_node(node) { Maybe::Present(image) => self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == image

                && actual_column == column

                && actual_indentation == indentation

                && actual_force == force))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::AfterFlatten)), Maybe::Absent(_) => false }, Maybe::Present(DocNode::Choice { left, right }) => self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == left

                && actual_column == column

                && actual_indentation == indentation

                && actual_force == force))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::AfterChoiceLeft { right: actual_right, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_right == right

                && actual_column == column

                && actual_indentation == indentation

                && actual_force == force)), Maybe::Present(DocNode::Concat { left, right }) => self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == left

                && actual_column == column

                && actual_indentation == indentation

                && actual_force == force))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::AfterConcatLeft { right: actual_right, indentation: actual_indentation, force: actual_force }
        if actual_right == right

                && actual_indentation == indentation

                && actual_force == force)), _ => false }), Step::Result(ref set) => before.1.checked_add(memo_work) == Some(self.work.len())

                && matches!(self.arena.node(node), Maybe::Present(DocNode::Empty | DocNode::Text(_) | DocNode::Verbatim(_) | DocNode::Line | DocNode::HardLine))

                && (match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(TaintPromise::Ready(measure)) => matches!(self.plans.get(measure.plan), Maybe::Present(_)), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => true }) } })
    )]
    fn begin_eval(
        &mut self,
        node: NodeId,
        column: Column,
        indentation: Indentation,
        force: ResolutionMode,
    ) -> Result<Step, RenderError>
    {
        self.meter.charge_layout_step()?;
        let bound = u32::from(self.options.computation_width);
        if force == ResolutionMode::Memoized
            && (u32::from(column) > bound || u32::from(indentation) > bound)
        {
            return Ok(Step::Result(deferred(node, column, indentation)));
        }
        if force == ResolutionMode::Memoized {
            let key = MemoKey {
                node,
                column,
                indentation,
            };
            if let Some(result) = self.memo.get(&key).cloned() {
                self.retain_set(&result)?;
                return Ok(Step::Result(result));
            }
            self.meter.charge_memo_state()?;
            self.push(WorkItem::StoreMemo { key })?;
        }
        let Maybe::Present(stored) = self.arena.node(node)
        else {
            return Err(broken(RenderInvariant::DocumentIdentity));
        };
        let (continuation, child, child_column, child_indentation) = match stored {
            | DocNode::Empty => return Ok(Step::Result(self.empty(column)?)),
            | DocNode::Text(text) => return Ok(Step::Result(self.text(text, column)?)),
            | DocNode::Verbatim(verbatim) => {
                return Ok(Step::Result(self.verbatim(verbatim, column)?));
            },
            | DocNode::Line | DocNode::HardLine => {
                return Ok(Step::Result(self.line(indentation)?));
            },
            | DocNode::Nest { amount, doc } => {
                let raised = u32::from(indentation).checked_add(amount).ok_or(
                    RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::Indentation,
                    },
                )?;
                (WorkItem::AfterNest, doc, column, Indentation::from(raised))
            },
            | DocNode::Align { doc } => (
                WorkItem::AfterAlign,
                doc,
                column,
                Indentation::from(u32::from(column)),
            ),
            | DocNode::Flatten { .. } => {
                let Maybe::Present(image) = self.arena.flattened_node(node)
                else {
                    return Err(broken(RenderInvariant::DocumentIdentity));
                };
                (WorkItem::AfterFlatten, image, column, indentation)
            },
            | DocNode::Choice { left, right } => (
                WorkItem::AfterChoiceLeft {
                    right,
                    column,
                    indentation,
                    force,
                },
                left,
                column,
                indentation,
            ),
            | DocNode::Concat { left, right } => (
                WorkItem::AfterConcatLeft {
                    right,
                    indentation,
                    force,
                },
                left,
                column,
                indentation,
            ),
        };
        self.push(continuation)?;
        self.push(WorkItem::Eval {
            node: child,
            column: child_column,
            indentation: child_indentation,
            force,
        })?;
        Ok(Step::Scheduled)
    }

    /// Retains one candidate in a fallibly reserved, metered frontier.
    ///
    /// # Specification
    /// - requires: `measure` owns its plan.
    /// - ensures: a one-measure frontier; a refused charge starts releasing the
    ///   plan. A release failure takes precedence over the refused charge.
    /// - provides: every leaf's result.
    /// - fails: a frontier ceiling or a frontier that cannot grow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::AllocationFailed`], the frontier ceiling or a
    /// release error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, Unicode text, physical endings, indentation
    ///   and mixed verbatim fragments expose exact columns, widened
    ///   squared-overflow costs, line counts, byte counts and taint at width
    ///   boundaries. Wrong first-fragment origins, byte/scalar confusion or
    ///   omitted ending and indentation bytes change these observations.
    ///   Allocation exhaustion is not injected.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_with_several_middle_lines_stores_absolute_widths`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `resolve::tests::leaf_measures_preserve_unicode_fragments_and_width_boundaries`
    #[anodized::spec(
        captures: before = self.meter.usage().frontier_entries,
        ensures: |ret| ret.as_ref().map_or_else(|_error| self.meter.usage().frontier_entries == before,
            |set| matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.as_slice() == [measure])
                && u64::from(before).checked_add(1) == Some(u64::from(self.meter.usage().frontier_entries)))
    )]
    fn singleton(
        &mut self,
        measure: Measure,
    ) -> Result<MeasureSet, RenderError>
    {
        let mut frontier = Vec::new();
        frontier
            .try_reserve(1usize)
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::Frontier,
            })?;
        if let Err(error) = self.meter.charge_frontier_entry() {
            self.release_plan(measure.plan)?;
            return Err(error);
        }
        frontier.push(measure);
        Ok(MeasureSet::Frontier(frontier))
    }

    /// Builds the empty leaf measure.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a zero-cost, zero-byte measure ending at `column`, where it
    ///   began.
    /// - provides: the result of `Empty`.
    /// - fails: a plan or frontier ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error the plan or frontier charge returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, Unicode text, physical endings, indentation
    ///   and mixed verbatim fragments expose exact columns, widened
    ///   squared-overflow costs, line counts, byte counts and taint at width
    ///   boundaries. Wrong first-fragment origins, byte/scalar confusion or
    ///   omitted ending and indentation bytes change these observations.
    ///   Allocation exhaustion is not injected.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_with_several_middle_lines_stores_absolute_widths`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `resolve::tests::leaf_measures_preserve_unicode_fragments_and_width_boundaries`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |set| { let Maybe::Present(measure) = first(set) else { return false };
            matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == 1)
                && measure.last_column == column
                && measure.cost == LayoutCost::zero()
                && u64::from(measure.output_bytes) == 0
                && self.plans.get(measure.plan) == Maybe::Present(PlanNode::Empty) })
    )]
    fn empty(
        &mut self,
        column: Column,
    ) -> Result<MeasureSet, RenderError>
    {
        let plan = self.plans.alloc(PlanNode::Empty, self.meter)?;
        self.singleton(Measure {
            last_column: column,
            cost: LayoutCost::zero(),
            plan,
            output_bytes: OutputBytes::from(0u64),
        })
    }

    /// Builds a text leaf measure.
    ///
    /// # Specification
    /// - requires: `text` names a text of the arena.
    /// - ensures: the measure ends at `column` plus the text's width and
    ///   charges its overflow from `column`; a text ending past the computation
    ///   width is tainted.
    /// - provides: the result of `Text`.
    /// - fails: an arithmetic overflow, a plan or frontier ceiling, or a text
    ///   the arena does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the leaf meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, Unicode text, physical endings, indentation
    ///   and mixed verbatim fragments expose exact columns, widened
    ///   squared-overflow costs, line counts, byte counts and taint at width
    ///   boundaries. Wrong first-fragment origins, byte/scalar confusion or
    ///   omitted ending and indentation bytes change these observations.
    ///   Allocation exhaustion is not injected.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_with_several_middle_lines_stores_absolute_widths`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `resolve::tests::leaf_measures_preserve_unicode_fragments_and_width_boundaries`
    #[anodized::spec(
        ensures: |ret| { let Maybe::Present(identity) = self.arena.text_identity(text) else { return matches!(ret, Err(RenderError::Invariant { invariant: RenderInvariant::DocumentIdentity })) };
            let end = u64::from(u32::from(column)).saturating_add(u64::from(u32::from(identity.width())));
            if end > u64::from(u32::MAX) { return matches!(ret, Err(RenderError::ArithmeticOverflow { operation: RenderArithmetic::Column })) }
            ret.as_ref().map_or(true,
            |set| { let Maybe::Present(measure) = first(set) else { return false };
            let page = u64::from(u32::from(self.options.page_width));
            let start_excess = u128::from(u64::from(u32::from(column)).saturating_sub(page));
            let end_excess = u128::from(end.saturating_sub(page));
            u64::from(u32::from(measure.last_column)) == end

                && u128::from(u64::from(measure.cost.squared_overflow)) == end_excess.saturating_mul(end_excess).saturating_sub(start_excess.saturating_mul(start_excess))

                && u64::from(measure.cost.line_breaks) == 0

                && identity.bytes_used().is_ok_and(|bytes| u64::from(measure.output_bytes) == u64::from(bytes))

                && self.plans.get(measure.plan) == Maybe::Present(PlanNode::Text(text))

                && (if end > u64::from(u32::from(self.options.computation_width)) { matches!(*set, MeasureSet::Tainted(TaintPromise::Ready(_))) }
            else { matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == 1) }) }) }
    )]
    fn text(
        &mut self,
        text: TextId,
        column: Column,
    ) -> Result<MeasureSet, RenderError>
    {
        let Maybe::Present(identity) = self.arena.text_identity(text)
        else {
            return Err(broken(RenderInvariant::DocumentIdentity));
        };
        let width = identity.width();
        let end = u32::from(column).checked_add(u32::from(width)).ok_or(
            RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::Column,
            },
        )?;
        let overflow = incoming_overflow(column, width, self.options.page_width)?;
        let bytes = identity
            .bytes_used()
            .map_err(|_error| RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            })?;
        let plan = self.plans.alloc(PlanNode::Text(text), self.meter)?;
        let set = self.singleton(Measure {
            last_column: Column::from(end),
            cost: LayoutCost {
                squared_overflow: overflow,
                line_breaks: LineBreaks::from(0u64),
            },
            plan,
            output_bytes: OutputBytes::from(u64::from(bytes)),
        })?;
        if end > u32::from(self.options.computation_width) {
            self.taint_set(set)
        }
        else {
            Ok(set)
        }
    }

    /// Builds a verbatim leaf measure with per-fragment charging.
    ///
    /// # Specification
    /// - requires: `verbatim` names a verbatim text of the arena.
    /// - ensures: the first fragment is charged from `column`, every later one
    ///   from column zero, each stored ending as one line break; the measure
    ///   ends at the last fragment's column; any fragment ending past the
    ///   computation width taints it.
    /// - provides: the result of `Verbatim`.
    /// - fails: an arithmetic overflow, a plan or frontier ceiling, or a
    ///   verbatim text the arena does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the leaf meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, Unicode text, physical endings, indentation
    ///   and mixed verbatim fragments expose exact columns, widened
    ///   squared-overflow costs, line counts, byte counts and taint at width
    ///   boundaries. Wrong first-fragment origins, byte/scalar confusion or
    ///   omitted ending and indentation bytes change these observations.
    ///   Allocation exhaustion is not injected.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_with_several_middle_lines_stores_absolute_widths`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `resolve::tests::leaf_measures_preserve_unicode_fragments_and_width_boundaries`
    #[anodized::spec(
        ensures: |ret| { let Maybe::Present(identity) = self.arena.verbatim_identity(verbatim) else { return matches!(ret, Err(RenderError::Invariant { invariant: RenderInvariant::DocumentIdentity })) };
            ret.as_ref().map_or(true,
            |set| { let Maybe::Present(measure) = first(set) else { return false };
            let page = u64::from(u32::from(self.options.page_width));
            let mut squared = 0_u128;
            let mut last = u64::from(u32::from(column));
            let mut breaks = 0_u128;
            let mut tainted = false;
            for (index, line) in identity.lines().iter().enumerate() { let start = if index == 0 { u64::from(u32::from(column)) }
            else { 0 };
            last = start.saturating_add(u64::from(u32::from(line.scalar_width())));
            let from = u128::from(start.saturating_sub(page));
            let to = u128::from(last.saturating_sub(page));
            squared = squared.saturating_add(to.saturating_mul(to).saturating_sub(from.saturating_mul(from)));
            if matches!(line.ending(), Maybe::Present(_)) { breaks = breaks.saturating_add(1);
            } tainted |= last > u64::from(u32::from(self.options.computation_width));
            } !identity.lines().is_empty()

                && u64::from(u32::from(measure.last_column)) == last

                && u128::from(u64::from(measure.cost.squared_overflow)) == squared

                && u128::from(u64::from(measure.cost.line_breaks)) == breaks

                && identity.bytes_used().is_ok_and(|bytes| u64::from(measure.output_bytes) == u64::from(bytes))

                && self.plans.get(measure.plan) == Maybe::Present(PlanNode::Verbatim(verbatim))

                && (if tainted { matches!(*set, MeasureSet::Tainted(TaintPromise::Ready(_))) }
            else { matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == 1) }) }) }
    )]
    fn verbatim(
        &mut self,
        verbatim: VerbatimId,
        column: Column,
    ) -> Result<MeasureSet, RenderError>
    {
        let Maybe::Present(identity) = self.arena.verbatim_identity(verbatim)
        else {
            return Err(broken(RenderInvariant::DocumentIdentity));
        };
        let Some(first_line) = identity.lines().first().copied()
        else {
            return Err(broken(RenderInvariant::VerbatimFragments));
        };
        let bound = u32::from(self.options.computation_width);
        let first_end = u32::from(column)
            .checked_add(u32::from(first_line.scalar_width()))
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::Column,
            })?;
        let mut cost = LayoutCost {
            squared_overflow: incoming_overflow(
                column,
                first_line.scalar_width(),
                self.options.page_width,
            )?,
            line_breaks: LineBreaks::from(0u64),
        };
        let mut taint = if first_end > bound {
            WidthTaint::Tainted
        }
        else {
            WidthTaint::Untainted
        };
        let mut last_column = Column::from(first_end);
        for (index, line) in identity.lines().iter().copied().enumerate() {
            if index > 0usize {
                let overflow = absolute_overflow(line.scalar_width(), self.options.page_width)?;
                let next = u64::from(cost.squared_overflow)
                    .checked_add(u64::from(overflow))
                    .ok_or(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::SquaredOverflow,
                    })?;
                cost.squared_overflow = SquaredOverflow::from(next);
                last_column = Column::from(u32::from(line.scalar_width()));
                if u32::from(last_column) > bound {
                    taint = WidthTaint::Tainted;
                }
            }
            if let Maybe::Present(_) = line.ending() {
                let next = u64::from(cost.line_breaks).checked_add(1u64).ok_or(
                    RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::LineBreaks,
                    },
                )?;
                cost.line_breaks = LineBreaks::from(next);
            }
        }
        let bytes = identity
            .bytes_used()
            .map_err(|_error| RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            })?;
        let plan = self.plans.alloc(PlanNode::Verbatim(verbatim), self.meter)?;
        let set = self.singleton(Measure {
            last_column,
            cost,
            plan,
            output_bytes: OutputBytes::from(u64::from(bytes)),
        })?;
        match taint {
            | WidthTaint::Tainted => self.taint_set(set),
            | WidthTaint::Untainted => Ok(set),
        }
    }

    /// Builds a line or hard-line measure.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one line break, the indentation's overflow, the ending's
    ///   bytes plus one byte per indentation column; the measure ends at the
    ///   indentation, tainted past the computation width.
    /// - provides: the result of `Line` and `HardLine`.
    /// - fails: an arithmetic overflow or a plan or frontier ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the leaf meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, Unicode text, physical endings, indentation
    ///   and mixed verbatim fragments expose exact columns, widened
    ///   squared-overflow costs, line counts, byte counts and taint at width
    ///   boundaries. Wrong first-fragment origins, byte/scalar confusion or
    ///   omitted ending and indentation bytes change these observations.
    ///   Allocation exhaustion is not injected.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    /// - witness: `algebra::tests::text_emits_at_the_current_column`
    /// - witness: `algebra::tests::verbatim_with_several_middle_lines_stores_absolute_widths`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    /// - witness: `resolve::tests::leaf_measures_preserve_unicode_fragments_and_width_boundaries`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or(true,
            |set| { let Maybe::Present(measure) = first(set) else { return false };
            let excess = u128::from(u32::from(indentation).saturating_sub(u32::from(self.options.page_width)));
            measure.last_column == Column::from(u32::from(indentation))

                && u128::from(u64::from(measure.cost.squared_overflow)) == excess.saturating_mul(excess)

                && u64::from(measure.cost.line_breaks) == 1

                && u64::from(measure.output_bytes) == u64::from(u32::from(indentation)).saturating_add(u64::from(self.options.line_ending.byte_width()))

                && self.plans.get(measure.plan) == Maybe::Present(PlanNode::Newline { indentation, ending: self.options.line_ending })

                && (if u32::from(indentation) > u32::from(self.options.computation_width) { matches!(*set, MeasureSet::Tainted(TaintPromise::Ready(_))) }
            else { matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == 1) }) })
    )]
    fn line(
        &mut self,
        indentation: Indentation,
    ) -> Result<MeasureSet, RenderError>
    {
        let cost = line_cost(indentation, self.options.page_width)?;
        let bytes = u64::from(self.options.line_ending.byte_width())
            .checked_add(u64::from(u32::from(indentation)))
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            })?;
        let plan = self.plans.alloc(
            PlanNode::Newline {
                indentation,
                ending: self.options.line_ending,
            },
            self.meter,
        )?;
        let set = self.singleton(Measure {
            last_column: Column::from(u32::from(indentation)),
            cost,
            plan,
            output_bytes: OutputBytes::from(bytes),
        })?;
        if u32::from(indentation) > u32::from(self.options.computation_width) {
            self.taint_set(set)
        }
        else {
            Ok(set)
        }
    }

    /// Starts right-side evaluation for a left result.
    ///
    /// # Specification
    /// - requires: `left_set` is a frontier or a ready promise.
    /// - ensures: the right child is pushed at the first left measure's ending
    ///   column, the rest of the left frontier kept for later.
    /// - provides: the first half of concatenation.
    /// - fails: an empty or deferred left set, or a push error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::Invariant`] for a left set with no measure, and
    /// the first push error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.work.len(), first(&left_set), match left_set { MeasureSet::Frontier(ref frontier) => (frontier.len().saturating_sub(1), frontier.get(1).copied(), if frontier.len() > 1 { frontier.last().copied() }
            else { None }, WidthTaint::Untainted), MeasureSet::Tainted(_) => (0, None, None, WidthTaint::Tainted) }),
        ensures: |ret| match before.1 { Maybe::Absent(_) => matches!(ret, Err(RenderError::Invariant { invariant: RenderInvariant::MissingMeasure }))
                && self.work.len() == before.0, Maybe::Present(left) => ret.as_ref().map_or(true,
            |&()| before.0.checked_add(2) == Some(self.work.len())
                && self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force } if actual_node == right
                && actual_column == left.last_column
                && actual_indentation == indentation
                && actual_force == force))
                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::ConcatNext(ref state) if state.left == left
                && state.right == right
                && state.indentation == indentation
                && state.force == force
                && state.remaining.len() == before.2.0
                && state.remaining.first().copied() == before.2.1
                && state.remaining.last().copied() == before.2.2
                && state.taint == before.2.3
                && state.results.is_empty()))) }
    )]
    fn start_concat(
        &mut self,
        right: NodeId,
        indentation: Indentation,
        force: ResolutionMode,
        left_set: MeasureSet,
    ) -> Result<(), RenderError>
    {
        let (left, remaining, taint) = match left_set {
            | MeasureSet::Frontier(mut frontier) => {
                if frontier.is_empty() {
                    return Err(broken(RenderInvariant::MissingMeasure));
                }
                let first_measure = frontier.remove(0usize);
                (first_measure, frontier, WidthTaint::Untainted)
            },
            | MeasureSet::Tainted(TaintPromise::Ready(measure)) => {
                (measure, Vec::new(), WidthTaint::Tainted)
            },
            | MeasureSet::Tainted(TaintPromise::Deferred { .. }) => {
                return Err(broken(RenderInvariant::MissingMeasure));
            },
        };
        let column = left.last_column;
        self.push(WorkItem::ConcatNext(ConcatState {
            right,
            indentation,
            force,
            left,
            remaining,
            results: Vec::new(),
            taint,
        }))?;
        self.push(WorkItem::Eval {
            node: right,
            column,
            indentation,
            force,
        })
    }

    /// Resumes a right-side concatenation and schedules the next left measure.
    ///
    /// # Specification
    /// - requires: `right_set` is the right child's result at the current left
    ///   measure's ending column.
    /// - ensures: a deferred right result is forced first; otherwise every
    ///   right measure is joined to the left one, and the next left measure is
    ///   scheduled, or — the left frontier spent — the normalized products are
    ///   the result, tainted when any part was.
    /// - provides: the second half of concatenation.
    /// - fails: an arithmetic overflow, a plan or frontier ceiling, or a push
    ///   error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the join meets.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: before = (self.work.len(), match right_set { MeasureSet::Tainted(TaintPromise::Deferred { doc, column, indentation }) => Some((doc, column, indentation)), _ => None }, state.remaining.first().copied(), state.right, state.indentation, state.force, state.taint == WidthTaint::Tainted || matches!(right_set, MeasureSet::Tainted(TaintPromise::Ready(_))), state.left, state.remaining.len(), state.results.len(), match right_set { MeasureSet::Frontier(ref frontier) => frontier.last().copied(), MeasureSet::Tainted(TaintPromise::Ready(measure)) => Some(measure), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => None }, match right_set { MeasureSet::Frontier(ref frontier) => frontier.len(), MeasureSet::Tainted(TaintPromise::Ready(_)) => 1, MeasureSet::Tainted(TaintPromise::Deferred { .. }) => 0 }),
        ensures: |ret| ret.as_ref().map_or(true,
            |step| { if let Some((doc, column, indentation)) = before.1 { return matches!(*step, Step::Scheduled)

                && before.0.checked_add(2) == Some(self.work.len())

                && self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == doc

                && actual_column == column

                && actual_indentation == indentation

                && actual_force == ResolutionMode::Forced))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::ForceConcatRight(ref state) if state.left == before.7

                && state.right == before.3

                && state.indentation == before.4

                && state.force == before.5

                && state.remaining.first().copied() == before.2

                && state.remaining.len() == before.8

                && state.results.len() == before.9)) }
        if let Some(next) = before.2 { return matches!(*step, Step::Scheduled)

                && before.0.checked_add(2) == Some(self.work.len())

                && self.work.last().is_some_and(|item| matches!(*item, WorkItem::Eval { node: actual_node, column: actual_column, indentation: actual_indentation, force: actual_force }
        if actual_node == before.3

                && actual_column == next.last_column

                && actual_indentation == before.4

                && actual_force == before.5))

                && self.work.get(self.work.len().saturating_sub(2)).is_some_and(|item| matches!(*item, WorkItem::ConcatNext(ref state) if state.left == next

                && state.right == before.3

                && state.indentation == before.4

                && state.force == before.5

                && state.remaining.len().checked_add(1) == Some(before.8)

                && before.9.checked_add(before.11) == Some(state.results.len())

                && (state.taint == WidthTaint::Tainted) == before.6

                && before.10.is_none_or(|right| state.results.last().is_some_and(|product| product.last_column == right.last_column

                && u64::from(before.7.cost.squared_overflow).checked_add(u64::from(right.cost.squared_overflow)) == Some(u64::from(product.cost.squared_overflow))

                && u64::from(before.7.cost.line_breaks).checked_add(u64::from(right.cost.line_breaks)) == Some(u64::from(product.cost.line_breaks))

                && u64::from(before.7.output_bytes).checked_add(u64::from(right.output_bytes)) == Some(u64::from(product.output_bytes))

                && self.plans.get(product.plan) == Maybe::Present(PlanNode::Seq { left: before.7.plan, right: right.plan }))))) } self.work.len() <= before.0

                && matches!(*step, Step::Result(ref set) if (match *set { MeasureSet::Frontier(ref frontier) => frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_))), MeasureSet::Tainted(TaintPromise::Ready(measure)) => matches!(self.plans.get(measure.plan), Maybe::Present(_)), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => true })

                && match *set { MeasureSet::Frontier(ref frontier) => (!before.6 || frontier.is_empty())

                && (frontier.iter().zip(frontier.iter().skip(1)).all(|(left, right)| left.cost < right.cost

                && left.last_column > right.last_column)

                && frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_)))), MeasureSet::Tainted(TaintPromise::Ready(_)) => before.6, MeasureSet::Tainted(TaintPromise::Deferred { .. }) => false }) })
    )]
    fn resume_concat(
        &mut self,
        mut state: ConcatState,
        right_set: MeasureSet,
    ) -> Result<Step, RenderError>
    {
        let right = match right_set {
            | MeasureSet::Tainted(TaintPromise::Deferred {
                doc,
                column,
                indentation,
            }) => {
                self.push(WorkItem::ForceConcatRight(state))?;
                self.push(WorkItem::Eval {
                    node: doc,
                    column,
                    indentation,
                    force: ResolutionMode::Forced,
                })?;
                return Ok(Step::Scheduled);
            },
            | MeasureSet::Frontier(frontier) => frontier,
            | MeasureSet::Tainted(TaintPromise::Ready(measure)) => {
                state.taint = WidthTaint::Tainted;
                let mut ready = Vec::new();
                ready
                    .try_reserve(1usize)
                    .map_err(|_error| RenderError::AllocationFailed {
                        site: RenderAllocationSite::Frontier,
                    })?;
                ready.push(measure);
                ready
            },
        };
        state
            .results
            .try_reserve(right.len())
            .map_err(|_error| RenderError::AllocationFailed {
                site: RenderAllocationSite::Frontier,
            })?;
        for right_measure in right {
            self.meter.charge_layout_step()?;
            let cost = add_cost(state.left.cost, right_measure.cost)?;
            let output_bytes =
                add_output_bytes(state.left.output_bytes, right_measure.output_bytes)?;
            let plan = self
                .plans
                .alloc_seq(state.left.plan, right_measure.plan, self.meter)?;
            state.results.push(Measure {
                last_column: right_measure.last_column,
                cost,
                plan,
                output_bytes,
            });
            self.release_plan(right_measure.plan)?;
        }
        self.release_plan(state.left.plan)?;
        if !state.remaining.is_empty() {
            state.left = state.remaining.remove(0usize);
            let right_node = state.right;
            let indentation = state.indentation;
            let force = state.force;
            let column = state.left.last_column;
            self.push(WorkItem::ConcatNext(state))?;
            self.push(WorkItem::Eval {
                node: right_node,
                column,
                indentation,
                force,
            })?;
            return Ok(Step::Scheduled);
        }
        let result = MeasureSet::Frontier(self.normalize(state.results)?);
        Ok(Step::Result(match state.taint {
            | WidthTaint::Tainted => self.taint_set(result)?,
            | WidthTaint::Untainted => result,
        }))
    }

    /// Normalizes a candidate set into a sorted, mutually non-dominating
    /// frontier.
    ///
    /// # Specification
    /// - requires: `set` owns its plans.
    /// - ensures: a frontier is normalized as [`Self::normalize`]; a promise is
    ///   returned unchanged.
    /// - provides: the normalization a choice's merge needs.
    /// - fails: as [`Self::normalize`].
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error [`Self::normalize`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every bag of up to three live-plan candidates over
    ///   nine cost/column ranks is compared with an independent pairwise Pareto
    ///   oracle, including stable ties. Complete retained identities and
    ///   released identities expose missing alternatives, reversed dominance,
    ///   changed lexicographic order and wrong duplicate ownership. This finite
    ///   model does not prove arbitrary document evaluation or allocation
    ///   failure.
    /// - witness: `resolve::tests::small_candidate_bags_match_a_stable_pairwise_pareto_oracle`
    #[anodized::spec(
        captures: before = match set { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.iter().enumerate().min_by_key(|&(index, measure)| (measure.cost, measure.last_column, index)).map(|(_index, measure)| *measure), None), MeasureSet::Tainted(promise) => (0, None, Some(promise)) },
        ensures: |ret| ret.as_ref().map_or(true,
            |set| match *set { MeasureSet::Frontier(ref frontier) => before.2.is_none()
                && frontier.len() <= before.0
                && frontier.first().copied() == before.1
                && (frontier.iter().zip(frontier.iter().skip(1)).all(|(left, right)| left.cost < right.cost
                && left.last_column > right.last_column)
                && frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_)))), MeasureSet::Tainted(promise) => before.2 == Some(promise) })
    )]
    fn normalize_set(
        &mut self,
        set: MeasureSet,
    ) -> Result<MeasureSet, RenderError>
    {
        match set {
            | MeasureSet::Frontier(frontier) => Ok(MeasureSet::Frontier(self.normalize(frontier)?)),
            | MeasureSet::Tainted(promise) => Ok(MeasureSet::Tainted(promise)),
        }
    }

    /// Inserts all candidates while charging each comparison and retained
    /// entry.
    ///
    /// # Specification
    /// - requires: every candidate owns its plan.
    /// - ensures: the result holds no measure another strictly dominates in
    ///   cost and ending column, keeps the earlier of two equal ones, and is
    ///   sorted by cost, then by later ending column; every dropped plan is
    ///   released.
    /// - provides: the Pareto frontier every non-leaf result is.
    /// - fails: a layout or frontier ceiling, a frontier that cannot grow, or a
    ///   release error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`RenderError`] the normalization meets.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every bag of up to three live-plan candidates over
    ///   nine cost/column ranks is compared with an independent pairwise Pareto
    ///   oracle, including stable ties. Complete retained identities and
    ///   released identities expose missing alternatives, reversed dominance,
    ///   changed lexicographic order and wrong duplicate ownership. This finite
    ///   model does not prove arbitrary document evaluation or allocation
    ///   failure.
    /// - witness: `resolve::tests::small_candidate_bags_match_a_stable_pairwise_pareto_oracle`
    #[anodized::spec(
        captures: before = (candidates.len(), candidates.iter().enumerate().min_by_key(|&(index, measure)| (measure.cost, measure.last_column, index)).map(|(_index, measure)| *measure)),
        ensures: |ret| ret.as_ref().map_or(true,
            |frontier| frontier.len() <= before.0
                && frontier.first().copied() == before.1
                && (frontier.iter().zip(frontier.iter().skip(1)).all(|(left, right)| left.cost < right.cost
                && left.last_column > right.last_column)
                && frontier.iter().all(|measure| matches!(self.plans.get(measure.plan), Maybe::Present(_)))))
    )]
    fn normalize(
        &mut self,
        candidates: Vec<Measure>,
    ) -> Result<Vec<Measure>, RenderError>
    {
        let mut frontier: Vec<Measure> = Vec::new();
        for candidate in candidates {
            let mut dominated = Dominance::None;
            for existing in &frontier {
                self.meter.charge_layout_step()?;
                if dominates(*existing, candidate) == Dominance::Strict
                    || (existing.cost == candidate.cost
                        && existing.last_column == candidate.last_column)
                {
                    dominated = Dominance::Strict;
                    break;
                }
            }
            if dominated == Dominance::Strict {
                self.release_plan(candidate.plan)?;
                continue;
            }
            let mut retained = Vec::new();
            retained
                .try_reserve(frontier.len().saturating_add(1usize))
                .map_err(|_error| RenderError::AllocationFailed {
                    site: RenderAllocationSite::Frontier,
                })?;
            for existing in frontier {
                self.meter.charge_layout_step()?;
                if dominates(candidate, existing) == Dominance::Strict {
                    self.release_plan(existing.plan)?;
                }
                else {
                    retained.push(existing);
                }
            }
            frontier = retained;
            self.meter.charge_frontier_entry()?;
            frontier.push(candidate);
        }
        frontier.sort_by(|left, right| {
            left.cost
                .cmp(&right.cost)
                .then_with(|| right.last_column.cmp(&left.last_column))
        });
        Ok(frontier)
    }
}

/// Returns whether `left` strictly dominates `right`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Dominance::Strict`] exactly when `left` is no worse in cost and
///   in ending column and strictly better in one of them.
/// - provides: the Pareto order the frontier is pruned by.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every bag of up to three live-plan candidates over nine
///   cost/column ranks is compared with an independent pairwise Pareto oracle,
///   including stable ties. Complete retained identities and released
///   identities expose missing alternatives, reversed dominance, changed
///   lexicographic order and wrong duplicate ownership. This finite model does
///   not prove arbitrary document evaluation or allocation failure.
/// - witness: `resolve::tests::small_candidate_bags_match_a_stable_pairwise_pareto_oracle`
#[anodized::spec(
    ensures: |ret| (ret == Dominance::Strict) == ((left.cost < right.cost
            && left.last_column <= right.last_column) || (left.cost <= right.cost
            && left.last_column < right.last_column))
)]
fn dominates(
    left: Measure,
    right: Measure,
) -> Dominance
{
    let no_worse = left.cost <= right.cost && left.last_column <= right.last_column;
    let strict = left.cost < right.cost || left.last_column < right.last_column;
    if no_worse && strict {
        Dominance::Strict
    }
    else {
        Dominance::None
    }
}

/// Resolves a document root into its winning plan summary.
///
/// # Specification
/// - requires: the finalized arena, candidate root and width options are
///   supplied; foreign handles and reversed widths are checked refusals.
/// - ensures: the selected plan has least lexicographic cost among the
///   untainted frontier and preserves exact tainted fallback context; the
///   selected output bytes are charged to `meter`.
/// - provides: winning plan identity, cost, taint status, and output bytes.
/// - fails: returns unknown-handle, width, arithmetic, allocation, render-limit
///   or invariant errors without returning partial output.
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError`] for invalid handles, widths, checked arithmetic,
/// allocation failure, a named render limit, or a broken engine invariant.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[anodized::spec(
    captures: before = meter.usage(),
    ensures: |ret| if arena.contains(root) == DocHandleStatus::Absent { matches!(ret, Err(RenderError::UnknownDoc))
            && meter.usage() == before }
        else if u32::from(options.computation_width) < u32::from(options.page_width) { matches!(ret, Err(RenderError::InvalidWidth))
            && meter.usage() == before }
        else { ret.as_ref().map_or(true,
        |winner| matches!(winner.plans.get(winner.plan), Maybe::Present(_))
            && if true { u64::from(before.output_bytes).checked_add(u64::from(winner.output_bytes)) == Some(u64::from(meter.usage().output_bytes)) }
        else { meter.usage().output_bytes == before.output_bytes }) }
)]
#[inline]
pub fn resolve(
    arena: &DocArena,
    root: DocId,
    options: LayoutOptions,
    meter: &mut RenderMeter,
) -> Result<Resolved, RenderError>
{
    resolve_with_output_accounting(arena, root, options, meter, OutputAccounting::AtResolve)
}

/// Resolves a root for the fused render machine.
///
/// # Specification
/// - requires: the finalized arena, candidate root and width options are
///   supplied; foreign handles and reversed widths are checked refusals.
/// - ensures: output bytes remain uncharged until the machine appends them.
/// - provides: the selected plan, cost, taint status, and exact output count.
/// - fails: returns the same checked resolution errors as [`resolve`].
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError`] for invalid handles, widths, checked arithmetic,
/// allocation failure, a named render limit, or a broken engine invariant.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[anodized::spec(
    captures: before = meter.usage(),
    ensures: |ret| if arena.contains(root) == DocHandleStatus::Absent { matches!(ret, Err(RenderError::UnknownDoc))
            && meter.usage() == before }
        else if u32::from(options.computation_width) < u32::from(options.page_width) { matches!(ret, Err(RenderError::InvalidWidth))
            && meter.usage() == before }
        else { ret.as_ref().map_or(true,
        |winner| matches!(winner.plans.get(winner.plan), Maybe::Present(_))
            && if false { u64::from(before.output_bytes).checked_add(u64::from(winner.output_bytes)) == Some(u64::from(meter.usage().output_bytes)) }
        else { meter.usage().output_bytes == before.output_bytes }) }
)]
pub(crate) fn resolve_for_render(
    arena: &DocArena,
    root: DocId,
    options: LayoutOptions,
    meter: &mut RenderMeter,
) -> Result<Resolved, RenderError>
{
    resolve_with_output_accounting(arena, root, options, meter, OutputAccounting::AtAppend)
}

/// Resolves one root and applies the selected output-accounting phase.
///
/// # Specification
/// - requires: the finalized arena, candidate root and width options are
///   supplied; foreign handles and reversed widths are checked refusals.
/// - ensures: the handle and the widths are checked before any work; the
///   returned plan owns its retained plan arena; output bytes are charged now
///   under [`OutputAccounting::AtResolve`] and left for the appends otherwise.
/// - provides: one shared implementation for standalone resolution and fused
///   rendering.
/// - fails: propagates checked resolution and accounting errors.
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError::UnknownDoc`] for a foreign handle,
/// [`RenderError::InvalidWidth`] for reversed widths, and the first error
/// resolution meets.
///
/// # Adequacy
/// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
///   tainted contexts expose selected cost, exact bytes, taint and budget
///   counts. Losing a retained plan, changing width or handle precedence, using
///   the wrong context or charging output in both phases changes these
///   observations. The bounded choice fixtures do not enumerate arbitrary
///   document graphs; allocation exhaustion is not injected.
/// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[anodized::spec(
    captures: before = meter.usage(),
    ensures: |ret| if arena.contains(root) == DocHandleStatus::Absent { matches!(ret, Err(RenderError::UnknownDoc))
            && meter.usage() == before }
        else if u32::from(options.computation_width) < u32::from(options.page_width) { matches!(ret, Err(RenderError::InvalidWidth))
            && meter.usage() == before }
        else { ret.as_ref().map_or(true,
        |winner| matches!(winner.plans.get(winner.plan), Maybe::Present(_))
            && if accounting == OutputAccounting::AtResolve { u64::from(before.output_bytes).checked_add(u64::from(winner.output_bytes)) == Some(u64::from(meter.usage().output_bytes)) }
        else { meter.usage().output_bytes == before.output_bytes }) }
)]
fn resolve_with_output_accounting(
    arena: &DocArena,
    root: DocId,
    options: LayoutOptions,
    meter: &mut RenderMeter,
    accounting: OutputAccounting,
) -> Result<Resolved, RenderError>
{
    if arena.contains(root) == DocHandleStatus::Absent {
        return Err(RenderError::UnknownDoc);
    }
    if u32::from(options.computation_width) < u32::from(options.page_width) {
        return Err(RenderError::InvalidWidth);
    }
    let (measure, width_taint, plans) = Resolver::new(arena, options, meter).run(root.node_id())?;
    if accounting == OutputAccounting::AtResolve {
        meter.charge_output_bytes(measure.output_bytes)?;
    }
    Ok(Resolved {
        plans,
        plan: measure.plan,
        cost: measure.cost,
        width_taint,
        output_bytes: measure.output_bytes,
    })
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::arena::TextSource;
    use crate::build::DocBuilder;
    use crate::limits::BuildLimits;
    use crate::limits::BuildMeter;
    use crate::limits::RenderLimits;
    use crate::measure::PhysicalLineEnding;
    use crate::units::ComputationWidth;
    use crate::units::PageWidth;

    /// The measure a forced context answers, whether frontier or ready.
    ///
    /// # Specification
    /// - requires: the test supplies the result of forcing a leaf.
    /// - ensures: the returned measure is the unique frontier member or exact
    ///   ready promise.
    /// - provides: a plan-bearing observation for forced-context witnesses.
    /// - panics: for a scheduled or deferred step, or a frontier without
    ///   exactly one member.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text, indentation, choice, repeated memo contexts and
    ///   tainted contexts expose selected cost, exact bytes, taint and budget
    ///   counts. Losing a retained plan, changing width or handle precedence,
    ///   using the wrong context or charging output in both phases changes
    ///   these observations. The bounded choice fixtures do not enumerate
    ///   arbitrary document graphs; allocation exhaustion is not injected.
    /// - witness: `algebra::tests::resolver_returns_the_text_winner_summary`
    /// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
    /// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
    /// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
    /// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
    #[anodized::spec(
        captures: expected = match step { Step::Result(MeasureSet::Frontier(ref frontier)) => frontier.first().copied(), Step::Result(MeasureSet::Tainted(TaintPromise::Ready(measure))) => Some(measure), Step::Result(MeasureSet::Tainted(TaintPromise::Deferred { .. })) | Step::Scheduled => None },
        ensures: |ret| expected == Some(ret)
    )]
    fn forced(step: Step) -> Measure
    {
        match step {
            | Step::Result(MeasureSet::Frontier(frontier)) => {
                assert_eq!(frontier.len(), 1usize, "a text leaf has one layout");
                frontier[0]
            },
            | Step::Result(MeasureSet::Tainted(TaintPromise::Ready(measure))) => measure,
            | Step::Result(MeasureSet::Tainted(TaintPromise::Deferred { .. }))
            | Step::Scheduled => {
                panic!("a forced leaf answers a measure")
            },
        }
    }

    /// Tainted promises retain distinct contexts and forced measures.
    #[test]
    fn tainted_promises_retain_distinct_contexts_and_forced_measures()
    {
        let mut build_meter = BuildMeter::new(BuildLimits::default());
        let mut builder = DocBuilder::try_new(&mut build_meter).unwrap();
        let text = builder.text(TextSource::from("x")).unwrap();
        let arena = builder.finish().unwrap();
        let options = LayoutOptions::try_new(
            PageWidth::from(2u32),
            ComputationWidth::from(2u32),
            PhysicalLineEnding::Lf,
        )
        .unwrap();
        let mut meter = RenderMeter::new(RenderLimits::default());
        let mut resolver = Resolver::new(&arena, options, &mut meter);
        let node = text.node_id();
        for (column, indentation) in [(3u32, 1u32), (4u32, 2u32)] {
            let promise = resolver
                .begin_eval(
                    node,
                    Column::from(column),
                    Indentation::from(indentation),
                    ResolutionMode::Memoized,
                )
                .unwrap();
            assert!(
                matches!(
                    promise,
                    Step::Result(MeasureSet::Tainted(TaintPromise::Deferred {
                        doc,
                        column: deferred_column,
                        indentation: deferred_indentation,
                    })) if doc == node
                        && deferred_column == Column::from(column)
                        && deferred_indentation == Indentation::from(indentation)
                ),
                "an out-of-bound context defers with its own context"
            );
        }
        let first_measure = forced(
            resolver
                .begin_eval(
                    node,
                    Column::from(3u32),
                    Indentation::from(1u32),
                    ResolutionMode::Forced,
                )
                .unwrap(),
        );
        let second_measure = forced(
            resolver
                .begin_eval(
                    node,
                    Column::from(4u32),
                    Indentation::from(2u32),
                    ResolutionMode::Forced,
                )
                .unwrap(),
        );
        assert_eq!(first_measure.last_column, Column::from(4u32));
        assert_eq!(
            first_measure.cost.squared_overflow,
            SquaredOverflow::from(3u64)
        );
        assert_eq!(second_measure.last_column, Column::from(5u32));
        assert_eq!(
            second_measure.cost.squared_overflow,
            SquaredOverflow::from(5u64)
        );
    }

    /// Validation precedes work, and standalone and fused resolution each spend
    /// output once.
    #[test]
    fn resolution_validates_inputs_before_work_and_charges_output_once()
    {
        let mut build_meter = BuildMeter::new(BuildLimits::default());
        let mut builder = DocBuilder::try_new(&mut build_meter).expect("builder");
        let root = builder.text(TextSource::from("é𐐀")).expect("Unicode text");
        let arena = builder.finish().expect("arena");
        let mut foreign_meter = BuildMeter::new(BuildLimits::default());
        let foreign_builder = DocBuilder::try_new(&mut foreign_meter).expect("foreign builder");
        let foreign = foreign_builder.empty();
        let invalid = LayoutOptions {
            page_width: PageWidth::from(3_u32),
            computation_width: ComputationWidth::from(2_u32),
            line_ending: PhysicalLineEnding::Lf,
        };
        let options = LayoutOptions::try_new(
            PageWidth::from(1_u32),
            ComputationWidth::from(2_u32),
            PhysicalLineEnding::Lf,
        )
        .expect("widths");
        let mut refused = RenderMeter::new(RenderLimits {
            max_layout_steps: 0_u64.into(),
            ..RenderLimits::default()
        });
        refused
            .charge_output_bytes(OutputBytes::from(5_u64))
            .expect("prior output");
        let before = refused.usage();
        assert!(matches!(
            resolve(&arena, foreign, invalid, &mut refused),
            Err(RenderError::UnknownDoc)
        ));
        assert_eq!(refused.usage(), before);
        assert!(matches!(
            resolve(&arena, root, invalid, &mut refused),
            Err(RenderError::InvalidWidth)
        ));
        assert_eq!(refused.usage(), before);
        assert!(
            matches!(resolve(&arena, root, options, &mut refused), Err(RenderError::LimitExceeded { kind: crate::error::RenderLimitKind::LayoutSteps, limit }) if u64::from(limit) == 0)
        );
        assert_eq!(refused.usage().output_bytes, before.output_bytes);
        let expected_cost = LayoutCost {
            squared_overflow: SquaredOverflow::from(1_u64),
            line_breaks: LineBreaks::from(0_u64),
        };
        let mut standalone = RenderMeter::new(RenderLimits::default());
        standalone
            .charge_output_bytes(OutputBytes::from(5_u64))
            .expect("prior output");
        let resolved =
            resolve(&arena, root, options, &mut standalone).expect("standalone resolution");
        assert_eq!(resolved.cost(), expected_cost);
        assert_eq!(resolved.width_taint(), WidthTaint::Untainted);
        assert_eq!(resolved.output_bytes(), OutputBytes::from(6_u64));
        assert_eq!(u64::from(standalone.usage().output_bytes), 11_u64);
        let mut fused = RenderMeter::new(RenderLimits::default());
        fused
            .charge_output_bytes(OutputBytes::from(5_u64))
            .expect("prior output");
        let resolved =
            resolve_for_render(&arena, root, options, &mut fused).expect("fused resolution");
        assert_eq!(u64::from(fused.usage().output_bytes), 5_u64);
        let output = crate::vm::execute(
            &arena,
            resolved.plan_arena(),
            resolved.plan(),
            resolved.output_bytes(),
            &mut fused,
        )
        .expect("retained plan execution")
        .into_text();
        assert_eq!(output, "é𐐀");
        assert_eq!(u64::from(fused.usage().output_bytes), 11_u64);
        assert_eq!(resolved.cost(), expected_cost);
        assert_eq!(resolved.width_taint(), WidthTaint::Untainted);
    }

    /// Aliased ownership is released exactly, without consuming unrelated
    /// continuation work.
    #[test]
    fn retained_aliases_release_without_consuming_pending_continuations()
    {
        let mut build_meter = BuildMeter::new(BuildLimits::default());
        let builder = DocBuilder::try_new(&mut build_meter).expect("builder");
        let empty = builder.empty();
        let arena = builder.finish().expect("arena");
        let mut meter = RenderMeter::new(RenderLimits::default());
        let mut resolver = Resolver::new(&arena, LayoutOptions::default(), &mut meter);
        resolver
            .push(WorkItem::AfterAlign)
            .expect("pending continuation");
        let promise = TaintPromise::Deferred {
            doc: empty.node_id(),
            column: Column::from(7_u32),
            indentation: Indentation::from(9_u32),
        };
        let before = resolver.meter.usage();
        resolver
            .retain_set(&MeasureSet::Tainted(promise))
            .expect("deferred retain");
        resolver
            .release_set(MeasureSet::Tainted(promise))
            .expect("deferred release");
        resolver
            .release_promise(promise)
            .expect("deferred promise release");
        assert_eq!(resolver.meter.usage(), before);
        assert!(matches!(resolver.work.as_slice(), &[WorkItem::AfterAlign]));
        let child = resolver
            .plans
            .alloc(PlanNode::Empty, resolver.meter)
            .expect("child");
        let parent = resolver
            .plans
            .alloc_seq(child, child, resolver.meter)
            .expect("aliased sequence");
        let measure = Measure {
            last_column: Column::from(0_u32),
            cost: LayoutCost::zero(),
            plan: parent,
            output_bytes: OutputBytes::from(0_u64),
        };
        resolver
            .plans
            .retain(parent)
            .expect("second owned parent reference");
        let aliases = MeasureSet::Frontier(alloc::vec![measure, measure]);
        resolver.retain_set(&aliases).expect("copy both references");
        resolver
            .release_set(aliases)
            .expect("drop original references");
        resolver
            .retain_set(&MeasureSet::Tainted(TaintPromise::Ready(measure)))
            .expect("ready retain");
        resolver
            .release_promise(TaintPromise::Ready(measure))
            .expect("ready release");
        resolver
            .release_plan(parent)
            .expect("first retained reference");
        assert_eq!(
            resolver.plans.get(parent),
            Maybe::Present(PlanNode::Seq {
                left: child,
                right: child
            })
        );
        resolver
            .release_plan(parent)
            .expect("last parent reference");
        assert_eq!(
            resolver.plans.get(parent),
            Maybe::Absent(crate::plan::lookup::Absent::Released)
        );
        assert_eq!(resolver.plans.get(child), Maybe::Present(PlanNode::Empty));
        resolver.release_plan(child).expect("last child reference");
        assert_eq!(
            resolver.plans.get(child),
            Maybe::Absent(crate::plan::lookup::Absent::Released)
        );
        assert!(matches!(resolver.work.as_slice(), &[WorkItem::AfterAlign]));
        let mut refused = RenderMeter::new(RenderLimits {
            max_resolver_work_entries: 0_u64.into(),
            ..RenderLimits::default()
        });
        let mut resolver = Resolver::new(&arena, LayoutOptions::default(), &mut refused);
        let plan = resolver
            .plans
            .alloc(PlanNode::Empty, resolver.meter)
            .expect("refusal subject");
        let before = resolver.meter.usage();
        assert_eq!(
            resolver.release_plan(plan),
            Err(RenderError::LimitExceeded {
                kind: crate::error::RenderLimitKind::ResolverWorkEntries,
                limit: crate::units::LimitBound::from(0_u64)
            })
        );
        assert_eq!(resolver.plans.get(plan), Maybe::Present(PlanNode::Empty));
        assert_eq!(resolver.meter.usage(), before);
        assert!(resolver.work.is_empty());
    }

    /// Leaf costs distinguish Unicode widths, every fragment origin and
    /// inclusive computation bounds.
    #[test]
    fn leaf_measures_preserve_unicode_fragments_and_width_boundaries()
    {
        let mut build_meter = BuildMeter::new(BuildLimits::default());
        let mut builder = DocBuilder::try_new(&mut build_meter).expect("builder");
        let text_doc = builder.text(TextSource::from("é𐐀")).expect("text");
        let short_doc = builder
            .verbatim(crate::arena::VerbatimSource::from("é\r\n𐐀\n"))
            .expect("short verbatim");
        let wide_doc = builder
            .verbatim(crate::arena::VerbatimSource::from("é\r\n𐐀𐐀𐐀\n"))
            .expect("wide verbatim");
        let arena = builder.finish().expect("arena");
        let Maybe::Present(DocNode::Text(text)) = arena.node(text_doc.node_id())
        else {
            panic!("text identity")
        };
        for ending in [PhysicalLineEnding::Lf, PhysicalLineEnding::CrLf] {
            let options = LayoutOptions::try_new(
                PageWidth::from(1_u32),
                ComputationWidth::from(2_u32),
                ending,
            )
            .expect("widths");
            let mut meter = RenderMeter::new(RenderLimits::default());
            let mut resolver = Resolver::new(&arena, options, &mut meter);
            for column in [0_u32, 1, 2, u32::MAX.saturating_sub(2)] {
                let set = resolver
                    .text(text, Column::from(column))
                    .expect("text measure");
                let end = column.saturating_add(2);
                assert_eq!(matches!(set, MeasureSet::Tainted(_)), end > 2);
                let measure = forced(Step::Result(set));
                let from = u128::from(column.saturating_sub(1));
                let to = u128::from(end.saturating_sub(1));
                assert_eq!(
                    u128::from(u64::from(measure.cost.squared_overflow)),
                    to.saturating_mul(to)
                        .saturating_sub(from.saturating_mul(from))
                );
                assert_eq!(measure.last_column, Column::from(end));
                assert_eq!(measure.cost.line_breaks, LineBreaks::from(0_u64));
                assert_eq!(measure.output_bytes, OutputBytes::from(6_u64));
                assert_eq!(
                    resolver.plans.get(measure.plan),
                    Maybe::Present(PlanNode::Text(text))
                );
            }
            let before = resolver.meter.usage();
            assert!(matches!(
                resolver.text(text, Column::from(u32::MAX)),
                Err(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::Column
                })
            ));
            assert_eq!(resolver.meter.usage(), before);
            assert!(matches!(
                resolver.text(TextId::from(u32::MAX), Column::from(0_u32)),
                Err(RenderError::Invariant {
                    invariant: RenderInvariant::DocumentIdentity
                })
            ));
            assert_eq!(resolver.meter.usage(), before);
            for (doc, width, bytes) in [(short_doc, 1_u32, 9_u64), (wide_doc, 3_u32, 17_u64)] {
                let Maybe::Present(DocNode::Verbatim(verbatim)) = arena.node(doc.node_id())
                else {
                    panic!("verbatim identity")
                };
                for column in [0_u32, 1, 2] {
                    let set = resolver
                        .verbatim(verbatim, Column::from(column))
                        .expect("verbatim measure");
                    assert_eq!(
                        matches!(set, MeasureSet::Tainted(_)),
                        column.saturating_add(1) > 2 || width > 2
                    );
                    let measure = forced(Step::Result(set));
                    let from = u128::from(column.saturating_sub(1));
                    let to = u128::from(column);
                    let middle = u128::from(width.saturating_sub(1));
                    assert_eq!(
                        u128::from(u64::from(measure.cost.squared_overflow)),
                        to.saturating_mul(to)
                            .saturating_sub(from.saturating_mul(from))
                            .saturating_add(middle.saturating_mul(middle))
                    );
                    assert_eq!(measure.last_column, Column::from(0_u32));
                    assert_eq!(measure.cost.line_breaks, LineBreaks::from(2_u64));
                    assert_eq!(measure.output_bytes, OutputBytes::from(bytes));
                    assert_eq!(
                        resolver.plans.get(measure.plan),
                        Maybe::Present(PlanNode::Verbatim(verbatim))
                    );
                }
            }
            for indentation in [0_u32, 1, 2, 3, u32::MAX] {
                let set = resolver
                    .line(Indentation::from(indentation))
                    .expect("line measure");
                assert_eq!(matches!(set, MeasureSet::Tainted(_)), indentation > 2);
                let measure = forced(Step::Result(set));
                let excess = u128::from(indentation.saturating_sub(1));
                assert_eq!(
                    u128::from(u64::from(measure.cost.squared_overflow)),
                    excess.saturating_mul(excess)
                );
                assert_eq!(measure.last_column, Column::from(indentation));
                assert_eq!(measure.cost.line_breaks, LineBreaks::from(1_u64));
                let ending_bytes = match ending {
                    | PhysicalLineEnding::Lf => 1_u64,
                    | PhysicalLineEnding::CrLf => 2_u64,
                };
                assert_eq!(
                    measure.output_bytes,
                    OutputBytes::from(u64::from(indentation).saturating_add(ending_bytes))
                );
            }
        }
    }

    /// Every small abstract candidate bag agrees with stable pairwise dominance
    /// and exact ownership.
    #[test]
    fn small_candidate_bags_match_a_stable_pairwise_pareto_oracle()
    {
        let mut build_meter = BuildMeter::new(BuildLimits::default());
        let arena = DocBuilder::try_new(&mut build_meter)
            .expect("builder")
            .finish()
            .expect("arena");
        for length in 0_u32 ..= 3 {
            for encoded in 0_usize .. 9_usize.saturating_pow(length) {
                let mut meter = RenderMeter::new(RenderLimits::default());
                let mut resolver = Resolver::new(&arena, LayoutOptions::default(), &mut meter);
                let mut candidates = Vec::new();
                let mut digits = encoded;
                for _position in 0 .. length {
                    let rank = digits % 9;
                    digits = digits.div_euclid(9);
                    let (squared, lines) = match rank.div_euclid(3) {
                        | 0 => (0_u64, 0_u64),
                        | 1 => (0, 1),
                        | _ => (1, 0),
                    };
                    let plan = resolver
                        .plans
                        .alloc(PlanNode::Empty, resolver.meter)
                        .expect("candidate plan");
                    candidates.push(Measure {
                        last_column: Column::from(u32::try_from(rank % 3).expect("bounded column")),
                        cost: LayoutCost {
                            squared_overflow: SquaredOverflow::from(squared),
                            line_breaks: LineBreaks::from(lines),
                        },
                        plan,
                        output_bytes: OutputBytes::from(0_u64),
                    });
                }
                let all_plans: [Option<PlanId>; 3] =
                    core::array::from_fn(|index| candidates.get(index).map(|measure| measure.plan));
                let mut expected: Vec<Measure> = candidates
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|&(index, candidate)| {
                        !candidates.iter().enumerate().any(|(other_index, other)| {
                            match (
                                other.cost.cmp(&candidate.cost),
                                other.last_column.cmp(&candidate.last_column),
                            ) {
                                | (
                                    core::cmp::Ordering::Less,
                                    core::cmp::Ordering::Less | core::cmp::Ordering::Equal,
                                )
                                | (core::cmp::Ordering::Equal, core::cmp::Ordering::Less) => true,
                                | (core::cmp::Ordering::Equal, core::cmp::Ordering::Equal) => {
                                    other_index < index
                                },
                                | _ => false,
                            }
                        })
                    })
                    .map(|(_index, candidate)| candidate)
                    .collect();
                expected.sort_by_key(|measure| measure.cost);
                let frontier = resolver.normalize(candidates).expect("normalized frontier");
                assert_eq!(frontier, expected);
                for plan in all_plans.into_iter().flatten() {
                    if expected.iter().any(|measure| measure.plan == plan) {
                        assert_eq!(resolver.plans.get(plan), Maybe::Present(PlanNode::Empty));
                    }
                    else {
                        assert_eq!(
                            resolver.plans.get(plan),
                            Maybe::Absent(crate::plan::lookup::Absent::Released)
                        );
                    }
                }
                for measure in frontier {
                    resolver
                        .release_plan(measure.plan)
                        .expect("one retained reference");
                    assert_eq!(
                        resolver.plans.get(measure.plan),
                        Maybe::Absent(crate::plan::lookup::Absent::Released)
                    );
                }
            }
        }
    }
}
