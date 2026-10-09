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
#[derive(Debug)]
enum Step
{
    /// A finished measure set.
    Result(MeasureSet),
    /// The step pushed its continuation and children.
    Scheduled,
}

/// Memoization key for one in-bound context.
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
    /// trivial.
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
    /// - hypothesis: L3 — the surface is the bound: two out-of-bound contexts
    ///   of one node defer to promises carrying their own contexts, and forcing
    ///   each yields the measure of its own column.
    /// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
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
            | DocNode::Empty => return Ok(Step::Result(self.empty()?)),
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
    /// - ensures: a one-measure frontier; on a refused charge the plan is
    ///   released and the charge's error returned.
    /// - provides: every leaf's result.
    /// - fails: a frontier ceiling or a frontier that cannot grow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::AllocationFailed`] or the frontier ceiling.
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
    /// - ensures: a zero-cost, zero-byte measure ending at column zero.
    /// - provides: the result of `Empty`.
    /// - fails: a plan or frontier ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first error the plan or frontier charge returns.
    fn empty(&mut self) -> Result<MeasureSet, RenderError>
    {
        let plan = self.plans.alloc(PlanNode::Empty, self.meter)?;
        self.singleton(Measure {
            last_column: Column::from(0u32),
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
    /// - hypothesis: L2 — every small document over the algebra is resolved and
    ///   its winning cost compared with a direct enumeration of its layouts.
    /// - witness: `algebra::tests::exhaustive_small_documents_match_the_direct_oracle`
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
/// - requires: `root` belongs to `arena`, and `options` has computation width
///   at least as large as page width.
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
/// - hypothesis: L2 — every small document over the algebra, at two page and
///   two computation widths and both endings, is resolved and its cost compared
///   with a direct enumeration; memo reuse and the line and choice cost rules
///   are each asserted at their exact counts.
/// - witness: `algebra::tests::exhaustive_small_documents_match_the_direct_oracle`
/// - witness: `algebra::tests::shared_contexts_reuse_memo_states`
/// - witness: `algebra::tests::resolver_charges_line_break_and_indentation`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
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
/// - requires: `root` belongs to `arena`, and `options` has computation width
///   at least as large as page width.
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
/// - hypothesis: L3 — the surfaces are the selected text, taint, cost and the
///   output charge, each asserted on a rendered result and its meter.
/// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
/// - witness: `algebra::tests::render_tainted_root_preserves_promise_columns_and_indentation`
/// - witness: `algebra::tests::render_limits_fail_without_partial_output`
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
/// - requires: `root` and `options` satisfy the public resolver preconditions.
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
    /// trivial.
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
}
