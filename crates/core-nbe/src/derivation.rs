//! The conversion machine's derivations: what each goal decided, kept only
//! when a recording sink asks for it, and emitted as one sequential trace once
//! the root answers.
//!
//! # Why the trace is emitted at the end
//!
//! The machine explores many branches at once, interleaved; the kernel replays
//! one derivation in order. The decisions a replay can follow are the winning
//! derivation's, read in preorder, and which derivation wins is known only
//! when its combinators answer. So each goal keeps its own decisions and, once
//! it answers, which children its answer rests on; the root's answer then
//! names a tree, and [`Derivations::emit`] walks it.
//!
//! # Nothing is kept for the null sink
//!
//! Every recording method returns at once when the sink is inactive, before
//! touching the store, so a run instantiated at the null sink allocates no
//! derivation: the store's length stays zero, which the machine reports and a
//! witness asserts.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::SinkActivity;
use gandr_kernel_conversion_trace::TraceSink;

use crate::arena::DomainArena;
use crate::conv::ConversionFault;
use crate::conv::Settlement;
use crate::conv::convert_computations;
use crate::conv::convert_values;
use crate::domain::Glued;
use crate::machine::ProcessId;
use crate::machine::TraceNode;

/// How a goal's derivation ends, beneath its own decisions.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Ending
{
    /// The goal answered on its own, or has not answered yet.
    Alone,
    /// The goal's answer rests on these children's derivations, in order.
    Children(Vec<ProcessId>),
    /// The goal decomposed into children that all agreed, over this pair: a
    /// replay may close the pair in one step when the search-free steps
    /// settle it, so the emission tries that first.
    Agreed
    {
        /// The pair the goal decomposed.
        pair: (Glued, Glued),
        /// The children, in subgoal order.
        children: Vec<ProcessId>,
    },
}

/// One process's derivation: its decisions in order and its ending.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Derivation
{
    /// The decisions the process made, in the order it made them.
    decisions: Vec<ConversionDecision<TraceNode>>,
    /// What the derivation continues with.
    ending: Ending,
}

/// The derivations of one run, one per process, held only when recording.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Derivations
{
    /// Whether the sink retains anything; nothing is stored when it does not.
    activity: SinkActivity,
    /// One derivation per process, by process id.
    store: Vec<Derivation>,
}

/// How many derivations a run kept.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DerivationCount(usize);

impl From<DerivationCount> for usize
{
    /// How many derivations `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: DerivationCount) -> Self
    {
        count.0
    }
}

impl Derivations
{
    /// An empty store for a sink of `activity`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn new(activity: SinkActivity) -> Self
    {
        Self {
            activity,
            store: Vec::new(),
        }
    }

    /// How many derivations the store holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: zero for a store built for an inactive sink, whatever the run
    ///   did; one per process started otherwise.
    /// - provides: the observation the sink-off witness asserts on.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — inactive recording keeps no derivation even for
    ///   invalid process ids, while an active run keeps exactly one per opened
    ///   process. Allocating under the inactive policy or losing an opened slot
    ///   changes the count.
    /// - witness: `machine::tests::derivation_refusals_preserve_state_and_inactive_recording_is_empty`
    /// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
    #[spec(ensures: |ret| ret.0 == self.store.len()
        && (!matches!(self.activity, SinkActivity::Inactive) || ret.0 == 0))]
    pub(crate) fn count(&self) -> DerivationCount
    {
        DerivationCount(self.store.len())
    }

    /// Open the derivation of a process just started.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when recording, the store holds one more derivation, empty;
    ///   otherwise nothing changes.
    /// - provides: the per-process slot every later recording call fills, so
    ///   the store stays indexed by process id.
    /// - fails: [`ConversionFault::MachineInvariant`] when recording and
    ///   `process` is not the next id the store expects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the next process opens once, duplicate and skipped
    ///   ids refuse without modifying previous derivations, and inactive
    ///   recording ignores the id. Accepting an out-of-order process or adding
    ///   a nonempty derivation changes state or emission.
    /// - witness: `machine::tests::derivation_refusals_preserve_state_and_inactive_recording_is_empty`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the ids and the store
    ///   disagree.
    #[spec(
        captures: entry_length = self.store.len(),
        ensures: |ret| if matches!(self.activity, SinkActivity::Inactive) {
            ret == Ok(()) && self.store.len() == entry_length
        } else if usize::from(process) == entry_length {
            ret == Ok(()) && self.store.len().checked_sub(1) == Some(entry_length)
                && self.store.last().is_some_and(|held| held.decisions.is_empty() && matches!(held.ending, Ending::Alone))
        } else { ret == Err(ConversionFault::MachineInvariant) && self.store.len() == entry_length },
    )]
    pub(crate) fn open(
        &mut self,
        process: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, SinkActivity::Inactive) {
            return Ok(());
        }
        if usize::from(process) != self.store.len() {
            return Err(ConversionFault::MachineInvariant);
        }
        self.store.push(Derivation {
            decisions: Vec::new(),
            ending: Ending::Alone,
        });
        Ok(())
    }

    /// Record one decision `process` made.
    ///
    /// # Specification
    /// - requires: `process` was opened.
    /// - ensures: when recording, the decision is the derivation's last;
    ///   otherwise nothing changes.
    /// - provides: the per-goal half of the trace.
    /// - fails: [`ConversionFault::MachineInvariant`] when recording and the
    ///   process was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — two decisions at one goal stay in order before both
    ///   child derivations, and an unopened goal refuses without changing the
    ///   store. Prepending, dropping or attributing a decision to another goal
    ///   changes the emitted preorder.
    /// - witness: `machine::tests::derivations_emit_preorder_and_repeat_shared_children`
    /// - witness: `machine::tests::derivation_refusals_preserve_state_and_inactive_recording_is_empty`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
    #[spec(
        captures: entry_decisions = self.store.get(usize::from(process)).map(|held| held.decisions.len()),
        ensures: |ret| if matches!(self.activity, SinkActivity::Inactive) { ret == Ok(()) }
        else { self.store.get(usize::from(process)).map_or_else(
            || ret == Err(ConversionFault::MachineInvariant),
            |held| ret == Ok(()) && held.decisions.last() == Some(&decision)
                && held.decisions.len().checked_sub(1) == entry_decisions) },
    )]
    pub(crate) fn decide(
        &mut self,
        process: ProcessId,
        decision: ConversionDecision<TraceNode>,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, SinkActivity::Inactive) {
            return Ok(());
        }
        let derivation = self
            .store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)?;
        derivation.decisions.push(decision);
        Ok(())
    }

    /// Record that `process`'s answer rests on `children`.
    ///
    /// # Specification
    /// - requires: `process` was opened.
    /// - ensures: when recording, the derivation continues with the children's
    ///   derivations in the order given; otherwise nothing changes.
    /// - provides: the winning-children half of the trace.
    /// - fails: [`ConversionFault::MachineInvariant`] when recording and the
    ///   process was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a derivation with two ordered children, both resting
    ///   on one shared child, emits each child in preorder and the shared child
    ///   under both parents. Reversing the children or deduplicating the shared
    ///   derivation changes the trace; the predicate retains cardinality and
    ///   both ends without cloning the consumed list.
    /// - witness: `machine::tests::derivations_emit_preorder_and_repeat_shared_children`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
    #[spec(
        captures: [child_count = children.len(), first_child = children.first().copied(), last_child = children.last().copied()],
        ensures: |ret| if matches!(self.activity, SinkActivity::Inactive) { ret == Ok(()) }
        else { self.store.get(usize::from(process)).map_or_else(
            || ret == Err(ConversionFault::MachineInvariant),
            |held| ret == Ok(()) && matches!(held.ending, Ending::Children(ref recorded)
                if recorded.len() == child_count && recorded.first().copied() == first_child && recorded.last().copied() == last_child)) },
    )]
    pub(crate) fn rest_on(
        &mut self,
        process: ProcessId,
        children: Vec<ProcessId>,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, SinkActivity::Inactive) {
            return Ok(());
        }
        let derivation = self
            .store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)?;
        derivation.ending = Ending::Children(children);
        Ok(())
    }

    /// Record that `process` decomposed `pair` and every child agreed.
    ///
    /// # Specification
    /// - requires: `process` was opened.
    /// - ensures: when recording, the derivation continues with the children's
    ///   derivations unless the emission closes `pair` in one step; otherwise
    ///   nothing changes.
    /// - provides: the agreeing-decomposition ending the emission may collapse.
    /// - fails: [`ConversionFault::MachineInvariant`] when recording and the
    ///   process was never opened.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an equal pair collapses its ending to one
    ///   shared-comparison decision, while a deferred pair retains the children
    ///   in order; earlier decisions of the parent remain in both cases. Losing
    ///   the pair or its children changes which trace is emitted.
    /// - witness: `machine::tests::derivation_collapse_keeps_parent_decisions_and_refuses_missing_nodes`
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
    #[spec(
        captures: [child_count = children.len(), first_child = children.first().copied(), last_child = children.last().copied()],
        ensures: |ret| if matches!(self.activity, SinkActivity::Inactive) { ret == Ok(()) }
        else { self.store.get(usize::from(process)).map_or_else(
            || ret == Err(ConversionFault::MachineInvariant),
            |held| ret == Ok(()) && matches!(held.ending, Ending::Agreed { pair: recorded_pair, children: ref recorded }
                if recorded_pair == pair && recorded.len() == child_count && recorded.first().copied() == first_child && recorded.last().copied() == last_child)) },
    )]
    pub(crate) fn agree_on(
        &mut self,
        process: ProcessId,
        pair: (Glued, Glued),
        children: Vec<ProcessId>,
    ) -> Result<(), ConversionFault>
    {
        if matches!(self.activity, SinkActivity::Inactive) {
            return Ok(());
        }
        let derivation = self
            .store
            .get_mut(usize::from(process))
            .ok_or(ConversionFault::MachineInvariant)?;
        derivation.ending = Ending::Agreed { pair, children };
        Ok(())
    }

    /// Emit the derivation rooted at `root` into `sink`, in preorder.
    ///
    /// # Specification
    /// - requires: every process the root's answer rests on, transitively, has
    ///   answered and recorded its ending.
    /// - ensures: when recording, `sink` receives each goal's decisions
    ///   followed by its children's derivations in order — except that an
    ///   agreeing decomposition whose pair the search-free steps settle equal
    ///   emits its ending as one [`ConversionDecision::ComparedShared`] on that
    ///   pair after its own decisions. This is the reading a replay gives to a
    ///   decision met at a decomposable goal it can close. A derivation shared
    ///   by two parents is emitted under each. Nothing is emitted when not
    ///   recording.
    /// - provides: the sequential trace the kernel replays. The predicate
    ///   checks inactivity, root resolution and observable decision counts; the
    ///   witnesses pin preorder and repeated children.
    /// - fails: [`ConversionFault::MachineInvariant`] for a process with no
    ///   derivation, and whatever the search-free steps refuse. Decisions
    ///   emitted before a refusal remain in the sink.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — a process has no derivation.
    /// - [`ConversionFault`] — as [`convert_values`] refuses.
    ///
    /// # Termination
    /// - reason: the `while let Some(process) = stack.pop()` preorder loop over
    ///   an explicit stack of processes, not recursion.
    /// - measure: the order in which processes answered: a goal records its
    ///   ending when it answers, naming only children that had answered before
    ///   it, so every push names a process that answered earlier than the one
    ///   popped to push it — by id or not, since a re-shared child may be older
    ///   than its parent.
    /// - boundedness: the answered processes are finitely many, so the walk
    ///   ends; a shared child is walked once per parent, which bounds the trace
    ///   by the derivation's expansion as a tree.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle is the kernel's replay, which shares no
    ///   code with this emission and refuses a trace that does not follow.
    ///   Reversing child order, omitting a repeated shared child or collapsing
    ///   a deferred pair changes the trace or its replay; a refusal preserves
    ///   the prefix already emitted.
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::derivations_emit_preorder_and_repeat_shared_children`
    /// - witness: `machine::tests::derivation_collapse_keeps_parent_decisions_and_refuses_missing_nodes`
    /// - witness: `machine::tests::derivation_refusals_preserve_state_and_inactive_recording_is_empty`
    // economy: a derivation shared by two parents is emitted once per parent,
    // so a proof whose sharing is a deep DAG emits its expansion. The replay
    // reads a tree, so the expansion is what it needs; upgrade path: a
    // back-reference decision, which is a vocabulary change and waits for a
    // measured trace that needs it.
    #[spec(
        captures: entry_count = usize::from(sink.recorded_count()),
        ensures: |ret| {
            let recorded = usize::from(sink.recorded_count());
            if matches!(self.activity, SinkActivity::Inactive) {
                ret == Ok(()) && recorded == entry_count
            } else if let Some(held) = self.store.get(usize::from(root)) {
                if matches!(S::ACTIVITY, SinkActivity::Inactive) { recorded == entry_count }
                else {
                    let own = entry_count.saturating_add(held.decisions.len());
                    recorded >= own && match held.ending {
                        Ending::Alone => ret == Ok(()) && recorded == own,
                        Ending::Agreed { pair, .. } if matches!(settle(core, domain, pair), Ok(Settlement::Identical | Settlement::StructurallyEqual)) =>
                            ret == Ok(()) && recorded == own.saturating_add(1),
                        Ending::Children(_) | Ending::Agreed { .. } => true,
                    }
                }
            } else { ret == Err(ConversionFault::MachineInvariant) && recorded == entry_count }
        },
    )]
    pub(crate) fn emit<S>(
        &self,
        core: &CoreArena,
        domain: &DomainArena,
        root: ProcessId,
        sink: &mut S,
    ) -> Result<(), ConversionFault>
    where
        S: TraceSink<TraceNode>,
    {
        if matches!(self.activity, SinkActivity::Inactive) {
            return Ok(());
        }
        let mut stack = Vec::from([root]);
        while let Some(process) = stack.pop() {
            let derivation = self
                .store
                .get(usize::from(process))
                .ok_or(ConversionFault::MachineInvariant)?;
            for &decision in &derivation.decisions {
                sink.record(decision);
            }
            match derivation.ending {
                | Ending::Alone => {},
                | Ending::Children(ref children) => stack.extend(children.iter().rev()),
                | Ending::Agreed { pair, ref children } => {
                    let settled = settle(core, domain, pair)?;
                    match settled {
                        | Settlement::Identical | Settlement::StructurallyEqual => {
                            sink.record(ConversionDecision::ComparedShared {
                                left: TraceNode::of(pair.0),
                                right: TraceNode::of(pair.1),
                            });
                        },
                        | Settlement::GuardedApart
                        | Settlement::StructurallyApart
                        | Settlement::Deferred(_) => stack.extend(children.iter().rev()),
                    }
                },
            }
        }
        Ok(())
    }
}

/// Run the search-free steps on a pair of one polarity.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the settlement [`convert_values`] or [`convert_computations`]
///   gives the pair.
/// - provides: the collapse test the emission applies to an agreeing
///   decomposition.
/// - fails: [`ConversionFault::Polarity`] for a pair of two polarities, and
///   whatever the steps refuse.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the emission collapses equal value and computation pairs,
///   retains a deferred pair’s children, and refuses a mixed-polarity or
///   removed pair. Treating a deferral as equality or ignoring polarity changes
///   the emitted trace or refusal.
/// - witness: `machine::tests::derivation_collapse_keeps_parent_decisions_and_refuses_missing_nodes`
///
/// # Errors
/// - [`ConversionFault::Polarity`] — a value met a computation.
/// - [`ConversionFault`] — as the steps refuse.
#[spec(ensures: |ret| match pair {
    (Glued::Value(left), Glued::Value(right)) => ret == convert_values(core, domain, left, right),
    (Glued::Computation(left), Glued::Computation(right)) => ret == convert_computations(core, domain, left, right),
    _ => ret == Err(ConversionFault::Polarity),
})]
fn settle(
    core: &CoreArena,
    domain: &DomainArena,
    pair: (Glued, Glued),
) -> Result<Settlement, ConversionFault>
{
    match pair {
        | (Glued::Value(left), Glued::Value(right)) => convert_values(core, domain, left, right),
        | (Glued::Computation(left), Glued::Computation(right)) => {
            convert_computations(core, domain, left, right)
        },
        | (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => {
            Err(ConversionFault::Polarity)
        },
    }
}
