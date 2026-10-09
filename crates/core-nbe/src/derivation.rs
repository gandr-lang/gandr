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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the ids and the store
    ///   disagree.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
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
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no derivation for `process`.
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
    ///   is emitted as one [`ConversionDecision::ComparedShared`] on that pair,
    ///   which is the reading a replay gives a decision met at a decomposable
    ///   goal it can close. A derivation shared by two parents is emitted under
    ///   each. Nothing is emitted when not recording.
    /// - provides: the sequential trace the kernel replays.
    /// - fails: [`ConversionFault::MachineInvariant`] for a process with no
    ///   derivation, and whatever the search-free steps refuse.
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
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    // economy: a derivation shared by two parents is emitted once per parent,
    // so a proof whose sharing is a deep DAG emits its expansion. The replay
    // reads a tree, so the expansion is what it needs; upgrade path: a
    // back-reference decision, which is a vocabulary change and waits for a
    // measured trace that needs it.
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
/// # Errors
/// - [`ConversionFault::Polarity`] — a value met a computation.
/// - [`ConversionFault`] — as the steps refuse.
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
