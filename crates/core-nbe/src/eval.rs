//! Evaluation to weak head, as a machine over an explicit task stack.
//!
//! # A machine, not a pair of mutually recursive functions
//!
//! Evaluating a value calls for evaluating its components and evaluating a
//! computation calls for evaluating both, so the direct presentation is two
//! mutually recursive functions whose depth scales with term depth — and a core
//! term's depth is whatever an elaborator built. The machine here carries a
//! task stack and two result stacks instead, so its depth lives on the heap and
//! the host stack sees one loop.
//!
//! The two result stacks are separated by polarity rather than merged, because
//! every frame knows which polarity its operands have and a merged stack would
//! turn that static fact into a runtime tag.
//!
//! # The term face is set by a check, not by a convention
//!
//! A composite keeps its source face **exactly when every child came back
//! denoting the corresponding source child** — that is, when the child's face
//! is `Source(c)` for the very `c` the source node names. Anything else,
//! including a variable that resolved to something out of the environment,
//! makes the composite `Reduced`.
//!
//! That check is what "nothing inside it reduced" means, made mechanical. It
//! cannot be fooled by a coincidence: if a child's face names the source
//! child's id, then the child *denotes* that source term, which is exactly the
//! condition the face asserts.
//!
//! A closure keeps its source face only when it captured the **empty**
//! environment, because a closure over a non-empty environment denotes its body
//! only up to what the environment supplies.
//!
//! The computation face is otherwise conservative: a stuck spine is marked
//! `Reduced` even where nothing reduced.
//! `economy: conservative computation face; refine to track the spine's own
//! sources when readback measures the rebuild cost`.
//!
//! # Definitions are not unfolded here
//!
//! A constant becomes a neutral carrying its **unfolding face** — the body's
//! content id when this scope reads the definition as manifest, and rigid
//! otherwise. Nothing is expanded. Weak-head evaluation that unfolded eagerly
//! would defeat the face it is supposed to populate, and the unfolding is what
//! conversion forces when the neutral forms fail to match.
//!
//! Extending a neutral's spine carries the unfolding along: the face names the
//! *head's* body, and forcing it means unfolding the head and re-applying the
//! spine, which stays well defined however long the spine grows.
//!
//! # Compound endpoints run, or hold for the conversion
//!
//! A compound endpoint — a computation standing where a value is read —
//! stands for what it returns, so under [`Endpoints::Run`] its computation
//! runs through every manifest definition it is stuck on, inside evaluation.
//! Under [`Endpoints::Hold`] a computation stuck on a manifest definition stops
//! there: the endpoint stays a neutral headed by that definition, and the
//! conversion machine unfolds it as it unfolds any constant, by a recorded
//! `Unfold` and the reduction naming its side.
//!
//! **Choice.** A conversion whose trace a kernel replays holds its endpoints:
//! a δ-step taken inside evaluation leaves no decision, and the kernel unfolds
//! only what a decision names, so a run would admit an endpoint the replay
//! refuses — every δ-step under a binder of an endpoint among them.
//! **Alternatives.** Re-emitting the steps evaluation took as decisions, which
//! records a derivation the machine did not perform; δ-steps under binders in
//! the kernel's own conversion, a search the trusted base does not take.
//! **Reversal.** A kernel that runs compound endpoints by its own evaluator at
//! every position, binders included, would read the run's steps itself, and
//! the stance would serve only the runs that keep no trace. The witnesses are
//! `eval::tests::a_held_endpoint_stays_at_its_definition` and
//! `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`.
//!
//! A held endpoint standing as a leaf of a presented constructor term is the
//! one a conversion reads without a decision; [`crate::presented`] says why.
//!
//! # Source sharing is expanded unless the policy handed a leg over
//!
//! A core term is a DAG, and this machine walks it as a tree: a node reached
//! twice is evaluated twice. That is the cost the duplication policy and the
//! memo seam exist to remove, and removing it with an ad-hoc cache keyed on the
//! source node would put a sharing decision inside the evaluator rather than
//! behind the parameter that is supposed to own it.
//!
//! So the machine shares only what it is handed. The overlay evaluator's
//! spinal run hands it the legs the duplication walk kept shared, each with its
//! free indices. The first evaluation of a leg in one **configuration** — one
//! binding at each of its free indices, in both zones — is remembered by one
//! more task once its weak head is on the stack, and every later occurrence
//! read in that configuration takes the remembered head at the cost of the
//! step that popped it. A leg read in another configuration is evaluated
//! again. An unshared run is handed no leg and pays nothing for the seam.
//!
//! The consequence is stated rather than left to be discovered: a term whose
//! sharing is deep and not handed over costs its **expansion**, and the fuel
//! budget is what bounds that rather than a promise that it will not happen.
//!
//! # Fuel, because β alone diverges
//!
//! With thunks and force, a term can loop without any definition being
//! unfolded, so a machine that ran to completion would be an unbounded loop
//! over untrusted input. The machine takes a fuel budget and refuses when it
//! runs out. Refusing is the fail-closed posture; a decline is a correct answer
//! at this surface and a divergence is not.
//!
//! # Evaluation
//!
//! A composite keeps its source face exactly when every child's face is
//! `Source(c)` for the very `c` the source node names; a variable resolved out
//! of the environment makes its parent `Reduced`. A closure keeps its source
//! face only when it captured the empty environment. A stuck computation spine
//! is marked `Reduced` even where nothing reduced. A constant becomes a neutral
//! whose unfolding face reads the definition through the scope's transparency;
//! nothing is expanded, because eager unfolding would defeat the face
//! evaluation fills. Extending a neutral's spine carries the unfolding along,
//! since forcing means unfolding the head and re-applying the spine.
//!
//! A resumable slice checks its budget before removing a task: a zero slice
//! pauses without losing work, and a task that finishes on the final available
//! step finishes rather than pauses. Missing operands in a malformed re-applied
//! spine are named `EvalFault::MachineInvariant` refusals in both build modes,
//! not assumptions that contract enforcement may turn into panics. Witnesses:
//! `eval::tests::a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause`
//! and `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`.
//!
//! ### Pure normalization boundary
//!
//! Conversion refuses all eight runtime-control formers with
//! `EvalFault::RuntimeControl(ControlFormer)`, every session action with
//! `EvalFault::SessionAction` and every memory form with
//! `EvalFault::MemoryForm`; it never invokes a host. Stack/With type codes
//! still compare and read back structurally with captured scope and
//! effect-operation types intact.
//!
//! **Choice.** The sequent machine executes control; conversion stays pure.
//! Host interpretation makes equality state-dependent; erasure certifies
//! another program. Revisit only for a pure equational theory with
//! independently checked evidence, not an adapter.
//!
//! Witnesses: `runtime_control_is_refused_by_former`,
//! `control_type_codes_read_back_their_captured_scope`,
//! `control_scopes_keep_only_ambient_indices`,
//! `control_type_codes_compare_distinct_inputs_and_outputs`.
//!
//! # Lowered definition bodies
//!
//! The chain carries a body as a canonical subterm-table entry index rather
//! than as a core node, because a core id means something only in the arena
//! that minted it and a chain is cloned into every run. A run therefore lowers
//! the chain into its own arena in one pass, in admission order:
//! `LoweredChain::lower` asks for each distinct index once, so definitions the
//! canonical table gave one body share one lowering, and every body the chain
//! holds has a lowering before any run reads it. A caller that admits
//! definitions one at a time, as the checker's code table does, appends each
//! with `LoweredChain::define`: one chain entry and one map insertion, where
//! lowering the extended chain again per admission costs a module of n
//! definitions n² map operations. Evaluation still unfolds nothing — a manifest
//! constant stays a neutral carrying its index unforced.
//! `ReadbackMode::Unfolding` forces a body when it meets one: it evaluates the
//! lowering in the empty environment from the readback's own budget and records
//! the result with `DomainArena::force_neutral`, so a neutral met twice
//! evaluates its body once and its neutral form stays readable beside the
//! unfolding.
//!
//! Alternatives: lowering at evaluation time, which is eager unfolding under
//! another name and defeats the term face; a table the caller fills one body at
//! a time and attaches, which leaves `ReadbackFault::UnloweredBody` reachable
//! for every definition the caller missed; and decoding the subterm table here,
//! which needs a lookup by entry index that the decoded artifact does not
//! expose and a kernel-to-core reading that no crate owns. Reversal: the
//! decoded artifact gains a lookup by entry index and a crate owns reading a
//! table entry as a core term; the per-entry lowering then moves behind that
//! crate and the pass keeps its shape.
//!
//! # Native data and records
//!
//! Constructors and records keep lazy field closures, a case or projection
//! demands only what it selects, a split of a tuple binds each component in
//! order and enters its body while a split of a neutral suspends whole as
//! `Elimination::Split`, compared by arity and by its bodies opened under one
//! fresh variable per component (`Opening::Many`), and `fix x. M` is its own
//! weak head until an application at a canonical argument or a bind unfolds it
//! once; evaluation unfolds a partial fixpoint as readily as a structurally
//! descending one and leaves the difference to the kernel's replay.
//!
//! # Constructors, cases and records
//!
//! Constructors and records retain ordered lazy field closures in flat arena
//! spans. Projection demands only the selected field; data case selects exactly
//! its tag's branch and supplies only that constructor's fields. A neutral head
//! retains the elimination until unfolding exposes its constructor or record.
//! Readback reconstructs every native child and classifier. Arena truncation
//! restores the field-span watermark as well as the node tables.
//!
//! The sequent machine's command IL runs native constructors and cases and
//! refuses records by name. The structural index-conversion boundary and
//! deferred readers are in the [checker
//! floor](https://github.com/gandr-lang/gandr/issues/199).
//!
//! # Two gates unfold a fixpoint
//!
//! `fix x. M` evaluates to `DomainComp::Fixpoint`, a computation closure over
//! the fixpoint node itself, and is its own weak head until something observes
//! it. Two gates unfold it once, `M[thunk (fix x. M)/x]`, with the self thunk
//! bound innermost in the closure's environment: an application at a canonical
//! argument, and a bind that runs it. At a neutral argument the application
//! sticks, and the fixpoint waits on the neutral's spine as
//! `Elimination::Fixpoint` until the head unfolds and the application resumes.
//!
//! # Native readback and conversion
//!
//! Readback opens the self binder and rebuilds the fixpoint with its evidence.
//! Conversion compares two fixpoints, and two stuck fixpoint eliminations, by
//! their bodies under one self variable, whatever their evidence.
//!
//! # Evaluation does not read the evidence
//!
//! A partial fixpoint unfolds at the same gates, and a loop is bounded by the
//! fuel every task is charged, not by the claim. Certification is where the
//! claim matters. The kernel replays a structural-descent unfolding at a
//! constructor and declines a partial one, so a decision the machine reached
//! through a partial unfolding is computed but never certified.
//!
//! # The fixpoint decision
//!
//! **Choice.** A self-closure unfolded on demand, which keeps the domain arena
//! acyclic and append-only and costs one closure per fixpoint.
//!
//! **Alternatives.** A cyclic environment that ties the self binder to its own
//! closure, which breaks acyclic minting; and eager unrolling to a depth, which
//! guesses the depth.
//!
//! **Reversal.** A measured workload whose cost is dominated by re-minting the
//! self thunk at each unfolding, which would cache that thunk on the closure.
//!
//! # Native data witnesses
//!
//! - Native data and records: `eval::tests::native_records_and_cases_compute`
//!   distinguishes all five constructor arguments, selected module components
//!   and poisoned unselected thunks;
//!   `eval::tests::native_cases_reapply_when_head_unfolds` covers delayed
//!   elimination; `machine::tests::native_records_cases_and_traces_agree`
//!   checks independently replayed native comparisons.
//! - Fixpoints:
//!   `eval::tests::a_fixpoint_unfolds_at_a_constructor_and_sticks_at_a_neutral`,
//!   `eval::tests::an_observed_loop_runs_out_of_fuel`,
//!   `readback::tests::a_fixpoint_reads_back_with_its_self_binder` and
//!   `machine::tests::stuck_fixpoints_compare_by_their_bodies`.
//!
//! # Source sharing
//!
//! A core term is a DAG, and both machines walk it as a tree: evaluation
//! evaluates a node reached twice twice, and readback mints a fresh core node
//! per rebuilt domain node. A term with deep sharing costs its expansion,
//! bounded by the fuel budget. Removing that cost is the duplication
//! parameter's job, over the sharing overlay: the evaluator remembers a leg's
//! evaluation only when the installed stance handed the leg over as a share
//! (see `traced`), and readback and conversion still walk the expansion. A
//! cache keyed on the source node inside a machine would make the sharing
//! decision behind the parameter's back.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionEntry;
use gandr_core_term::DefinitionError;
use gandr_core_term::DefinitionHeight;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ScopeId;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::closure::CompBody;
use crate::closure::Environment;
use crate::closure::EnvironmentDepth;
use crate::closure::Mover;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::LiftTarget;
use crate::domain::NeutralHead;
use crate::domain::Suspended;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::free::CoreTerm;
use crate::free::Free;

mod words;

/// The number of machine steps an evaluation may take.
///
/// A step is one task popped. The budget exists because β and `force` alone
/// suffice to loop, so completion is not a property of the input this machine
/// can assume.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel(u32);

impl From<u32> for Fuel
{
    /// Read a `u32` as a step budget.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u32) -> Self
    {
        Self(steps)
    }
}

impl From<Fuel> for u32
{
    /// Read the budget back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fuel: Fuel) -> Self
    {
        fuel.0
    }
}

/// The index of one environment held by a running machine.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct EnvId(usize);

/// Why an evaluation was refused.
///
/// Every variant is a fail-closed answer rather than a panic. The shape faults
/// name an ill-typed input, which this crate does not re-derive types for and
/// so cannot rule out at the door.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EvalFault
{
    /// A named runtime control former is outside the certificate normalizer.
    RuntimeControl(gandr_core_term::control::ControlFormer),
    /// A session action communicates over an endpoint; it runs in a session
    /// runtime, never in the certificate normalizer.
    SessionAction,
    /// A memory form reads and writes a held slot; it runs on the abstract
    /// machine, never in the certificate normalizer.
    MemoryForm,
    /// Runtime-native arithmetic is outside the certificate normalizer.
    NativePrimitive(gandr_core_term::primitive::Primitive),
    /// Transport met neither a native path nor a neutral path operand.
    TransportedNonPath,
    /// A ride met a canonical flow and a value no row of the directed
    /// computation table moves, and no neutral flow to stack on.
    RodeUncomputed,
    /// Transport met `ua` written in place. The path it names is the one the
    /// checker derives at its stratum, which a declaration whose body is the
    /// statement unfolds to; written in place, it has no path to compute
    /// along.
    TransportedUnderived,
    /// The budget ran out. The term may or may not have a weak-head form; the
    /// machine declines rather than continuing.
    OutOfFuel,
    /// A core id named no node of the arena being evaluated.
    DanglingTerm,
    /// The domain arena refused, in its own vocabulary. Carried rather than
    /// translated, so a refusal never arrives under a name that describes a
    /// different condition.
    Domain(DomainFault),
    /// A variable counted past the environment's bindings in its zone.
    UnboundVariable
    {
        /// The zone the index counted in.
        zone: Zone,
        /// The index that resolved to nothing.
        index: DeBruijnIndex,
    },
    /// `force` met a value that was neither a thunk nor stuck.
    ForcedNonThunk,
    /// An application met a weak head that was neither a lambda nor stuck.
    AppliedNonFunction,
    /// A bind met a bound computation that was neither a returner nor stuck.
    BoundNonReturner,
    /// A case met a scrutinee that was neither an injection nor stuck.
    CasedNonInjection,
    /// A fold met neither a native list nor a neutral list.
    FoldedNonList,
    /// A static application met an operator that was neither a static lambda
    /// nor stuck.
    AppliedNonOperator,
    /// An internal invariant broke: a frame found no operand where one of its
    /// own tasks should have left one, or a task named an environment the
    /// machine does not hold. Unreachable while the machine's own pushes are
    /// the only source of tasks; reported rather than asserted, so a future
    /// frame that miscounts surfaces as a refusal instead of a wrong
    /// answer.
    MachineInvariant,
    /// Nominal elimination received a value other than a constructor or
    /// neutral.
    CasedNonConstructor,
    /// The constructor ordinal has no branch in the supplied case.
    UnknownConstructor
    {
        tag: gandr_core_term::ConstructorTag,
    },
    /// The injected summand has no branch in the supplied sum case.
    UnknownSummand
    {
        summand: gandr_kernel_term::Summand
    },
    /// Record projection received a non-record, non-neutral value.
    ProjectedNonRecord,
    /// The exact projection label is absent from the record.
    AbsentRecordField,
    /// Tuple projection received a non-tuple, non-neutral value.
    ProjectedNonTuple,
    /// The projected component is past the tuple's last.
    AbsentTupleComponent,
    /// A split received a non-tuple, non-neutral value.
    SplitNonTuple,
    /// A split binds a number of components other than its tuple's.
    SplitArity,
    /// A compound endpoint's computation reached a weak head that is neither
    /// a returner nor stuck, so it returns no value.
    ReturnedNonReturner,
}

/// A definition chain with every body lowered into the core arena a run
/// evaluates against.
///
/// The chain names a body by its canonical subterm-table entry index, which is
/// arena-independent and so names no core term; unfolding needs the body as a
/// core term. A run lowers the chain into its own arena in one pass, in
/// admission order, and this is the pass's result: the chain together with one
/// core value per distinct entry index it names. Every body the chain holds is
/// lowered by construction, so a readback forcing a body of this chain never
/// meets one it cannot read.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LoweredChain
{
    /// The definitions, in admission order.
    chain: DefinitionChain,
    /// Each body's core value, keyed by its canonical entry index.
    bodies: BTreeMap<GlobalIndex, ValueId>,
    /// The rules of each presented data declaration, by admission position.
    presentations: BTreeMap<ConstantIndex, crate::presented::Presented>,
    /// How many constructors each data declaration takes, by admission
    /// position: where a case's loop arms start after its constructors'.
    constructors: BTreeMap<ConstantIndex, gandr_kernel_term::ConstructorCount>,
}

impl LoweredChain
{
    /// The empty chain, which lowers nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Lower every body of `chain`, in admission order, through `lowering`.
    ///
    /// # Specification
    /// - requires: `lowering` answers, for one entry, a closed core value in
    ///   the arena the run evaluates against, spelling the body the entry's
    ///   index names; a free variable in it surfaces as
    ///   [`EvalFault::UnboundVariable`] when the body is forced.
    /// - ensures: on success every entry's body index reads as lowered, and
    ///   `lowering` was called once per distinct entry index, in admission
    ///   order, so two definitions the canonical table gave one body share one
    ///   lowering.
    /// - provides: the one pass that turns the chain's arena-independent bodies
    ///   into this run's terms, and the completeness that makes
    ///   [`ReadbackFault::UnloweredBody`](crate::ReadbackFault::UnloweredBody)
    ///   unreachable for a definition the chain holds. Reading one table entry
    ///   as a core term is the caller's, because the caller holds the table.
    /// - fails: the first refusal `lowering` returns, unchanged; no partial
    ///   chain is returned.
    /// - panics: none.
    ///
    /// # Errors
    /// Whatever `lowering` refuses, at the first entry it refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the per-index lowering and
    ///   the refusal, separated by two definitions sharing one body index
    ///   lowered by one call, and a lowering that refuses the second entry.
    /// - witness: `eval::tests::a_chain_lowers_each_body_once_in_admission_order`
    /// - witness: `eval::tests::a_refused_lowering_returns_no_chain`
    #[inline]
    #[spec(
        captures: [entry_count = chain.entries().len(), entry_first = chain.entries().first().copied(), entry_last = chain.entries().last().copied()],
        ensures: |ret| ret.as_ref().map_or(true, |lowered| {
            lowered.chain.entries().len() == entry_count
                && lowered.chain.entries().first().copied() == entry_first
                && lowered.chain.entries().last().copied() == entry_last
                && lowered.bodies.len() <= entry_count
                && lowered.chain.entries().iter().all(|entry| lowered.bodies.contains_key(&entry.body()))
        }),
    )]
    pub fn lower<Lowering, Refusal>(
        chain: DefinitionChain,
        mut lowering: Lowering,
    ) -> Result<Self, Refusal>
    where
        Lowering: FnMut(DefinitionEntry) -> Result<ValueId, Refusal>,
    {
        let mut bodies = BTreeMap::new();
        for &entry in chain.entries() {
            if let Entry::Vacant(vacant) = bodies.entry(entry.body()) {
                let lowered = lowering(entry)?;
                vacant.insert(lowered);
            }
        }
        Ok(Self {
            chain,
            bodies,
            presentations: BTreeMap::new(),
            constructors: BTreeMap::new(),
        })
    }

    /// Append one definition to the chain in place, its body already lowered
    /// to `lowered`.
    ///
    /// # Specification
    /// - requires: `lowered` is a closed core value in the arena the run
    ///   evaluates against, spelling the body `body` names.
    /// - ensures: on success the chain is [`DefinitionChain::define`] of the
    ///   chain before, and `body` reads as lowered: as `lowered` when no entry
    ///   before named it, as the earlier lowering otherwise. The result equals
    ///   [`lower`](Self::lower) of the extended chain under a lowering that
    ///   answers the earlier bodies as before and `lowered` for `body`. On a
    ///   refusal the chain and its bodies are unchanged.
    /// - provides: one definition's growth at the cost of one chain append and
    ///   one map insertion, where lowering the extended chain again costs a
    ///   pass over every entry.
    /// - fails: the chain's [`DefinitionError`], unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// Whatever [`DefinitionChain::define`] refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three definitions appended in place equal the same
    ///   chain lowered whole, entry for entry and body for body; a repeated
    ///   position is refused without a half-recorded body. An append that
    ///   dropped the body, overwrote an earlier lowering or recorded a refused
    ///   entry changes the comparison.
    /// - witness: `eval::tests::an_in_place_definition_equals_lowering_the_extended_chain`
    #[inline]
    #[spec(
        captures: [entry_count = self.chain.entries().len(), body_count = self.bodies.len()],
        ensures: |ret| match ret {
            Ok(_) => self.chain.entries().len() == entry_count.saturating_add(1)
                && self.chain.entries().last().is_some_and(|entry| entry.constant() == constant && entry.body() == body)
                && self.bodies.contains_key(&body),
            Err(_) => self.chain.entries().len() == entry_count && self.bodies.len() == body_count,
        },
    )]
    pub fn define(
        &mut self,
        constant: ConstantIndex,
        body: GlobalIndex,
        declared: Transparency,
        mentions: &[ConstantIndex],
        lowered: ValueId,
    ) -> Result<DefinitionHeight, DefinitionError>
    {
        let height = self.chain.define(constant, body, declared, mentions)?;
        if let Entry::Vacant(vacant) = self.bodies.entry(body) {
            vacant.insert(lowered);
        }
        Ok(height)
    }

    /// Record the data declaration at `constant` as presented by
    /// `presented`: conversion reads its terms by their normal forms.
    ///
    /// # Specification
    /// - requires: `presented` validated against the declaration's constructor
    ///   table.
    /// - ensures: [`Definitions::presented`] answers `presented` at `constant`
    ///   for every run over this chain; an earlier record at `constant` is
    ///   replaced.
    /// - provides: the one place a presented type reaches conversion.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle word converts with its reduced word once the
    ///   circle is recorded, and not before.
    /// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
    #[inline]
    #[spec(ensures: self.presentations.contains_key(&constant))]
    pub fn present(
        &mut self,
        constant: ConstantIndex,
        presented: crate::presented::Presented,
    )
    {
        let _replaced = self.presentations.insert(constant, presented);
    }

    /// Record that the data declaration at `constant` takes `constructors`
    /// constructors.
    ///
    /// # Specification
    /// - requires: `constructors` is the length of the declaration's
    ///   constructor table.
    /// - ensures: [`Definitions::constructors`] answers `constructors` at
    ///   `constant` for every run over this chain; an earlier record at
    ///   `constant` is replaced.
    /// - provides: where a case over a sort its words loop at keeps its loop
    ///   arms: after one branch per constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a map out of the circle carries its loop's image only
    ///   once the circle's constructor count is recorded.
    /// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
    #[inline]
    #[spec(ensures: self.constructors.get(&constant) == Some(&constructors))]
    pub fn admit_data(
        &mut self,
        constant: ConstantIndex,
        constructors: gandr_kernel_term::ConstructorCount,
    )
    {
        let _replaced = self.constructors.insert(constant, constructors);
    }

    /// The definitions, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn chain(&self) -> &DefinitionChain
    {
        &self.chain
    }

    /// Each body's core value, keyed by its canonical entry index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn bodies(&self) -> &BTreeMap<GlobalIndex, ValueId>
    {
        &self.bodies
    }
}

/// What a run may unfold, and where it is reading from.
///
/// The three travel together because the answer to "is this definition manifest
/// here" needs all three, and splitting them across parameters is how a call
/// site ends up asking the root scope by accident. The endpoint stance travels
/// with them because it, too, decides where a definition unfolds, and so does
/// the constant stance.
#[derive(Clone, Copy, Debug)]
pub struct Definitions<'run>
{
    /// Every definition's body, height and lowering.
    chain: &'run LoweredChain,
    /// Which definitions are manifest in which scope.
    environment: &'run DefinitionalEnvironment,
    /// The scope this run reads from.
    scope: ScopeId,
    /// How a compound endpoint's computation reads.
    endpoints: Endpoints,
    /// Whether a manifest definition unfolds at all.
    constants: Constants,
    /// How a readback names a definition's own recursion.
    recursion: Recursion,
}

/// Whether a run unfolds the definitions its scope reads as manifest.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Constants
{
    /// A definition the scope reads as manifest unfolds.
    Unfold,
    /// No definition unfolds: every constant is compared by name, as the
    /// kernel's own conversion compares it. A presented type's terms still
    /// read by their normal forms.
    Rigid,
}

/// How a run reads a compound endpoint's computation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Endpoints
{
    /// The computation runs on through every manifest definition it is stuck
    /// on, until it returns or sticks on a rigid head.
    Run,
    /// The computation holds at the first manifest definition it is stuck on:
    /// the endpoint stays a neutral until a conversion unfolds that
    /// definition, as a step its trace records.
    Hold,
}

/// How a readback names a fixpoint that is a definition's own recursion.
///
/// That fixpoint is the one a definition's body suspends, closed over
/// nothing, which an unfolding of that definition binds for its recursive
/// calls.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Recursion
{
    /// As the fixpoint it is.
    Unrolled,
    /// As the definition forced: a recursive call stuck at a variable reads
    /// back as the call its source wrote, `el(a)`, not the fixpoint applied.
    Refolded,
}

impl<'run> Definitions<'run>
{
    /// Read `chain` from `scope` of `environment`, running compound endpoints
    /// through their definitions.
    ///
    /// # Specification
    /// - requires: `environment` was built over `chain`; every scope id is
    ///   admissible, and an unknown scope reads as unfolding nothing.
    /// - ensures: the three travel together thereafter, so no later call can
    ///   pair a chain with another run's scope; the endpoint stance is
    ///   [`Endpoints::Run`].
    /// - provides: the one bundle every unfolding question is asked of, which
    ///   is what keeps a call site from reaching the root scope by accident.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same admitted body is manifest at one scope and
    ///   sealed at another. Replacing the supplied scope with the root would
    ///   unfold the sealed case.
    /// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
    /// - witness: `eval::tests::a_sealed_definition_is_rigid`
    #[inline]
    #[must_use]
    #[spec(
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.chain), core::ptr::from_ref(chain))
            && core::ptr::eq(core::ptr::from_ref(ret.environment), core::ptr::from_ref(environment))
            && ret.scope == scope && ret.endpoints == Endpoints::Run
            && ret.constants == Constants::Unfold && ret.recursion == Recursion::Unrolled,
    )]
    pub fn new(
        chain: &'run LoweredChain,
        environment: &'run DefinitionalEnvironment,
        scope: ScopeId,
    ) -> Self
    {
        Self {
            chain,
            environment,
            scope,
            endpoints: Endpoints::Run,
            constants: Constants::Unfold,
            recursion: Recursion::Unrolled,
        }
    }

    /// The same definitions, naming a definition's own recursion in
    /// `recursion`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every stance unchanged but the recursion stance, which is
    ///   `recursion`.
    /// - provides: the reading of an open code's run under
    ///   [`Recursion::Refolded`]: the quote a decoder returns over a binder
    ///   names its recursive calls as its source wrote them, so the decode
    ///   `el(a)` it holds is the one a signature writes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive decoder's arm read back under a binder
    ///   names its stuck call `el(a)` under the refolding stance and the
    ///   fixpoint applied under the unrolling one; a stance that does not reach
    ///   the readback loses the distinction.
    /// - witness: `readback::tests::a_definition_s_own_recursion_reads_back_as_the_definition`
    #[inline]
    #[must_use]
    #[spec(
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.chain), core::ptr::from_ref(self.chain))
            && core::ptr::eq(core::ptr::from_ref(ret.environment), core::ptr::from_ref(self.environment))
            && ret.scope == self.scope && ret.endpoints == self.endpoints
            && ret.constants == self.constants && ret.recursion == recursion,
    )]
    pub fn reading_recursion(
        self,
        recursion: Recursion,
    ) -> Self
    {
        Self { recursion, ..self }
    }

    /// The definition whose own recursion the fixpoint `source` is, closed
    /// over nothing, when this run refolds recursion.
    ///
    /// # Specification
    /// - requires: nothing — any computation id is admissible input.
    /// - ensures: under [`Recursion::Refolded`], the first constant in
    ///   admission order whose body this scope reads as manifest and which
    ///   suspends `source`; `None` under [`Recursion::Unrolled`] and for a
    ///   fixpoint no definition suspends.
    /// - provides: the name a readback gives a definition's recursion.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reading_recursion`].
    /// - witness: `readback::tests::a_definition_s_own_recursion_reads_back_as_the_definition`
    #[inline]
    #[spec(ensures: |ret| self.recursion == Recursion::Refolded || ret.is_none())]
    pub(crate) fn recursion_of(
        &self,
        core: &CoreArena,
        source: ComputationId,
    ) -> Option<ConstantIndex>
    {
        if self.recursion == Recursion::Unrolled {
            return None;
        }
        self.chain
            .chain()
            .entries()
            .iter()
            .map(DefinitionEntry::constant)
            .find(|&constant| {
                self.definition(constant)
                    .is_some_and(|body| core.value(body) == Some(&Value::Thunk(source)))
            })
    }

    /// The same definitions, reading compound endpoints in `endpoints`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chain, the environment and the scope unchanged, the
    ///   endpoint stance `endpoints`.
    /// - provides: the stance a traced endpoint comparison runs in: under
    ///   [`Endpoints::Hold`] every δ-step an endpoint takes is a conversion's
    ///   recorded `Unfold`, never an evaluation's silent one.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one endpoint applying a definition to a variable
    ///   evaluates to the variable under the running stance and to a held
    ///   neutral under the holding one; a stance that does not reach the
    ///   evaluation loses that distinction.
    /// - witness: `eval::tests::a_held_endpoint_stays_at_its_definition`
    #[inline]
    #[must_use]
    #[spec(
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.chain), core::ptr::from_ref(self.chain))
            && core::ptr::eq(core::ptr::from_ref(ret.environment), core::ptr::from_ref(self.environment))
            && ret.scope == self.scope && ret.endpoints == endpoints,
    )]
    pub fn reading_endpoints(
        self,
        endpoints: Endpoints,
    ) -> Self
    {
        Self { endpoints, ..self }
    }

    /// The same definitions, unfolding none of them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chain, the environment, the scope and the endpoint stance
    ///   unchanged; the constant stance [`Constants::Rigid`], so
    ///   [`Self::unfolding`] answers [`Unfolding::Rigid`] for every constant.
    /// - provides: the δ-free conversion a case's respect for its type's rules
    ///   is decided by, the one the kernel re-derives with no engine trace.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one manifest definition carries its body unforced
    ///   under the unfolding stance and is rigid under this one; a stance that
    ///   does not reach the lookup loses the distinction.
    /// - witness: `eval::tests::a_rigid_run_unfolds_no_definition`
    #[inline]
    #[must_use]
    #[spec(
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.chain), core::ptr::from_ref(self.chain))
            && core::ptr::eq(core::ptr::from_ref(ret.environment), core::ptr::from_ref(self.environment))
            && ret.scope == self.scope && ret.endpoints == self.endpoints
            && ret.constants == Constants::Rigid,
    )]
    pub fn rigid(self) -> Self
    {
        Self {
            constants: Constants::Rigid,
            ..self
        }
    }

    /// The same definitions, unfolding every one the scope reads as manifest
    /// and running every compound endpoint through them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chain, the environment and the scope unchanged; the
    ///   constant stance [`Constants::Unfold`] and the endpoint stance
    ///   [`Endpoints::Run`], so a compound endpoint runs on through every
    ///   manifest definition until it returns or sticks on a rigid head.
    /// - provides: the reading a cong chain's composite function takes in a
    ///   conversion of any stance, rigid or holding: the function is read by
    ///   what it computes, as the kernel reads it by its own evaluator, and no
    ///   δ-step of the reading is a recorded decision.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a respect obligation whose cong chain composes to the
    ///   identity through two definitions converts under a rigid run only when
    ///   the chain's functions are read under this stance; a stance that does
    ///   not reach the reading leaves the chain stuck and the case refused.
    /// - witness: `fusion::tests::a_cong_chain_composing_to_the_identity_is_its_path`
    #[inline]
    #[must_use]
    #[spec(
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.chain), core::ptr::from_ref(self.chain))
            && core::ptr::eq(core::ptr::from_ref(ret.environment), core::ptr::from_ref(self.environment))
            && ret.scope == self.scope && ret.endpoints == Endpoints::Run
            && ret.constants == Constants::Unfold,
    )]
    pub(crate) fn manifest(self) -> Self
    {
        Self {
            constants: Constants::Unfold,
            endpoints: Endpoints::Run,
            ..self
        }
    }

    /// How this run reads a compound endpoint's computation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn endpoints(&self) -> Endpoints
    {
        self.endpoints
    }

    /// Each body's core value, keyed by its canonical entry index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn bodies(&self) -> &'run BTreeMap<GlobalIndex, ValueId>
    {
        self.chain.bodies()
    }

    /// The rules presenting the data declaration at `constant`, when it is
    /// presented.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn presented(
        &self,
        constant: ConstantIndex,
    ) -> Option<&'run crate::presented::Presented>
    {
        self.chain.presentations.get(&constant)
    }

    /// How many constructors the data declaration at `constant` takes, when
    /// the chain recorded it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn constructors(
        &self,
        constant: ConstantIndex,
    ) -> Option<gandr_kernel_term::ConstructorCount>
    {
        self.chain.constructors.get(&constant).copied()
    }

    /// The types of words whose cells loop in the sort admitted at `sort`, by
    /// admission position ascending, each with its cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn looping(
        &self,
        sort: ConstantIndex,
    ) -> impl Iterator<Item = (ConstantIndex, &'run gandr_kernel_term::FreeCells)>
    {
        self.chain
            .presentations
            .iter()
            .filter_map(move |(&words, presented)| {
                presented
                    .cells()
                    .filter(|cells| cells.sort() == sort)
                    .map(|cells| (words, cells))
            })
    }

    /// The body of the definition at `constant` as the scope reads it
    /// manifest, whatever the run's constant stance: the function a family's
    /// endpoint runs its binder through, read for the image of a loop.
    ///
    /// # Specification
    /// - requires: nothing — an unknown constant is admissible input.
    /// - ensures: the lowered body exactly when the chain holds one for
    ///   `constant` and the scope reads it as manifest; `None` for an axiom, a
    ///   sealed definition or an unknown position.
    /// - provides: the reading [`Self::manifest`] gives a cong chain's
    ///   functions, for a loop's image.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::unfolding`] under [`Self::manifest`].
    /// - witness: `eval::words::tests::cong_along_the_loop_is_the_arm_s_image`
    #[inline]
    #[spec(ensures: |ret| ret.is_some() == matches!(self.manifest().unfolding(constant), Unfolding::Unforced(entry) if self.bodies().contains_key(&entry)))]
    pub(crate) fn definition(
        &self,
        constant: ConstantIndex,
    ) -> Option<ValueId>
    {
        match self.manifest().unfolding(constant) {
            Unfolding::Unforced(entry) => self.bodies().get(&entry).copied(),
            Unfolding::Rigid | Unfolding::Forced(_) => None,
        }
    }

    /// The definitional height of `constant`, or the floor when the chain
    /// holds no body for it.
    ///
    /// # Specification
    /// - requires: nothing — an unknown constant is admissible input.
    /// - ensures: the height the chain recorded for `constant`, and
    ///   [`DefinitionHeight`]'s floor for a position with no body.
    /// - provides: the input the scheduling policy's share reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a deep refuting definition competes with a shallow
    ///   divergence. The uniform schedule refutes while the height-weighted
    ///   schedule declines under the same budget; flattening recorded heights
    ///   removes that distinction.
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
        ensures: |ret| ret == self.chain.chain().entry(constant)
            .map_or_else(DefinitionHeight::default, DefinitionEntry::height),
    )]
    pub(crate) fn height(
        &self,
        constant: ConstantIndex,
    ) -> DefinitionHeight
    {
        self.chain
            .chain()
            .entry(constant)
            .map_or_else(DefinitionHeight::default, DefinitionEntry::height)
    }

    /// The unfolding face a neutral headed by `constant` carries here.
    ///
    /// # Specification
    /// - requires: nothing — an unknown constant and an unknown scope are both
    ///   admissible input.
    /// - ensures: [`Unfolding::Unforced`] naming the body's content id exactly
    ///   when the run unfolds definitions, the chain holds a body for
    ///   `constant` **and** this scope reads it as manifest;
    ///   [`Unfolding::Rigid`] otherwise, which covers a rigid run, an axiom, a
    ///   sealed atom, a definition sealed by an enclosing scope, and a scope
    ///   this environment never opened.
    /// - provides: the one place a scope's transparency reaches the domain, so
    ///   an unfolding face never disagrees with the environment that governs
    ///   it.
    /// - fails: never — every refusal degrades to rigidity, which is the
    ///   conservative direction: a neutral that could have been unfolded stays
    ///   stuck, costing completeness rather than soundness.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the constant stance, the
    ///   chain lookup, the transparency lookup and the unknown-scope
    ///   degradation, separated by a manifest definition read rigidly, the same
    ///   definition sealed in an enclosing scope, an admission position with no
    ///   body, and a scope that was never opened.
    /// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
    /// - witness: `eval::tests::a_sealed_definition_is_rigid`
    /// - witness: `eval::tests::a_rigid_run_unfolds_no_definition`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match self.chain.chain().entry(constant) {
        | Some(entry) if self.constants == Constants::Unfold => {
            match self.environment.transparency(self.scope, constant, entry.declared()) {
                | Ok(Transparency::Manifest) => ret == Unfolding::Unforced(entry.body()),
                | Ok(Transparency::Opaque) | Err(_) => ret == Unfolding::Rigid,
            }
        },
        | Some(_) | None => ret == Unfolding::Rigid,
    })]
    pub fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Unfolding
    {
        if self.constants == Constants::Rigid {
            return Unfolding::Rigid;
        }
        let Some(entry) = self.chain.chain().entry(constant)
        else {
            return Unfolding::Rigid;
        };
        let stance = self
            .environment
            .transparency(self.scope, constant, entry.declared());
        match stance {
            Ok(Transparency::Manifest) => Unfolding::Unforced(entry.body()),
            Ok(Transparency::Opaque) | Err(_) => Unfolding::Rigid,
        }
    }
}

/// One unit of work on the machine's task stack.
///
/// Every variant either evaluates a source node or assembles a result from
/// operands its own earlier tasks left on the result stacks, so the stack is
/// the defunctionalized continuation of the recursive presentation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Assemble evaluated nominal fields and capture the classifier's scope.
    Constructor
    {
        /// The source constructor whose classifier is captured.
        term: ValueId,
        /// The constructor occurrence's lexical environment.
        env: EnvId,
    },
    /// Assemble evaluated record fields in source label order.
    Record(ValueId),
    /// Select a native branch and apply its constructor fields.
    DataCase
    {
        /// The source case carrying its motive and branch table.
        term: ComputationId,
        /// The environment in which its branch functions are evaluated.
        env: EnvId,
    },
    /// Reapply a suspended nominal case after its head unfolds.
    DataCaseClosure(CompClosureId),
    /// Bind a tuple's components into the source split's body.
    Split
    {
        /// The source split, carrying its arity and body.
        term: ComputationId,
        /// The environment its body extends.
        env: EnvId,
    },
    /// Reapply a suspended split after its head unfolds.
    SplitClosure(CompClosureId),
    /// Select the source's field or component from an evaluated record or
    /// tuple.
    Projection(ComputationId),
    /// Enter a source or native computation body.
    Body
    {
        /// The suspended source or native continuation.
        body: crate::closure::CompBody,
        /// Bindings for a source body or a native continuation’s returned
        /// value.
        env: EnvId,
    },
    /// Assemble a native product path.
    PathProduct(ValueId),
    /// Transport the operand above the path on the value stack.
    Transport,
    /// Transport a neutral pair through the held product path.
    ProductTransport(DomainValueId),
    /// Transport the operand above the element path on the value stack in a
    /// motive.
    PathTransport(crate::arena::ValueClosureId),
    /// Ride the value above the flow on the value stack along it, in a
    /// motive.
    Ride(crate::arena::ValueClosureId),
    /// Assemble a flow introduction from its evaluated parts.
    Flow
    {
        /// The source introduction, naming the former and its parts.
        term: ValueId,
    },
    /// Transport the operand above the identity over the path, the start and
    /// the path on the value stack, along a two-entry telescope in a motive.
    TelescopeTransport(crate::arena::ValueClosureId),
    /// Assemble reflexivity from its evaluated point.
    Here
    {
        /// The source node.
        term: ValueId,
    },
    /// Read the value the computation on the stack returns: a compound
    /// endpoint's value.
    Returned,
    /// Read the value the computation on the stack returns, running it on
    /// through every manifest definition it is stuck on whatever the run's
    /// endpoint stance: a held operand's run ([`words::appended`]).
    Running,
    /// Evaluate a core value.
    Value
    {
        /// The source node.
        term: ValueId,
        /// The environment it is read in.
        env: EnvId,
    },
    /// Evaluate a core computation to weak head.
    Comp
    {
        /// The source node.
        term: ComputationId,
        /// The environment it is read in.
        env: EnvId,
    },
    /// Assemble a tuple from the values its own tasks produced.
    Tuple
    {
        /// The source node, which supplies the arity, the children to compare
        /// faces against and the face to keep when they match.
        term: ValueId,
    },
    /// Assemble a native list cell from its evaluated head and tail.
    ListCons(ValueId),
    /// Fold the list on the value stack using captured pure branches.
    ListFold
    {
        /// Ambient element annotation.
        element: gandr_core_term::ValueTypeId,
        /// Ambient result annotation.
        result: gandr_core_term::ValueTypeId,
        /// Empty branch in its ambient environment.
        on_nil: CompClosureId,
        /// Cell branch binding head then folded result.
        on_cons: CompClosureId,
    },
    /// Assemble a sum injection.
    Inject
    {
        /// The source node.
        term: ValueId,
    },
    /// Assemble a universe lift.
    Lift
    {
        /// The source node.
        term: ValueId,
        /// The held level.
        target: LiftTarget,
    },
    /// Assemble a returner from the value its own task produced.
    Return
    {
        /// The source node.
        term: ComputationId,
    },
    /// Run the thunk the value on the stack holds, or get stuck on it.
    Force,
    /// Apply the weak head on the stack to the value on the stack.
    Apply,
    /// Apply the operator beneath the top of the value stack to the argument
    /// on top of it: static beta, or its stuck case.
    StaticApply,
    /// Sequence into a body once the bound computation has a weak head.
    Bind
    {
        /// The continuation's source node.
        body: ComputationId,
        /// The environment the continuation is read in.
        env: EnvId,
    },
    /// Choose a branch once the scrutinee has a value.
    Case
    {
        /// The source case, which supplies its branches.
        term: ComputationId,
        /// The environment the branches are read in.
        env: EnvId,
    },
    /// Push a domain value the machine already holds onto the value stack:
    /// the operand a re-applied spine's application frame consumes.
    Supply(DomainValueId),
    /// Sequence into an already-captured continuation once the bound
    /// computation has a weak head: a spine's bind, re-applied.
    BindClosure(CompClosureId),
    /// Choose among already-captured branches once the scrutinee has a
    /// value: a spine's case, re-applied.
    CaseBranches(crate::arena::BranchSpan),
    /// Remember the weak head on the stack as the evaluation of a pending
    /// configuration.
    Remember(PendingId),
    /// Apply an already-captured fixpoint to the value on the stack: a
    /// spine's stuck fixpoint, re-applied.
    FixpointClosure(CompClosureId),
    /// Finish reading a held computation through its bind at `bind`, once
    /// that bind's continuation has run with the call before it: what the
    /// continuation returned, under the eliminations past the bind; or, when
    /// it sticks at a bind of its own, that continuation read first, beneath
    /// [`Task::ReadContinued`]; or, when it did not return, the computation
    /// read from the next position ([`read_from`]).
    ReadThrough
    {
        /// The held computation.
        computation: DomainCompId,
        /// The position of the bind in the computation's spine.
        bind: SpinePosition,
        /// Where the reading leaves what it reads to.
        delivery: Delivery,
    },
    /// Finish reading a held computation through its bind at `bind`, once
    /// the continuation, stuck at a bind of its own, has been read: what that
    /// reading returned, under the eliminations past the bind, or, when it did
    /// not return, the computation read from the next position.
    ReadContinued
    {
        /// The held computation.
        computation: DomainCompId,
        /// The position of the bind in the computation's spine.
        bind: SpinePosition,
        /// Where the reading leaves what it reads to.
        delivery: Delivery,
    },
    /// Read the computation on the stack again from its first position, for
    /// a continuation's reading whose bind just returned.
    Reread,
    /// Run a loop arm under its function's arguments once the fixed ones have
    /// their values: the values above on the stack, one per argument but the
    /// moving one, the first deepest ([`words::arm_entered`]).
    Arm(words::ArmEntry),
    /// Return the value on the stack: what a held continuation binds once the
    /// machine has evaluated a value as its answer.
    Yield,
}

/// Where a reading of a held computation leaves what it reads to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Delivery
{
    /// An endpoint's own reading: delivered as the value it returns, on the
    /// value stack.
    Value,
    /// The reading of a continuation stuck at a bind of its own: left on the
    /// computation stack, for the [`Task::ReadContinued`] beneath it to judge
    /// whether it returned.
    Continuation,
}

/// The position of an elimination in a neutral's spine, innermost first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SpinePosition(usize);

impl SpinePosition
{
    /// The spine's innermost position.
    const INNERMOST: Self = Self(0);

    /// The position just outside this one.
    ///
    /// # Specification
    /// trivial.
    const fn outward(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// The index of one configuration whose evaluation is under way.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct PendingId(usize);

/// One shared leg read in one environment: its core term, and the bindings at
/// its free indices, intuitionistic ones first, each zone ascending.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Configuration
{
    /// The leg's core term.
    term: CoreTerm,
    /// The bindings its free indices resolve to.
    entries: Vec<DomainValueId>,
}

/// What the machine shares by configuration: the legs it was handed with their
/// free indices, the weak heads already remembered, and the configurations
/// under way.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct LegSharing
{
    /// The shared legs, each with its free indices; empty for an unshared run.
    legs: BTreeMap<CoreTerm, Free>,
    /// The weak head of each configuration evaluated so far.
    remembered: BTreeMap<Configuration, Glued>,
    /// The configurations whose evaluation is under way, each taken once its
    /// weak head is remembered.
    pending: Vec<Option<Configuration>>,
}

/// What recalling a configuration found.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Recall
{
    /// The term is no shared leg: evaluate it.
    Unshared,
    /// The configuration is new: evaluate it, a task remembering its weak
    /// head pushed beneath.
    Pending,
    /// The configuration was evaluated already, to this weak head.
    Remembered(Glued),
}

/// The running machine: the task stack, the two result stacks, and the
/// environments the tasks name.
struct Machine<'run>
{
    /// Work still to do, most recent last.
    tasks: Vec<Task>,
    /// Value results, most recent last.
    values: Vec<DomainValueId>,
    /// Weak-head computation results, most recent last.
    comps: Vec<DomainCompId>,
    /// The environments tasks name, so a task stays `Copy`.
    envs: Vec<Environment>,
    /// What may be unfolded, and where from.
    definitions: Definitions<'run>,
    /// Steps left.
    fuel: Fuel,
    /// The legs shared by configuration, and what sharing them has remembered.
    sharing: LegSharing,
}

impl<'run> Machine<'run>
{
    /// Start a machine over the empty environment.
    ///
    /// # Specification
    /// - requires: nothing; `fuel` may be zero, which refuses at the first step
    ///   rather than running one.
    /// - ensures: a machine holding no task, no operand, and exactly one
    ///   environment — the empty one, which [`Machine::root_env`] names.
    /// - provides: the entry state every run starts from, so the root
    ///   environment's id is a constant rather than a value threaded from the
    ///   caller.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed value evaluates, a loose occurrence refuses,
    ///   and a zero-step slice retains its first task. A pre-bound root,
    ///   inherited result or pre-spent budget changes one of those outcomes.
    /// - witness: `eval::tests::a_variable_resolves_out_of_the_environment`
    /// - witness: `eval::tests::a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause`
    #[spec(
        ensures: |ret| ret.tasks.is_empty() && ret.values.is_empty() && ret.comps.is_empty()
            && ret.envs.len() == 1_usize
            && ret.envs.first().is_some_and(|env| usize::from(env.depth(Zone::Intuitionistic)) == 0_usize
                && usize::from(env.depth(Zone::Linear)) == 0_usize)
            && ret.fuel == fuel && ret.definitions.scope == definitions.scope
            && core::ptr::eq(core::ptr::from_ref(ret.definitions.chain), core::ptr::from_ref(definitions.chain))
            && core::ptr::eq(core::ptr::from_ref(ret.definitions.environment), core::ptr::from_ref(definitions.environment))
            && ret.sharing.legs.is_empty() && ret.sharing.remembered.is_empty() && ret.sharing.pending.is_empty(),
    )]
    fn new(
        definitions: Definitions<'run>,
        fuel: Fuel,
    ) -> Self
    {
        Self {
            tasks: Vec::new(),
            values: Vec::new(),
            comps: Vec::new(),
            envs: Vec::from([Environment::new()]),
            definitions,
            fuel,
            sharing: LegSharing::default(),
        }
    }

    /// The empty environment, which every run starts from.
    ///
    /// # Specification
    /// - requires: the machine was built by [`Machine::new`], whose table
    ///   starts with the empty environment at that position.
    /// - ensures: the id of the empty environment, which no push ever
    ///   overwrites because the table only grows.
    /// - provides: the environment a closed term is evaluated under.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a loose root occurrence refuses while the same
    ///   occurrence under a beta binder resolves. Choosing an appended
    ///   environment instead of the empty root confuses those cases.
    /// - witness: `eval::tests::a_variable_resolves_out_of_the_environment`
    #[inline]
    #[spec(
        ensures: |ret| ret.0 == 0_usize,
    )]
    fn root_env() -> EnvId
    {
        EnvId(0_usize)
    }

    /// Read an environment, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an id this machine does not hold is admissible
    ///   input.
    /// - ensures: the environment `id` names, borrowed from the machine's own
    ///   table.
    /// - provides: the one read of the environment table, so a task's env id is
    ///   resolved in one place rather than indexed at each rule.
    /// - fails: [`EvalFault::MachineInvariant`] when the id names no held
    ///   environment. Only the machine's own pushes mint an id, so the
    ///   condition is unreachable while that stays true — it is reported rather
    ///   than asserted so a future rule that miscounts surfaces as a refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — the id names no held environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supplied bindings differ from the empty root, and the
    ///   two zones carry different values in a shared configuration. An
    ///   off-by-one environment read or zone substitution changes the resulting
    ///   pair.
    /// - witness: `eval::tests::an_evaluation_in_a_supplied_environment_reports_its_remainder`
    /// - witness: `eval::tests::shared_configurations_distinguish_zones_but_ignore_unused_bindings`
    #[spec(
        ensures: |ret| ret.as_ref().map_or_else(
            |fault| *fault == EvalFault::MachineInvariant && self.envs.get(id.0).is_none(),
            |held| self.envs.get(id.0).is_some_and(|stored| core::ptr::eq(core::ptr::from_ref(*held), core::ptr::from_ref(stored))),
        ),
    )]
    fn env(
        &self,
        id: EnvId,
    ) -> Result<&Environment, EvalFault>
    {
        self.envs.get(id.0).ok_or(EvalFault::MachineInvariant)
    }

    /// Copy the environment `id` names out of the machine, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an id this machine does not hold is admissible
    ///   input.
    /// - ensures: an owned environment equal to the one `id` names, which the
    ///   caller is free to capture into a closure or extend.
    /// - provides: the capture step every closure-building rule shares, so the
    ///   fallible read and the copy stay one operation rather than a chain.
    /// - fails: [`EvalFault::MachineInvariant`] when the id names no held
    ///   environment.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — the id names no held environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — applying a captured closure under a different
    ///   argument preserves the outer binding, and replayed branches retain
    ///   distinct captures. Capturing the root or replacing the old binding by
    ///   the new argument changes the result.
    /// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
    /// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
    #[spec(
        ensures: |ret| ret.as_ref().map_or_else(
            |fault| *fault == EvalFault::MachineInvariant && self.envs.get(id.0).is_none(),
            |captured| self.envs.get(id.0) == Some(captured),
        ),
    )]
    fn capture(
        &self,
        id: EnvId,
    ) -> Result<Environment, EvalFault>
    {
        let held = self.env(id)?;
        Ok(held.clone())
    }

    /// Hold an environment and return the id naming it.
    ///
    /// # Specification
    /// - requires: nothing; every environment is admissible.
    /// - ensures: the environment is appended to the machine's table and the
    ///   returned id resolves to it; ids already handed out keep naming what
    ///   they named, because the table only grows.
    /// - provides: the indirection that keeps a task `Copy` while an
    ///   environment owns two vectors.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a supplied environment and two differently captured
    ///   continuations produce different ordered pairs. Reusing an old slot,
    ///   dropping one zone or losing an outer binding changes those
    ///   observations.
    /// - witness: `eval::tests::an_evaluation_in_a_supplied_environment_reports_its_remainder`
    /// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
    /// - witness: `eval::tests::shared_configurations_distinguish_zones_but_ignore_unused_bindings`
    #[spec(
        captures: [entry_len = self.envs.len(),
            intuitionistic = environment.depth(Zone::Intuitionistic), linear = environment.depth(Zone::Linear),
            intuitionistic_top = environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
            linear_top = environment.lookup(Zone::Linear, DeBruijnIndex::from(0_u32))],
        ensures: |ret| ret.0 == entry_len && self.envs.len() == entry_len.saturating_add(1_usize)
            && self.envs.get(ret.0).is_some_and(|held| held.depth(Zone::Intuitionistic) == intuitionistic
                && held.depth(Zone::Linear) == linear
                && held.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == intuitionistic_top
                && held.lookup(Zone::Linear, DeBruijnIndex::from(0_u32)) == linear_top),
    )]
    fn hold_env(
        &mut self,
        environment: Environment,
    ) -> EnvId
    {
        let id = EnvId(self.envs.len());
        self.envs.push(environment);
        id
    }

    /// Hold `env` extended in `zone` by `bound`.
    ///
    /// # Specification
    /// - requires: nothing — an id this machine does not hold is admissible
    ///   input; `bound` is stored rather than dereferenced.
    /// - ensures: on success a fresh id naming a copy of `env` whose `zone` is
    ///   one binding deeper, with `env` itself untouched.
    /// - provides: the binder-entering step of the bind and case rules.
    /// - fails: [`EvalFault::MachineInvariant`] when `env` names no held
    ///   environment.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — `env` names no held environment.
    // economy: this copies the whole environment and retains the copy for the
    // run. It is the bind and case sites' extension; the beta site extends a
    // *closure's* environment inline in `step_apply`, which is the dominant
    // shape and carries the same note. Ceiling and upgrade path are stated
    // there, once, at the site that reaches them first.
    /// # Adequacy
    /// - hypothesis: L3 — bind and case introduce the returned or injected
    ///   value innermost without discarding captured bindings. Using the wrong
    ///   zone or replacing rather than extending the environment changes the
    ///   returned value.
    /// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
    /// - witness: `eval::tests::a_case_picks_the_branch_the_injection_names`
    /// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
    #[spec(
        captures: [
            entry_len = self.envs.len(),
            entry_depth = self.envs.get(env.0).map(|held| usize::from(held.depth(zone))),
        ],
        ensures: |ret| match ret {
            | Ok(fresh) => {
                fresh.0 == entry_len
                    && self.envs.len() == entry_len.saturating_add(1_usize)
                    && self.envs.get(env.0).map(|held| usize::from(held.depth(zone))) == entry_depth
                    && self.envs.get(fresh.0).map(|held| usize::from(held.depth(zone)))
                        == entry_depth.map(|depth| depth.saturating_add(1_usize))
                    && self
                        .envs
                        .get(fresh.0)
                        .and_then(|held| held.lookup(zone, DeBruijnIndex::from(0_u32)))
                        == Some(bound)
            },
            | Err(_) => self.envs.len() == entry_len && self.envs.get(env.0).is_none(),
        },
    )]
    fn extended(
        &mut self,
        env: EnvId,
        zone: Zone,
        bound: DomainValueId,
    ) -> Result<EnvId, EvalFault>
    {
        let mut extended = self.capture(env)?;
        extended.extend(zone, bound);
        Ok(self.hold_env(extended))
    }

    /// Pop one value result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent value result, which is no longer on the
    ///   stack.
    /// - provides: the one read of the value result stack.
    /// - fails: [`EvalFault::MachineInvariant`] when the stack is empty, which
    ///   a frame reaches only by claiming an operand its own tasks never
    ///   pushed.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — the value result stack was empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered eliminations consume the most recent operand,
    ///   and a later elimination with no operand refuses by `MachineInvariant`.
    ///   Reading the opposite stack or reusing a consumed result changes the
    ///   pair or replaces the named refusal.
    /// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
    /// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
    #[spec(
        captures: [entry_len = self.values.len(), entry_last = self.values.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(EvalFault::MachineInvariant)
            && self.values.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_value(&mut self) -> Result<DomainValueId, EvalFault>
    {
        self.values.pop().ok_or(EvalFault::MachineInvariant)
    }

    /// Pop one weak-head computation result, or fail closed.
    ///
    /// # Specification
    /// - requires: nothing — an empty result stack is admissible input.
    /// - ensures: the most recent weak-head computation result, which is no
    ///   longer on the stack.
    /// - provides: the one read of the computation result stack.
    /// - fails: [`EvalFault::MachineInvariant`] when the stack is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — the computation result stack was
    ///   empty.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered eliminations consume the most recent operand,
    ///   and a later elimination with no operand refuses by `MachineInvariant`.
    ///   Reading the opposite stack or reusing a consumed result changes the
    ///   pair or replaces the named refusal.
    /// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
    /// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
    #[spec(
        captures: [entry_len = self.comps.len(), entry_last = self.comps.last().copied()],
        ensures: |ret| ret == entry_last.ok_or(EvalFault::MachineInvariant)
            && self.comps.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_comp(&mut self) -> Result<DomainCompId, EvalFault>
    {
        self.comps.pop().ok_or(EvalFault::MachineInvariant)
    }

    /// Recall `term` read in `env`, when it is a shared leg.
    ///
    /// # Specification
    /// - requires: nothing — an id this machine does not hold is admissible
    ///   input.
    /// - ensures: [`Recall::Unshared`] when `term` is no leg this run shares,
    ///   or when a free index of it resolves to nothing in `env`; such an open
    ///   configuration is not cached, and reading the missing index later
    ///   refuses by name. [`Recall::Remembered`] carries the weak head of equal
    ///   bindings at every free index; otherwise [`Recall::Pending`] pushes the
    ///   task that will remember the weak head the evaluation leaves.
    /// - provides: the closed-configuration rule: one evaluation serves every
    ///   occurrence of a leg that reads its free indices in one environment.
    /// - fails: [`EvalFault::MachineInvariant`] when a shared leg names an
    ///   environment not held by the machine. An unshared term does not read
    ///   it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — `env` names no held environment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are leg membership and the
    ///   bindings at the free indices, separated by a rib whose evaluation is
    ///   shared across two applications of one closure, a subterm under an
    ///   inner binder applied to one value at both copies, and a leg whose free
    ///   index names a different binder at its two occurrences, each read off
    ///   the evaluator's step count.
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    /// - witness:
    ///   `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
    /// - witness:
    ///   `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
    /// - witness: `eval::tests::shared_configurations_distinguish_zones_but_ignore_unused_bindings`
    #[spec(
        captures: [entry_tasks = self.tasks.len(), entry_pending = self.sharing.pending.len(), entry_remembered = self.sharing.remembered.len()],
        ensures: |ret| self.sharing.remembered.len() == entry_remembered && {
            let unchanged = self.tasks.len() == entry_tasks && self.sharing.pending.len() == entry_pending;
            match ret {
                Err(fault) => fault == EvalFault::MachineInvariant && unchanged
                    && self.sharing.legs.contains_key(&term) && self.envs.get(env.0).is_none(),
                Ok(Recall::Unshared) => unchanged && self.sharing.legs.get(&term).is_none_or(|free| {
                    self.envs.get(env.0).is_some_and(|environment| {
                        free.intuitionistic().counts().iter().any(|index| environment.lookup(Zone::Intuitionistic, *index).is_none())
                            || free.linear().counts().iter().any(|index| environment.lookup(Zone::Linear, *index).is_none())
                    })
                }),
                Ok(Recall::Pending) => self.tasks.len() == entry_tasks.saturating_add(1_usize)
                    && self.sharing.pending.len() == entry_pending.saturating_add(1_usize)
                    && matches!(self.tasks.last(), Some(Task::Remember(pending)) if pending.0 == entry_pending)
                    && self.sharing.pending.last().and_then(Option::as_ref).is_some_and(|configuration| {
                        configuration.term == term && !self.sharing.remembered.contains_key(configuration)
                            && self.sharing.legs.get(&term).zip(self.envs.get(env.0)).is_some_and(|(free, environment)| configuration.entries.iter().copied().map(Some).eq(
            free.intuitionistic().counts().iter().map(|index| environment.lookup(Zone::Intuitionistic, *index))
                .chain(free.linear().counts().iter().map(|index| environment.lookup(Zone::Linear, *index)))))
                    }),
                Ok(Recall::Remembered(remembered)) => unchanged
                    && self.sharing.legs.get(&term).zip(self.envs.get(env.0)).and_then(|(free, environment)|
            free.intuitionistic().counts().iter().map(|index| environment.lookup(Zone::Intuitionistic, *index))
                .chain(free.linear().counts().iter().map(|index| environment.lookup(Zone::Linear, *index)))
                .collect::<Option<Vec<_>>>())
                    .is_some_and(|entries| self.sharing.remembered.get(&Configuration { term, entries }) == Some(&remembered)),
            }
        },
    )]
    fn recall(
        &mut self,
        term: CoreTerm,
        env: EnvId,
    ) -> Result<Recall, EvalFault>
    {
        let Some(free) = self.sharing.legs.get(&term)
        else {
            return Ok(Recall::Unshared);
        };
        let environment = self.envs.get(env.0).ok_or(EvalFault::MachineInvariant)?;
        let zones = [
            (Zone::Intuitionistic, free.intuitionistic()),
            (Zone::Linear, free.linear()),
        ];
        let mut entries = Vec::new();
        for (zone, indices) in zones {
            for &index in indices.counts() {
                let Some(bound) = environment.lookup(zone, index)
                else {
                    return Ok(Recall::Unshared);
                };
                entries.push(bound);
            }
        }
        let configuration = Configuration { term, entries };
        if let Some(&remembered) = self.sharing.remembered.get(&configuration) {
            return Ok(Recall::Remembered(remembered));
        }
        let pending = PendingId(self.sharing.pending.len());
        self.sharing.pending.push(Some(configuration));
        self.tasks.push(Task::Remember(pending));
        Ok(Recall::Pending)
    }

    /// Remember the weak head on the stack as `pending`'s evaluation.
    ///
    /// # Specification
    /// - requires: the topmost result of the configuration's polarity is the
    ///   weak head its evaluation left.
    /// - ensures: the configuration is remembered at that weak head and taken
    ///   off the pending list; the result stays on the stack for the frame that
    ///   consumes it.
    /// - provides: the recording half of the closed-configuration rule.
    /// - fails: [`EvalFault::MachineInvariant`] when `pending` names no
    ///   configuration under way or no result of its polarity is on the stack.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::MachineInvariant`] — the configuration or its result is
    ///   missing. The pending slot is taken before reading the result, so a
    ///   missing result consumes that slot without recording a weak head.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same free bindings are evaluated once even when
    ///   an unused binding differs, but exchanging values between zones
    ///   produces a different pair and incurs the first-evaluation cost again.
    ///   Remembering the wrong head, consuming its operand or conflating keys
    ///   changes those observations.
    /// - witness: `eval::tests::shared_configurations_distinguish_zones_but_ignore_unused_bindings`
    /// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
    #[spec(
        captures: [entry_pending = self.sharing.pending.len(), entry_remembered = self.sharing.remembered.len(),
            entry_values = self.values.len(), entry_comps = self.comps.len(),
            entry_value = self.values.last().copied(), entry_comp = self.comps.last().copied(),
            entry_configuration = self.sharing.pending.get(pending.0).and_then(Option::as_ref).cloned()],
        ensures: |ret| self.sharing.pending.len() == entry_pending
            && self.sharing.pending.get(pending.0).is_none_or(Option::is_none)
            && self.values.len() == entry_values && self.comps.len() == entry_comps
            && self.values.last().copied() == entry_value && self.comps.last().copied() == entry_comp
            && {
                let produced = entry_configuration.as_ref().and_then(|configuration| match configuration.term {
                    CoreTerm::Value(_) => entry_value.map(Glued::Value),
                    CoreTerm::Computation(_) => entry_comp.map(Glued::Computation),
                });
                match produced {
                    None => ret == Err(EvalFault::MachineInvariant) && self.sharing.remembered.len() == entry_remembered,
                    Some(produced) => ret.is_ok()
                        && (self.sharing.remembered.len() == entry_remembered || self.sharing.remembered.len() == entry_remembered.saturating_add(1_usize))
                        && entry_configuration.as_ref().and_then(|configuration| self.sharing.remembered.get(configuration)) == Some(&produced),
                }
            },
    )]
    fn remember(
        &mut self,
        pending: PendingId,
    ) -> Result<(), EvalFault>
    {
        let Some(configuration) = self
            .sharing
            .pending
            .get_mut(pending.0)
            .and_then(Option::take)
        else {
            return Err(EvalFault::MachineInvariant);
        };
        let produced = match configuration.term {
            CoreTerm::Value(_) => self.values.last().copied().map(Glued::Value),
            CoreTerm::Computation(_) => self.comps.last().copied().map(Glued::Computation),
        };
        let Some(produced) = produced
        else {
            return Err(EvalFault::MachineInvariant);
        };
        self.sharing.remembered.insert(configuration, produced);
        Ok(())
    }
}

/// The face a domain value carries, read off the arena.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input.
/// - ensures: the term face of the node `value` names, which every value arm
///   carries in the same field.
/// - provides: the one read of a value's face, so the face check below never
///   matches on the value's own former.
/// - fails: returns `None` when the id names no node of the value family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unchanged leaves retain their exact source ids while
///   substituted children and captured closures lose their source faces.
///   Returning a generic source or Reduced for every value confuses those
///   cases.
/// - witness: `eval::tests::the_leaf_and_lift_arms_evaluate_and_keep_their_faces`
/// - witness: `eval::tests::a_substituted_child_costs_the_composite_its_face`
/// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
#[spec(ensures: |ret| ret == domain.value(value).map(DomainValue::face))]
fn face_of(
    domain: &DomainArena,
    value: DomainValueId,
) -> Option<TermFace>
{
    domain.value(value).map(DomainValue::face)
}

/// Whether a node's source face survives the evaluation of what is under it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum SourceKept
{
    /// Nothing under this node reduced, so the source term still denotes it.
    Kept,
    /// Something under it reduced or was substituted.
    Lost,
}

impl SourceKept
{
    /// The verdict for a node whose survival needs both of two parts to
    /// survive.
    ///
    /// Written out rather than delegated to a boolean conjunction, so the table
    /// is total over its own definition and a third verdict added later has to
    /// answer here.
    ///
    /// # Specification
    /// - requires: nothing; both verdicts are admissible on either side.
    /// - ensures: [`SourceKept::Kept`] exactly when both sides kept their
    ///   source, and [`SourceKept::Lost`] otherwise.
    /// - provides: the composition every multi-child face decision goes
    ///   through, written as a total table for the reason above.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wholly unchanged pair keeps its face and a pair
    ///   with one substituted child loses it. Replacing conjunction by
    ///   disjunction incorrectly preserves the second pair.
    /// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
    /// - witness: `eval::tests::a_substituted_child_costs_the_composite_its_face`
    #[inline]
    #[spec(
        ensures: |ret| (ret == Self::Kept) == (self == Self::Kept && other == Self::Kept),
    )]
    fn and(
        self,
        other: Self,
    ) -> Self
    {
        match (self, other) {
            (Self::Kept, Self::Kept) => Self::Kept,
            (Self::Kept, Self::Lost) | (Self::Lost, Self::Kept | Self::Lost) => Self::Lost,
        }
    }
}

/// Whether `value` came back denoting exactly the source node `source`.
///
/// This is the whole content of "nothing inside it reduced", applied one child
/// at a time.
///
/// # Specification
/// - requires: nothing — a dangling domain id is admissible input and reads as
///   having lost its source.
/// - ensures: [`SourceKept::Kept`] exactly when `value` carries the source face
///   naming `source` itself, and [`SourceKept::Lost`] for a reduced face,
///   another source node, or an id that resolves to nothing.
/// - provides: the per-child test the composite face decisions are built from,
///   so "nothing inside it reduced" is decided one child at a time.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unchanged source children are distinguished from supplied
///   values with another source and from reduced faces. Ignoring source
///   identity gives a substituted composite its original face.
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
/// - witness: `eval::tests::a_substituted_child_costs_the_composite_its_face`
#[spec(
    ensures: |ret| (ret == SourceKept::Kept) == (face_of(domain, value) == Some(TermFace::Source(source))),
)]
fn denotes(
    domain: &DomainArena,
    value: DomainValueId,
    source: ValueId,
) -> SourceKept
{
    if face_of(domain, value) == Some(TermFace::Source(source)) {
        return SourceKept::Kept;
    }
    SourceKept::Lost
}

/// Whether a closure over `environment` may keep its source face.
///
/// It may exactly when the environment binds nothing, because a closure over a
/// non-empty environment denotes its body only up to what the environment
/// supplies.
///
/// # Specification
/// - requires: nothing; every environment is admissible input.
/// - ensures: [`SourceKept::Kept`] exactly when both zones are empty, and
///   [`SourceKept::Lost`] as soon as either binds anything.
/// - provides: the closure-side face decision, kept separate from the
///   child-side one because a closure's body is not evaluated and so has no
///   child to compare.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — closed lambdas and quotes keep their source faces, while
///   closures carrying substitutions lose them. Ignoring the captured
///   environment gives the open closure a source shortcut it cannot justify.
/// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
/// - witness: `eval::tests::native_cases_reapply_when_head_unfolds`
#[spec(
    ensures: |ret| (ret == SourceKept::Kept)
        == (usize::from(environment.depth(Zone::Intuitionistic)) == 0_usize
            && usize::from(environment.depth(Zone::Linear)) == 0_usize),
)]
fn capture_keeps_source(environment: &Environment) -> SourceKept
{
    if environment.depth(Zone::Intuitionistic) == EnvironmentDepth::from(0_usize)
        && environment.depth(Zone::Linear) == EnvironmentDepth::from(0_usize)
    {
        return SourceKept::Kept;
    }
    SourceKept::Lost
}

/// The face a composite keeps: its own source when every child denotes the
/// corresponding source child, and `Reduced` otherwise.
///
/// # Specification
/// - requires: `term` is the source node the composite was evaluated from, and
///   `kept` is the verdict over its children.
/// - ensures: the source face naming `term` exactly when `kept` is
///   [`SourceKept::Kept`], and [`TermFace::Reduced`] otherwise.
/// - provides: the single site that turns a survival verdict into a face, so no
///   rule mints a source face over children that reduced.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an unchanged composite retains its own source id and a
///   composite with a substituted child is Reduced. Inverting the verdict or
///   using a child source changes these faces.
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
/// - witness: `eval::tests::a_substituted_child_costs_the_composite_its_face`
#[spec(
    ensures: |ret| ret == match kept { SourceKept::Kept => TermFace::Source(term), SourceKept::Lost => TermFace::Reduced },
)]
fn composite_face(
    kept: SourceKept,
    term: ValueId,
) -> TermFace
{
    match kept {
        SourceKept::Kept => TermFace::Source(term),
        SourceKept::Lost => TermFace::Reduced,
    }
}

/// The negative side's counterpart of [`composite_face`].
///
/// # Specification
/// - requires: `term` is the source node the composite was evaluated from, and
///   `kept` is the verdict over its children.
/// - ensures: the source face naming `term` exactly when `kept` is
///   [`SourceKept::Kept`], and [`CompTermFace::Reduced`] otherwise.
/// - provides: the negative side's single verdict-to-face site.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a closed lambda retains its source but a captured lambda
///   and a return of a substituted value are Reduced. Keeping an original
///   source after substitution changes these observations.
/// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
/// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
#[spec(
    ensures: |ret| ret == match kept { SourceKept::Kept => CompTermFace::Source(term), SourceKept::Lost => CompTermFace::Reduced },
)]
fn composite_comp_face(
    kept: SourceKept,
    term: ComputationId,
) -> CompTermFace
{
    match kept {
        SourceKept::Kept => CompTermFace::Source(term),
        SourceKept::Lost => CompTermFace::Reduced,
    }
}

/// Mint a neutral that is `neutral` with one more elimination on its spine.
///
/// The unfolding face rides along unchanged: it names the *head's* body, and
/// forcing it means unfolding the head and re-applying the whole spine, which
/// stays well defined however long the spine grows.
///
/// # Specification
/// - requires: nothing — a dangling neutral id is admissible input.
/// - ensures: on success a fresh neutral with `neutral`'s head and unfolding
///   face and its spine with `elimination` appended, leaving `neutral` itself
///   unchanged.
/// - provides: the one growth step of a stuck spine, shared by all four
///   eliminator rules. The clause states the fresh neutral's head, unfolding
///   face and source form against the entry metadata, and compares the grown
///   prefix with the still-held source spine without copying an entry snapshot.
/// - fails: [`EvalFault::Domain`] carrying [`DomainFault::Dangling`] when the
///   id names no neutral. The head-against-face condition the arena re-checks
///   cannot fail here: both come off a neutral the arena already accepted, so
///   it holds by transport — and the refusal is carried rather than swallowed.
/// - panics: none.
// economy: the spine is copied to grow it, so stacking n eliminations on one
// stuck head costs O(n^2) copying. Upgrade path: hold the spine as an
// id-addressed cons chain in its own arena family, where extending is one cell
// and the tail is shared — the same flat-representation move the arena already
// makes for terms, not taken here because it costs every reader of `spine()` a
// walk in exchange.
/// # Adequacy
/// - hypothesis: L3 — force, application, bind and case grow stuck spines, and
///   a mixed spine replays to the same returned value after unfolding. Dropping
///   the prefix, reversing frames or replacing a captured closure changes that
///   result.
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::a_reapplied_spine_fires_once_the_head_unfolds`
/// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
#[spec(
    captures: [entry_form = domain.neutral(neutral).map(|held| (held.head(), held.unfolding(), held.spine().len()))],
    ensures: |ret| match ret {
        Ok(fresh) => domain.neutral(fresh).map(|held| (held.head(), held.unfolding(), held.spine().len()))
            == entry_form.map(|form| (form.0, form.1, form.2.saturating_add(1_usize)))
            && domain.neutral(neutral).map(|held| (held.head(), held.unfolding(), held.spine().len())) == entry_form
            && domain.neutral(neutral).zip(domain.neutral(fresh)).is_some_and(|(source, grown)| {
                grown.spine().split_last().is_some_and(|(last, prefix)| *last == elimination && prefix == source.spine())
            }),
        Err(fault) => fault == EvalFault::Domain(DomainFault::Dangling) && entry_form.is_none(),
    },
)]
pub fn extend_spine(
    domain: &mut DomainArena,
    neutral: NeutralId,
    elimination: Elimination,
) -> Result<NeutralId, EvalFault>
{
    let held = domain
        .neutral(neutral)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let head = held.head();
    let unfolding = held.unfolding();
    let mut spine = Vec::from(held.spine());
    spine.push(elimination);
    domain
        .neutral_node(head, spine, unfolding)
        .map_err(EvalFault::Domain)
}

/// Evaluate a core value in the empty environment, minting into `domain`.
///
/// # Specification
/// - requires: `term` resolves in `core`; the caller's budget is the only bound
///   on the machine, so a term whose weak-head evaluation diverges is declined
///   rather than run.
/// - ensures: on success a domain value whose term face names `term` exactly
///   when nothing inside it reduced, and whose neutrals carry the unfolding
///   face `definitions` gives their heads.
/// - provides: the value half of evaluation to weak head, which is total: a
///   value has no redex of its own, so "weak head" is the whole value. The
///   clause states that a successful result resolves in `domain`; that the term
///   face names `term` exactly when nothing inside it reduced, and that every
///   neutral in the result carries the unfolding face `definitions` gives its
///   head, are judgements over the whole produced graph rather than over one
///   call's exit state, and the witnesses below carry them.
/// - fails: every variant of [`EvalFault`]. A refusal returns no produced id;
///   the arena may retain nodes minted before the refusal.
///   [`EvalFault::DanglingTerm`] is publicly reachable when the passed core
///   arena holds no node at the supplied term id.
/// - panics: none — every stack read is checked and every arithmetic step is
///   saturating.
/// - intension: the machine performs one task per step and spends one unit of
///   fuel per step, so the fuel is an observable step count rather than a
///   heuristic. Sub-values are evaluated left to right.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the value arms and the face
///   check, separated by each leaf arm keeping its face, a composite whose
///   children both keep theirs, a composite and a lift with one substituted
///   child that must lose it, a variable resolving out of the environment, and
///   a constant at each unfolding stance.
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
/// - witness: `eval::tests::the_leaf_and_lift_arms_evaluate_and_keep_their_faces`
/// - witness: `eval::tests::a_lift_over_a_substituted_body_loses_its_face`
/// - witness: `eval::tests::a_substituted_child_costs_the_composite_its_face`
/// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
/// - witness: `eval::tests::a_term_from_another_arena_is_refused`
/// - witness: `eval::tests::a_refused_evaluation_leaves_existing_values_usable`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all, fields(fuel = u32::from(fuel))))]
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|value| domain.value(*value).is_some()))]
pub fn eval_value(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    term: ValueId,
) -> Result<DomainValueId, EvalFault>
{
    let (value, _remaining) = eval_closed_value(core, domain, definitions, fuel, term)?;
    Ok(value)
}

/// Evaluate a closed core value, reporting the budget the run did not spend.
///
/// # Specification
/// - requires: `term` resolves in `core` and is closed.
/// - ensures: on success the value `term` evaluates to, paired with the fuel
///   left over — one unit per task the run popped, subtracted from `fuel`.
/// - provides: the entry a readback forces a lowered body through, spending
///   from its own budget rather than from a fresh one. The clause states that
///   the produced value resolves in `domain` and that the reported remainder
///   does not exceed `fuel`.
/// - fails: every variant of [`EvalFault`]; [`EvalFault::UnboundVariable`] when
///   `term` is not closed.
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the reported remainder, separated
///   by a forced body whose cost the readback's remainder carries.
/// - witness: `readback::tests::a_lowered_definition_body_unfolds_through_readback`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.value(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
pub fn eval_closed_value(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    term: ValueId,
) -> Result<(DomainValueId, Fuel), EvalFault>
{
    let mut machine = Machine::new(definitions, fuel);
    let env = Machine::root_env();
    machine.tasks.push(Task::Value { term, env });
    run(core, domain, &mut machine)?;
    let value = machine.pop_value()?;
    Ok((value, machine.fuel))
}

/// Evaluate a core computation to weak head in the empty environment.
///
/// # Specification
/// - requires: `term` resolves in `core`.
/// - ensures: on success a domain computation in weak-head form — a lambda
///   closure, a returner, or a neutral carrying the eliminations that could not
///   fire.
/// - provides: the computation half of evaluation, stopping at weak head rather
///   than normalizing, which is what leaves the readback free to choose how far
///   to go. The clause states that a successful result resolves in `domain`;
///   that it is in weak-head form is a judgement over the produced graph rather
///   than over one call's exit state, and the witnesses below carry it.
/// - fails: every variant of [`EvalFault`].
/// - panics: none.
/// - intension: one task per step, one unit of fuel per step. An application
///   evaluates its argument before its head, which is the order
///   call-by-push-value fixes rather than a choice made here: a value cannot
///   diverge, so evaluating it first costs nothing and keeps the argument
///   available to the frame that needs it. The order is observable through the
///   refusal an application reports when **both** sides fault *during their own
///   evaluation*: it is the argument's fault, never the head's. A fault raised
///   at the application's own frame would not separate the orders, because that
///   frame runs after both operands either way.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the computation arms and the
///   three stuck branches, separated by a β-redex that fires, a bind on a
///   returner, a case on each injection, and each eliminator applied to a
///   neutral so the spine grows instead.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::a_case_picks_the_branch_the_injection_names`
/// - witness: `eval::tests::a_loop_declines_on_fuel_rather_than_diverging`
/// - witness: `eval::tests::an_application_reports_its_arguments_fault_first`
#[cfg_attr(feature = "tracing", tracing::instrument(skip_all, fields(fuel = u32::from(fuel))))]
#[inline]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|produced| domain.computation(*produced).is_some()))]
pub fn eval_computation(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    term: ComputationId,
) -> Result<DomainCompId, EvalFault>
{
    let (produced, _remaining) =
        eval_comp_within(core, domain, definitions, fuel, term, Environment::new())?;
    Ok(produced)
}

/// Evaluate a core computation to weak head in `environment`, reporting the
/// budget the run did not spend.
///
/// # Specification
/// - requires: `term` resolves in `core`; `environment` binds every occurrence
///   `term` counts past its own binders, in the zone that occurrence names.
/// - ensures: on success the weak head of `term` read in `environment`, paired
///   with the fuel left over — one unit per task the run popped, subtracted
///   from `fuel`.
/// - provides: the one entry that starts a run from a non-empty environment,
///   which is how a readback goes under a binder: it binds a fresh variable and
///   evaluates the closure's body against the extended environment, spending
///   from the readback's own budget rather than from a fresh one. The clause
///   states that the produced head resolves in `domain` and that the reported
///   remainder does not exceed `fuel`; the remainder's exact value is one unit
///   per task the run popped, a count no argument or exit state carries, and
///   the witness below asserts it.
/// - fails: every variant of [`EvalFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the supplied environment and
///   the reported remainder, separated by a body that reads the supplied
///   binding, the same body read against the empty environment so the binding
///   is what answers it, and a remainder asserted as an exact step count rather
///   than as "some fuel is left".
/// - witness: `eval::tests::an_evaluation_in_a_supplied_environment_reports_its_remainder`
#[cfg_attr(feature = "tracing", tracing::instrument(level = "debug", skip_all, fields(fuel = u32::from(fuel))))]
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.computation(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
#[inline]
pub fn eval_comp_within(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    term: ComputationId,
    environment: Environment,
) -> Result<(DomainCompId, Fuel), EvalFault>
{
    eval_body_within(
        core,
        domain,
        definitions,
        fuel,
        crate::closure::CompBody::Source(term),
        environment,
    )
}

/// Evaluate a captured source or native transport body in its environment.
///
/// # Specification
/// - requires: the environment supplies all free source variables or the native
///   continuation's innermost result binder.
/// - ensures: the body's weak head and the unspent task allowance.
/// - provides: one shared driver for source closures and native continuations.
/// - fails: a domain, evaluation or budget fault.
/// - panics: none.
///
/// # Errors
/// Any `EvalFault`.
///
/// # Adequacy
/// - hypothesis: L3 — nested product transport preserves component order.
/// - witness: `eval::tests::native_transport_sequences_product_components`
#[spec(ensures: |ret| match ret { Ok((id, remaining)) => domain.computation(id).is_some() && u32::from(remaining) < u32::from(fuel), Err(EvalFault::OutOfFuel) => true, Err(_) => u32::from(fuel) > 0 })]
pub fn eval_body_within(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    body: crate::closure::CompBody,
    environment: Environment,
) -> Result<(DomainCompId, Fuel), EvalFault>
{
    let mut machine = Machine::new(definitions, fuel);
    let env = machine.hold_env(environment);
    machine.tasks.push(Task::Body { body, env });
    run(core, domain, &mut machine)?;
    let produced = machine.pop_comp()?;
    Ok((produced, machine.fuel))
}

/// Evaluate a core value in `environment`, reporting the budget the run did
/// not spend.
///
/// # Specification
/// - requires: `term` resolves in `core`; `environment` binds every occurrence
///   `term` counts past its own binders, in the zone that occurrence names.
/// - ensures: on success the domain value of `term` read in `environment`,
///   paired with the fuel left over.
/// - provides: the value twin of [`eval_comp_within`], which is how a readback
///   reads a decode's code inside a quoted type — in the quote's environment,
///   extended by the binders the type's own dependent arrows open — and how a
///   caller certifies a conversion between open values, their free binders read
///   as rigid variables it supplies.
/// - fails: every variant of [`EvalFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the supplied environment is the one decision surface,
///   separated by a quoted decode whose code is a variable the environment
///   binds.
/// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.value(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
#[inline]
pub fn eval_value_within(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    term: ValueId,
    environment: Environment,
) -> Result<(DomainValueId, Fuel), EvalFault>
{
    let mut machine = Machine::new(definitions, fuel);
    let env = machine.hold_env(environment);
    machine.tasks.push(Task::Value { term, env });
    run(core, domain, &mut machine)?;
    let produced = machine.pop_value()?;
    Ok((produced, machine.fuel))
}

/// Apply the operator `head` to `arguments` in order, reporting the budget
/// the run did not spend.
///
/// # Specification
/// - requires: `head` and every argument resolve in `domain`.
/// - ensures: on success the domain value of `head` applied to each argument in
///   turn — static beta wherever the operator is a static lambda, a grown
///   neutral wherever it is stuck — paired with the fuel left over.
/// - provides: the re-application a readback spends an unfolded operator
///   through: an unfolded head's body meets the neutral's static spine by beta
///   rather than standing beside it as a redex, which is what makes the
///   readback a static normal form.
/// - fails: every variant of [`EvalFault`]; [`EvalFault::AppliedNonOperator`]
///   for an operator neither a static lambda nor stuck.
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the per-argument beta, separated
///   by an unfolded operator of two parameters read back at two arguments.
/// - witness: `readback::tests::an_unfolded_operator_reads_back_reduced`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        domain.value(pair.0).is_some() && u32::from(pair.1) <= u32::from(fuel)
    }))]
pub fn apply_static_within(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    head: DomainValueId,
    arguments: &[DomainValueId],
) -> Result<(DomainValueId, Fuel), EvalFault>
{
    let mut machine = Machine::new(definitions, fuel);
    for &argument in arguments.iter().rev() {
        machine.tasks.push(Task::StaticApply);
        machine.tasks.push(Task::Supply(argument));
    }
    machine.values.push(head);
    if !machine.tasks.is_empty() {
        run(core, domain, &mut machine)?;
    }
    let produced = machine.pop_value()?;
    Ok((produced, machine.fuel))
}

/// Evaluate a closed core term to weak head in the empty environment, sharing
/// each leg of `legs` across the occurrences that read it in one
/// configuration.
///
/// # Specification
/// - requires: `root` resolves in `core` and is closed; each leg of `legs` is a
///   term of `core` paired with exactly its free indices.
/// - ensures: on success the weak head of `root`, paired with the fuel left
///   over — one unit per task the run popped. A leg met in a configuration
///   already evaluated is not evaluated again: the occurrence costs the one
///   step that popped it, and the first evaluation of each configuration one
///   step more, for the task that remembers it.
/// - provides: the machine behind the overlay evaluator's sharing run. The
///   clause states that the produced head resolves in `domain`, in the polarity
///   of `root`, and that the remainder does not exceed `fuel`; which
///   evaluations were shared is a count no exit state carries, and the
///   witnesses below read it off the step count.
/// - fails: every variant of [`EvalFault`].
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the leg table and the
///   configuration key, separated by a rib shared across two applications of
///   one closure, a subterm under an inner binder read under one binding at
///   both copies, and a leg whose free index names a different binder at its
///   two occurrences, each read off the step count against the unshared run.
/// - witness: `full_laziness::full_laziness::a_spinal_duplicate_shares_every_rib`
/// - witness:
///   `full_laziness::full_laziness::a_spinal_duplicate_shares_what_full_laziness_copies`
/// - witness:
///   `full_laziness::full_laziness::an_open_configuration_is_evaluated_per_occurrence`
#[spec(ensures: |ret| ret.is_err()
    || ret.as_ref().is_ok_and(|pair| {
        u32::from(pair.1) <= u32::from(fuel)
            && match (root, pair.0) {
                | (CoreTerm::Value(_), Glued::Value(value)) => domain.value(value).is_some(),
                | (CoreTerm::Computation(_), Glued::Computation(comp)) => {
                    domain.computation(comp).is_some()
                },
                | (CoreTerm::Value(_), Glued::Computation(_))
                | (CoreTerm::Computation(_), Glued::Value(_)) => false,
            }
    }))]
pub fn eval_sharing(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    root: CoreTerm,
    legs: BTreeMap<CoreTerm, Free>,
) -> Result<(Glued, Fuel), EvalFault>
{
    let mut machine = Machine::new(definitions, fuel);
    machine.sharing.legs = legs;
    let env = Machine::root_env();
    machine.tasks.push(match root {
        CoreTerm::Value(term) => Task::Value { term, env },
        CoreTerm::Computation(term) => Task::Comp { term, env },
    });
    run(core, domain, &mut machine)?;
    let produced = match root {
        CoreTerm::Value(_) => machine.pop_value().map(Glued::Value),
        CoreTerm::Computation(_) => machine.pop_comp().map(Glued::Computation),
    };
    let produced = produced?;
    Ok((produced, machine.fuel))
}

/// How far one slice of a resumable evaluation got.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Progress
{
    /// The evaluation reached its weak head.
    Finished(Glued),
    /// The slice ran out with work still on the task stack.
    Paused,
}

/// Which result stack an evaluation's answer lands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Answer
{
    /// A value: a definition body.
    Value,
    /// A weak-head computation: an entered closure or a re-applied spine.
    Computation,
}

/// What a slice of the machine's loop ended on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SliceEnd
{
    /// The task stack emptied.
    Drained,
    /// The slice's budget ran out before the task stack emptied.
    Spent,
}

/// An evaluation that runs in slices, its machine kept between them.
///
/// The conversion machine interleaves evaluations with comparisons, so an
/// evaluation cannot run to its end in one call: a diverging one would hold
/// the scheduler. This keeps the task stack, the result stacks and the
/// environments across slices, so a resumed evaluation continues where it
/// stopped rather than restarting.
pub struct Evaluation<'run>
{
    /// The machine, with whatever the last slice left on its stacks.
    machine: Machine<'run>,
    /// Which stack the answer lands on.
    answer: Answer,
}

impl<'run> Evaluation<'run>
{
    /// An evaluation of a closed definition body.
    ///
    /// # Specification
    /// - requires: `body` is closed and resolves in the core arena the slices
    ///   will read.
    /// - ensures: an evaluation whose first slice starts at `body` in the empty
    ///   environment and whose answer is a value.
    /// - provides: the channel a skeleton-granularity run mints once per
    ///   distinct body entry.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a zero-step first slice pauses and the next exact
    ///   one-step slice produces the requested unit with its source face.
    ///   Losing or replacing the initial task changes that answer.
    /// - witness: `eval::tests::a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause`
    #[spec(
        ensures: |ret| ret.answer == Answer::Value && ret.machine.fuel.0 == 0_u32
            && matches!(ret.machine.tasks.as_slice(), [Task::Value { term, env }] if *term == body && env.0 == 0_usize),
    )]
    pub(crate) fn body(
        definitions: Definitions<'run>,
        body: ValueId,
    ) -> Self
    {
        let mut machine = Machine::new(definitions, Fuel(0_u32));
        let env = Machine::root_env();
        machine.tasks.push(Task::Value { term: body, env });
        Self {
            machine,
            answer: Answer::Value,
        }
    }

    /// An evaluation re-applying `spine` to `head`, innermost elimination
    /// first.
    ///
    /// # Specification
    /// - requires: `spine` is non-empty and its first elimination eliminates a
    ///   value — a force, case, transport or static application — as every
    ///   neutral's spine does.
    /// - ensures: an evaluation whose answer is the weak head of `head` under
    ///   `spine`'s eliminations, in order: a value when every elimination is a
    ///   static application, a computation otherwise.
    /// - provides: the unfolding of a neutral whose head's body is `head`: the
    ///   body stands where the head stood and the spine runs again, so an
    ///   unfolded type operator meets its arguments by static beta.
    /// - fails: never here; an ill-shaped spine is refused by the slice that
    ///   reaches it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed force/application/bind spine reduces after
    ///   unfolding, two case branches retain different captures, and later
    ///   ill-shaped eliminations refuse by variant. Reversing frames or
    ///   supplying an argument after its consumer changes the answer or the
    ///   refusal.
    /// - witness: `eval::tests::a_reapplied_spine_fires_once_the_head_unfolds`
    /// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
    /// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[spec(
        requires: matches!(spine.first(), Some(Elimination::ListFold { .. } | Elimination::DataCase(_) | Elimination::Split(_) | Elimination::Projection(_) | Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::PathTransport { .. } | Elimination::Ride { .. } | Elimination::TelescopeTransport { .. } | Elimination::Force | Elimination::Case(_) | Elimination::StaticApply(_) | Elimination::Fixpoint(_))),
        ensures: |ret| ret.machine.values.as_slice() == [head] && ret.machine.comps.is_empty()
            && ret.machine.fuel.0 == 0_u32 && {
                let mut tasks = ret.machine.tasks.iter().rev();
                let mut answer = Answer::Value;
                let ordered = spine.iter().all(|elimination| match *elimination {
                    Elimination::DataCase(closure) => { answer = Answer::Computation; matches!(tasks.next(),Some(Task::DataCaseClosure(held)) if *held == closure) },
                    Elimination::Split(closure) => { answer = Answer::Computation; matches!(tasks.next(),Some(Task::SplitClosure(held)) if *held == closure) },
                    Elimination::Projection(term) => { answer = Answer::Computation; matches!(tasks.next(),Some(Task::Projection(held)) if *held == term) },
                    Elimination::Transport(value) => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(held)) if *held == value) && matches!(tasks.next(), Some(Task::Transport)) },
                    Elimination::ProductTransport(path) => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::ProductTransport(held)) if *held == path) },
                    Elimination::PathTransport { motive, value } => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(held)) if *held == value) && matches!(tasks.next(), Some(Task::PathTransport(held)) if *held == motive) },
                    Elimination::Ride { motive, value } => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(held)) if *held == value) && matches!(tasks.next(), Some(Task::Ride(held)) if *held == motive) },
                    Elimination::TelescopeTransport { motive, start, over, value } => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(held)) if *held == start) && matches!(tasks.next(), Some(Task::Supply(held)) if *held == over)
                        && matches!(tasks.next(), Some(Task::Supply(held)) if *held == value) && matches!(tasks.next(), Some(Task::TelescopeTransport(held)) if *held == motive) },
                    Elimination::StaticApply(argument) => matches!(tasks.next(), Some(Task::Supply(value)) if *value == argument)
                        && matches!(tasks.next(), Some(Task::StaticApply)),
                    Elimination::Apply(argument) => {
                        answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(value)) if *value == argument) && matches!(tasks.next(), Some(Task::Apply))
                    },
                    Elimination::Force => { answer = Answer::Computation; matches!(tasks.next(), Some(Task::Force)) },
                    Elimination::Bind(body) => { answer = Answer::Computation; matches!(tasks.next(), Some(Task::BindClosure(held)) if *held == body) },
                    Elimination::ListFold { element, result, on_nil, on_cons } => {
                        answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::ListFold { element: e, result: r, on_nil: n, on_cons: c }) if (*e,*r,*n,*c) == (element,result,on_nil,on_cons))
                    },
                    Elimination::Case(branches) => {
                        answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::CaseBranches(held)) if *held == branches)
                    },
                    Elimination::Fixpoint(recursive) => { answer = Answer::Computation; matches!(tasks.next(), Some(Task::FixpointClosure(held)) if *held == recursive) },
                });
                ordered && tasks.next().is_none() && ret.answer == answer
            },
    )]
    pub(crate) fn eliminate(
        definitions: Definitions<'run>,
        head: DomainValueId,
        spine: &[Elimination],
    ) -> Self
    {
        let mut machine = Machine::new(definitions, Fuel(0_u32));
        let answer = push_eliminations(&mut machine, spine);
        machine.values.push(head);
        Self { machine, answer }
    }

    /// An evaluation of a held endpoint once the definition its computation
    /// is stuck on unfolds: `inner` re-applied to `head`, the computation that
    /// gives delivered as a value, and each spine of `enclosing`, innermost
    /// last in the slice, applied to what the one inside it delivers.
    ///
    /// # Specification
    /// - requires: `inner` is the spine of the neutral computation the
    ///   innermost endpoint holds, so it is non-empty, its first elimination
    ///   eliminates a value and the last leaves a computation; `enclosing`
    ///   holds the endpoint's own spine first, then the spine of each neutral
    ///   computation between it and `inner`, outermost first, so it is
    ///   non-empty.
    /// - ensures: an evaluation whose stacks hold `head` alone and whose tasks
    ///   run `inner`'s eliminations, then, for each spine of `enclosing` from
    ///   the last to the first, one delivery of the returned value and that
    ///   spine's eliminations; its answer is a value when every elimination of
    ///   the first spine is a static application, a computation otherwise.
    /// - provides: the unfolding of a held endpoint, `E[c]` with `c` stuck on a
    ///   definition: the definition's body stands where it stood, the endpoint
    ///   delivers what `c` then returns, and `E` runs on it. A nested endpoint
    ///   `E[F[c]]`, where `F` eliminates the endpoint over `c`, delivers twice.
    /// - fails: never here; an ill-shaped spine is refused by the slice that
    ///   reaches it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held endpoint nested under a force and an
    ///   application unfolds to the value its definition returns and runs the
    ///   force on it, one under another endpoint's elimination runs that
    ///   elimination on the value, and the kernel replays the recorded
    ///   unfolding at the endpoint's head; dropping a delivery or an enclosing
    ///   spine changes the verdict or the replay.
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
    /// - witness: `machine::tests::a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on`
    #[spec(
        requires: matches!(inner.first(), Some(Elimination::ListFold { .. } | Elimination::DataCase(_) | Elimination::Split(_) | Elimination::Projection(_) | Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::PathTransport { .. } | Elimination::Ride { .. } | Elimination::Force | Elimination::Case(_) | Elimination::StaticApply(_) | Elimination::Fixpoint(_)))
            && !enclosing.is_empty(),
        ensures: |ret| ret.machine.values.as_slice() == [head] && ret.machine.comps.is_empty()
            && ret.machine.fuel.0 == 0_u32
            && ret.machine.tasks.iter().filter(|task| matches!(task, Task::Returned)).count() == enclosing.len()
            && ret.answer == if enclosing.first().is_none_or(|outer| outer.iter().all(|elimination| matches!(elimination, Elimination::StaticApply(_)))) {
                Answer::Value
            } else {
                Answer::Computation
            },
    )]
    pub(crate) fn endpoint(
        definitions: Definitions<'run>,
        head: DomainValueId,
        inner: &[Elimination],
        enclosing: &[&[Elimination]],
    ) -> Self
    {
        let mut machine = Machine::new(definitions, Fuel(0_u32));
        let mut answer = Answer::Value;
        if let Some((outer, within)) = enclosing.split_first() {
            answer = push_eliminations(&mut machine, outer);
            machine.tasks.push(Task::Returned);
            for spine in within {
                let _computation = push_eliminations(&mut machine, spine);
                machine.tasks.push(Task::Returned);
            }
        }
        let _computation = push_eliminations(&mut machine, inner);
        machine.values.push(head);
        Self { machine, answer }
    }

    /// An evaluation of a closure's body, in its environment extended by
    /// `bound` when one is given.
    ///
    /// # Specification
    /// - requires: `closure` resolves in `domain`.
    /// - ensures: an evaluation whose answer is the weak head of the closure's
    ///   body, read in its captured environment with `bound` as the innermost
    ///   intuitionistic binding when it is [`Bound::Variable`].
    /// - provides: the two closure channels: entering a thunk, and opening a
    ///   binder under a fresh variable.
    /// - fails: [`EvalFault::Domain`] when `closure` does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EvalFault::Domain`] — `closure` names no closure of `domain`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk resumes under its captured environment, while
    ///   opening a lambda adds its argument inside the existing capture.
    ///   Emptying the capture or opening in the wrong zone changes the weak
    ///   head and the conversion verdict.
    /// - witness: `eval::tests::a_sliced_evaluation_agrees_with_an_unsliced_one`
    /// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
    /// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
    /// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[spec(
        ensures: |ret| ret.as_ref().map_or_else(
            |fault| *fault == EvalFault::Domain(DomainFault::Dangling) && domain.comp_closure(closure).is_none(),
            |evaluation| evaluation.answer == Answer::Computation && evaluation.machine.fuel.0 == 0_u32
                && domain.comp_closure(closure).is_some_and(|held| match evaluation.machine.tasks.as_slice() {
                    &[Task::Body { body: term, env }] => term == held.body() && evaluation.machine.envs.get(env.0).is_some_and(|environment| match bound {
                        Bound::Nothing => environment == held.environment(),
                        Bound::Variable(variable) => usize::from(environment.depth(Zone::Intuitionistic))
                            == usize::from(held.environment().depth(Zone::Intuitionistic)).saturating_add(1_usize)
                            && environment.depth(Zone::Linear) == held.environment().depth(Zone::Linear)
                            && environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(variable),
                        Bound::Variables(variables) => usize::from(environment.depth(Zone::Intuitionistic))
                            == usize::from(held.environment().depth(Zone::Intuitionistic)).saturating_add(variables.len())
                            && environment.depth(Zone::Linear) == held.environment().depth(Zone::Linear)
                            && variables.iter().rev().enumerate().all(|(index, &variable)| u32::try_from(index)
                                .is_ok_and(|index| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(index)) == Some(variable))),
                    }),
                    _ => false,
                }),
        ),
    )]
    pub(crate) fn enter(
        definitions: Definitions<'run>,
        domain: &DomainArena,
        closure: CompClosureId,
        bound: Bound<'_>,
    ) -> Result<Self, EvalFault>
    {
        let held = domain
            .comp_closure(closure)
            .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
        let mut environment = held.environment().clone();
        match bound {
            Bound::Nothing => {},
            Bound::Variable(variable) => environment.extend(Zone::Intuitionistic, variable),
            Bound::Variables(variables) => {
                for &variable in variables {
                    environment.extend(Zone::Intuitionistic, variable);
                }
            },
        }
        let term = held.body();
        let mut machine = Machine::new(definitions, Fuel(0_u32));
        let env = machine.hold_env(environment);
        machine.tasks.push(Task::Body { body: term, env });
        Ok(Self {
            machine,
            answer: Answer::Computation,
        })
    }

    /// Run one slice of at most `slice` steps.
    ///
    /// # Specification
    /// - requires: `core` and `domain` are the arenas every earlier slice of
    ///   this evaluation read and minted into.
    /// - ensures: [`Progress::Finished`] with the answer when the task stack
    ///   emptied within the slice, [`Progress::Paused`] otherwise, paired with
    ///   the steps the slice spent, which never exceed `slice`. No task is lost
    ///   at a pause: the budget is checked before a task is popped.
    /// - provides: the resumable step a conversion's evaluation channel takes
    ///   once per scheduler turn.
    /// - fails: every variant of [`EvalFault`] except [`EvalFault::OutOfFuel`],
    ///   which a pause replaces.
    /// - panics: none.
    ///
    /// # Errors
    /// Every variant of [`EvalFault`] a step raises; see its documentation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the pause and the finish,
    ///   separated by a body evaluated in one ample slice against the same body
    ///   driven to its answer through slices of one step each, which must
    ///   agree.
    /// - witness: `eval::tests::a_sliced_evaluation_agrees_with_an_unsliced_one`
    /// - witness: `eval::tests::a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause`
    /// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
    #[spec(
        captures: [entry_tasks = self.machine.tasks.len(), entry_values = self.machine.values.len(), entry_comps = self.machine.comps.len()],
        ensures: |ret| self.machine.fuel.0 <= slice.0 && ret != Err(EvalFault::OutOfFuel)
            && (slice.0 != 0_u32 || entry_tasks == 0_usize || (ret == Ok((Progress::Paused, Fuel(0_u32)))
                && self.machine.tasks.len() == entry_tasks && self.machine.values.len() == entry_values && self.machine.comps.len() == entry_comps))
            && ret.as_ref().map_or(true, |&(progress, spent)| spent.0 == slice.0.saturating_sub(self.machine.fuel.0)
                && match progress {
                    Progress::Paused => !self.machine.tasks.is_empty() && self.machine.fuel.0 == 0_u32,
                    Progress::Finished(Glued::Value(_)) => self.machine.tasks.is_empty() && self.answer == Answer::Value,
                    Progress::Finished(Glued::Computation(_)) => self.machine.tasks.is_empty() && self.answer == Answer::Computation,
                }),
    )]
    pub(crate) fn resume(
        &mut self,
        core: &CoreArena,
        domain: &mut DomainArena,
        slice: Fuel,
    ) -> Result<(Progress, Fuel), EvalFault>
    {
        self.machine.fuel = slice;
        let end = run_slice(core, domain, &mut self.machine)?;
        let spent = Fuel(u32::from(slice).saturating_sub(u32::from(self.machine.fuel)));
        match end {
            SliceEnd::Spent => Ok((Progress::Paused, spent)),
            SliceEnd::Drained => {
                let answer = match self.answer {
                    Answer::Value => Glued::Value(self.machine.pop_value()?),
                    Answer::Computation => Glued::Computation(self.machine.pop_comp()?),
                };
                Ok((Progress::Finished(answer), spent))
            },
        }
    }
}

/// What a closure is entered with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bound<'bound>
{
    /// Nothing: the closure's own environment, as forcing a thunk reads it.
    Nothing,
    /// A variable bound innermost, as opening a binder reads it.
    Variable(DomainValueId),
    /// Fresh variables, outermost first, for a native List cell branch or a
    /// split body.
    Variables(&'bound [DomainValueId]),
}

/// Drive the machine until its task stack empties or its slice runs out.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`SliceEnd::Drained`] when the task stack is empty, having spent
///   one unit of fuel per task popped; [`SliceEnd::Spent`] when the fuel ran
///   out first, with every unpopped task still on the stack.
/// - provides: the pausable loop under [`Evaluation::resume`], which differs
///   from [`run`] only in checking the budget before it pops.
/// - fails: every variant of [`EvalFault`] a step raises.
/// - panics: none.
///
/// # Errors
/// Every variant of [`EvalFault`] a step raises.
///
/// # Termination
/// - reason: the `loop` below, which pops one task per iteration, not
///   recursion; it audits only this slice, never the conversion driver that
///   resumes it.
/// - measure: the machine's fuel, which falls by one per iteration that pops.
/// - boundedness: the loop ends when the fuel is zero or the task stack is
///   empty, whichever is first.
/// - input recursion: none.
///
/// # Adequacy
/// - hypothesis: L3 — a zero slice leaves the initial task available, exact
///   exhaustion on the finishing task finishes rather than pauses, and one-step
///   slices agree with an uninterrupted run. Popping before the budget check or
///   checking exhaustion before completion changes these boundaries.
/// - witness: `eval::tests::a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause`
/// - witness: `eval::tests::a_sliced_evaluation_agrees_with_an_unsliced_one`
#[spec(
    captures: [entry_fuel = machine.fuel, entry_tasks = machine.tasks.len(), entry_domain = domain.watermark()],
    ensures: |ret| machine.fuel.0 <= entry_fuel.0 && ret != Err(EvalFault::OutOfFuel)
        && (entry_fuel.0 != 0_u32 || (machine.tasks.len() == entry_tasks && domain.watermark() == entry_domain))
        && match ret {
            Ok(SliceEnd::Drained) => machine.tasks.is_empty(),
            Ok(SliceEnd::Spent) => !machine.tasks.is_empty() && machine.fuel.0 == 0_u32,
            Err(_) => true,
        },
)]
fn run_slice(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<SliceEnd, EvalFault>
{
    loop {
        if machine.tasks.is_empty() {
            return Ok(SliceEnd::Drained);
        }
        let Some(remaining) = u32::from(machine.fuel).checked_sub(1_u32)
        else {
            return Ok(SliceEnd::Spent);
        };
        let Some(task) = machine.tasks.pop()
        else {
            return Ok(SliceEnd::Drained);
        };
        machine.fuel = Fuel(remaining);
        step(core, domain, machine, task)?;
    }
}

/// Drive the machine until its task stack empties or its fuel runs out.
///
/// # Specification
/// - requires: the machine's task stack holds the run's initial task.
/// - ensures: on success the task stack is empty and the result stacks hold
///   exactly what the run produced.
/// - provides: the one loop; every rule is an arm of it, so there is no call
///   cycle for the recursion gate to find. The clauses state a non-empty task
///   stack at entry and an empty one on success; that the stack held exactly
///   the run's initial task, and that the result stacks hold exactly what the
///   run produced, are statements about the run's history rather than about
///   either state the attribute observes.
/// - fails: every variant of [`EvalFault`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the fuel guard against the
///   task-stack guard, separated by a run that completes with fuel to spare and
///   a run that exhausts it, the second asserted by variant.
/// - witness: `eval::tests::a_loop_declines_on_fuel_rather_than_diverging`
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
#[spec(
    requires: !machine.tasks.is_empty(),
    captures: [entry_fuel = machine.fuel],
    ensures: |ret| machine.fuel.0 <= entry_fuel.0 && (ret.is_err() || machine.tasks.is_empty())
        && (ret != Err(EvalFault::OutOfFuel) || machine.fuel.0 == 0_u32),
)]
fn run(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), EvalFault>
{
    while let Some(task) = machine.tasks.pop() {
        let Some(remaining) = u32::from(machine.fuel).checked_sub(1_u32)
        else {
            #[cfg(feature = "tracing")]
            tracing::warn!("evaluation fuel exhausted");
            return Err(EvalFault::OutOfFuel);
        };
        machine.fuel = Fuel(remaining);
        step(core, domain, machine, task)?;
    }
    Ok(())
}

/// Perform one task.
///
/// # Specification
/// - requires: `task` belongs to this run. A malformed re-applied spine may
///   leave an operand absent, which is reported as
///   [`EvalFault::MachineInvariant`].
/// - ensures: the task's result is pushed on the stack of its own polarity, or
///   further tasks are pushed that will produce it. Fuel remains unchanged: the
///   driver, not a transition, charges the popped task.
/// - provides: the machine's whole transition relation, one arm per source
///   former plus one per assembly frame. Scalar lengths and copied operands
///   state the assembly transitions and preserve polarity; the delegated
///   eliminators state their own transitions. Only the driver charges fuel.
/// - fails: every variant of [`EvalFault`] except [`EvalFault::OutOfFuel`],
///   which belongs to the driver rather than to a step.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the source-former arms and the
///   frame arms, separated by one case per arm across the suite; the shape
///   faults are separated by an eliminator applied to the wrong polarity of
///   weak head.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
/// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
#[spec(
    captures: [entry_fuel = machine.fuel, entry_tasks = machine.tasks.len(),
        entry_values = machine.values.len(), entry_comps = machine.comps.len(),
        entry_value = machine.values.last().copied(),
        entry_first = machine.values.len().checked_sub(2_usize).and_then(|index| machine.values.get(index)).copied()],
    ensures: |ret| machine.fuel == entry_fuel && ret != Err(EvalFault::OutOfFuel)
        && (ret.is_err() || match task {
            Task::Constructor { .. } | Task::Record(_) => machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks && machine.values.last().is_some_and(|id| domain.value(*id).is_some()),
            Task::DataCase { .. } | Task::DataCaseClosure(_) | Task::Split { .. } | Task::SplitClosure(_) | Task::Projection(_) | Task::Force | Task::Apply | Task::StaticApply | Task::Bind { .. } | Task::Case { .. }
            | Task::BindClosure(_) | Task::CaseBranches(_) | Task::Transport | Task::ProductTransport(_) | Task::FixpointClosure(_) | Task::ListFold { .. }
            | Task::PathTransport(_) | Task::Ride(_) | Task::TelescopeTransport(_) => machine.tasks.len() >= entry_tasks,
            Task::Flow { .. } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() <= entry_values
                && matches!(machine.values.last().and_then(|value| domain.value(*value)), Some(DomainValue::Flow { .. })),
            Task::Here { .. } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() == entry_values
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::Here { point, .. }) if Some(*point) == entry_value),
            Task::Returned | Task::Running => entry_comps.checked_sub(1_usize) == Some(machine.comps.len())
                && ((machine.tasks.len() == entry_tasks && machine.values.len() == entry_values.saturating_add(1_usize))
                    || machine.tasks.len() > entry_tasks),
            Task::ReadThrough { .. } | Task::ReadContinued { .. } => (machine.comps.len() == entry_comps && machine.tasks.len() >= entry_tasks)
                || (entry_comps.checked_sub(1_usize) == Some(machine.comps.len())
                    && ((machine.tasks.len() == entry_tasks && machine.values.len() == entry_values.saturating_add(1_usize))
                        || machine.tasks.len() > entry_tasks)),
            Task::Reread => machine.values.len() == entry_values
                && ((machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks)
                    || (entry_comps.checked_sub(1_usize) == Some(machine.comps.len()) && machine.tasks.len() > entry_tasks)),
            Task::Value { .. } => machine.comps.len() == entry_comps
                && ((machine.values.len() == entry_values.saturating_add(1_usize) && machine.tasks.len() >= entry_tasks)
                    || (machine.values.len() == entry_values && machine.tasks.len() > entry_tasks)),
            Task::Body { body: crate::closure::CompBody::Source(_), .. } | Task::Comp { .. } => machine.values.len() == entry_values
                && ((machine.comps.len() == entry_comps.saturating_add(1_usize) && machine.tasks.len() >= entry_tasks)
                    || (machine.comps.len() == entry_comps && machine.tasks.len() > entry_tasks)),
            Task::Body { body: crate::closure::CompBody::Pair(first), env } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if matches!(domain.value(value).and_then(|held| domain.components(held)), Some(&[held, second])
                        if held == first && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(second)))),
            Task::Body { body: crate::closure::CompBody::TransportPair { path, value }, .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2) && machine.values.ends_with(&[path, value])
                && machine.tasks.len() == entry_tasks.saturating_add(2)
                && matches!(machine.tasks.get(entry_tasks..), Some([Task::BindClosure(_), Task::Transport])),
            Task::Body { body: crate::closure::CompBody::Returned, env } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(value))),
            Task::Body { body: crate::closure::CompBody::Then { then, .. }, .. } => machine.values.len() == entry_values
                && machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks.saturating_add(2)
                && matches!(machine.tasks.get(entry_tasks..), Some([Task::BindClosure(held), Task::Body { .. }]) if *held == then),
            Task::Body { body: crate::closure::CompBody::RideAlong { motive, flow }, env } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2)
                && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)).is_some_and(|bound| machine.values.ends_with(&[flow, bound])))
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::Ride(held)]) if held == motive),
            Task::Body { body: crate::closure::CompBody::RideFunction { .. }, .. } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Lambda { .. })),
            Task::Body { body: crate::closure::CompBody::RideArgument { motive, .. }, .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2)
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::BindClosure(_), Task::BindClosure(_), Task::Ride(held)]) if held == motive),
            Task::Body { body: crate::closure::CompBody::ForceApplied(function), .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(1)
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::Apply, Task::Force, Task::Supply(held)]) if held == function),
            Task::Body { body: crate::closure::CompBody::RidePair { motive, flow, value }, .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2) && machine.values.ends_with(&[flow, value])
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::BindClosure(_), Task::Ride(held)]) if held == motive),
            Task::Body { body: crate::closure::CompBody::Components { mover, .. }, .. } => (machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. }) if domain.value(value).and_then(|held| domain.components(held)).is_some()))
                || (machine.comps.len() == entry_comps && machine.values.len() == entry_values.saturating_add(2)
                    && matches!((mover, machine.tasks.get(entry_tasks..)), (crate::closure::Mover::Ride, Some(&[Task::BindClosure(_), Task::Ride(_)])) | (crate::closure::Mover::Transport, Some(&[Task::BindClosure(_), Task::PathTransport(_)])))),
            Task::Body { body: crate::closure::CompBody::Inject(summand), env } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if matches!(domain.value(value), Some(&DomainValue::Injection { summand: held, body, .. })
                        if held == summand && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(body)))),
            Task::Body { body: crate::closure::CompBody::MoveTail { mover, motive, along, tail }, .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2) && machine.values.ends_with(&[along, tail])
                && matches!((mover, machine.tasks.get(entry_tasks..)), (crate::closure::Mover::Ride, Some(&[Task::BindClosure(_), Task::Ride(held)])) | (crate::closure::Mover::Transport, Some(&[Task::BindClosure(_), Task::PathTransport(held)])) if held == motive),
            Task::Body { body: crate::closure::CompBody::Cons(head), env } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if matches!(domain.value(value), Some(&DomainValue::ListCons { first, second, .. })
                        if first == head && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(second)))),
            Task::Body { body: crate::closure::CompBody::AlongWord { motive, rest }, env } => machine.comps.len() == entry_comps
                && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)).is_some_and(|bound| machine.values.ends_with(&[rest, bound])))
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::PathTransport(held)]) if held == motive),
            Task::Body { body: crate::closure::CompBody::Prefixed(word), .. } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if matches!((domain.value(value), domain.value(word)), (Some(&DomainValue::Constructor { tag, .. }), Some(&DomainValue::Constructor { tag: first, .. })) if tag == first)),
            Task::Body { body: crate::closure::CompBody::Appending { motive, path, .. }, env } => machine.values.len() == entry_values.saturating_add(2)
                && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)).is_some_and(|bound| machine.values.ends_with(&[path, bound])))
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::PathTransport(held)]) if held == motive)
                || machine.values.len() == entry_values && machine.tasks.len() == entry_tasks
                    && machine.comps.len() == entry_comps.saturating_add(1),
            Task::Body { body: crate::closure::CompBody::Conjugated { .. } | crate::closure::CompBody::Mapping(_) | crate::closure::CompBody::Selecting(_), .. } => machine.values.len() == entry_values
                && (machine.comps.len() == entry_comps.saturating_add(1) || machine.tasks.len() > entry_tasks),
            Task::PathProduct(_) => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && entry_values.checked_sub(1) == Some(machine.values.len())
                && matches!(machine.values.last().and_then(|&id| domain.value(id)), Some(&DomainValue::PathProduct { first, second, .. })
                    if Some(first) == entry_first && Some(second) == entry_value),
            Task::ListCons(_) => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && entry_values.checked_sub(1_usize) == Some(machine.values.len())
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::ListCons { first, second, .. }) if Some(*first) == entry_first && Some(*second) == entry_value),
            Task::Tuple { term } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && core.value(term).and_then(Value::components).is_some_and(|source| entry_values.checked_sub(source.len()).and_then(|left| left.checked_add(1_usize)) == Some(machine.values.len())
                    && machine.values.last().and_then(|value| domain.value(*value)).and_then(|value| domain.components(value)).is_some_and(|held| held.len() == source.len())),
            Task::Inject { term } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() == entry_values
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::Injection { summand, body, .. }) if Some(*body) == entry_value
                        && matches!(core.value(term), Some(Value::Injection(source_summand, _)) if source_summand == summand)),
            Task::Lift { target, .. } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() == entry_values
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::Lift { target: held, body, .. }) if *held == target && Some(*body) == entry_value),
            Task::Return { .. } => machine.tasks.len() == entry_tasks
                && entry_values.checked_sub(1_usize) == Some(machine.values.len())
                && machine.comps.len() == entry_comps.saturating_add(1_usize)
                && matches!(machine.comps.last().and_then(|comp| domain.computation(*comp)),
                    Some(DomainComp::Return { value, .. }) if Some(*value) == entry_value),
            Task::Supply(value) => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(1_usize) && machine.values.last() == Some(&value),
            Task::Remember(pending) => machine.tasks.len() == entry_tasks && machine.values.len() == entry_values
                && machine.comps.len() == entry_comps && machine.sharing.pending.get(pending.0).is_none_or(Option::is_none),
            Task::Arm(entry) => machine.comps.len() == entry_comps
                && entry_values.checked_sub(entry.count.saturating_sub(1_usize)) == Some(machine.values.len())
                && matches!(machine.tasks.get(entry_tasks..), Some(&[Task::Comp { term, .. }]) if term == entry.arm),
            Task::Yield => machine.tasks.len() == entry_tasks
                && entry_values.checked_sub(1_usize) == Some(machine.values.len())
                && machine.comps.len() == entry_comps.saturating_add(1_usize)
                && matches!(machine.comps.last().and_then(|comp| domain.computation(*comp)),
                    Some(DomainComp::Return { value, .. }) if Some(*value) == entry_value),
            }),
)]
fn step(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    task: Task,
) -> Result<(), EvalFault>
{
    match task {
        Task::Constructor { term, env } => step_constructor(core, domain, machine, term, env),
        Task::Record(term) => step_record(core, domain, machine, term),
        Task::DataCase { term, env } => step_data_case(core, domain, machine, term, env),
        Task::Projection(term) => step_projection(core, domain, machine, term),
        Task::DataCaseClosure(closure) => {
            let closure = domain
                .comp_closure(closure)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            let crate::closure::CompBody::Source(term) = closure.body()
            else {
                return Err(EvalFault::MachineInvariant);
            };
            let env = machine.hold_env(closure.environment().clone());
            step_data_case(core, domain, machine, term, env)
        },
        Task::Split { term, env } => step_split(core, domain, machine, term, env),
        Task::SplitClosure(closure) => {
            let closure = domain
                .comp_closure(closure)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            let crate::closure::CompBody::Source(term) = closure.body()
            else {
                return Err(EvalFault::MachineInvariant);
            };
            let env = machine.hold_env(closure.environment().clone());
            step_split(core, domain, machine, term, env)
        },
        Task::Value { term, env } => {
            let recalled = machine.recall(CoreTerm::Value(term), env)?;
            match recalled {
                Recall::Remembered(Glued::Value(remembered)) => {
                    machine.values.push(remembered);
                    Ok(())
                },
                Recall::Remembered(Glued::Computation(_)) => Err(EvalFault::MachineInvariant),
                Recall::Unshared | Recall::Pending => step_value(core, domain, machine, term, env),
            }
        },
        Task::Body {
            body: crate::closure::CompBody::Source(term),
            env,
        }
        | Task::Comp { term, env } => {
            let recalled = machine.recall(CoreTerm::Computation(term), env)?;
            match recalled {
                Recall::Remembered(Glued::Computation(remembered)) => {
                    machine.comps.push(remembered);
                    Ok(())
                },
                Recall::Remembered(Glued::Value(_)) => Err(EvalFault::MachineInvariant),
                Recall::Unshared | Recall::Pending => step_comp(core, domain, machine, term, env),
            }
        },
        // The thunk a function flow rides a function to, forced: the lambda
        // that rides its argument, applies the function and rides the result.
        Task::Body {
            body:
                crate::closure::CompBody::RideFunction {
                    motive,
                    flow,
                    function,
                },
            ..
        } => {
            let applied = domain.native_continuation(crate::closure::CompBody::RideArgument {
                motive,
                flow,
                function,
            });
            machine
                .comps
                .push(domain.comp_lambda(applied, CompTermFace::Reduced));
            Ok(())
        },
        Task::Body { body, env } => {
            let bound = machine
                .env(env)?
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
                .ok_or(EvalFault::MachineInvariant)?;
            match body {
                crate::closure::CompBody::Source(_)
                | crate::closure::CompBody::RideFunction { .. } => Err(EvalFault::MachineInvariant),
                crate::closure::CompBody::Pair(first) => {
                    let pair = domain.value_tuple([first, bound], TermFace::Reduced);
                    machine
                        .comps
                        .push(domain.comp_return(pair, CompTermFace::Reduced));
                    Ok(())
                },
                crate::closure::CompBody::TransportPair { path, value } => {
                    let continuation =
                        domain.native_continuation(crate::closure::CompBody::Pair(bound));
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::Transport);
                    machine.values.extend([path, value]);
                    Ok(())
                },
                crate::closure::CompBody::Returned => {
                    machine
                        .comps
                        .push(domain.comp_return(bound, CompTermFace::Reduced));
                    Ok(())
                },
                // `x. (N to y. P)`: the inner continuation runs at the bound
                // value under its own environment, and its result binds into
                // the outer one as it stands.
                crate::closure::CompBody::Then { first, then } => {
                    let held = domain
                        .comp_closure(first)
                        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
                    let body = held.body();
                    let mut environment = held.environment().clone();
                    environment.extend(Zone::Intuitionistic, bound);
                    let env = machine.hold_env(environment);
                    machine.tasks.push(Task::BindClosure(then));
                    machine.tasks.push(Task::Body { body, env });
                    Ok(())
                },
                // After the first leg of a composite rode, ride its result
                // along the second leg in the same motive.
                crate::closure::CompBody::RideAlong { motive, flow } => {
                    machine.tasks.push(Task::Ride(motive));
                    machine.values.extend([flow, bound]);
                    Ok(())
                },
                // `a'. a ← ride(El, d, a'); b ← force f a; ride(El, c, b)`:
                // the argument rides the domain flow, the function applies,
                // and the result rides the codomain flow.
                crate::closure::CompBody::RideArgument {
                    motive,
                    flow,
                    function,
                } => {
                    let Some(&DomainValue::Flow {
                        former: crate::domain::FlowFormer::Function,
                        parts,
                        ..
                    }) = domain.value(flow)
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    let &[argument, result] = domain.fields(parts).map_err(EvalFault::Domain)?
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    let onward = domain.native_continuation(crate::closure::CompBody::RideAlong {
                        motive,
                        flow: result,
                    });
                    let applied = domain
                        .native_continuation(crate::closure::CompBody::ForceApplied(function));
                    machine.tasks.push(Task::BindClosure(onward));
                    machine.tasks.push(Task::BindClosure(applied));
                    machine.tasks.push(Task::Ride(motive));
                    machine.values.extend([argument, bound]);
                    Ok(())
                },
                crate::closure::CompBody::ForceApplied(function) => {
                    machine.values.push(bound);
                    machine.tasks.push(Task::Apply);
                    machine.tasks.push(Task::Force);
                    machine.tasks.push(Task::Supply(function));
                    Ok(())
                },
                // `x. y ← ride(P, g, b); return (x, y)`: the right component
                // rides only once the left one returned.
                crate::closure::CompBody::RidePair {
                    motive,
                    flow,
                    value,
                } => {
                    let continuation =
                        domain.native_continuation(crate::closure::CompBody::Pair(bound));
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::Ride(motive));
                    machine.values.extend([flow, value]);
                    Ok(())
                },
                crate::closure::CompBody::Components {
                    mover,
                    motive,
                    along,
                    source,
                    moved,
                } => {
                    let environment = machine.env(env)?.clone();
                    move_components(
                        core,
                        domain,
                        machine,
                        Componentwise {
                            mover,
                            motive,
                            along,
                            source,
                        },
                        (environment, moved),
                    )
                },
                crate::closure::CompBody::Inject(summand) => {
                    let injected = domain.value_injection(summand, bound, TermFace::Reduced);
                    machine
                        .comps
                        .push(domain.comp_return(injected, CompTermFace::Reduced));
                    Ok(())
                },
                // `h. t ← step(List E, p, tail); return cons(h, t)`: the tail
                // moves only once the head returned.
                crate::closure::CompBody::MoveTail {
                    mover,
                    motive,
                    along,
                    tail,
                } => {
                    let continuation =
                        domain.native_continuation(crate::closure::CompBody::Cons(bound));
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(moving(mover, motive));
                    machine.values.extend([along, tail]);
                    Ok(())
                },
                crate::closure::CompBody::Cons(head) => {
                    let cell = domain.value_list_cons(head, bound, TermFace::Reduced);
                    machine
                        .comps
                        .push(domain.comp_return(cell, CompTermFace::Reduced));
                    Ok(())
                },
                // `y. tr(P, u, y)`: the rest of the word moves the value the
                // first letter moved.
                crate::closure::CompBody::AlongWord { motive, rest } => {
                    machine.tasks.push(Task::PathTransport(motive));
                    machine.values.extend([rest, bound]);
                    Ok(())
                },
                // `v. tr(P, q, v)`: the held operand's run moves along the
                // path, unless it returned a held endpoint again.
                crate::closure::CompBody::Appending {
                    motive,
                    path,
                    operand,
                } => words::ran(domain, machine, (motive, path, operand), bound),
                // `w. return ℓ ∷ w`: the word's first letter goes back before
                // the rest's transport.
                crate::closure::CompBody::Prefixed(word) => {
                    let Some(&DomainValue::Constructor { tag, .. }) = domain.value(word)
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    let prefixed = words::relettered(domain, word, tag, bound)?;
                    machine
                        .comps
                        .push(domain.comp_return(prefixed, CompTermFace::Reduced));
                    Ok(())
                },
                crate::closure::CompBody::Conjugated {
                    motive,
                    along,
                    value,
                    stage,
                } => words::conjugated(
                    core,
                    domain,
                    machine,
                    (motive, along, value),
                    (stage, bound),
                ),
                crate::closure::CompBody::Mapping(state) => {
                    words::mapped(core, domain, machine, state, bound)
                },
                crate::closure::CompBody::Selecting(state) => {
                    words::selected(core, domain, machine, state, bound)
                },
            }
        },
        Task::PathProduct(term) => {
            let second = machine.pop_value()?;
            let first = machine.pop_value()?;
            let Some(&Value::PathProduct(left, right)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(
                denotes(domain, first, left).and(denotes(domain, second, right)),
                term,
            );
            machine
                .values
                .push(domain.value_path_product(first, second, face));
            Ok(())
        },
        Task::Transport => step_transport(core, domain, machine),
        Task::ProductTransport(path) => {
            let value = machine.pop_value()?;
            machine.values.extend([path, value]);
            step_transport(core, domain, machine)
        },
        Task::PathTransport(motive) => step_path_transport(core, domain, machine, motive),
        Task::Ride(motive) => step_ride(core, domain, machine, motive),
        Task::Flow { term } => {
            let flow = match core.value(term) {
                Some(&(Value::Stay(part) | Value::Forward(part))) => {
                    let former = if matches!(core.value(term), Some(Value::Stay(_))) {
                        crate::domain::FlowFormer::Stay
                    }
                    else {
                        crate::domain::FlowFormer::Forward
                    };
                    let evaluated = machine.pop_value()?;
                    let face = composite_face(denotes(domain, evaluated, part), term);
                    domain.value_flow(former, [evaluated], face)
                },
                Some(
                    &(Value::Then(left, right)
                    | Value::FunctionFlow(left, right)
                    | Value::FlowProduct(left, right)),
                ) => {
                    let former = match core.value(term) {
                        Some(&Value::Then(..)) => crate::domain::FlowFormer::Then,
                        Some(&Value::FlowProduct(..)) => crate::domain::FlowFormer::Product,
                        _ => crate::domain::FlowFormer::Function,
                    };
                    let second = machine.pop_value()?;
                    let first = machine.pop_value()?;
                    let face = composite_face(
                        denotes(domain, first, left).and(denotes(domain, second, right)),
                        term,
                    );
                    domain.value_flow(former, [first, second], face)
                },
                _ => return Err(EvalFault::DanglingTerm),
            };
            machine.values.push(flow);
            Ok(())
        },
        Task::TelescopeTransport(motive) => step_telescope_transport(core, domain, machine, motive),
        Task::Here { term } => {
            let point = machine.pop_value()?;
            let Some(&Value::Here(source)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(denotes(domain, point, source), term);
            machine.values.push(domain.value_here(point, face));
            Ok(())
        },
        Task::Returned => {
            let produced = machine.pop_comp()?;
            let stance = machine.definitions.endpoints();
            resume_returned(domain, machine, (produced, stance))
        },
        Task::Running => {
            let produced = machine.pop_comp()?;
            resume_returned(domain, machine, (produced, Endpoints::Run))
        },
        Task::ListCons(term) => {
            let second = machine.pop_value()?;
            let first = machine.pop_value()?;
            let Some(&Value::ListCons(left, right)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(
                denotes(domain, first, left).and(denotes(domain, second, right)),
                term,
            );
            machine
                .values
                .push(domain.value_list_cons(first, second, face));
            Ok(())
        },
        Task::ListFold {
            element,
            result,
            on_nil,
            on_cons,
        } => {
            let list = machine.pop_value()?;
            let node = *domain
                .value(list)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            match node {
                DomainValue::ListNil { .. } => {
                    let closure = domain
                        .comp_closure(on_nil)
                        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
                    let body = closure.body();
                    let env = machine.hold_env(closure.environment().clone());
                    machine.tasks.push(Task::Body { body, env });
                },
                DomainValue::ListCons { first, second, .. } => {
                    let closure = domain
                        .comp_closure(on_cons)
                        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
                    let crate::closure::CompBody::Source(body) = closure.body()
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    let mut captured = closure.environment().clone();
                    captured.extend(Zone::Intuitionistic, first);
                    let continuation = domain.comp_closure_node(body, captured);
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::ListFold {
                        element,
                        result,
                        on_nil,
                        on_cons,
                    });
                    machine.values.push(second);
                },
                DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(domain, neutral, Elimination::ListFold {
                        element,
                        result,
                        on_nil,
                        on_cons,
                    })?;
                    machine
                        .comps
                        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
                },
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. } => return Err(EvalFault::FoldedNonList),
            }
            Ok(())
        },
        Task::Tuple { term } => {
            let Some(source) = core.value(term).and_then(Value::components)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let start = machine
                .values
                .len()
                .checked_sub(source.len())
                .ok_or(EvalFault::MachineInvariant)?;
            let evaluated = machine.values.get(start ..).unwrap_or_default();
            let kept = evaluated
                .iter()
                .zip(source)
                .fold(SourceKept::Kept, |kept, (&value, &component)| {
                    kept.and(denotes(domain, value, component))
                });
            let face = composite_face(kept, term);
            let tuple = domain.value_tuple(evaluated.iter().copied(), face);
            machine.values.truncate(start);
            machine.values.push(tuple);
            Ok(())
        },
        Task::Inject { term } => {
            let body = machine.pop_value()?;
            let Some(&Value::Injection(summand, source)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(denotes(domain, body, source), term);
            machine
                .values
                .push(domain.value_injection(summand, body, face));
            Ok(())
        },
        Task::Lift { term, target } => {
            let body = machine.pop_value()?;
            let Some(&Value::Lift { body: source, .. }) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(denotes(domain, body, source), term);
            machine.values.push(domain.value_lift(target, body, face));
            Ok(())
        },
        Task::Return { term } => {
            let produced = machine.pop_value()?;
            let Some(&(Computation::Return(source) | Computation::Ride { value: source, .. })) =
                core.computation(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_comp_face(denotes(domain, produced, source), term);
            machine.comps.push(domain.comp_return(produced, face));
            Ok(())
        },
        Task::Force => step_force(domain, machine),
        Task::Apply => step_apply(core, domain, machine),
        Task::StaticApply => step_static_apply(core, domain, machine),
        Task::Bind { body, env } => step_bind(core, domain, machine, body, env),
        Task::Case { term, env } => step_case(core, domain, machine, term, env),
        Task::Supply(value) => {
            machine.values.push(value);
            Ok(())
        },
        Task::BindClosure(body) => step_bind_closure(core, domain, machine, body),
        Task::CaseBranches(branches) => step_case_branches(domain, machine, branches),
        Task::Remember(pending) => machine.remember(pending),
        Task::FixpointClosure(recursive) => {
            machine
                .comps
                .push(domain.comp_fixpoint(recursive, CompTermFace::Reduced));
            step_apply(core, domain, machine)
        },
        Task::ReadThrough {
            computation,
            bind,
            delivery,
        } => {
            let continued = machine.pop_comp()?;
            if matches!(
                domain.computation(continued),
                Some(&DomainComp::Return { .. })
            ) {
                return continue_past(domain, machine, computation, bind, delivery, continued);
            }
            // A continuation stuck at a bind of its own is read before it is
            // judged; one stuck otherwise comes back whole.
            machine.tasks.push(Task::ReadContinued {
                computation,
                bind,
                delivery,
            });
            read_from(
                domain,
                machine,
                continued,
                SpinePosition::INNERMOST,
                Delivery::Continuation,
            )
        },
        Task::ReadContinued {
            computation,
            bind,
            delivery,
        } => {
            let read = machine.pop_comp()?;
            if matches!(domain.computation(read), Some(&DomainComp::Return { .. })) {
                return continue_past(domain, machine, computation, bind, delivery, read);
            }
            read_from(domain, machine, computation, bind.outward(), delivery)
        },
        Task::Arm(entry) => words::arm_entered(machine, entry),
        Task::Yield => {
            let produced = machine.pop_value()?;
            machine
                .comps
                .push(domain.comp_return(produced, CompTermFace::Reduced));
            Ok(())
        },
        Task::Reread => {
            let produced = machine.pop_comp()?;
            read_from(
                domain,
                machine,
                produced,
                SpinePosition::INNERMOST,
                Delivery::Continuation,
            )
        },
    }
}

/// Perform one value task: evaluate a core value node.
///
/// # Specification
/// - requires: `env` names an environment this machine holds.
/// - ensures: a leaf pushes its result directly; a composite pushes its
///   children's tasks and its own assembly frame, so the frame runs after them.
/// - provides: the value half of the transition relation. The clause states the
///   two admissible stack movements — one value result and no new task, or new
///   tasks and no value result; which node or task each arm pushed is a
///   judgement over the produced graph, and the witnesses below carry it.
/// - fails: [`EvalFault::DanglingTerm`] for an unresolvable node,
///   [`EvalFault::UnboundVariable`] for an index past its zone's bindings.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the value-former match plus the
///   variable and constant lookups, separated by one case per arm — the leaf
///   arms and the lift arm included, the last being the only one that holds a
///   level and so the only producer of the level family — an index past the
///   environment, a constant at each unfolding stance, a quote over the empty
///   environment and over a captured one, and a static lambda applied and left
///   standing.
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
/// - witness: `eval::tests::the_leaf_and_lift_arms_evaluate_and_keep_their_faces`
/// - witness: `eval::tests::a_lift_over_a_substituted_body_loses_its_face`
/// - witness: `eval::tests::a_variable_resolves_out_of_the_environment`
/// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
/// - witness: `eval::tests::native_records_and_cases_compute`
/// - witness: `eval::tests::normalizes_beta_redex`
/// - witness: `eval::tests::normalization_preserves_a_stuck_application`
#[spec(
    requires: env.0 < machine.envs.len(),
    captures: [
        entry_values = machine.values.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.values.len() == entry_values.saturating_add(1_usize)
            && machine.tasks.len() == entry_tasks)
        || (machine.values.len() == entry_values && machine.tasks.len() > entry_tasks),
)]
fn step_value(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ValueId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(node) = core.value(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    match *node {
        Value::Constructor { ref fields, .. } => {
            machine.tasks.push(Task::Constructor { term, env });
            machine.tasks.extend(
                fields
                    .iter()
                    .rev()
                    .map(|field| Task::Value { term: *field, env }),
            );
            Ok(())
        },
        Value::Record(ref fields) => {
            machine.tasks.push(Task::Record(term));
            machine.tasks.extend(
                fields
                    .values()
                    .rev()
                    .map(|field| Task::Value { term: *field, env }),
            );
            Ok(())
        },
        Value::Reify(_) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Reify,
        )),
        Value::ListNil => {
            machine
                .values
                .push(domain.value_list_nil(TermFace::Source(term)));
            Ok(())
        },
        Value::ListCons(first, second) => {
            machine.tasks.push(Task::ListCons(term));
            machine.tasks.push(Task::Value { term: second, env });
            machine.tasks.push(Task::Value { term: first, env });
            Ok(())
        },
        // A closed native path, a closed funext, a closed equivalence, a
        // univalence statement, a session statement and a recorded run are
        // inert certificates: nothing reduces them, and transport reads their
        // syntax.
        Value::PathRefl(_)
        | Value::PathEquiv { .. }
        | Value::Funext(..)
        | Value::Equiv(..)
        | Value::Ua { .. }
        | Value::SessionRelated { .. }
        | Value::Recorded(_) => {
            machine
                .values
                .push(domain.value_path_certificate(term, TermFace::Source(term)));
            Ok(())
        },
        // A flow introduction evaluates its parts where it stands, so a ride
        // reads a composite's or a function flow's parts in the environment
        // they were written in.
        Value::Stay(part) | Value::Forward(part) => {
            machine.tasks.push(Task::Flow { term });
            machine.tasks.push(Task::Value { term: part, env });
            Ok(())
        },
        Value::Then(first, second)
        | Value::FunctionFlow(first, second)
        | Value::FlowProduct(first, second) => {
            machine.tasks.push(Task::Flow { term });
            machine.tasks.push(Task::Value { term: second, env });
            machine.tasks.push(Task::Value { term: first, env });
            Ok(())
        },
        Value::Here(point) => {
            machine.tasks.push(Task::Here { term });
            machine.tasks.push(Task::Value { term: point, env });
            Ok(())
        },
        // A compound endpoint runs its computation and stands for what it
        // returns, or for the stuck computation when it does not return. A
        // nested computation and a written run evaluate the same way: only the
        // checker meets them, before elaboration, and it reads one standing in
        // a dependent position by what it returns.
        Value::Returned(computation) | Value::Nested(computation) | Value::Run(computation) => {
            machine.tasks.push(Task::Returned);
            machine.tasks.push(Task::Comp {
                term: computation,
                env,
            });
            Ok(())
        },
        Value::PathProduct(first, second) => {
            machine.tasks.push(Task::PathProduct(term));
            machine.tasks.push(Task::Value { term: second, env });
            machine.tasks.push(Task::Value { term: first, env });
            Ok(())
        },
        Value::Variable { zone, index } => {
            let environment = machine.env(env)?;
            let bound = environment
                .lookup(zone, index)
                .ok_or(EvalFault::UnboundVariable { zone, index })?;
            machine.values.push(bound);
            Ok(())
        },
        Value::Constant(constant) => {
            let unfolding = machine.definitions.unfolding(constant);
            let neutral = domain
                .neutral_node(NeutralHead::Constant(constant), Vec::new(), unfolding)
                .map_err(EvalFault::Domain)?;
            let stood = domain
                .value_neutral(neutral, TermFace::Source(term))
                .map_err(EvalFault::Domain)?;
            machine.values.push(stood);
            Ok(())
        },
        Value::Literal(ref payload) => {
            machine
                .values
                .push(domain.value_literal(term, payload, TermFace::Source(term)));
            Ok(())
        },
        // The empty tuple is the unit, a leaf: it has no assembly to defer.
        Value::Tuple(ref components) if components.is_empty() => {
            machine
                .values
                .push(domain.value_unit(TermFace::Source(term)));
            Ok(())
        },
        Value::Tuple(ref components) => {
            machine.tasks.push(Task::Tuple { term });
            for &component in components.iter().rev() {
                machine.tasks.push(Task::Value {
                    term: component,
                    env,
                });
            }
            Ok(())
        },
        Value::Injection(_, body) => {
            machine.tasks.push(Task::Inject { term });
            machine.tasks.push(Task::Value { term: body, env });
            Ok(())
        },
        Value::Thunk(body) | Value::Primitive { body, .. } => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.comp_closure_node(body, captured);
            let face = composite_face(closed, term);
            machine.values.push(domain.value_thunk(closure, face));
            Ok(())
        },
        Value::Lift { ref target, body } => {
            let target = domain.hold_level(target.clone());
            machine.tasks.push(Task::Lift { term, target });
            machine.tasks.push(Task::Value { term: body, env });
            Ok(())
        },
        // A quote is suspended whole over the environment its type reads: a
        // type has no weak head, so the codes inside it are evaluated where a
        // readback or a comparison reaches them.
        Value::Quote(_) | Value::QuoteComputation(_) => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.value_closure_node(crate::ValueBody::Source(term), captured);
            let face = composite_face(closed, term);
            machine.values.push(domain.value_code(closure, face));
            Ok(())
        },
        // A static lambda is suspended whole, as a quote is: the closure's
        // body is the lambda itself, which a comparison reads whole and a
        // static application enters.
        Value::StaticLambda(_) => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.value_closure_node(crate::ValueBody::Source(term), captured);
            let face = composite_face(closed, term);
            machine
                .values
                .push(domain.value_static_lambda(closure, face));
            Ok(())
        },
        Value::StaticApplication(head, argument) => {
            machine.tasks.push(Task::StaticApply);
            machine.tasks.push(Task::Value {
                term: argument,
                env,
            });
            machine.tasks.push(Task::Value { term: head, env });
            Ok(())
        },
        // A hole or a mark stops evaluation: it stands as a neutral head,
        // suspended whole over the environment it was met in, which is what a
        // fill reads its filling in and what a mark's body is read back
        // through.
        Value::Hole(hole) => {
            let (closure, face) = suspend_value(domain, machine, term, env)?;
            let head = NeutralHead::Hole { hole, closure };
            stand_value(domain, machine, head, face)
        },
        Value::Mark { mark, .. } => {
            let (closure, face) = suspend_value(domain, machine, term, env)?;
            let head = NeutralHead::Mark { mark, closure };
            stand_value(domain, machine, head, face)
        },
    }
}

/// Close the hole or mark `term` over the environment `env` names.
///
/// # Specification
/// - requires: `env` names an environment this machine holds.
/// - ensures: a fresh value closure over `term` and that environment, and the
///   face the neutral standing on it carries: `term`'s own when the environment
///   is empty, reduced otherwise.
/// - provides: the suspension a hole or a mark in value position stands on.
/// - fails: [`EvalFault::MachineInvariant`] when `env` names no environment.
/// - panics: none.
///
/// # Errors
/// - [`EvalFault::MachineInvariant`] — `env` names no environment.
///
/// # Adequacy
/// - hypothesis: L3 — a hole met under no binder and under one separate the
///   kept face from the reduced one, and the closure's environment from an
///   empty one.
/// - witness: `live::tests::a_hole_evaluates_to_a_neutral_carrying_its_environment`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(closure, _)| matches!(closure, Suspended::Value(id) if domain.value_closure(id).is_some())))]
fn suspend_value(
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    term: ValueId,
    env: EnvId,
) -> Result<(Suspended, TermFace), EvalFault>
{
    let captured = machine.capture(env)?;
    let closed = capture_keeps_source(&captured);
    let closure = domain.value_closure_node(crate::ValueBody::Source(term), captured);
    Ok((Suspended::Value(closure), composite_face(closed, term)))
}

/// Stand a fresh neutral over `head`, with no elimination, in value position.
///
/// # Specification
/// - requires: `head` cannot unfold.
/// - ensures: one value pushed: a neutral over `head`, an empty spine and a
///   rigid unfolding face, carrying `face`.
/// - provides: the value a hole or a mark evaluates to.
/// - fails: [`EvalFault::Domain`] carrying the arena's refusal.
/// - panics: none.
///
/// # Errors
/// - [`EvalFault::Domain`] — the arena refused the neutral.
///
/// # Adequacy
/// - hypothesis: L3 — as [`suspend_value`].
/// - witness: `live::tests::a_hole_evaluates_to_a_neutral_carrying_its_environment`
#[spec(captures: entry = machine.values.len(), ensures: |ret| ret.is_err() || machine.values.len() == entry.saturating_add(1_usize))]
fn stand_value(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    head: NeutralHead,
    face: TermFace,
) -> Result<(), EvalFault>
{
    let neutral = domain
        .neutral_node(head, Vec::new(), Unfolding::Rigid)
        .map_err(EvalFault::Domain)?;
    let stood = domain
        .value_neutral(neutral, face)
        .map_err(EvalFault::Domain)?;
    machine.values.push(stood);
    Ok(())
}

/// Perform one computation task: evaluate a core computation node one layer
/// toward weak head.
///
/// # Specification
/// - requires: `env` names an environment this machine holds.
/// - ensures: an introduction pushes its weak head directly; an eliminator
///   pushes its operands' tasks and its own frame.
/// - provides: the computation half of the transition relation. The clause
///   states the two admissible stack movements — one computation result and no
///   new task, or new tasks and no computation result; which node or task each
///   arm pushed is a judgement over the produced graph, and the witnesses below
///   carry it.
/// - fails: [`EvalFault::DanglingTerm`] for an unresolvable node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the six-arm match, separated by
///   one case per arm, with the lambda's closed-environment face separated from
///   its captured-environment face.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::a_closed_lambda_keeps_its_source_face`
#[spec(
    requires: env.0 < machine.envs.len(),
    captures: [
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == entry_comps.saturating_add(1_usize)
            && machine.tasks.len() == entry_tasks)
        || (machine.comps.len() == entry_comps && machine.tasks.len() > entry_tasks),
)]
fn step_comp(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(node) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    match *node {
        Computation::Perform { .. } => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Perform,
        )),
        Computation::Handle { .. } => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Handle,
        )),
        Computation::Resume(..) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Resume,
        )),
        Computation::Reset(_) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Reset,
        )),
        Computation::Shift(_) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Shift,
        )),
        Computation::With(..) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::With,
        )),
        Computation::Project(..) => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Project,
        )),
        Computation::Session(_) => Err(EvalFault::SessionAction),
        Computation::Memory(_) => Err(EvalFault::MemoryForm),
        Computation::Exercise { .. } => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Exercise,
        )),
        Computation::Scope { .. } => Err(EvalFault::RuntimeControl(
            gandr_core_term::control::ControlFormer::Scope,
        )),
        Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } => {
            let captured = machine.capture(env)?;
            let on_nil = domain.comp_closure_node(on_nil, captured.clone());
            let on_cons = domain.comp_closure_node(on_cons, captured);
            machine.tasks.push(Task::ListFold {
                element,
                result,
                on_nil,
                on_cons,
            });
            machine.tasks.push(Task::Value { term: list, env });
            Ok(())
        },
        Computation::Primitive { primitive, .. } => Err(EvalFault::NativePrimitive(primitive)),
        Computation::Split { scrutinee, .. } => {
            machine.tasks.push(Task::Split { term, env });
            machine.tasks.push(Task::Value {
                term: scrutinee,
                env,
            });
            Ok(())
        },
        Computation::DataCase { scrutinee, .. } => {
            machine.tasks.push(Task::DataCase { term, env });
            machine.tasks.push(Task::Value {
                term: scrutinee,
                env,
            });
            Ok(())
        },
        Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => {
            machine.tasks.push(Task::Projection(term));
            machine.tasks.push(Task::Value { term: record, env });
            Ok(())
        },
        Computation::Transport(path, value) => {
            machine.tasks.push(Task::Transport);
            machine.tasks.push(Task::Value { term: value, env });
            machine.tasks.push(Task::Value { term: path, env });
            Ok(())
        },
        Computation::PathTransport {
            motive,
            path,
            value,
        } => {
            let captured = machine.capture(env)?;
            let motive = domain.value_closure_node(crate::ValueBody::ValueType(motive), captured);
            machine.tasks.push(Task::PathTransport(motive));
            machine.tasks.push(Task::Value { term: value, env });
            machine.tasks.push(Task::Value { term: path, env });
            Ok(())
        },
        Computation::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        } => {
            let captured = machine.capture(env)?;
            let motive = domain.value_closure_node(crate::ValueBody::CompType(motive), captured);
            machine.tasks.push(Task::TelescopeTransport(motive));
            for term in [value, over, start, path] {
                machine.tasks.push(Task::Value { term, env });
            }
            Ok(())
        },
        Computation::Lambda(body) => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.comp_closure_node(body, captured);
            let face = composite_comp_face(closed, term);
            machine.comps.push(domain.comp_lambda(closure, face));
            Ok(())
        },
        // A fixpoint is inert until a gate observes it: it closes over its
        // own source node, which is what the self thunk suspends.
        Computation::Fixpoint { .. } => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.comp_closure_node(term, captured);
            let face = composite_comp_face(closed, term);
            machine.comps.push(domain.comp_fixpoint(closure, face));
            Ok(())
        },
        Computation::Ride {
            motive,
            flow,
            value,
        } => {
            let captured = machine.capture(env)?;
            let motive = domain.value_closure_node(crate::ValueBody::ValueType(motive), captured);
            machine.tasks.push(Task::Ride(motive));
            machine.tasks.push(Task::Value { term: value, env });
            machine.tasks.push(Task::Value { term: flow, env });
            Ok(())
        },
        Computation::Return(value) => {
            machine.tasks.push(Task::Return { term });
            machine.tasks.push(Task::Value { term: value, env });
            Ok(())
        },
        Computation::Application(head, argument) => {
            machine.tasks.push(Task::Apply);
            machine.tasks.push(Task::Comp { term: head, env });
            machine.tasks.push(Task::Value {
                term: argument,
                env,
            });
            Ok(())
        },
        Computation::Force(value) => {
            machine.tasks.push(Task::Force);
            machine.tasks.push(Task::Value { term: value, env });
            Ok(())
        },
        Computation::Bind(bound, body) => {
            machine.tasks.push(Task::Bind { body, env });
            machine.tasks.push(Task::Comp { term: bound, env });
            Ok(())
        },
        // An ascription runs as its body runs: the type it states is the
        // checker's, and evaluation reads none.
        Computation::Ascribe { body, .. } => {
            machine.tasks.push(Task::Comp { term: body, env });
            Ok(())
        },
        Computation::Case { scrutinee, .. } => {
            machine.tasks.push(Task::Case { term, env });
            machine.tasks.push(Task::Value {
                term: scrutinee,
                env,
            });
            Ok(())
        },
        Computation::Hole(hole) => {
            let (closure, face) = suspend_comp(domain, machine, term, env)?;
            stand_comp(domain, machine, NeutralHead::Hole { hole, closure }, face)
        },
        Computation::Mark { mark, .. } => {
            let (closure, face) = suspend_comp(domain, machine, term, env)?;
            stand_comp(domain, machine, NeutralHead::Mark { mark, closure }, face)
        },
    }
}

/// Close the hole or mark `term` over the environment `env` names, in
/// computation position.
///
/// # Specification
/// - requires: `env` names an environment this machine holds.
/// - ensures: a fresh computation closure over `term` and that environment, and
///   the face the neutral standing on it carries: `term`'s own when the
///   environment is empty, reduced otherwise.
/// - provides: the suspension a hole or a mark in computation position stands
///   on.
/// - fails: [`EvalFault::MachineInvariant`] when `env` names no environment.
/// - panics: none.
///
/// # Errors
/// - [`EvalFault::MachineInvariant`] — `env` names no environment.
///
/// # Adequacy
/// - hypothesis: L3 — a computation hole applied to an argument stands with the
///   application on its spine.
/// - witness: `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(closure, _)| matches!(closure, Suspended::Computation(id) if domain.comp_closure(id).is_some())))]
fn suspend_comp(
    domain: &mut DomainArena,
    machine: &Machine<'_>,
    term: ComputationId,
    env: EnvId,
) -> Result<(Suspended, CompTermFace), EvalFault>
{
    let captured = machine.capture(env)?;
    let closed = capture_keeps_source(&captured);
    let closure = domain.comp_closure_node(term, captured);
    Ok((
        Suspended::Computation(closure),
        composite_comp_face(closed, term),
    ))
}

/// Stand a fresh neutral over `head`, with no elimination, in computation
/// position.
///
/// # Specification
/// - requires: `head` cannot unfold and is held in computation position.
/// - ensures: one computation pushed: a neutral over `head`, an empty spine and
///   a rigid unfolding face, carrying `face`.
/// - provides: the weak head a computation hole or mark evaluates to.
/// - fails: [`EvalFault::Domain`] carrying the arena's refusal.
/// - panics: none.
///
/// # Errors
/// - [`EvalFault::Domain`] — the arena refused the neutral.
///
/// # Adequacy
/// - hypothesis: L3 — as [`suspend_comp`].
/// - witness: `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`
#[spec(captures: entry = machine.comps.len(), ensures: |ret| ret.is_err() || machine.comps.len() == entry.saturating_add(1_usize))]
fn stand_comp(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    head: NeutralHead,
    face: CompTermFace,
) -> Result<(), EvalFault>
{
    let neutral = domain
        .neutral_node(head, Vec::new(), Unfolding::Rigid)
        .map_err(EvalFault::Domain)?;
    machine.comps.push(domain.comp_neutral(neutral, face));
    Ok(())
}

/// Run the thunk the value on the stack holds, or get stuck on it.
///
/// # Specification
/// - requires: nothing; a missing value operand is admissible and refused.
/// - ensures: a thunk pushes a task entering its closure, so the forced
///   computation's weak head becomes this task's result; a stuck value grows
///   its neutral's spine by one `force`.
/// - provides: the `force` rule. The clause states the consumed value result
///   and the two admissible outcomes — one task entering the closure, or one
///   computation result; that the stuck outcome's spine grew by exactly one
///   `force` is a judgement over the produced graph, and the witnesses below
///   carry it.
/// - fails: [`EvalFault::MachineInvariant`] when the operand is missing,
///   [`EvalFault::Domain`] when the value or its closure does not resolve, and
///   [`EvalFault::ForcedNonThunk`] for another value. Ill-typed inputs are
///   refused rather than re-derived here.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   forcing a thunk, forcing a neutral, and forcing a pair.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_values == 0_usize))
        && (ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize)
                && machine.comps.len() == entry_comps)
                || (machine.comps.len() == entry_comps.saturating_add(1_usize)
                    && machine.tasks.len() == entry_tasks)))),
)]
fn step_force(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), EvalFault>
{
    let forced = machine.pop_value()?;
    let Some(node) = domain.value(forced)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainValue::Thunk { body, .. } => {
            let Some(closure) = domain.comp_closure(body)
            else {
                return Err(EvalFault::Domain(DomainFault::Dangling));
            };
            let term = closure.body();
            let env = machine.hold_env(closure.environment().clone());
            machine.tasks.push(Task::Body { body: term, env });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Force)?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::ForcedNonThunk),
    }
}

/// Apply the weak head on the stack to the value on the stack.
///
/// # Specification
/// - requires: nothing; a missing head or argument is admissible and refused.
/// - ensures: a lambda pushes a task entering its closure with the argument
///   bound in the intuitionistic zone; a neutral grows its spine by one
///   application; a fixpoint applied to a canonical value unfolds once, the
///   argument kept beneath for the application that follows, and applied to a
///   stuck value stacks itself on that value's neutral.
/// - provides: the β rule and its stuck case, which are one arm apart, and the
///   fixpoint's `<` gate. The clause states the consumed head and the three
///   admissible outcomes — one task entering the closure, one computation
///   result standing for the grown neutral, or the argument restored beneath
///   two tasks unfolding the fixpoint and applying it; that a stuck outcome's
///   spine grew by exactly one elimination is a judgement over the produced
///   graph, and the witnesses below carry it.
/// - fails: [`EvalFault::MachineInvariant`] for a missing head or argument,
///   [`EvalFault::Domain`] for a missing node, [`EvalFault::DanglingTerm`] for
///   a fixpoint closure over no source fixpoint, and
///   [`EvalFault::AppliedNonFunction`] when the head is a returner.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the four-way match, separated by
///   applying a lambda, a neutral, a returner, and a fixpoint at a constructor
///   and at a neutral.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::a_fixpoint_unfolds_at_a_constructor_and_sticks_at_a_neutral`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_comps == 0_usize || entry_values == 0_usize))
        && (ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize)
                && machine.comps.len() == entry_comps.saturating_sub(1_usize))
                || (machine.comps.len() == entry_comps
                    && machine.tasks.len() == entry_tasks)))
        || (machine.values.len() == entry_values
            && machine.comps.len() == entry_comps.saturating_sub(1_usize)
            && machine.tasks.len() == entry_tasks.saturating_add(2_usize))),
)]
fn step_apply(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), EvalFault>
{
    let head = machine.pop_comp()?;
    let argument = machine.pop_value()?;
    let Some(node) = domain.computation(head)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainComp::Lambda { body, .. } => {
            let Some(closure) = domain.comp_closure(body)
            else {
                return Err(EvalFault::Domain(DomainFault::Dangling));
            };
            let term = closure.body();
            // economy: the beta rule copies the closure's whole environment and
            // the copy is retained for the run, so a chain of n beta reductions
            // costs O(n^2) copying and O(n^2) retained entries against O(n)
            // steps. A deeply curried application is the shape that reaches it,
            // and this is the site it reaches — `Machine::extended` carries the
            // same cost at the bind and case rules. Upgrade path: hold the
            // environment as a persistent chain in the machine's own table — a
            // frame naming its parent, its zone and its binding — so an
            // extension is one push, and materialize a flat `Environment` only
            // where a closure captures one. That trades O(1) lookup for a walk,
            // so it is worth taking when a measurement says which of the two
            // dominates rather than before.
            let mut extended = closure.environment().clone();
            extended.extend(Zone::Intuitionistic, argument);
            let env = machine.hold_env(extended);
            machine.tasks.push(Task::Body { body: term, env });
            Ok(())
        },
        DomainComp::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Apply(argument))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainComp::Return { .. } => Err(EvalFault::AppliedNonFunction),
        // The `<` gate: a canonical argument unfolds the fixpoint once and
        // the application follows; a stuck one carries the fixpoint on its
        // spine until its head unfolds.
        DomainComp::Fixpoint { recursive, .. } => {
            let Some(&argument_node) = domain.value(argument)
            else {
                return Err(EvalFault::Domain(DomainFault::Dangling));
            };
            match argument_node {
                DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(domain, neutral, Elimination::Fixpoint(recursive))?;
                    machine
                        .comps
                        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
                    Ok(())
                },
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. } => {
                    machine.values.push(argument);
                    machine.tasks.push(Task::Apply);
                    unfold(core, domain, machine, recursive)
                },
            }
        },
    }
}

/// Unfold a fixpoint once: push the task entering its body with a thunk of
/// the fixpoint itself bound innermost in its own environment.
///
/// # Specification
/// - requires: nothing; a closure over anything but a source fixpoint is
///   admissible and refused.
/// - ensures: one task pushed, entering the fixpoint's body in the closure's
///   environment extended by a thunk suspending the closure itself.
/// - provides: `fix x. M ⇝ M[thunk (fix x. M)/x]`, the step both gates fire. It
///   is not otherwise bounded: the driver charges every task, so an unfolding
///   that never reaches a weak head runs out of fuel.
/// - fails: [`EvalFault::Domain`] when the closure does not resolve, and
///   [`EvalFault::DanglingTerm`] when it closes no source fixpoint.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an unfolding at a constructor reaches the branch the
///   constructor selects with the recursive call bound, and a loop under a bind
///   exhausts its fuel.
/// - witness: `eval::tests::a_fixpoint_unfolds_at_a_constructor_and_sticks_at_a_neutral`
/// - witness: `eval::tests::an_observed_loop_runs_out_of_fuel`
#[spec(
    captures: entry_tasks = machine.tasks.len(),
    ensures: |ret| ret.is_err() || machine.tasks.len() == entry_tasks.saturating_add(1_usize),
)]
fn unfold(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    recursive: CompClosureId,
) -> Result<(), EvalFault>
{
    let closure = domain
        .comp_closure(recursive)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let crate::closure::CompBody::Source(term) = closure.body()
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let Some(&Computation::Fixpoint { body, .. }) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let mut extended = closure.environment().clone();
    let recursion = domain.value_thunk(recursive, TermFace::Reduced);
    extended.extend(Zone::Intuitionistic, recursion);
    let env = machine.hold_env(extended);
    machine.tasks.push(Task::Comp { term: body, env });
    Ok(())
}

/// Apply the operator beneath the top of the value stack to the argument on
/// top of it.
///
/// # Specification
/// - requires: nothing; a malformed spine may leave an operator or argument
///   missing, which is refused rather than assumed away.
/// - ensures: a static lambda pushes a task entering its body with the argument
///   bound in the intuitionistic zone; a neutral grows its spine by one static
///   application and stands as a value again.
/// - provides: static beta and its stuck case, one arm apart, which is what
///   makes static normalization the value evaluation itself rather than a
///   second normaliser. The clause states the two consumed values and the two
///   admissible outcomes — one task entering the lambda's body, or one value
///   result standing for the grown neutral; that the stuck outcome's spine grew
///   by exactly one static application is a judgement over the produced graph,
///   and the witnesses below carry it.
/// - fails: [`EvalFault::MachineInvariant`] for a missing operator or argument;
///   [`EvalFault::AppliedNonOperator`] when the operator is neither a static
///   lambda nor stuck, without re-deriving types; [`EvalFault::DanglingTerm`]
///   when the lambda's closure holds anything but a static lambda.
/// - panics: none.
///
/// # Errors
/// As above, and [`EvalFault::Domain`] for a node that does not resolve.
///
/// # Adequacy
/// - hypothesis: L1 — over generated simply kinded static terms, normal order
///   and applicative order by substitution reach the normal form evaluation and
///   readback reach; the three-way match is separated by applying a static
///   lambda, a stuck variable and a unit, and a chain of redexes far deeper
///   than a small stack normalizes inside one.
/// - witness: `eval::tests::normalizes_beta_redex`
/// - witness: `eval::tests::normalization_preserves_a_stuck_application`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
/// - witness: `static_normalization::static_normalization::static_normalization_is_confluent`
/// - witness: `static_normalization::static_normalization::a_static_redex_normalizes_to_its_ground_type`
/// - witness: `static_normalization::static_normalization::a_deep_static_term_normalizes_inside_a_small_stack`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
#[spec(
    captures: [
        entry_values = machine.values.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_values < 2_usize))
        && (ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(2_usize)
            && machine.tasks.len() == entry_tasks.saturating_add(1_usize))
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && machine.tasks.len() == entry_tasks)),
)]
fn step_static_apply(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), EvalFault>
{
    let argument = machine.pop_value()?;
    let operator = machine.pop_value()?;
    let Some(node) = domain.value(operator)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainValue::StaticLambda { lambda, .. } => {
            let Some(closure) = domain.value_closure(lambda)
            else {
                return Err(EvalFault::Domain(DomainFault::Dangling));
            };
            let crate::ValueBody::Source(body) = closure.body()
            else {
                return Err(EvalFault::MachineInvariant);
            };
            let Some(&Value::StaticLambda(term)) = core.value(body)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let mut extended = closure.environment().clone();
            extended.extend(Zone::Intuitionistic, argument);
            let env = machine.hold_env(extended);
            machine.tasks.push(Task::Value { term, env });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::StaticApply(argument))?;
            let stood = domain
                .value_neutral(grown, TermFace::Reduced)
                .map_err(EvalFault::Domain)?;
            machine.values.push(stood);
            Ok(())
        },
        DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. } => Err(EvalFault::AppliedNonOperator),
    }
}

/// Sequence into a body once the bound computation has a weak head.
///
/// # Specification
/// - requires: one computation result on the stack; `env` names an environment
///   this machine holds.
/// - ensures: a returner pushes the body's task with the returned value bound;
///   a neutral grows its spine by one bind, capturing the body as a closure; a
///   fixpoint unfolds once beneath the same bind.
/// - provides: the sequencing rule, its stuck case, and the fixpoint's `>`
///   gate: one observation, one unfolding. The clause states the consumed
///   computation result and the three admissible outcomes — one task carrying
///   the body, one computation result standing for the grown neutral, or two
///   tasks re-binding beneath the unfolding; that the returned value is bound
///   in the body's environment, and that the stuck outcome's spine grew by
///   exactly one bind, are judgements over the produced graph, and the
///   witnesses below carry them.
/// - fails: [`EvalFault::BoundNonReturner`] when the bound computation is a
///   lambda.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the four-way match, separated by
///   binding a returner, a neutral, a lambda and a fixpoint.
/// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
/// - witness: `eval::tests::an_observed_loop_runs_out_of_fuel`
#[spec(
    requires: [!machine.comps.is_empty(), env.0 < machine.envs.len()],
    captures: [
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == entry_comps.saturating_sub(1_usize)
            && machine.tasks.len() == entry_tasks.saturating_add(1_usize))
        || (machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks)
        || (machine.comps.len() == entry_comps.saturating_sub(1_usize)
            && machine.tasks.len() == entry_tasks.saturating_add(2_usize)),
)]
fn step_bind(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    body: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let bound = machine.pop_comp()?;
    let Some(node) = domain.computation(bound)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainComp::Return { value, .. } => {
            let env = machine.extended(env, Zone::Intuitionistic, value)?;
            machine.tasks.push(Task::Comp { term: body, env });
            Ok(())
        },
        DomainComp::Neutral { neutral, .. } => {
            let captured = machine.capture(env)?;
            let closure = domain.comp_closure_node(body, captured);
            let grown = extend_spine(domain, neutral, Elimination::Bind(closure))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainComp::Lambda { .. } => Err(EvalFault::BoundNonReturner),
        // The `>` gate: the observation stays, and the fixpoint beneath it
        // unfolds once.
        DomainComp::Fixpoint { recursive, .. } => {
            machine.tasks.push(Task::Bind { body, env });
            unfold(core, domain, machine, recursive)
        },
    }
}

/// Choose a branch once the scrutinee has a value.
///
/// # Specification
/// - requires: one value result on the stack; `env` names an environment this
///   machine holds.
/// - ensures: an injection pushes the named branch's task with the injected
///   value bound; a neutral grows its spine by one case, capturing both
///   branches as closures so neither is evaluated.
/// - provides: the sum elimination and its stuck case. The clause states the
///   consumed value result and the two admissible outcomes — one task carrying
///   the chosen branch, or one computation result standing for the grown
///   neutral; that the branch the injection names is the one pushed, and that
///   the stuck outcome's spine grew by exactly one case, are judgements over
///   the produced graph, and the witnesses below carry them.
/// - fails: [`EvalFault::CasedNonInjection`] for any other value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the three-way match and the
///   side selection, separated by each injection, a neutral scrutinee and a
///   unit scrutinee.
/// - witness: `eval::tests::a_case_picks_the_branch_the_injection_names`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
#[spec(
    requires: [!machine.values.is_empty(), env.0 < machine.envs.len()],
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize)
                && machine.comps.len() == entry_comps)
                || (machine.comps.len() == entry_comps.saturating_add(1_usize)
                    && machine.tasks.len() == entry_tasks))),
)]
fn step_case(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(case) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let Computation::Case { ref branches, .. } = *case
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let scrutinee = machine.pop_value()?;
    let Some(node) = domain.value(scrutinee)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainValue::Injection { summand, body, .. } => {
            let term = *branches
                .get(usize::from(summand))
                .ok_or(EvalFault::UnknownSummand { summand })?;
            let env = machine.extended(env, Zone::Intuitionistic, body)?;
            machine.tasks.push(Task::Comp { term, env });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let captured = machine.capture(env)?;
            let mut closures = Vec::with_capacity(branches.len());
            for &branch in branches {
                closures.push(domain.comp_closure_node(branch, captured.clone()));
            }
            let held = domain.hold_branches(closures);
            let grown = extend_spine(domain, neutral, Elimination::Case(held))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::CasedNonInjection),
    }
}

/// Sequence into an already-captured continuation once the bound computation
/// has a weak head.
///
/// # Specification
/// - requires: nothing; an absent computation operand is admissible and
///   refused.
/// - ensures: a returner pushes the continuation's body with the returned value
///   bound innermost in its own environment; a neutral grows its spine by the
///   same bind, the closure reused rather than re-captured, except under a
///   word's first letter ([`crate::closure::CompBody::Prefixed`]), which
///   returns the letter before the neutral held as the value it stands for; a
///   fixpoint unfolds once beneath the same bind.
/// - provides: [`step_bind`] for a continuation a spine already captured, which
///   is how an unfolding re-applies a stuck bind.
/// - fails: [`EvalFault::MachineInvariant`] when the operand is missing,
///   [`EvalFault::BoundNonReturner`] when it is a lambda, and
///   [`EvalFault::Domain`] when a needed node does not resolve.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   an unfolded body that returns into the bind and one that stays stuck.
/// - witness: `eval::tests::a_reapplied_spine_fires_once_the_head_unfolds`
/// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
/// - witness: `eval::tests::reapplied_closures_keep_stuck_spines_and_refuse_wrong_formers`
/// - witness: `eval::words::tests::a_word_appends_on_its_first_word`
#[spec(
    captures: [entry_values = machine.values.len(), entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_comps == 0_usize))
        && machine.values.len() == entry_values
        && (ret.is_err()
            || (machine.comps.len() == entry_comps.saturating_sub(1_usize) && machine.tasks.len() == entry_tasks.saturating_add(1_usize))
            || (machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks)
            || (machine.comps.len() == entry_comps.saturating_sub(1_usize) && machine.tasks.len() == entry_tasks.saturating_add(2_usize))),
)]
fn step_bind_closure(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    body: CompClosureId,
) -> Result<(), EvalFault>
{
    let bound = machine.pop_comp()?;
    let Some(node) = domain.computation(bound)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainComp::Return { value, .. } => {
            let closure = domain
                .comp_closure(body)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            let term = closure.body();
            let mut extended = closure.environment().clone();
            extended.extend(Zone::Intuitionistic, value);
            let env = machine.hold_env(extended);
            machine.tasks.push(Task::Body { body: term, env });
            Ok(())
        },
        DomainComp::Neutral { neutral, .. } => {
            // A word's first letter goes back before its rest's stuck
            // transport, held as the value it stands for, as `ℓ ∷ ⟨c⟩` reads
            // its field: the transport is pure, so the bind is that field.
            if let Some(&crate::closure::CompBody::Prefixed(word)) = domain
                .comp_closure(body)
                .map(crate::closure::CompClosure::body)
                .as_ref()
            {
                let held = returned_value(domain, bound)?;
                let Some(&DomainValue::Constructor { tag, .. }) = domain.value(word)
                else {
                    return Err(EvalFault::MachineInvariant);
                };
                let prefixed = words::relettered(domain, word, tag, held)?;
                machine
                    .comps
                    .push(domain.comp_return(prefixed, CompTermFace::Reduced));
                return Ok(());
            }
            let grown = extend_spine(domain, neutral, Elimination::Bind(body))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainComp::Lambda { .. } => Err(EvalFault::BoundNonReturner),
        DomainComp::Fixpoint { recursive, .. } => {
            machine.tasks.push(Task::BindClosure(body));
            unfold(core, domain, machine, recursive)
        },
    }
}

/// Choose between two already-captured branches once the scrutinee has a
/// value.
///
/// # Specification
/// - requires: nothing; an absent value operand is admissible and refused.
/// - ensures: an injection pushes the named branch's body with the injected
///   value bound innermost in that branch's own environment; a neutral grows
///   its spine by the same case, both closures reused. Only the selected branch
///   is read; a missing unselected closure does not refuse the chosen branch.
/// - provides: [`step_case`] for branches a spine already captured, which is
///   how an unfolding re-applies a stuck case.
/// - fails: [`EvalFault::MachineInvariant`] when the operand is missing,
///   [`EvalFault::CasedNonInjection`] for another value, and
///   [`EvalFault::Domain`] when the scrutinee or chosen closure does not
///   resolve.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match and the side
///   selection, separated by an unfolded scrutinee injecting on the right.
/// - witness: `eval::tests::a_reapplied_spine_fires_once_the_head_unfolds`
/// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
/// - witness: `eval::tests::reapplied_cases_refuse_only_when_the_selected_closure_is_missing`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
/// - witness: `eval::tests::reapplied_closures_keep_stuck_spines_and_refuse_wrong_formers`
#[spec(
    captures: [entry_values = machine.values.len(), entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_values == 0_usize))
        && (ret.is_err()
            || (machine.values.len() == entry_values.saturating_sub(1_usize)
                && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize) && machine.comps.len() == entry_comps)
                    || (machine.comps.len() == entry_comps.saturating_add(1_usize) && machine.tasks.len() == entry_tasks)))),
)]
fn step_case_branches(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    branches: crate::arena::BranchSpan,
) -> Result<(), EvalFault>
{
    let scrutinee = machine.pop_value()?;
    let Some(node) = domain.value(scrutinee)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        DomainValue::Injection { summand, body, .. } => {
            let chosen = *domain
                .branches(branches)
                .map_err(EvalFault::Domain)?
                .get(usize::from(summand))
                .ok_or(EvalFault::UnknownSummand { summand })?;
            let closure = domain
                .comp_closure(chosen)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            let term = closure.body();
            let mut extended = closure.environment().clone();
            extended.extend(Zone::Intuitionistic, body);
            let env = machine.hold_env(extended);
            machine.tasks.push(Task::Body { body: term, env });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Case(branches))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::CasedNonInjection),
    }
}

/// Apply a native path using the same iterative evaluation stack as CBPV.
///
/// # Specification
/// - requires: nothing; missing operands are admitted as malformed spines.
/// - ensures: reflexivity returns unchanged; an equivalence, native or written
///   `equiv(f, g)`, invokes the forward map; product transport uses ordinary
///   bind closures, including neutral cases.
/// - provides: a returned value, a forward application or sequenced components,
///   never an evaluation of a certificate merely to compare it.
/// - fails: missing operands are `MachineInvariant`; dangling nodes, non-path
///   operands and existing evaluation faults retain their errors.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`.
///
/// # Adequacy
/// - hypothesis: L3 — product components sequence and reflexivity preserves
///   values. A computation-valued prefix followed by transport must return a
///   machine fault rather than panic under enforcement.
/// - witness: `eval::tests::native_transport_sequences_product_components`
/// - witness: `eval::tests::ill_shaped_reapplied_spines_return_machine_faults`
#[spec(
    captures: [values = machine.values.len(), comps = machine.comps.len(), tasks = machine.tasks.len(), path = machine.values.get(machine.values.len().saturating_sub(2)).copied(), value = machine.values.last().copied()],
    ensures: |ret| if values < 2 { ret == Err(EvalFault::MachineInvariant) && machine.values.is_empty() && machine.comps.len() == comps && machine.tasks.len() == tasks } else { ret.is_err() || match path.and_then(|id| domain.value(id)) {
        Some(&DomainValue::PathCertificate { certificate, .. }) => match core.value(certificate) {
            Some(&Value::PathRefl(_)) => machine.values.len() == values.saturating_sub(2) && machine.tasks.len() == tasks && machine.comps.len() == comps.saturating_add(1) && machine.comps.last().is_some_and(|&id| matches!(domain.computation(id), Some(&DomainComp::Return { value: returned, .. }) if Some(returned) == value)),
            Some(&(Value::PathEquiv { forward, .. } | Value::Equiv(forward, _))) => machine.values.len() == values.saturating_sub(1) && machine.values.last().copied() == value && machine.comps.len() == comps && matches!(machine.tasks.get(tasks..), Some(&[Task::Apply, Task::Force, Task::Value { term, .. }]) if term == forward),
            _ => false,
        },
        Some(&DomainValue::PathProduct { .. }) => (machine.values.len() == values && machine.tasks.len() == tasks.saturating_add(2) && machine.comps.len() == comps) || (machine.values.len() == values.saturating_sub(2) && machine.tasks.len() == tasks && machine.comps.len() == comps.saturating_add(1)),
        Some(&DomainValue::Neutral { .. }) => machine.values.len() == values.saturating_sub(2) && machine.tasks.len() == tasks && machine.comps.len() == comps.saturating_add(1),
        _ => false,
    } },
)]
fn step_transport(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
) -> Result<(), EvalFault>
{
    let value = machine.pop_value()?;
    let path = machine.pop_value()?;
    match domain
        .value(path)
        .copied()
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        DomainValue::PathCertificate { certificate, .. } => match core.value(certificate) {
            Some(&Value::PathRefl(_)) => {
                machine
                    .comps
                    .push(domain.comp_return(value, CompTermFace::Reduced));
                Ok(())
            },
            Some(&(Value::PathEquiv { forward, .. } | Value::Equiv(forward, _))) => {
                machine.values.push(value);
                machine.tasks.push(Task::Apply);
                machine.tasks.push(Task::Force);
                machine.tasks.push(Task::Value {
                    term: forward,
                    env: Machine::root_env(),
                });
                Ok(())
            },
            Some(&Value::Ua { .. }) => Err(EvalFault::TransportedUnderived),
            _ => Err(EvalFault::DanglingTerm),
        },
        DomainValue::PathProduct { first, second, .. } => {
            match domain
                .value(value)
                .copied()
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?
            {
                DomainValue::Tuple { fields, .. } => {
                    let &[left, right] = domain.fields(fields).map_err(EvalFault::Domain)?
                    else {
                        return Err(EvalFault::TransportedNonPath);
                    };
                    let continuation =
                        domain.native_continuation(crate::closure::CompBody::TransportPair {
                            path: second,
                            value: right,
                        });
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::Transport);
                    machine.values.extend([first, left]);
                    Ok(())
                },
                DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(domain, neutral, Elimination::ProductTransport(path))?;
                    machine
                        .comps
                        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
                    Ok(())
                },
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Literal { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. } => Err(EvalFault::TransportedNonPath),
            }
        },
        DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Transport(value))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::TransportedNonPath),
    }
}

/// Transport the operand above an element path along it, in a motive.
///
/// # Specification
/// - requires: the path, then the operand, occupy the top of the value stack;
///   `motive` closes a value type under one binder over the environment the
///   transport was read in.
/// - ensures: reflexivity returns the operand unchanged, and so does a motive
///   that never reads its binder, the kernel's constant row; a product motive
///   read against a tuple of its arity transports each component in its own
///   motive, binding each before the next, and returns their tuple; a sum
///   motive read against an injection transports the payload in its summand's
///   motive and binds it into its injection; a list motive returns `nil`
///   unchanged and binds a cell's head, transported in the element's motive,
///   before its tail, transported in the list's — the kernel's reducts, so a
///   component stuck on a definition holds the components after it; the decode
///   of the motive's own binder hands a universe path to native transport; the
///   singleton `y. Path(D, l, y)`, its carrier and left endpoint closed over
///   the binder, read against reflexivity returns the path itself; a word moves
///   by the rules of the `words` module, and in that singleton a path no word
///   rule reads moves the empty word or a letter-headed word by appending on
///   it; any other configuration over a stuck path stacks the transport on the
///   path's spine.
/// - provides: transport's computation rules — identity on `here` and in a
///   constant motive, through the motive's constructors, the singleton's, and
///   along a word — and its stuck form.
/// - fails: [`EvalFault::MachineInvariant`] for a missing operand or a motive
///   closure holding no type; [`EvalFault::TransportedNonPath`] for a path that
///   is neither reflexivity nor stuck; domain faults for dangling nodes;
///   [`EvalFault::DanglingTerm`] for a family naming no core node.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity, a constant motive, a stuck path in a product
///   motive over a tuple, a stuck path in a sum motive over an injection, a
///   stuck path in the singleton over reflexivity, and a stuck path in a motive
///   reading its binder each reach their own arm; dropping the reflexivity or
///   the constant rule, reordering components, losing the summand or computing
///   a family whose left endpoint moves changes the read-back term.
/// - witness: `identity::tests::transport_along_here_is_the_identity`
/// - witness: `identity::tests::transport_in_a_constant_motive_returns_the_operand`
/// - witness: `identity::tests::transport_through_a_product_is_componentwise`
/// - witness: `identity::tests::transport_through_a_sum_keeps_the_summand`
/// - witness: `identity::tests::transport_in_the_singleton_returns_the_path`
/// - witness: `identity::tests::transport_along_a_stuck_path_is_stuck`
/// - witness: `identity::tests::transport_moves_a_list_through_a_universe_path`
/// - witness: `eval::words::tests::a_word_appends_on_its_first_word`
#[spec(
    captures: [values = machine.values.len(), comps = machine.comps.len(), tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == comps.saturating_add(1_usize) && machine.tasks.len() == tasks
            && machine.values.len() == values.saturating_sub(2_usize))
        || (machine.comps.len() <= comps.saturating_add(1_usize) && machine.tasks.len() > tasks && machine.values.len() <= values),
)]
fn step_path_transport(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: crate::arena::ValueClosureId,
) -> Result<(), EvalFault>
{
    let value = machine.pop_value()?;
    let path = machine.pop_value()?;
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    let carried = *domain.value(path).ok_or(dangling)?;
    if let DomainValue::Here { .. } = carried {
        machine
            .comps
            .push(domain.comp_return(value, CompTermFace::Reduced));
        return Ok(());
    }
    let closure = domain.value_closure(motive).ok_or(dangling)?;
    let crate::ValueBody::ValueType(family) = closure.body()
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let environment = closure.environment().clone();
    let read = crate::identity::binder_read(core, family).map_err(|fault| match fault {
        crate::free::FreeFault::Dangling => EvalFault::DanglingTerm,
        crate::free::FreeFault::MachineInvariant => EvalFault::MachineInvariant,
    })?;
    if read == crate::free::Membership::Absent {
        machine
            .comps
            .push(domain.comp_return(value, CompTermFace::Reduced));
        return Ok(());
    }
    match (
        core.value_type(family),
        *domain.value(value).ok_or(dangling)?,
    ) {
        (Some(&ValueType::Product(ref components)), DomainValue::Tuple { fields, .. }) => {
            if domain.fields(fields).map_err(EvalFault::Domain)?.len() == components.len() {
                return move_components(
                    core,
                    domain,
                    machine,
                    Componentwise {
                        mover: Mover::Transport,
                        motive,
                        along: path,
                        source: value,
                    },
                    (Environment::new(), ComponentCount::from(0_usize)),
                );
            }
        },
        (
            Some(&ValueType::Sum(ref summands)),
            DomainValue::Injection {
                summand,
                body: payload,
                ..
            },
        ) => {
            if let Some(&component) = summands.get(usize::from(summand)) {
                let part =
                    domain.value_closure_node(crate::ValueBody::ValueType(component), environment);
                let continuation = domain.native_continuation(CompBody::Inject(summand));
                machine.tasks.push(Task::BindClosure(continuation));
                machine.tasks.push(Task::PathTransport(part));
                machine.values.extend([path, payload]);
                return Ok(());
            }
        },
        (Some(&ValueType::List(_)), DomainValue::ListNil { .. }) => {
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            return Ok(());
        },
        (Some(&ValueType::List(element)), DomainValue::ListCons { first, second, .. }) => {
            let head = domain.value_closure_node(crate::ValueBody::ValueType(element), environment);
            let continuation = domain.native_continuation(CompBody::MoveTail {
                mover: Mover::Transport,
                motive,
                along: path,
                tail: second,
            });
            machine.tasks.push(Task::BindClosure(continuation));
            machine.tasks.push(Task::PathTransport(head));
            machine.values.extend([path, first]);
            return Ok(());
        },
        // The motive's own binder decoded: the universe path itself carries
        // the operand, as native transport does.
        (Some(&ValueType::Element { code, .. }), _)
            if matches!(
                core.value(code),
                Some(&Value::Variable { zone: gandr_core_term::Zone::Intuitionistic, index }) if u32::from(index) == 0
            ) && matches!(
                carried,
                DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. }
            ) =>
        {
            machine.tasks.push(Task::Transport);
            machine.tasks.push(Task::Supply(value));
            machine.tasks.push(Task::Supply(path));
            return Ok(());
        },
        (Some(&ValueType::Path { .. }), DomainValue::Here { .. }) => {
            let read =
                crate::identity::transport_family(core, family).map_err(|fault| match fault {
                    crate::free::FreeFault::Dangling => EvalFault::DanglingTerm,
                    crate::free::FreeFault::MachineInvariant => EvalFault::MachineInvariant,
                })?;
            if read == crate::identity::TransportFamily::Singleton {
                machine
                    .comps
                    .push(domain.comp_return(path, CompTermFace::Reduced));
                return Ok(());
            }
        },
        _ => {},
    }
    if let DomainValue::Constructor { .. } = carried
        && words::transport(core, domain, machine, motive, (path, value))? == words::Moved::Stepped
    {
        return Ok(());
    }
    if let Some(body) = words::named(core, domain, machine, path)? {
        words::reread(
            machine,
            motive,
            (path, value),
            (gandr_kernel_term::Side::Left, body),
        );
        return Ok(());
    }
    // `then` appends on its first word when the path moved along reads no
    // further.
    if words::appended(core, domain, machine, motive, (path, value))? == words::Moved::Stepped {
        return Ok(());
    }
    let DomainValue::Neutral { neutral, .. } = carried
    else {
        return Err(EvalFault::TransportedNonPath);
    };
    let grown = extend_spine(domain, neutral, Elimination::PathTransport {
        motive,
        value,
    })?;
    machine
        .comps
        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
    Ok(())
}

/// Ride the value above a flow along it, in a motive, by the kernel's directed
/// computation table.
///
/// # Specification
/// - requires: the flow, then the value, occupy the top of the value stack;
///   `motive` closes a value type under one binder over the environment the
///   ride was read in.
/// - ensures: the kernel's rows in its order: `stay` returns the value; a
///   composite rides its first leg, then its second from the result; a motive
///   that ignores its binder returns the value; a product motive over a tuple
///   of its arity, a sum motive over an injection and a list motive over a list
///   cell ride constructorwise, each part bound before the next and the
///   constructor returned last, `nil` returning unchanged; at the decode of the
///   motive's own binder a forward flow applies its translator, a function flow
///   returns the function wrapped by its boundaries, in a thunk that rides the
///   argument along the domain flow, applies the function and rides the result
///   along the codomain flow, and a flow product rides a pair's left component
///   along its first flow, then the right along its second, and pairs them; at
///   the singleton `y. Flow(D, l, y)` a `stay` value returns the flow and any
///   other value composes with it. A part stuck on a definition holds every
///   part after it, as the kernel's reduct binds it. A session simulation
///   returns the run unchanged — the checker admitted it by the protocol's
///   simulation, and runs move between related sessions as themselves. Any
///   other configuration over a stuck flow stacks the ride on the flow's spine.
/// - provides: the ride's computation rules, the same table the kernel replays,
///   and its stuck form.
/// - fails: [`EvalFault::MachineInvariant`] for a missing operand, a flow of
///   the wrong part count or a motive closure holding no type;
///   [`EvalFault::RodeUncomputed`] for a canonical flow no row moves the value
///   along; domain faults for dangling nodes; [`EvalFault::DanglingTerm`] for a
///   family naming no core node.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Adequacy
/// - hypothesis: L3 — `stay`, a composite of two forward flows, a constant
///   motive over a stuck flow, a pair motive, a forward flow and a function
///   flow at the decode of the binder, the flow singleton, and a stuck flow at
///   the identity motive each reach their own row; dropping a row, reordering a
///   composite's legs or a function flow's boundaries changes the read-back
///   term; a stuck left component of a flow product, a product motive, a sum
///   motive or a list cell holds the parts after it.
/// - witness: `identity::tests::rides_compute_by_the_kernels_rows`
/// - witness: `identity::tests::a_function_flow_rides_in_variance_order`
/// - witness: `identity::tests::a_flow_product_rides_a_pair_componentwise`
/// - witness: `identity::tests::a_stuck_part_holds_the_parts_after_it`
#[spec(
    captures: [values = machine.values.len(), comps = machine.comps.len(), tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || (machine.comps.len() == comps.saturating_add(1_usize) && machine.tasks.len() == tasks && machine.values.len() == values.saturating_sub(2_usize))
        || (machine.comps.len() == comps && machine.tasks.len() > tasks),
)]
fn step_ride(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: crate::arena::ValueClosureId,
) -> Result<(), EvalFault>
{
    let value = machine.pop_value()?;
    let flow = machine.pop_value()?;
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    let carried = *domain.value(flow).ok_or(dangling)?;
    match carried {
        DomainValue::Flow {
            former: crate::domain::FlowFormer::Stay,
            ..
        } => {
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            return Ok(());
        },
        DomainValue::Flow {
            former: crate::domain::FlowFormer::Then,
            parts,
            ..
        } => {
            let &[first, second] = domain.fields(parts).map_err(EvalFault::Domain)?
            else {
                return Err(EvalFault::MachineInvariant);
            };
            let onward = domain.native_continuation(crate::closure::CompBody::RideAlong {
                motive,
                flow: second,
            });
            machine.tasks.push(Task::BindClosure(onward));
            machine.tasks.push(Task::Ride(motive));
            machine.values.extend([first, value]);
            return Ok(());
        },
        DomainValue::PathCertificate { certificate, .. }
            if matches!(core.value(certificate), Some(Value::SessionRelated { .. })) =>
        {
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            return Ok(());
        },
        DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Neutral { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => {},
    }
    let closure = domain.value_closure(motive).ok_or(dangling)?;
    let crate::ValueBody::ValueType(family) = closure.body()
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let environment = closure.environment().clone();
    let free = |fault| match fault {
        crate::free::FreeFault::Dangling => EvalFault::DanglingTerm,
        crate::free::FreeFault::MachineInvariant => EvalFault::MachineInvariant,
    };
    if crate::identity::binder_read(core, family).map_err(free)? == crate::free::Membership::Absent
    {
        machine
            .comps
            .push(domain.comp_return(value, CompTermFace::Reduced));
        return Ok(());
    }
    match (
        core.value_type(family),
        *domain.value(value).ok_or(dangling)?,
    ) {
        (Some(&ValueType::Product(ref components)), DomainValue::Tuple { fields, .. }) => {
            if domain.fields(fields).map_err(EvalFault::Domain)?.len() == components.len() {
                return move_components(
                    core,
                    domain,
                    machine,
                    Componentwise {
                        mover: Mover::Ride,
                        motive,
                        along: flow,
                        source: value,
                    },
                    (Environment::new(), ComponentCount::from(0_usize)),
                );
            }
        },
        (
            Some(&ValueType::Sum(ref summands)),
            DomainValue::Injection {
                summand,
                body: payload,
                ..
            },
        ) => {
            if let Some(&component) = summands.get(usize::from(summand)) {
                let part =
                    domain.value_closure_node(crate::ValueBody::ValueType(component), environment);
                let continuation = domain.native_continuation(CompBody::Inject(summand));
                machine.tasks.push(Task::BindClosure(continuation));
                machine.tasks.push(Task::Ride(part));
                machine.values.extend([flow, payload]);
                return Ok(());
            }
        },
        (Some(&ValueType::List(_)), DomainValue::ListNil { .. }) => {
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            return Ok(());
        },
        (Some(&ValueType::List(element)), DomainValue::ListCons { first, second, .. }) => {
            let head = domain.value_closure_node(crate::ValueBody::ValueType(element), environment);
            let continuation = domain.native_continuation(CompBody::MoveTail {
                mover: Mover::Ride,
                motive,
                along: flow,
                tail: second,
            });
            machine.tasks.push(Task::BindClosure(continuation));
            machine.tasks.push(Task::Ride(head));
            machine.values.extend([flow, first]);
            return Ok(());
        },
        // The motive's own binder decoded: a forward flow applies its
        // translator, and a function flow wraps the function in its
        // boundaries.
        (Some(&ValueType::Element { code, .. }), _)
            if matches!(
                core.value(code),
                Some(&Value::Variable { zone: gandr_core_term::Zone::Intuitionistic, index }) if u32::from(index) == 0
            ) =>
        {
            match carried {
                DomainValue::Flow {
                    former: crate::domain::FlowFormer::Forward,
                    parts,
                    ..
                } => {
                    let &[translator] = domain.fields(parts).map_err(EvalFault::Domain)?
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    machine.values.push(value);
                    machine.tasks.push(Task::Apply);
                    machine.tasks.push(Task::Force);
                    machine.tasks.push(Task::Supply(translator));
                    return Ok(());
                },
                DomainValue::Flow {
                    former: crate::domain::FlowFormer::Function,
                    ..
                } => {
                    let wrapped =
                        domain.native_continuation(crate::closure::CompBody::RideFunction {
                            motive,
                            flow,
                            function: value,
                        });
                    let thunk = domain.value_thunk(wrapped, TermFace::Reduced);
                    machine
                        .comps
                        .push(domain.comp_return(thunk, CompTermFace::Reduced));
                    return Ok(());
                },
                // A flow product rides a pair's left component along its first
                // flow, then the right along its second, each at the decode of
                // the binder, and pairs them.
                DomainValue::Flow {
                    former: crate::domain::FlowFormer::Product,
                    parts,
                    ..
                } => {
                    let &[first, second] = domain.fields(parts).map_err(EvalFault::Domain)?
                    else {
                        return Err(EvalFault::MachineInvariant);
                    };
                    if let DomainValue::Tuple { fields, .. } =
                        *domain.value(value).ok_or(dangling)?
                    {
                        let fields = domain.fields(fields).map_err(EvalFault::Domain)?;
                        let &[left, right] = fields
                        else {
                            return Err(EvalFault::RodeUncomputed);
                        };
                        let continuation = domain.native_continuation(CompBody::RidePair {
                            motive,
                            flow: second,
                            value: right,
                        });
                        machine.tasks.push(Task::BindClosure(continuation));
                        machine.tasks.push(Task::Ride(motive));
                        machine.values.extend([first, left]);
                        return Ok(());
                    }
                },
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Neutral { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. } => {},
            }
        },
        (Some(&ValueType::Flow { .. }), held)
            if crate::identity::transport_family(core, family).map_err(free)?
                == crate::identity::TransportFamily::Singleton =>
        {
            let result = match held {
                DomainValue::Flow {
                    former: crate::domain::FlowFormer::Stay,
                    ..
                } => flow,
                DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Neutral { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. } => domain.value_flow(
                    crate::domain::FlowFormer::Then,
                    [value, flow],
                    TermFace::Reduced,
                ),
            };
            machine
                .comps
                .push(domain.comp_return(result, CompTermFace::Reduced));
            return Ok(());
        },
        _ => {},
    }
    let DomainValue::Neutral { neutral, .. } = carried
    else {
        return Err(EvalFault::RodeUncomputed);
    };
    let grown = extend_spine(domain, neutral, Elimination::Ride { motive, value })?;
    machine
        .comps
        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
    Ok(())
}

/// The task moving the value above a path or flow on the value stack in a
/// motive, for a mover.
///
/// # Specification
/// trivial.
const fn moving(
    mover: Mover,
    motive: crate::arena::ValueClosureId,
) -> Task
{
    match mover {
        Mover::Transport => Task::PathTransport(motive),
        Mover::Ride => Task::Ride(motive),
    }
}

/// A tuple moving componentwise through its product motive.
#[derive(Clone, Copy, Debug)]
struct Componentwise
{
    /// Transport or ride.
    mover: Mover,
    /// The product motive, closed over its environment.
    motive: crate::arena::ValueClosureId,
    /// The path or flow every component moves along.
    along: DomainValueId,
    /// The tuple moved.
    source: DomainValueId,
}

/// Move the next component of a tuple in its own part of the product motive,
/// or return the tuple of every moved component.
///
/// # Specification
/// - requires: `moving_tuple.motive` closes a product motive whose arity is
///   `moving_tuple.source`'s; `count` components have moved, their results
///   bound in `bound`, the latest innermost.
/// - ensures: with a component left, the move of the next component in its part
///   along `moving_tuple.along`, under a continuation over `bound` that moves
///   the rest; with none left, the return of the tuple of `bound`'s values in
///   component order. This is the kernel's `x₀ ← step(P₀, p, v₀); …; return
///   (x₀, …)`, so a component stuck on a definition holds every component after
///   it.
/// - provides: the product row of transport and ride.
/// - fails: [`EvalFault::MachineInvariant`] for a motive closure holding no
///   product, a source that is no tuple, an arity mismatch or a binding `bound`
///   lacks; [`EvalFault::DanglingTerm`] for a motive naming no core node;
///   domain faults for dangling nodes.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Termination
/// - reason: the `for` loop over the moved components, not recursion; each
///   later component moves in a later step of the machine.
/// - measure: the components left to read off `bound`.
///
/// # Adequacy
/// - hypothesis: L3 — a three-component product motive moves its components in
///   order and returns them in source order; a component stuck on its path
///   holds the components after it; reordering the reads off the environment or
///   moving the next component before the bind changes the read-back term.
/// - witness: `identity::tests::a_product_motive_binds_each_component_before_the_next`
/// - witness: `identity::tests::a_stuck_part_holds_the_parts_after_it`
#[spec(
    captures: [values = machine.values.len(), comps = machine.comps.len(), tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == comps.saturating_add(1_usize) && machine.tasks.len() == tasks && machine.values.len() == values)
        || (machine.comps.len() == comps && machine.tasks.len() == tasks.saturating_add(2_usize) && machine.values.len() == values.saturating_add(2_usize)),
)]
fn move_components(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    moving_tuple: Componentwise,
    (bound, count): (Environment, ComponentCount),
) -> Result<(), EvalFault>
{
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    let closure = domain.value_closure(moving_tuple.motive).ok_or(dangling)?;
    let crate::ValueBody::ValueType(family) = closure.body()
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let environment = closure.environment().clone();
    let family = core.value_type(family).ok_or(EvalFault::DanglingTerm)?;
    let ValueType::Product(ref parts) = *family
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let moved = usize::from(count);
    let DomainValue::Tuple { fields, .. } = *domain.value(moving_tuple.source).ok_or(dangling)?
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let field = domain
        .fields(fields)
        .map_err(EvalFault::Domain)?
        .get(moved)
        .copied();
    match (parts.get(moved), field) {
        (Some(&part), Some(field)) => {
            let part = domain.value_closure_node(crate::ValueBody::ValueType(part), environment);
            let next = moved
                .checked_add(1_usize)
                .ok_or(EvalFault::MachineInvariant)?;
            let continuation = domain.native_continuation_over(
                CompBody::Components {
                    mover: moving_tuple.mover,
                    motive: moving_tuple.motive,
                    along: moving_tuple.along,
                    source: moving_tuple.source,
                    moved: ComponentCount::from(next),
                },
                bound,
            );
            machine.tasks.push(Task::BindClosure(continuation));
            machine.tasks.push(moving(moving_tuple.mover, part));
            machine.values.extend([moving_tuple.along, field]);
            Ok(())
        },
        (None, None) => {
            let mut components = Vec::with_capacity(moved);
            for index in (0 .. moved).rev() {
                let index =
                    u32::try_from(index).map_err(|_overflow| EvalFault::MachineInvariant)?;
                let component = bound
                    .lookup(Zone::Intuitionistic, DeBruijnIndex::from(index))
                    .ok_or(EvalFault::MachineInvariant)?;
                components.push(component);
            }
            let tuple = domain.value_tuple(components, TermFace::Reduced);
            machine
                .comps
                .push(domain.comp_return(tuple, CompTermFace::Reduced));
            Ok(())
        },
        (Some(_), None) | (None, Some(_)) => Err(EvalFault::MachineInvariant),
    }
}

/// Transport the operand above an identity over a path, a start and the path
/// along a two-entry telescope, in a motive `Π (y : A). Π (z : B). F C`.
///
/// # Specification
/// - requires: the path, the start, the identity over the path and the operand
///   occupy the top of the value stack in that order; `motive` closes the
///   motive's computation type over the environment the transport was read in.
/// - ensures: when both identities are reflexivity the operand returns
///   unchanged; when only the path is `here(c)` the operand transports along
///   the identity over it in the fibre `z. C[c, z]`; over a stuck path the
///   transport stacks on the path's spine.
/// - provides: the telescope transport's computation rules, a subset of the
///   kernel's, and its stuck form.
/// - fails: [`EvalFault::MachineInvariant`] for a missing operand, or a motive
///   closure holding no telescope where the fibre is read;
///   [`EvalFault::TransportedNonPath`] for a path that is neither reflexivity
///   nor stuck; domain faults for dangling nodes.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Adequacy
/// - hypothesis: L3 — `here` along both identities, `here` along the path with
///   a stuck identity over it, and a stuck path each reach their own arm;
///   dropping the fibre's point or the stuck form's start changes the read-back
///   term.
/// - witness: `identity::tests::telescope_transport_along_here_is_the_identity`
/// - witness: `identity::tests::telescope_transport_along_here_replays_the_fibre`
/// - witness: `identity::tests::telescope_transport_along_a_stuck_path_is_stuck`
#[spec(
    captures: [values = machine.values.len(), comps = machine.comps.len(), tasks = machine.tasks.len()],
    ensures: |ret| ret.is_err() || (machine.values.len() == values.saturating_sub(4_usize)
        && ((machine.comps.len() == comps.saturating_add(1_usize) && machine.tasks.len() == tasks)
            || (machine.comps.len() == comps && machine.tasks.len() > tasks))),
)]
fn step_telescope_transport(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    motive: crate::arena::ValueClosureId,
) -> Result<(), EvalFault>
{
    let value = machine.pop_value()?;
    let over = machine.pop_value()?;
    let start = machine.pop_value()?;
    let path = machine.pop_value()?;
    let dangling = EvalFault::Domain(DomainFault::Dangling);
    match *domain.value(path).ok_or(dangling)? {
        DomainValue::Here { point, .. } => {
            if let DomainValue::Here { .. } = *domain.value(over).ok_or(dangling)? {
                machine
                    .comps
                    .push(domain.comp_return(value, CompTermFace::Reduced));
                return Ok(());
            }
            let closure = domain.value_closure(motive).ok_or(dangling)?;
            let crate::ValueBody::CompType(telescope) = closure.body()
            else {
                return Err(EvalFault::MachineInvariant);
            };
            let mut environment = closure.environment().clone();
            let body = telescope_body(core, telescope)?;
            environment.extend(Zone::Intuitionistic, point);
            let fibre = domain.value_closure_node(crate::ValueBody::ValueType(body), environment);
            machine.tasks.push(Task::PathTransport(fibre));
            machine.tasks.push(Task::Supply(value));
            machine.tasks.push(Task::Supply(over));
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::TelescopeTransport {
                motive,
                start,
                over,
                value,
            })?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::TransportedNonPath),
    }
}

/// The returned type `C` of a telescope motive `Π (y : A). Π (z : B). F C`,
/// standing under both entries.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `C` exactly when the motive has that shape.
/// - provides: the fibre read of [`step_telescope_transport`].
/// - fails: [`EvalFault::MachineInvariant`] for any other shape, which the
///   checker refuses before evaluation.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the fibre transport of a two-arrow motive reads its body.
/// - witness: `identity::tests::telescope_transport_along_here_replays_the_fibre`
#[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|body| core.value_type(body).is_some()))]
fn telescope_body(
    core: &CoreArena,
    motive: gandr_core_term::CompTypeId,
) -> Result<gandr_core_term::ValueTypeId, EvalFault>
{
    let Some(&CompType::Pi { codomain, .. }) = core.comp_type(motive)
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let Some(&CompType::Pi {
        codomain: innermost,
        ..
    }) = core.comp_type(codomain)
    else {
        return Err(EvalFault::MachineInvariant);
    };
    match core.comp_type(innermost) {
        Some(&CompType::Returner { result, .. }) if core.value_type(result).is_some() => Ok(result),
        _ => Err(EvalFault::MachineInvariant),
    }
}

/// Queue the eliminations of `spine` over the value the machine produces next,
/// innermost elimination first, and say which polarity they leave.
///
/// # Specification
/// - requires: nothing; an ill-shaped spine is refused by the step reaching it.
/// - ensures: one frame per elimination — a supplied operand and its consumer
///   for an application, a static application, a transport and a path transport
///   — queued so the innermost runs first; the answer is a value exactly when
///   every elimination is a static application.
/// - provides: the re-application of a neutral's spine once its head unfolds,
///   shared by the conversion's unfolding channel and a compound endpoint run
///   through its head's definition.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a mixed force/application/bind spine reduces after
///   unfolding, and two case branches retain different captures; reversing
///   frames changes the answer.
/// - witness: `eval::tests::a_reapplied_spine_fires_once_the_head_unfolds`
/// - witness: `eval::tests::reapplied_eliminations_preserve_captures_and_argument_order`
/// - witness: `identity::tests::a_compound_endpoint_runs_through_a_definition`
#[spec(
    captures: entry_tasks = machine.tasks.len(),
    ensures: |ret| machine.tasks.len() >= entry_tasks.saturating_add(spine.len())
        && (ret == Answer::Value) == spine.iter().all(|elimination| matches!(elimination, Elimination::StaticApply(_))),
)]
fn push_eliminations(
    machine: &mut Machine<'_>,
    spine: &[Elimination],
) -> Answer
{
    let mut answer = Answer::Value;
    for elimination in spine.iter().rev() {
        match *elimination {
            Elimination::DataCase(closure) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::DataCaseClosure(closure));
            },
            Elimination::Split(closure) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::SplitClosure(closure));
            },
            Elimination::Projection(term) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::Projection(term));
            },
            Elimination::ListFold {
                element,
                result,
                on_nil,
                on_cons,
            } => {
                answer = Answer::Computation;
                machine.tasks.push(Task::ListFold {
                    element,
                    result,
                    on_nil,
                    on_cons,
                });
            },
            Elimination::Transport(value) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::Transport);
                machine.tasks.push(Task::Supply(value));
            },
            Elimination::ProductTransport(path) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::ProductTransport(path));
            },
            Elimination::PathTransport { motive, value } => {
                answer = Answer::Computation;
                machine.tasks.push(Task::PathTransport(motive));
                machine.tasks.push(Task::Supply(value));
            },
            Elimination::Ride { motive, value } => {
                answer = Answer::Computation;
                machine.tasks.push(Task::Ride(motive));
                machine.tasks.push(Task::Supply(value));
            },
            Elimination::TelescopeTransport {
                motive,
                start,
                over,
                value,
            } => {
                answer = Answer::Computation;
                machine.tasks.push(Task::TelescopeTransport(motive));
                for held in [value, over, start] {
                    machine.tasks.push(Task::Supply(held));
                }
            },
            Elimination::StaticApply(argument) => {
                machine.tasks.push(Task::StaticApply);
                machine.tasks.push(Task::Supply(argument));
            },
            Elimination::Apply(argument) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::Apply);
                machine.tasks.push(Task::Supply(argument));
            },
            Elimination::Force => {
                answer = Answer::Computation;
                machine.tasks.push(Task::Force);
            },
            Elimination::Bind(body) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::BindClosure(body));
            },
            Elimination::Case(branches) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::CaseBranches(branches));
            },
            Elimination::Fixpoint(recursive) => {
                answer = Answer::Computation;
                machine.tasks.push(Task::FixpointClosure(recursive));
            },
        }
    }
    answer
}

/// Deliver the value a compound endpoint's computation returns, running a
/// computation stuck on a manifest definition on through that definition
/// when `stance` is [`Endpoints::Run`], and reading the rest through their
/// binds ([`read_from`]).
///
/// # Specification
/// - requires: nothing; a dangling id is refused.
/// - ensures: under [`Endpoints::Run`], a computation stuck on a neutral whose
///   head has a body here — forced already, or lowered in this run's chain —
///   queues the head's body, the neutral's spine over it and this delivery
///   again — [`Task::Returned`] at the run's own stance, [`Task::Running`]
///   otherwise — so the endpoint runs on until it returns or sticks on a rigid
///   head; any other computation, under either stance, is delivered as
///   [`read_from`] delivers it from its spine's first position.
/// - provides: the reading of a compound endpoint as what its computation
///   returns: `dbl(x)` and `x + x` are one endpoint once `dbl` unfolds. The run
///   is strict where a value position is lazy, because an endpoint is compared
///   by its returned value, and the driver's fuel bounds it. A held endpoint
///   leaves that unfolding to the conversion, which records it.
/// - fails: as [`read_from`].
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as [`read_from`] raises.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint applying a definition to a variable runs to
///   the variable, and an endpoint stuck on native addition over a variable
///   stays the compound endpoint; skipping the unfolding or the spine changes
///   the read-back term. Under the holding stance the same definition stays the
///   endpoint's head.
/// - witness: `identity::tests::a_compound_endpoint_runs_through_a_definition`
/// - witness: `identity::tests::a_compound_endpoint_stands_for_what_it_returns`
/// - witness: `eval::tests::a_held_endpoint_stays_at_its_definition`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_values = machine.values.len()],
    ensures: |ret| ret.is_err()
        || (machine.tasks.len() == entry_tasks && machine.values.len() == entry_values.saturating_add(1_usize))
        || machine.tasks.len() > entry_tasks,
)]
fn resume_returned(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    (produced, stance): (DomainCompId, Endpoints),
) -> Result<(), EvalFault>
{
    if stance == Endpoints::Run
        && let DomainComp::Neutral { neutral, .. } = *domain
            .computation(produced)
            .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        let held = domain
            .neutral(neutral)
            .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
        let head = match held.unfolding() {
            Unfolding::Forced(Glued::Value(body)) => Some(Task::Supply(body)),
            Unfolding::Unforced(entry) => {
                machine
                    .definitions
                    .bodies()
                    .get(&entry)
                    .map(|&term| Task::Value {
                        term,
                        env: Machine::root_env(),
                    })
            },
            Unfolding::Rigid | Unfolding::Forced(Glued::Computation(_)) => None,
        };
        if let Some(head) = head {
            machine
                .tasks
                .push(if stance == machine.definitions.endpoints() {
                    Task::Returned
                }
                else {
                    Task::Running
                });
            let _answer = push_eliminations(machine, held.spine());
            machine.tasks.push(head);
            return Ok(());
        }
    }
    read_from(
        domain,
        machine,
        produced,
        SpinePosition::INNERMOST,
        Delivery::Value,
    )
}

/// Deliver `computation` as an endpoint, read through the first bind at or
/// past `from` in its spine over a call stuck at a rigid head.
///
/// An endpoint's computation is pure, so a bind over a call no unfolding
/// reaches is its continuation run with the call, held as an endpoint, for
/// the bound value: `wind(Loop(x))` sticks at `run n <- wind(x); return
/// S(n)` and reads as `S(wind(x))`. The reading takes the continuation only
/// when it returns, so an arm that cases on the call stays stuck at the
/// bind; a call a definition heads waits for the conversion to unfold it as
/// a recorded step. A continuation stuck at a bind of its own is read the same
/// way before it is judged, so a decoder's arm `run x <- el(a); run y <-
/// el(b); return (x => y)` reads as `⟨el(a)⟩ => ⟨el(b)⟩`. The kernel mirrors
/// the reading in its replay of an endpoint, by the same forced run, so it
/// records no decision of its own.
///
/// # Specification
/// - requires: nothing; a dangling id is refused.
/// - ensures: when [`read_through`] finds a bind at or past `from`, the bind's
///   continuation is queued over the call before it, beneath
///   [`Task::ReadThrough`], which delivers what it returns under the
///   eliminations past the bind or reads on from the next position; with no
///   such bind, `computation` is delivered at once: [`returned_value`] of it on
///   the value stack for [`Delivery::Value`], itself on the computation stack
///   for [`Delivery::Continuation`].
/// - provides: a held call's reading under the binds of a compound endpoint.
/// - fails: as [`read_through`] and [`returned_value`].
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as [`read_through`] and [`returned_value`] raise.
///
/// # Termination
/// - reason: no loop or recursion here; a failed reading re-enters through
///   [`Task::ReadContinued`] at a later position of the same spine, and a
///   continuation's reading through [`Task::ReadThrough`] at the first position
///   of the continuation's own spine.
/// - measure: the positions past `from`, which fall at every re-entry; each
///   continuation run spends the driver's fuel, which bounds the nesting.
///
/// # Adequacy
/// - hypothesis: L3 — a bind over a fixpoint stuck at a variable reads as its
///   arm's constructor over the call, and the kernel replays that endpoint
///   without a decision; a bind whose continuation cases on the call stays
///   whole, and skipping the reading leaves the first apart; two binds in turn,
///   each over a stuck call, read as the quote over both calls, and judging the
///   outer continuation before reading its own bind leaves the decode stuck.
/// - witness: `machine::tests::a_bind_over_a_stuck_call_reads_through_its_continuation`
/// - witness: `machine::tests::a_continuation_casing_on_a_stuck_call_stays_whole`
/// - witness: `machine::tests::a_continuation_stuck_at_its_own_bind_reads_through_both`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_values = machine.values.len(), entry_comps = machine.comps.len()],
    ensures: |ret| ret.is_err()
        || (machine.tasks.len() == entry_tasks && match delivery {
            Delivery::Value => machine.values.len() == entry_values.saturating_add(1_usize),
            Delivery::Continuation => machine.comps.len() == entry_comps.saturating_add(1_usize),
        })
        || machine.tasks.len() == entry_tasks.saturating_add(2_usize),
)]
fn read_from(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    computation: DomainCompId,
    from: SpinePosition,
    delivery: Delivery,
) -> Result<(), EvalFault>
{
    if let Some((bind, continuation, call)) = read_through(domain, computation, from)? {
        let closure = domain
            .comp_closure(continuation)
            .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
        let body = closure.body();
        let mut extended = closure.environment().clone();
        extended.extend(Zone::Intuitionistic, call);
        let env = machine.hold_env(extended);
        machine.tasks.push(Task::ReadThrough {
            computation,
            bind,
            delivery,
        });
        machine.tasks.push(Task::Body { body, env });
        return Ok(());
    }
    match delivery {
        Delivery::Value => {
            let value = returned_value(domain, computation)?;
            machine.values.push(value);
        },
        Delivery::Continuation => machine.comps.push(computation),
    }
    Ok(())
}

/// Go on past a held computation's bind at `bind` once its continuation
/// returned: `returned` under the eliminations past the bind, read again.
///
/// # Specification
/// - requires: `computation` is the neutral the bind sits in and `returned` a
///   returner.
/// - ensures: the eliminations past the bind queued over `returned`, beneath
///   the reading `delivery` names: [`Task::Returned`] for an endpoint's own
///   reading, with its unfolding under [`Endpoints::Run`]; [`Task::Reread`] for
///   a continuation's.
/// - provides: the step a read-through takes once a continuation returns.
/// - fails: [`EvalFault::MachineInvariant`] when `computation` is no neutral or
///   `bind` lies past its spine; [`DomainFault::Dangling`] for a node that does
///   not resolve.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Adequacy
/// - hypothesis: L3 — the outer bind of a decoder's arm goes on with what its
///   inner reading returned, and stopping at the inner bind leaves the decode
///   stuck.
/// - witness: `machine::tests::a_continuation_stuck_at_its_own_bind_reads_through_both`
#[spec(
    captures: [entry_tasks = machine.tasks.len(), entry_comps = machine.comps.len()],
    ensures: |ret| ret.is_err()
        || (machine.tasks.len() > entry_tasks && machine.comps.len() == entry_comps.saturating_add(1_usize)),
)]
fn continue_past(
    domain: &DomainArena,
    machine: &mut Machine<'_>,
    computation: DomainCompId,
    bind: SpinePosition,
    delivery: Delivery,
    returned: DomainCompId,
) -> Result<(), EvalFault>
{
    let DomainComp::Neutral { neutral, .. } = *domain
        .computation(computation)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    else {
        return Err(EvalFault::MachineInvariant);
    };
    let held = domain
        .neutral(neutral)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let past = held
        .spine()
        .get(bind.outward().0 ..)
        .ok_or(EvalFault::MachineInvariant)?;
    machine.tasks.push(match delivery {
        Delivery::Value => Task::Returned,
        Delivery::Continuation => Task::Reread,
    });
    let _answer = push_eliminations(machine, past);
    machine.comps.push(returned);
    Ok(())
}

/// The first bind at or past `from` in a stuck computation's spine, when the
/// computation is stuck at a variable or a constant with no body: the bind's
/// position, its continuation, and the call before it as a held endpoint.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when `computation` is neutral, its head — read
///   through returned heads to the call they wait on — is a variable or a
///   constant, rigid, and its spine holds a bind at or past `from`; the
///   position is the first such bind's, and the call is the neutral's head
///   under its spine before that position, delivered by [`returned_value`].
/// - provides: the bind [`read_from`] reads through.
/// - fails: [`DomainFault::Dangling`] when a node does not resolve.
/// - panics: none.
///
/// # Errors
/// [`EvalFault::Domain`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a bind over a fixpoint stuck at a rigid head is found
///   with the stuck call as its leaf, and a bind whose continuation then sticks
///   is passed over; finding no bind, or the call with its bind, leaves the
///   first endpoint apart.
/// - witness: `machine::tests::a_bind_over_a_stuck_call_reads_through_its_continuation`
/// - witness: `machine::tests::a_continuation_casing_on_a_stuck_call_stays_whole`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |found| found.is_none_or(|(bind, _, _)| bind >= from)))]
fn read_through(
    domain: &mut DomainArena,
    computation: DomainCompId,
    from: SpinePosition,
) -> Result<Option<(SpinePosition, CompClosureId, DomainValueId)>, EvalFault>
{
    let DomainComp::Neutral { neutral, .. } = *domain
        .computation(computation)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    else {
        return Ok(None);
    };
    let held = domain
        .neutral(neutral)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let (head, unfolding) = (held.head(), held.unfolding());
    let Some((bind, continuation)) =
        held.spine()
            .iter()
            .enumerate()
            .skip(from.0)
            .find_map(|(position, elimination)| match *elimination {
                Elimination::Bind(continuation) => Some((SpinePosition(position), continuation)),
                Elimination::DataCase(_)
                | Elimination::Split(_)
                | Elimination::Projection(_)
                | Elimination::Transport(_)
                | Elimination::ProductTransport(_)
                | Elimination::PathTransport { .. }
                | Elimination::Ride { .. }
                | Elimination::TelescopeTransport { .. }
                | Elimination::Apply(_)
                | Elimination::Force
                | Elimination::Case(_)
                | Elimination::ListFold { .. }
                | Elimination::StaticApply(_)
                | Elimination::Fixpoint(_) => None,
            })
    else {
        return Ok(None);
    };
    let prefix = Vec::from(
        held.spine()
            .get(.. bind.0)
            .ok_or(EvalFault::MachineInvariant)?,
    );
    let waits = match head {
        NeutralHead::Returned(inner) => {
            let Some(inner) = crate::rules::held_call(domain, inner)
                .map_err(|_fault| EvalFault::Domain(DomainFault::Dangling))?
            else {
                return Ok(None);
            };
            let node = domain
                .neutral(inner)
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
            (node.head(), node.unfolding())
        },
        NeutralHead::Variable { .. }
        | NeutralHead::Constant(_)
        | NeutralHead::Module(_)
        | NeutralHead::Hole { .. }
        | NeutralHead::Mark { .. } => (head, unfolding),
    };
    if !matches!(
        waits,
        (
            NeutralHead::Variable { .. } | NeutralHead::Constant(_),
            Unfolding::Rigid
        )
    ) {
        return Ok(None);
    }
    let call = domain
        .neutral_node(head, prefix, unfolding)
        .map_err(EvalFault::Domain)?;
    let call = domain.comp_neutral(call, CompTermFace::Reduced);
    Ok(Some((bind, continuation, returned_value(domain, call)?)))
}

/// The value a computation's weak head returns: a returner's value, or a
/// neutral standing for the stuck computation.
///
/// # Specification
/// - requires: nothing; a dangling id is refused.
/// - ensures: a returner's own value; for a stuck computation, a fresh
///   value-position neutral whose head is that computation and whose spine is
///   empty.
/// - provides: what a compound endpoint and a component transport stand for in
///   value position, so neither is erased when it does not return.
/// - fails: [`EvalFault::ReturnedNonReturner`] for a lambda or a fixpoint;
///   [`EvalFault::Domain`] for a dangling computation.
/// - panics: none.
///
/// # Errors
/// An `EvalFault`, as above.
///
/// # Adequacy
/// - hypothesis: L3 — a compound endpoint that returns reads back as its value
///   and one stuck on a variable reads back as the compound endpoint; erasing
///   either or mistaking a lambda for a returner changes the read-back term.
/// - witness: `identity::tests::a_compound_endpoint_stands_for_what_it_returns`
#[spec(ensures: |ret| match domain.computation(computation) {
    | Some(&DomainComp::Return { value, .. }) => ret == Ok(value),
    | Some(&DomainComp::Neutral { .. }) => ret.is_ok(),
    | Some(&(DomainComp::Lambda { .. } | DomainComp::Fixpoint { .. })) => ret == Err(EvalFault::ReturnedNonReturner),
    | None => ret == Err(EvalFault::Domain(DomainFault::Dangling)),
})]
fn returned_value(
    domain: &mut DomainArena,
    computation: DomainCompId,
) -> Result<DomainValueId, EvalFault>
{
    match *domain
        .computation(computation)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        DomainComp::Return { value, .. } => Ok(value),
        DomainComp::Neutral { .. } => {
            let stuck = domain
                .neutral_node(
                    NeutralHead::Returned(computation),
                    Vec::new(),
                    Unfolding::Rigid,
                )
                .map_err(EvalFault::Domain)?;
            domain
                .value_neutral(stuck, TermFace::Reduced)
                .map_err(EvalFault::Domain)
        },
        DomainComp::Lambda { .. } | DomainComp::Fixpoint { .. } => {
            Err(EvalFault::ReturnedNonReturner)
        },
    }
}

/// What a held endpoint returns once its computation runs on through the
/// definitions it is stuck on.
///
/// # Specification
/// - requires: `value` lives in `domain`.
/// - ensures: `Ok((Some(read), left))` when `value` is a held endpoint — a
///   neutral headed by a returned computation, with an empty spine — whose
///   computation, run under [`Endpoints::Run`], returns `read`, a value that is
///   no held endpoint; `Ok((None, left))` for any other value, and for an
///   endpoint whose run sticks again. `left` is `fuel` less one unit per task
///   the run popped.
/// - provides: the reading of a held endpoint no recorded decision can reach:
///   one standing as a leaf of a presented type's constructor term.
/// - fails: every variant of [`EvalFault`] the run raises,
///   [`EvalFault::OutOfFuel`] when `fuel` runs out first.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `loop(⟨ident(unloop(base))⟩)` over the presented circle
///   reads as `base` once the held `ident(unloop(base))` returns
///   `unloop(base)`, and the kernel's replay reads the same leaf by its own
///   evaluator; over a free circle the word stays apart from `base`.
/// - witness: `presented::tests::a_held_call_under_a_presented_constructor_reads_as_what_it_returns`
#[spec(ensures: |ret| match ret {
    Ok((read, left)) => u32::from(left) <= u32::from(fuel)
        && read.is_none_or(|read| domain.value(read).is_some()),
    Err(_) => true,
})]
pub fn run_held(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    fuel: Fuel,
    value: DomainValueId,
) -> Result<(Option<DomainValueId>, Fuel), EvalFault>
{
    let Some(computation) = held_endpoint(domain, value)?
    else {
        return Ok((None, fuel));
    };
    let mut machine = Machine::new(definitions.reading_endpoints(Endpoints::Run), fuel);
    machine.comps.push(computation);
    machine.tasks.push(Task::Returned);
    run(core, domain, &mut machine)?;
    let read = machine.pop_value()?;
    let read = if held_endpoint(domain, read)?.is_some() {
        None
    }
    else {
        Some(read)
    };
    Ok((read, machine.fuel))
}

/// The computation a held endpoint stands for: `value` when it is a neutral
/// headed by a returned computation, with an empty spine.
///
/// # Specification
/// - requires: nothing; a dangling id is refused.
/// - ensures: `Some(computation)` exactly when `value` is such a neutral over
///   `computation`; `None` for any other value.
/// - provides: the test [`run_held`] and a held operand's run
///   ([`words::appended`]) share.
/// - fails: [`EvalFault::Domain`] for a value or neutral the arena does not
///   hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`run_held`].
/// - witness: `presented::tests::a_held_call_under_a_presented_constructor_reads_as_what_it_returns`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |held| held.is_none_or(|computation| domain.computation(computation).is_some())))]
pub fn held_endpoint(
    domain: &DomainArena,
    value: DomainValueId,
) -> Result<Option<DomainCompId>, EvalFault>
{
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(value)
    else {
        return Ok(None);
    };
    let node = domain
        .neutral(neutral)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    Ok(match node.head() {
        NeutralHead::Returned(computation) if node.spine().is_empty() => Some(computation),
        NeutralHead::Variable { .. }
        | NeutralHead::Constant(_)
        | NeutralHead::Module(_)
        | NeutralHead::Hole { .. }
        | NeutralHead::Mark { .. }
        | NeutralHead::Returned(_) => None,
    })
}

/// Assemble a nominal value from its already evaluated fields.
///
/// # Specification
/// - requires: fields occupy the value stack suffix in signature order.
/// - ensures: a constructor retains those fields, its ordinal and captured
///   classifier.
/// - fails: missing source nodes, environments or stack operands.
/// - panics: none.
///
/// # Errors
/// Returns an evaluation invariant, domain or environment fault.
///
/// # Adequacy
/// - hypothesis: L3 — distinct fields stay ordered when a case applies its
///   branch.
/// - witness: `eval::tests::native_records_and_cases_compute`
#[spec(ensures: |ret| ret.is_err() || matches!(machine.values.last().and_then(|id| domain.value(*id)),Some(DomainValue::Constructor { .. }))) ]
fn step_constructor(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ValueId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(&Value::Constructor {
        datatype,
        tag,
        ref fields,
    }) = core.value(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let start = machine
        .values
        .len()
        .checked_sub(fields.len())
        .ok_or(EvalFault::MachineInvariant)?;
    let captured = machine.capture(env)?;
    let mut kept = capture_keeps_source(&captured);
    for (value, source) in machine
        .values
        .get(start ..)
        .ok_or(EvalFault::MachineInvariant)?
        .iter()
        .zip(fields)
    {
        kept = kept.and(denotes(domain, *value, *source));
    }
    let fields = domain.hold_fields(machine.values.drain(start ..));
    let datatype = domain.value_closure_node(crate::ValueBody::ValueType(datatype), captured);
    let value = domain.value_constructor(datatype, tag, fields, composite_face(kept, term));
    machine.values.push(value);
    Ok(())
}

/// Assemble a record without copying labels out of the source arena.
///
/// # Specification
/// - requires: evaluated fields occupy the stack suffix in source label order.
/// - ensures: the record retains that order and keeps its source only when
///   every field does.
/// - fails: missing source nodes, spans or stack operands.
/// - panics: none.
///
/// # Errors
/// Returns a dangling term, domain fault or machine invariant refusal.
///
/// # Adequacy
/// - hypothesis: L3 — selecting either of two unequal fields distinguishes
///   order.
/// - witness: `eval::tests::native_records_and_cases_compute`
#[spec(ensures: |ret| ret.is_err() || matches!(machine.values.last().and_then(|id| domain.value(*id)),Some(DomainValue::Record { .. }))) ]
fn step_record(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ValueId,
) -> Result<(), EvalFault>
{
    let Some(matched_native_node) = core.value(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let Value::Record(ref fields) = *matched_native_node
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let start = machine
        .values
        .len()
        .checked_sub(fields.len())
        .ok_or(EvalFault::MachineInvariant)?;
    let mut kept = SourceKept::Kept;
    for (value, source) in machine
        .values
        .get(start ..)
        .ok_or(EvalFault::MachineInvariant)?
        .iter()
        .zip(fields.values())
    {
        kept = kept.and(denotes(domain, *value, *source));
    }
    let fields = domain.hold_fields(machine.values.drain(start ..));
    let value = domain
        .value_record(term, fields, composite_face(kept, term))
        .map_err(EvalFault::Domain)?;
    machine.values.push(value);
    Ok(())
}

/// Select a nominal branch, or suspend the complete case on a neutral head.
///
/// # Specification
/// - requires: the scrutinee is the top value operand.
/// - ensures: a constructor selects exactly its ordinal and supplies fields in
///   order; a neutral retains the whole case and its ambient capture.
/// - fails: a missing branch, a non-constructor or malformed machine state.
/// - panics: none.
///
/// # Errors
/// Returns the typed constructor, domain, term or machine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — distinct fields, unknown tags and reapplication
///   distinguish selection.
/// - witness: `eval::tests::native_records_and_cases_compute`
/// - witness: `eval::tests::native_cases_reapply_when_head_unfolds`
#[spec(ensures: |ret| ret != Err(EvalFault::OutOfFuel))]
fn step_data_case(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(matched_native_node) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let Computation::DataCase { ref branches, .. } = *matched_native_node
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let scrutinee = machine.pop_value()?;
    match *domain
        .value(scrutinee)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        DomainValue::Constructor { tag, fields, .. } => {
            let branch = *branches
                .get(usize::from(tag))
                .ok_or(EvalFault::UnknownConstructor { tag })?;
            for field in domain
                .fields(fields)
                .map_err(EvalFault::Domain)?
                .iter()
                .rev()
            {
                machine.tasks.push(Task::Apply);
                machine.tasks.push(Task::Supply(*field));
            }
            machine.tasks.push(Task::Comp { term: branch, env });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let closure = domain.comp_closure_node(term, machine.capture(env)?);
            let grown = extend_spine(domain, neutral, Elimination::DataCase(closure))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::Record { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Tuple { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::CasedNonConstructor),
    }
}

/// Bind a tuple's components into a split's body, or suspend the whole split
/// on a neutral head.
///
/// # Specification
/// - requires: the scrutinee is the top value operand.
/// - ensures: a tuple of the split's arity extends the environment with each
///   component in order, the last innermost, and enters the body; a neutral
///   retains the whole split and its ambient capture.
/// - fails: a tuple of another arity, a non-tuple, or malformed machine state.
/// - panics: none.
///
/// # Errors
/// Returns the typed tuple, domain, term or machine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a three-component split reading each component, an empty
///   split, a neutral scrutinee, an arity mismatch and a non-tuple distinguish
///   binding order, suspension and both refusals.
/// - witness: `eval::tests::a_split_binds_each_component_in_order`
#[spec(ensures: |ret| ret != Err(EvalFault::OutOfFuel))]
fn step_split(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let Some(&Computation::Split { arity, body, .. }) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let scrutinee = machine.pop_value()?;
    match *domain
        .value(scrutinee)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        DomainValue::Tuple { fields, .. } => {
            let components = domain.fields(fields).map_err(EvalFault::Domain)?.to_vec();
            if components.len() != usize::from(arity) {
                return Err(EvalFault::SplitArity);
            }
            let mut extended = env;
            for component in components {
                extended = machine.extended(extended, Zone::Intuitionistic, component)?;
            }
            machine.tasks.push(Task::Comp {
                term: body,
                env: extended,
            });
            Ok(())
        },
        DomainValue::Neutral { neutral, .. } => {
            let closure = domain.comp_closure_node(term, machine.capture(env)?);
            let grown = extend_spine(domain, neutral, Elimination::Split(closure))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathCertificate { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Here { .. }
        | DomainValue::Flow { .. }
        | DomainValue::Literal { .. }
        | DomainValue::ListNil { .. }
        | DomainValue::ListCons { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. }
        | DomainValue::Code { .. }
        | DomainValue::StaticLambda { .. } => Err(EvalFault::SplitNonTuple),
    }
}

/// Select a record's field by its label or a tuple's component by its
/// position, or suspend the projection on a neutral.
///
/// # Specification
/// - requires: the projected operand is the top value.
/// - ensures: returns the selected field or component, never a positional
///   substitute for a missing label or position.
/// - fails: absent labels or components, a record projection of anything but a
///   record, a tuple projection of anything but a tuple, dangling domains or
///   malformed state.
/// - panics: none.
///
/// # Errors
/// Returns the typed record, tuple, domain, term or machine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — unequal fields and an absent label distinguish exact
///   lookup; each component of a three-component tuple and a component past its
///   last distinguish positional lookup.
/// - witness: `eval::tests::native_records_and_cases_compute`
/// - witness: `eval::tests::a_tuple_projection_reads_each_component`
#[spec(ensures: |ret| ret != Err(EvalFault::OutOfFuel))]
fn step_projection(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    term: ComputationId,
) -> Result<(), EvalFault>
{
    let Some(matched_native_node) = core.computation(term)
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let projected = machine.pop_value()?;
    let operand = *domain
        .value(projected)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
    let (fields, position) = match (matched_native_node, operand) {
        (
            &Computation::RecordProjection(_, ref label),
            DomainValue::Record { source, fields, .. },
        ) => {
            let Some(matched_native_node) = core.value(source)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let Value::Record(ref source_fields) = *matched_native_node
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let position = source_fields
                .keys()
                .position(|field| field == label)
                .ok_or(EvalFault::AbsentRecordField)?;
            (fields, position)
        },
        (&Computation::TupleProjection(_, component), DomainValue::Tuple { fields, .. }) => {
            (fields, usize::from(component))
        },
        (
            &(Computation::RecordProjection(..) | Computation::TupleProjection(..)),
            DomainValue::Neutral { neutral, .. },
        ) => {
            let grown = extend_spine(domain, neutral, Elimination::Projection(term))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            return Ok(());
        },
        (&Computation::RecordProjection(..), _) => return Err(EvalFault::ProjectedNonRecord),
        (&Computation::TupleProjection(..), _) => return Err(EvalFault::ProjectedNonTuple),
        _ => return Err(EvalFault::DanglingTerm),
    };
    let value = *domain
        .fields(fields)
        .map_err(EvalFault::Domain)?
        .get(position)
        .ok_or(match *matched_native_node {
            Computation::TupleProjection(..) => EvalFault::AbsentTupleComponent,
            Computation::Primitive { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Lambda(_)
            | Computation::Fixpoint { .. }
            | Computation::Application(..)
            | Computation::Return(_)
            | Computation::Bind(..)
            | Computation::Ascribe { .. }
            | Computation::Force(_)
            | Computation::Case { .. }
            | Computation::Split { .. }
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::Hole(_)
            | Computation::Mark { .. }
            | Computation::ListFold { .. }
            | Computation::Perform { .. }
            | Computation::Handle { .. }
            | Computation::Exercise { .. }
            | Computation::Scope { .. }
            | Computation::Resume(..)
            | Computation::Reset(_)
            | Computation::Shift(_)
            | Computation::With(..)
            | Computation::Project(..)
            | Computation::Session(_)
            | Computation::Memory(_) => EvalFault::MachineInvariant,
        })?;
    machine
        .comps
        .push(domain.comp_return(value, CompTermFace::Reduced));
    Ok(())
}

#[cfg(test)]
mod tests;
