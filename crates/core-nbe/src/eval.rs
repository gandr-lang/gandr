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

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionEntry;
use gandr_core_term::DefinitionHeight;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ScopeId;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::Side;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::closure::Environment;
use crate::closure::EnvironmentDepth;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::LiftTarget;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::free::CoreTerm;
use crate::free::Free;

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
    /// Runtime-native arithmetic is outside the certificate normalizer.
    NativePrimitive(gandr_core_term::primitive::Primitive),
    /// Transport met neither a native path nor a neutral path operand.
    TransportedNonPath,
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
    /// Record projection received a non-record, non-neutral value.
    ProjectedNonRecord,
    /// The exact projection label is absent from the record.
    AbsentRecordField,
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
        Ok(Self { chain, bodies })
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
/// site ends up asking the root scope by accident.
#[derive(Clone, Copy, Debug)]
pub struct Definitions<'run>
{
    /// Every definition's body, height and lowering.
    chain: &'run LoweredChain,
    /// Which definitions are manifest in which scope.
    environment: &'run DefinitionalEnvironment,
    /// The scope this run reads from.
    scope: ScopeId,
}

impl<'run> Definitions<'run>
{
    /// Read `chain` from `scope` of `environment`.
    ///
    /// # Specification
    /// - requires: `environment` was built over `chain`; every scope id is
    ///   admissible, and an unknown scope reads as unfolding nothing.
    /// - ensures: the three travel together thereafter, so no later call can
    ///   pair a chain with another run's scope.
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
            && ret.scope == scope,
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
        }
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
    ///   when the chain holds a body for `constant` **and** this scope reads it
    ///   as manifest; [`Unfolding::Rigid`] otherwise, which covers an axiom, a
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
    /// - hypothesis: L3 — the decision surfaces are the chain lookup, the
    ///   transparency lookup and the unknown-scope degradation, separated by a
    ///   manifest definition, the same definition sealed in an enclosing scope,
    ///   an admission position with no body, and a scope that was never opened.
    /// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
    /// - witness: `eval::tests::a_sealed_definition_is_rigid`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match self.chain.chain().entry(constant) {
        | Some(entry) => {
            match self.environment.transparency(self.scope, constant, entry.declared()) {
                | Ok(Transparency::Manifest) => ret == Unfolding::Unforced(entry.body()),
                | Ok(Transparency::Opaque) | Err(_) => ret == Unfolding::Rigid,
            }
        },
        | None => ret == Unfolding::Rigid,
    })]
    pub fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Unfolding
    {
        let Some(entry) = self.chain.chain().entry(constant)
        else {
            return Unfolding::Rigid;
        };
        let stance = self
            .environment
            .transparency(self.scope, constant, entry.declared());
        match stance {
            | Ok(Transparency::Manifest) => Unfolding::Unforced(entry.body()),
            | Ok(Transparency::Opaque) | Err(_) => Unfolding::Rigid,
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
    /// Select the exact source label from an evaluated record.
    RecordProjection(ComputationId),
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
    /// Assemble a pair from the two values its own tasks produced.
    Pair
    {
        /// The source node, which supplies both the children to compare faces
        /// against and the face to keep when they match.
        term: ValueId,
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
        /// The left branch's source node.
        on_left: ComputationId,
        /// The right branch's source node.
        on_right: ComputationId,
        /// The environment the branches are read in.
        env: EnvId,
    },
    /// Push a domain value the machine already holds onto the value stack:
    /// the operand a re-applied spine's application frame consumes.
    Supply(DomainValueId),
    /// Sequence into an already-captured continuation once the bound
    /// computation has a weak head: a spine's bind, re-applied.
    BindClosure(CompClosureId),
    /// Choose between two already-captured branches once the scrutinee has a
    /// value: a spine's case, re-applied.
    CaseClosures
    {
        /// The left branch.
        on_left: CompClosureId,
        /// The right branch.
        on_right: CompClosureId,
    },
    /// Remember the weak head on the stack as the evaluation of a pending
    /// configuration.
    Remember(PendingId),
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
                    && self.sharing.legs.get(&term).zip(self.envs.get(env.0)).is_some_and(|(free, environment)| {
                        self.sharing.remembered.iter().any(|(configuration, head)| configuration.term == term
                            && *head == remembered && configuration.entries.iter().copied().map(Some).eq(
            free.intuitionistic().counts().iter().map(|index| environment.lookup(Zone::Intuitionistic, *index))
                .chain(free.linear().counts().iter().map(|index| environment.lookup(Zone::Linear, *index)))))
                    }),
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
            entry_configuration = self.sharing.pending.get(pending.0).and_then(Option::as_ref)
                .map(|configuration| (configuration.term, configuration.entries.len(), configuration.entries.first().copied(), configuration.entries.last().copied()))],
        ensures: |ret| self.sharing.pending.len() == entry_pending
            && self.sharing.pending.get(pending.0).is_none_or(Option::is_none)
            && self.values.len() == entry_values && self.comps.len() == entry_comps
            && self.values.last().copied() == entry_value && self.comps.last().copied() == entry_comp
            && {
                let produced = entry_configuration.and_then(|configuration| match configuration.0 {
                    CoreTerm::Value(_) => entry_value.map(Glued::Value),
                    CoreTerm::Computation(_) => entry_comp.map(Glued::Computation),
                });
                match produced {
                    None => ret == Err(EvalFault::MachineInvariant) && self.sharing.remembered.len() == entry_remembered,
                    Some(produced) => ret.is_ok()
                        && (self.sharing.remembered.len() == entry_remembered || self.sharing.remembered.len() == entry_remembered.saturating_add(1_usize))
                        && self.sharing.remembered.iter().any(|(configuration, head)| *head == produced
                            && Some((configuration.term, configuration.entries.len(), configuration.entries.first().copied(), configuration.entries.last().copied())) == entry_configuration),
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
            | CoreTerm::Value(_) => self.values.last().copied().map(Glued::Value),
            | CoreTerm::Computation(_) => self.comps.last().copied().map(Glued::Computation),
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
            | (Self::Kept, Self::Kept) => Self::Kept,
            | (Self::Kept, Self::Lost) | (Self::Lost, Self::Kept | Self::Lost) => Self::Lost,
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
        | SourceKept::Kept => TermFace::Source(term),
        | SourceKept::Lost => TermFace::Reduced,
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
        | SourceKept::Kept => CompTermFace::Source(term),
        | SourceKept::Lost => CompTermFace::Reduced,
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
        | CoreTerm::Value(term) => Task::Value { term, env },
        | CoreTerm::Computation(term) => Task::Comp { term, env },
    });
    run(core, domain, &mut machine)?;
    let produced = match root {
        | CoreTerm::Value(_) => machine.pop_value().map(Glued::Value),
        | CoreTerm::Computation(_) => machine.pop_comp().map(Glued::Computation),
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
        requires: matches!(spine.first(), Some(Elimination::DataCase(_) | Elimination::RecordProjection(_) | Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::Force | Elimination::Case { .. } | Elimination::StaticApply(_))),
        ensures: |ret| ret.machine.values.as_slice() == [head] && ret.machine.comps.is_empty()
            && ret.machine.fuel.0 == 0_u32 && {
                let mut tasks = ret.machine.tasks.iter().rev();
                let mut answer = Answer::Value;
                let ordered = spine.iter().all(|elimination| match *elimination {
                    Elimination::DataCase(closure) => { answer = Answer::Computation; matches!(tasks.next(),Some(Task::DataCaseClosure(held)) if *held == closure) },
                    Elimination::RecordProjection(term) => { answer = Answer::Computation; matches!(tasks.next(),Some(Task::RecordProjection(held)) if *held == term) },
                    Elimination::Transport(value) => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(held)) if *held == value) && matches!(tasks.next(), Some(Task::Transport)) },
                    Elimination::ProductTransport(path) => { answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::ProductTransport(held)) if *held == path) },
                    Elimination::StaticApply(argument) => matches!(tasks.next(), Some(Task::Supply(value)) if *value == argument)
                        && matches!(tasks.next(), Some(Task::StaticApply)),
                    Elimination::Apply(argument) => {
                        answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::Supply(value)) if *value == argument) && matches!(tasks.next(), Some(Task::Apply))
                    },
                    Elimination::Force => { answer = Answer::Computation; matches!(tasks.next(), Some(Task::Force)) },
                    Elimination::Bind(body) => { answer = Answer::Computation; matches!(tasks.next(), Some(Task::BindClosure(held)) if *held == body) },
                    Elimination::Case { on_left, on_right } => {
                        answer = Answer::Computation;
                        matches!(tasks.next(), Some(Task::CaseClosures { on_left: left, on_right: right }) if *left == on_left && *right == on_right)
                    },
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
        let mut answer = Answer::Value;
        for elimination in spine.iter().rev() {
            match *elimination {
                | Elimination::DataCase(closure) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::DataCaseClosure(closure));
                },
                | Elimination::RecordProjection(term) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::RecordProjection(term));
                },
                | Elimination::Transport(value) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::Transport);
                    machine.tasks.push(Task::Supply(value));
                },
                | Elimination::ProductTransport(path) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::ProductTransport(path));
                },
                | Elimination::StaticApply(argument) => {
                    machine.tasks.push(Task::StaticApply);
                    machine.tasks.push(Task::Supply(argument));
                },
                | Elimination::Apply(argument) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::Apply);
                    machine.tasks.push(Task::Supply(argument));
                },
                | Elimination::Force => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::Force);
                },
                | Elimination::Bind(body) => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::BindClosure(body));
                },
                | Elimination::Case { on_left, on_right } => {
                    answer = Answer::Computation;
                    machine.tasks.push(Task::CaseClosures { on_left, on_right });
                },
            }
        }
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
                    }),
                    _ => false,
                }),
        ),
    )]
    pub(crate) fn enter(
        definitions: Definitions<'run>,
        domain: &DomainArena,
        closure: CompClosureId,
        bound: Bound,
    ) -> Result<Self, EvalFault>
    {
        let held = domain
            .comp_closure(closure)
            .ok_or(EvalFault::Domain(DomainFault::Dangling))?;
        let mut environment = held.environment().clone();
        if let Bound::Variable(variable) = bound {
            environment.extend(Zone::Intuitionistic, variable);
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
            | SliceEnd::Spent => Ok((Progress::Paused, spent)),
            | SliceEnd::Drained => {
                let answer = match self.answer {
                    | Answer::Value => Glued::Value(self.machine.pop_value()?),
                    | Answer::Computation => Glued::Computation(self.machine.pop_comp()?),
                };
                Ok((Progress::Finished(answer), spent))
            },
        }
    }
}

/// What a closure is entered with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bound
{
    /// Nothing: the closure's own environment, as forcing a thunk reads it.
    Nothing,
    /// A variable bound innermost, as opening a binder reads it.
    Variable(DomainValueId),
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
            Task::DataCase { .. } | Task::DataCaseClosure(_) | Task::RecordProjection(_) | Task::Force | Task::Apply | Task::StaticApply | Task::Bind { .. } | Task::Case { .. }
            | Task::BindClosure(_) | Task::CaseClosures { .. } | Task::Transport | Task::ProductTransport(_) => machine.tasks.len() >= entry_tasks,
            Task::Value { .. } => machine.comps.len() == entry_comps
                && ((machine.values.len() == entry_values.saturating_add(1_usize) && machine.tasks.len() >= entry_tasks)
                    || (machine.values.len() == entry_values && machine.tasks.len() > entry_tasks)),
            Task::Body { body: crate::closure::CompBody::Source(_), .. } | Task::Comp { .. } => machine.values.len() == entry_values
                && ((machine.comps.len() == entry_comps.saturating_add(1_usize) && machine.tasks.len() >= entry_tasks)
                    || (machine.comps.len() == entry_comps && machine.tasks.len() > entry_tasks)),
            Task::Body { body: crate::closure::CompBody::Pair(first), env } => machine.values.len() == entry_values
                && machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps.saturating_add(1)
                && matches!(machine.comps.last().and_then(|&id| domain.computation(id)), Some(&DomainComp::Return { value, .. })
                    if matches!(domain.value(value), Some(&DomainValue::Pair { first: held, second, .. })
                        if held == first && machine.env(env).is_ok_and(|environment| environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) == Some(second)))),
            Task::Body { body: crate::closure::CompBody::TransportPair { path, value }, .. } => machine.comps.len() == entry_comps
                && machine.values.len() == entry_values.saturating_add(2) && machine.values.ends_with(&[path, value])
                && machine.tasks.len() == entry_tasks.saturating_add(2)
                && matches!(machine.tasks.get(entry_tasks..), Some([Task::BindClosure(_), Task::Transport])),
            Task::PathProduct(_) => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && entry_values.checked_sub(1) == Some(machine.values.len())
                && matches!(machine.values.last().and_then(|&id| domain.value(id)), Some(&DomainValue::PathProduct { first, second, .. })
                    if Some(first) == entry_first && Some(second) == entry_value),
            Task::Pair { .. } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && entry_values.checked_sub(1_usize) == Some(machine.values.len())
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::Pair { first, second, .. }) if Some(*first) == entry_first && Some(*second) == entry_value),
            Task::Inject { term } => machine.tasks.len() == entry_tasks && machine.comps.len() == entry_comps
                && machine.values.len() == entry_values
                && matches!(machine.values.last().and_then(|value| domain.value(*value)),
                    Some(DomainValue::Injection { side, body, .. }) if Some(*body) == entry_value
                        && matches!(core.value(term), Some(Value::Injection(source_side, _)) if source_side == side)),
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
        | Task::Constructor { term, env } => step_constructor(core, domain, machine, term, env),
        | Task::Record(term) => step_record(core, domain, machine, term),
        | Task::DataCase { term, env } => step_data_case(core, domain, machine, term, env),
        | Task::RecordProjection(term) => step_record_projection(core, domain, machine, term),
        | Task::DataCaseClosure(closure) => {
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
        | Task::Value { term, env } => {
            let recalled = machine.recall(CoreTerm::Value(term), env)?;
            match recalled {
                | Recall::Remembered(Glued::Value(remembered)) => {
                    machine.values.push(remembered);
                    Ok(())
                },
                | Recall::Remembered(Glued::Computation(_)) => Err(EvalFault::MachineInvariant),
                | Recall::Unshared | Recall::Pending => {
                    step_value(core, domain, machine, term, env)
                },
            }
        },
        | Task::Body {
            body: crate::closure::CompBody::Source(term),
            env,
        }
        | Task::Comp { term, env } => {
            let recalled = machine.recall(CoreTerm::Computation(term), env)?;
            match recalled {
                | Recall::Remembered(Glued::Computation(remembered)) => {
                    machine.comps.push(remembered);
                    Ok(())
                },
                | Recall::Remembered(Glued::Value(_)) => Err(EvalFault::MachineInvariant),
                | Recall::Unshared | Recall::Pending => step_comp(core, domain, machine, term, env),
            }
        },
        | Task::Body { body, env } => {
            let bound = machine
                .env(env)?
                .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
                .ok_or(EvalFault::MachineInvariant)?;
            match body {
                | crate::closure::CompBody::Source(_) => Err(EvalFault::MachineInvariant),
                | crate::closure::CompBody::Pair(first) => {
                    let pair = domain.value_pair(first, bound, TermFace::Reduced);
                    machine
                        .comps
                        .push(domain.comp_return(pair, CompTermFace::Reduced));
                    Ok(())
                },
                | crate::closure::CompBody::TransportPair { path, value } => {
                    let continuation =
                        domain.transport_continuation(crate::closure::CompBody::Pair(bound));
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::Transport);
                    machine.values.extend([path, value]);
                    Ok(())
                },
            }
        },
        | Task::PathProduct(term) => {
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
        | Task::Transport => step_transport(core, domain, machine),
        | Task::ProductTransport(path) => {
            let value = machine.pop_value()?;
            machine.values.extend([path, value]);
            step_transport(core, domain, machine)
        },
        | Task::Pair { term } => {
            let second = machine.pop_value()?;
            let first = machine.pop_value()?;
            let Some(&Value::Pair(left, right)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let kept = denotes(domain, first, left).and(denotes(domain, second, right));
            let face = composite_face(kept, term);
            machine.values.push(domain.value_pair(first, second, face));
            Ok(())
        },
        | Task::Inject { term } => {
            let body = machine.pop_value()?;
            let Some(&Value::Injection(side, source)) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(denotes(domain, body, source), term);
            machine
                .values
                .push(domain.value_injection(side, body, face));
            Ok(())
        },
        | Task::Lift { term, target } => {
            let body = machine.pop_value()?;
            let Some(&Value::Lift { body: source, .. }) = core.value(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_face(denotes(domain, body, source), term);
            machine.values.push(domain.value_lift(target, body, face));
            Ok(())
        },
        | Task::Return { term } => {
            let produced = machine.pop_value()?;
            let Some(&Computation::Return(source)) = core.computation(term)
            else {
                return Err(EvalFault::DanglingTerm);
            };
            let face = composite_comp_face(denotes(domain, produced, source), term);
            machine.comps.push(domain.comp_return(produced, face));
            Ok(())
        },
        | Task::Force => step_force(domain, machine),
        | Task::Apply => step_apply(domain, machine),
        | Task::StaticApply => step_static_apply(core, domain, machine),
        | Task::Bind { body, env } => step_bind(domain, machine, body, env),
        | Task::Case {
            on_left,
            on_right,
            env,
        } => step_case(domain, machine, on_left, on_right, env),
        | Task::Supply(value) => {
            machine.values.push(value);
            Ok(())
        },
        | Task::BindClosure(body) => step_bind_closure(domain, machine, body),
        | Task::CaseClosures { on_left, on_right } => {
            step_case_closures(domain, machine, on_left, on_right)
        },
        | Task::Remember(pending) => machine.remember(pending),
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
        | Value::Constructor { ref fields, .. } => {
            machine.tasks.push(Task::Constructor { term, env });
            machine.tasks.extend(
                fields
                    .iter()
                    .rev()
                    .map(|field| Task::Value { term: *field, env }),
            );
            Ok(())
        },
        | Value::Record(ref fields) => {
            machine.tasks.push(Task::Record(term));
            machine.tasks.extend(
                fields
                    .values()
                    .rev()
                    .map(|field| Task::Value { term: *field, env }),
            );
            Ok(())
        },
        | Value::PathRefl(_) | Value::PathEquiv { .. } => {
            machine
                .values
                .push(domain.value_path_certificate(term, TermFace::Source(term)));
            Ok(())
        },
        | Value::PathProduct(first, second) => {
            machine.tasks.push(Task::PathProduct(term));
            machine.tasks.push(Task::Value { term: second, env });
            machine.tasks.push(Task::Value { term: first, env });
            Ok(())
        },
        | Value::Variable { zone, index } => {
            let environment = machine.env(env)?;
            let bound = environment
                .lookup(zone, index)
                .ok_or(EvalFault::UnboundVariable { zone, index })?;
            machine.values.push(bound);
            Ok(())
        },
        | Value::Constant(constant) => {
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
        | Value::Unit => {
            machine
                .values
                .push(domain.value_unit(TermFace::Source(term)));
            Ok(())
        },
        | Value::Literal(ref payload) => {
            machine
                .values
                .push(domain.value_literal(term, payload, TermFace::Source(term)));
            Ok(())
        },
        | Value::Pair(first, second) => {
            machine.tasks.push(Task::Pair { term });
            machine.tasks.push(Task::Value { term: second, env });
            machine.tasks.push(Task::Value { term: first, env });
            Ok(())
        },
        | Value::Injection(_, body) => {
            machine.tasks.push(Task::Inject { term });
            machine.tasks.push(Task::Value { term: body, env });
            Ok(())
        },
        | Value::Thunk(body) | Value::Primitive { body, .. } => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.comp_closure_node(body, captured);
            let face = composite_face(closed, term);
            machine.values.push(domain.value_thunk(closure, face));
            Ok(())
        },
        | Value::Lift { ref target, body } => {
            let target = domain.hold_level(target.clone());
            machine.tasks.push(Task::Lift { term, target });
            machine.tasks.push(Task::Value { term: body, env });
            Ok(())
        },
        // A quote is suspended whole over the environment its type reads: a
        // type has no weak head, so the codes inside it are evaluated where a
        // readback or a comparison reaches them.
        | Value::Quote(_) | Value::QuoteComputation(_) => {
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
        | Value::StaticLambda(_) => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.value_closure_node(crate::ValueBody::Source(term), captured);
            let face = composite_face(closed, term);
            machine
                .values
                .push(domain.value_static_lambda(closure, face));
            Ok(())
        },
        | Value::StaticApplication(head, argument) => {
            machine.tasks.push(Task::StaticApply);
            machine.tasks.push(Task::Value {
                term: argument,
                env,
            });
            machine.tasks.push(Task::Value { term: head, env });
            Ok(())
        },
    }
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
        | Computation::Primitive { primitive, .. } => Err(EvalFault::NativePrimitive(primitive)),
        | Computation::DataCase { scrutinee, .. } => {
            machine.tasks.push(Task::DataCase { term, env });
            machine.tasks.push(Task::Value {
                term: scrutinee,
                env,
            });
            Ok(())
        },
        | Computation::RecordProjection(record, _) => {
            machine.tasks.push(Task::RecordProjection(term));
            machine.tasks.push(Task::Value { term: record, env });
            Ok(())
        },
        | Computation::Transport(path, value) => {
            machine.tasks.push(Task::Transport);
            machine.tasks.push(Task::Value { term: value, env });
            machine.tasks.push(Task::Value { term: path, env });
            Ok(())
        },
        | Computation::Lambda(body) => {
            let captured = machine.capture(env)?;
            let closed = capture_keeps_source(&captured);
            let closure = domain.comp_closure_node(body, captured);
            let face = composite_comp_face(closed, term);
            machine.comps.push(domain.comp_lambda(closure, face));
            Ok(())
        },
        | Computation::Return(value) => {
            machine.tasks.push(Task::Return { term });
            machine.tasks.push(Task::Value { term: value, env });
            Ok(())
        },
        | Computation::Application(head, argument) => {
            machine.tasks.push(Task::Apply);
            machine.tasks.push(Task::Comp { term: head, env });
            machine.tasks.push(Task::Value {
                term: argument,
                env,
            });
            Ok(())
        },
        | Computation::Force(value) => {
            machine.tasks.push(Task::Force);
            machine.tasks.push(Task::Value { term: value, env });
            Ok(())
        },
        | Computation::Bind(bound, body) => {
            machine.tasks.push(Task::Bind { body, env });
            machine.tasks.push(Task::Comp { term: bound, env });
            Ok(())
        },
        | Computation::Case {
            scrutinee,
            on_left,
            on_right,
        } => {
            machine.tasks.push(Task::Case {
                on_left,
                on_right,
                env,
            });
            machine.tasks.push(Task::Value {
                term: scrutinee,
                env,
            });
            Ok(())
        },
    }
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
        | DomainValue::Thunk { body, .. } => {
            let Some(closure) = domain.comp_closure(body)
            else {
                return Err(EvalFault::Domain(DomainFault::Dangling));
            };
            let term = closure.body();
            let env = machine.hold_env(closure.environment().clone());
            machine.tasks.push(Task::Body { body: term, env });
            Ok(())
        },
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Force)?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
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
///   application.
/// - provides: the β rule and its stuck case, which are one arm apart. The
///   clause states the consumed argument and head results and the two
///   admissible outcomes — one task entering the closure, or one computation
///   result standing for the grown neutral; that the stuck outcome's spine grew
///   by exactly one application is a judgement over the produced graph, and the
///   witnesses below carry it.
/// - fails: [`EvalFault::MachineInvariant`] for a missing head or argument,
///   [`EvalFault::Domain`] for a missing node, and
///   [`EvalFault::AppliedNonFunction`] when the head is a returner.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   applying a lambda, a neutral and a returner.
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
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_comps == 0_usize || entry_values == 0_usize))
        && (ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize)
                && machine.comps.len() == entry_comps.saturating_sub(1_usize))
                || (machine.comps.len() == entry_comps
                    && machine.tasks.len() == entry_tasks)))),
)]
fn step_apply(
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
        | DomainComp::Lambda { body, .. } => {
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
        | DomainComp::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Apply(argument))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainComp::Return { .. } => Err(EvalFault::AppliedNonFunction),
    }
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
        | DomainValue::StaticLambda { lambda, .. } => {
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
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::StaticApply(argument))?;
            let stood = domain
                .value_neutral(grown, TermFace::Reduced)
                .map_err(EvalFault::Domain)?;
            machine.values.push(stood);
            Ok(())
        },
        | DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
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
///   a neutral grows its spine by one bind, capturing the body as a closure.
/// - provides: the sequencing rule and its stuck case. The clause states the
///   consumed computation result and the two admissible outcomes — one task
///   carrying the body, or one computation result standing for the grown
///   neutral; that the returned value is bound in the body's environment, and
///   that the stuck outcome's spine grew by exactly one bind, are judgements
///   over the produced graph, and the witnesses below carry them.
/// - fails: [`EvalFault::BoundNonReturner`] when the bound computation is a
///   lambda.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   binding a returner, a neutral and a lambda.
/// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
#[spec(
    requires: [!machine.comps.is_empty(), env.0 < machine.envs.len()],
    captures: [
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.comps.len() == entry_comps.saturating_sub(1_usize)
            && machine.tasks.len() == entry_tasks.saturating_add(1_usize))
        || (machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks),
)]
fn step_bind(
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
        | DomainComp::Return { value, .. } => {
            let env = machine.extended(env, Zone::Intuitionistic, value)?;
            machine.tasks.push(Task::Comp { term: body, env });
            Ok(())
        },
        | DomainComp::Neutral { neutral, .. } => {
            let captured = machine.capture(env)?;
            let closure = domain.comp_closure_node(body, captured);
            let grown = extend_spine(domain, neutral, Elimination::Bind(closure))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainComp::Lambda { .. } => Err(EvalFault::BoundNonReturner),
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
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    on_left: ComputationId,
    on_right: ComputationId,
    env: EnvId,
) -> Result<(), EvalFault>
{
    let scrutinee = machine.pop_value()?;
    let Some(node) = domain.value(scrutinee)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        | DomainValue::Injection { side, body, .. } => {
            let term = match side {
                | Side::Left => on_left,
                | Side::Right => on_right,
            };
            let env = machine.extended(env, Zone::Intuitionistic, body)?;
            machine.tasks.push(Task::Comp { term, env });
            Ok(())
        },
        | DomainValue::Neutral { neutral, .. } => {
            let captured = machine.capture(env)?;
            let left = domain.comp_closure_node(on_left, captured.clone());
            let right = domain.comp_closure_node(on_right, captured);
            let grown = extend_spine(domain, neutral, Elimination::Case {
                on_left: left,
                on_right: right,
            })?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
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
///   same bind, the closure reused rather than re-captured.
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
#[spec(
    captures: [entry_values = machine.values.len(), entry_comps = machine.comps.len(), entry_tasks = machine.tasks.len()],
    ensures: |ret| ((ret == Err(EvalFault::MachineInvariant)) == (entry_comps == 0_usize))
        && machine.values.len() == entry_values
        && (ret.is_err()
            || (machine.comps.len() == entry_comps.saturating_sub(1_usize) && machine.tasks.len() == entry_tasks.saturating_add(1_usize))
            || (machine.comps.len() == entry_comps && machine.tasks.len() == entry_tasks)),
)]
fn step_bind_closure(
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
        | DomainComp::Return { value, .. } => {
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
        | DomainComp::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Bind(body))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainComp::Lambda { .. } => Err(EvalFault::BoundNonReturner),
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
fn step_case_closures(
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    on_left: CompClosureId,
    on_right: CompClosureId,
) -> Result<(), EvalFault>
{
    let scrutinee = machine.pop_value()?;
    let Some(node) = domain.value(scrutinee)
    else {
        return Err(EvalFault::Domain(DomainFault::Dangling));
    };
    match *node {
        | DomainValue::Injection { side, body, .. } => {
            let chosen = match side {
                | Side::Left => on_left,
                | Side::Right => on_right,
            };
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
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Case { on_left, on_right })?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainValue::PathCertificate { .. }
        | DomainValue::Constructor { .. }
        | DomainValue::Record { .. }
        | DomainValue::PathProduct { .. }
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
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
/// - ensures: reflexivity returns unchanged; equivalence invokes the forward
///   map; product transport uses ordinary bind closures, including neutral
///   cases.
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
            Some(&Value::PathEquiv { forward, .. }) => machine.values.len() == values.saturating_sub(1) && machine.values.last().copied() == value && machine.comps.len() == comps && matches!(machine.tasks.get(tasks..), Some(&[Task::Apply, Task::Force, Task::Value { term, .. }]) if term == forward),
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
        | DomainValue::PathCertificate { certificate, .. } => match core.value(certificate) {
            | Some(&Value::PathRefl(_)) => {
                machine
                    .comps
                    .push(domain.comp_return(value, CompTermFace::Reduced));
                Ok(())
            },
            | Some(&Value::PathEquiv { forward, .. }) => {
                machine.values.push(value);
                machine.tasks.push(Task::Apply);
                machine.tasks.push(Task::Force);
                machine.tasks.push(Task::Value {
                    term: forward,
                    env: Machine::root_env(),
                });
                Ok(())
            },
            | _ => Err(EvalFault::DanglingTerm),
        },
        | DomainValue::PathProduct { first, second, .. } => {
            match domain
                .value(value)
                .copied()
                .ok_or(EvalFault::Domain(DomainFault::Dangling))?
            {
                | DomainValue::Pair {
                    first: left,
                    second: right,
                    ..
                } => {
                    let continuation =
                        domain.transport_continuation(crate::closure::CompBody::TransportPair {
                            path: second,
                            value: right,
                        });
                    machine.tasks.push(Task::BindClosure(continuation));
                    machine.tasks.push(Task::Transport);
                    machine.values.extend([first, left]);
                    Ok(())
                },
                | DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(domain, neutral, Elimination::ProductTransport(path))?;
                    machine
                        .comps
                        .push(domain.comp_neutral(grown, CompTermFace::Reduced));
                    Ok(())
                },
                | _ => Err(EvalFault::TransportedNonPath),
            }
        },
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Transport(value))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | _ => Err(EvalFault::TransportedNonPath),
    }
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
        | DomainValue::Constructor { tag, fields, .. } => {
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
        | DomainValue::Neutral { neutral, .. } => {
            let closure = domain.comp_closure_node(term, machine.capture(env)?);
            let grown = extend_spine(domain, neutral, Elimination::DataCase(closure))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | _ => Err(EvalFault::CasedNonConstructor),
    }
}

/// Select the exact label from a record, or suspend projection on a neutral.
///
/// # Specification
/// - requires: the record operand is the top value.
/// - ensures: returns the selected field, never a positional substitute for a
///   missing label.
/// - fails: absent labels, non-records, dangling domains or malformed state.
/// - panics: none.
///
/// # Errors
/// Returns the typed record, domain, term or machine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — unequal fields and an absent label distinguish exact
///   lookup.
/// - witness: `eval::tests::native_records_and_cases_compute`
#[spec(ensures: |ret| ret != Err(EvalFault::OutOfFuel))]
fn step_record_projection(
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
    let Computation::RecordProjection(_, ref label) = *matched_native_node
    else {
        return Err(EvalFault::DanglingTerm);
    };
    let record = machine.pop_value()?;
    match *domain
        .value(record)
        .ok_or(EvalFault::Domain(DomainFault::Dangling))?
    {
        | DomainValue::Record { source, fields, .. } => {
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
            let value = *domain
                .fields(fields)
                .map_err(EvalFault::Domain)?
                .get(position)
                .ok_or(EvalFault::MachineInvariant)?;
            machine
                .comps
                .push(domain.comp_return(value, CompTermFace::Reduced));
            Ok(())
        },
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::RecordProjection(term))?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | _ => Err(EvalFault::ProjectedNonRecord),
    }
}
#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::convert::Infallible;

    use anodized::spec;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ScopeId;
    use gandr_core_term::Transparency;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use super::Bound;
    use super::Definitions;
    use super::EvalFault;
    use super::Evaluation;
    use super::Fuel;
    use super::LoweredChain;
    use super::Progress;
    use super::eval_comp_within;
    use super::eval_computation;
    use super::eval_value;
    use super::face_of;
    use crate::arena::DomainArena;
    use crate::closure::Environment;
    use crate::conv::Settlement;
    use crate::conv::convert_computations;
    use crate::domain::CompTermFace;
    use crate::domain::DomainComp;
    use crate::domain::DomainValue;
    use crate::domain::Elimination;
    use crate::domain::Glued;
    use crate::domain::LevelEntry;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;
    use crate::readback::ReadbackMode;
    use crate::readback::readback_value;

    /// Ample fuel for every case that is meant to finish.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a budget far above the step count any fixture below needs, so
    ///   an exhaustion refusal in one of them is a defect rather than a tight
    ///   budget.
    /// - provides: the budget every finishing case is run with; the exhaustion
    ///   cases name their own small budgets.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the positive budget is sufficient for the finite
    ///   beta, bind and case fixtures, whose exact results would instead be
    ///   `OutOfFuel` if the budget did not cover their work.
    /// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
    /// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
    /// - witness: `eval::tests::a_case_picks_the_branch_the_injection_names`
    #[spec(
        ensures: |ret| ret.0 > 0_u32,
    )]
    fn ample() -> Fuel
    {
        Fuel::from(4_096_u32)
    }

    /// The index at the innermost binder.
    ///
    /// # Specification
    /// trivial.
    fn innermost() -> DeBruijnIndex
    {
        DeBruijnIndex::from(0_u32)
    }

    /// An empty chain and environment, which unfold nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an empty chain and an empty definitional environment, so
    ///   every constant reads as not manifest and no run unfolds.
    /// - provides: the definition side of every fixture that is about reduction
    ///   rather than unfolding.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant under the empty chain remains a rigid
    ///   neutral and its eliminations remain stuck. Introducing a body would
    ///   change the unfolding face and the normalization path.
    /// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
    /// - witness: `eval::tests::normalization_preserves_a_stuck_application`
    #[spec(
        ensures: |ret| ret.0.chain.entries().is_empty() && ret.0.bodies.is_empty(),
    )]
    fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
    {
        (LoweredChain::new(), DefinitionalEnvironment::new())
    }

    /// Lower every body of `chain` to one core value.
    ///
    /// # Specification
    /// - requires: `lowered` resolves in the arena the fixture evaluates
    ///   against.
    /// - ensures: a lowered chain whose every body is `lowered`.
    /// - provides: the lowering side of every fixture that reads an unfolding
    ///   face without forcing it, where what the body lowers to is not what is
    ///   asserted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one lowered definition is manifest or sealed
    ///   according to the chosen scope, and its unforced face names the
    ///   admitted body. Losing a body mapping or using another lowering
    ///   prevents the advertised definition from being forced.
    /// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
    /// - witness: `eval::tests::a_sealed_definition_is_rigid`
    #[spec(
        captures: [entry_count = chain.entries().len()],
        ensures: |ret| ret.chain.entries().len() == entry_count
            && ret.bodies.values().all(|body| *body == lowered)
            && ret.chain.entries().iter().all(|entry| ret.bodies.get(&entry.body()) == Some(&lowered)),
    )]
    fn lowered_to(
        chain: DefinitionChain,
        lowered: ValueId,
    ) -> LoweredChain
    {
        let Ok(chain) = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(lowered));
        chain
    }

    #[test]
    fn an_unreduced_composite_keeps_its_source_face()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let pair = core.value_pair(first, second);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_value(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            pair,
        )
        .expect("a closed pair of units evaluates");

        assert_eq!(
            Some(TermFace::Source(pair)),
            face_of(&domain, evaluated),
            "nothing inside reduced, so the pair still denotes its own source node"
        );
        let Some(&DomainValue::Pair {
            first: left,
            second: right,
            ..
        }) = domain.value(evaluated)
        else {
            panic!("the result is a pair");
        };
        assert_eq!(Some(TermFace::Source(first)), face_of(&domain, left));
        assert_eq!(
            Some(TermFace::Source(second)),
            face_of(&domain, right),
            "and each child denotes the source child it came from"
        );
    }

    #[test]
    fn the_leaf_and_lift_arms_evaluate_and_keep_their_faces()
    {
        let mut core = CoreArena::new();
        let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let lifted = core.value_unit();
        let target = Level::zero().succ().expect("level one exists");
        let lift = core.value_lift(target.clone(), lifted);
        let pair = core.value_pair(literal, lift);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_value(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            pair,
        )
        .expect("a closed pair of a literal and a lift evaluates");

        assert_eq!(
            Some(TermFace::Source(pair)),
            face_of(&domain, evaluated),
            "nothing inside reduced, so both arms kept their faces and the pair kept its own"
        );
        let Some(&DomainValue::Pair { first, second, .. }) = domain.value(evaluated)
        else {
            panic!("the result is a pair");
        };
        assert!(
            matches!(
                domain.value(first),
                Some(&DomainValue::Literal { literal: held, .. }) if held == literal
            ),
            "the literal arm points at the core node holding the payload rather than copying it"
        );
        let Some(&DomainValue::Lift {
            target: held,
            body,
            face,
        }) = domain.value(second)
        else {
            panic!("the second component is a lift");
        };
        assert_eq!(TermFace::Source(lift), face);
        assert_eq!(
            Some(TermFace::Source(lifted)),
            face_of(&domain, body),
            "and its body kept the source it came from"
        );
        assert_eq!(
            Some(&target),
            domain.level(held).map(LevelEntry::level),
            "the lift arm is the only producer of the level family, and it filled it"
        );
    }

    #[test]
    fn a_lift_over_a_substituted_body_loses_its_face()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let target = Level::zero().succ().expect("level one exists");
        let lift = core.value_lift(target, occurrence);
        let body = core.computation_return(lift);
        let lambda = core.computation_lambda(body);
        let redex = core.computation_application(lambda, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            redex,
        )
        .expect("the redex fires");

        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Reduced),
            face_of(&domain, value),
            "the lift's body resolved out of the environment, so the lift lost its source"
        );
        let Some(&DomainValue::Lift { body, .. }) = domain.value(value)
        else {
            panic!("the returned value is a lift");
        };
        assert_eq!(
            Some(TermFace::Source(argument)),
            face_of(&domain, body),
            "while the body it lifted denotes the argument"
        );
    }

    #[test]
    fn a_term_from_another_arena_is_refused()
    {
        let mut evaluated_arena = CoreArena::new();
        let _padding = evaluated_arena.value_unit();

        let mut other = CoreArena::new();
        let mut stranger = other.value_unit();
        let mut remaining = 8_usize;
        while remaining > 0 {
            stranger = other.value_pair(stranger, stranger);
            remaining = remaining.saturating_sub(1);
        }

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        assert_eq!(
            Err(EvalFault::DanglingTerm),
            eval_value(
                &evaluated_arena,
                &mut domain,
                Definitions::new(&chain, &environment, scope),
                ample(),
                stranger,
            ),
            "a term id minted by one arena names no node of another, and the refusal says \
             the term dangled rather than blaming the domain"
        );
    }

    #[test]
    fn an_application_reports_its_arguments_fault_first()
    {
        // Both sides are faulty, and — the load-bearing part — each faults
        // *during its own evaluation* rather than at the application's own
        // frame. The argument is an occurrence with no binder over it; the head
        // forces a unit, which its own `Force` frame refuses. The application's
        // frame runs after both operands, so a fault raised there would surface
        // under either order and would constrain nothing.
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let head = core.computation_force(unit);
        let loose = core.value_variable(Zone::Intuitionistic, innermost());
        let applied = core.computation_application(head, loose);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        assert_eq!(
            Err(EvalFault::UnboundVariable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            eval_computation(
                &core,
                &mut domain,
                Definitions::new(&chain, &environment, scope),
                ample(),
                applied,
            ),
            "the argument is evaluated first, so its fault is the one that surfaces; \
             evaluating the head first would answer ForcedNonThunk"
        );
    }

    #[test]
    fn a_substituted_child_costs_the_composite_its_face()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let held = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let pair = core.value_pair(bound, held);
        let body = core.computation_return(pair);
        let lambda = core.computation_lambda(body);
        let redex = core.computation_application(lambda, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            redex,
        )
        .expect("the redex fires");

        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Reduced),
            face_of(&domain, value),
            "the variable resolved out of the environment, so the pair no longer denotes its source"
        );
        let Some(&DomainValue::Pair { first, .. }) = domain.value(value)
        else {
            panic!("the returned value is a pair");
        };
        assert_eq!(
            Some(TermFace::Source(argument)),
            face_of(&domain, first),
            "and the substituted child denotes the argument rather than the variable"
        );
    }

    #[test]
    fn a_variable_resolves_out_of_the_environment()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let body = core.computation_return(bound);
        let lambda = core.computation_lambda(body);
        let redex = core.computation_application(lambda, argument);
        let loose = core.computation_return(bound);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), redex)
            .expect("the redex fires");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Source(argument)),
            face_of(&domain, value),
            "the bound occurrence stands for what the environment holds"
        );

        assert_eq!(
            Err(EvalFault::UnboundVariable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            eval_computation(&core, &mut domain, definitions, ample(), loose),
            "and an occurrence with no binder over it is refused rather than guessed at"
        );
    }

    #[test]
    fn a_closed_lambda_keeps_its_source_face()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let inner_body = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let returner = core.computation_return(inner_body);
        let inner = core.computation_lambda(returner);
        let outer = core.computation_lambda(inner);
        let applied = core.computation_application(outer, argument);
        let different = core.value_pair(argument, argument);
        let applied_twice = core.computation_application(applied, different);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();

        let closed = eval_computation(&core, &mut domain, definitions, ample(), outer)
            .expect("a lambda is already a weak head");
        let Some(&DomainComp::Lambda { face, .. }) = domain.computation(closed)
        else {
            panic!("the weak head is a lambda");
        };
        assert_eq!(
            CompTermFace::Source(outer),
            face,
            "a lambda over the empty environment denotes its own source node"
        );

        let captured = eval_computation(&core, &mut domain, definitions, ample(), applied)
            .expect("the outer redex fires");
        let Some(&DomainComp::Lambda { face, .. }) = domain.computation(captured)
        else {
            panic!("the weak head is the inner lambda");
        };
        assert_eq!(
            CompTermFace::Reduced,
            face,
            "one that captured a binding denotes its body only up to what the environment supplies"
        );
        let twice = eval_computation(&core, &mut domain, definitions, ample(), applied_twice)
            .expect("the captured outer binding survives the second application");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(twice)
        else {
            panic!("the outer-bound variable returns its argument");
        };
        assert_eq!(
            Some(TermFace::Source(argument)),
            face_of(&domain, value),
            "the captured unit, not the inner pair argument, is returned"
        );
    }

    #[test]
    fn a_redex_fires_and_the_body_sees_the_argument()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let returner = core.computation_return(bound);
        let identity = core.computation_lambda(returner);
        let thunked = core.value_thunk(identity);
        let forced = core.computation_force(thunked);
        let applied = core.computation_application(forced, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            applied,
        )
        .expect("forcing a thunk of a lambda and applying it fires");

        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Source(argument)),
            face_of(&domain, value),
            "force entered the closure and the application bound the argument in it"
        );
    }

    #[test]
    fn a_bind_passes_the_returned_value_on()
    {
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let bound_comp = core.computation_return(produced);
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let continuation = core.computation_return(occurrence);
        let sequenced = core.computation_bind(bound_comp, continuation);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            sequenced,
        )
        .expect("a bind over a returner runs its continuation");

        let Some(&DomainComp::Return { value, face }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Source(produced)),
            face_of(&domain, value),
            "the continuation sees exactly what the bound computation returned"
        );
        assert_eq!(
            CompTermFace::Reduced,
            face,
            "and the returner it built no longer denotes its own source, because the \
             occurrence resolved"
        );
    }

    #[test]
    fn native_certificate_conversion_retains_map_syntax()
    {
        let mut core = CoreArena::new();
        let unit_type = core.value_type_unit();
        let code = core.value_quote(unit_type);
        let path_type = core.value_type_path_universe(code, code);
        let variable = core.value_variable(Zone::Intuitionistic, innermost());
        let returned = core.computation_return(variable);
        let direct = core.computation_lambda(returned);
        let direct = core.value_thunk(direct);
        let sequenced = core.computation_bind(returned, returned);
        let expanded = core.computation_lambda(sequenced);
        let expanded = core.value_thunk(expanded);
        let proof = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
            source: Vec::from([Vec::new()]),
            target: Vec::from([Vec::new()]),
        });
        let first =
            core.value_path_equiv(path_type, direct, direct, alloc::sync::Arc::clone(&proof));
        let other = core.value_path_equiv(path_type, direct, expanded, proof);
        let altered = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
            source: Vec::from([Vec::from([
                gandr_kernel_conversion_trace::ConversionDecision::ComparedShared {
                    left: (),
                    right: (),
                },
            ])]),
            target: Vec::from([Vec::new()]),
        });
        let evidence_only = core.value_path_equiv(path_type, direct, direct, altered);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let first = eval_value(&core, &mut domain, definitions, ample(), first)
            .expect("closed certificate");
        let other = eval_value(&core, &mut domain, definitions, ample(), other)
            .expect("closed certificate");
        let evidence_only = eval_value(&core, &mut domain, definitions, ample(), evidence_only)
            .expect("closed syntax");
        assert_eq!(
            Ok(crate::conv::Convertibility::Distinct),
            crate::conv::convert_values(&core, &domain, first, other).map(Settlement::verdict),
            "extensionally equal maps do not identify certificate programs"
        );
        assert_eq!(
            Ok(crate::conv::Convertibility::Convertible),
            crate::conv::convert_values(&core, &domain, first, evidence_only)
                .map(Settlement::verdict),
            "comparison erases evidence; only kernel admission can certify it"
        );
    }

    #[test]
    fn native_transport_sequences_product_components()
    {
        for (first_stuck, second_stuck) in
            [(false, false), (true, false), (false, true), (true, true)]
        {
            let mut core = CoreArena::new();
            let unit = core.value_unit();
            let unit_type = core.value_type_unit();
            let boolean = core.value_type_sum(unit_type, unit_type);
            let code = core.value_quote(boolean);
            let refl = core.value_path_refl(code);
            let first_path = if first_stuck {
                core.value_constant(ConstantIndex::from(0_usize))
            }
            else {
                refl
            };
            let second_path = if second_stuck {
                core.value_constant(ConstantIndex::from(1_usize))
            }
            else {
                refl
            };
            let path = core.value_path_product(first_path, second_path);
            let left = core.value_injection(Side::Left, unit);
            let right = core.value_injection(Side::Right, unit);
            let operand = core.value_pair(left, right);
            let transported = core.computation_transport(path, operand);
            let first = if first_stuck {
                core.value_variable(
                    Zone::Intuitionistic,
                    DeBruijnIndex::from(u32::from(second_stuck)),
                )
            }
            else {
                left
            };
            let second = if second_stuck {
                core.value_variable(Zone::Intuitionistic, innermost())
            }
            else {
                right
            };
            let pair = core.value_pair(first, second);
            let mut expected = core.computation_return(pair);
            if second_stuck {
                let transport = core.computation_transport(second_path, right);
                expected = core.computation_bind(transport, expected);
            }
            if first_stuck {
                let transport = core.computation_transport(first_path, left);
                expected = core.computation_bind(transport, expected);
            }
            let expected = core.value_thunk(expected);
            let (chain, environment) = nothing_unfolds();
            let definitions = Definitions::new(&chain, &environment, environment.root());
            let mut domain = DomainArena::new();
            let evaluated = eval_computation(&core, &mut domain, definitions, ample(), transported)
                .expect("neutral components suspend; reflexivity returns");
            for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
                let normal = crate::readback::readback_computation(
                    &mut core,
                    &mut domain,
                    definitions,
                    mode,
                    ample(),
                    evaluated,
                )
                .expect("captured product continuations reopen under binders");
                let normal = core.value_thunk(normal);
                assert!(
                    gandr_core_term::equal_certificate_syntax(&core, normal, expected)
                        == gandr_core_term::CertificateEquality::Equal,
                    "product sequencing preserves both coordinates and binder depths: {first_stuck:?}, {second_stuck:?}, {mode:?}"
                );
            }
        }
    }

    #[test]
    fn a_case_picks_the_branch_the_injection_names()
    {
        let mut core = CoreArena::new();
        let injected = core.value_unit();
        let untaken = core.value_unit();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let on_left = core.computation_return(occurrence);
        let on_right = core.computation_return(untaken);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        for (side, expected) in [(Side::Left, injected), (Side::Right, untaken)] {
            let scrutinee = core.value_injection(side, injected);
            let cased = core.computation_case(scrutinee, on_left, on_right);
            let mut domain = DomainArena::new();
            let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased)
                .expect("a case over an injection picks a branch");
            let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
            else {
                panic!("the weak head is a returner");
            };
            assert_eq!(
                Some(TermFace::Source(expected)),
                face_of(&domain, value),
                "the side of the injection decides which branch ran"
            );
        }
    }

    #[test]
    fn an_eliminator_on_a_neutral_grows_its_spine()
    {
        let mut core = CoreArena::new();
        let opaque = core.value_constant(ConstantIndex::from(0_usize));
        let argument = core.value_unit();
        let forced = core.computation_force(opaque);
        let applied = core.computation_application(forced, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            applied,
        )
        .expect("an eliminator over a rigid constant gets stuck rather than failing");

        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is stuck");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            held.head(),
            "the head is the constant that could not step"
        );
        assert_eq!(
            2_usize,
            held.spine().len(),
            "both eliminations stacked rather than either being dropped"
        );
        assert_eq!(
            Some(&Elimination::Force),
            held.spine().first(),
            "innermost first"
        );
        assert!(
            matches!(held.spine().get(1_usize), Some(&Elimination::Apply(_))),
            "outermost last"
        );
        assert_eq!(
            Unfolding::Rigid,
            held.unfolding(),
            "an unknown constant has no body, so growing the spine kept it rigid"
        );
    }

    #[test]
    fn a_manifest_definition_carries_its_body_unforced()
    {
        let mut core = CoreArena::new();
        let constant = ConstantIndex::from(0_usize);
        let reference = core.value_constant(constant);

        let mut chain = DefinitionChain::new();
        let body = GlobalIndex::from(9_u32);
        let defined = chain.define(constant, body, Transparency::Manifest, &[]);
        assert!(defined.is_ok());
        let chain = lowered_to(chain, reference);
        let environment = DefinitionalEnvironment::new();
        let scope = environment.root();

        let mut domain = DomainArena::new();
        let evaluated = eval_value(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            reference,
        )
        .expect("a constant evaluates to a neutral");

        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
        else {
            panic!("a constant is stuck");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            Unfolding::Unforced(body),
            held.unfolding(),
            "a manifest definition carries its body's content id, unforced"
        );
        assert!(
            held.spine().is_empty(),
            "and stands in a value position, so it carries no spine"
        );
    }

    #[test]
    fn a_sealed_definition_is_rigid()
    {
        let mut core = CoreArena::new();
        let constant = ConstantIndex::from(0_usize);
        let reference = core.value_constant(constant);

        let mut chain = DefinitionChain::new();
        let defined = chain.define(
            constant,
            GlobalIndex::from(9_u32),
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
        let chain = lowered_to(chain, reference);
        let mut environment = DefinitionalEnvironment::new();
        let outer = environment.root();
        let inner = environment.open_scope(outer).expect("the root resolves");
        let sealed = environment.state(outer, constant, Transparency::Opaque);
        assert_eq!(Ok(()), sealed);

        for (scope, expected) in [
            (inner, Unfolding::Rigid),
            (ScopeId::from(9_usize), Unfolding::Rigid),
        ] {
            let mut domain = DomainArena::new();
            let evaluated = eval_value(
                &core,
                &mut domain,
                Definitions::new(&chain, &environment, scope),
                ample(),
                reference,
            )
            .expect("a constant evaluates to a neutral");
            let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
            else {
                panic!("a constant is stuck");
            };
            let held = domain.neutral(neutral).expect("the neutral resolves");
            assert_eq!(
                expected,
                held.unfolding(),
                "a seal in an enclosing scope, and a scope that was never opened, both \
                 degrade to rigidity rather than unfolding"
            );
        }
    }

    #[test]
    fn an_ill_shaped_elimination_is_refused()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let returner = core.computation_return(unit);
        let inner = core.computation_return(unit);
        let lambda = core.computation_lambda(inner);

        let forced_unit = core.computation_force(unit);
        let applied_returner = core.computation_application(returner, unit);
        let bound_lambda = core.computation_bind(lambda, returner);
        let cased_unit = core.computation_case(unit, returner, returner);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);

        for (term, expected) in [
            (forced_unit, EvalFault::ForcedNonThunk),
            (applied_returner, EvalFault::AppliedNonFunction),
            (bound_lambda, EvalFault::BoundNonReturner),
            (cased_unit, EvalFault::CasedNonInjection),
        ] {
            let mut domain = DomainArena::new();
            assert_eq!(
                Err(expected),
                eval_computation(&core, &mut domain, definitions, ample(), term),
                "an eliminator meeting the wrong polarity of weak head is refused by name"
            );
        }

        let applied_unit = core.value_static_application(unit, unit);
        let mut domain = DomainArena::new();
        assert_eq!(
            Err(EvalFault::AppliedNonOperator),
            eval_value(&core, &mut domain, definitions, ample(), applied_unit),
            "a static application of a value that is no operator is refused by name"
        );
    }

    #[test]
    fn normalizes_beta_redex()
    {
        let mut core = CoreArena::new();
        // (λX. ⌜El X × El X⌝) ⌜Integer⌝ ⇝ ⌜Integer × Integer⌝.
        let integer = core.value_type_base(BaseType::Integer);
        let argument = core.value_quote(integer);
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let decoded = core.value_type_element(bound, Level::zero());
        let doubled = core.value_type_product(decoded, decoded);
        let body = core.value_quote(doubled);
        let operator = core.value_static_lambda(body);
        let redex = core.value_static_application(operator, argument);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), redex)
            .expect("a static redex evaluates");
        assert!(
            matches!(domain.value(evaluated), Some(&DomainValue::Code { .. })),
            "static beta fired: the weak head is the body's code, not a stuck application"
        );
        let normal = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the reduct reads back");
        let Some(&Value::Quote(quoted)) = core.value(normal)
        else {
            panic!("the normal form is a quote");
        };
        let Some(&ValueType::Product(first, second)) = core.value_type(quoted)
        else {
            panic!("the quoted type is the body's product");
        };
        for component in [first, second] {
            assert_eq!(
                Some(&ValueType::Base(BaseType::Integer)),
                core.value_type(component),
                "each decode of the bound code reads as the argument's quoted type"
            );
        }
    }

    #[test]
    fn normalization_preserves_a_stuck_application()
    {
        let mut core = CoreArena::new();
        // F ((λX. X) ⌜Integer⌝) with F a constant that cannot unfold ⇝
        // F ⌜Integer⌝: the application stays, and its argument normalizes.
        let family = ConstantIndex::from(0_usize);
        let head = core.value_constant(family);
        let integer = core.value_type_base(BaseType::Integer);
        let quote = core.value_quote(integer);
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let identity = core.value_static_lambda(bound);
        let redex = core.value_static_application(identity, quote);
        let stuck = core.value_static_application(head, redex);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let evaluated = eval_value(&core, &mut domain, definitions, ample(), stuck)
            .expect("a stuck application evaluates");
        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
        else {
            panic!("an application of a rigid head is a neutral value");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            NeutralHead::Constant(family),
            held.head(),
            "the neutral stands on the family's head"
        );
        assert!(
            matches!(held.spine(), [Elimination::StaticApply(_)]),
            "and carries the one static application"
        );
        let normal = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the stuck application reads back");
        let Some(&Value::StaticApplication(read_head, read_argument)) = core.value(normal)
        else {
            panic!("the normal form is still a static application");
        };
        assert_eq!(
            Some(&Value::Constant(family)),
            core.value(read_head),
            "its head is the family"
        );
        let Some(&Value::Quote(quoted)) = core.value(read_argument)
        else {
            panic!("its argument normalized past the inner redex to the quote");
        };
        assert_eq!(
            Some(&ValueType::Base(BaseType::Integer)),
            core.value_type(quoted),
            "and the quote carries the argument's type"
        );
    }

    #[test]
    fn an_evaluation_in_a_supplied_environment_reports_its_remainder()
    {
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let returner = core.computation_return(occurrence);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let definitions = Definitions::new(&chain, &environment, scope);
        let mut domain = DomainArena::new();
        let bound = domain.value_unit(TermFace::Reduced);
        let mut supplied = Environment::new();
        supplied.extend(Zone::Intuitionistic, bound);

        let budget = Fuel::from(10_u32);
        let (produced, remaining) =
            eval_comp_within(&core, &mut domain, definitions, budget, returner, supplied)
                .expect("the supplied environment answers the occurrence");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(produced)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            bound, value,
            "the run started from the environment it was handed rather than from the empty one"
        );
        assert_eq!(
            Fuel::from(7_u32),
            remaining,
            "three tasks ran — the returner, its value, and the returner's assembly frame — \
             and each spent exactly one unit of the budget"
        );

        assert_eq!(
            Err(EvalFault::UnboundVariable {
                zone: Zone::Intuitionistic,
                index: innermost(),
            }),
            eval_comp_within(
                &core,
                &mut domain,
                definitions,
                budget,
                returner,
                Environment::new(),
            ),
            "and the same body over the empty environment is refused, so the binding is what \
             answered it"
        );
    }

    #[test]
    fn a_loop_declines_on_fuel_rather_than_diverging()
    {
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let inner_force = core.computation_force(occurrence);
        let self_application = core.computation_application(inner_force, occurrence);
        let lambda = core.computation_lambda(self_application);
        let looper = core.value_thunk(lambda);
        let outer_force = core.computation_force(looper);
        let omega = core.computation_application(outer_force, looper);

        let (chain, environment) = nothing_unfolds();
        let scope = environment.root();
        let mut domain = DomainArena::new();
        assert_eq!(
            Err(EvalFault::OutOfFuel),
            eval_computation(
                &core,
                &mut domain,
                Definitions::new(&chain, &environment, scope),
                Fuel::from(500_u32),
                omega,
            ),
            "beta and force alone loop, so the machine declines within its budget"
        );
    }

    #[test]
    fn a_chain_lowers_each_body_once_in_admission_order()
    {
        let mut core = CoreArena::new();
        let mut chain = DefinitionChain::new();
        let shared = GlobalIndex::from(5_u32);
        let own = GlobalIndex::from(6_u32);
        for (position, body) in [(0_usize, shared), (1_usize, own), (2_usize, shared)] {
            let defined = chain.define(
                ConstantIndex::from(position),
                body,
                Transparency::Manifest,
                &[],
            );
            assert!(defined.is_ok());
        }

        let mut asked = Vec::new();
        let Ok(lowered) = LoweredChain::lower(chain, |entry| {
            let lowered = core.value_unit();
            asked.push((entry.constant(), lowered));
            Ok::<_, Infallible>(lowered)
        });
        let &[(first, first_lowering), (second, second_lowering)] = asked.as_slice()
        else {
            panic!(
                "the pass asks once per distinct body index, so the third definition reuses \
                 the first one's lowering"
            );
        };
        assert_eq!(
            (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)),
            (first, second),
            "and it asks in admission order"
        );
        assert_eq!(
            (Some(&first_lowering), Some(&second_lowering)),
            (lowered.bodies().get(&shared), lowered.bodies().get(&own)),
            "each index reads as the lowering it was asked for"
        );
    }

    #[test]
    fn a_refused_lowering_returns_no_chain()
    {
        let mut chain = DefinitionChain::new();
        for (position, body) in [(0_usize, 0_u32), (1_usize, 1_u32)] {
            let defined = chain.define(
                ConstantIndex::from(position),
                GlobalIndex::from(body),
                Transparency::Manifest,
                &[],
            );
            assert!(defined.is_ok());
        }

        let mut core = CoreArena::new();
        let refused = LoweredChain::lower(chain, |entry| {
            if entry.constant() == ConstantIndex::from(1_usize) {
                Err(entry.constant())
            }
            else {
                Ok(core.value_unit())
            }
        });
        assert_eq!(
            Err(ConstantIndex::from(1_usize)),
            refused,
            "the first refusal is the answer, unchanged, and no partly lowered chain \
             escapes"
        );
    }

    #[test]
    fn a_sliced_evaluation_agrees_with_an_unsliced_one()
    {
        let mut core = CoreArena::new();
        let argument = core.value_unit();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let doubled = core.value_pair(occurrence, occurrence);
        let returned = core.computation_return(doubled);
        let lambda = core.computation_lambda(returned);
        let redex = core.computation_application(lambda, argument);
        let delayed = core.value_thunk(redex);

        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let unsliced = eval_computation(&core, &mut domain, definitions, ample(), redex)
            .expect("a closed redex evaluates");
        let suspended = eval_value(&core, &mut domain, definitions, ample(), delayed)
            .expect("a thunk evaluates to its closure");
        let Some(&DomainValue::Thunk { body, .. }) = domain.value(suspended)
        else {
            panic!("a thunk evaluates to a thunk");
        };

        let mut sliced = Evaluation::enter(definitions, &domain, body, Bound::Nothing)
            .expect("the closure resolves");
        let answer = loop {
            let (progress, spent) = sliced
                .resume(&core, &mut domain, Fuel::from(1_u32))
                .expect("no slice of a closed redex is refused");
            assert!(
                u32::from(spent) <= 1_u32,
                "a slice never outspends its budget"
            );
            if let Progress::Finished(answer) = progress {
                break answer;
            }
        };

        let Glued::Computation(sliced) = answer
        else {
            panic!("an entered closure answers a computation");
        };
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_computations(&core, &domain, unsliced, sliced),
            "and the paused run reached the weak head the uninterrupted one did"
        );
    }

    #[test]
    fn a_reapplied_spine_fires_once_the_head_unfolds()
    {
        let mut core = CoreArena::new();
        let function = ConstantIndex::from(0_usize);
        let injected = ConstantIndex::from(1_usize);
        let unit = core.value_unit();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let identity = core.computation_return(occurrence);
        let lambda = core.computation_lambda(identity);
        let function_body = core.value_thunk(lambda);
        let injected_body = core.value_injection(Side::Left, unit);

        let function_reference = core.value_constant(function);
        let forced = core.computation_force(function_reference);
        let applied = core.computation_application(forced, unit);
        let passed_on = core.computation_return(occurrence);
        let bound = core.computation_bind(applied, passed_on);
        let injected_reference = core.value_constant(injected);
        let on_left = core.computation_return(occurrence);
        let on_right = core.computation_return(unit);
        let cased = core.computation_case(injected_reference, on_left, on_right);

        let mut chain = DefinitionChain::new();
        for (constant, body) in [(function, 0_u32), (injected, 1_u32)] {
            let defined = chain.define(
                constant,
                GlobalIndex::from(body),
                Transparency::Manifest,
                &[],
            );
            assert!(defined.is_ok());
        }
        let Ok(chain) = LoweredChain::lower(chain, |entry| {
            Ok::<_, Infallible>(if entry.constant() == function {
                function_body
            }
            else {
                injected_body
            })
        });
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();

        for (stuck, head_body) in [(bound, function_body), (cased, injected_body)] {
            let evaluated = eval_computation(&core, &mut domain, definitions, ample(), stuck)
                .expect("an eliminator over an unforced constant gets stuck");
            let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
            else {
                panic!("the constant is not unfolded by evaluation, so the computation is stuck");
            };
            let spine = Vec::from(
                domain
                    .neutral(neutral)
                    .expect("the neutral resolves")
                    .spine(),
            );
            let head = eval_value(&core, &mut domain, definitions, ample(), head_body)
                .expect("a definition body evaluates");

            let mut reapplied = Evaluation::eliminate(definitions, head, &spine);
            let (progress, _spent) = reapplied
                .resume(&core, &mut domain, ample())
                .expect("every elimination fits the unfolded head");
            let Progress::Finished(Glued::Computation(answer)) = progress
            else {
                panic!("an ample slice reaches the weak head, a computation");
            };
            let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
            else {
                panic!("every spine here ends in a returner once its head unfolds");
            };
            assert!(
                matches!(domain.value(value), Some(&DomainValue::Unit { .. })),
                "the force, the application, the bind and the case each fired on the \
                 unfolded head in order"
            );
        }
    }

    #[test]
    fn a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let mut evaluation = Evaluation::body(definitions, unit);
        assert_eq!(
            Ok((Progress::Paused, Fuel::from(0_u32))),
            evaluation.resume(&core, &mut domain, Fuel::from(0_u32))
        );
        let (progress, spent) = evaluation
            .resume(&core, &mut domain, Fuel::from(1_u32))
            .expect("the unspent task is still available");
        assert_eq!(Fuel::from(1_u32), spent);
        let Progress::Finished(Glued::Value(value)) = progress
        else {
            panic!("draining on the last available step finishes rather than pauses");
        };
        assert_eq!(
            Some(&DomainValue::Unit {
                face: TermFace::Source(unit)
            }),
            domain.value(value)
        );
    }

    #[test]
    fn reapplied_eliminations_preserve_captures_and_argument_order()
    {
        let mut core = CoreArena::new();
        let argument = core.value_variable(Zone::Intuitionistic, innermost());
        let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let pair = core.value_pair(captured, argument);
        let body = core.computation_return(pair);
        let pass = core.computation_return(argument);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let first = domain.value_unit(TermFace::Reduced);
        let second = domain.value_injection(Side::Left, first, TermFace::Reduced);
        let supplied = domain.value_injection(Side::Right, first, TermFace::Reduced);
        let mut left_capture = Environment::new();
        left_capture.extend(Zone::Intuitionistic, first);
        let mut right_capture = Environment::new();
        right_capture.extend(Zone::Intuitionistic, second);
        let on_left = domain.comp_closure_node(body, left_capture);
        let on_right = domain.comp_closure_node(body, right_capture);
        let left = domain.value_injection(Side::Left, supplied, TermFace::Reduced);
        let right = domain.value_injection(Side::Right, supplied, TermFace::Reduced);
        let mut returned_capture = Environment::new();
        returned_capture.extend(Zone::Intuitionistic, supplied);
        let returning = domain.comp_closure_node(pass, returned_capture);
        let thunk = domain.value_thunk(returning, TermFace::Reduced);
        let case = [Elimination::Case { on_left, on_right }];
        let bind = [Elimination::Force, Elimination::Bind(on_right)];
        for (head, spine, expected_capture) in [
            (left, case.as_slice(), first),
            (right, case.as_slice(), second),
            (thunk, bind.as_slice(), second),
        ] {
            let mut evaluation = Evaluation::eliminate(definitions, head, spine);
            let (progress, _spent) = evaluation
                .resume(&core, &mut domain, ample())
                .expect("the captured elimination has its operands");
            let Progress::Finished(Glued::Computation(answer)) = progress
            else {
                panic!("each elimination finishes at a returner");
            };
            let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
            else {
                panic!("the selected continuation returns its pair");
            };
            assert_eq!(
                Some(&DomainValue::Pair {
                    first: expected_capture,
                    second: supplied,
                    face: TermFace::Reduced,
                }),
                domain.value(value),
                "the old capture stays outside the new argument, in the selected environment"
            );
        }
    }

    #[test]
    fn reapplied_cases_refuse_only_when_the_selected_closure_is_missing()
    {
        let mut core = CoreArena::new();
        let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
        let body = core.computation_return(occurrence);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let value = domain.value_unit(TermFace::Reduced);
        let mut captured = Environment::new();
        captured.extend(Zone::Intuitionistic, value);
        let live = domain.comp_closure_node(body, captured);
        let left = domain.value_injection(Side::Left, value, TermFace::Reduced);
        let right = domain.value_injection(Side::Right, value, TermFace::Reduced);
        let boundary = domain.watermark();
        let missing = domain.comp_closure_node(body, Environment::new());
        domain.truncate_to(boundary);
        let spine = [Elimination::Case {
            on_left: missing,
            on_right: live,
        }];
        let mut selected_live = Evaluation::eliminate(definitions, right, &spine);
        let (progress, _spent) = selected_live
            .resume(&core, &mut domain, ample())
            .expect("the unselected closure is not read");
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("the live branch finishes");
        };
        assert_eq!(
            Some(&DomainComp::Return {
                value,
                face: CompTermFace::Reduced
            }),
            domain.computation(answer)
        );
        let mut selected_missing = Evaluation::eliminate(definitions, left, &spine);
        assert_eq!(
            Err(EvalFault::Domain(super::DomainFault::Dangling)),
            selected_missing.resume(&core, &mut domain, ample())
        );
    }

    #[test]
    fn shared_configurations_distinguish_zones_but_ignore_unused_bindings()
    {
        let mut core = CoreArena::new();
        let intuitionistic = core.value_variable(Zone::Intuitionistic, innermost());
        let linear = core.value_variable(Zone::Linear, innermost());
        let pair = core.value_pair(intuitionistic, linear);
        let term = super::CoreTerm::Value(pair);
        let mut indices = crate::free::FreeIndices::default();
        let free = indices
            .of(&core, term)
            .expect("both free indices resolve in the core")
            .clone();
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut machine = super::Machine::new(definitions, ample());
        machine.sharing.legs.insert(term, free);
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(TermFace::Reduced);
        let injection = domain.value_injection(Side::Left, unit, TermFace::Reduced);
        for (first, second, unused, steps) in [
            (unit, injection, unit, 5_u32),
            (unit, injection, injection, 1_u32),
            (injection, unit, unit, 5_u32),
        ] {
            let mut environment = Environment::new();
            environment.extend(Zone::Intuitionistic, unused);
            environment.extend(Zone::Intuitionistic, first);
            environment.extend(Zone::Linear, second);
            let env = machine.hold_env(environment);
            machine.tasks.push(super::Task::Value { term: pair, env });
            machine.fuel = ample();
            super::run(&core, &mut domain, &mut machine).expect("both free bindings are supplied");
            let result = machine.pop_value().expect("the leg produced its pair");
            assert_eq!(
                Some(&DomainValue::Pair {
                    first,
                    second,
                    face: TermFace::Reduced
                }),
                domain.value(result)
            );
            assert_eq!(
                steps,
                u32::from(ample()).saturating_sub(u32::from(machine.fuel))
            );
        }
    }

    #[test]
    fn a_refused_evaluation_leaves_existing_values_usable()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let loose = core.value_variable(Zone::Linear, innermost());
        let pair = core.value_pair(unit, loose);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let existing = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Err(EvalFault::UnboundVariable {
                zone: Zone::Linear,
                index: innermost()
            }),
            eval_value(&core, &mut domain, definitions, ample(), pair)
        );
        assert_eq!(
            Some(&DomainValue::Unit {
                face: TermFace::Reduced
            }),
            domain.value(existing)
        );
        let retried = eval_value(&core, &mut domain, definitions, ample(), unit)
            .expect("a refused run does not poison later evaluation");
        assert_eq!(
            Some(&DomainValue::Unit {
                face: TermFace::Source(unit)
            }),
            domain.value(retried)
        );
    }

    #[test]
    fn ill_shaped_reapplied_spines_return_machine_faults()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let body = core.computation_return(unit);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let argument = domain.value_unit(TermFace::Reduced);
        let continuation = domain.comp_closure_node(body, Environment::new());
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a rigid constant carries no body");
        let head = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("the initial spine is a value spine");
        for spine in [
            [Elimination::Force, Elimination::Transport(argument)],
            [Elimination::Force, Elimination::ProductTransport(argument)],
            [Elimination::Force, Elimination::Force],
            [Elimination::Force, Elimination::StaticApply(argument)],
            [
                Elimination::StaticApply(argument),
                Elimination::Apply(argument),
            ],
            [
                Elimination::StaticApply(argument),
                Elimination::Bind(continuation),
            ],
            [Elimination::Force, Elimination::Case {
                on_left: continuation,
                on_right: continuation,
            }],
        ] {
            let mut evaluation = Evaluation::eliminate(definitions, head, &spine);
            assert_eq!(
                Err(EvalFault::MachineInvariant),
                evaluation.resume(&core, &mut domain, ample()),
                "an ill-shaped later elimination is a named refusal, not a contract panic"
            );
        }
    }

    #[test]
    fn reapplied_closures_keep_stuck_spines_and_refuse_wrong_formers()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let returned = core.computation_return(unit);
        let pair = core.value_pair(unit, unit);
        let paired = core.computation_return(pair);
        let lambda = core.computation_lambda(returned);
        let suspended_lambda = core.value_thunk(lambda);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let argument = domain.value_unit(TermFace::Reduced);
        let on_left = domain.comp_closure_node(returned, Environment::new());
        let on_right = domain.comp_closure_node(paired, Environment::new());
        let neutral = domain
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::from([Elimination::StaticApply(argument)]),
                Unfolding::Rigid,
            )
            .expect("a rigid head can carry an existing static frame");
        let head = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("the prefix still denotes a value");
        let bind = [Elimination::Force, Elimination::Bind(on_left)];
        let case = [Elimination::Case { on_left, on_right }];
        let bound = [
            Elimination::StaticApply(argument),
            Elimination::Force,
            Elimination::Bind(on_left),
        ];
        let cased = [Elimination::StaticApply(argument), Elimination::Case {
            on_left,
            on_right,
        }];
        for (spine, expected) in [
            (bind.as_slice(), bound.as_slice()),
            (case.as_slice(), cased.as_slice()),
        ] {
            let mut evaluation = Evaluation::eliminate(definitions, head, spine);
            let (progress, _spent) = evaluation
                .resume(&core, &mut domain, ample())
                .expect("a rigid head leaves its eliminations stuck");
            let Progress::Finished(Glued::Computation(answer)) = progress
            else {
                panic!("the eliminations produce a computation");
            };
            let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(answer)
            else {
                panic!("the result stays neutral");
            };
            assert_eq!(
                expected,
                domain
                    .neutral(neutral)
                    .expect("the grown spine resolves")
                    .spine()
            );
        }
        let mut wrong_case = Evaluation::eliminate(definitions, argument, &case);
        assert_eq!(
            Err(EvalFault::CasedNonInjection),
            wrong_case.resume(&core, &mut domain, ample())
        );
        let thunk = eval_value(&core, &mut domain, definitions, ample(), suspended_lambda)
            .expect("the thunk captures the lambda");
        let mut wrong_bind = Evaluation::eliminate(definitions, thunk, &bind);
        assert_eq!(
            Err(EvalFault::BoundNonReturner),
            wrong_bind.resume(&core, &mut domain, ample())
        );
    }

    #[test]
    fn native_records_and_cases_compute()
    {
        use alloc::collections::BTreeMap;
        use alloc::string::String;

        use gandr_core_term::ConstructorTag;
        use gandr_core_term::FieldLabel;
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let left = core.value_injection(Side::Left, unit);
        let right = core.value_injection(Side::Right, unit);
        let pair = core.value_pair(unit, unit);
        let empty = core.value_record(BTreeMap::new());
        let labels = ["a", "b", "c", "d", "e"].map(|label| FieldLabel::from(String::from(label)));
        let source = core.value_record(
            labels
                .iter()
                .cloned()
                .zip([unit, left, right, pair, empty])
                .collect(),
        );
        let variables = [4_u32, 3, 2, 1, 0]
            .map(|index| core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
        let record = core.value_record(labels.iter().cloned().zip(variables).collect());
        let untaken = core.value_record(
            labels
                .iter()
                .cloned()
                .zip([unit, right, left, pair, empty])
                .collect(),
        );
        let mut selected = core.computation_return(record);
        let mut alternate = core.computation_return(untaken);
        for _ in 0 .. 5_u8 {
            selected = core.computation_lambda(selected);
            alternate = core.computation_lambda(alternate);
        }
        let unit_type = core.value_type_unit();
        let sum = core.value_type_sum(unit_type, unit_type);
        let product = core.value_type_product(unit_type, unit_type);
        let empty_type = core.value_type_record(BTreeMap::new());
        let record_type = core.value_type_record(
            labels
                .iter()
                .cloned()
                .zip([unit_type, sum, sum, product, empty_type])
                .collect(),
        );
        let motive = core.comp_type_returner(record_type);
        let datatype = core.value_type_data(ConstantIndex::from(2_usize), Vec::new());
        let fields = [unit, left, right, pair, empty];
        let constructor =
            core.value_constructor(datatype, ConstructorTag::from(1_usize), Vec::from(fields));
        let cased =
            core.computation_data_case(constructor, motive, Vec::from([alternate, selected]));
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("case returns its selected record");
        };
        let normal = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            value,
        )
        .unwrap();
        let Some(matched_native_node) = core.value(normal)
        else {
            panic!("record readback");
        };
        let Value::Record(ref record) = *matched_native_node
        else {
            panic!("record readback");
        };
        assert!(record.keys().eq(labels.iter()));
        let mut actual = record.values().copied();
        assert!(matches!(
            core.value(actual.next().unwrap()),
            Some(Value::Unit)
        ));
        assert!(matches!(
            core.value(actual.next().unwrap()),
            Some(Value::Injection(Side::Left, _))
        ));
        assert!(matches!(
            core.value(actual.next().unwrap()),
            Some(Value::Injection(Side::Right, _))
        ));
        assert!(matches!(
            core.value(actual.next().unwrap()),
            Some(Value::Pair(_, _))
        ));
        assert!(
            matches!(core.value(actual.next().unwrap()),Some(Value::Record(fields)) if fields.is_empty())
        );
        let projection = core.computation_record_projection(source, labels[2].clone());
        let projected =
            eval_computation(&core, &mut domain, definitions, ample(), projection).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(projected)
        else {
            panic!("projection returns a field");
        };
        assert!(matches!(
            domain.value(value),
            Some(DomainValue::Injection {
                side: Side::Right,
                ..
            })
        ));
        let absent =
            core.computation_record_projection(source, FieldLabel::from(String::from("absent")));
        let wrong_record = core.computation_record_projection(unit, labels[0].clone());
        let wrong_data = core.computation_data_case(unit, motive, Vec::from([alternate, selected]));
        let unknown =
            core.value_constructor(datatype, ConstructorTag::from(2_usize), Vec::from(fields));
        let unknown = core.computation_data_case(unknown, motive, Vec::from([alternate, selected]));
        for (term, fault) in [
            (absent, EvalFault::AbsentRecordField),
            (wrong_record, EvalFault::ProjectedNonRecord),
            (wrong_data, EvalFault::CasedNonConstructor),
            (unknown, EvalFault::UnknownConstructor {
                tag: ConstructorTag::from(2_usize),
            }),
        ] {
            assert_eq!(
                eval_computation(&core, &mut domain, definitions, ample(), term),
                Err(fault)
            );
        }
        // Unselected suspended fields must stay unopened.
        let poison = core.value_thunk(wrong_record);
        let quiet = core.value_record(BTreeMap::from([
            (labels[0].clone(), poison),
            (labels[1].clone(), right),
        ]));
        let quiet = core.computation_record_projection(quiet, labels[1].clone());
        let projected = eval_computation(&core, &mut domain, definitions, ample(), quiet).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(projected)
        else {
            panic!("only the selected field returns");
        };
        let normal = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            value,
        )
        .unwrap();
        assert!(matches!(
            core.value(normal),
            Some(Value::Injection(Side::Right, _))
        ));
        let argument = core.value_variable(Zone::Intuitionistic, innermost());
        let identity = core.computation_return(argument);
        let identity = core.computation_lambda(identity);
        let identity = core.value_thunk(identity);
        let module = core.value_record(BTreeMap::from([
            (labels[0].clone(), poison),
            (labels[1].clone(), identity),
        ]));
        let selected = core.computation_record_projection(module, labels[1].clone());
        let forced = core.computation_force(argument);
        let applied = core.computation_application(forced, right);
        let applied = core.computation_bind(selected, applied);
        let evaluated =
            eval_computation(&core, &mut domain, definitions, ample(), applied).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the projected function applies");
        };
        assert!(matches!(
            domain.value(value),
            Some(DomainValue::Injection {
                side: Side::Right,
                ..
            })
        ));
        let poisoned = core.computation_record_projection(module, labels[0].clone());
        let poisoned = core.computation_bind(poisoned, forced);
        assert_eq!(
            eval_computation(&core, &mut domain, definitions, ample(), poisoned),
            Err(EvalFault::ProjectedNonRecord)
        );

        // A constructor's classifier closes over the argument, not merely its
        // value fields. Readback must substitute that captured value index.
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let indexed = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
        let constructor =
            core.value_constructor(indexed, ConstructorTag::from(0_usize), Vec::from([source]));
        let returned = core.computation_return(constructor);
        let lambda = core.computation_lambda(returned);
        let applied = core.computation_application(lambda, unit);
        let evaluated =
            eval_computation(&core, &mut domain, definitions, ample(), applied).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("constructor introduction");
        };
        let normal = readback_value(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            value,
        )
        .unwrap();
        let Some(matched_native_node) = core.value(normal)
        else {
            panic!("native constructor survives normalization");
        };
        let Value::Constructor {
            ref datatype,
            ref fields,
            ..
        } = *matched_native_node
        else {
            panic!("native constructor survives normalization");
        };
        let Some(matched_native_node) = core.value_type(*datatype)
        else {
            panic!("native classifier survives normalization");
        };
        let ValueType::Data {
            ref declaration,
            ref arguments,
        } = *matched_native_node
        else {
            panic!("native classifier survives normalization");
        };
        assert_eq!(*declaration, ConstantIndex::from(3_usize));
        assert!(
            matches!(arguments.as_slice(),[argument] if matches!(core.value(*argument),Some(Value::Unit)))
        );
        assert!(
            matches!(fields.as_slice(),[field] if matches!(core.value(*field),Some(Value::Record(record)) if record.keys().eq(labels.iter())))
        );
    }

    #[test]
    fn native_cases_reapply_when_head_unfolds()
    {
        use alloc::collections::BTreeMap;
        use alloc::string::String;

        use gandr_core_term::ConstructorTag;
        use gandr_core_term::FieldLabel;
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let captured = core.value_injection(Side::Left, unit);
        let field = core.value_injection(Side::Right, unit);
        let label = FieldLabel::from(String::from("field"));
        let data = core.value_type_data(ConstantIndex::from(2_usize), Vec::new());
        let constructor =
            core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([field]));
        let record = core.value_record(BTreeMap::from([(label.clone(), field)]));
        let bound = core.value_variable(Zone::Intuitionistic, innermost());
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let motive_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
        let motive = core.comp_type_returner(motive_type);
        let index = core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([bound]));
        let result_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([index]));
        let pair = core.value_pair(outer, bound);
        let result = core.value_constructor(
            result_type,
            ConstructorTag::from(0_usize),
            Vec::from([pair]),
        );
        let returned = core.computation_return(result);
        let branch = core.computation_lambda(returned);
        let data_reference = core.value_constant(ConstantIndex::from(0_usize));
        let record_reference = core.value_constant(ConstantIndex::from(1_usize));
        let cased = core.computation_data_case(data_reference, motive, Vec::from([branch]));
        let projected = core.computation_record_projection(record_reference, label);
        let mut chain = DefinitionChain::new();
        for (constant, entry) in [(0_usize, 0_u32), (1, 1)] {
            chain
                .define(
                    ConstantIndex::from(constant),
                    GlobalIndex::from(entry),
                    Transparency::Manifest,
                    &[],
                )
                .unwrap();
        }
        let Ok(chain) = LoweredChain::lower(chain, |entry| {
            Ok::<_, Infallible>(if entry.constant() == ConstantIndex::from(0_usize) {
                constructor
            }
            else {
                record
            })
        });
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let held = eval_value(&core, &mut domain, definitions, ample(), captured).unwrap();
        let mut supplied = Environment::new();
        supplied.extend(Zone::Intuitionistic, held);
        let (stuck, _) =
            eval_comp_within(&core, &mut domain, definitions, ample(), cased, supplied).unwrap();
        let normal = crate::readback::readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::ZeroUnfold,
            ample(),
            stuck,
        )
        .unwrap();
        let Some(matched_native_node) = core.computation(normal)
        else {
            panic!("stuck native case keeps its eliminator");
        };
        let gandr_core_term::Computation::DataCase { ref motive, .. } = *matched_native_node
        else {
            panic!("stuck native case keeps its eliminator");
        };
        let Some(matched_native_node) = core.comp_type(*motive)
        else {
            panic!("motive returns a value");
        };
        let gandr_core_term::CompType::Returner(ref motive) = *matched_native_node
        else {
            panic!("motive returns a value");
        };
        let Some(matched_native_node) = core.value_type(*motive)
        else {
            panic!("dependent motive");
        };
        let ValueType::Data { ref arguments, .. } = *matched_native_node
        else {
            panic!("dependent motive");
        };
        assert!(
            matches!(arguments.as_slice(),[argument] if matches!(core.value(*argument),Some(Value::Variable {zone:Zone::Intuitionistic,index}) if *index == innermost())),
            "the motive's scrutinee binder must not become the captured value"
        );
        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(stuck)
        else {
            panic!("constant head is initially stuck");
        };
        let spine = Vec::from(domain.neutral(neutral).unwrap().spine());
        let head = eval_value(&core, &mut domain, definitions, ample(), constructor).unwrap();
        let (progress, _) = Evaluation::eliminate(definitions, head, &spine)
            .resume(&core, &mut domain, ample())
            .unwrap();
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("case reapplication finishes");
        };
        let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
        else {
            panic!("case returns its branch result");
        };
        let Some(&DomainValue::Constructor { fields, .. }) = domain.value(value)
        else {
            panic!("native result");
        };
        let [ref pair] = *(domain.fields(fields).unwrap())
        else {
            panic!("one result field");
        };
        let Some(&DomainValue::Pair { first, second, .. }) = domain.value(*pair)
        else {
            panic!("capture and payload pair");
        };
        assert!(matches!(
            domain.value(first),
            Some(DomainValue::Injection {
                side: Side::Left,
                ..
            })
        ));
        assert!(matches!(
            domain.value(second),
            Some(DomainValue::Injection {
                side: Side::Right,
                ..
            })
        ));
        let projected =
            eval_computation(&core, &mut domain, definitions, ample(), projected).unwrap();
        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(projected)
        else {
            panic!("record constant is initially stuck");
        };
        let spine = Vec::from(domain.neutral(neutral).unwrap().spine());
        let head = eval_value(&core, &mut domain, definitions, ample(), record).unwrap();
        let (progress, _) = Evaluation::eliminate(definitions, head, &spine)
            .resume(&core, &mut domain, ample())
            .unwrap();
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("projection reapplication finishes");
        };
        let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
        else {
            panic!("projection returns its field");
        };
        assert!(matches!(
            domain.value(value),
            Some(DomainValue::Injection {
                side: Side::Right,
                ..
            })
        ));
    }
}
