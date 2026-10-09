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
//! # Source sharing is expanded, not preserved
//!
//! A core term is a DAG, and this machine walks it as a tree: a node reached
//! twice is evaluated twice. That is the cost the duplication policy and the
//! memo seam exist to remove, and removing it here — with an ad-hoc cache keyed
//! on the source node — would put a sharing decision inside the evaluator
//! rather than behind the parameter that is supposed to own it.
//!
//! The consequence is stated rather than left to be discovered: a term whose
//! sharing is deep costs its **expansion**, and the fuel budget is what bounds
//! that rather than a promise that it will not happen.
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
use crate::domain::LiftTarget;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;

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
    /// An internal invariant broke: a frame found no operand where one of its
    /// own tasks should have left one, or a task named an environment the
    /// machine does not hold. Unreachable while the machine's own pushes are
    /// the only source of tasks; reported rather than asserted, so a future
    /// frame that miscounts surfaces as a refusal instead of a wrong
    /// answer.
    MachineInvariant,
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
    /// - requires: `scope` is a scope of `environment`, and `environment` was
    ///   built over `chain`; an unknown scope is admissible and reads as
    ///   unfolding nothing.
    /// - ensures: the three travel together thereafter, so no later call can
    ///   pair a chain with another run's scope.
    /// - provides: the one bundle every unfolding question is asked of, which
    ///   is what keeps a call site from reaching the root scope by accident.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
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
    #[inline]
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
    #[spec(ensures: |ret| ret.as_ref().ok().copied() == self.envs.get(id.0))]
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
    #[spec(ensures: |ret| ret.as_ref().ok() == self.envs.get(id.0))]
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
    #[spec(
        captures: [entry_len = self.values.len(), entry_last = self.values.last().copied()],
        ensures: |ret| ret.as_ref().ok().copied() == entry_last
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
    #[spec(
        captures: [entry_len = self.comps.len(), entry_last = self.comps.last().copied()],
        ensures: |ret| ret.as_ref().ok().copied() == entry_last
            && self.comps.len() == entry_len.saturating_sub(1_usize),
    )]
    fn pop_comp(&mut self) -> Result<DomainCompId, EvalFault>
    {
        self.comps.pop().ok_or(EvalFault::MachineInvariant)
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
    #[inline]
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
///   face, spine length and appended elimination against the source's, and the
///   source's own spine length unchanged; the source spine's contents would
///   need an owned entry snapshot, which the pinned expansion evaluates even in
///   a non-enforcing build.
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
#[spec(
    captures: [
        entry_form = domain
            .neutral(neutral)
            .map(|held| (held.head(), held.unfolding(), held.spine().len())),
    ],
    ensures: |ret| match ret {
        | Ok(fresh) => {
            domain
                .neutral(fresh)
                .map(|held| (held.head(), held.unfolding(), held.spine().len()))
                == entry_form.map(|form| (form.0, form.1, form.2.saturating_add(1_usize)))
                && domain.neutral(fresh).and_then(|held| held.spine().last().copied())
                    == Some(elimination)
                && domain.neutral(neutral).map(|held| held.spine().len())
                    == entry_form.map(|form| form.2)
        },
        | Err(_) => entry_form.is_none(),
    },
)]
fn extend_spine(
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
/// - fails: every variant of [`EvalFault`]; a refusal mints nothing the caller
///   can observe, because the ids it would have returned are never handed back.
///   [`EvalFault::DanglingTerm`] is publicly reachable: a term id minted by one
///   core arena and evaluated against another names no node there.
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
    let mut machine = Machine::new(definitions, fuel);
    let env = machine.hold_env(environment);
    machine.tasks.push(Task::Comp { term, env });
    run(core, domain, &mut machine)?;
    let produced = machine.pop_comp()?;
    Ok((produced, machine.fuel))
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
    ensures: |ret| ret.is_err() || machine.tasks.is_empty(),
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
/// - requires: `task` was popped from `machine`'s own stack, so its operands
///   are on the result stacks.
/// - ensures: the task's result is pushed on the stack of its own polarity, or
///   further tasks are pushed that will produce it.
/// - provides: the machine's whole transition relation, one arm per source
///   former plus one per assembly frame. This block stays prose: an assembly
///   frame pops its operands in the same step that pushes its result, so no
///   relation between the entry and exit stack lengths states that the result
///   is pushed on the stack of its own polarity, and the operand precondition
///   is a statement about the frame that popped the task.
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
fn step(
    core: &CoreArena,
    domain: &mut DomainArena,
    machine: &mut Machine<'_>,
    task: Task,
) -> Result<(), EvalFault>
{
    match task {
        | Task::Value { term, env } => step_value(core, domain, machine, term, env),
        | Task::Comp { term, env } => step_comp(core, domain, machine, term, env),
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
        | Task::Bind { body, env } => step_bind(domain, machine, body, env),
        | Task::Case {
            on_left,
            on_right,
            env,
        } => step_case(domain, machine, on_left, on_right, env),
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
/// - hypothesis: L3 — the decision surface is the seven-arm match plus the
///   variable and constant lookups, separated by one case per arm — the leaf
///   arms and the lift arm included, the last being the only one that holds a
///   level and so the only producer of the level family — an index past the
///   environment, and a constant at each unfolding stance.
/// - witness: `eval::tests::an_unreduced_composite_keeps_its_source_face`
/// - witness: `eval::tests::the_leaf_and_lift_arms_evaluate_and_keep_their_faces`
/// - witness: `eval::tests::a_lift_over_a_substituted_body_loses_its_face`
/// - witness: `eval::tests::a_variable_resolves_out_of_the_environment`
/// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
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
        | Value::Thunk(body) => {
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
/// - requires: one value result on the stack.
/// - ensures: a thunk pushes a task entering its closure, so the forced
///   computation's weak head becomes this task's result; a stuck value grows
///   its neutral's spine by one `force`.
/// - provides: the `force` rule. The clause states the consumed value result
///   and the two admissible outcomes — one task entering the closure, or one
///   computation result; that the stuck outcome's spine grew by exactly one
///   `force` is a judgement over the produced graph, and the witnesses below
///   carry it.
/// - fails: [`EvalFault::ForcedNonThunk`] for any other value, which is an
///   ill-typed input this crate does not re-derive types to exclude.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   forcing a thunk, forcing a neutral, and forcing a pair.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
#[spec(
    requires: !machine.values.is_empty(),
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
            machine.tasks.push(Task::Comp { term, env });
            Ok(())
        },
        | DomainValue::Neutral { neutral, .. } => {
            let grown = extend_spine(domain, neutral, Elimination::Force)?;
            machine
                .comps
                .push(domain.comp_neutral(grown, CompTermFace::Reduced));
            Ok(())
        },
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
        | DomainValue::Injection { .. }
        | DomainValue::Lift { .. } => Err(EvalFault::ForcedNonThunk),
    }
}

/// Apply the weak head on the stack to the value on the stack.
///
/// # Specification
/// - requires: one computation result and one value result on the stacks.
/// - ensures: a lambda pushes a task entering its closure with the argument
///   bound in the intuitionistic zone; a neutral grows its spine by one
///   application.
/// - provides: the β rule and its stuck case, which are one arm apart. The
///   clause states the consumed argument and head results and the two
///   admissible outcomes — one task entering the closure, or one computation
///   result standing for the grown neutral; that the stuck outcome's spine grew
///   by exactly one application is a judgement over the produced graph, and the
///   witnesses below carry it.
/// - fails: [`EvalFault::AppliedNonFunction`] when the head is a returner.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-way match, separated by
///   applying a lambda, a neutral and a returner.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::an_ill_shaped_elimination_is_refused`
#[spec(
    requires: [!machine.comps.is_empty(), !machine.values.is_empty()],
    captures: [
        entry_values = machine.values.len(),
        entry_comps = machine.comps.len(),
        entry_tasks = machine.tasks.len(),
    ],
    ensures: |ret| ret.is_err()
        || (machine.values.len() == entry_values.saturating_sub(1_usize)
            && ((machine.tasks.len() == entry_tasks.saturating_add(1_usize)
                && machine.comps.len() == entry_comps.saturating_sub(1_usize))
                || (machine.comps.len() == entry_comps
                    && machine.tasks.len() == entry_tasks))),
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
            machine.tasks.push(Task::Comp { term, env });
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
        | DomainValue::Unit { .. }
        | DomainValue::Literal { .. }
        | DomainValue::Pair { .. }
        | DomainValue::Thunk { .. }
        | DomainValue::Lift { .. } => Err(EvalFault::CasedNonInjection),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::convert::Infallible;

    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::ScopeId;
    use gandr_core_term::Transparency;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use super::Definitions;
    use super::EvalFault;
    use super::Fuel;
    use super::LoweredChain;
    use super::eval_comp_within;
    use super::eval_computation;
    use super::eval_value;
    use super::face_of;
    use crate::arena::DomainArena;
    use crate::closure::Environment;
    use crate::domain::CompTermFace;
    use crate::domain::DomainComp;
    use crate::domain::DomainValue;
    use crate::domain::Elimination;
    use crate::domain::LevelEntry;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;

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
}
