//! The L machine: an environment machine stepping commands over the
//! two-region [`Store`].
//!
//! A run is a loop over one control state, each iteration one transition:
//!
//! ```text
//! run ⟨p |ε c⟩ ρ        p a μ, unless ε is − and c a μ̃:
//!                         load c, bind α to its mark, run the μ's body
//!                       otherwise: evaluate p to a value, deliver it to c
//! deliver v α ρ         return v to the mark α reads
//! deliver v ★ ρ         return v to the base of the frame region
//! deliver v μ̃x.s ρ      run s with x bound to v
//! deliver v case ρ      run the arm of v's constructor, its fields bound
//! deliver v datacase(t̄; c) ρ
//!                       v = K_i(w̄): load c, push apply(w̄), force t_i
//! deliver v D(ā; c) ρ   load c, observe v by D with the arguments ā
//! deliver v select[f](c) ρ
//!                       v a tuple or a record: deliver its field f to c
//! return v m            shrink the frame region to m, then pop
//! pop v                 the top frame receives v; an empty region halts
//! ```
//!
//! Loading a consumer pushes the frames it denotes and answers the mark of
//! the continuation it names: a chain of destructor frames over a
//! covariable or `★` shrinks to that base first, and one over a `μ̃` or a
//! match pushes onto the current region. Observing a thunk by `force` opens
//! its memo cell: a forced cell returns its cached value, an opened one
//! pushes an update frame under the body's return point, and a re-entrant one
//! runs the body inline. A recursive thunk whose body returns a copattern
//! object follows the same protocol, its body running with the thunk itself
//! bound innermost; any other recursive thunk, a loop, unfolds against the
//! forcing continuation with no frame of its own. Observing a copattern
//! object runs the arm its destructor selects. A suspended `μ` delivered
//! anywhere but to a `μ̃` runs against the consumer it meets.
//!
//! Producers evaluate to heap values without a transition: constructors
//! allocate their evaluated fields, a thunk or a cached recursive thunk
//! allocates a fresh cell, a copattern object or a `μ` closes over the
//! environment, and a constant unfolds its [`Definition`] once per machine, a
//! cycle among definitions stopping the run. Every walk is a loop over an
//! explicit stack.
//!
//! # Ordinary continuations are marks
//!
//! `Machine::run` is a loop over one control state — run a cut, deliver a value
//! to a consumer, return a value to a mark, pop the top frame — each iteration
//! one transition against the caller's `StepCount`:
//!
//! ```text
//! run ⟨μα.s |ε c⟩ ρ      load c, bind α to its mark, run s      (not at ε = − against a μ̃)
//! run ⟨p |ε c⟩ ρ         evaluate p, deliver it to c
//! deliver v α            return v to α's mark       deliver v ★        return v to the base
//! deliver v μ̃x.s         run s with x bound to v    deliver v case     run v's arm, fields bound
//! deliver v D(ā; c)      load c, observe v by D     return v m         shrink to m, pop
//! deliver c_i(v̄) datacase(b̄; c)                     load c, push apply(v_j) for each field, force b_i
//! deliver K(v̄) select[f](c)                          deliver the field f names to c, reading
//!                                                     the width from K
//! ```
//!
//! Loading a consumer pushes the frames it denotes: a chain of destructor
//! frames over a covariable or `★` first shrinks the region to that base, and
//! one over a `μ̃` or a match pushes onto the current top. A covariable binds
//! the mark of the continuation it names, so returning through it is a shrink
//! to that mark, and a mark whose frame has since been popped and replaced is
//! refused as stale by the store. Forcing a thunk follows its cell: a forced
//! cell returns its cached value, an opened one pushes an update frame under
//! the body's return point, a re-entrant one runs the body inline; a cached
//! recursive thunk does the same with itself bound innermost, and a loop
//! unfolds with itself bound innermost and no frame. A `μ` against a `μ̃` at a
//! negative cut is suspended and bound, the call-by-name side of the critical
//! pair; everywhere else the `μ` runs first. Producers evaluate within a
//! transition — a constructor over its evaluated fields, a thunk or a cached
//! recursive thunk with a fresh cell, a loop with none, a copattern object or
//! a `μ` closed over the environment — and a constant unfolds its definition
//! once per machine, a cycle among definitions stopping the run as
//! `Stuck::CyclicConstant`.
//!
//! Ordinary covariables use marks into the one frame region; values and
//! environments use shared heap addresses, and the caller supplies the step
//! budget. First-class capture copies only the delimited frame segment into an
//! immutable heap stack. Copying every ordinary continuation would add work
//! where no capture occurs; opaque continuation closures would prevent
//! structural handler dispatch. Revisit that split only if measured capture
//! workloads justify another shared frame representation.
//!
//! # Fixpoints
//!
//! A core fixpoint `fix x. M` focuses to a recursive thunk, `fix{x; force(α) ⇒
//! 𝓕⟦M⟧α}`: a thunk whose body binds one producer, the thunk itself, innermost,
//! besides its return point. Forcing it binds the forced value itself as `x`,
//! so a self reference is an address in the environment and the heap stays
//! acyclic and append-only. What forcing does next follows the body. A body
//! that returns a copattern object at once — a recursive function, or a lazy
//! record — gets a memo cell like any thunk and the same cell protocol: the
//! cell caches the object, which no argument changes. Any other body, a loop
//! at a computation type such as `F A`, gets no cell: forcing unfolds `fix x.
//! M` to `M[thunk (fix x. M)/x]` against the forcing continuation, pushing
//! nothing, so a body that forces itself in tail position re-enters with the
//! continuation it was forced with. A nominal match `case_D v {b̄}` delivers
//! `c_i(v̄)` to `datacase(b̄; c)` by loading `c`, pushing one application frame
//! per field, the first on top, and forcing `b_i`: the core's case-β, `b_i`
//! applied to `v̄`.
//!
//! The machine unfolds a fixpoint when it is forced; `core-nbe` unfolds one
//! when it is applied to a canonical argument. The two strategies agree on a
//! closed first-order answer, and the differential compares them over Nat, List
//! and a Tree with a function field. **Choice.** A recursive thunk, rather than
//! a refusal, which leaves every recursive program without a runner; a cell
//! only for a body that returns a copattern object, since a loop's body
//! returns nothing to cache. The recorded design binds every recursive thunk
//! through the ordinary memo cell. Around a loop that cell's update frame
//! memoizes a result that does not exist yet and stands for the loop's whole
//! run, so an inner loop left by a `break` that re-enters the outer one, or a
//! `become` inside a loop, leaves one frame under every further iteration;
//! unfolding holds none, which is the loop's constant continuation.
//! **Alternatives.** A cell for every fixpoint, the recorded design, holds the
//! frame above. No cell for any fixpoint re-closes a recursive function's
//! object at every call for no gain. Unrolling the fixpoint a bounded number
//! of times hands the machine a term that diverges from the core at the bound.
//! A cyclic environment — `x` bound to a closure over the environment that
//! binds it — breaks the append-only heap the readback walks in address order.
//! Self-application through a recursive type needs types the IL does not carry.
//! A nominal match's branches as pattern arms binding the fields would strip
//! each branch's `λ`s, which is not total: a branch is any computation of the
//! function type. **Reversal.** A loop whose result a later force should share
//! — the thunk escaping its own body and forced again after the loop returned
//! — would want the cell back for that body shape.
//!
//! # Effects and delimited control
//!
//! Effect requests carry an inline signature, an operation name and a live
//! payload. An anonymous request is decided by the nearest delimiter: a
//! matching handler captures its own frame and the intervening continuation; a
//! nonmatching handler or a reset offers the request to the host rather than
//! searching an outer handler. Matching uses both interface and operation
//! names, so unrelated interfaces cannot intercept each other's equally named
//! operations.
//!
//! A handler that introduces a capability (the core's `Scope`) allocates a
//! fresh `HeapValue::Capability`, binds it in its subject and records its
//! address in its frame. An exercise through that capability is lexical: it
//! captures up to the frame carrying the same address, across every reset and
//! handler above it, so an inner handler of the same interface cannot claim
//! it. An exercise through a capability no handler introduced — a host
//! constant — is offered to the host.
//!
//! A shift captures through the nearest reachable reset, across every handler
//! frame above it, as the checker types a shift against the nearest reset
//! across handler frames. A shift that discards its stack therefore unwinds
//! those handlers without running their return clauses: the lowering spells
//! an early `return` out of a handled subject this way.
//!
//! Captured stacks are immutable frame slices over shared heap addresses.
//! Resume copies the frames onto the ambient continuation, making capture
//! multishot and deep handling explicit. Local returns inside delimiters fall
//! through the reinstalled stack instead of retaining stale absolute marks.
//! Memo updates crossed by capture or a host offer are declined: effectful
//! forcing cannot cache a context-dependent reply. Pure forcing keeps the cell
//! protocol.
//!
//! `Machine::run_with_host` offers only unclaimed operations. `HostValues`
//! permits inspection, allocation and structural readback without exposing
//! continuation mutation. A reply resumes the original stack once, `Abort`
//! terminates without resuming, and `Decline` retains `Stuck::PerformNoHandler`
//! at the request. The adapter owns external effects, reply typing and policy;
//! the machine performs no host I/O itself. Shared heap replies preserve thunk
//! and continuation identity without refocusing a copied source term.
//!
//! Literal stacks retain independent frame scopes and read back exactly;
//! captured delimiter frames have no literal-stack spelling and return
//! `ReadbackRefusal::NonLiteralStack`, never an invented value. Lazy pairs use
//! two projection copatterns and evaluate only the selected branch.
//!
//! **Choice.** Qualified interface-and-operation dispatch prevents equal
//! operation names from crossing distinct interfaces. The alternative,
//! operation-name-only matching, cannot preserve inline interface identity.
//! Multi-shot captures keep immutable frame sequences and shared heap addresses
//! rather than cloning payload values. Revisit multiplicity only if the type
//! system makes resumptions explicitly one-shot; revisit unqualified dispatch
//! only with globally unique operation identities.
//!
//! Witnesses: `machine::tests::hand_built_effect_cases_agree`,
//! `machine::tests::hand_built_shift_cases_agree`,
//! `machine::tests::a_shift_unwinds_the_handlers_above_its_reset`,
//! `machine::tests::an_exercise_reaches_the_scope_that_introduced_its_capability`,
//! the eight `host_seam_*` tests,
//! `machine::tests::handler_resumption_under_projection_uses_the_ambient_continuation_once`,
//! `machine::tests::the_assert_handler_runs_combinator_assertions`,
//! `machine::tests::the_assert_handler_reports_a_failure`,
//! `machine::tests::a_mock_exec_handler_replaces_a_real_command`, and
//! `machine::tests::literal_stacks_close_flat_frame_scopes_and_resume_in_order`.
//! These directed outcomes cover runtime control independently of the pure NBE
//! oracle, which refuses effect and control instructions by former.
//!
//! # Temporary access
//!
//! A hold binds its evaluated value in the environment's linear chain and
//! runs its body; the binding is the held value's one cell, and a read of
//! it copies the value it holds now. An access looks up the held binding,
//! binds a view holding the value it holds, and pushes one
//! [`Frame::Access`] above its loaded continuation before its body runs. A
//! resume evaluates the value it writes back and records it on that frame;
//! an abort records that it ran. The frame's pop does what was recorded:
//! a resume's value is written into the held binding and the answer passes
//! on; an abort pushes [`Frame::Answer`] and runs the unwind, whose unit
//! that frame discards for the answer, writing nothing. Nothing is
//! allocated per access beyond the view's binding and the frame; an
//! eliminator returns a fresh unit.
//!
//! An eliminator finds its frame by the view's binding, the nearest frame
//! naming it, so a captured stack resumed later still ends its own access.
//! A stack resumed twice replays the access twice: the checker refuses a
//! capture naming a view, and a handler outside the access that resumes its
//! continuation twice is the multi-shot case the linear zone does not yet
//! govern. An access whose body answers with its view unended is stuck as
//! [`Stuck::Unended`]; the checker refuses such a body.
//!
//! Witnesses:
//! `machine::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`,
//! `store::tests::a_linear_binding_is_written_in_place`,
//! `store::tests::a_view_ends_once_on_its_own_frame`.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ProducerArity;
use crate::boundary::StepCount;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::Introduces;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Route;
use crate::il::Selector;
use crate::readback::ReadbackRefusal;
use crate::readback::read_back_terminal;
use crate::readback::read_back_value;
use crate::store::ContinuationMark;
use crate::store::Ending;
use crate::store::Environment;
use crate::store::ForceEntry;
use crate::store::Frame;
use crate::store::HeapValue;
use crate::store::HeapValueId;
use crate::store::Introduced;
use crate::store::Memo;
use crate::store::Store;
use crate::store::StoreFault;
use crate::store::ValueBindingId;

/// What a constant stands for when a run meets it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Definition
{
    /// A definition with a body: its focused value, closed.
    Transparent(ProducerId),
    /// A declaration with no body to run, owed or refused, which a run
    /// carries as itself.
    Opaque,
}

/// The definitions a run unfolds, by admission position.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Definitions
{
    /// Each constant's definition, at its admission position.
    entries: Vec<Definition>,
}

impl Definitions
{
    /// No definitions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Admit the next definition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the definition is admitted at the next position, which is
    ///   returned.
    /// - provides: the one way a constant gets a definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant admitted transparent unfolds, one admitted
    ///   opaque is carried as itself, and a position never admitted stops the
    ///   run.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    #[inline]
    #[spec(
        captures: [entry = self.entries.len()],
        ensures: |ret| usize::from(ret) == entry && entry.checked_add(1) == Some(self.entries.len())
            && self.entries.get(entry) == Some(&definition),
    )]
    pub fn push(
        &mut self,
        definition: Definition,
    ) -> ConstantIndex
    {
        let position = ConstantIndex::from(self.entries.len());
        self.entries.push(definition);
        position
    }

    /// The definition admitted at a position, or `None`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> Option<Definition>
    {
        self.entries.get(usize::from(constant)).copied()
    }

    /// How many definitions are admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> crate::NodeCount
    {
        crate::NodeCount::from(self.entries.len())
    }
}

/// Why a run stopped short of a value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Stuck
{
    /// No reachable source handler or host accepted this operation.
    PerformNoHandler(CommandId),
    /// No reset is reachable across the structural continuation prefix.
    ShiftNoReset(CommandId),
    /// A resumption was supplied a value which is not a first-class stack.
    ResumedNonStack
    {
        /// The resumption command.
        at: CommandId,
        /// The supplied value.
        value: HeapValueId,
    },
    /// A native operation refused its arguments, including zero division.
    Primitive(gandr_core_term::primitive::PrimitiveError),
    /// A native operand has no scalar interpretation, retaining its blame site.
    NonScalar(HeapValueId),
    /// A producer variable no binding of the environment answers.
    UnboundVariable
    {
        /// The variable's zone.
        zone: Zone,
        /// The variable's index.
        index: DeBruijnIndex,
    },
    /// A covariable no binding of the environment answers.
    UnboundCovariable(CovariableIndex),
    /// A constant with no admitted definition.
    UndefinedConstant(ConstantIndex),
    /// A constant whose definition needs its own value.
    CyclicConstant(ConstantIndex),
    /// A destructor met a value it cannot observe.
    Unobservable
    {
        /// The value.
        value: HeapValueId,
        /// The destructor.
        head: DestructorTag,
    },
    /// A match, a fold or a selection has no arm for the value it met: a
    /// selection meets something other than a tuple or a record, or one
    /// without the component or the label it names.
    Unmatched
    {
        /// The value.
        value: HeapValueId,
        /// The match, the fold or the selection.
        arms: ConsumerId,
    },
    /// A command the arena does not hold.
    IllFormedCommand(CommandId),
    /// A producer the arena does not hold, or one whose children contradict
    /// its head.
    IllFormedProducer(ProducerId),
    /// A consumer the arena does not hold, or one whose children contradict
    /// its head.
    IllFormedConsumer(ConsumerId),
    /// An access answered with its view never ended: neither eliminator ran.
    Unended(ValueBindingId),
}

impl fmt::Display for Stuck
{
    /// Names what stopped the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::PerformNoHandler(at) => write!(f, "operation at command {at} has no handler"),
            Self::ShiftNoReset(at) => write!(f, "shift at command {at} has no reset"),
            Self::ResumedNonStack { at, value } => {
                write!(f, "resume at command {at} received non-stack value {value}")
            },
            Self::Primitive(error) => write!(f, "native operation: {error}"),
            Self::NonScalar(value) => write!(f, "native operand {value} is not a scalar"),
            Self::UnboundVariable { index, .. } => {
                write!(f, "variable {} is unbound", u32::from(index))
            },
            Self::UnboundCovariable(index) => write!(f, "covariable {index} is unbound"),
            Self::UndefinedConstant(constant) => {
                write!(f, "constant {} has no definition", usize::from(constant))
            },
            Self::CyclicConstant(constant) => {
                write!(f, "constant {} needs its own value", usize::from(constant))
            },
            Self::Unobservable { value, .. } => write!(f, "value {value} cannot be observed"),
            Self::Unmatched { value, arms } => {
                write!(f, "match {arms} has no arm for value {value}")
            },
            Self::IllFormedCommand(id) => write!(f, "command {id} is not well formed"),
            Self::IllFormedProducer(id) => write!(f, "producer {id} is not well formed"),
            Self::IllFormedConsumer(id) => write!(f, "consumer {id} is not well formed"),
            Self::Unended(view) => write!(f, "view {view} reached its access's end unended"),
        }
    }
}

/// How a run ended.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// The value returned to an empty frame region.
    Halted(HeapValueId),
    /// The run stopped short of a value.
    Stuck(Stuck),
}

/// An operation not claimed by the nearest source delimiter.
#[derive(Clone, Copy, Debug)]
pub struct HostRequest<'request>
{
    /// The inline interface; its type handles belong to
    /// `HostValues::annotations`.
    pub signature: &'request gandr_core_term::effect::EffectSig,
    /// The requested operation within that interface.
    pub operation: &'request gandr_core_term::effect::OperationName,
    /// The live payload, retaining thunk and continuation identity.
    pub payload: HeapValueId,
}

/// A host decision about one operation offer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostReply<Abort>
{
    /// Deliver an existing or newly allocated heap value to the live
    /// continuation.
    Resume(HeapValueId),
    /// Stop without resuming, carrying the host's termination result.
    Abort(Abort),
    /// Leave the operation unhandled, retaining its Perform blame site.
    Decline,
}

/// A source-machine outcome or an explicit non-resuming host termination.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostOutcome<Abort>
{
    /// Ordinary machine completion or source-language stuckness.
    Completed(Outcome),
    /// An adapter chose to terminate instead of replying.
    Aborted(Abort),
}

/// Interpret operation offers without access to continuation mutation.
pub trait HostHandler
{
    /// The adapter's non-resuming termination result, such as a process exit
    /// code.
    type Abort;

    /// Decide one unclaimed operation; source-claimed operations never call
    /// this.
    ///
    /// # Specification
    /// - requires: a resumed value belongs to the supplied heap and has the
    ///   operation's reply type. The adapter owns external effects and policy.
    /// - ensures: a reply continues the original stack, an abort stops it, and
    ///   decline names this operation as unhandled. The machine never retries.
    /// - executable: none — the trait states the adapter's obligation; each
    ///   body is an implementor's, and the machine checks what it receives at
    ///   the resumption.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scripted hosts that resume, abort and decline,
    ///   offered operations claimed and unclaimed by source handlers, separate
    ///   a retried, misrouted or silently dropped decision.
    /// - witness: `machine::tests::host_seam_resumes_a_single_unhandled_perform`
    /// - witness: `machine::tests::host_seam_decline_blames_perform_no_handler`
    /// - witness: `machine::tests::host_seam_never_consulted_for_a_claimed_perform`
    /// - witness: `machine::tests::host_abort_never_resumes_and_missing_replies_fault`
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>;
}

/// The host's value capability: inspect, allocate and read back, never alter
/// frames.
pub struct HostValues<'run>
{
    /// Immutable focused code and interface annotations.
    arena: &'run CommandArena,
    /// The current heap; continuation access stays private to the machine.
    store: &'run mut Store,
}

impl HostValues<'_>
{
    /// The arena owning the offered interface's type handles.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn annotations(&self) -> &CoreArena
    {
        self.arena.annotations()
    }

    /// Inspect a live payload or previously allocated reply.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        value: HeapValueId,
    ) -> Option<&HeapValue>
    {
        self.store.value(value)
    }

    /// Allocate a reply node over already allocated children.
    ///
    /// # Errors
    /// Heap address space exhaustion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn allocate(
        &mut self,
        value: HeapValue,
    ) -> Result<HeapValueId, StoreFault>
    {
        self.store.allocate(value)
    }

    /// Read a payload structurally, closing captured thunk and stack-frame
    /// values.
    ///
    /// # Errors
    /// The readback refusal names a dangling value, suspended capture or
    /// runtime continuation outside flat literal-stack syntax. No
    /// placeholder is emitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn read_back_value(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ValueId, crate::readback::ReadbackRefusal>
    {
        crate::readback::read_back_value(self.arena, self.store, value, core)
    }
}

/// The pure entry point explicitly declines every unclaimed operation.
struct NoHost;

impl HostHandler for NoHost
{
    type Abort = core::convert::Infallible;

    /// Do not interpret an external operation in a host-free run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        HostReply::Decline
    }
}

/// Why a run could not go on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MachineFault
{
    /// The step budget ran out.
    OutOfSteps,
    /// The store refused an operation.
    Store(StoreFault),
}

impl fmt::Display for MachineFault
{
    /// Names the fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::OutOfSteps => f.write_str("the step budget ran out"),
            Self::Store(fault) => write!(f, "the store refused: {fault}"),
        }
    }
}

impl core::error::Error for MachineFault
{
}

impl From<StoreFault> for MachineFault
{
    /// Carries the store's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: StoreFault) -> Self
    {
        Self::Store(fault)
    }
}

/// What stops a transition: the run is stuck, or it faulted.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Stop
{
    /// The run is stuck.
    Stuck(Stuck),
    /// The run faulted.
    Fault(MachineFault),
}

impl From<Stuck> for Stop
{
    /// Stops on a stuck state.
    ///
    /// # Specification
    /// trivial.
    fn from(stuck: Stuck) -> Self
    {
        Self::Stuck(stuck)
    }
}

impl From<StoreFault> for Stop
{
    /// Stops on a store fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: StoreFault) -> Self
    {
        Self::Fault(MachineFault::Store(fault))
    }
}

/// The machine's control state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Control
{
    /// Run a command under an environment.
    Run(CommandId, Environment),
    /// Hand a value to a consumer under an environment.
    Deliver(HeapValueId, ConsumerId, Environment),
    /// Fold one native cell with the caller continuation already loaded.
    ListFold(HeapValueId, ConsumerId, Environment),
    /// Return a value to the continuation at a mark.
    Return(HeapValueId, ContinuationMark),
    /// Hand a value to the top of the frame region.
    Pop(HeapValueId),
}

/// What one transition leads to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Next
{
    /// An unclaimed operation offered below the complete live continuation.
    Host
    {
        /// The Perform instruction carrying its interface and operation.
        at: CommandId,
        /// The fully evaluated, untruncated payload.
        payload: HeapValueId,
    },
    /// The next control state.
    Continue(Control),
    /// The run halted with a value.
    Halt(HeapValueId),
}

/// How far a constant's unfolding has got.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unfolding
{
    /// Not yet met.
    Pending,
    /// Being evaluated: meeting it again is a cycle.
    Running,
    /// Evaluated, to this value.
    Done(HeapValueId),
}

/// The position of a field in a constructed value, counted from the left.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FieldPosition(usize);

/// One pending unit of producer evaluation.
#[derive(Clone, Copy, Debug)]
enum Evaluation
{
    /// Assemble a stack after its eager application operands are evaluated.
    Reify(ProducerId, Environment),
    /// Apply a table operation to the evaluated operands.
    Primitive(ProducerId),
    /// Evaluate a producer under an environment; leaves one value.
    Producer(ProducerId, Environment),
    /// Pop a constructor's evaluated fields and allocate it.
    Construct(ProducerId),
    /// Record the value on top as a constant's.
    Remember(ConstantIndex, ProducerId),
}

/// The L machine over one arena and its definitions.
#[derive(Clone, Debug)]
pub struct Machine<'program>
{
    /// The commands run.
    arena: &'program CommandArena,
    /// The constants' definitions.
    definitions: &'program Definitions,
    /// The heap and frame regions.
    store: Store,
    /// Each constant's unfolding, by admission position.
    unfoldings: Vec<Unfolding>,
}

impl<'program> Machine<'program>
{
    /// A machine with an empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        arena: &'program CommandArena,
        definitions: &'program Definitions,
    ) -> Self
    {
        Self {
            arena,
            definitions,
            store: Store::new(),
            unfoldings: alloc::vec![Unfolding::Pending; usize::from(definitions.len())],
        }
    }

    /// The store, for readback and inspection.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn store(&self) -> &Store
    {
        &self.store
    }

    /// Read a run's terminal back as a core computation.
    ///
    /// # Specification
    /// - requires: `value` is a value this machine's runs allocated.
    /// - ensures: on success `return v` for a positive value `v`, and the
    ///   function a copattern object denotes; a thunk's or a function's body is
    ///   decoded and closed over its captured environment's readbacks.
    /// - provides: the readback of a halted run.
    /// - fails: [`ReadbackRefusal`] naming the first value with no core
    ///   reading; `core` is then exactly as on entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function and a thunk read back closed over their
    ///   environments, and a suspended capture is refused with the core arena
    ///   back at its mark.
    /// - witness: `machine::tests::a_function_terminal_reads_back_closed_over_its_environment`
    /// - witness: `machine::tests::a_thunk_reads_back_closed_over_its_environment`
    /// - witness: `machine::tests::a_suspended_capture_has_no_reading`
    #[inline]
    #[spec(
        requires: self.store.value(value).is_some(),
        captures: [entry = core.watermark()],
        ensures: |ret| match ret {
            | Ok(read) => core.computation(read).is_some(),
            | Err(_) => core.watermark() == entry,
        },
    )]
    pub fn read_back(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ComputationId, ReadbackRefusal>
    {
        read_back_terminal(self.arena, &self.store, value, core)
    }

    /// Read a positive value back as a core value.
    ///
    /// # Specification
    /// - requires: as [`Self::read_back`].
    /// - ensures: on success the closed core value `value` denotes.
    /// - provides: the readback of a value, such as a constant's.
    /// - fails: as [`Self::read_back`], and for a closure, with the same
    ///   rollback.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read_back`].
    /// - witness: `machine::tests::a_thunk_reads_back_closed_over_its_environment`
    #[inline]
    #[spec(
        requires: self.store.value(value).is_some(),
        captures: [entry = core.watermark()],
        ensures: |ret| match ret {
            | Ok(read) => core.value(read).is_some(),
            | Err(_) => core.watermark() == entry,
        },
    )]
    pub fn read_back_value(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ValueId, ReadbackRefusal>
    {
        read_back_value(self.arena, &self.store, value, core)
    }

    /// Run a command from an empty frame region.
    ///
    /// # Specification
    /// - requires: `command` passes [`check_command`](crate::check_command)
    ///   closed; otherwise the run may stop [`Outcome::Stuck`] on what the
    ///   check would refuse.
    /// - ensures: the frame region is first shrunk to its base, declining every
    ///   forcing an earlier run abandoned; then [`Outcome::Halted`] with the
    ///   value returned to the empty region, or [`Outcome::Stuck`] naming what
    ///   stopped the run. The heap and the constants' values persist across
    ///   runs of one machine.
    /// - provides: the L machine's one entry.
    /// - fails: [`MachineFault::OutOfSteps`] after `budget` transitions, and
    ///   [`MachineFault::Store`] when the store refuses an operation.
    /// - panics: none.
    /// - intension: one loop iteration per transition; producer evaluation is
    ///   linear in the producer's size and runs within a transition.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated closed pure terms and stuck outcomes are
    ///   compared with the independent normaliser. L3 — hand-built formers, the
    ///   polarity-sensitive critical pair, exact budget boundaries and nominal
    ///   memo observations distinguish wrong reductions and ordering; this
    ///   covers the bounded generator and named cases, not all programs.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::force_runs_a_thunk_body`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::application_binds_the_argument`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    #[inline]
    #[spec(ensures: |ref ret| match ret.as_ref() {
        | Ok(&Outcome::Halted(value)) => usize::from(budget) > 0 && self.store.value(value).is_some()
            && self.store.mark() == ContinuationMark::BASE,
        | Ok(&Outcome::Stuck(_)) => usize::from(budget) > 0,
        | Err(_) => true,
    })]
    pub fn run(
        &mut self,
        command: CommandId,
        budget: StepCount,
    ) -> Result<Outcome, MachineFault>
    {
        match self.run_with_host(command, budget, &mut NoHost)? {
            HostOutcome::Completed(outcome) => Ok(outcome),
            HostOutcome::Aborted(never) => match never {},
        }
    }

    /// Run with an explicit adapter for operations not claimed by source
    /// handlers.
    ///
    /// # Specification
    /// - ensures: callbacks see the complete live payload and are called once
    ///   per unclaimed perform, in evaluation order. Replies continue the
    ///   unchanged stack, including nonmatching handlers; a claimed perform
    ///   never calls out. Abort does not resume, and decline returns
    ///   `PerformNoHandler` at the offer.
    /// - fails: the same budget and store faults as `Self::run`, including a
    ///   dangling root address supplied as a host reply.
    /// - panics: only if the host callback panics.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered offers, deep re-entry, payload capture and a
    ///   later arithmetic computation distinguish replay, truncation and
    ///   discarded replies.
    /// - witness: `machine::tests::host_seam_offers_deep_re_entry_in_order`
    /// - witness: `machine::tests::host_seam_offers_across_a_non_matching_handler`
    /// - witness: `machine::tests::host_seam_never_consulted_for_a_claimed_perform`
    /// - witness: `machine::tests::host_seam_reply_flows_into_subsequent_computation`
    /// - witness: `machine::tests::host_seam_higher_order_payload_reads_back_exactly`
    #[spec(ensures: |ref ret| match ret.as_ref() {
        Ok(&HostOutcome::Completed(Outcome::Halted(value))) => usize::from(budget) > 0 && self.store.value(value).is_some() && self.store.mark() == ContinuationMark::BASE,
        Ok(_) => usize::from(budget) > 0,
        Err(_) => true,
    })]
    #[inline]
    pub fn run_with_host<H>(
        &mut self,
        command: CommandId,
        budget: StepCount,
        host: &mut H,
    ) -> Result<HostOutcome<H::Abort>, MachineFault>
    where
        H: HostHandler + ?Sized,
    {
        self.store.shrink_to(ContinuationMark::BASE)?;
        let mut control = Control::Run(command, Environment::EMPTY);
        let mut remaining = usize::from(budget);
        loop {
            remaining = remaining.checked_sub(1).ok_or(MachineFault::OutOfSteps)?;
            match self.step(control) {
                Ok(Next::Continue(next)) => control = next,
                Ok(Next::Halt(value)) => {
                    return Ok(HostOutcome::Completed(Outcome::Halted(value)));
                },
                Ok(Next::Host { at, payload }) => {
                    let Some(request) = self.arena.command(at)
                    else {
                        return Ok(HostOutcome::Completed(Outcome::Stuck(
                            Stuck::IllFormedCommand(at),
                        )));
                    };
                    let CommandNode::Perform {
                        ref signature,
                        ref operation,
                        ..
                    } = *request
                    else {
                        return Ok(HostOutcome::Completed(Outcome::Stuck(
                            Stuck::IllFormedCommand(at),
                        )));
                    };
                    let reply = host.handle(
                        HostRequest {
                            signature,
                            operation,
                            payload,
                        },
                        &mut HostValues {
                            arena: self.arena,
                            store: &mut self.store,
                        },
                    );
                    match reply {
                        HostReply::Resume(value) => {
                            self.store
                                .value(value)
                                .ok_or(StoreFault::DanglingValue(value))?;
                            control = Control::Pop(value);
                        },
                        HostReply::Abort(abort) => return Ok(HostOutcome::Aborted(abort)),
                        HostReply::Decline => {
                            return Ok(HostOutcome::Completed(Outcome::Stuck(
                                Stuck::PerformNoHandler(at),
                            )));
                        },
                    }
                },
                Err(Stop::Stuck(stuck)) => {
                    return Ok(HostOutcome::Completed(Outcome::Stuck(stuck)));
                },
                Err(Stop::Fault(fault)) => return Err(fault),
            }
        }
    }

    /// One transition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the transition the module documentation's table gives.
    /// - provides: the machine's step relation.
    /// - fails: a stuck state or a store fault.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the return path has an exact transition budget,
    ///   reentrant forcing shares the update continuation, and a halted run has
    ///   no frames. L2 — composed reductions compare with an independent
    ///   normaliser, distinguishing swapped control states and skipped returns.
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ref ret| match (control, ret.as_ref().copied()) {
        | (Control::Return(value, mark), Ok(next)) => next == Next::Continue(Control::Pop(value)) && self.store.mark() == mark,
        | (Control::Pop(value), Ok(Next::Halt(held))) => held == value && self.store.mark() == ContinuationMark::BASE,
        | (Control::Run(..) | Control::Deliver(..), Ok(Next::Halt(_))) => false,
        | _ => true,
    })]
    fn step(
        &mut self,
        control: Control,
    ) -> Result<Next, Stop>
    {
        match control {
            Control::Run(command, environment) => self.cut(command, environment),
            Control::ListFold(value, consumer, environment) => {
                self.list_fold(value, consumer, environment)
            },
            Control::Deliver(value, consumer, environment) => {
                self.deliver(value, consumer, environment)
            },
            Control::Return(value, mark) => {
                self.store.shrink_to(mark)?;
                Ok(Next::Continue(Control::Pop(value)))
            },
            Control::Pop(value) => self.pop(value),
        }
    }

    /// Run a cut.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `μ` producer runs its body against its loaded consumer,
    ///   except at a negative cut against a `μ̃`, where it is suspended and
    ///   bound; any other producer is evaluated and delivered.
    /// - provides: the critical pair's resolution by the cut's polarity.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one closed capture whose body would get stuck is cut
    ///   against an ignoring binder at each polarity. The positive cut is stuck
    ///   and the negative cut returns unit, distinguishing the critical pair,
    ///   not merely the shape of the next control state. Missing commands have
    ///   exact refusals. L2 — pure reductions compare with normalisation.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ref ret| match ret.as_ref().copied() {
        | Err(_) => self.arena.command(id).is_some() || *ret == Err(Stop::Stuck(Stuck::IllFormedCommand(id))),
        | Ok(next) => self.arena.command(id).is_some_and(|node| {
            let &CommandNode::Cut { polarity, producer, consumer } = node else { return matches!(next, Next::Continue(Control::Run(..) | Control::Deliver(..)) | Next::Host { .. }); };
            let strict_capture = self.arena.producer(producer).and_then(|node| match *node {
                | ProducerNode::Mu { body } if polarity != Polarity::Negative
                    || !matches!(self.arena.consumer(consumer), Some(&ConsumerNode::MuTilde { .. })) => Some(body),
                | _ => None,
            });
            match (strict_capture, next) {
                | (Some(body), Next::Continue(Control::Run(found, inner))) => body == found
                    && inner.values() == environment.values()
                    && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.return_continuation(self.store.mark())),
                | (None, Next::Continue(Control::Deliver(value, found, inner))) => consumer == found
                    && inner == environment && self.store.value(value).is_some(),
                | _ => false,
            }
        }),
    })]
    fn cut(
        &mut self,
        id: CommandId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let &CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } = arena.command(id).ok_or(Stuck::IllFormedCommand(id))?
        else {
            return self.control_command(id, environment);
        };
        if let Some(&ProducerNode::Mu { body }) = arena.producer(producer) {
            let by_name = polarity == Polarity::Negative
                && matches!(
                    arena.consumer(consumer),
                    Some(&ConsumerNode::MuTilde { .. })
                );
            if !by_name {
                let mark = self.load(consumer, environment)?;
                let inner = self
                    .store
                    .bind_covalue(environment, self.store.return_continuation(mark))?;
                return Ok(Next::Continue(Control::Run(body, inner)));
            }
        }
        let value = self.evaluate(producer, environment)?;
        Ok(Next::Continue(Control::Deliver(
            value,
            consumer,
            environment,
        )))
    }

    /// Enter an effect, delimited-control or memory instruction.
    ///
    /// # Specification
    /// - ensures: each body receives a fresh local return; reset and handler
    ///   install their delimiter, resume reinstalls its reusable prefix, and
    ///   perform or shift capture only through the nearest eligible delimiter.
    ///   A hold binds its value linearly; an access binds its view and pushes
    ///   its frame; an eliminator records its view's ending on that frame and
    ///   delivers the unit to its continuation.
    /// - fails: malformed instructions, absent delimiters, non-stack
    ///   resumptions, an unbound linear index, a view with no live access or
    ///   one ended already, and the store's capacity or stale-mark faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — deep re-entry, repeated resumption and an ambient
    ///   projection distinguish lost delimiters, destructive captures and
    ///   duplicated tails; a counter resumed and aborted distinguishes a
    ///   write-back from none.
    /// - witness: `machine::tests::hand_built_effect_cases_agree`
    /// - witness: `machine::tests::hand_built_shift_cases_agree`
    /// - witness: `machine::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|next| match *next {
        Next::Host { at, payload } => at == id && self.store.value(payload).is_some(),
        Next::Continue(Control::Run(body, inner)) => self.arena.command(body).is_some()
            && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(crate::store::Covalue::FallThrough),
        Next::Continue(Control::Deliver(unit, found, inner)) => inner == environment
            && self.store.value(unit).is_some()
            && matches!(self.arena.command(id), Some(&CommandNode::Memory { continuation, .. }) if continuation == found),
        Next::Continue(_) | Next::Halt(_) => false,
    }))]
    fn control_command(
        &mut self,
        id: CommandId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let node = arena.command(id).ok_or(Stuck::IllFormedCommand(id))?;
        match *node {
            CommandNode::Cut { .. } => Err(Stuck::IllFormedCommand(id).into()),
            CommandNode::Perform {
                route,
                payload,
                continuation,
                ..
            } => {
                self.load(continuation, environment)?;
                let through = match route {
                    Route::Nearest => Introduced::Nothing,
                    Route::Capability(capability) => {
                        Introduced::Capability(self.evaluate(capability, environment)?)
                    },
                };
                let payload = self.evaluate(payload, environment)?;
                self.perform(id, through, payload)
            },
            CommandNode::Handle {
                introduces,
                subject,
                continuation,
                ..
            } => {
                self.load(continuation, environment)?;
                let (introduced, scope) = match introduces {
                    Introduces::Nothing => (Introduced::Nothing, environment),
                    Introduces::Capability => {
                        let capability = self.store.allocate(HeapValue::Capability)?;
                        (
                            Introduced::Capability(capability),
                            self.store.bind_value(environment, capability)?,
                        )
                    },
                };
                self.store.push_frame(Frame::Handler {
                    command: id,
                    environment,
                    introduced,
                })?;
                let inner = self
                    .store
                    .bind_covalue(scope, crate::store::Covalue::FallThrough)?;
                Ok(Next::Continue(Control::Run(subject, inner)))
            },
            CommandNode::Reset { body, continuation } => {
                self.load(continuation, environment)?;
                self.store.push_frame(Frame::Reset)?;
                let inner = self
                    .store
                    .bind_covalue(environment, crate::store::Covalue::FallThrough)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            CommandNode::Shift { body, continuation } => {
                self.load(continuation, environment)?;
                self.shift(id, body, environment)
            },
            CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                self.load(continuation, environment)?;
                let stack = self.evaluate(stack, environment)?;
                self.replay_stack(id, stack)?;
                let inner = self
                    .store
                    .bind_covalue(environment, crate::store::Covalue::FallThrough)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            CommandNode::Memory {
                ref form,
                continuation,
            } => self.memory(form, continuation, environment),
        }
    }

    /// Enter a memory instruction.
    ///
    /// # Specification
    /// - ensures: a hold loads its continuation and runs its body with the held
    ///   value bound innermost in the linear chain; an access binds a view
    ///   holding what the held binding holds now, pushes its open
    ///   [`Frame::Access`] above its loaded continuation and runs its body; a
    ///   resume records its evaluated value on its view's frame and an abort
    ///   records that it ran, each then delivering a fresh unit to its
    ///   continuation.
    /// - fails: [`Stuck::UnboundVariable`] for a linear index past the chain;
    ///   the store's [`StoreFault::NoAccess`] or [`StoreFault::Ended`] for an
    ///   eliminator; an evaluation's or the store's capacity faults.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a counter resumed with its successor reads one after,
    ///   and one aborted reads what it held, its unwind run once.
    /// - witness: `machine::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(ensures: |ref ret| ret.is_err() || match *form {
        | MemoryForm::Hold { .. } | MemoryForm::Access { .. } => matches!(ret, Ok(Next::Continue(Control::Run(..)))),
        | MemoryForm::Resume { .. } | MemoryForm::Abort { .. } => matches!(ret, Ok(Next::Continue(Control::Deliver(_, found, inner))) if *found == continuation && *inner == environment),
    })]
    fn memory(
        &mut self,
        form: &MemoryForm<ProducerId, CommandId>,
        continuation: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let resident = |index: DeBruijnIndex, store: &Store| {
            store
                .lookup_linear(environment, index)
                .ok_or(Stuck::UnboundVariable {
                    zone: Zone::Linear,
                    index,
                })
        };
        let (view, ending) = match *form {
            MemoryForm::Hold { value, body } => {
                self.load(continuation, environment)?;
                let held = self.evaluate(value, environment)?;
                let (scope, _) = self.store.bind_linear(environment, held)?;
                let inner = self
                    .store
                    .bind_covalue(scope, crate::store::Covalue::FallThrough)?;
                return Ok(Next::Continue(Control::Run(body, inner)));
            },
            MemoryForm::Access { held, body, unwind } => {
                let cell = resident(held, &self.store)?;
                let lent = self
                    .store
                    .linear(cell)
                    .ok_or(StoreFault::DanglingBinding(cell))?;
                self.load(continuation, environment)?;
                let (scope, view) = self.store.bind_linear(environment, lent)?;
                self.store.push_frame(Frame::Access {
                    held: cell,
                    view,
                    unwind,
                    environment,
                    ending: Ending::Open,
                })?;
                let inner = self
                    .store
                    .bind_covalue(scope, crate::store::Covalue::FallThrough)?;
                return Ok(Next::Continue(Control::Run(body, inner)));
            },
            MemoryForm::Resume { view, value } => {
                let view = resident(view, &self.store)?;
                (view, Ending::Resumed(self.evaluate(value, environment)?))
            },
            MemoryForm::Abort { view } => (resident(view, &self.store)?, Ending::Aborted),
        };
        self.store.settle(view, ending)?;
        let unit = self.store.allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            fields: Box::from([]),
        })?;
        Ok(Next::Continue(Control::Deliver(
            unit,
            continuation,
            environment,
        )))
    }

    /// Capture a claimed operation, or offer it with its live continuation
    /// intact.
    ///
    /// # Specification
    /// - ensures: an anonymous request is decided by the nearest delimiter: a
    ///   matching interface and operation capture that handler and its inner
    ///   frames. An exercise through a capability a handler introduced captures
    ///   that handler's frame and every frame above it, whatever stands
    ///   between; one through any other capability, which only the host holds,
    ///   is offered to the host. Clauses bind payload then resumption and
    ///   return to the ambient tail. Unclaimed operations retain every frame
    ///   for the host reply.
    /// - fails: malformed handler instructions, an introduced capability whose
    ///   handler's frame is gone, and store faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — matching and nonmatching nested handlers, repeated
    ///   resumes, same-named operations from distinct interfaces, and an
    ///   exercise past an inner handler of the same interface separate
    ///   dispatch.
    /// - witness: `machine::tests::hand_built_effect_cases_agree`
    /// - witness: `machine::tests::handler_resumption_under_projection_uses_the_ambient_continuation_once`
    /// - witness: `machine::tests::an_exercise_reaches_the_scope_that_introduced_its_capability`
    /// - witness: `machine::tests::host_seam_answers_an_exercise_through_a_capability_it_holds`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|next| match *next {
        Next::Host { at: found, payload: found_payload } => found == at && found_payload == payload,
        Next::Continue(Control::Run(_, inner)) => self.store.lookup_value(inner, DeBruijnIndex::from(1_u32)) == Some(payload)
            && self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)).is_some_and(|stack|
                matches!(self.store.value(stack), Some(HeapValue::Stack { frames }) if matches!(frames.first(), Some(Frame::Handler { .. })))),
        Next::Continue(_) | Next::Halt(_) => false,
    }))]
    fn perform(
        &mut self,
        at: CommandId,
        through: Introduced,
        payload: HeapValueId,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let request = arena.command(at).ok_or(Stuck::IllFormedCommand(at))?;
        let CommandNode::Perform {
            ref signature,
            ref operation,
            ..
        } = *request
        else {
            return Err(Stuck::IllFormedCommand(at).into());
        };
        let introduced = match through {
            Introduced::Capability(capability)
                if matches!(self.store.value(capability), Some(&HeapValue::Capability)) =>
            {
                Introduced::Capability(capability)
            },
            Introduced::Capability(_) => {
                self.store.cancel_updates(ContinuationMark::BASE)?;
                return Ok(Next::Host { at, payload });
            },
            Introduced::Nothing => Introduced::Nothing,
        };
        let mut selected = None;
        for (index, frame) in self.store.frames().enumerate().rev() {
            match (*frame, introduced) {
                (Frame::Reset, Introduced::Nothing) => break,
                (
                    Frame::Handler {
                        command,
                        environment,
                        introduced: installed,
                    },
                    _,
                ) if introduced == Introduced::Nothing || installed == introduced => {
                    let handler = arena
                        .command(command)
                        .ok_or(Stuck::IllFormedCommand(command))?;
                    let CommandNode::Handle {
                        signature: ref handled,
                        ref clauses,
                        ..
                    } = *handler
                    else {
                        return Err(Stuck::IllFormedCommand(command).into());
                    };
                    if handled.name() == signature.name()
                        && let Some(clause) =
                            clauses.iter().find(|clause| &clause.operation == operation)
                    {
                        selected =
                            Some((crate::FrameHeight::from(index), environment, clause.body));
                    }
                    break;
                },
                _ => {},
            }
        }
        let Some((height, environment, body)) = selected
        else {
            if let Introduced::Capability(_) = introduced {
                return Err(Stuck::PerformNoHandler(at).into());
            }
            self.store.cancel_updates(ContinuationMark::BASE)?;
            return Ok(Next::Host { at, payload });
        };
        let base = self
            .store
            .mark_below(height)
            .ok_or(Stuck::IllFormedCommand(at))?;
        let stack = self.store.capture(base)?;
        let inner = self.store.bind_value(environment, payload)?;
        let inner = self.store.bind_value(inner, stack)?;
        let inner = self
            .store
            .bind_covalue(inner, crate::store::Covalue::FallThrough)?;
        Ok(Next::Continue(Control::Run(body, inner)))
    }

    /// Capture through the nearest reset, across every handler frame above
    /// it.
    ///
    /// # Specification
    /// - ensures: the shift body receives a reusable stack including its reset
    ///   and every handler frame above it, while the active continuation
    ///   becomes exactly the tail below that reset: a shift whose body never
    ///   resumes the stack unwinds those handlers, their return clauses not
    ///   run.
    /// - fails: a missing reachable reset and store faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested prompts, a handler between the shift and its
    ///   reset, and repeated resumption distinguish shallow capture, a handler
    ///   barrier and one-shot or missing reset behavior.
    /// - witness: `machine::tests::hand_built_shift_cases_agree`
    /// - witness: `machine::tests::a_shift_unwinds_the_handlers_above_its_reset`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|next|
        matches!(*next, Next::Continue(Control::Run(found, inner)) if found == body
            && self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)).is_some_and(|stack|
                matches!(self.store.value(stack), Some(HeapValue::Stack { frames }) if frames.first() == Some(&Frame::Reset))))))]
    fn shift(
        &mut self,
        at: CommandId,
        body: CommandId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let height = self
            .store
            .frames()
            .enumerate()
            .rev()
            .find_map(|(index, frame)| {
                (*frame == Frame::Reset).then(|| crate::FrameHeight::from(index))
            })
            .ok_or(Stuck::ShiftNoReset(at))?;
        let base = self
            .store
            .mark_below(height)
            .ok_or(Stuck::ShiftNoReset(at))?;
        let stack = self.store.capture(base)?;
        let inner = self.store.bind_value(environment, stack)?;
        let inner = self
            .store
            .bind_covalue(inner, crate::store::Covalue::FallThrough)?;
        Ok(Next::Continue(Control::Run(body, inner)))
    }

    /// Append a first-class continuation without consuming its reusable
    /// capture.
    ///
    /// # Specification
    /// - ensures: the saved frames appear above the caller in their original
    ///   order.
    /// - fails: a non-stack value or exhausted frame serials.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two resumes with different replies and an outer
    ///   projection distinguish destructive consumption, reversed frames and
    ///   lost tails. The predicate reads the region's height and its top frames
    ///   from the top down, as many as the capture holds, so it reads none of
    ///   the caller's frames beneath them.
    /// - witness: `machine::tests::handler_resumption_under_projection_uses_the_ambient_continuation_once`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body pushes every captured frame once; the check compares each pushed frame once, from the top"
        )
    )]
    #[spec(captures: height = usize::from(self.store.frame_height()), ensures: |ref ret| ret.is_err()
        || matches!(self.store.value(stack), Some(HeapValue::Stack { frames })
            if height.checked_add(frames.len()) == Some(usize::from(self.store.frame_height()))
                && self.store.frames().rev().take(frames.len()).eq(frames.iter().rev())))]
    fn replay_stack(
        &mut self,
        at: CommandId,
        stack: HeapValueId,
    ) -> Result<(), Stop>
    {
        let value = self
            .store
            .value(stack)
            .ok_or(Stuck::ResumedNonStack { at, value: stack })?;
        let HeapValue::Stack { ref frames } = *value
        else {
            return Err(Stuck::ResumedNonStack { at, value: stack }.into());
        };
        let count = frames.len();
        for index in 0 .. count {
            let frame = match self.store.value(stack) {
                Some(&HeapValue::Stack { ref frames }) => frames.get(index).copied(),
                _ => None,
            }
            .ok_or(Stuck::ResumedNonStack { at, value: stack })?;
            self.store.push_frame(frame)?;
        }
        Ok(())
    }

    /// Evaluate a native observation's bounded operand without allocating a
    /// box.
    ///
    /// # Specification
    /// - ensures: force and projection carry no operand; application carries
    ///   its one evaluated argument, retaining the consumer's blame on a wrong
    ///   arity.
    /// - fails: malformed observation arity or producer evaluation failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force, projection and application exercise each
    ///   native arity.
    /// - witness: `machine::tests::hand_built_shift_cases_agree`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|arguments|
        arguments.as_slice().len() == usize::from(tag.producer_arity()) && arguments.as_slice().iter().all(|&value| self.store.value(value).is_some())))]
    fn observation_arguments(
        &mut self,
        at: ConsumerId,
        tag: DestructorTag,
        producers: &[ProducerId],
        environment: Environment,
    ) -> Result<crate::store::ObservationArguments, Stop>
    {
        match (tag, producers) {
            (DestructorTag::Force | DestructorTag::Project(_), &[]) => {
                Ok(crate::store::ObservationArguments::Nullary)
            },
            (DestructorTag::Apply, &[argument]) => Ok(crate::store::ObservationArguments::Unary(
                self.evaluate(argument, environment)?,
            )),
            _ => Err(Stuck::IllFormedConsumer(at).into()),
        }
    }

    /// Hand a value to a consumer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the delivery rows of the module documentation's table; a
    ///   suspended `μ` met by anything but a `μ̃` runs against it.
    /// - provides: the consumer side of a cut.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct return, binding, matching, forcing and the
    ///   polarity-sensitive capture have distinct terminal or stuck outcomes;
    ///   unbound and missing consumers have exact refusals. L2 — generated pure
    ///   spines compare with normalisation. These observe consumer dispatch,
    ///   environment extension and continuation selection.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    /// - witness: `machine::tests::a_selection_reads_the_width_of_the_value_it_meets`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&next|
        self.arena.consumer(consumer).is_some_and(|node| {
            if let Some((body, captured)) = self.suspended_capture(value)
                && !matches!(node, &ConsumerNode::MuTilde { .. }) {
                return matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                    && inner.values() == captured.values()
                    && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.return_continuation(self.store.mark())));
            }
            match *node {
                | ConsumerNode::Top => next == Next::Continue(Control::Return(value, ContinuationMark::BASE)),
                | ConsumerNode::Covariable(index) => match self.store.lookup_covalue(environment, index) {
                    Some(crate::store::Covalue::Pinned(mark)) => next == Next::Continue(Control::Return(value, mark)),
                    Some(crate::store::Covalue::FallThrough) => next == Next::Continue(Control::Pop(value)),
                    None => false,
                },
                | ConsumerNode::MuTilde { body } => matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                    && inner.covalues() == environment.covalues()
                    && self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)) == Some(value)),
                | ConsumerNode::Case { .. } => matches!(next, Next::Continue(Control::Run(..))),
                | ConsumerNode::ListFold { .. } => matches!(next, Next::Continue(Control::ListFold(..))),
                | ConsumerNode::DataCase { .. } | ConsumerNode::Destructor { .. } => matches!(next, Next::Continue(Control::Run(..) | Control::Return(..))),
                | ConsumerNode::Select { then, .. } => matches!(next, Next::Continue(Control::Deliver(_, found, inner)) if found == then && inner == environment),
            }
        })))]
    fn deliver(
        &mut self,
        value: HeapValueId,
        consumer: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let node = arena
            .consumer(consumer)
            .ok_or(Stuck::IllFormedConsumer(consumer))?;
        if let Some((body, captured)) = self.suspended_capture(value)
            && !matches!(*node, ConsumerNode::MuTilde { .. })
        {
            let mark = self.load(consumer, environment)?;
            let inner = self
                .store
                .bind_covalue(captured, self.store.return_continuation(mark))?;
            return Ok(Next::Continue(Control::Run(body, inner)));
        }
        match *node {
            ConsumerNode::Covariable(index) => {
                let mark = self
                    .store
                    .lookup_covalue(environment, index)
                    .ok_or(Stuck::UnboundCovariable(index))?;
                Ok(Next::Continue(match mark {
                    crate::store::Covalue::Pinned(mark) => Control::Return(value, mark),
                    crate::store::Covalue::FallThrough => Control::Pop(value),
                }))
            },
            ConsumerNode::Top => Ok(Next::Continue(Control::Return(
                value,
                ContinuationMark::BASE,
            ))),
            ConsumerNode::MuTilde { body } => {
                let inner = self.store.bind_value(environment, value)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            ConsumerNode::Case { .. } | ConsumerNode::DataCase { .. } => {
                self.select(value, consumer, environment)
            },
            ConsumerNode::ListFold { continuation, .. } => {
                let _mark = self.load(continuation, environment)?;
                Ok(Next::Continue(Control::ListFold(
                    value,
                    consumer,
                    environment,
                )))
            },
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let &[then] = consumers.as_ref()
                else {
                    return Err(Stuck::IllFormedConsumer(consumer).into());
                };
                let arguments =
                    self.observation_arguments(consumer, tag, producers, environment)?;
                let mark = self.load(then, environment)?;
                self.observe(value, tag, arguments.as_slice(), mark)
            },
            ConsumerNode::Select { then, .. } => {
                let field = self.selection(value, consumer)?;
                Ok(Next::Continue(Control::Deliver(field, then, environment)))
            },
        }
    }

    /// Fold one native cell without using the Rust call stack.
    ///
    /// # Specification
    /// - requires: the fold's caller continuation is the current frame region.
    /// - ensures: nil enters the empty branch; a cell folds its tail before
    ///   entering the cell branch with head at index one and result at zero.
    /// - fails: a non-list value or malformed fold consumer is named.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — asymmetric list elements and an outer binder
    ///   distinguish reversed traversal, reversed branch binders and capture.
    /// - witness: `machine::tests::native_list_fold_preserves_order_and_outer_scope`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Next::Continue(Control::Run(..) | Control::ListFold(..)))))]
    fn list_fold(
        &mut self,
        value: HeapValueId,
        fold: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let Some(&ConsumerNode::ListFold {
            on_nil, on_cons, ..
        }) = self.arena.consumer(fold)
        else {
            return Err(Stuck::IllFormedConsumer(fold).into());
        };
        let node = self
            .store
            .value(value)
            .ok_or(Stuck::Unmatched { value, arms: fold })?;
        let HeapValue::Constructed {
            ref tag,
            ref fields,
        } = *node
        else {
            return Err(Stuck::Unmatched { value, arms: fold }.into());
        };
        match (tag, fields.as_ref()) {
            (&crate::il::ConstructorTag::ListNil, &[]) => {
                let inner = self.store.bind_covalue(
                    environment,
                    self.store.return_continuation(self.store.mark()),
                )?;
                Ok(Next::Continue(Control::Run(on_nil, inner)))
            },
            (&crate::il::ConstructorTag::ListCons, &[head, tail]) => {
                let inner = self.store.bind_value(environment, head)?;
                let inner = self
                    .store
                    .bind_covalue(inner, self.store.return_continuation(self.store.mark()))?;
                self.store.push_frame(Frame::Bind {
                    body: on_cons,
                    environment: inner,
                })?;
                Ok(Next::Continue(Control::ListFold(tail, fold, environment)))
            },
            _ => Err(Stuck::Unmatched { value, arms: fold }.into()),
        }
    }

    /// The body and environment of a suspended `μ`, when `value` is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the body and captured environment exactly when the held value
    ///   is a closure of a present capture producer; otherwise none.
    /// - provides: delayed capture recognition before ordinary delivery.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — delaying a capture at a negative cut and later
    ///   delivering one to a non-binder distinguish eager capture dispatch from
    ///   ordinary closures. Missing and non-capture values return none.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    #[spec(ensures: |ret| ret == match self.store.value(value) {
        | Some(&HeapValue::Closure { producer, environment }) => match self.arena.producer(producer) {
            | Some(&ProducerNode::Mu { body }) => Some((body, environment)),
            | _ => None,
        },
        | _ => None,
    })]
    fn suspended_capture(
        &self,
        value: HeapValueId,
    ) -> Option<(CommandId, Environment)>
    {
        let &HeapValue::Closure {
            producer,
            environment,
        } = self.store.value(value)?
        else {
            return None;
        };
        let arena = self.arena;
        let &ProducerNode::Mu { body } = arena.producer(producer)?
        else {
            return None;
        };
        Some((body, environment))
    }

    /// Hand a value to the top frame, or halt on an empty region.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a destructor frame observes the value, a binder frame binds
    ///   it, a match frame selects on it, a selection frame passes its field
    ///   on, and an update frame writes it back to its cell and passes it on.
    ///   An access frame whose view resumed writes the resumed value into its
    ///   held binding and passes the value on; one whose view aborted runs its
    ///   unwind under an answer frame, which passes the value on in place of
    ///   the unwind's unit.
    /// - provides: returning into the frame region.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returning through bind, match, destructor and update
    ///   frames is observed by the resulting value and memo cell; an empty
    ///   region halts at the exact return budget. Reentrant forcing
    ///   distinguishes duplicate updates and skipped write-back; a counter
    ///   resumed and aborted distinguishes a write-back from none.
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::a_selection_reads_the_width_of_the_value_it_meets`
    /// - witness: `machine::tests::a_counter_observes_write_back_on_resume_and_none_on_abort`
    #[spec(
        captures: [height = self.store.frame_height()],
        ensures: |ref ret| if usize::from(height) == 0 { *ret == Ok(Next::Halt(value)) }
            else { !matches!(ret, &Ok(Next::Halt(_))) },
    )]
    fn pop(
        &mut self,
        value: HeapValueId,
    ) -> Result<Next, Stop>
    {
        let Some(frame) = self.store.pop_frame()
        else {
            return Ok(Next::Halt(value));
        };
        match frame {
            Frame::Reset | Frame::DeclinedUpdate => Ok(Next::Continue(Control::Pop(value))),
            Frame::Handler {
                command,
                environment,
                ..
            } => {
                let Some(&CommandNode::Handle { on_return, .. }) = self.arena.command(command)
                else {
                    return Err(Stuck::IllFormedCommand(command).into());
                };
                let inner = self.store.bind_value(environment, value)?;
                let inner = self
                    .store
                    .bind_covalue(inner, crate::store::Covalue::FallThrough)?;
                Ok(Next::Continue(Control::Run(on_return, inner)))
            },
            Frame::Destructor { tag, arguments } => {
                let mark = self.store.mark();
                self.observe(value, tag, arguments.as_slice(), mark)
            },
            Frame::Bind { body, environment } => {
                let inner = self.store.bind_value(environment, value)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            Frame::Case { arms, environment } => self.select(value, arms, environment),
            Frame::ListFold { fold, environment } => self.list_fold(value, fold, environment),
            Frame::Select { select } => {
                let field = self.selection(value, select)?;
                Ok(Next::Continue(Control::Pop(field)))
            },
            Frame::Update { cell } => {
                self.store.write_back(cell, value)?;
                Ok(Next::Continue(Control::Pop(value)))
            },
            Frame::Access {
                held,
                view,
                unwind,
                environment,
                ending,
            } => match ending {
                Ending::Resumed(written) => {
                    self.store.write_linear(held, written)?;
                    Ok(Next::Continue(Control::Pop(value)))
                },
                Ending::Aborted => {
                    self.store.push_frame(Frame::Answer { value })?;
                    let inner = self
                        .store
                        .bind_covalue(environment, crate::store::Covalue::FallThrough)?;
                    Ok(Next::Continue(Control::Run(unwind, inner)))
                },
                Ending::Open => Err(Stuck::Unended(view).into()),
            },
            Frame::Answer { value: answer } => Ok(Next::Continue(Control::Pop(answer))),
        }
    }

    /// Observe a value by a destructor, continuing at `mark`.
    ///
    /// # Specification
    /// - requires: the frame region's top is `mark`.
    /// - ensures: `force` on a thunk or a cached recursive thunk follows its
    ///   cell's protocol, a recursive thunk's body running with the thunk
    ///   itself bound innermost; `force` on a loop runs its body with itself
    ///   bound innermost and `mark` as its return point, pushing nothing; any
    ///   destructor on a copattern object runs the arm it selects with the
    ///   arguments and `mark` bound.
    /// - provides: the elimination of the negative values and thunks.
    /// - fails: [`Stuck::Unobservable`] for any other value or a missing arm,
    ///   and the store's faults.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first force, reentry and a cached force distinguish
    ///   the three cell states by continuation marks, the unique update frame
    ///   and exact cached address. Abandonment declines the update before a new
    ///   run. A recursive thunk computes through its own binding and a loop
    ///   through it re-enters with no frame, nested or under a function's tail
    ///   call. L2 — captured and curried functions compare with normal forms.
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::a_recursive_thunk_computes_through_its_own_binding`
    /// - witness: `machine::tests::a_loop_holds_no_frame_across_its_iterations`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
    #[spec(
        requires: self.store.mark() == mark,
        captures: [forcing = match self.store.value(value) {
            | Some(&HeapValue::Thunk { body, environment, cell }) if head == DestructorTag::Force =>
                Some((body, environment, cell, self.store.cell(cell), false)),
            | Some(&HeapValue::Fixpoint { body, environment, memo: crate::store::Memo::Cell(cell), .. }) if head == DestructorTag::Force =>
                Some((body, environment, cell, self.store.cell(cell), true)),
            | _ => None,
        }, unfolding = match self.store.value(value) {
            | Some(&HeapValue::Fixpoint { body, memo: crate::store::Memo::Unfolds, .. }) if head == DestructorTag::Force => Some(body),
            | _ => None,
        }],
        ensures: |ref ret| match ret.as_ref().copied() {
            | Err(_) => true,
            | Ok(next) => if let Some(body) = unfolding {
                matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                    && self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)) == Some(value)
                    && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.return_continuation(mark)))
                    && self.store.mark() == mark
            } else if let Some((body, captured, cell, state, recursive)) = forcing {
                match state {
                    | Some(crate::store::MemoState::Forced(cached)) => next == Next::Continue(Control::Return(cached, mark))
                        && self.store.cell(cell) == state && self.store.mark() == mark,
                    | Some(crate::store::MemoState::Unforced | crate::store::MemoState::InProgress) =>
                        matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                            && if recursive {
                                self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)) == Some(value)
                            } else { inner.values() == captured.values() }
                            && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.return_continuation(self.store.mark())))
                        && self.store.cell(cell) == Some(crate::store::MemoState::InProgress)
                        && if state == Some(crate::store::MemoState::Unforced) {
                            usize::from(mark.height()).checked_add(1) == Some(usize::from(self.store.frame_height()))
                        } else { self.store.mark() == mark },
                    | None => false,
                }
            } else {
                self.store.value(value).is_some_and(|held| match *held {
                    | HeapValue::Closure { producer, .. } => self.arena.producer(producer).is_some_and(|node|
                        matches!(*node, ProducerNode::Cocase { ref arms } if arms.iter().find(|arm| arm.destructor == head)
                            .is_some_and(|arm| matches!(next, Next::Continue(Control::Run(body, inner)) if body == arm.body
                                && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.return_continuation(mark))
                                && arguments.iter().rev().enumerate().all(|(position, argument)|
                                    u32::try_from(position).is_ok_and(|index|
                                        self.store.lookup_value(inner, DeBruijnIndex::from(index)) == Some(*argument))))))),
                    | _ => false,
                })
            },
        },
    )]
    fn observe(
        &mut self,
        value: HeapValueId,
        head: DestructorTag,
        arguments: &[HeapValueId],
        mark: ContinuationMark,
    ) -> Result<Next, Stop>
    {
        let unobservable = Stuck::Unobservable { value, head };
        match self.store.value(value) {
            Some(&HeapValue::Fixpoint {
                body,
                environment,
                memo: Memo::Unfolds,
                ..
            }) if head == DestructorTag::Force => {
                let captured = self.store.bind_value(environment, value)?;
                let inner = self
                    .store
                    .bind_covalue(captured, self.store.return_continuation(mark))?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            Some(
                &(HeapValue::Thunk {
                    body,
                    environment,
                    cell,
                }
                | HeapValue::Fixpoint {
                    body,
                    environment,
                    memo: Memo::Cell(cell),
                    ..
                }),
            ) if head == DestructorTag::Force => {
                let recursive =
                    matches!(self.store.value(value), Some(&HeapValue::Fixpoint { .. }));
                match self.store.begin_force(cell)? {
                    ForceEntry::Cached(cached) => Ok(Next::Continue(Control::Return(cached, mark))),
                    entry @ (ForceEntry::Opened | ForceEntry::Reentrant) => {
                        let captured = if recursive {
                            self.store.bind_value(environment, value)?
                        }
                        else {
                            environment
                        };
                        let returning = if entry == ForceEntry::Opened {
                            self.store.push_frame(Frame::Update { cell })?;
                            self.store.return_continuation(self.store.mark())
                        }
                        else {
                            self.store.return_continuation(mark)
                        };
                        let inner = self.store.bind_covalue(captured, returning)?;
                        Ok(Next::Continue(Control::Run(body, inner)))
                    },
                }
            },
            Some(&HeapValue::Closure {
                producer,
                environment,
            }) => {
                let arena = self.arena;
                let Some(object) = arena.producer(producer)
                else {
                    return Err(unobservable.into());
                };
                let ProducerNode::Cocase { ref arms } = *object
                else {
                    return Err(unobservable.into());
                };
                let arm = arms
                    .iter()
                    .find(|arm| arm.destructor == head)
                    .ok_or(unobservable)?;
                let mut inner = environment;
                for &argument in arguments {
                    inner = self.store.bind_value(inner, argument)?;
                }
                inner = self
                    .store
                    .bind_covalue(inner, self.store.return_continuation(mark))?;
                Ok(Next::Continue(Control::Run(arm.body, inner)))
            },
            _ => Err(unobservable.into()),
        }
    }

    /// Run the arm a match selects for a value: a structural match's arm with
    /// the fields bound left to right, or a nominal match's branch applied to
    /// them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a structural match, the arm of the value's constructor
    ///   runs under `environment` extended by the value's fields, the last
    ///   innermost; for a nominal match, as [`Self::branch`].
    /// - provides: the elimination of the constructed values.
    /// - fails: [`Stuck::Unmatched`] for a value that is not constructed or a
    ///   constructor no arm answers; [`Stuck::IllFormedConsumer`] when `arms`
    ///   is not a match.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair match returns both unequal fields in source
    ///   order after binding the last innermost, distinguishing omitted,
    ///   duplicated and reversed fields. Missing and non-match consumers and
    ///   unhandled heads have exact refusals; both sum injections are compared
    ///   independently in the pure-spine cases.
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `machine::tests::data_case_selects_arm_returns_three`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&next|
        self.arena.consumer(arms).zip(self.store.value(value)).is_some_and(|(node, held)|
            match (node, held) {
                | (&ConsumerNode::Case { arms: ref choices }, &HeapValue::Constructed { ref tag, ref fields }) =>
                    choices.iter().find(|arm| arm.constructor == *tag).is_some_and(|arm|
                        matches!(next, Next::Continue(Control::Run(body, inner)) if body == arm.body
                            && inner.covalues() == environment.covalues()
                            && fields.iter().rev().enumerate().all(|(position, field)|
                                u32::try_from(position).is_ok_and(|index|
                                    self.store.lookup_value(inner, DeBruijnIndex::from(index)) == Some(*field))))),
                | (&ConsumerNode::DataCase { .. }, &HeapValue::Constructed { tag: ConstructorTag::Data { .. }, .. }) =>
                    matches!(next, Next::Continue(Control::Run(..) | Control::Return(..))),
                | _ => false,
            })))]
    fn select(
        &mut self,
        value: HeapValueId,
        arms: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let Some(node) = arena.consumer(arms)
        else {
            return Err(Stuck::IllFormedConsumer(arms).into());
        };
        let choices = match *node {
            ConsumerNode::Case { arms: ref choices } => choices,
            ConsumerNode::DataCase { ref branches, then } => {
                return self.branch(value, arms, branches, then, environment);
            },
            ConsumerNode::Covariable(_)
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Destructor { .. }
            | ConsumerNode::ListFold { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::Top => return Err(Stuck::IllFormedConsumer(arms).into()),
        };
        let unmatched = Stuck::Unmatched { value, arms };
        let Some(held) = self.store.value(value)
        else {
            return Err(unmatched.into());
        };
        let HeapValue::Constructed { ref tag, .. } = *held
        else {
            return Err(unmatched.into());
        };
        let arm = choices
            .iter()
            .find(|arm| arm.constructor == *tag)
            .ok_or(unmatched)?;
        let mut inner = environment;
        let mut position = FieldPosition(0);
        while let Some(field) = self.field(value, position) {
            inner = self.store.bind_value(inner, field)?;
            position = FieldPosition(position.0.saturating_add(1));
        }
        Ok(Next::Continue(Control::Run(arm.body, inner)))
    }

    /// The field a selection reads from the value it meets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a component selects the field at its position of a tuple, and
    ///   a label the field at the label's place among a record's labels; the
    ///   width is the value's own, never one the selection states.
    /// - provides: the elimination of a tuple or a record by one field.
    /// - fails: [`Stuck::Unmatched`] for a component of anything but a tuple
    ///   holding it, or a label of anything but a record carrying it;
    ///   [`Stuck::IllFormedConsumer`] when `select` is not a selection.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a middle component of a tuple wider than three, a
    ///   label at a different place in two records of different widths, a
    ///   component past the width, an absent label and a selection of the other
    ///   kind's value distinguish an off-by-one position, a width read from the
    ///   selection and a label matched by place. The predicate pairs labels
    ///   with fields, where the body searches for a place.
    /// - witness: `machine::tests::a_selection_reads_the_width_of_the_value_it_meets`
    #[spec(ensures: |ref ret| match self.arena.consumer(select) {
        | Some(&ConsumerNode::Select { ref selector, .. }) => {
            let unmatched = Stop::Stuck(Stuck::Unmatched { value, arms: select });
            *ret == match (selector, self.store.value(value)) {
                | (&Selector::Component(component), Some(&HeapValue::Constructed { tag: ConstructorTag::Tuple(_), ref fields })) =>
                    fields.get(usize::from(component)).copied().ok_or(unmatched),
                | (&Selector::Label(ref label), Some(&HeapValue::Constructed { tag: ConstructorTag::Record(ref labels), ref fields })) =>
                    labels.iter().zip(fields.iter()).find(|&(held, _)| held == label).map(|(_, &field)| field).ok_or(unmatched),
                | _ => Err(unmatched),
            }
        },
        | _ => *ret == Err(Stop::Stuck(Stuck::IllFormedConsumer(select))),
    })]
    fn selection(
        &self,
        value: HeapValueId,
        select: ConsumerId,
    ) -> Result<HeapValueId, Stop>
    {
        let node = self
            .arena
            .consumer(select)
            .ok_or(Stuck::IllFormedConsumer(select))?;
        let ConsumerNode::Select { ref selector, .. } = *node
        else {
            return Err(Stuck::IllFormedConsumer(select).into());
        };
        let place = match (selector, self.store.value(value)) {
            (
                &Selector::Component(component),
                Some(&HeapValue::Constructed {
                    tag: ConstructorTag::Tuple(_),
                    ref fields,
                }),
            ) => fields.get(usize::from(component)),
            (
                &Selector::Label(ref label),
                Some(&HeapValue::Constructed {
                    tag: ConstructorTag::Record(ref labels),
                    ref fields,
                }),
            ) => labels
                .iter()
                .position(|held| held == label)
                .and_then(|place| fields.get(place)),
            _ => None,
        };
        place.copied().ok_or_else(|| {
            Stuck::Unmatched {
                value,
                arms: select,
            }
            .into()
        })
    }

    /// Force the branch a nominal match selects for a constructed value
    /// against the application of its fields to the match's continuation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for `K_i(v̄)`, the branch `t_i` is evaluated under
    ///   `environment`, `then` is loaded, one application frame per field is
    ///   pushed over it — the first field's on top — and `t_i` is forced
    ///   against the resulting top.
    /// - provides: the case-β of a nominal datatype: `case (c_i v̄) of {b̄}` runs
    ///   `b_i v̄`.
    /// - fails: [`Stuck::Unmatched`] for a value that is not a datatype's
    ///   constructor or one whose ordinal names no branch, and the faults of
    ///   evaluation, loading and forcing.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-constructor match selects the branch of its
    ///   value's ordinal and applies two unequal fields in order; a match on a
    ///   value that is not a datatype's constructor is stuck by name. L2 —
    ///   recursive definitions over Nat, List and Tree compare with the
    ///   independent normaliser.
    /// - witness: `machine::tests::data_case_selects_arm_returns_three`
    /// - witness: `machine::tests::data_case_on_non_ctor_is_stuck`
    /// - witness: `tests::differential::hand_built_declared_data_cases_agree`
    #[spec(ensures: |ref ret| match self.store.value(value) {
        | Some(&HeapValue::Constructed { tag: ConstructorTag::Data { tag, .. }, .. })
            if branches.get(usize::from(tag)).is_some() =>
            ret.is_err() || matches!(ret, Ok(Next::Continue(Control::Run(..) | Control::Return(..)))),
        | _ => matches!(ret, Err(Stop::Stuck(Stuck::Unmatched { value: found, arms: matcher }))
            if *found == value && *matcher == case),
    })]
    fn branch(
        &mut self,
        value: HeapValueId,
        case: ConsumerId,
        branches: &[ProducerId],
        then: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let selected = match self.store.value(value) {
            Some(&HeapValue::Constructed {
                tag: ConstructorTag::Data { tag, .. },
                ref fields,
            }) => branches
                .get(usize::from(tag))
                .map(|&branch| (branch, fields.clone())),
            Some(_) | None => None,
        };
        let Some((branch, fields)) = selected
        else {
            return Err(Stuck::Unmatched { value, arms: case }.into());
        };
        let function = self.evaluate(branch, environment)?;
        let _base = self.load(then, environment)?;
        for &field in fields.iter().rev() {
            self.store.push_frame(Frame::Destructor {
                tag: DestructorTag::Apply,
                arguments: crate::store::ObservationArguments::Unary(field),
            })?;
        }
        let top = self.store.mark();
        self.observe(function, DestructorTag::Force, &[], top)
    }

    /// The field at `position` of a constructed value, or `None`.
    ///
    /// # Specification
    /// trivial.
    fn field(
        &self,
        value: HeapValueId,
        position: FieldPosition,
    ) -> Option<HeapValueId>
    {
        let HeapValue::Constructed { ref fields, .. } = *self.store.value(value)?
        else {
            return None;
        };
        fields.get(position.0).copied()
    }

    /// Push the frames a consumer denotes and answer its continuation's mark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a chain of destructor frames over a covariable or `★` shrinks
    ///   the region to that base, then pushes the chain's frames, the first
    ///   observation on top; a chain over a `μ̃` or a match pushes its frames
    ///   onto the current region. The answer is the mark of the resulting top.
    /// - provides: a consumer as a continuation.
    /// - fails: an unbound covariable, a frame with other than one
    ///   continuation, and the store's faults.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the critical pair loads a binder continuation;
    ///   reentry and abandonment observe exact frame marks, and malformed
    ///   continuations and unbound covariables have exact refusals. L2 —
    ///   composed application and forcing spines compare with normalisation,
    ///   distinguishing reversed frames and the wrong base continuation.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    /// - witness: `machine::tests::a_selection_reads_the_width_of_the_value_it_meets`
    #[spec(
        captures: [height = self.store.frame_height()],
        ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&mark| self.store.mark() == mark
            && self.arena.consumer(consumer).is_some_and(|node| match *node {
                | ConsumerNode::Top => mark == ContinuationMark::BASE,
                | ConsumerNode::Covariable(index) => self.store.lookup_covalue(environment, index) == Some(crate::store::Covalue::Pinned(mark)) || (height == mark.height() && self.store.lookup_covalue(environment, index) == Some(crate::store::Covalue::FallThrough)),
                | ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } | ConsumerNode::DataCase { .. } => usize::from(height).checked_add(1) == Some(usize::from(mark.height())),
                | ConsumerNode::Destructor { .. } | ConsumerNode::ListFold { .. } | ConsumerNode::Select { .. } => true,
                })),
    )]
    fn load(
        &mut self,
        consumer: ConsumerId,
        environment: Environment,
    ) -> Result<ContinuationMark, Stop>
    {
        let arena = self.arena;
        let mut pending: Vec<Frame> = Vec::new();
        let mut cursor = consumer;
        let base = loop {
            let node = arena
                .consumer(cursor)
                .ok_or(Stuck::IllFormedConsumer(cursor))?;
            match *node {
                ConsumerNode::Covariable(index) => {
                    let mark = self
                        .store
                        .lookup_covalue(environment, index)
                        .ok_or(Stuck::UnboundCovariable(index))?;
                    break match mark {
                        crate::store::Covalue::Pinned(mark) => Some(mark),
                        crate::store::Covalue::FallThrough => None,
                    };
                },
                ConsumerNode::Top => break Some(ContinuationMark::BASE),
                ConsumerNode::ListFold { continuation, .. } => {
                    pending.push(Frame::ListFold {
                        fold: cursor,
                        environment,
                    });
                    cursor = continuation;
                },
                ConsumerNode::Select { then, .. } => {
                    pending.push(Frame::Select { select: cursor });
                    cursor = then;
                },
                ConsumerNode::MuTilde { body } => {
                    pending.push(Frame::Bind { body, environment });
                    break None;
                },
                ConsumerNode::Case { .. } | ConsumerNode::DataCase { .. } => {
                    pending.push(Frame::Case {
                        arms: cursor,
                        environment,
                    });
                    break None;
                },
                ConsumerNode::Destructor {
                    tag,
                    ref producers,
                    ref consumers,
                } => {
                    let &[then] = consumers.as_ref()
                    else {
                        return Err(Stuck::IllFormedConsumer(cursor).into());
                    };
                    let arguments =
                        self.observation_arguments(cursor, tag, producers, environment)?;
                    pending.push(Frame::Destructor { tag, arguments });
                    cursor = then;
                },
            }
        };
        if let Some(base) = base {
            self.store.shrink_to(base)?;
        }
        while let Some(frame) = pending.pop() {
            self.store.push_frame(frame)?;
        }
        Ok(self.store.mark())
    }

    /// Evaluate a producer to a heap value.
    ///
    /// # Specification
    /// - requires: no constant unfolding is currently running.
    /// - ensures: a variable reads its binding; a literal and a constructor
    ///   over its evaluated fields are allocated; a thunk is allocated with a
    ///   fresh cell, a recursive thunk with the memo its body takes; a
    ///   copattern object or a `μ` closes over `environment`; a constant reads
    ///   its value, unfolding its definition in the empty environment the first
    ///   time it is met.
    /// - provides: the value side of a cut.
    /// - fails: an unbound variable, an undefined or cyclic constant, a
    ///   constructor carrying a consumer, and the store's faults; a constant
    ///   whose unfolding was cut short is reset, so a later run meets it
    ///   afresh.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact constant identities, a nested failed unfolding
    ///   followed by a retry, both variable zones and malformed endpoints
    ///   distinguish wrong lookup and poisoned memo state. Distinct constructor
    ///   fields observe order. L2 — generated pure terms compare with the
    ///   independent normaliser.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "fixed size: the unfolding table holds one entry per definition of the program, sized when the machine is made and never grown; the check scans it once per evaluation"
        )
    )]
    #[spec(
        requires: !self.unfoldings.contains(&Unfolding::Running),
        ensures: |ref ret| !self.unfoldings.contains(&Unfolding::Running)
            && (ret.is_err() || ret.as_ref().is_ok_and(|&value|
                self.arena.producer(root).zip(self.store.value(value)).is_some_and(|(node, held)| match *node {
                    | ProducerNode::Reify(ref source) => matches!(held, HeapValue::Stack { frames } if frames.len() == source.len()),
                    | ProducerNode::Primitive { .. } => self.scalar(value).is_ok(),
                    | ProducerNode::Variable { zone: Zone::Intuitionistic, index } => self.store.lookup_value(environment, index) == Some(value),
                    | ProducerNode::Variable { zone: Zone::Linear, index } => self.store.lookup_linear(environment, index).and_then(|binding| self.store.linear(binding)) == Some(value),
                    | ProducerNode::Constant(constant) => self.unfolding(constant) == Ok(Unfolding::Done(value)),
                    | ProducerNode::Literal(ref literal) => matches!(*held, HeapValue::Literal(ref found) if literal == found),
                    | ProducerNode::Constructor { ref tag, ref producers, ref consumers } => consumers.is_empty()
                        && matches!(*held, HeapValue::Constructed { tag: ref found, ref fields } if tag == found && fields.len() == producers.len()),
                    | ProducerNode::Thunk { body } => matches!(*held, HeapValue::Thunk { body: found, environment: captured, cell }
                        if found == body && captured == environment && self.store.cell(cell) == Some(crate::store::MemoState::Unforced)),
                    | ProducerNode::Fixpoint { body, evidence } => matches!(*held, HeapValue::Fixpoint { body: found, environment: captured, memo, evidence: claimed }
                        if found == body && captured == environment && claimed == evidence && match memo {
                            | Memo::Cell(cell) => self.store.cell(cell) == Some(crate::store::MemoState::Unforced),
                            | Memo::Unfolds => true,
                        }),
                    | ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => matches!(*held,
                        HeapValue::Closure { producer, environment: captured } if producer == root && captured == environment),
                }))),
    )]
    fn evaluate(
        &mut self,
        root: ProducerId,
        environment: Environment,
    ) -> Result<HeapValueId, Stop>
    {
        let mut tasks = alloc::vec![Evaluation::Producer(root, environment)];
        let mut results: Vec<HeapValueId> = Vec::new();
        if let Err(stop) = self.drive(&mut tasks, &mut results) {
            for task in tasks {
                if let Evaluation::Remember(constant, _) = task {
                    self.record(constant, Unfolding::Pending);
                }
            }
            return Err(stop);
        }
        match results.as_slice() {
            &[value] => Ok(value),
            _ => Err(Stuck::IllFormedProducer(root).into()),
        }
    }

    /// Run producer evaluation tasks to completion.
    ///
    /// # Specification
    /// - requires: any results already on the stack resolve in the store.
    /// - ensures: on success every task has run and left its value.
    /// - provides: [`Self::evaluate`]'s loop.
    /// - fails: as [`Self::evaluate`], leaving the unrun tasks in `tasks`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested constants recover from a failed unfolding;
    ///   distinct constructor fields retain order and fresh thunks share their
    ///   nominal cell on repeat force. L2 — generated pure computations compare
    ///   with the normaliser, distinguishing missing tasks, wrong result-stack
    ///   order and incorrect constructor or constant completion.
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body leaves every value it computes on the result stack; the check reads each once"
        )
    )]
    #[spec(
        requires: results.iter().all(|value| self.store.value(*value).is_some()),
        ensures: |ref ret| ret.is_err() || (tasks.is_empty() && results.iter().all(|value| self.store.value(*value).is_some())),
    )]
    fn drive(
        &mut self,
        tasks: &mut Vec<Evaluation>,
        results: &mut Vec<HeapValueId>,
    ) -> Result<(), Stop>
    {
        let arena = self.arena;
        while let Some(task) = tasks.pop() {
            match task {
                Evaluation::Producer(id, environment) => {
                    let node = arena.producer(id).ok_or(Stuck::IllFormedProducer(id))?;
                    let value = match *node {
                        ProducerNode::Reify(ref frames) => {
                            tasks.push(Evaluation::Reify(id, environment));
                            for frame in frames.iter().rev() {
                                if let gandr_core_term::control::StackFrame::Apply(value) = *frame {
                                    tasks.push(Evaluation::Producer(value, environment));
                                }
                            }
                            continue;
                        },
                        ProducerNode::Primitive { arguments, .. } => {
                            tasks.push(Evaluation::Primitive(id));
                            for argument in arguments.iter().rev() {
                                tasks.push(Evaluation::Producer(*argument, environment));
                            }
                            continue;
                        },
                        ProducerNode::Variable { zone, index } => {
                            let bound = match zone {
                                Zone::Intuitionistic => self.store.lookup_value(environment, index),
                                Zone::Linear => self
                                    .store
                                    .lookup_linear(environment, index)
                                    .and_then(|binding| self.store.linear(binding)),
                            };
                            bound.ok_or(Stuck::UnboundVariable { zone, index })?
                        },
                        ProducerNode::Constant(constant) => match self.unfolding(constant)? {
                            Unfolding::Done(value) => value,
                            Unfolding::Running => {
                                return Err(Stuck::CyclicConstant(constant).into());
                            },
                            Unfolding::Pending => match self.definitions.get(constant) {
                                Some(Definition::Transparent(body)) => {
                                    self.record(constant, Unfolding::Running);
                                    tasks.push(Evaluation::Remember(constant, body));
                                    tasks.push(Evaluation::Producer(body, Environment::EMPTY));
                                    continue;
                                },
                                Some(Definition::Opaque) => {
                                    let value = self.store.allocate(HeapValue::Opaque(constant))?;
                                    self.record(constant, Unfolding::Done(value));
                                    value
                                },
                                None => return Err(Stuck::UndefinedConstant(constant).into()),
                            },
                        },
                        ProducerNode::Literal(ref literal) => {
                            self.store.allocate(HeapValue::Literal(literal.clone()))?
                        },
                        ProducerNode::Constructor {
                            ref producers,
                            ref consumers,
                            ..
                        } => {
                            if !consumers.is_empty() {
                                return Err(Stuck::IllFormedProducer(id).into());
                            }
                            tasks.push(Evaluation::Construct(id));
                            for &field in producers.iter().rev() {
                                tasks.push(Evaluation::Producer(field, environment));
                            }
                            continue;
                        },
                        ProducerNode::Thunk { body } => {
                            let cell = self.store.allocate_cell()?;
                            self.store.allocate(HeapValue::Thunk {
                                body,
                                environment,
                                cell,
                            })?
                        },
                        ProducerNode::Fixpoint { body, evidence } => {
                            let memo = self.memo(body)?;
                            self.store.allocate(HeapValue::Fixpoint {
                                body,
                                environment,
                                memo,
                                evidence,
                            })?
                        },
                        ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => {
                            self.store.allocate(HeapValue::Closure {
                                producer: id,
                                environment,
                            })?
                        },
                    };
                    results.push(value);
                },
                Evaluation::Reify(id, environment) => {
                    let node = arena.producer(id).ok_or(Stuck::IllFormedProducer(id))?;
                    let ProducerNode::Reify(ref source) = *node
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let mut frames = Vec::with_capacity(source.len());
                    let mut bind_environment = None;
                    for frame in source.iter().rev() {
                        frames.push(match *frame {
                            gandr_core_term::control::StackFrame::Apply(_) => Frame::Destructor {
                                tag: DestructorTag::Apply,
                                arguments: crate::store::ObservationArguments::Unary(
                                    results.pop().ok_or(Stuck::IllFormedProducer(id))?,
                                ),
                            },
                            gandr_core_term::control::StackFrame::Project(side) => {
                                Frame::Destructor {
                                    tag: DestructorTag::Project(side),
                                    arguments: crate::store::ObservationArguments::Nullary,
                                }
                            },
                            gandr_core_term::control::StackFrame::Bind(body) => {
                                let inner = if let Some(inner) = bind_environment {
                                    inner
                                }
                                else {
                                    let inner = self.store.bind_covalue(
                                        environment,
                                        crate::store::Covalue::FallThrough,
                                    )?;
                                    bind_environment = Some(inner);
                                    inner
                                };
                                Frame::Bind {
                                    body,
                                    environment: inner,
                                }
                            },
                        });
                    }
                    let value = self.store.allocate(HeapValue::Stack {
                        frames: frames.into_boxed_slice(),
                    })?;
                    results.push(value);
                },
                Evaluation::Construct(id) => {
                    let Some(node) = arena.producer(id)
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let ProducerNode::Constructor {
                        ref tag,
                        ref producers,
                        ..
                    } = *node
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let start = results
                        .len()
                        .checked_sub(producers.len())
                        .ok_or(Stuck::IllFormedProducer(id))?;
                    let fields: Box<[HeapValueId]> = results.drain(start ..).collect();
                    let value = self.store.allocate(HeapValue::Constructed {
                        tag: tag.clone(),
                        fields,
                    })?;
                    results.push(value);
                },
                Evaluation::Primitive(id) => {
                    use gandr_core_term::primitive::Arguments;
                    use gandr_core_term::primitive::Scalar;
                    let Some(&ProducerNode::Primitive {
                        primitive,
                        arguments,
                    }) = arena.producer(id)
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let last = results.pop().ok_or(Stuck::IllFormedProducer(id))?;
                    let last = self.scalar(last)?;
                    let arguments = match arguments {
                        Arguments::Unary(_) => Arguments::Unary(last),
                        Arguments::Binary(_) => {
                            let first = results.pop().ok_or(Stuck::IllFormedProducer(id))?;
                            Arguments::Binary([self.scalar(first)?, last])
                        },
                    };
                    let result = primitive.evaluate(&arguments).map_err(Stuck::Primitive)?;
                    let value = match result {
                        Scalar::Integer(integer) => self.store.allocate(HeapValue::Literal(
                            gandr_kernel_term::Literal::Integer(integer),
                        ))?,
                        Scalar::Boolean(side) => {
                            let unit = self.store.allocate(HeapValue::Constructed {
                                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                                fields: Box::from([]),
                            })?;
                            self.store.allocate(HeapValue::Constructed {
                                tag: ConstructorTag::Injection(side.into()),
                                fields: Box::from([unit]),
                            })?
                        },
                    };
                    results.push(value);
                },
                Evaluation::Remember(constant, body) => {
                    let &value = results.last().ok_or(Stuck::IllFormedProducer(body))?;
                    self.record(constant, Unfolding::Done(value));
                },
            }
        }
        Ok(())
    }

    /// The memo a recursive thunk over `body` is forced by.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a body that cuts a copattern object against its own return
    ///   point — a recursive function or lazy record — takes a fresh unforced
    ///   cell; any other body, a loop, unfolds.
    /// - provides: the choice between caching a fixpoint and unfolding it.
    /// - fails: the store's faults when its cell region is full.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursive function computes through its cached cell
    ///   and loops re-enter with no frame, which a cell on the wrong body shape
    ///   would add.
    /// - witness: `machine::tests::a_recursive_thunk_computes_through_its_own_binding`
    /// - witness: `machine::tests::a_loop_holds_no_frame_across_its_iterations`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&memo| match memo {
        | Memo::Cell(cell) => self.store.cell(cell) == Some(crate::store::MemoState::Unforced),
        | Memo::Unfolds => true,
    }))]
    fn memo(
        &mut self,
        body: CommandId,
    ) -> Result<Memo, Stop>
    {
        let arena = self.arena;
        let returns_object = matches!(arena.command(body), Some(&CommandNode::Cut { producer, consumer, .. })
            if matches!(arena.producer(producer), Some(&ProducerNode::Cocase { .. }))
                && arena.consumer(consumer) == Some(&ConsumerNode::Covariable(CovariableIndex::from(0_u32))));
        if returns_object {
            Ok(Memo::Cell(self.store.allocate_cell()?))
        }
        else {
            Ok(Memo::Unfolds)
        }
    }

    /// How far a constant's unfolding has got.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded state of an admitted constant.
    /// - provides: the memo of constants' values.
    /// - fails: [`Stuck::UndefinedConstant`] for a position never admitted.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transparent, opaque, cyclic and undefined
    ///   declarations have distinct outcomes; a two-level failed unfolding is
    ///   retried and both records are pending, distinguishing wrong admission
    ///   indexing and retained running states.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    #[spec(ensures: |ref ret| *ret == self.unfoldings.get(usize::from(constant)).copied().ok_or(Stuck::UndefinedConstant(constant)))]
    fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Result<Unfolding, Stuck>
    {
        self.unfoldings
            .get(usize::from(constant))
            .copied()
            .ok_or(Stuck::UndefinedConstant(constant))
    }

    /// Record a constant's unfolding state.
    ///
    /// # Specification
    /// trivial.
    fn record(
        &mut self,
        constant: ConstantIndex,
        state: Unfolding,
    )
    {
        if let Some(slot) = self.unfoldings.get_mut(usize::from(constant)) {
            *slot = state;
        }
    }

    /// Read the native scalar carried by a terminal operand.
    ///
    /// # Specification
    /// - ensures: integers and unit injections retain their exact payload; all
    ///   other shapes are refused.
    /// - fails: a non-scalar operand yields the table's argument-type refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the native argument-type refusal for malformed or non-scalar
    /// values.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal operands and both injection tags separate
    ///   classifier and order errors.
    /// - witness: `machine::tests::native_arithmetic_and_partial_application`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(ret, Err(Stop::Stuck(Stuck::NonScalar(actual))) if *actual == value))]
    fn scalar(
        &self,
        value: HeapValueId,
    ) -> Result<gandr_core_term::primitive::Scalar<&gandr_kernel_term::IntegerLiteral>, Stop>
    {
        use gandr_core_term::primitive::Scalar;
        match self.store.value(value) {
            Some(&HeapValue::Literal(gandr_kernel_term::Literal::Integer(ref integer))) => {
                Ok(Scalar::Integer(integer))
            },
            Some(&HeapValue::Constructed {
                tag: ConstructorTag::Injection(summand),
                ref fields,
            }) => {
                if let &[body] = fields.as_ref()
                    && matches!(self.store.value(body), Some(&HeapValue::Constructed { tag: ConstructorTag::Tuple(ProducerArity::ZERO), ref fields }) if fields.is_empty())
                    && let Ok(side) = gandr_kernel_term::Side::try_from(summand)
                {
                    Ok(Scalar::Boolean(side))
                }
                else {
                    Err(Stuck::NonScalar(value).into())
                }
            },
            _ => Err(Stuck::NonScalar(value).into()),
        }
    }
}

#[cfg(test)]
mod tests;
