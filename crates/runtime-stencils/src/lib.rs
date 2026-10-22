//! The L machine's transitions, written once.
//!
//! Every transition is one stencil: an `extern "rust-preserve-none"` Rust
//! function over the run's registers that ends in a `become` to a
//! continuation. The same functions are compiled two ways, and that is the
//! whole of how gandr runs a program:
//!
//! - **Stencils for copy-and-patch.** `gandr-runtime-emitter`'s build script
//!   compiles this file alone, with the pinned rustc and `--cfg
//!   gandr_stencil_object`, into an object. There a continuation is a call to
//!   an undefined function (`hole_next`, `hole_alt`, the exhaustion exits) and
//!   an operand is the address of an undefined static (`HOLE_A`, `HOLE_B`), so
//!   each use is a relocation the emitter patches when it copies the stencil
//!   into executable memory.
//! - **The portable executor.** Built as an ordinary library, the holes are
//!   defined here: an operand reads the current [`Instruction`], a continuation
//!   advances to the next instruction and `become`s its stencil through the
//!   [`StencilId`] dispatch table. It runs wherever rustc builds this crate,
//!   with or without a patcher for the target, and it is the reference the
//!   emitted code is compared against.
//!
//! The choice is one definition for both executors (Deegen's lesson: two
//! hand-written implementations of the same transitions are held together only
//! by tests). The alternative was the emitter's stencils beside a separate
//! interpreter loop, which is what `gandr-core-sequent`'s hand-written
//! machine was until this crate retired it. The choice reverses if a
//! transition needs a form the copy-and-patch build cannot take — an
//! out-of-line call, a constant pool — that the executor needs anyway, which
//! would split the two again.
//!
//! # The registers
//!
//! Every stencil has one signature, [`Stencil`]: five arguments under the
//! `preserve_none` convention, which LLVM passes in registers the callee need
//! not save, so a chain of stencils keeps them pinned and no stencil but
//! `call` has a prologue.
//!
//! | Argument | Holds | aarch64 | x86-64 |
//! | -------- | ----- | ------- | ------ |
//! | `runtime` | the run's [`Runtime`] record | `x20` | `r12` |
//! | `heap` | the heap region's bump pointer | `x21` | `r13` |
//! | `frames` | the frame region's top | `x22` | `r14` |
//! | `environment` | the current window of slots | `x23` | `r15` |
//! | `value` | the value in hand | `x24` | `rdi` |
//!
//! The heap region is a bump pointer over [`Word`]s, with a free list per
//! small block size in the [`Runtime`] record that an allocation takes from
//! first (the layout module's count section); the frame region a stack of
//! two-word frames, a code word and the environment it resumes in, above a
//! sentinel frame whose code halts; the environment a window of slots, one per
//! binder. `gandr-runtime-emitter`'s lowering documents the linear form that
//! assigns them.
//!
//! # The holes
//!
//! | Hole | Stencil object | Executor |
//! | ---- | -------------- | -------- |
//! | `HOLE_A`, `HOLE_B` | an undefined static whose address the patcher writes | the current instruction's operand |
//! | `hole_next` | a branch the patcher aims at the next copy | the next instruction |
//! | `hole_alt` | a branch the patcher aims at a label | the instruction's `alt` |
//! | `hole_heap_exhausted`, `hole_frames_exhausted`, `hole_fuel_exhausted`, `hole_stuck` | a branch the patcher aims at the region's shared exit | the exit stencil |
//! | a code word in hand | a native address, called | an instruction's address, dispatched |
//!
//! # The host call
//!
//! A primitive leaves the stencils for the host through one stencil, `call`,
//! and the same seam is the shape a foreign call takes at the host boundary
//! (#327). The lowering numbers each distinct callee of a function and
//! pushes the call's arguments, left to right, as it pushes a constructor's
//! fields; `call` pops them, writes the heap's top, the frame region's top
//! and the window to the [`Runtime`] record and makes an ordinary platform
//! call to the record's [`Host`] entry with the record, the callee's number
//! and the first two arguments. The host answers with a value it allocated
//! on the heap through the record, or refuses ([`Refusal`]): an answer past
//! a region's limit takes that region's exhausted exit, as any allocation
//! does, and operands the callee does not take stop the run stuck. The call
//! is indirect through the record, so the stencil carries no relocation and
//! both builds share it; LLVM saves what the platform convention clobbers
//! around the call, the one stencil that has a prologue. The alternative was
//! a stencil per primitive, which puts host arithmetic — unbounded integers
//! among it — inside the stencil object, where no allocation and no call can
//! live.
//!
//! Control takes the same seam. An operation, a shift, a replay and every
//! memory form are host calls that read and rewrite the frame region: the
//! host moves the frame region's top and may name a code word and window to
//! continue at, where an operation's clause or an aborted view's unwind
//! starts. A handler's frame is an ordinary frame resuming at its return
//! clause, a reset's resumes at the shared `pop` copy and an aborted view's
//! answer frame at `answer_frame`, so the stencils hold no control
//! transition of their own; the alternative, a stencil per capture and
//! replay, would copy windows of sizes only the lowering knows inside code
//! that cannot call.
//!
//! # The authoring rules
//!
//! - **A hole is never a valid pointer to the optimiser.** The address of a
//!   static is never null, and LLVM uses that: a copy loop counted by `&HOLE_B`
//!   was compiled to run at least once, so a closure over no slots read an
//!   empty window. An immediate operand is patched biased by one and `operand!`
//!   subtracts it; an address operand is patched as it is.
//! - **No two stencils share a body.** LLVM merges identical functions into one
//!   symbol, leaving the other stencil with no bytes; the generator refuses an
//!   empty stencil, so a duplicate fails the build.
//! - **A stencil calls nothing but the host.** No `memcpy` (the crate is
//!   `#![no_builtins]`), no panic path (arithmetic wraps and the object is
//!   built with overflow checks and debug assertions off), no constant pool: a
//!   relocation to anything but a hole fails the build. `call` reaches the host
//!   through a pointer the record holds, which needs none.
//! - **Every unbounded jump spends fuel.** Lowered code is straight-line
//!   between code-word jumps — a frame's resumption, a closure's entry — so
//!   `resume!` decrements the run's fuel and exits with
//!   [`Status::FuelExhausted`] at zero: a divergent program stops. A fold's
//!   `jump` back to its test runs once per cell of a list the heap already
//!   holds, so it is bounded without fuel.
//!
//! # The agreement differential
//!
//! The witnesses run each program on emitted native code where the host has
//! a patcher and on the executor, and compare the two outcomes value by value
//! across their stores. Both tiers share every stencil, so a stencil's error
//! is caught where a program states its answer: each named program and
//! witness states the reading it halts with, and each corpus `runs` item the
//! spelling its run reaches. `gandr-core-sequent` holds both tiers to
//! normalisation by evaluation over generated programs as well.
//!
//! # The feature gates
//!
//! The crate enables two unstable features, the only nightly surface the
//! runtime takes. `rust_preserve_none_cc` gives the convention that pins the
//! registers across a chain with no saves; `explicit_tail_calls` gives
//! `become`, the guaranteed tail call that makes a continuation a branch and
//! not a call that grows the native stack. Neither has a stable equivalent:
//! without them every transition would return to a dispatch loop. Reversal:
//! both stabilise, and the expectations below leave.
//!
//! # Safety
//!
//! A stencil dereferences its register arguments without checking them; it is
//! entered only by emitted code or the executor, which hold the invariants
//! the emitter's lowering establishes: every slot a stencil names lies inside
//! the window, every mark above the sentinel frame, every object a stencil
//! reads was written by a constructor stencil or laid out as a constant. The
//! entries ([`enter`], [`execute`]) are the one place a Rust caller crosses
//! into that chain, and they are `unsafe` for that reason.

// Module documentation that predates the shape lint: 7 headings outside the
// vocabulary, 1 decision record, 1 issue reference and 1 budget exceeded. Each
// allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]
#![no_builtins]
#![feature(rust_preserve_none_cc, explicit_tail_calls)]
#![expect(
    unstable_features,
    reason = "the two feature gates the module documentation names; no stable equivalent"
)]
#![expect(
    incomplete_features,
    reason = "explicit_tail_calls is incomplete upstream; `become` is its whole use here"
)]

mod holes;
mod layout;
mod transitions;

#[cfg(not(gandr_stencil_object))]
mod executor;

#[cfg(not(gandr_stencil_object))]
pub use crate::executor::StencilId;
#[cfg(not(gandr_stencil_object))]
pub use crate::executor::Symbol;
#[cfg(not(gandr_stencil_object))]
pub use crate::executor::enter;
#[cfg(not(gandr_stencil_object))]
pub use crate::executor::execute;
pub use crate::layout::Arity;
pub use crate::layout::COUNT_IMMORTAL;
pub use crate::layout::COUNT_ONE;
pub use crate::layout::FREE_CLASSES;
pub use crate::layout::Family;
pub use crate::layout::FieldOverflow;
pub use crate::layout::Flavour;
pub use crate::layout::Fuel;
pub use crate::layout::Header;
pub use crate::layout::Kind;
pub use crate::layout::Observed;
pub use crate::layout::RELEASE;
pub use crate::layout::Status;
pub use crate::layout::Tag;
pub use crate::layout::UnknownKind;
pub use crate::layout::UnknownStatus;
pub use crate::layout::Unnamed;
pub use crate::layout::Words;

/// One stencil, and every continuation it reaches.
///
/// # Specification
/// - requires: the five registers hold the invariants the crate's `# Safety`
///   section states.
/// - ensures: control reaches a continuation by `become`, or an exit returns
///   the value in hand to the entry.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
pub type Stencil = extern "rust-preserve-none" fn(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word;

/// The machine word every register, slot, frame word and heap word holds.
///
/// A word is a pointer-sized integer: an address (a heap object, a frame
/// mark, a code address, a window), an integer literal's two's-complement
/// bits, or a header.
///
/// # Specification
/// - ensures: one word is exactly one `usize`, so a heap object's fields and a
///   window's slots are addressed by word offsets.
/// - executable: none — a layout claim is a property of the type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Word(usize);

// An integer literal is one 64-bit word and a header's family rides in bits
// 32–63, so the layout needs 64-bit words. Reversal: a 32-bit host, which
// would box integers and move the family into a second header word.
const _: () = assert!(usize::BITS == 64, "the stencil layout needs 64-bit words");

impl Word
{
    /// The zero word: the value register's content when a run starts.
    pub const ZERO: Self = Self(0);

    /// The word holding `pointer`'s address, its provenance exposed so
    /// [`Self::to_pointer`] recovers a usable pointer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn from_pointer<Target>(pointer: *const Target) -> Self
    {
        Self(pointer.expose_provenance())
    }

    /// The pointer whose address this word holds, with the provenance the
    /// address was exposed with.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_pointer<Target>(self) -> *mut Target
    {
        core::ptr::with_exposed_provenance_mut(self.0)
    }
}

impl From<usize> for Word
{
    /// The word holding a count, an offset or an immediate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(raw: usize) -> Self
    {
        Self(raw)
    }
}

impl From<Word> for usize
{
    /// The word's bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(word: Word) -> Self
    {
        word.0
    }
}

impl From<i64> for Word
{
    /// An integer literal's two's-complement bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(integer: i64) -> Self
    {
        Self(usize::from_le_bytes(integer.to_le_bytes()))
    }
}

impl From<Word> for i64
{
    /// The integer literal whose bits the word holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(word: Word) -> Self
    {
        Self::from_le_bytes(word.0.to_le_bytes())
    }
}

impl From<u64> for Word
{
    /// The word with these bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bits: u64) -> Self
    {
        Self(usize::from_le_bytes(bits.to_le_bytes()))
    }
}

impl From<Word> for u64
{
    /// The word's bits, unsigned.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(word: Word) -> Self
    {
        Self::from_le_bytes(word.0.to_le_bytes())
    }
}

/// The host's entry, which a call stencil enters through the runtime record:
/// the seam where a run leaves the stencils' convention for the platform's.
///
/// The call stencil passes the record, the call's entry in the run's host
/// table — the lowering numbers each distinct callee of a function — and its
/// first two arguments, unused ones zero; every argument lies at
/// [`Runtime::frame_top`], popped but intact while the host runs. The host
/// reads the heap's top and limit from the record, allocates its answer
/// there, writes the new top back with [`Runtime::set_heap_top`] and returns
/// the answer; when it cannot, it writes [`Status::HeapExhausted`],
/// [`Status::FramesExhausted`] or [`Status::Stuck`] with [`Runtime::refuse`]
/// and returns anything, and the stencil takes that exit. A control
/// operation also reads the frame region's top and the window in reach, may
/// move the top with [`Runtime::set_frame_top`] — a capture removes frames, a
/// replay pushes them — and may name the code word and window the run
/// continues at with [`Runtime::jump`], where the stencil goes instead of its
/// next instruction. The host's own state rides in [`Runtime::context`].
///
/// # Specification
/// - requires: the host never unwinds across the call, and leaves every word
///   below the heap's top as it found it.
/// - executable: none — a contract on a function the host supplies.
pub type Host =
    extern "C" fn(runtime: *mut Runtime, entry: Word, first: Word, second: Word) -> Word;

/// Why a host call refused.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Refusal
{
    /// The answer would pass the heap region's limit: the run takes the heap
    /// exit.
    Heap,
    /// The frames a replay pushes would pass the frame region's limit: the
    /// run takes the frame exit.
    Frames,
    /// The operands are not the callee's: the run is stuck.
    Operands,
}

/// The record every stencil reaches through its first register.
///
/// One record per run, owned by the host that enters emitted code or the
/// executor; the stencils read the limits and the fuel and write the exit
/// fields.
///
/// # Specification
/// - ensures: the layout is C's, so emitted code reaches each field at the
///   offset the stencils were compiled against.
/// - executable: none — a layout claim is a property of the type.
#[repr(C)]
#[derive(Debug)]
pub struct Runtime
{
    /// One past the heap region's last word.
    heap_limit: *mut Word,
    /// One past the frame region's last word.
    frame_limit: *mut Word,
    /// The base mark: the frame region's height above the sentinel frame.
    frame_base: *mut Word,
    /// The heap pointer when the run exited, or across a host call.
    heap_top: *mut Word,
    /// Why the run exited, as a status word.
    status: Word,
    /// The code-word jumps the run may still take.
    fuel: Word,
    /// The executor's current instruction; emitted code never reads it.
    instruction: *const Instruction,
    /// The host's entry, which every call stencil enters.
    host: Host,
    /// The host's own state, which no stencil reads.
    context: Word,
    /// The frame region's top across a host call.
    frame_top: *mut Word,
    /// The window in reach across a host call.
    environment: *mut Word,
    /// The code word a host call continues at, or zero for the next
    /// instruction.
    jump: Word,
    /// The window the code word continues in.
    jump_window: *mut Word,
    /// What the stuck or unmatched exit observed by: an [`Observed`]
    /// destructor's word, or the unmatched case's site; zero when a host call
    /// refused.
    observed: Word,
    /// The run's constants, one word each: zero until unfolded, one while
    /// unfolding, the value once unfolded.
    globals: *mut Word,
    /// The freed blocks waiting to be reused, by size in words, count word
    /// included; each links the next through its count word, null ending it.
    free: [*mut Word; FREE_CLASSES],
    /// The window region's first word: a window below it, the entry window
    /// or a replayed frame's, is never given back.
    window_base: *mut Word,
    /// One past the window region's last live word: the next window's
    /// address.
    window_top: *mut Word,
    /// One past the window region's last word.
    window_limit: *mut Word,
}

impl Runtime
{
    /// A record for a run over the heap region `[heap, heap_limit)` and the
    /// frame region whose limit is `frame_limit` and whose base mark is
    /// `frame_base`, whose calls enter `host` with `context` in reach.
    ///
    /// # Specification
    /// - requires: the heap region's start is at or below its limit, and
    ///   `frame_base` lies within the frame region.
    /// - ensures: the record reports [`Status::Running`] until an exit writes
    ///   it, and holds `fuel` jumps.
    /// - executable: none — the pointers' validity is the caller's to keep and
    ///   no predicate observes it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run whose entry is an exit reports the exit's
    ///   status and the heap pointer it was given, and a run given no fuel
    ///   exits by fuel at its first jump.
    /// - witness: `tests::exits::a_run_without_fuel_exits_by_name`
    /// - witness: `tests::exits::a_full_heap_exits_by_name`
    #[inline]
    #[must_use]
    pub fn new(
        heap: *mut Word,
        heap_limit: *mut Word,
        frame_limit: *mut Word,
        frame_base: *mut Word,
        fuel: Fuel,
        host: Host,
        context: Word,
    ) -> Self
    {
        Self {
            heap_limit,
            frame_limit,
            frame_base,
            heap_top: heap,
            status: layout::STATUS_RUNNING,
            fuel: Word(usize::from(fuel)),
            instruction: core::ptr::null(),
            host,
            context,
            frame_top: frame_base,
            environment: core::ptr::null_mut(),
            jump: Word::ZERO,
            jump_window: core::ptr::null_mut(),
            observed: Word::ZERO,
            globals: core::ptr::null_mut(),
            free: [core::ptr::null_mut(); FREE_CLASSES],
            window_base: core::ptr::null_mut(),
            window_top: core::ptr::null_mut(),
            window_limit: core::ptr::null_mut(),
        }
    }

    /// Give the run's constants the table `globals`.
    ///
    /// # Specification
    /// - requires: `globals` holds one zeroed word per constant the function
    ///   unfolds, live for the run.
    /// - ensures: each unfolding stencil reads and writes its word there.
    /// - executable: none — the requirement is about the table's memory.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant read twice answers one value, a constant
    ///   needing its own value is stuck as cyclic, and an undefined one as
    ///   undefined only when reached.
    /// - witness: `tests::agreement::constants_unfold_once_and_a_cycle_is_stuck`
    #[inline]
    pub const fn set_globals(
        &mut self,
        globals: *mut Word,
    )
    {
        self.globals = globals;
    }

    /// The host's state, as the record was made with it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn context(&self) -> Word
    {
        self.context
    }

    /// One past the heap region's last word: the bound a host allocation
    /// stays below.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn heap_limit(&self) -> *mut Word
    {
        self.heap_limit
    }

    /// Move the heap's top to `top`, past a host call's allocations.
    ///
    /// # Specification
    /// - requires: `top` lies between the top the call found and the heap's
    ///   limit.
    /// - ensures: [`Self::heap_top`] is `top`.
    /// - executable: none — the requirement is about the host's allocations.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named primitive programs allocate their answers
    ///   through the host and halt with the readings they state; a top left
    ///   behind lets the next allocation overwrite the answer.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub const fn set_heap_top(
        &mut self,
        top: *mut Word,
    )
    {
        self.heap_top = top;
    }

    /// The frame region's base mark, above the sentinel frame: no capture
    /// reaches below it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn frame_base(&self) -> *mut Word
    {
        self.frame_base
    }

    /// One past the frame region's last word: the bound a replay stays below.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn frame_limit(&self) -> *mut Word
    {
        self.frame_limit
    }

    /// The frame region's top as a host call found it, its arguments popped.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn frame_top(&self) -> *mut Word
    {
        self.frame_top
    }

    /// Move the frame region's top to `top`: below the frames a capture
    /// takes, above those a replay pushes.
    ///
    /// # Specification
    /// - requires: `top` lies between the base mark and the frame region's
    ///   limit, every frame below it whole.
    /// - ensures: [`Self::frame_top`] is `top`.
    /// - executable: none — the requirement is about the region's frames.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus's handlers capture and resume; a top left
    ///   where the call found it resumes the captured frames twice.
    /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
    #[inline]
    pub const fn set_frame_top(
        &mut self,
        top: *mut Word,
    )
    {
        self.frame_top = top;
    }

    /// The window in reach where the host call stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn environment(&self) -> *mut Word
    {
        self.environment
    }

    /// Continue the run at `code` in `window` once the host call returns,
    /// its answer in hand, one unit of fuel spent.
    ///
    /// # Specification
    /// - requires: `code` is a code word of the running function and `window`
    ///   holds the slots its block reads.
    /// - ensures: the call stencil resumes at `code` rather than its next
    ///   instruction.
    /// - executable: none — where the run continues is observed only by running
    ///   it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an operation's clause and an aborted view's unwind
    ///   are entered this way; a jump ignored runs the instruction after the
    ///   call, which takes the stuck exit.
    /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
    #[inline]
    pub const fn jump(
        &mut self,
        code: Word,
        window: *mut Word,
    )
    {
        self.jump = code;
        self.jump_window = window;
    }

    /// Refuse a host call for `refusal`: the call stencil takes the heap exit
    /// for [`Refusal::Heap`], the frame exit for [`Refusal::Frames`], the
    /// stuck exit for [`Refusal::Operands`].
    ///
    /// # Specification
    /// - ensures: [`Self::status`] reads [`Status::HeapExhausted`] for
    ///   [`Refusal::Heap`], [`Status::FramesExhausted`] for
    ///   [`Refusal::Frames`], [`Status::Stuck`] for [`Refusal::Operands`].
    /// - executable: none — the exit taken is observed only by running it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a host refusing each way takes the exit it names.
    /// - witness: `tests::exits::a_host_call_answers_or_names_its_exit`
    #[inline]
    pub const fn refuse(
        &mut self,
        refusal: Refusal,
    )
    {
        self.status = match refusal {
            Refusal::Heap => layout::STATUS_HEAP_EXHAUSTED,
            Refusal::Frames => layout::STATUS_FRAMES_EXHAUSTED,
            Refusal::Operands => layout::STATUS_STUCK,
        };
    }

    /// Why the run exited.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`UnknownStatus`] for a status word no exit writes.
    #[inline]
    pub fn status(&self) -> Result<Status, UnknownStatus>
    {
        Status::try_from(self.status)
    }

    /// What the stuck or unmatched exit observed by: an [`Observed`]
    /// destructor's word after a stuck observation, the case's site after an
    /// unmatched one, zero when a host call refused or no exit wrote it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn observed(&self) -> Word
    {
        self.observed
    }

    /// The heap pointer when the run exited: one past its last allocation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn heap_top(&self) -> *mut Word
    {
        self.heap_top
    }

    /// Give the run's closure entries the window region `[base, limit)`,
    /// empty until the first entry. A record given none has an empty region,
    /// and its first closure entry takes the heap exit.
    ///
    /// # Specification
    /// - requires: `base` is at or below `limit` and the words between are the
    ///   run's, apart from the heap and the frame region.
    /// - ensures: [`Self::window_top`] is `base`.
    /// - executable: none — the pointers' validity is the caller's to keep.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure entered and returned from leaves the
    ///   region's top where it found it, and every corpus program runs its
    ///   entries in the region.
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
    #[inline]
    pub const fn set_windows(
        &mut self,
        base: *mut Word,
        limit: *mut Word,
    )
    {
        self.window_base = base;
        self.window_top = base;
        self.window_limit = limit;
    }

    /// One past the window region's last live word: where the next closure
    /// entry's window goes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closure entered and returned from leaves the
    ///   region's top where it found it; a top read as null or elsewhere moves
    ///   it.
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    #[inline]
    #[must_use]
    pub const fn window_top(&self) -> *mut Word
    {
        self.window_top
    }

    /// The code-word jumps the run did not take.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fuel(&self) -> Fuel
    {
        Fuel::from_word(self.fuel)
    }

    /// Allocate an object of `words` words, header and fields: a block of its
    /// size from the free list when one waits there, else at the heap's top;
    /// its count is one. Answers the object's address, past its count word.
    ///
    /// # Specification
    /// - requires: called across a host call, when [`Self::heap_top`] is the
    ///   run's heap pointer.
    /// - ensures: the object's count word reads [`COUNT_ONE`], and the heap's
    ///   top moves only when no freed block of the size waits.
    /// - executable: none — the requirement is about the run's registers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block freed by a release is the next of its size a
    ///   host allocation takes, and the heap's top stays.
    /// - witness: `tests::count::a_freed_block_is_the_next_of_its_size`
    ///
    /// # Errors
    /// [`Refusal::Heap`] when no block waits and the words would pass the
    /// heap's limit.
    #[inline]
    pub fn reserve(
        &mut self,
        words: Words,
    ) -> Result<*mut Word, Refusal>
    {
        let size = words.0.wrapping_add(1);
        let block = match self.free.get_mut(size) {
            Some(head) if !head.is_null() => {
                let block = *head;
                // SAFETY: a free list holds freed blocks, each linking the
                // next through its count word.
                *head = unsafe { *block }.to_pointer::<Word>();
                block
            },
            Some(_) | None => self.bump(Words(size))?,
        };
        // SAFETY: the block spans `size` words of the run's heap.
        unsafe {
            *block = COUNT_ONE;
        }
        Ok(block.wrapping_add(1))
    }

    /// Allocate `words` words at the heap's top, with no count: a window a
    /// replay copies out.
    ///
    /// # Specification
    /// - requires: as [`Self::reserve`].
    /// - ensures: the heap's top moves past the words.
    /// - executable: none — as [`Self::reserve`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus's handlers replay captured stacks, each
    ///   window copied here; a window overlapping a live object changes the
    ///   answer.
    /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
    ///
    /// # Errors
    /// [`Refusal::Heap`] when the words would pass the heap's limit.
    #[inline]
    pub fn bump(
        &mut self,
        words: Words,
    ) -> Result<*mut Word, Refusal>
    {
        let top = self.heap_top;
        let next = top.wrapping_add(words.0);
        if next > self.heap_limit {
            return Err(Refusal::Heap);
        }
        self.heap_top = next;
        Ok(top)
    }

    /// Return the block of the object `object` to the free list of its
    /// size, when its header says the size and a list keeps it.
    ///
    /// # Specification
    /// - requires: `object` addresses a heap object no live value reaches.
    /// - ensures: the next [`Self::reserve`] or constructor of the block's size
    ///   takes it.
    /// - executable: none — the requirement is about the run's values.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::reserve`].
    /// - witness: `tests::count::a_freed_block_is_the_next_of_its_size`
    ///
    /// # Safety
    /// - unsafe invariants: `object` addresses a heap object of this run,
    ///   preceded by its count word, and nothing reads its block again before
    ///   an allocation takes it.
    #[inline]
    pub unsafe fn reclaim(
        &mut self,
        object: Word,
    )
    {
        let header = object.to_pointer::<Word>();
        // SAFETY: the caller's object addresses its header.
        let read = Header::from_word(unsafe { *header });
        // SAFETY: as above; a freed header names no kind, so a value read
        // after its release is refused by name rather than read as data.
        unsafe {
            *header = layout::FREED;
        }
        let Some(Words(size)) = read.block()
        else {
            return;
        };
        if let Some(head) = self.free.get_mut(size) {
            let block = header.wrapping_sub(1);
            // SAFETY: the block's count word is the caller's to overwrite.
            unsafe {
                *block = Word::from_pointer(*head);
            }
            *head = block;
        }
    }
}

/// The count word of the object `object`, the word before its header.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn count_word(object: Word) -> *mut Word
{
    object.to_pointer::<Word>().wrapping_sub(1)
}

/// One instruction of the portable executor: the stencil that runs it, its
/// two operands and the instruction its second continuation reaches.
///
/// An executor program is an array of these; an instruction's first
/// continuation is the next element, so a code word — a frame's resumption,
/// a closure's entry — is an instruction's address.
///
/// # Specification
/// - ensures: the layout is C's, fixed for both builds of the crate.
/// - executable: none — a layout claim is a property of the type.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct Instruction
{
    /// The stencil.
    handler: Stencil,
    /// Operand A, unbiased.
    a: Word,
    /// Operand B, unbiased.
    b: Word,
    /// The `hole_alt` continuation, or null for a one-way stencil.
    alt: *const Self,
}
