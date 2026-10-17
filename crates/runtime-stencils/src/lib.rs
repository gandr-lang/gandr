//! The L machine's transitions, written once.
//!
//! Every transition is one stencil: an `extern "rust-preserve-none"` Rust
//! function over the machine's registers that ends in a `become` to a
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
//!   with or without a patcher for the target, and it is the differential the
//!   emitted code is compared against.
//!
//! The choice is one definition for both executors (Deegen's lesson: two
//! hand-written implementations of the same transitions are held together only
//! by tests). The alternative was the emitter's stencils beside a separate
//! interpreter loop, which is what `gandr-core-sequent`'s machine is today and
//! what this crate retires. The choice reverses if a transition needs a form
//! the copy-and-patch build cannot take — an out-of-line call, a constant pool
//! — that the executor needs anyway, which would split the two again.
//!
//! # The registers
//!
//! Every stencil has one signature, [`Stencil`]: five arguments under the
//! `preserve_none` convention, which LLVM passes in registers the callee need
//! not save, so a chain of stencils keeps them pinned and no stencil has a
//! prologue.
//!
//! | Argument | Holds | aarch64 | x86-64 |
//! | -------- | ----- | ------- | ------ |
//! | `runtime` | the run's [`Runtime`] record | `x20` | `r12` |
//! | `heap` | the heap region's bump pointer | `x21` | `r13` |
//! | `frames` | the frame region's top | `x22` | `r14` |
//! | `environment` | the current window of slots | `x23` | `r15` |
//! | `value` | the value in hand | `x24` | `rdi` |
//!
//! The heap region is a bump pointer over [`Word`]s; the frame region a stack
//! of two-word frames, a code word and the environment it resumes in, above a
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
//! | `hole_heap_exhausted`, `hole_frames_exhausted`, `hole_fuel_exhausted` | a branch the patcher aims at the region's shared exit | the exit stencil |
//! | a code word in hand | a native address, called | an instruction's address, dispatched |
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
//! - **A stencil calls nothing.** No `memcpy` (the crate is `#![no_builtins]`),
//!   no panic path (arithmetic wraps and the object is built with overflow
//!   checks and debug assertions off), no constant pool: a relocation to
//!   anything but a hole fails the build.
//! - **Every backward jump spends fuel.** Lowered code is straight-line between
//!   code-word jumps — a frame's resumption, a closure's entry — so `resume!`
//!   decrements the run's fuel and exits with [`Status::FuelExhausted`] at
//!   zero: a divergent program stops.
//!
//! # The feature gates
//!
//! The crate enables two unstable features, the only nightly surface the
//! runtime takes. `rust_preserve_none_cc` gives the convention that pins the
//! registers across a chain with no saves; `explicit_tail_calls` gives
//! `become`, the guaranteed tail call that makes a continuation a branch and
//! not a call that grows the native stack. Neither has a stable equivalent:
//! without them every transition would return to a dispatch loop, the
//! machine `gandr-core-sequent` holds. Reversal: both stabilise, and the
//! expectations below leave.
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
pub use crate::layout::Family;
pub use crate::layout::FieldOverflow;
pub use crate::layout::Flavour;
pub use crate::layout::Fuel;
pub use crate::layout::Header;
pub use crate::layout::Kind;
pub use crate::layout::Status;
pub use crate::layout::Tag;
pub use crate::layout::UnknownKind;
pub use crate::layout::UnknownStatus;
pub use crate::layout::Unnamed;

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
    /// The heap pointer when the run exited.
    heap_top: *mut Word,
    /// Why the run exited, as a status word.
    status: Word,
    /// The code-word jumps the run may still take.
    fuel: Word,
    /// The executor's current instruction; emitted code never reads it.
    instruction: *const Instruction,
}

impl Runtime
{
    /// A record for a run over the heap region `[heap, heap_limit)` and the
    /// frame region whose limit is `frame_limit` and whose base mark is
    /// `frame_base`.
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
        }
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
