//! The holes a stencil reads and continues through, in both builds.
//!
//! A stencil names its holes the same way in either build — `hole_next(…)`
//! in a `become`, `operand!` and `address!` for its two operands, `resume!`
//! for a code word in hand — and this module gives those names their meaning:
//! undefined symbols the emitter's patcher fills under
//! `--cfg gandr_stencil_object`, the current instruction's fields and the
//! dispatch table otherwise.

#[cfg(not(gandr_stencil_object))]
use crate::Instruction;
use crate::Runtime;
use crate::Word;

/// The continuation holes: symbols no object defines, each `b`/`jmp` to one
/// a relocation the patcher rewrites to a copy's address.
///
/// # Safety
/// - unsafe invariants: the stencil object is never linked; the emitter patches
///   every relocation naming these symbols to code that runs under the
///   stencils' convention before the copy runs, so no call reaches an undefined
///   symbol, and calling one is safe as the stencils' own calls are.
#[cfg(gandr_stencil_object)]
unsafe extern "rust-preserve-none" {
    /// The continuation that follows in the lowered order.
    pub safe fn hole_next(
        runtime: *mut Runtime,
        heap: *mut Word,
        frames: *mut Word,
        environment: *mut Word,
        value: Word,
    ) -> Word;
    /// The other continuation of a two-way stencil.
    pub safe fn hole_alt(
        runtime: *mut Runtime,
        heap: *mut Word,
        frames: *mut Word,
        environment: *mut Word,
        value: Word,
    ) -> Word;
    /// The exit taken when an allocation would pass the heap's limit.
    pub safe fn hole_heap_exhausted(
        runtime: *mut Runtime,
        heap: *mut Word,
        frames: *mut Word,
        environment: *mut Word,
        value: Word,
    ) -> Word;
    /// The exit taken when a push would pass the frame region's limit.
    pub safe fn hole_frames_exhausted(
        runtime: *mut Runtime,
        heap: *mut Word,
        frames: *mut Word,
        environment: *mut Word,
        value: Word,
    ) -> Word;
    /// The exit taken when a code-word jump finds no fuel left.
    pub safe fn hole_fuel_exhausted(
        runtime: *mut Runtime,
        heap: *mut Word,
        frames: *mut Word,
        environment: *mut Word,
        value: Word,
    ) -> Word;
}

/// The operand holes: their addresses are the operands, never their contents.
///
/// # Safety
/// - unsafe invariants: no stencil reads either static; each takes the address
///   alone, which the patcher rewrites to the operand's value, so the statics'
///   absence is never observed.
#[cfg(gandr_stencil_object)]
unsafe extern "C" {
    /// Operand A: its address is the operand.
    pub safe static HOLE_A: u8;
    /// Operand B: its address is the operand.
    pub safe static HOLE_B: u8;
}

/// Continue at the instruction after the current one.
///
/// # Specification
/// - requires: the current instruction is not its program's last.
/// - ensures: the runtime's instruction is the next one, and control reaches
///   its stencil with the registers unchanged.
/// - executable: none — a continuation runs inside a chain of tail calls.
///
/// # Adequacy
/// - hypothesis: L2 — every executor run continues through this hole after each
///   one-way stencil; a skipped or repeated instruction changes the answer the
///   agreement suite compares with the L machine's.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[cfg(not(gandr_stencil_object))]
pub extern "rust-preserve-none" fn hole_next(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the executor keeps the runtime's instruction inside its program.
    let current = unsafe { (*runtime).instruction };
    let next = current.wrapping_add(1);
    // SAFETY: the runtime record outlives the run.
    unsafe {
        (*runtime).instruction = next;
    }
    // SAFETY: the lowering ends every block in a delivery, so the next
    // instruction exists.
    let handler = unsafe { (*next).handler };
    become handler(runtime, heap, frames, environment, value)
}

/// Continue at the current instruction's second continuation.
///
/// # Specification
/// - requires: the current instruction's `alt` is an instruction of its
///   program.
/// - ensures: the runtime's instruction is the `alt`, and control reaches its
///   stencil with the registers unchanged.
/// - executable: none — a continuation runs inside a chain of tail calls.
///
/// # Adequacy
/// - hypothesis: L2 — every executor case split takes this hole on a match; a
///   wrong target takes the wrong arm.
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
#[cfg(not(gandr_stencil_object))]
pub extern "rust-preserve-none" fn hole_alt(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the executor keeps the runtime's instruction inside its program.
    let current = unsafe { (*runtime).instruction };
    // SAFETY: as above.
    let alt = unsafe { (*current).alt };
    // SAFETY: the runtime record outlives the run.
    unsafe {
        (*runtime).instruction = alt;
    }
    // SAFETY: a two-way stencil's instruction carries its label's address.
    let handler = unsafe { (*alt).handler };
    become handler(runtime, heap, frames, environment, value)
}

/// The heap exit, taken directly.
///
/// # Specification
/// - ensures: as `stencil_heap_exhausted`.
/// - executable: none — an exit runs inside a chain of tail calls.
///
/// # Adequacy
/// - hypothesis: L3 — an executor run over a one-object heap exits by name.
/// - witness: `tests::exits::a_full_heap_exits_by_name`
#[cfg(not(gandr_stencil_object))]
pub extern "rust-preserve-none" fn hole_heap_exhausted(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    become crate::transitions::stencil_heap_exhausted(runtime, heap, frames, environment, value)
}

/// The frame exit, taken directly.
///
/// # Specification
/// - ensures: as `stencil_frames_exhausted`.
/// - executable: none — an exit runs inside a chain of tail calls.
///
/// # Adequacy
/// - hypothesis: L3 — an executor run over a one-word frame region exits by
///   name.
/// - witness: `tests::exits::a_full_frame_region_exits_by_name`
#[cfg(not(gandr_stencil_object))]
pub extern "rust-preserve-none" fn hole_frames_exhausted(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    become crate::transitions::stencil_frames_exhausted(runtime, heap, frames, environment, value)
}

/// The fuel exit, taken directly.
///
/// # Specification
/// - ensures: as `stencil_fuel_exhausted`.
/// - executable: none — an exit runs inside a chain of tail calls.
///
/// # Adequacy
/// - hypothesis: L3 — an executor run with no fuel exits by name at its first
///   jump.
/// - witness: `tests::exits::a_run_without_fuel_exits_by_name`
#[cfg(not(gandr_stencil_object))]
pub extern "rust-preserve-none" fn hole_fuel_exhausted(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    become crate::transitions::stencil_fuel_exhausted(runtime, heap, frames, environment, value)
}

/// The current instruction, for an operand read.
///
/// # Specification
/// - requires: the executor set the runtime's instruction.
/// - executable: none — the pointer's validity is the executor's invariant.
///
/// # Adequacy
/// - hypothesis: L2 — every operand an executor stencil reads comes through
///   this pointer; a stale one reads another instruction's operand.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[cfg(not(gandr_stencil_object))]
#[inline]
pub fn current(runtime: *mut Runtime) -> *const Instruction
{
    // SAFETY: the runtime record outlives the run.
    unsafe { (*runtime).instruction }
}

/// Read an immediate operand hole (`A` or `B`) as a raw `usize`: a slot, a
/// count, an ordinal, half a header.
///
/// In the stencil object the hole is a static's address, which the emitter
/// patched biased by one; the bias is subtracted here, so the value computed
/// with carries no non-null assumption.
#[cfg(gandr_stencil_object)]
macro_rules! operand {
    ($runtime:ident,A) => {{
        let _ = $runtime;
        (&raw const $crate::holes::HOLE_A).addr().wrapping_sub(1)
    }};
    ($runtime:ident,B) => {{
        let _ = $runtime;
        (&raw const $crate::holes::HOLE_B).addr().wrapping_sub(1)
    }};
}

/// Read an immediate operand hole (`A` or `B`) as a raw `usize` from the
/// current instruction.
#[cfg(not(gandr_stencil_object))]
macro_rules! operand {
    ($runtime:ident,A) => {{
        let instruction = $crate::holes::current($runtime);
        // SAFETY: the executor's instruction is an element of its program.
        usize::from(unsafe { (*instruction).a })
    }};
    ($runtime:ident,B) => {{
        let instruction = $crate::holes::current($runtime);
        // SAFETY: as above.
        usize::from(unsafe { (*instruction).b })
    }};
}

/// Read an address operand hole (`A` or `B`) as a [`Word`]: a code word, a
/// constant's address, a shared stub. Never null, so patched unbiased.
#[cfg(gandr_stencil_object)]
macro_rules! address {
    ($runtime:ident,A) => {{
        let _ = $runtime;
        $crate::Word::from((&raw const $crate::holes::HOLE_A).expose_provenance())
    }};
    ($runtime:ident,B) => {{
        let _ = $runtime;
        $crate::Word::from((&raw const $crate::holes::HOLE_B).expose_provenance())
    }};
}

/// Read an address operand hole (`A` or `B`) as a [`Word`] from the current
/// instruction.
#[cfg(not(gandr_stencil_object))]
macro_rules! address {
    ($runtime:ident,A) => {{
        let instruction = $crate::holes::current($runtime);
        // SAFETY: the executor's instruction is an element of its program.
        unsafe { (*instruction).a }
    }};
    ($runtime:ident,B) => {{
        let instruction = $crate::holes::current($runtime);
        // SAFETY: as above.
        unsafe { (*instruction).b }
    }};
}

/// Jump to the code word `code` with the registers given, spending one unit
/// of fuel; at zero fuel, take the fuel exit instead.
///
/// In the stencil object a code word is a native address, called; in the
/// executor it is an instruction's address, made current and dispatched.
macro_rules! resume {
    ($code:expr, $runtime:ident, $heap:expr, $frames:expr, $environment:expr, $value:expr) => {{
        let code: $crate::Word = $code;
        let heap: *mut $crate::Word = $heap;
        let frames: *mut $crate::Word = $frames;
        let environment: *mut $crate::Word = $environment;
        let value: $crate::Word = $value;
        // SAFETY: the runtime record outlives the run.
        let fuel = usize::from(unsafe { (*$runtime).fuel });
        if fuel == 0 {
            become $crate::holes::hole_fuel_exhausted($runtime, heap, frames, environment, value)
        }
        // SAFETY: as above.
        unsafe { (*$runtime).fuel = $crate::Word::from(fuel.wrapping_sub(1)) };
        let handler = $crate::holes::target($runtime, code);
        become handler($runtime, heap, frames, environment, value)
    }};
}

/// The stencil a code word reaches: the native code at its address.
///
/// # Specification
/// - requires: `code` is the address of a stencil copy the emitter patched.
/// - executable: none — a code address carries no checkable property.
///
/// # Adequacy
/// - hypothesis: L2 — every frame and closure entry of emitted code resumes
///   through this conversion.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[cfg(gandr_stencil_object)]
#[inline]
pub fn target(
    runtime: *mut Runtime,
    code: Word,
) -> crate::Stencil
{
    let _ = runtime;
    // SAFETY: a code word in emitted code is a stencil copy's address, which
    // runs under the stencils' convention.
    unsafe {
        core::mem::transmute::<*const (), crate::Stencil>(code.to_pointer::<()>().cast_const())
    }
}

/// The stencil a code word reaches: the instruction at its address, made
/// current.
///
/// # Specification
/// - requires: `code` is the address of an instruction of the running program.
/// - ensures: the runtime's instruction is that instruction.
/// - executable: none — an instruction address carries no checkable property.
///
/// # Adequacy
/// - hypothesis: L2 — every frame and closure entry of an executor program
///   resumes through this conversion; a stale current instruction reads the
///   wrong operands after the jump.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[cfg(not(gandr_stencil_object))]
#[inline]
pub fn target(
    runtime: *mut Runtime,
    code: Word,
) -> crate::Stencil
{
    let instruction = code.to_pointer::<Instruction>().cast_const();
    // SAFETY: the runtime record outlives the run.
    unsafe {
        (*runtime).instruction = instruction;
    }
    // SAFETY: the code word is an instruction of the running program.
    unsafe { (*instruction).handler }
}

pub(crate) use address;
pub(crate) use operand;
pub(crate) use resume;
