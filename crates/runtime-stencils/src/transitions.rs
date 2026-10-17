//! The stencils: one function per transition of the L machine's lowered
//! form.
//!
//! The groups follow the machine's transitions:
//!
//! | Transition | Stencils |
//! | ---------- | -------- |
//! | a value delivered | `ret`, `halt`, `unmatched` |
//! | a binder loaded as a continuation | `pushk`, `bind`, `alias`, `alias_top` |
//! | constructor dispatch | `match`, `field`, `match_tag`, `select_field` |
//! | constructor introduction | `push`, `ctor1`, `ctor2`, `ctor3`, `ctor_n`, `const` |
//! | a variable read | `var` |
//! | a closure introduced and entered | `closure`, `enter_apply`, `enter_force`, `enter_fix` |
//! | an observation | `invoke_apply`, `invoke_force`, `invoke_force_value`, `apply_frame`, `argument_frame` |
//! | an observation's continuation loaded | `pushf`, `push_apply`, `push_force`, `push_fields`, `shrink`, `shrink_top`, `mark` |
//! | a loop | `jump` |
//! | an exit | `heap_exhausted`, `frames_exhausted`, `fuel_exhausted`, `stuck` |
//!
//! An observation checks that it observes a closure: an opaque constant, or
//! any other object, takes the stuck exit rather than a code word it does not
//! hold.
//!
//! Operand A and B are the instruction's two holes; each stencil's
//! documentation says which it reads and as what. A window slot, a field
//! position and a count are immediates; a code word, a constant and a shared
//! stub are addresses.

use crate::Runtime;
use crate::Word;
use crate::holes::address;
use crate::holes::hole_alt;
use crate::holes::hole_frames_exhausted;
use crate::holes::hole_heap_exhausted;
use crate::holes::hole_next;
use crate::holes::hole_stuck;
use crate::holes::operand;
use crate::holes::resume;
use crate::layout;

/// Load a constant's address into the value register: a literal, or a
/// constructor of no fields, laid out once in the item's data.
///
/// # Specification
/// - ensures: the value register holds address operand A.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over the named, generated and
///   corpus programs; a wrong constant changes an answer read back.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_const(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    let constant = address!(runtime, A);
    become hole_next(runtime, heap, frames, environment, constant)
}

/// Read a bound variable: the value register takes slot A.
///
/// # Specification
/// - requires: slot A lies inside the window and is bound.
/// - ensures: the value register holds slot A.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential; reading the wrong slot
///   changes the stated answer of a named program binding two variables, and of
///   the corpus programs that do.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_var(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    let value = unsafe { *slot };
    become hole_next(runtime, heap, frames, environment, value)
}

/// Bind the value in hand to slot A: delivery to `μ̃x. s`.
///
/// # Specification
/// - requires: slot A lies inside the window.
/// - ensures: slot A holds the value register.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential; a bind to the wrong slot
///   changes a later variable read.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_bind(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    unsafe {
        *slot = value;
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Push the value in hand as a constructor field awaiting its siblings.
///
/// # Specification
/// - ensures: the frame region grows by one word holding the value, or the
///   frame exit is taken at its limit.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over programs building tuples;
///   a lost or misplaced field changes the tuple read back, and a one-word
///   frame region exits.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::exits::a_full_frame_region_exits_by_name`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_push(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let limit = unsafe { (*runtime).frame_limit };
    if frames >= limit {
        become hole_frames_exhausted(runtime, heap, frames, environment, value)
    }
    // SAFETY: `frames` is below the limit.
    unsafe {
        *frames = value;
    }
    become hole_next(runtime, heap, frames.wrapping_add(1), environment, value)
}

/// Generate a constructor stencil over a fixed number of pushed fields.
macro_rules! constructor {
    ($name:ident, $count:literal) => {
        /// Allocate a constructor over the fields pushed before it, the first
        /// pushed first: operand A is its header's low 32 bits, operand B its
        /// family field.
        ///
        /// # Specification
        /// - requires: the fields were pushed just below the frame region's top.
        /// - ensures: the value register holds a fresh object of the header and the
        ///   fields, popped; or the heap exit is taken.
        /// - executable: none — a stencil runs only inside a chain of tail calls whose
        ///   state no predicate can observe.
        ///
        /// # Adequacy
        /// - hypothesis: L2 — the agreement differential over programs building one-,
        ///   two- and three-field constructors; a reordered field or a wrong header
        ///   changes the value read back.
        /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
        /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
        #[unsafe(no_mangle)]
        pub extern "rust-preserve-none" fn $name(
            runtime: *mut Runtime,
            heap: *mut Word,
            frames: *mut Word,
            environment: *mut Word,
            value: Word,
        ) -> Word
        {
            let next = heap.wrapping_add(1_usize.wrapping_add($count));
            // SAFETY: the runtime record outlives the run.
            let limit = unsafe { (*runtime).heap_limit };
            if next > limit {
                become hole_heap_exhausted(runtime, heap, frames, environment, value)
            }
            let header =
                operand!(runtime, A) | operand!(runtime, B).wrapping_shl(layout::FAMILY_SHIFT);
            // SAFETY: the object fits below the heap's limit.
            unsafe { *heap = Word::from(header) };
            let fields = frames.wrapping_sub($count);
            let mut index = 0_usize;
            while index < $count {
                // SAFETY: the lowering pushed the fields below the top.
                let field = unsafe { *fields.wrapping_add(index) };
                // SAFETY: the object fits below the heap's limit.
                unsafe { *heap.wrapping_add(index.wrapping_add(1)) = field };
                index = index.wrapping_add(1);
            }
            become hole_next(runtime, next, fields, environment, Word::from_pointer(heap))
        }
    };
}

constructor!(stencil_ctor1, 1_usize);
constructor!(stencil_ctor2, 2_usize);
constructor!(stencil_ctor3, 3_usize);

/// Allocate a constructor over as many pushed fields as its header's arity:
/// operand A is the header's low 32 bits, operand B its family field.
///
/// # Specification
/// - requires: as the fixed-arity constructors.
/// - ensures: as the fixed-arity constructors, the count read from A.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs building
///   constructors of four fields or more.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_ctor_n(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let low = operand!(runtime, A);
    let count = low.wrapping_shr(layout::ARITY_SHIFT) & layout::ARITY_MASK;
    let next = heap.wrapping_add(count.wrapping_add(1));
    // SAFETY: the runtime record outlives the run.
    let limit = unsafe { (*runtime).heap_limit };
    if next > limit {
        become hole_heap_exhausted(runtime, heap, frames, environment, value)
    }
    let header = low | operand!(runtime, B).wrapping_shl(layout::FAMILY_SHIFT);
    // SAFETY: the object fits below the heap's limit.
    unsafe {
        *heap = Word::from(header);
    }
    let fields = frames.wrapping_sub(count);
    let mut index = 0_usize;
    while index < count {
        // SAFETY: the lowering pushed the fields below the top.
        let field = unsafe { *fields.wrapping_add(index) };
        // SAFETY: the object fits below the heap's limit.
        unsafe {
            *heap.wrapping_add(index.wrapping_add(1)) = field;
        }
        index = index.wrapping_add(1);
    }
    become hole_next(runtime, next, fields, environment, Word::from_pointer(heap))
}

/// Test the constructor in hand against one case arm: the arm on a match,
/// the next test otherwise. Operand A is the arm's header's low 32 bits,
/// operand B its family field.
///
/// # Specification
/// - requires: the value register addresses an object.
/// - ensures: control reaches `hole_alt` exactly when the object's header is
///   the arm's, family included.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over sum cases and tuple
///   splits; a wrong comparison takes the wrong arm or sticks.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_match(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: a positive value in hand addresses an object.
    let header = usize::from(unsafe { *value.to_pointer::<Word>() });
    let expected = operand!(runtime, A) | operand!(runtime, B).wrapping_shl(layout::FAMILY_SHIFT);
    if header == expected {
        become hole_alt(runtime, heap, frames, environment, value)
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Bind field B of the object in hand to slot A: one binder of a matched
/// arm.
///
/// # Specification
/// - requires: the value register addresses an object of more than B fields;
///   slot A lies inside the window.
/// - ensures: slot A holds field B.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over tuple splits of two
///   fields; binding the wrong field swaps them in the answer.
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_field(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let object = value.to_pointer::<Word>();
    let position = object.wrapping_add(operand!(runtime, B).wrapping_add(1));
    // SAFETY: the arm matched the header, so the field exists.
    let field = unsafe { *position };
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    unsafe {
        *slot = field;
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Load a binder or a match as a continuation: push a frame resuming at code
/// operand A in this window, and bind the covariable in slot B to the mark
/// above it.
///
/// # Specification
/// - requires: slot B lies inside the window.
/// - ensures: the frame region grows by one frame and slot B holds its mark; or
///   the frame exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over binds whose bound
///   computation returns; a wrong frame resumes the wrong code.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::the_generated_programs_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_pushk(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let top = frames.wrapping_add(2);
    // SAFETY: the runtime record outlives the run.
    let limit = unsafe { (*runtime).frame_limit };
    if top > limit {
        become hole_frames_exhausted(runtime, heap, frames, environment, value)
    }
    let code = address!(runtime, A);
    // SAFETY: the frame fits below the limit.
    unsafe {
        *frames = code;
    }
    // SAFETY: as above.
    unsafe {
        *frames.wrapping_add(1) = Word::from_pointer(environment);
    }
    let slot = environment.wrapping_add(operand!(runtime, B));
    // SAFETY: the lowering assigned slot B inside the window.
    unsafe {
        *slot = Word::from_pointer(top);
    }
    become hole_next(runtime, heap, top, environment, value)
}

/// Load a covariable as a continuation: shrink to the mark slot B holds and
/// bind the covariable in slot A to it.
///
/// # Specification
/// - requires: both slots lie inside the window, slot B bound to a mark.
/// - ensures: the frame region's top and slot A are the mark in slot B.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs whose `μ`
///   aliases an outer covariable.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_alias(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let source = environment.wrapping_add(operand!(runtime, B));
    // SAFETY: the lowering assigned slot B inside the window.
    let mark = unsafe { *source };
    let target = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    unsafe {
        *target = mark;
    }
    become hole_next(runtime, heap, mark.to_pointer(), environment, value)
}

/// Load `★` as a continuation: shrink to the base mark and bind the
/// covariable in slot A to it.
///
/// # Specification
/// - requires: slot A lies inside the window.
/// - ensures: the frame region's top and slot A are the base mark.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential; every named and generated
///   program's outermost `μ` aliases `★`.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_alias_top(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let base = unsafe { (*runtime).frame_base };
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    unsafe {
        *slot = Word::from_pointer(base);
    }
    become hole_next(runtime, heap, base, environment, value)
}

/// Deliver the value in hand to the covariable in slot A: shrink to its
/// mark, pop the frame below it and resume there.
///
/// # Specification
/// - requires: slot A holds a mark at or above the base, so a frame — the
///   sentinel at the least — lies below it.
/// - ensures: control resumes at the popped frame's code in its window, one
///   unit of fuel spent; or the fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential; every program that binds a
///   computation's result resumes through this stencil, and a run with no fuel
///   exits by name.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::exits::a_run_without_fuel_exits_by_name`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_ret(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window, bound to a mark.
    let mark = unsafe { *slot }.to_pointer::<Word>();
    let frame = mark.wrapping_sub(2);
    // SAFETY: two words below a mark above the sentinel are a frame.
    let code = unsafe { *frame };
    // SAFETY: as above.
    let resumed = unsafe { *frame.wrapping_add(1) }.to_pointer::<Word>();
    resume!(code, runtime, heap, frame, resumed, value)
}

/// Allocate a closure entering at code operand A whose header's low 32 bits
/// are operand B: its flavour in the tag, its capture count in the arity.
/// The captures are the window's first slots.
///
/// # Specification
/// - requires: the window holds at least as many slots as the header's arity.
/// - ensures: the value register holds a fresh closure; or the heap exit is
///   taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs with
///   thunks, fixpoints and functions; a lost capture changes a variable the
///   body reads, structurally compared at readback.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_closure(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let header = operand!(runtime, B);
    let count = header.wrapping_shr(layout::ARITY_SHIFT) & layout::ARITY_MASK;
    let next = heap.wrapping_add(count.wrapping_add(2));
    // SAFETY: the runtime record outlives the run.
    let limit = unsafe { (*runtime).heap_limit };
    if next > limit {
        become hole_heap_exhausted(runtime, heap, frames, environment, value)
    }
    let code = address!(runtime, A);
    // SAFETY: the closure fits below the heap's limit.
    unsafe {
        *heap = Word::from(header);
    }
    // SAFETY: as above.
    unsafe {
        *heap.wrapping_add(1) = code;
    }
    let mut index = 0_usize;
    while index < count {
        // SAFETY: the window holds the captured slots.
        let capture = unsafe { *environment.wrapping_add(index) };
        // SAFETY: the closure fits below the heap's limit.
        unsafe {
            *heap.wrapping_add(index.wrapping_add(2)) = capture;
        }
        index = index.wrapping_add(1);
    }
    become hole_next(runtime, next, frames, environment, Word::from_pointer(heap))
}

/// Generate a closure entry: allocate a window of A slots, copy the closure's
/// B captures into its first slots, and bind the entry's own binders above.
macro_rules! entry {
    (
        $name:ident,
        $summary:literal,
        $ensures:literal,
        | $window:ident, $closure:ident, $value:ident, $frames:ident, $at:ident | $bind:block
    ) => {
        #[doc = $summary]
        ///
        /// # Specification
        /// - requires: the environment register addresses the closure entered,
        ///   which holds operand B captures.
        #[doc = $ensures]
        /// - executable: none — a stencil runs only inside a chain of tail
        ///   calls whose state no predicate can observe.
        ///
        /// # Adequacy
        /// - hypothesis: L2 — the agreement differential over
        ///   corpus programs applying functions, forcing thunks and recursing
        ///   through fixpoints; a capture or binder in the wrong slot changes
        ///   the answer read back.
        /// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
        #[unsafe(no_mangle)]
        pub extern "rust-preserve-none" fn $name(
            runtime: *mut Runtime,
            heap: *mut Word,
            $frames: *mut Word,
            environment: *mut Word,
            $value: Word,
        ) -> Word
        {
            let next = heap.wrapping_add(operand!(runtime, A));
            // SAFETY: the runtime record outlives the run.
            let limit = unsafe { (*runtime).heap_limit };
            if next > limit {
                become hole_heap_exhausted(runtime, heap, $frames, environment, $value)
            }
            let $closure = environment;
            let $window = heap;
            let $at = operand!(runtime, B);
            let mut index = 0_usize;
            while index < $at {
                // SAFETY: the closure holds B captures after its two words.
                let capture = unsafe { *$closure.wrapping_add(index.wrapping_add(2)) };
                // SAFETY: the window fits below the heap's limit.
                unsafe { *$window.wrapping_add(index) = capture };
                index = index.wrapping_add(1);
            }
            $bind
            become hole_next(runtime, next, $frames, $window, $value)
        }
    };
}

entry!(
    stencil_enter_apply,
    "Enter an application arm: the argument at slot B, the return mark above.",
    "- ensures: the environment register is a fresh window holding the \
     captures, the argument at slot B and the frame region's top at B + 1; or \
     the heap exit is taken.",
    |window, closure, value, frames, at| {
        let _ = closure;
        // SAFETY: the window has A slots, A above B + 1.
        unsafe {
            *window.wrapping_add(at) = value;
        }
        // SAFETY: as above.
        unsafe {
            *window.wrapping_add(at.wrapping_add(1)) = Word::from_pointer(frames);
        }
    }
);
entry!(
    stencil_enter_force,
    "Enter a thunk or a force arm: the return mark at slot B.",
    "- ensures: the environment register is a fresh window holding the \
     captures and the frame region's top at slot B; or the heap exit is taken.",
    |window, closure, value, frames, at| {
        let _ = (closure, value);
        // SAFETY: the window has A slots, A above B.
        unsafe {
            *window.wrapping_add(at) = Word::from_pointer(frames);
        }
    }
);
entry!(
    stencil_enter_fix,
    "Enter a fixpoint: itself at slot B, the return mark above.",
    "- ensures: the environment register is a fresh window holding the \
     captures, the fixpoint itself at slot B and the frame region's top at B + \
     1; or the heap exit is taken.",
    |window, closure, value, frames, at| {
        let _ = value;
        // SAFETY: the window has A slots, A above B + 1.
        unsafe {
            *window.wrapping_add(at) = Word::from_pointer(closure);
        }
        // SAFETY: as above.
        unsafe {
            *window.wrapping_add(at.wrapping_add(1)) = Word::from_pointer(frames);
        }
    }
);

/// Observe the closure `function` by application to `argument`: enter its
/// code with the closure in the environment register, an object's dispatch
/// with the application observed; take the stuck exit, `function` in hand and
/// the application observed, when `function` is neither.
macro_rules! apply {
    (
        $runtime:ident, $heap:expr, $frames:expr, $environment:expr, $function:expr, $argument:expr
    ) => {{
        let function: Word = $function;
        let argument: Word = $argument;
        let object = function.to_pointer::<Word>();
        // SAFETY: a positive value in hand addresses an object.
        let header = usize::from(unsafe { *object });
        let flavour = header & layout::OBSERVED_MASK;
        if flavour != layout::APPLY_CLOSURE {
            // SAFETY: the runtime record outlives the run.
            unsafe {
                (*$runtime).observed = layout::OBSERVED_APPLY;
            }
            if flavour != layout::OBJECT_CLOSURE {
                become hole_stuck($runtime, $heap, $frames, $environment, function)
            }
        }
        // SAFETY: a closure's second word is its entry's code word.
        let code = unsafe { *object.wrapping_add(1) };
        resume!(code, $runtime, $heap, $frames, object, argument)
    }};
}

/// Observe the closure `thunk` by a force: enter its code with the closure
/// in the environment register, an object's dispatch with the force observed;
/// take the stuck exit, `thunk` in hand and the force observed, when `thunk`
/// is no closure, an application arm's or a suspended capture.
macro_rules! force {
    ($runtime:ident, $heap:expr, $frames:expr, $environment:expr, $thunk:expr) => {{
        let thunk: Word = $thunk;
        let object = thunk.to_pointer::<Word>();
        // SAFETY: a positive value in hand addresses an object.
        let header = usize::from(unsafe { *object });
        let flavour = header & layout::OBSERVED_MASK;
        if header & layout::KIND_MASK != layout::KIND_CLOSURE
            || flavour == layout::APPLY_CLOSURE
            || flavour >= layout::OBJECT_CLOSURE
        {
            // SAFETY: the runtime record outlives the run.
            unsafe {
                (*$runtime).observed = layout::OBSERVED_FORCE;
            }
            if flavour != layout::OBJECT_CLOSURE {
                become hole_stuck($runtime, $heap, $frames, $environment, thunk)
            }
        }
        // SAFETY: a closure's second word is its entry's code word.
        let code = unsafe { *object.wrapping_add(1) };
        resume!(code, $runtime, $heap, $frames, object, Word::ZERO)
    }};
}

/// Observe the value `pair` by the projection whose observed word is
/// `side`: enter an object's dispatch with the projection observed; take the
/// stuck exit, `pair` in hand and the projection observed, for any other
/// value.
macro_rules! project {
    ($runtime:ident, $heap:expr, $frames:expr, $environment:expr, $pair:expr, $side:expr) => {{
        let pair: Word = $pair;
        let object = pair.to_pointer::<Word>();
        // SAFETY: a positive value in hand addresses an object.
        let header = usize::from(unsafe { *object });
        // SAFETY: the runtime record outlives the run.
        unsafe {
            (*$runtime).observed = $side;
        }
        if header & layout::OBSERVED_MASK != layout::OBJECT_CLOSURE {
            become hole_stuck($runtime, $heap, $frames, $environment, pair)
        }
        // SAFETY: a closure's second word is its entry's code word.
        let code = unsafe { *object.wrapping_add(1) };
        resume!(code, $runtime, $heap, $frames, object, Word::ZERO)
    }};
}

/// Apply the function in slot A to the argument in slot B.
///
/// # Specification
/// - requires: both slots lie inside the window, slot A holding a closure; the
///   continuation is loaded.
/// - ensures: control enters the closure's code, one unit of fuel spent; or the
///   fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs applying
///   functions to arguments.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_invoke_apply(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    let function_slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    let function = unsafe { *function_slot };
    let argument_slot = environment.wrapping_add(operand!(runtime, B));
    // SAFETY: the lowering assigned slot B inside the window.
    let argument = unsafe { *argument_slot };
    apply!(runtime, heap, frames, environment, function, argument)
}

/// Force the thunk in slot A.
///
/// # Specification
/// - requires: slot A lies inside the window and holds a closure; the
///   continuation is loaded.
/// - ensures: control enters the closure's code, one unit of fuel spent; or the
///   fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs forcing
///   thunks they bound.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_invoke_force(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    let thunk = unsafe { *slot };
    force!(runtime, heap, frames, environment, thunk)
}

/// Force the thunk in hand. A force frame resumes here, so it is also the
/// shared stub every force frame's code word names.
///
/// # Specification
/// - requires: the value register holds a closure; the continuation is loaded.
/// - ensures: control enters the closure's code, one unit of fuel spent; or the
///   fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs with
///   nominal matches, whose branches are forced here.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_invoke_force_value(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    force!(runtime, heap, frames, environment, value)
}

/// The shared stub an application frame resumes: the function arrives in
/// hand, the argument in the frame's second word, which is the environment
/// register on resumption.
///
/// # Specification
/// - requires: the value register holds a closure.
/// - ensures: as [`stencil_invoke_apply`].
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs applying
///   a returned function and matching nominally.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_apply_frame(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    apply!(
        runtime,
        heap,
        frames,
        environment,
        value,
        Word::from_pointer(environment)
    )
}

/// The shared stub a fold's cell frame resumes: the folded tail arrives in
/// hand as the argument, the closure that answers the cell in the frame's
/// second word, which is the environment register on resumption.
///
/// # Specification
/// - requires: the environment register holds a closure.
/// - ensures: as [`stencil_invoke_apply`], the value in hand the argument.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs folding
///   native lists of more than one cell.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_argument_frame(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    apply!(
        runtime,
        heap,
        frames,
        environment,
        Word::from_pointer(environment),
        value
    )
}

/// Project the left component of the object in hand. A left projection's
/// frame resumes here, so it is also the shared stub every such frame's code
/// word names.
///
/// # Specification
/// - requires: the value register holds an object; the continuation is loaded.
/// - ensures: control enters the object's dispatch with the left projection
///   observed, one unit of fuel spent; or the fuel exit or, for anything but a
///   copattern object, the stuck exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — both tiers project a lazy pair's components and stick
///   projecting a function; a swapped side answers the other component.
/// - witness: `tests::agreement::an_object_answers_its_arms_and_sticks_on_the_rest`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_project_left(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    project!(
        runtime,
        heap,
        frames,
        environment,
        value,
        layout::OBSERVED_PROJECT_LEFT
    )
}

/// Project the right component of the object in hand; also the right
/// projection frames' shared stub.
///
/// # Specification
/// - requires: as [`stencil_project_left`].
/// - ensures: as [`stencil_project_left`], the right projection observed.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — as [`stencil_project_left`].
/// - witness: `tests::agreement::an_object_answers_its_arms_and_sticks_on_the_rest`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_project_right(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    project!(
        runtime,
        heap,
        frames,
        environment,
        value,
        layout::OBSERVED_PROJECT_RIGHT
    )
}

/// Dispatch a copattern object's observation: continue at `hole_alt`, the
/// arm's entry, when the observed word is operand A.
///
/// # Specification
/// - requires: the environment register holds the object entered, the value
///   register the observation's argument.
/// - ensures: control reaches `hole_alt` when the record's observed word is
///   operand A and the next instruction otherwise, the registers unchanged.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — both tiers project each side of a lazy pair and apply an
///   object of several arms; a dispatch that ignores the observed word enters
///   the first arm for every observation.
/// - witness: `tests::agreement::an_object_answers_its_arms_and_sticks_on_the_rest`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_arm(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let observed = unsafe { (*runtime).observed };
    if usize::from(observed) == operand!(runtime, A) {
        become hole_alt(runtime, heap, frames, environment, value)
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// End a copattern object's dispatch: no arm answers the observation, so the
/// stuck exit takes the object in hand, the observed word as the observation
/// wrote it.
///
/// # Specification
/// - requires: the environment register holds the object entered.
/// - ensures: the stuck exit is taken with the object in hand.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — forcing a lazy pair sticks naming the pair and the force
///   on both tiers.
/// - witness: `tests::agreement::an_object_answers_its_arms_and_sticks_on_the_rest`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_unobserved(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    become hole_stuck(
        runtime,
        heap,
        frames,
        environment,
        Word::from_pointer(environment),
    )
}

/// Test the value in hand for a suspended capture: continue at `hole_alt`,
/// where the cut runs it against its consumer, when it is one.
///
/// # Specification
/// - requires: the value register holds an object.
/// - ensures: control reaches `hole_alt` when the value is a suspended capture
///   and the next instruction otherwise, the registers unchanged.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — a capture bound by name and then delivered to `★` runs
///   its body there on both tiers; a missed test halts with the capture.
/// - witness: `tests::agreement::a_suspended_capture_runs_against_the_consumer_it_meets`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_captured(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: a positive value in hand addresses an object.
    let header = usize::from(unsafe { *value.to_pointer::<Word>() });
    if header & layout::OBSERVED_MASK == layout::CAPTURE_CLOSURE {
        become hole_alt(runtime, heap, frames, environment, value)
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Run the suspended capture in hand against the consumer loaded on top.
///
/// # Specification
/// - requires: the value register holds a suspended capture; its consumer is
///   loaded.
/// - ensures: control enters the capture's code with it in the environment
///   register, one unit of fuel spent; or the fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — as [`stencil_captured`]: the capture's body observes the
///   unit it returns by a force and sticks there.
/// - witness: `tests::agreement::a_suspended_capture_runs_against_the_consumer_it_meets`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_run_capture(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    _environment: *mut Word,
    value: Word,
) -> Word
{
    let object = value.to_pointer::<Word>();
    // SAFETY: a closure's second word is its entry's code word.
    let code = unsafe { *object.wrapping_add(1) };
    resume!(code, runtime, heap, frames, object, Word::ZERO)
}

/// Read constant A's word: its value in hand when unfolded, `hole_alt`
/// otherwise.
///
/// # Specification
/// - requires: the record's constant table holds word A.
/// - ensures: the value register holds the constant's value and control reaches
///   the next instruction when it is unfolded; control reaches `hole_alt` with
///   the registers unchanged otherwise.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — a constant read twice is one value, its thunk's body run
///   once per force; a constant read before it is unfolded unfolds it.
/// - witness: `tests::agreement::constants_unfold_once_and_a_cycle_is_stuck`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_global(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let table = unsafe { (*runtime).globals };
    let slot = table.wrapping_add(operand!(runtime, A));
    // SAFETY: the table holds word A.
    let word = unsafe { *slot };
    if usize::from(word) > 1 {
        become hole_next(runtime, heap, frames, environment, word)
    }
    become hole_alt(runtime, heap, frames, environment, value)
}

/// Begin unfolding constant A: mark it unfolding and continue, or continue
/// at `hole_alt` when it is already unfolding — its definition needs its own
/// value.
///
/// # Specification
/// - requires: the record's constant table holds word A, which is not a value.
/// - ensures: word A is one and control reaches the next instruction when it
///   was zero; control reaches `hole_alt` otherwise; the registers unchanged.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — a constant whose definition is a pair holding itself
///   sticks as cyclic on both tiers; one whose definition suspends itself in a
///   thunk unfolds.
/// - witness: `tests::agreement::constants_unfold_once_and_a_cycle_is_stuck`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_unfold(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let table = unsafe { (*runtime).globals };
    let slot = table.wrapping_add(operand!(runtime, A));
    // SAFETY: the table holds word A.
    if unsafe { *slot } != Word::ZERO {
        become hole_alt(runtime, heap, frames, environment, value)
    }
    // SAFETY: as above.
    unsafe {
        *slot = Word(1);
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// End unfolding constant A: its word takes the value in hand.
///
/// # Specification
/// - requires: the record's constant table holds word A.
/// - ensures: word A is the value register.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — as [`stencil_global`]: a second read finds the value the
///   first unfolding wrote.
/// - witness: `tests::agreement::constants_unfold_once_and_a_cycle_is_stuck`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_set_global(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let table = unsafe { (*runtime).globals };
    let slot = table.wrapping_add(operand!(runtime, A));
    // SAFETY: the table holds word A.
    unsafe {
        *slot = value;
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Push a two-word frame of code word `code` and second word `word`.
macro_rules! push_frame {
    (
        $runtime:ident,
        $heap:expr,
        $frames:expr,
        $environment:expr,
        $value:expr,
        $code:expr,
        $word:expr
    ) => {{
        let top = $frames.wrapping_add(2);
        // SAFETY: the runtime record outlives the run.
        let limit = unsafe { (*$runtime).frame_limit };
        if top > limit {
            become hole_frames_exhausted($runtime, $heap, $frames, $environment, $value)
        }
        let code: Word = $code;
        let word: Word = $word;
        // SAFETY: the frame fits below the limit.
        unsafe { *$frames = code };
        // SAFETY: as above.
        unsafe { *$frames.wrapping_add(1) = word };
        become hole_next($runtime, $heap, top, $environment, $value)
    }};
}

/// Load a binder or a match as an observation's continuation: push a frame
/// resuming at code operand A in this window.
///
/// # Specification
/// - ensures: the frame region grows by one frame; or the frame exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs binding a
///   function's result.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_pushf(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    push_frame!(
        runtime,
        heap,
        frames,
        environment,
        value,
        address!(runtime, A),
        Word::from_pointer(environment)
    )
}

/// Load an application frame: resume at the stub operand B with the
/// argument in slot A.
///
/// # Specification
/// - requires: slot A lies inside the window.
/// - ensures: the frame region grows by one frame; or the frame exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs applying
///   curried functions.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_push_apply(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    let argument = unsafe { *slot };
    push_frame!(
        runtime,
        heap,
        frames,
        environment,
        value,
        address!(runtime, B),
        argument
    )
}

/// Load a force frame: resume at the stub operand A.
///
/// # Specification
/// - ensures: the frame region grows by one frame; or the frame exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs forcing a
///   returned thunk.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_push_force(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    push_frame!(
        runtime,
        heap,
        frames,
        environment,
        value,
        address!(runtime, A),
        Word::ZERO
    )
}

/// Load one application frame per field of the constructor in slot A, the
/// first field's on top, each resuming at the stub operand B: a nominal
/// match's branch then meets its fields in order.
///
/// # Specification
/// - requires: slot A lies inside the window and holds a constructor.
/// - ensures: the frame region grows by one frame per field; or the frame exit
///   is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs matching
///   constructors of several fields; a reversed order swaps the branch's
///   arguments.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_push_fields(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    let object = unsafe { *slot }.to_pointer::<Word>();
    // SAFETY: the slot holds a constructor, whose first word is its header.
    let header = usize::from(unsafe { *object });
    let count = header.wrapping_shr(layout::ARITY_SHIFT) & layout::ARITY_MASK;
    let top = frames.wrapping_add(count.wrapping_mul(2));
    // SAFETY: the runtime record outlives the run.
    let limit = unsafe { (*runtime).frame_limit };
    if top > limit {
        become hole_frames_exhausted(runtime, heap, frames, environment, value)
    }
    let code = address!(runtime, B);
    let mut index = 0_usize;
    while index < count {
        let frame = top.wrapping_sub(index.wrapping_add(1).wrapping_mul(2));
        // SAFETY: the frames fit below the limit.
        unsafe {
            *frame = code;
        }
        // SAFETY: the object has `count` fields after its header.
        let field = unsafe { *object.wrapping_add(index.wrapping_add(1)) };
        // SAFETY: the frames fit below the limit.
        unsafe {
            *frame.wrapping_add(1) = field;
        }
        index = index.wrapping_add(1);
    }
    become hole_next(runtime, heap, top, environment, value)
}

/// Load a covariable as an observation's continuation: shrink to the mark
/// slot A holds.
///
/// # Specification
/// - requires: slot A lies inside the window and holds a mark.
/// - ensures: the frame region's top is the mark in slot A.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs whose
///   function body tail-calls another.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_shrink(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window, bound to a mark.
    let mark = unsafe { *slot }.to_pointer::<Word>();
    become hole_next(runtime, heap, mark, environment, value)
}

/// Load `★` as an observation's continuation: shrink to the base mark.
///
/// # Specification
/// - ensures: the frame region's top is the base mark.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over the forced entries of
///   corpus declarations, whose observation's continuation is `★`.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_shrink_top(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: the runtime record outlives the run.
    let base = unsafe { (*runtime).frame_base };
    become hole_next(runtime, heap, base, environment, value)
}

/// Test the constructor in hand against one nominal ordinal, operand A: the
/// branch on a match, the next test otherwise.
///
/// # Specification
/// - requires: the value register addresses an object.
/// - ensures: control reaches `hole_alt` exactly when the object is a
///   datatype's constructor of ordinal A, whatever its family.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs recursing
///   over Nat and lists; a wrong ordinal takes the wrong branch.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_match_tag(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    // SAFETY: a positive value in hand addresses an object.
    let header = usize::from(unsafe { *value.to_pointer::<Word>() });
    let expected = layout::KIND_DATA | operand!(runtime, A).wrapping_shl(layout::TAG_SHIFT);
    if header & layout::ORDINAL_MASK == expected {
        become hole_alt(runtime, heap, frames, environment, value)
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Bind the covariable in slot A to the frame region's top: a `μ` whose
/// continuation an observation loaded.
///
/// # Specification
/// - requires: slot A lies inside the window.
/// - ensures: slot A holds the frame region's top.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs whose `μ`
///   meets a destructor frame.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_mark(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let slot = environment.wrapping_add(operand!(runtime, A));
    // SAFETY: the lowering assigned slot A inside the window.
    unsafe {
        *slot = Word::from_pointer(frames);
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Select a record's field by label: operand A addresses the selection's
/// table, whose first word counts the head entries after it, each the
/// labelled field's position plus one in the record of that head, or zero
/// when the head has no such field. The field in hand at `hole_alt`; the
/// next instruction, with the record still in hand, when the head names no
/// such field.
///
/// # Specification
/// - requires: the value register addresses an object.
/// - ensures: control reaches `hole_alt` with the labelled field in hand
///   exactly when the object's family names a head entry that carries the
///   label.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs selecting
///   record fields; a wrong position selects the wrong field.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_select_field(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let object = value.to_pointer::<Word>();
    // SAFETY: a positive value in hand addresses an object.
    let header = usize::from(unsafe { *object });
    let entry = header.wrapping_shr(layout::FAMILY_SHIFT).wrapping_sub(1);
    let table = address!(runtime, A).to_pointer::<Word>();
    // SAFETY: the table's first word is its entry count.
    let count = usize::from(unsafe { *table });
    if entry < count {
        // SAFETY: the entry is below the count, so its word lies in the table.
        let position = usize::from(unsafe { *table.wrapping_add(entry.wrapping_add(1)) });
        if position != 0 {
            // SAFETY: a non-zero entry names a field of the head it indexes.
            let field = unsafe { *object.wrapping_add(position) };
            become hole_alt(runtime, heap, frames, environment, field)
        }
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Continue at `hole_alt` unconditionally: a fold's step back to its test.
///
/// # Specification
/// - ensures: control reaches `hole_alt` with the registers unchanged.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs folding
///   native lists; a fold that never steps back answers its first cell alone.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_jump(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    become hole_alt(runtime, heap, frames, environment, value)
}

/// Select a tuple's component A: the component in hand at `hole_alt`; the
/// next instruction, with the value still in hand, when the value is no
/// tuple or holds no component A.
///
/// # Specification
/// - requires: the value register addresses an object.
/// - ensures: control reaches `hole_alt` with component A in hand exactly when
///   the object is a tuple of more than A components.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs
///   projecting tuple components; a wrong offset selects a neighbour.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_select_component(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let object = value.to_pointer::<Word>();
    // SAFETY: a positive value in hand addresses an object.
    let header = usize::from(unsafe { *object });
    let component = operand!(runtime, A);
    let arity = header.wrapping_shr(layout::ARITY_SHIFT) & layout::ARITY_MASK;
    if header & layout::KIND_MASK == layout::KIND_TUPLE && component < arity {
        // SAFETY: the tuple holds more than `component` fields.
        let field = unsafe { *object.wrapping_add(component.wrapping_add(1)) };
        become hole_alt(runtime, heap, frames, environment, field)
    }
    become hole_next(runtime, heap, frames, environment, value)
}

/// Deliver the value in hand to the frame region's top frame: resume it in
/// its window. A loaded selection's block ends here, its continuation's
/// frames below.
///
/// # Specification
/// - requires: a frame — the sentinel at the least — lies below the frame
///   region's top.
/// - ensures: control resumes at the popped frame's code in its window, one
///   unit of fuel spent; or the fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs whose
///   selection meets a loaded continuation.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_pop(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    _environment: *mut Word,
    value: Word,
) -> Word
{
    let frame = frames.wrapping_sub(2);
    // SAFETY: two words below the top are a frame.
    let code = unsafe { *frame };
    // SAFETY: as above.
    let resumed = unsafe { *frame.wrapping_add(1) }.to_pointer::<Word>();
    resume!(code, runtime, heap, frame, resumed, value)
}

/// Call the host: operand A is the call's entry in the run's host table,
/// operand B the count of arguments pushed before it, the first pushed
/// first. The first two pass as the host's operands; every argument lies at
/// the frame region's top the host reads, popped but intact while it runs.
/// The heap's top, the frame region's top and the window cross in the
/// runtime record; the host's answer arrives in hand at the next
/// instruction, or at the code word the host named, or the status the host
/// wrote names the exit.
///
/// # Specification
/// - requires: B arguments lie below the frame region's top; the record's host
///   entry follows [`crate::Host`]'s contract.
/// - ensures: the arguments are popped; the host's answer is in hand, the
///   heap's and the frame region's tops are the host's, and control is at the
///   code word the host named, one unit of fuel spent, or else at the next
///   instruction; or the heap or frame exit is taken when the host wrote that
///   status, the stuck exit when it wrote any other.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs calling
///   primitives, unary and binary, booleans and integers past 64 bits among the
///   answers, and performing operations their handlers answer.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_call(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    value: Word,
) -> Word
{
    let count = operand!(runtime, B);
    let base = frames.wrapping_sub(count);
    let first = if count > 0_usize {
        // SAFETY: the lowering pushed the first argument at the base.
        unsafe { *base }
    }
    else {
        Word::ZERO
    };
    let second = if count > 1_usize {
        // SAFETY: a second argument lies above the first.
        unsafe { *base.wrapping_add(1) }
    }
    else {
        Word::ZERO
    };
    // SAFETY: the runtime record outlives the run.
    unsafe {
        (*runtime).heap_top = heap;
    }
    // SAFETY: as above.
    unsafe {
        (*runtime).frame_top = base;
    }
    // SAFETY: as above.
    unsafe {
        (*runtime).environment = environment;
    }
    // SAFETY: as above.
    let host = unsafe { (*runtime).host };
    let answer = host(runtime, Word::from(operand!(runtime, A)), first, second);
    // SAFETY: as above; the host wrote the heap's and the frame region's new
    // tops, its status and where the run continues.
    let top = unsafe { (*runtime).heap_top };
    // SAFETY: as above.
    let frames = unsafe { (*runtime).frame_top };
    // SAFETY: as above.
    let status = unsafe { (*runtime).status };
    // SAFETY: as above.
    let jump = unsafe { (*runtime).jump };
    if status == layout::STATUS_RUNNING {
        if jump == Word::ZERO {
            become hole_next(runtime, top, frames, environment, answer)
        }
        // SAFETY: as above.
        unsafe {
            (*runtime).jump = Word::ZERO;
        }
        // SAFETY: as above.
        let window = unsafe { (*runtime).jump_window };
        resume!(jump, runtime, top, frames, window, answer);
    }
    if status == layout::STATUS_HEAP_EXHAUSTED {
        become hole_heap_exhausted(runtime, top, frames, environment, value)
    }
    if status == layout::STATUS_FRAMES_EXHAUSTED {
        become hole_frames_exhausted(runtime, top, frames, environment, value)
    }
    // A refusal observed no value: the stuck exit's word is zero.
    become hole_stuck(runtime, top, frames, environment, Word::ZERO)
}

/// Answer the value an aborted access's frame saved: the frame resumes here,
/// the saved answer as its window word, when its unwind delivers its unit,
/// and the answer goes on to the frame below in the unit's place.
///
/// # Specification
/// - requires: a frame — the sentinel at the least — lies below the frame
///   region's top.
/// - ensures: control resumes at that frame's code in its window with the saved
///   answer in hand, one unit of fuel spent; or the fuel exit is taken.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over corpus programs aborting
///   a view; an answer frame passing the unit on answers the unit.
/// - witness: `tests::agreement::the_corpus_runs_items_agree_on_both_executors`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_answer_frame(
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
    _value: Word,
) -> Word
{
    let answer = Word::from_pointer(environment);
    let frame = frames.wrapping_sub(2);
    // SAFETY: two words below the top are a frame.
    let code = unsafe { *frame };
    // SAFETY: as above.
    let resumed = unsafe { *frame.wrapping_add(1) }.to_pointer::<Word>();
    resume!(code, runtime, heap, frame, resumed, answer)
}

/// Generate an exit: record the status and the heap's top, and return the
/// value in hand to the entry.
macro_rules! exit {
    ($name:ident, $status:expr, $summary:literal, $witness:literal) => {
        #[doc = $summary]
        /// # Specification
        /// - ensures: the runtime records the status and the heap's top, and the value
        ///   in hand returns to the entry.
        /// - executable: none — a stencil runs only inside a chain of tail calls whose
        ///   state no predicate can observe.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — each exit's status is asserted by name on a run built to
        ///   take it.
        #[doc = $witness]
        #[unsafe(no_mangle)]
        pub extern "rust-preserve-none" fn $name(
            runtime: *mut Runtime,
            heap: *mut Word,
            _frames: *mut Word,
            _environment: *mut Word,
            value: Word,
        ) -> Word
        {
            // SAFETY: the runtime record outlives the run.
            unsafe { (*runtime).status = $status };
            // SAFETY: as above.
            unsafe { (*runtime).heap_top = heap };
            value
        }
    };
}

exit!(
    stencil_halt,
    layout::STATUS_HALTED,
    "The exit `★` reaches: the run's answer is the value in hand.",
    "- witness: `tests::agreement::the_named_programs_agree_on_both_executors`"
);

/// The exit a case takes when no arm answers the constructor in hand: the
/// case's site, operand A, becomes the record's observed word.
///
/// # Specification
/// - requires: operand A is the site the lowering numbered the case by.
/// - ensures: the runtime records the unmatched status, the site and the heap's
///   top, and the value in hand returns to the entry.
/// - executable: none — a stencil runs only inside a chain of tail calls whose
///   state no predicate can observe.
///
/// # Adequacy
/// - hypothesis: L3 — a case on an injection it has no arm for exits unmatched
///   with the scrutinee in hand and its site observed.
/// - witness: `tests::exits::an_unmatched_case_names_its_site`
#[unsafe(no_mangle)]
pub extern "rust-preserve-none" fn stencil_unmatched(
    runtime: *mut Runtime,
    heap: *mut Word,
    _frames: *mut Word,
    _environment: *mut Word,
    value: Word,
) -> Word
{
    let site = operand!(runtime, A);
    // SAFETY: the runtime record outlives the run.
    unsafe {
        (*runtime).observed = Word(site);
    }
    // SAFETY: as above.
    unsafe {
        (*runtime).status = layout::STATUS_UNMATCHED;
    }
    // SAFETY: as above.
    unsafe {
        (*runtime).heap_top = heap;
    }
    value
}

exit!(
    stencil_heap_exhausted,
    layout::STATUS_HEAP_EXHAUSTED,
    "The exit an allocation takes at the heap region's limit.",
    "- witness: `tests::exits::a_full_heap_exits_by_name`"
);
exit!(
    stencil_frames_exhausted,
    layout::STATUS_FRAMES_EXHAUSTED,
    "The exit a push takes at the frame region's limit.",
    "- witness: `tests::exits::a_full_frame_region_exits_by_name`"
);
exit!(
    stencil_fuel_exhausted,
    layout::STATUS_FUEL_EXHAUSTED,
    "The exit a code-word jump takes when the run's fuel is spent.",
    "- witness: `tests::exits::a_run_without_fuel_exits_by_name`"
);
exit!(
    stencil_stuck,
    layout::STATUS_STUCK,
    "The exit an observation takes on a value it does not observe, that value in hand, and a host call on operands it refuses, zero in hand.",
    "- witness: `tests::exits::an_opaque_observation_exits_stuck`"
);
