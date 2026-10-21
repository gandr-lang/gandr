//! The portable executor: the stencils reached through a dispatch table, and
//! the two entries a Rust caller crosses into a chain of stencils by.
//!
//! An executor program is an array of [`Instruction`]s the emitter builds
//! from the same lowered function it copies and patches: each names its
//! stencil by [`StencilId`], carries its two operands unbiased and the
//! address of its `hole_alt` target. The holes this build defines read and
//! advance the runtime's current instruction, so the stencil bodies are the
//! ones the patcher copies, byte for byte the same source.

use crate::Instruction;
use crate::Runtime;
use crate::Stencil;
use crate::Word;
use crate::transitions;

/// A stencil's symbol in the stencil object, without the platform's prefix.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol(&'static str);

impl AsRef<str> for Symbol
{
    /// The symbol's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// Generate [`StencilId`], its dispatch table and its symbols from one list.
macro_rules! stencils {
    ($( $(#[doc = $doc:literal])* $variant:ident => $function:ident ),* $(,)?) => {
        /// A stencil, by name: the index of the executor's dispatch table and
        /// of the emitter's stencil table, which its build script orders by
        /// [`StencilId::ALL`].
        ///
        /// # Specification
        /// trivial.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum StencilId
        {
            $( $(#[doc = $doc])* $variant, )*
        }

        impl StencilId
        {
            /// Every stencil, in table order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// The stencil's symbol in the stencil object.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            #[must_use]
            pub const fn symbol(self) -> Symbol
            {
                match self {
                    $(Self::$variant => Symbol(stringify!($function)),)*
                }
            }

            /// The dispatch table's entry: the stencil's function.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            const fn handler(self) -> Stencil
            {
                match self {
                    $(Self::$variant => transitions::$function,)*
                }
            }
        }
    };
}

stencils! {
    /// `stencil_const`.
    Const => stencil_const,
    /// `stencil_var`.
    Var => stencil_var,
    /// `stencil_bind`.
    Bind => stencil_bind,
    /// `stencil_const_bind`: `const` then `bind`, fused.
    ConstBind => stencil_const_bind,
    /// `stencil_push`.
    Push => stencil_push,
    /// `stencil_ctor1`.
    Ctor1 => stencil_ctor1,
    /// `stencil_ctor2`.
    Ctor2 => stencil_ctor2,
    /// `stencil_ctor3`.
    Ctor3 => stencil_ctor3,
    /// `stencil_ctor_n`.
    CtorN => stencil_ctor_n,
    /// `stencil_match`.
    Match => stencil_match,
    /// `stencil_field`.
    Field => stencil_field,
    /// `stencil_pushk`.
    Pushk => stencil_pushk,
    /// `stencil_alias`.
    Alias => stencil_alias,
    /// `stencil_alias_top`.
    AliasTop => stencil_alias_top,
    /// `stencil_ret`.
    Ret => stencil_ret,
    /// `stencil_closure`.
    Closure => stencil_closure,
    /// `stencil_enter_apply`.
    EnterApply => stencil_enter_apply,
    /// `stencil_enter_force`.
    EnterForce => stencil_enter_force,
    /// `stencil_enter_fix`.
    EnterFix => stencil_enter_fix,
    /// `stencil_invoke_apply`.
    InvokeApply => stencil_invoke_apply,
    /// `stencil_invoke_force`.
    InvokeForce => stencil_invoke_force,
    /// `stencil_invoke_force_value`: also the force frames' shared stub.
    InvokeForceValue => stencil_invoke_force_value,
    /// `stencil_apply_frame`: the application frames' shared stub.
    ApplyFrame => stencil_apply_frame,
    /// `stencil_argument_frame`: the fold cell frames' shared stub.
    ArgumentFrame => stencil_argument_frame,
    /// `stencil_project`.
    Project => stencil_project,
    /// `stencil_project_frame`: the projection frames' shared stub.
    ProjectFrame => stencil_project_frame,
    /// `stencil_arm`.
    Arm => stencil_arm,
    /// `stencil_unobserved`.
    Unobserved => stencil_unobserved,
    /// `stencil_captured`.
    Captured => stencil_captured,
    /// `stencil_run_capture`.
    RunCapture => stencil_run_capture,
    /// `stencil_global`.
    Global => stencil_global,
    /// `stencil_unfold`.
    Unfold => stencil_unfold,
    /// `stencil_set_global`.
    SetGlobal => stencil_set_global,
    /// `stencil_pushf`.
    Pushf => stencil_pushf,
    /// `stencil_push_apply`.
    PushApply => stencil_push_apply,
    /// `stencil_push_force`.
    PushForce => stencil_push_force,
    /// `stencil_push_project`.
    PushProject => stencil_push_project,
    /// `stencil_push_fields`.
    PushFields => stencil_push_fields,
    /// `stencil_shrink`.
    Shrink => stencil_shrink,
    /// `stencil_shrink_top`.
    ShrinkTop => stencil_shrink_top,
    /// `stencil_match_tag`.
    MatchTag => stencil_match_tag,
    /// `stencil_mark`.
    Mark => stencil_mark,
    /// `stencil_select_field`.
    SelectField => stencil_select_field,
    /// `stencil_select_component`.
    SelectComponent => stencil_select_component,
    /// `stencil_jump`.
    Jump => stencil_jump,
    /// `stencil_pop`: also the reset frames' shared stub.
    Pop => stencil_pop,
    /// `stencil_call`.
    Call => stencil_call,
    /// `stencil_dup`.
    Dup => stencil_dup,
    /// `stencil_drop`.
    Drop => stencil_drop,
    /// `stencil_answer_frame`: the aborted accesses' answer frames' shared
    /// stub.
    AnswerFrame => stencil_answer_frame,
    /// `stencil_halt`: also the sentinel frame's code.
    Halt => stencil_halt,
    /// `stencil_unmatched`.
    Unmatched => stencil_unmatched,
    /// `stencil_heap_exhausted`.
    HeapExhausted => stencil_heap_exhausted,
    /// `stencil_frames_exhausted`.
    FramesExhausted => stencil_frames_exhausted,
    /// `stencil_fuel_exhausted`.
    FuelExhausted => stencil_fuel_exhausted,
    /// `stencil_stuck`.
    Stuck => stencil_stuck,
}

impl Instruction
{
    /// The instruction running `stencil` with operands `a` and `b`, whose
    /// second continuation is `alt`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        stencil: StencilId,
        a: Word,
        b: Word,
        alt: *const Self,
    ) -> Self
    {
        Self {
            handler: stencil.handler(),
            a,
            b,
            alt,
        }
    }
}

/// Enter emitted code at the code word `code`, and return the value in hand
/// when an exit returns.
///
/// # Specification
/// - requires: as `# Safety` states.
/// - ensures: the runtime record holds the exit's status and heap top.
/// - panics: none.
/// - executable: none — the chain the call enters is native code no predicate
///   observes.
///
/// # Safety
/// - unsafe invariants: `code` is the entry of a function the emitter copied
///   and patched into executable memory that stays mapped for the call;
///   `runtime` addresses a live record whose regions are valid for writes up to
///   their limits; `frames` is the record's base mark with the sentinel frame
///   below it; `environment` is a window of at least the function's slot count.
///
/// # Adequacy
/// - hypothesis: L2 — every agreement case enters emitted code here and
///   compares its answer with the executor's and the answer it states.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub unsafe fn enter(
    code: Word,
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
) -> Word
{
    // SAFETY: the caller guarantees `code` is a patched entry, which runs under
    // the stencils' convention.
    let stencil = unsafe { core::mem::transmute::<*const (), Stencil>(code.to_pointer::<()>()) };
    stencil(runtime, heap, frames, environment, Word::ZERO)
}

/// Run the executor program from `first`, and return the value in hand when
/// an exit returns.
///
/// # Specification
/// - requires: as `# Safety` states.
/// - ensures: the runtime record holds the exit's status and heap top.
/// - panics: none.
/// - executable: none — the chain the call enters is a sequence of tail calls
///   no predicate observes.
///
/// # Safety
/// - unsafe invariants: `first` is an element of an instruction array the
///   emitter built, every code word and `alt` of which addresses an element of
///   the same array, live for the call; the register requirements are
///   [`enter`]'s.
///
/// # Adequacy
/// - hypothesis: L2 — every agreement case runs the executor here and compares
///   its answer with the emitted code's and the answer it states.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub unsafe fn execute(
    first: *const Instruction,
    runtime: *mut Runtime,
    heap: *mut Word,
    frames: *mut Word,
    environment: *mut Word,
) -> Word
{
    // SAFETY: the caller guarantees `runtime` addresses a live record.
    unsafe {
        (*runtime).instruction = first;
    }
    // SAFETY: the caller guarantees `first` is an instruction of the program.
    let handler = unsafe { (*first).handler };
    handler(runtime, heap, frames, environment, Word::ZERO)
}
