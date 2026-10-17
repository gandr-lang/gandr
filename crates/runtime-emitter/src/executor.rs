//! The portable executor's programs: a lowered function laid out as an
//! array of stencil instructions the stencil crate's dispatch runs.
//!
//! The program is the function's instructions in order, then the shared
//! frame stubs and the halt the sentinel frame resumes. A code word is an
//! instruction's address and a constant's address points into the program's
//! own constant words, so a frame, a closure and a constant mean the same in
//! both tiers: only what a code word addresses differs.

use gandr_runtime_stencils::Instruction as Step;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Word;

use crate::function::Alt;
use crate::function::Function;
use crate::function::Label;
use crate::function::Operand;
use crate::function::Stub;
use crate::function::Unbound;

/// An executor program built from one lowered function.
///
/// # Specification
/// - ensures: every code word, constant address and `alt` the steps hold
///   addresses an element of `steps` or of `constants`, which never move after
///   the build.
/// - executable: none — the addresses are pointers no predicate dereferences.
#[derive(Debug)]
pub struct Program
{
    /// The steps: the function's instructions, then each of [`Stub::ALL`]
    /// and the halt.
    steps: Box<[Step]>,
    /// The function's constants, owned here so the steps' constant addresses
    /// stay valid; no step reads the box itself.
    #[expect(
        dead_code,
        reason = "held for its allocation, which the steps address by pointer"
    )]
    constants: Box<[Word]>,
    /// The instruction count of the function, where the stubs begin.
    stubs: usize,
    /// Each of [`Stub::ALL`]'s step, as a code word.
    codes: [Word; Stub::ALL.len()],
}

/// The stubs after a function's instructions, in order: each of
/// [`Stub::ALL`], then the halt.
const STUBS: [StencilId; Stub::ALL.len().wrapping_add(1)] = [
    Stub::Apply.stencil(),
    Stub::Force.stencil(),
    Stub::Argument.stencil(),
    Stub::Reset.stencil(),
    Stub::Answer.stencil(),
    Stub::ProjectLeft.stencil(),
    Stub::ProjectRight.stencil(),
    StencilId::Halt,
];

/// The position of the halt among [`STUBS`].
const HALT: usize = Stub::ALL.len();

impl Program
{
    /// The program running `function`.
    ///
    /// # Specification
    /// - ensures: the first step runs the function's first instruction, each
    ///   step continuing at the next or at its label's step, as the emitted
    ///   copy of the same function continues.
    /// - executable: none — continuing as the emitted copy does is observed
    ///   only by running both.
    ///
    /// # Errors
    /// [`Unbound`] for a label an instruction names and the lowering never
    /// bound.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every agreement case runs the program this builds
    ///   beside the emitted code of the same function and the answer it states.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    #[inline]
    pub fn build(function: &Function) -> Result<Self, Unbound>
    {
        let instructions = function.instructions();
        let stubs = instructions.len();
        let constants: Box<[Word]> = function.constants().into();
        let placeholder = Step::new(StencilId::Halt, Word::ZERO, Word::ZERO, core::ptr::null());
        let mut steps: Box<[Step]> =
            core::iter::repeat_n(placeholder, stubs.saturating_add(STUBS.len())).collect();
        let base = (&raw const *steps).cast::<Step>();
        let at = |index: usize| -> Word { Word::from_pointer(base.wrapping_add(index)) };
        let codes: [Word; Stub::ALL.len()] =
            core::array::from_fn(|index| at(stubs.saturating_add(index)));
        let label = |label: Label| -> Result<Word, Unbound> {
            function.target(label).map(|position| at(position.0))
        };
        let constant_base = (&raw const *constants).cast::<Word>();
        let operand = |operand: Operand| -> Result<Word, Unbound> {
            Ok(match operand {
                Operand::Unused => Word::ZERO,
                Operand::Immediate(immediate) => Word::from(usize::from(immediate)),
                Operand::Code(code) => label(code)?,
                Operand::Data(offset) => {
                    Word::from_pointer(constant_base.wrapping_add(usize::from(offset)))
                },
                Operand::Stub(stub) => stub.of(&codes),
            })
        };
        let (body, tail) = steps.split_at_mut(stubs);
        for (step, instruction) in body.iter_mut().zip(instructions) {
            let alt = match instruction.alt {
                Alt::None => core::ptr::null(),
                Alt::At(target) => label(target)?.to_pointer::<Step>().cast_const(),
            };
            *step = Step::new(
                instruction.stencil,
                operand(instruction.a)?,
                operand(instruction.b)?,
                alt,
            );
        }
        for (step, stub) in tail.iter_mut().zip(STUBS) {
            *step = Step::new(stub, Word::ZERO, Word::ZERO, core::ptr::null());
        }
        Ok(Self {
            steps,
            constants,
            stubs,
            codes,
        })
    }

    /// The first step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entry(&self) -> *const Step
    {
        self.steps.as_ptr()
    }

    /// The code word of the halt the sentinel frame resumes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn halt(&self) -> Word
    {
        Word::from_pointer(
            self.steps
                .as_ptr()
                .wrapping_add(self.stubs.saturating_add(HALT)),
        )
    }

    /// The code word a label of the function addresses: a closure entry's,
    /// which a closure in the answer carries, or a frame's or a clause's,
    /// which a control operation finds or enters.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Unbound`] as [`Self::build`].
    #[inline]
    pub fn code(
        &self,
        function: &Function,
        label: Label,
    ) -> Result<Word, Unbound>
    {
        function
            .target(label)
            .map(|position| Word::from_pointer(self.steps.as_ptr().wrapping_add(position.0)))
    }

    /// The code word of a stub's shared step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stub(
        &self,
        stub: Stub,
    ) -> Word
    {
        stub.of(&self.codes)
    }
}
