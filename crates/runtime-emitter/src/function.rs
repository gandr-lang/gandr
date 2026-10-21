//! A lowered function: the straight list of stencil instructions both tiers
//! run, its labels and its constants.
//!
//! The function is the cache key: two lowerings that produce equal functions
//! run the same code, so a function is compared by value — every instruction,
//! label, constant and the slot count — and hashed the same way.

use gandr_runtime_stencils::COUNT_IMMORTAL;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Word;

/// A label: an index into the function's label table, bound to one
/// instruction.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label(usize);

impl From<Label> for usize
{
    /// The label's index in the label table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(label: Label) -> Self
    {
        label.0
    }
}

/// A word offset into a function's constants.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Constant(usize);

impl From<Constant> for usize
{
    /// The constant's first word's offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: Constant) -> Self
    {
        constant.0
    }
}

/// An immediate operand: a slot, a count, an ordinal or half a header,
/// below 2³² so either patcher materialises it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Immediate(u32);

impl From<u32> for Immediate
{
    /// The immediate `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<Immediate> for usize
{
    /// The immediate's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(immediate: Immediate) -> Self
    {
        // A u32 always fits a 64-bit usize, which the stencil layout asserts.
        Self::try_from(immediate.0).unwrap_or(Self::MAX)
    }
}

/// A frame stub every function shares: the code a frame whose second word
/// is a value, never a window, resumes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Stub
{
    /// `stencil_apply_frame`.
    Apply,
    /// `stencil_invoke_force_value`: a force frame resumes with the thunk in
    /// hand, which is that stencil's input.
    Force,
    /// `stencil_argument_frame`: a fold's cell frame resumes with the folded
    /// tail in hand and the closure answering the cell in its second word.
    Argument,
    /// `stencil_pop`: a reset frame passes the answer in hand on to the frame
    /// below, and a capture to the nearest reset finds it by this code.
    Reset,
    /// `stencil_answer_frame`: an aborted access's answer frame passes the
    /// answer in its second word on, the unwind's unit discarded.
    Answer,
    /// `stencil_project_frame`: a projection's frame resumes with the object
    /// in hand and the component in its second word.
    Project,
}

impl Stub
{
    /// Every stub, in the order both tiers lay them out.
    pub const ALL: [Self; 6] = [
        Self::Apply,
        Self::Force,
        Self::Argument,
        Self::Reset,
        Self::Answer,
        Self::Project,
    ];

    /// The stencil the stub's shared copy runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stencil(self) -> StencilId
    {
        match self {
            Self::Apply => StencilId::ApplyFrame,
            Self::Force => StencilId::InvokeForceValue,
            Self::Argument => StencilId::ArgumentFrame,
            Self::Reset => StencilId::Pop,
            Self::Answer => StencilId::AnswerFrame,
            Self::Project => StencilId::ProjectFrame,
        }
    }

    /// The stub's entry in `table`, which holds one entry per stub in
    /// [`Self::ALL`]'s order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of<Entry>(
        self,
        table: &[Entry; Self::ALL.len()],
    ) -> Entry
    where
        Entry: Copy,
    {
        let [apply, force, argument, reset, answer, project] = *table;
        match self {
            Self::Apply => apply,
            Self::Force => force,
            Self::Argument => argument,
            Self::Reset => reset,
            Self::Answer => answer,
            Self::Project => project,
        }
    }
}

/// What an operand hole receives.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Operand
{
    /// The stencil does not read this operand.
    Unused,
    /// An immediate.
    Immediate(Immediate),
    /// The address of a labelled instruction's code.
    Code(Label),
    /// The address of a constant.
    Data(Constant),
    /// The address of a shared frame stub.
    Stub(Stub),
}

/// One stencil instruction.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Instruction
{
    /// The stencil.
    pub stencil: StencilId,
    /// Operand A.
    pub a: Operand,
    /// Operand B.
    pub b: Operand,
    /// The `hole_alt` target of a two-way stencil.
    pub alt: Alt,
}

/// The second continuation of an instruction.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Alt
{
    /// A one-way stencil: no second continuation.
    None,
    /// The label a two-way stencil continues at on a match.
    At(Label),
}

/// A count of window slots.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Slots(pub usize);

/// A lowered function.
///
/// # Specification
/// - ensures: every label a well-formed function's instructions name is bound,
///   and every instruction whose stencil continues at `hole_next` has a
///   successor; the lowering establishes both.
/// - executable: none — the property is the lowering's postcondition, stated
///   where the lowering's specification checks it.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Function
{
    /// The instructions, in layout order.
    instructions: Vec<Instruction>,
    /// Each label's instruction index; `usize::MAX` while unbound.
    labels: Vec<usize>,
    /// The constants, as words.
    constants: Vec<Word>,
    /// The entry window's slot count.
    slots: Slots,
}

impl Function
{
    /// A fresh label, unbound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn label(&mut self) -> Label
    {
        let label = Label(self.labels.len());
        self.labels.push(usize::MAX);
        label
    }

    /// Bind `label` to the next instruction appended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn bind(
        &mut self,
        label: Label,
    )
    {
        let next = self.instructions.len();
        if let Some(slot) = self.labels.get_mut(label.0) {
            *slot = next;
        }
    }

    /// Append an instruction, answering its index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn push(
        &mut self,
        instruction: Instruction,
    ) -> Position
    {
        let at = Position(self.instructions.len());
        self.instructions.push(instruction);
        at
    }

    /// Rewrite operand A of the instruction at `at`: a closure entry's window
    /// size, known once its body is lowered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn set_a(
        &mut self,
        at: Position,
        a: Operand,
    )
    {
        if let Some(instruction) = self.instructions.get_mut(at.0) {
            instruction.a = a;
        }
    }

    /// Lay out constant words, answering the first one's offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn constant(
        &mut self,
        words: &[Word],
    ) -> Constant
    {
        let at = Constant(self.constants.len());
        self.constants.extend_from_slice(words);
        at
    }

    /// Lay out an object's words, header first, after an immortal count
    /// word, answering the header's offset: a constant no drop frees.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn object(
        &mut self,
        words: &[Word],
    ) -> Constant
    {
        self.constants.push(COUNT_IMMORTAL);
        self.constant(words)
    }

    /// Set the entry window's slot count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn set_slots(
        &mut self,
        slots: Slots,
    )
    {
        self.slots = slots;
    }

    /// The instructions, in layout order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn instructions(&self) -> &[Instruction]
    {
        &self.instructions
    }

    /// The instruction index `label` is bound to, when bound.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Unbound`] for a label never bound or never issued.
    #[inline]
    pub fn target(
        &self,
        label: Label,
    ) -> Result<Position, Unbound>
    {
        match self.labels.get(label.0) {
            Some(&index) if index != usize::MAX => Ok(Position(index)),
            Some(_) | None => Err(Unbound(label)),
        }
    }

    /// Every label issued, in issue order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn labels(&self) -> impl Iterator<Item = Label>
    {
        (0 .. self.labels.len()).map(Label)
    }

    /// The constants, as words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constants(&self) -> &[Word]
    {
        &self.constants
    }

    /// The entry window's slot count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn slots(&self) -> Slots
    {
        self.slots
    }

    /// The positions a label is bound to, ascending, each once: the
    /// instructions a jump, a branch or a resumed frame enters.
    ///
    /// # Specification
    /// - ensures: ascending and without repeats; a position is present exactly
    ///   when some bound label names it.
    /// - panics: none.
    /// - executable: none — the clause would scan the label table again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair whose second instruction a label enters is
    ///   kept apart, and one no label enters is fused.
    /// - witness: `fuse::tests::a_pair_a_label_enters_is_kept_apart`
    #[inline]
    pub(crate) fn entries(&self) -> Vec<Position>
    {
        let mut entries: Vec<Position> = self
            .labels
            .iter()
            .filter(|&&at| at != usize::MAX)
            .map(|&at| Position(at))
            .collect();
        entries.sort_unstable();
        entries.dedup();
        entries
    }

    /// The function with each pair `merges` names run as one instruction:
    /// the pair's first position, ascending, and the instruction that runs
    /// the pair. Each label keeps the instruction it named, so a label bound
    /// past a pair is bound one position lower for each pair before it.
    ///
    /// # Specification
    /// - requires: the positions ascend, each pair lies inside the function, no
    ///   two pairs overlap, and no label is bound to a pair's second
    ///   instruction.
    /// - ensures: one instruction fewer per pair; every other instruction, the
    ///   constants and the slot count kept.
    /// - panics: none.
    /// - executable: none — the clause would compare the rebuilt function with
    ///   the one it was built from, which the fusion's replay already does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a label bound past a fused pair still names the
    ///   instruction it named.
    /// - witness: `fuse::tests::a_label_past_a_fused_pair_names_its_instruction`
    #[inline]
    #[must_use]
    pub(crate) fn merged(
        &self,
        merges: &[(Position, Instruction)],
    ) -> Self
    {
        let mut instructions =
            Vec::with_capacity(self.instructions.len().saturating_sub(merges.len()));
        // Each old position's new one, and one past the end for a label
        // bound after the last instruction.
        let mut moved = Vec::with_capacity(self.instructions.len().saturating_add(1));
        let mut pending = merges.iter().peekable();
        let mut index = 0_usize;
        while let Some(&instruction) = self.instructions.get(index) {
            let at = instructions.len();
            moved.push(at);
            match pending.peek() {
                Some(&&(Position(first), fused)) if first == index => {
                    let _merged = pending.next();
                    instructions.push(fused);
                    moved.push(at);
                    index = index.saturating_add(2);
                },
                Some(_) | None => {
                    instructions.push(instruction);
                    index = index.saturating_add(1);
                },
            }
        }
        moved.push(instructions.len());
        let labels = self
            .labels
            .iter()
            .map(|&at| moved.get(at).copied().unwrap_or(at))
            .collect();
        Self {
            instructions,
            labels,
            constants: self.constants.clone(),
            slots: self.slots,
        }
    }
}

/// An instruction's index in its function.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Position(pub usize);

/// A label no instruction is bound to.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Unbound(pub Label);
