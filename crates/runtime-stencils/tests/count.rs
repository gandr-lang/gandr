//! The count: hand-built executor programs that duplicate and drop objects
//! by the `dup` and `drop` stencils, under a host whose release reads a
//! tuple's fields as what it owns, and the heap they leave read word by word.

use gandr_runtime_emitter::release;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::COUNT_IMMORTAL;
use gandr_runtime_stencils::COUNT_ONE;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Instruction;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::RELEASE;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Tag;
use gandr_runtime_stencils::Word;
use gandr_runtime_stencils::Words;
use gandr_runtime_stencils::count_word;
use gandr_runtime_stencils::execute;

/// The heap words every program here runs over.
const HEAP: usize = 32;

/// The instruction running `stencil` with operands `a` and `b`, falling
/// through.
///
/// # Specification
/// trivial.
fn instruction(
    stencil: StencilId,
    a: Word,
    b: Word,
) -> Instruction
{
    Instruction::new(stencil, a, b, core::ptr::null())
}

/// A tuple constructor's instruction over `fields` pushed fields.
///
/// # Specification
/// trivial.
fn tuple(fields: Words) -> Instruction
{
    let header = Header::new(
        Kind::Tuple,
        Tag::try_from(0_usize).expect("a zero tag fits"),
        Arity::try_from(fields.0).expect("the arity fits"),
        Family::UNNAMED,
    );
    instruction(StencilId::CtorN, header.matched(), Word::ZERO)
}

/// The stencil `stencil` over the value in hand.
///
/// # Specification
/// trivial.
fn bare(stencil: StencilId) -> Instruction
{
    instruction(stencil, Word::ZERO, Word::ZERO)
}

/// The stencil `stencil` over window slot `slot`.
///
/// # Specification
/// trivial.
fn slotted(
    stencil: StencilId,
    slot: Words,
) -> Instruction
{
    instruction(stencil, Word::from(slot.0), Word::ZERO)
}

/// The fields of the tuple `object`: what a tuple owns.
///
/// # Specification
/// trivial.
fn fields(object: Word) -> Vec<Word>
{
    let header = object.to_pointer::<Word>();
    // SAFETY: the programs here hand the host tuples of their heap.
    let arity = usize::from(Header::from_word(unsafe { *header }).arity());
    // SAFETY: as above; a tuple's fields follow its header.
    (1 ..= arity)
        .map(|at| unsafe { *header.wrapping_add(at) })
        .collect()
}

/// A host answering only a drop's release, over a tuple's fields.
///
/// # Specification
/// trivial.
extern "C" fn releasing(
    runtime: *mut Runtime,
    entry: Word,
    first: Word,
    _second: Word,
) -> Word
{
    if entry == RELEASE {
        // SAFETY: the drop stencil passes the run's live record and an
        // object of its heap at its last owner, whose fields are tuples.
        let record = unsafe { &mut *runtime };
        // SAFETY: as above.
        unsafe {
            release(record, first, fields);
        }
    }
    Word::ZERO
}

/// What a run left: its answer, the heap it ran over and the words it
/// allocated past the heap's start.
struct Ran
{
    /// The value in hand at the halt.
    answer: Word,
    /// The heap.
    heap: Vec<Word>,
    /// The words between the heap's start and its top.
    allocated: usize,
}

impl Ran
{
    /// The address of the heap word `at`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        &self,
        at: Words,
    ) -> Word
    {
        Word::from_pointer(self.heap.as_ptr().wrapping_add(at.0))
    }
}

/// Run `program` to its halt over a fresh heap.
///
/// # Specification
/// trivial.
fn run(program: &[Instruction]) -> Ran
{
    let mut heap = vec![Word::ZERO; HEAP];
    let mut frames = vec![Word::ZERO; 18];
    let mut window = [Word::ZERO; 4];
    let halt = program.last().expect("a program ends in its halt");
    frames[0] = Word::from_pointer(core::ptr::from_ref(halt));
    let start = heap.as_mut_ptr();
    let base = frames.as_mut_ptr().wrapping_add(2);
    let frame_limit = frames.as_mut_ptr().wrapping_add(frames.len());
    let mut runtime = Runtime::new(
        start,
        start.wrapping_add(HEAP),
        frame_limit,
        base,
        Fuel::from(16_usize),
        releasing,
        Word::ZERO,
    );
    // SAFETY: the program falls through to its halt; the regions live to the
    // end of the call, the sentinel frame below the base mark.
    let answer = unsafe {
        execute(
            program.as_ptr(),
            &raw mut runtime,
            start,
            base,
            (&raw mut window).cast::<Word>(),
        )
    };
    assert_eq!(Ok(Status::Halted), runtime.status(), "the program halts");
    let allocated = runtime
        .heap_top()
        .addr()
        .saturating_sub(start.addr())
        .checked_div(size_of::<Word>())
        .unwrap_or(0);
    Ran {
        answer,
        heap,
        allocated,
    }
}

/// A tuple dropped at its last owner gives its block back, and the next tuple
/// of its size takes it: the same address, the heap's top unmoved.
#[test]
fn a_freed_block_is_the_next_of_its_size()
{
    let ran = run(&[
        tuple(Words(0)),
        slotted(StencilId::Bind, Words(0)),
        slotted(StencilId::Drop, Words(0)),
        tuple(Words(0)),
        bare(StencilId::Halt),
    ]);
    assert_eq!(
        ran.at(Words(1)),
        ran.answer,
        "the second tuple is the first's block"
    );
    assert_eq!(
        2, ran.allocated,
        "one block's words: the count and the header"
    );
    assert_eq!(COUNT_ONE, ran.heap[0], "the reused block counts one owner");
}

/// A tuple duplicated once survives a drop, counted one owner again, and the
/// next tuple is allocated past it.
#[test]
fn a_dup_keeps_an_object_through_one_drop()
{
    let ran = run(&[
        tuple(Words(0)),
        slotted(StencilId::Bind, Words(0)),
        slotted(StencilId::Dup, Words(0)),
        slotted(StencilId::Drop, Words(0)),
        tuple(Words(0)),
        bare(StencilId::Halt),
    ]);
    assert_eq!(
        ran.at(Words(3)),
        ran.answer,
        "the second tuple is a fresh block"
    );
    assert_eq!(4, ran.allocated, "two blocks");
    assert_eq!(
        COUNT_ONE, ran.heap[0],
        "the first tuple keeps its one owner"
    );
}

/// A constant laid out with an immortal count is neither counted nor freed,
/// however often it is dropped.
#[test]
fn an_immortal_constant_is_never_freed()
{
    let header = Header::new(
        Kind::Tuple,
        Tag::try_from(0_usize).expect("a zero tag fits"),
        Arity::try_from(0_usize).expect("the arity fits"),
        Family::UNNAMED,
    );
    let constant = [COUNT_IMMORTAL, header.word()];
    let object = Word::from_pointer((&raw const constant).cast::<Word>().wrapping_add(1));
    let ran = run(&[
        instruction(StencilId::Const, object, Word::ZERO),
        slotted(StencilId::Bind, Words(0)),
        slotted(StencilId::Dup, Words(0)),
        slotted(StencilId::Drop, Words(0)),
        slotted(StencilId::Drop, Words(0)),
        tuple(Words(0)),
        bare(StencilId::Halt),
    ]);
    // SAFETY: the constant outlives the run.
    assert_eq!(COUNT_IMMORTAL, unsafe { *count_word(object) });
    assert_eq!(
        ran.at(Words(1)),
        ran.answer,
        "the tuple takes the heap's first block"
    );
}

/// A pair dropped at its last owner frees itself and the field whose last
/// owner it held, and leaves the field another owner holds counted one
/// less: the next tuple of the freed field's size takes its block.
#[test]
fn a_released_object_drops_what_it_holds()
{
    let ran = run(&[
        tuple(Words(0)),
        slotted(StencilId::Bind, Words(0)),
        bare(StencilId::Push),
        tuple(Words(0)),
        slotted(StencilId::Bind, Words(1)),
        slotted(StencilId::Dup, Words(1)),
        bare(StencilId::Push),
        tuple(Words(2)),
        slotted(StencilId::Bind, Words(2)),
        slotted(StencilId::Drop, Words(2)),
        tuple(Words(0)),
        bare(StencilId::Halt),
    ]);
    assert_eq!(8, ran.allocated, "two empty tuples and the pair");
    assert_eq!(COUNT_ONE, ran.heap[2], "the shared field keeps one owner");
    assert_eq!(
        ran.at(Words(1)),
        ran.answer,
        "the field freed with the pair is the next block taken"
    );
}
