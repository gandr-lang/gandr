//! The block entry: a hand-built executor program pushes two machine
//! integers and enters a block of machine code, which the emitter's block
//! compiler gave and the emitter's table of blocks mapped. The program reads
//! the answer's object, the heap's top and the words that the block left.

use gandr_runtime_emitter::block::Answer;
use gandr_runtime_emitter::block::Assembler;
use gandr_runtime_emitter::block::Blocks;
use gandr_runtime_emitter::block::Cache;
use gandr_runtime_emitter::block::Class;
use gandr_runtime_emitter::block::Description;
use gandr_runtime_emitter::block::Direction;
use gandr_runtime_emitter::block::Operand;
use gandr_runtime_emitter::block::Options;
use gandr_runtime_emitter::block::Place;
use gandr_runtime_emitter::block::Target;
use gandr_runtime_emitter::machine;
use gandr_runtime_stencils::BLOCK_ANSWERS;
use gandr_runtime_stencils::COUNT_IMMORTAL;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::INTEGER_HEADER;
use gandr_runtime_stencils::Instruction;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Word;
use gandr_runtime_stencils::Words;
use gandr_runtime_stencils::execute;

/// The target of this host's blocks.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const HOST: Target = Target::LinuxX86_64;
/// The target of this host's blocks.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const HOST: Target = Target::LinuxAarch64;
/// The target of this host's blocks.
#[cfg(all(target_os = "linux", target_arch = "riscv64"))]
const HOST: Target = Target::LinuxRiscv64;
/// The target of this host's blocks.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const HOST: Target = Target::DarwinAarch64;

/// The block that adds its second word into its first and answers the sum.
///
/// # Specification
/// trivial.
fn adding() -> Description
{
    let general = Place::Class(Class::General);
    let word = |direction| Operand {
        direction,
        place: general.clone(),
    };
    let template = match HOST {
        Target::LinuxX86_64 => "add {0}, {1}\nmov {answer}, {0}",
        Target::LinuxAarch64 | Target::DarwinAarch64 => "add {0}, {0}, {1}\nmov {answer}, {0}",
        Target::LinuxRiscv64 => "add {0}, {0}, {1}\nmv {answer}, {0}",
    };
    Description {
        target: HOST,
        template: template.into(),
        operands: Box::new([word(Direction::InOut), word(Direction::In)]),
        answer: Answer::Place(general.clone()),
        clobbers: Box::new([]),
        options: Options::DEFAULT,
    }
}

/// The address of `description`'s block in this process.
///
/// # Specification
/// trivial.
fn mapped(description: &Description) -> Word
{
    let block = Blocks::new(Assembler::pinned(), Cache::Process)
        .compile(description)
        .expect("the block compiles");
    machine::address(block.key).expect("the block maps")
}

/// What a run left: its status, the heap words it allocated, the value in
/// hand, the object in hand when the heap holds it, and the two words above
/// the sentinel frame.
#[derive(Debug, Eq, PartialEq)]
struct Exit
{
    /// Why it returned.
    status: Status,
    /// The words between the heap's start and the heap pointer it exited
    /// with.
    allocated: usize,
    /// The value in hand.
    answer: Word,
    /// The header and the field of the object in hand, when the heap holds it.
    object: Option<[Word; 2]>,
    /// The two frame words above the sentinel: the pushed integers, then the
    /// block's words.
    words: [Word; 2],
}

/// Push the machine integers `first` and `second`, enter the block at
/// `block` with operand B `operands`, and halt, over a heap of `heap` words.
///
/// # Specification
/// trivial.
fn run(
    block: Word,
    operands: Word,
    (first, second): (&[Word; 3], &[Word; 3]),
    heap: Words,
) -> Exit
{
    let header = |integer: &[Word; 3]| Word::from_pointer(&raw const integer[1]);
    let step = |stencil, a, b| Instruction::new(stencil, a, b, core::ptr::null());
    let program = [
        step(StencilId::Const, header(first), Word::ZERO),
        step(StencilId::Push, Word::ZERO, Word::ZERO),
        step(StencilId::Const, header(second), Word::ZERO),
        step(StencilId::Push, Word::ZERO, Word::ZERO),
        step(StencilId::Block, block, operands),
        step(StencilId::Halt, Word::ZERO, Word::ZERO),
    ];
    let mut memory: Vec<Word> = vec![Word::ZERO; heap.0];
    let mut frames = [Word::ZERO; 4];
    let mut window = [Word::ZERO; 1];
    frames[0] = Word::from_pointer(&raw const program[5]);
    let start = memory.as_mut_ptr();
    let bottom = (&raw mut frames).cast::<Word>();
    let base = bottom.wrapping_add(2);
    let limit = bottom.wrapping_add(frames.len());
    let mut runtime = Runtime::new(
        start,
        start.wrapping_add(memory.len()),
        limit,
        base,
        Fuel::from(1_usize),
        refusing,
        Word::ZERO,
    );
    runtime.set_memory(heap);
    // SAFETY: each instruction falls through to the next, the block is
    // mapped for the process, and the regions live to the end of the call
    // with the sentinel frame below the base mark.
    let answer = unsafe {
        execute(
            (&raw const program).cast::<Instruction>(),
            &raw mut runtime,
            start,
            base,
            (&raw mut window).cast::<Word>(),
        )
    };
    let allocated = runtime
        .heap_top()
        .addr()
        .saturating_sub(start.addr())
        .checked_div(size_of::<Word>())
        .unwrap_or(0);
    let object = memory
        .iter()
        .position(|word| Word::from_pointer(core::ptr::from_ref(word)) == answer)
        .and_then(|at| Some([*memory.get(at)?, *memory.get(at.checked_add(1)?)?]));
    Exit {
        status: runtime.status().expect("an exit writes a known status"),
        allocated,
        answer,
        object,
        words: [frames[2], frames[3]],
    }
}

/// A host that refuses each call: no block entry calls the host.
///
/// # Specification
/// trivial.
extern "C" fn refusing(
    runtime: *mut Runtime,
    _entry: Word,
    _first: Word,
    _second: Word,
) -> Word
{
    // SAFETY: the runtime record is live for the call.
    unsafe {
        (*runtime).refuse(gandr_runtime_stencils::Refusal::Operands);
    }
    Word::ZERO
}

/// The machine integer `bits`, after its immortal count.
///
/// # Specification
/// trivial.
fn integer(bits: Word) -> [Word; 3]
{
    [COUNT_IMMORTAL, INTEGER_HEADER, bits]
}

/// A block that adds its two words answers their sum as one fresh machine
/// integer of three heap words: its count, its header and its field. The
/// block wrote the sum into its first word, so it read the fields and not
/// the objects. A heap of two words holds no answer: the run exits by the
/// heap's name, and the first word keeps the field, so the block never ran.
#[test]
fn a_block_answers_the_sum_of_its_words()
{
    let block = mapped(&adding());
    let (forty, two) = (integer(Word::from(40_i64)), integer(Word::from(2_i64)));
    let operands = Word::from(2 | BLOCK_ANSWERS);
    let exit = run(block, operands, (&forty, &two), Words(3));
    assert_eq!(Status::Halted, exit.status);
    assert_eq!(3, exit.allocated, "the count, the header and the field");
    assert_eq!(Some([INTEGER_HEADER, Word::from(42_i64)]), exit.object);
    assert_eq!([Word::from(42_i64), Word::from(2_i64)], exit.words);
    let full = run(block, operands, (&forty, &two), Words(2));
    assert_eq!(Status::HeapExhausted, full.status);
    assert_eq!(0, full.allocated);
    assert_eq!([Word::from(40_i64), Word::from(2_i64)], full.words);
}

/// A block that answers nothing allocates nothing and leaves the last
/// integer pushed in hand, though the block ran and wrote its first word.
#[test]
fn a_block_that_answers_nothing_allocates_nothing()
{
    let block = mapped(&adding());
    let (forty, two) = (integer(Word::from(40_i64)), integer(Word::from(2_i64)));
    let exit = run(block, Word::from(2_usize), (&forty, &two), Words(3));
    assert_eq!(
        Exit {
            status: Status::Halted,
            allocated: 0,
            answer: Word::from_pointer(&raw const two[1]),
            object: None,
            words: [Word::from(42_i64), Word::from(2_i64)],
        },
        exit
    );
}
