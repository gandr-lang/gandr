//! The exits: a run that reaches a region's limit or spends its fuel returns
//! to its entry with the status that names why, the regions untouched past
//! their limits.
//!
//! Each case is a hand-built executor program over regions sized to put the
//! limit exactly where the case needs it.

use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Instruction;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Tag;
use gandr_runtime_stencils::Word;
use gandr_runtime_stencils::execute;

/// The instruction running `stencil` with operand A, falling through.
///
/// # Specification
/// trivial.
fn instruction(
    stencil: StencilId,
    a: Word,
) -> Instruction
{
    Instruction::new(stencil, a, Word::ZERO, core::ptr::null())
}

/// What a run left: its status, the heap words it allocated and its fuel.
struct Exit
{
    /// Why it returned.
    status: Status,
    /// The words between the heap's start and the heap pointer it exited
    /// with.
    allocated: usize,
    /// The jumps it did not take.
    fuel: Fuel,
    /// The value in hand.
    answer: Word,
}

/// A region's size in words.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Words(usize);

/// Run `program` from its first instruction over a heap of `heap` words and
/// `frames` frame words above the sentinel, with `fuel`; the sentinel frame
/// resumes at the program's last instruction.
///
/// # Specification
/// trivial.
fn run(
    program: &[Instruction],
    heap: Words,
    frames: Words,
    fuel: Fuel,
) -> Exit
{
    let mut heap = vec![Word::ZERO; heap.0];
    let mut frames = vec![Word::ZERO; frames.0.saturating_add(2)];
    let mut window = [Word::ZERO; 1];
    let halt = program.last().expect("a program ends in its halt");
    frames[0] = Word::from_pointer(core::ptr::from_ref(halt));
    let start = heap.as_mut_ptr();
    let heap_limit = start.wrapping_add(heap.len());
    let base = frames.as_mut_ptr().wrapping_add(2);
    let frame_limit = frames.as_mut_ptr().wrapping_add(frames.len());
    let mut runtime = Runtime::new(start, heap_limit, frame_limit, base, fuel);
    // SAFETY: the program's every instruction falls through to the next or
    // exits, and its only code word is its last instruction's address; the
    // regions live to the end of the call, the sentinel frame below the base
    // mark, and the window holds the one slot the program names.
    let answer = unsafe {
        execute(
            program.as_ptr(),
            &raw mut runtime,
            start,
            base,
            (&raw mut window).cast::<Word>(),
        )
    };
    Exit {
        status: runtime.status().expect("an exit writes a known status"),
        allocated: runtime
            .heap_top()
            .addr()
            .saturating_sub(start.addr())
            .checked_div(size_of::<Word>())
            .unwrap_or(0),
        fuel: runtime.fuel(),
        answer,
    }
}

/// The header of a one-field tuple.
///
/// # Specification
/// trivial.
fn single() -> Word
{
    let header = Header::new(
        Kind::Tuple,
        Tag::try_from(0_usize).expect("tag 0"),
        Arity::try_from(1_usize).expect("arity 1"),
        Family::UNNAMED,
    );
    header.matched()
}

/// A one-field tuple needs two heap words: with one, the constructor exits
/// by the heap's name before it writes, and allocates nothing; with two, the
/// same program halts with the tuple.
#[test]
fn a_full_heap_exits_by_name()
{
    let program = [
        instruction(StencilId::Push, Word::ZERO),
        instruction(StencilId::Ctor1, single()),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let short = run(&program, Words(1), Words(4), Fuel::from(4_usize));
    assert_eq!(
        Status::HeapExhausted,
        short.status,
        "one word holds no tuple"
    );
    assert_eq!(0, short.allocated, "the exit allocates nothing");
    let room = run(&program, Words(2), Words(4), Fuel::from(4_usize));
    assert_eq!(Status::Halted, room.status, "two words hold the tuple");
    assert_eq!(2, room.allocated, "the header and its field");
}

/// A push at the frame region's limit exits by the frames' name; one word of
/// room lets it through.
#[test]
fn a_full_frame_region_exits_by_name()
{
    let program = [
        instruction(StencilId::Push, Word::ZERO),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let full = run(&program, Words(1), Words(0), Fuel::from(4_usize));
    assert_eq!(
        Status::FramesExhausted,
        full.status,
        "no room above the sentinel"
    );
    let room = run(&program, Words(1), Words(1), Fuel::from(4_usize));
    assert_eq!(Status::Halted, room.status, "one word of room");
}

/// A return to the sentinel frame is a jump: with no fuel it exits by the
/// fuel's name, with one unit it halts with the value it returned and none
/// left.
#[test]
fn a_run_without_fuel_exits_by_name()
{
    let constant = [Word::from(0_usize), Word::from(42_i64)];
    let address = Word::from_pointer((&raw const constant).cast::<Word>());
    let program = [
        instruction(StencilId::AliasTop, Word::ZERO),
        instruction(StencilId::Const, address),
        instruction(StencilId::Ret, Word::ZERO),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let spent = run(&program, Words(1), Words(1), Fuel::from(0_usize));
    assert_eq!(Status::FuelExhausted, spent.status, "the return is a jump");
    let one = run(&program, Words(1), Words(1), Fuel::from(1_usize));
    assert_eq!(Status::Halted, one.status, "one jump reaches the halt");
    assert_eq!(Fuel::from(0_usize), one.fuel, "the jump spent the unit");
    assert_eq!(address, one.answer, "the constant in hand");
}
