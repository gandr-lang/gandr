//! The exits: a run that reaches a region's limit, spends its fuel or
//! observes what it cannot returns to its entry with the status that names
//! why, the regions untouched past their limits.
//!
//! Each case is a hand-built executor program over regions sized to put the
//! limit exactly where the case needs it.

use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Host;
use gandr_runtime_stencils::Instruction;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Refusal;
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
    /// What the run observed as it exited.
    observed: Word,
}

/// A region's size in words.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Words(usize);

/// Run `program` from its first instruction over a heap of `heap` words and
/// `frames` frame words above the sentinel, with `fuel`, its calls entering
/// `host`; the sentinel frame resumes at the program's last instruction.
///
/// # Specification
/// trivial.
fn run(
    program: &[Instruction],
    heap: Words,
    frames: Words,
    fuel: Fuel,
    host: Host,
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
    let mut runtime = Runtime::new(start, heap_limit, frame_limit, base, fuel, host, Word::ZERO);
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
        observed: runtime.observed(),
    }
}

/// A host that answers every call with its first operand.
///
/// # Specification
/// trivial.
extern "C" fn answering(
    _runtime: *mut Runtime,
    _entry: Word,
    first: Word,
    _second: Word,
) -> Word
{
    first
}

/// A host that refuses every call for want of heap.
///
/// # Specification
/// trivial.
extern "C" fn exhausted(
    runtime: *mut Runtime,
    _entry: Word,
    _first: Word,
    _second: Word,
) -> Word
{
    // SAFETY: a call stencil passes the run's live record.
    unsafe {
        (*runtime).refuse(Refusal::Heap);
    }
    Word::ZERO
}

/// A host that refuses every call's operands.
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
    // SAFETY: a call stencil passes the run's live record.
    unsafe {
        (*runtime).refuse(Refusal::Operands);
    }
    Word::ZERO
}

/// A host that refuses every call for want of frames.
///
/// # Specification
/// trivial.
extern "C" fn crowded(
    runtime: *mut Runtime,
    _entry: Word,
    _first: Word,
    _second: Word,
) -> Word
{
    // SAFETY: a call stencil passes the run's live record.
    unsafe {
        (*runtime).refuse(Refusal::Frames);
    }
    Word::ZERO
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

/// A one-field tuple needs three heap words, its count, header and field:
/// with two, the constructor exits by the heap's name before it writes, and
/// allocates nothing; with three, the same program halts with the tuple.
#[test]
fn a_full_heap_exits_by_name()
{
    let program = [
        instruction(StencilId::Push, Word::ZERO),
        instruction(StencilId::Ctor1, single()),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let short = run(&program, Words(2), Words(4), Fuel::from(4_usize), refusing);
    assert_eq!(
        Status::HeapExhausted,
        short.status,
        "two words hold no tuple"
    );
    assert_eq!(0, short.allocated, "the exit allocates nothing");
    let room = run(&program, Words(3), Words(4), Fuel::from(4_usize), refusing);
    assert_eq!(Status::Halted, room.status, "three words hold the tuple");
    assert_eq!(3, room.allocated, "the count, the header and its field");
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
    let full = run(&program, Words(1), Words(0), Fuel::from(4_usize), refusing);
    assert_eq!(
        Status::FramesExhausted,
        full.status,
        "no room above the sentinel"
    );
    let room = run(&program, Words(1), Words(1), Fuel::from(4_usize), refusing);
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
    let spent = run(&program, Words(1), Words(1), Fuel::from(0_usize), refusing);
    assert_eq!(Status::FuelExhausted, spent.status, "the return is a jump");
    let one = run(&program, Words(1), Words(1), Fuel::from(1_usize), refusing);
    assert_eq!(Status::Halted, one.status, "one jump reaches the halt");
    assert_eq!(Fuel::from(0_usize), one.fuel, "the jump spent the unit");
    assert_eq!(address, one.answer, "the constant in hand");
}

/// Forcing a value that is no closure — an opaque constant — takes the stuck
/// exit, the observed value in hand, rather than entering a code word the
/// object does not hold.
#[test]
fn an_opaque_observation_exits_stuck()
{
    let opaque = [Header::new(
        Kind::Opaque,
        Tag::try_from(0_usize).expect("tag 0"),
        Arity::try_from(0_usize).expect("arity 0"),
        Family::try_from(3_usize).expect("constant 3"),
    )
    .word()];
    let address = Word::from_pointer((&raw const opaque).cast::<Word>());
    let program = [
        instruction(StencilId::Const, address),
        instruction(StencilId::Bind, Word::ZERO),
        instruction(StencilId::InvokeForce, Word::ZERO),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let stuck = run(&program, Words(1), Words(1), Fuel::from(4_usize), refusing);
    assert_eq!(
        Status::Stuck,
        stuck.status,
        "an opaque constant is no closure"
    );
    assert_eq!(address, stuck.answer, "the observed value in hand");
}

/// A case with no arm for the constructor in hand takes the unmatched exit,
/// the scrutinee in hand and the case's site observed, so the run names the
/// case it stuck at.
#[test]
fn an_unmatched_case_names_its_site()
{
    let injection = [Word::from(0_usize), Word::from(7_i64)];
    let address = Word::from_pointer((&raw const injection).cast::<Word>());
    let site = Word::from(5_usize);
    let program = [
        instruction(StencilId::Const, address),
        instruction(StencilId::Unmatched, site),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let unmatched = run(&program, Words(1), Words(1), Fuel::from(4_usize), refusing);
    assert_eq!(
        (Status::Unmatched, address, site),
        (unmatched.status, unmatched.answer, unmatched.observed),
        "the scrutinee in hand and the case's site observed"
    );
}

/// A host call pops its argument and continues with the host's answer in
/// hand; a host refusing for want of heap takes the heap exit, one refusing
/// for want of frames the frame exit, one refusing its operands the stuck
/// exit with zero in hand, so no operand passes for an observed value.
#[test]
fn a_host_call_answers_or_names_its_exit()
{
    let constant = [Word::from(0_usize), Word::from(7_i64)];
    let address = Word::from_pointer((&raw const constant).cast::<Word>());
    let program = [
        instruction(StencilId::Const, address),
        instruction(StencilId::Push, Word::ZERO),
        Instruction::new(
            StencilId::Call,
            Word::ZERO,
            Word::from(1_usize),
            core::ptr::null(),
        ),
        instruction(StencilId::Halt, Word::ZERO),
    ];
    let answered = run(&program, Words(1), Words(1), Fuel::from(4_usize), answering);
    assert_eq!(Status::Halted, answered.status, "the host answered");
    assert_eq!(address, answered.answer, "the host's answer in hand");
    let heap = run(&program, Words(1), Words(1), Fuel::from(4_usize), exhausted);
    assert_eq!(Status::HeapExhausted, heap.status, "the heap's refusal");
    let stuck = run(&program, Words(1), Words(1), Fuel::from(4_usize), refusing);
    assert_eq!(Status::Stuck, stuck.status, "the operands' refusal");
    assert_eq!(
        Word::ZERO,
        stuck.answer,
        "a refusal observed no value, so nothing in hand is blamed"
    );
    let frames = run(&program, Words(1), Words(1), Fuel::from(4_usize), crowded);
    assert_eq!(
        Status::FramesExhausted,
        frames.status,
        "the frame region's refusal"
    );
}
