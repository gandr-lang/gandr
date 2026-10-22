//! What every refusal and stop says. The dispatcher and the runtime show
//! these messages as they stand, so each must keep its reasons apart, name
//! the address it blames, read a declared count before a found one, and
//! carry the message of the refusal it wraps.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt::Display;

use gandr_core_sequent::ArityHead;
use gandr_core_sequent::CheckRefusal;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConsumerArity;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::FocusRefusal;
use gandr_core_sequent::HeapFamily;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::MintRefusal;
use gandr_core_sequent::MotiveHead;
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::NodeFamily;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ReadbackRefusal;
use gandr_core_sequent::ReifyRefusal;
use gandr_core_sequent::StoreFault;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::UnfocusRefusal;
use gandr_core_term::CoreArena;
use gandr_core_term::primitive::PrimitiveError;
use gandr_kernel_term::ConstantIndex;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::Sym;

/// What one reason says: its message and the numbers it spells, in order.
#[derive(Debug)]
struct Reading
{
    /// The message.
    message: String,
    /// The runs of digits in the message.
    numbers: Vec<u64>,
}

/// The readings of `reasons`, their messages asserted pairwise distinct.
///
/// # Specification
/// trivial.
fn read<T>(reasons: &[T]) -> Vec<Reading>
where
    T: Display,
{
    let readings: Vec<Reading> = reasons
        .iter()
        .map(|reason| {
            let message = reason.to_string();
            let numbers = message
                .split(|character: char| !character.is_ascii_digit())
                .filter(|word| !word.is_empty())
                .map(|word| word.parse().expect("a run of digits"))
                .collect();
            Reading { message, numbers }
        })
        .collect();
    let unique: BTreeSet<&String> = readings.iter().map(|reading| &reading.message).collect();
    assert_eq!(
        readings.len(),
        unique.len(),
        "two reasons read alike: {readings:#?}"
    );
    readings
}

/// Each arena refusal names the child it blames or the family that is full,
/// and an address names its family beside its number.
#[test]
fn mint_refusals_and_addresses_name_what_they_blame()
{
    let mut core = CoreArena::new();
    let annotation = core.value_type_unit();
    let messages = read(&[
        MintRefusal::DanglingProducer(ProducerId::from(11_u32)),
        MintRefusal::DanglingConsumer(ConsumerId::from(12_u32)),
        MintRefusal::DanglingCommand(CommandId::from(13_u32)),
        MintRefusal::DanglingAnnotation(annotation),
        MintRefusal::FamilyFull(NodeFamily::Producer),
        MintRefusal::FamilyFull(NodeFamily::Consumer),
        MintRefusal::FamilyFull(NodeFamily::Command),
    ]);
    let blamed: Vec<&[u64]> = messages
        .iter()
        .take(3)
        .map(|reading| reading.numbers.as_slice())
        .collect();
    assert_eq!(blamed, [&[11][..], &[12], &[13]]);
    let addresses = read(&[
        NodeAddress::Producer(ProducerId::from(4_u32)),
        NodeAddress::Consumer(ConsumerId::from(4_u32)),
        NodeAddress::Command(CommandId::from(4_u32)),
    ]);
    assert!(addresses.iter().all(|reading| reading.numbers == [4]));
}

/// Each well-formedness refusal reads apart from the others, names its
/// address, carries the node an annotation dangles from, and reads a
/// declared arity before the found one.
#[test]
fn check_refusals_name_the_node_and_the_counts_in_order()
{
    let node = NodeAddress::Consumer(ConsumerId::from(24_u32));
    let head = ArityHead::Destructor(DestructorTag::Apply);
    let messages = read(&[
        CheckRefusal::DanglingCommand(CommandId::from(21_u32)),
        CheckRefusal::DanglingProducer(ProducerId::from(22_u32)),
        CheckRefusal::DanglingConsumer(ConsumerId::from(23_u32)),
        CheckRefusal::DanglingAnnotation(node),
        CheckRefusal::NonValueArgument(ProducerId::from(25_u32)),
        CheckRefusal::PolarityMismatch {
            command: CommandId::from(26_u32),
            cut: Polarity::Positive,
            observed: Polarity::Negative,
        },
        CheckRefusal::ProducerArity {
            head: head.clone(),
            expected: ProducerArity::ONE,
            found: ProducerArity::TWO,
        },
        CheckRefusal::ConsumerArity {
            head: head.clone(),
            expected: ConsumerArity::ONE,
            found: ConsumerArity::from(3_usize),
        },
        CheckRefusal::DuplicateArm(head),
    ]);
    let blamed: Vec<&[u64]> = messages
        .iter()
        .map(|reading| reading.numbers.as_slice())
        .collect();
    assert_eq!(blamed, [
        &[21][..],
        &[22],
        &[23],
        &[24],
        &[25],
        &[26],
        &[1, 2],
        &[1, 3],
        &[],
    ]);
    assert!(messages[3].message.contains(&node.to_string()));
}

/// A pattern refusal names the metavariable, the constructor or the
/// operation, reads the declared arity first, and carries the arena's
/// refusal.
#[test]
fn reify_refusals_name_the_pattern_node_and_carry_the_arena()
{
    let mint = MintRefusal::DanglingCommand(CommandId::from(41_u32));
    let messages = read(&[
        ReifyRefusal::Metavariable(MetaVar::producer("hole")),
        ReifyRefusal::UnresolvedConstructor(Sym::new("Zero")),
        ReifyRefusal::ArityMismatch {
            constructor: Sym::new("Pair"),
            expected: ProducerArity::TWO,
            found: ProducerArity::ONE,
        },
        ReifyRefusal::OperationFrame(Sym::new("add")),
        ReifyRefusal::from(mint),
        ReifyRefusal::ReificationInvariant,
    ]);
    assert!(messages[0].message.contains("hole"));
    assert!(messages[1].message.contains("Zero"));
    assert!(messages[2].message.contains("Pair"));
    assert_eq!(messages[2].numbers, [2, 1]);
    assert!(messages[3].message.contains("add"));
    assert!(messages[4].message.ends_with(&mint.to_string()));
}

/// A translation refusal reads apart from every other but its twin: a hole
/// in value and in computation position share one reason. An element
/// transport names the motive's head, and an arena refusal is carried.
#[test]
fn focus_refusals_keep_their_reasons_apart()
{
    let mut core = CoreArena::new();
    let value = core.value_unit();
    let computation = core.computation_return(value);
    let mint = MintRefusal::FamilyFull(NodeFamily::Command);
    let messages = read(&[
        FocusRefusal::ElementTransport(computation, MotiveHead::Telescope),
        FocusRefusal::ElementPath(value),
        FocusRefusal::DanglingValue(value),
        FocusRefusal::DanglingComputation(computation),
        FocusRefusal::from(mint),
        FocusRefusal::Code(value),
        FocusRefusal::IncompleteValue(value),
        FocusRefusal::Session(computation),
        FocusRefusal::World(computation),
        FocusRefusal::Unelaborated(value),
        FocusRefusal::TranslationInvariant,
    ]);
    assert!(
        messages[0]
            .message
            .ends_with(&MotiveHead::Telescope.to_string())
    );
    assert!(messages[4].message.ends_with(&mint.to_string()));
    assert_eq!(
        messages[6].message,
        FocusRefusal::IncompleteComputation(computation).to_string()
    );
}

/// Every motive head no transport row reads has its own name.
#[test]
fn motive_heads_read_apart()
{
    read(&[
        MotiveHead::Data,
        MotiveHead::Record,
        MotiveHead::PathUniverse,
        MotiveHead::Path,
        MotiveHead::Flow,
        MotiveHead::Run,
        MotiveHead::RecursiveRun,
        MotiveHead::Base,
        MotiveHead::Sigma,
        MotiveHead::Thunk,
        MotiveHead::Universe,
        MotiveHead::Lift,
        MotiveHead::Element,
        MotiveHead::Abstract,
        MotiveHead::Staged,
        MotiveHead::StaticPi,
        MotiveHead::Unknown,
        MotiveHead::Stack,
        MotiveHead::Session,
        MotiveHead::Capability,
        MotiveHead::Buffer,
        MotiveHead::Kept,
        MotiveHead::World,
        MotiveHead::Telescope,
    ]);
}

/// A decoding refusal names the node with no core reading, and a readback
/// refusal names its value or carries the decoding's refusal.
#[test]
fn unfocus_and_readback_refusals_name_the_node()
{
    let unfocus = read(&[
        UnfocusRefusal::DanglingCommand(CommandId::from(51_u32)),
        UnfocusRefusal::DanglingProducer(ProducerId::from(52_u32)),
        UnfocusRefusal::DanglingConsumer(ConsumerId::from(53_u32)),
        UnfocusRefusal::CommandOutsideTheImage(CommandId::from(54_u32)),
        UnfocusRefusal::ProducerOutsideTheImage(ProducerId::from(55_u32)),
        UnfocusRefusal::ConsumerOutsideTheImage(ConsumerId::from(56_u32)),
        UnfocusRefusal::EscapingContinuation(ConsumerId::from(57_u32)),
        UnfocusRefusal::DecodeInvariant,
    ]);
    let blamed: Vec<&[u64]> = unfocus
        .iter()
        .map(|reading| reading.numbers.as_slice())
        .collect();
    assert_eq!(blamed, [
        &[51][..],
        &[52],
        &[53],
        &[54],
        &[55],
        &[56],
        &[57],
        &[],
    ]);
    let cause = UnfocusRefusal::EscapingContinuation(ConsumerId::from(62_u32));
    let readback = read(&[
        ReadbackRefusal::Unreadable(HeapValueId::from(61_u32)),
        ReadbackRefusal::Dangling(HeapValueId::from(61_u32)),
        ReadbackRefusal::Decode(cause),
        ReadbackRefusal::Capture(HeapValueId::from(63_u32)),
    ]);
    let blamed: Vec<&[u64]> = readback
        .iter()
        .map(|reading| reading.numbers.as_slice())
        .collect();
    assert_eq!(blamed, [&[61][..], &[61], &[62], &[63]]);
    assert!(readback[2].message.ends_with(&cause.to_string()));
    read(&[
        StoreFault::RegionFull(HeapFamily::Values),
        StoreFault::RegionFull(HeapFamily::ValueBindings),
    ]);
}

/// Every stop names its command, its value, its match or its constant, and
/// a native refusal carries the operation's error.
#[test]
fn stops_name_their_site()
{
    let messages = read(&[
        Stuck::PerformNoHandler(CommandId::from(71_u32)),
        Stuck::ShiftNoReset(CommandId::from(72_u32)),
        Stuck::ResumedNonStack {
            at: CommandId::from(73_u32),
            value: HeapValueId::from(74_u32),
        },
        Stuck::Primitive(PrimitiveError::DivisionByZero),
        Stuck::NonScalar(HeapValueId::from(75_u32)),
        Stuck::UndefinedConstant(ConstantIndex::from(76_usize)),
        Stuck::CyclicConstant(ConstantIndex::from(77_usize)),
        Stuck::Unobservable {
            value: HeapValueId::from(78_u32),
            head: DestructorTag::Force,
        },
        Stuck::Unmatched {
            value: HeapValueId::from(79_u32),
            arms: ConsumerId::from(80_u32),
        },
        Stuck::Unended(CommandId::from(81_u32)),
        Stuck::Outside(CommandId::from(82_u32)),
    ]);
    let blamed: Vec<&[u64]> = messages
        .iter()
        .map(|reading| reading.numbers.as_slice())
        .collect();
    assert_eq!(blamed, [
        &[71][..],
        &[72],
        &[73, 74],
        &[],
        &[75],
        &[76],
        &[77],
        &[78],
        &[80, 79],
        &[81],
        &[82],
    ]);
    assert!(
        messages[3]
            .message
            .ends_with(&PrimitiveError::DivisionByZero.to_string())
    );
}
