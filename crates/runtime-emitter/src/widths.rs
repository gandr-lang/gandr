//! The blocks of the width rows: a row of a width that one instruction of
//! each host computes runs as a block of machine code, in place of a call of
//! the host.
//!
//! A call of the host for one addition of `u64` reads its two operands into
//! a vector, runs the evaluator of the prelude and allocates its answer. A
//! block does the one instruction. Its operands are the fields of the two
//! machine integers, and the block stencil gives its answer a machine
//! integer of the row's form.
//!
//! The field of a width is its two's complement at its own width,
//! zero-extended to the word. An operation on two such words gives the right
//! low bits of the answer, and the high bits can be wrong. So the block of a
//! narrow width ends with two shifts, which clear the bits above the width.
//!
//! The process compiles the block of each row one time, by its description,
//! and each later lowering takes its key with no process. A row with no
//! description keeps the call of the host, and so does a row whose block the
//! assembler refuses. Both give the same answer, because the call evaluates
//! the row's own definition.
//!
//! # References
//!
//! - `vault:01a1ead7-6581-7f22-9479-5b0b363e80d3` — newest: the typed machine
//!   interface (§ typed-machine-plan) builds a block of machine code for each
//!   operation of a width.

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use core::fmt::Write as _;
use std::sync::LazyLock;

use gandr_core_term::primitive::MachineInstruction;
use gandr_core_term::primitive::MachineOperation;
use gandr_core_term::primitive::Primitive;

use crate::block::Answer;
use crate::block::Assembler;
use crate::block::Blocks;
use crate::block::Cache;
use crate::block::Class;
use crate::block::Description;
use crate::block::Direction;
use crate::block::Flags;
use crate::block::Key;
use crate::block::Memory;
use crate::block::Operand;
use crate::block::Options;
use crate::block::Place;
use crate::block::Refusal;
use crate::block::Target;
use crate::lower::width_form;
use crate::machine;

/// The block compiler of the width rows, with the cache of the process.
static BLOCKS: LazyLock<Blocks> =
    LazyLock::new(|| Blocks::new(Assembler::pinned(), Cache::Process));

/// The block of a width row on this host: what a lowering enters.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct WidthBlock
{
    /// The key of the block's code in the process's table of blocks.
    pub key: Key,
    /// The bits of the block entry's operand B past the count of operands:
    /// the answer in the form of the row's width.
    pub answered: usize,
}

/// Why a row runs as a call of the host and not as a block.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Unblocked
{
    /// No description gives the row: it is no machine operation of a width.
    Undescribed,
    /// This host runs no block: its target is none of the targets of a block.
    Unhosted,
    /// The block compiler refused the row's description.
    Refused(Refusal),
}

/// How many words an instruction of a width row reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reads
{
    /// One word: the negation.
    One,
    /// Two words: each other instruction.
    Two,
}

/// The bits above a width that a block clears from its answer: none for a
/// width of 64 bits.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Cut(u32);

/// How a target that writes the answer apart from its operands spells an
/// instruction, its two shifts and an immediate.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Spelling
{
    /// The instruction.
    mnemonic: &'static str,
    /// The shift toward the high bits.
    left: &'static str,
    /// The logical shift toward the low bits.
    right: &'static str,
    /// The prefix of an immediate.
    immediate: &'static str,
}

/// The description of the block that computes `operation` on `target`.
///
/// The block computes the instruction on the words of the operands, then
/// clears the bits above a narrow width by a shift toward the high bits and
/// a logical shift back. x86-64 computes in place, so its first word takes
/// the answer, which the answer's register copies last.
///
/// # Specification
/// - ensures: the block's answer is the low bits of the instruction on the
///   operands' words, zero-extended from the operation's width; it reads its
///   operands and touches no memory.
/// - executable: none — the bytes are the assembler's, observable only by their
///   run.
///
/// # Cost
/// - allocation: the template and the operands, durable by the block
///
/// # Adequacy
/// - hypothesis: L2 — each machine row of each width answers on the native tier
///   and on the executor what the host's evaluation of the row answers, on the
///   bounds of its width; a wrong instruction, a lost cut or a cut that keeps a
///   bit too many changes one answer.
/// - witness: `widths::tests::each_machine_row_answers_as_the_host_on_each_tier_8002`
#[inline]
#[must_use]
pub fn description(
    target: Target,
    operation: MachineOperation,
) -> Description
{
    let Cut(cut) = Cut(64_u32.saturating_sub(u32::from(operation.width.bits())));
    let reads = if operation.instruction == MachineInstruction::Not {
        Reads::One
    }
    else {
        Reads::Two
    };
    let general = Place::Class(Class::General);
    let word = |direction| Operand {
        direction,
        place: general.clone(),
    };
    let (template, first) = match target {
        Target::LinuxX86_64 => {
            let mnemonic = match operation.instruction {
                MachineInstruction::Add => "add",
                MachineInstruction::Sub => "sub",
                MachineInstruction::Mul => "imul",
                MachineInstruction::And => "and",
                MachineInstruction::Or => "or",
                MachineInstruction::Xor => "xor",
                MachineInstruction::Not => "not",
            };
            let mut template = if reads == Reads::One {
                format!("{mnemonic} {{0}}")
            }
            else {
                format!("{mnemonic} {{0}}, {{1}}")
            };
            if cut > 0 {
                let _written = write!(template, "\nshl {{0}}, {cut}\nshr {{0}}, {cut}");
            }
            template.push_str("\nmov {answer}, {0}");
            (template, Direction::InOut)
        },
        Target::LinuxAarch64 | Target::DarwinAarch64 => {
            let mnemonic = match operation.instruction {
                MachineInstruction::Add => "add",
                MachineInstruction::Sub => "sub",
                MachineInstruction::Mul => "mul",
                MachineInstruction::And => "and",
                MachineInstruction::Or => "orr",
                MachineInstruction::Xor => "eor",
                MachineInstruction::Not => "mvn",
            };
            let spelling = Spelling {
                mnemonic,
                left: "lsl",
                right: "lsr",
                immediate: "#",
            };
            (three_address(spelling, reads, Cut(cut)), Direction::In)
        },
        Target::LinuxRiscv64 => {
            let mnemonic = match operation.instruction {
                MachineInstruction::Add => "add",
                MachineInstruction::Sub => "sub",
                MachineInstruction::Mul => "mul",
                MachineInstruction::And => "and",
                MachineInstruction::Or => "or",
                MachineInstruction::Xor => "xor",
                MachineInstruction::Not => "not",
            };
            let spelling = Spelling {
                mnemonic,
                left: "slli",
                right: "srli",
                immediate: "",
            };
            (three_address(spelling, reads, Cut(cut)), Direction::In)
        },
    };
    let operands: Box<[Operand]> = if reads == Reads::One {
        Box::new([word(first)])
    }
    else {
        Box::new([word(first), word(Direction::In)])
    };
    Description {
        target,
        template: template.as_str().into(),
        operands,
        answer: Answer::Place(general),
        clobbers: Box::new([]),
        options: Options {
            memory: Memory::Untouched,
            flags: Flags::Clobbered,
        },
    }
}

/// The template of a target whose instructions name the answer apart from
/// their operands: the instruction into the answer, then its cut by `cut`
/// bits, with the two shifts and the prefix of an immediate that `spelling`
/// names.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the template, durable by the block
fn three_address(
    spelling: Spelling,
    reads: Reads,
    Cut(cut): Cut,
) -> String
{
    let Spelling {
        mnemonic,
        left,
        right,
        immediate,
    } = spelling;
    let mut template = match reads {
        Reads::One => format!("{mnemonic} {{answer}}, {{0}}"),
        Reads::Two => format!("{mnemonic} {{answer}}, {{0}}, {{1}}"),
    };
    if cut > 0 {
        let _written = write!(
            template,
            "\n{left} {{answer}}, {{answer}}, {immediate}{cut}\n{right} {{answer}}, {{answer}}, {immediate}{cut}"
        );
    }
    template
}

/// The block of `primitive` on this host, compiled one time for the process.
///
/// # Specification
/// - ensures: `Ok` exactly for a row with a machine operation whose description
///   the block compiler compiles for this host; its key names the compiled
///   block, and its bits ask for the answer in the row's form.
/// - fails: [`Unblocked::Undescribed`] for a row with no machine operation,
///   [`Unblocked::Unhosted`] on a host that runs no block, and
///   [`Unblocked::Refused`] with the block compiler's refusal.
/// - executable: none — a compile is a process of the assembler.
///
/// # Cost
/// - allocation: the description, transient; the block's slot and code on its
///   first request, durable by the process
///
/// # Errors
/// As `fails` states.
///
/// # Adequacy
/// - hypothesis: L2 — each machine row of each width lowers to a block entry on
///   each host whose assembler compiles, and a row of another operation lowers
///   to a call of the host.
/// - witness: `widths::tests::each_machine_row_lowers_to_a_block_8002`
pub(crate) fn block(primitive: Primitive) -> Result<WidthBlock, Unblocked>
{
    let operation = primitive
        .machine_operation()
        .ok_or(Unblocked::Undescribed)?;
    let host = machine::HOSTED.map_err(|_unhosted| Unblocked::Unhosted)?;
    let compiled = BLOCKS
        .compile(&description(host, operation))
        .map_err(Unblocked::Refused)?;
    Ok(WidthBlock {
        key: compiled.key,
        answered: usize::from(width_form(operation.width).answered()),
    })
}

#[cfg(test)]
#[cfg(gandr_executable)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_sequent::CommandArena;
    use gandr_core_sequent::CommandId;
    use gandr_core_sequent::Definitions;
    use gandr_core_sequent::HeapValue;
    use gandr_core_sequent::Outcome;
    use gandr_core_sequent::Provenance;
    use gandr_core_sequent::Store;
    use gandr_core_sequent::Writers;
    use gandr_core_sequent::focus_computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::PRELUDE;
    use gandr_core_term::primitive::Primitive;
    use gandr_core_term::primitive::PrimitiveType;
    use gandr_core_term::primitive::Scalar;
    use gandr_kernel_term::FixedInteger;
    use gandr_kernel_term::IntegerWidth;
    use gandr_kernel_term::Literal;

    use crate::PATCHER;
    use crate::budget::Budget;
    use crate::lower::Callee;
    use crate::lower::lower;
    use crate::run::RunInputs;
    use crate::run::Tier;
    use crate::run::evaluate_on;

    /// The ten widths and the names of their rows.
    const WIDTHS: [(IntegerWidth, &str); 10] = [
        (IntegerWidth::U8, "u8"),
        (IntegerWidth::U16, "u16"),
        (IntegerWidth::U32, "u32"),
        (IntegerWidth::U64, "u64"),
        (IntegerWidth::Usize, "usize"),
        (IntegerWidth::I8, "i8"),
        (IntegerWidth::I16, "i16"),
        (IntegerWidth::I32, "i32"),
        (IntegerWidth::I64, "i64"),
        (IntegerWidth::Isize, "isize"),
    ];

    /// The tiers this host runs: native where a patcher exists, the executor
    /// everywhere.
    ///
    /// # Specification
    /// trivial.
    fn tiers() -> &'static [Tier]
    {
        if PATCHER {
            &[Tier::Native, Tier::Executor]
        }
        else {
            &[Tier::Executor]
        }
    }

    /// The bounds of `width`: zero, one, the largest signed value, the least
    /// signed value and all ones, as the width's bit patterns.
    ///
    /// # Specification
    /// trivial.
    fn bounds(width: IntegerWidth) -> [FixedInteger; 5]
    {
        let count = u32::from(width.bits());
        let ones = u64::MAX.unbounded_shr(64_u32.saturating_sub(count));
        let sign = 1_u64.unbounded_shl(count.saturating_sub(1));
        [0_u64, 1, sign.wrapping_sub(1), sign, ones].map(|pattern| {
            FixedInteger::try_from((width, pattern)).expect("a pattern of the width")
        })
    }

    /// The name of a row of the prelude.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct RowName<'name>(&'name str);

    /// The row of the prelude that `name` names.
    ///
    /// # Specification
    /// trivial.
    fn row(RowName(name): RowName<'_>) -> Primitive
    {
        PRELUDE
            .iter()
            .copied()
            .find(|row| row.name().as_ref() == name)
            .expect("a prelude row")
    }

    /// The focused command that `root` makes of the literals `operands`.
    ///
    /// # Specification
    /// trivial.
    fn focused(
        operands: &[FixedInteger],
        root: impl FnOnce(&mut CoreArena, &[gandr_core_term::ValueId]) -> gandr_core_term::ComputationId,
    ) -> (CommandArena, CommandId)
    {
        let mut core = CoreArena::new();
        let values: Vec<_> = operands
            .iter()
            .map(|&fixed| core.value_literal(Literal::Fixed(fixed)))
            .collect();
        let root = root(&mut core, &values);
        let mut commands = CommandArena::new();
        let root = focus_computation(
            &core,
            root,
            &mut commands,
            &mut Provenance::new(),
            &Writers::NONE,
        )
        .expect("the program focuses");
        (commands, root)
    }

    /// The focused call of `row` on the literals `operands`.
    ///
    /// # Specification
    /// trivial.
    fn applied(
        row: Primitive,
        operands: &[FixedInteger],
    ) -> (CommandArena, CommandId)
    {
        focused(operands, |core, values| {
            let arguments = match *values {
                [only] => Arguments::Unary(only),
                [first, second] => Arguments::Binary([first, second]),
                _ => panic!("a row of one or two operands"),
            };
            core.computation_primitive(row, arguments)
        })
    }

    /// The value that the program halts with on `tier`.
    ///
    /// # Specification
    /// trivial.
    fn ran(
        tier: Tier,
        &(ref commands, root): &(CommandArena, CommandId),
    ) -> HeapValue
    {
        let mut store = Store::new();
        let outcome = evaluate_on(
            tier,
            commands,
            &Definitions::new(),
            root,
            Budget::from(1_usize << 20_u32),
            RunInputs::new(&mut store),
        )
        .expect("the program runs");
        let Outcome::Halted(value) = outcome
        else {
            panic!("the program halts on {tier:?}");
        };
        store
            .value(value)
            .expect("the store holds the answer")
            .clone()
    }

    /// The machine rows of the prelude.
    ///
    /// # Specification
    /// trivial.
    fn machine_rows() -> impl Iterator<Item = Primitive>
    {
        PRELUDE
            .iter()
            .copied()
            .filter(|row| row.machine_operation().is_some())
    }

    /// Each machine row of each width answers, on the native tier and on the
    /// executor, what the host's evaluation of the row answers, over each
    /// pair of the width's bounds. The bounds hold a carry out of the width,
    /// a borrow below zero, a product past it and the negation of zero, so a
    /// wrong instruction, a lost cut or a cut that keeps a bit too many
    /// changes one answer.
    #[test]
    fn each_machine_row_answers_as_the_host_on_each_tier_8002()
    {
        for row in machine_rows() {
            let PrimitiveType::Fixed(width) = row.result()
            else {
                panic!("{} answers a width", row.name().as_ref());
            };
            let bounds = bounds(width);
            for first in bounds {
                for second in bounds {
                    let pair = [first, second];
                    let operands = pair
                        .get(.. row.arguments().len())
                        .expect("a row of one or two operands");
                    let scalars = pair.map(Scalar::Fixed);
                    let borrowed = scalars.each_ref().map(Scalar::borrowed);
                    let arguments = borrowed
                        .get(.. row.arguments().len())
                        .expect("a row of one or two operands");
                    let Ok(Scalar::Fixed(expected)) = row.evaluate(arguments)
                    else {
                        panic!("{} answers a width", row.name().as_ref());
                    };
                    let program = applied(row, operands);
                    for &tier in tiers() {
                        assert_eq!(
                            HeapValue::Literal(Literal::Fixed(expected)),
                            ran(tier, &program),
                            "{} {operands:?} on {tier:?}",
                            row.name().as_ref()
                        );
                    }
                }
            }
        }
    }

    /// Each machine row lowers to one block entry, with no call of the host
    /// and no row of the literal table, and each other row of a width that
    /// answers a width lowers to a call of the host. The seventy machine rows
    /// are seven for each width, so a row that the lowering leaves a call
    /// changes the count of blocks.
    #[test]
    fn each_machine_row_lowers_to_a_block_8002()
    {
        let mut blocks = 0_usize;
        for row in PRELUDE.iter().copied() {
            let PrimitiveType::Fixed(width) = row.result()
            else {
                continue;
            };
            let [bound, ..] = bounds(width);
            let pair = [bound; 2];
            let operands = pair
                .get(.. row.arguments().len())
                .expect("a row of one or two operands");
            let (commands, root) = applied(row, operands);
            let lowered = lower(&commands, &Definitions::new(), root).expect("the call lowers");
            let name = row.name();
            assert!(
                lowered.literals.is_empty(),
                "{}: no literal row",
                name.as_ref()
            );
            if row.machine_operation().is_some() {
                assert_eq!(
                    1,
                    lowered.function.blocks().len(),
                    "{}: one block",
                    name.as_ref()
                );
                assert!(lowered.callees.is_empty(), "{}: no call", name.as_ref());
                blocks = blocks.saturating_add(1);
            }
            else {
                assert!(
                    lowered.function.blocks().is_empty(),
                    "{}: no block",
                    name.as_ref()
                );
                assert_eq!(
                    Vec::from([Callee::Primitive(row)]),
                    lowered.callees,
                    "{}: a call of the host",
                    name.as_ref()
                );
            }
        }
        assert_eq!(70, blocks, "seven machine rows for each of ten widths");
    }

    /// One operation of a width allocates exactly one object of two words on
    /// each tier: three heap words, its count, its header and its field. It
    /// calls no host, so it fills no vector, and its program names no row of
    /// the literal table. The sum carries out of the width, so the answer is
    /// the cut one. A second box, a lost box or a call of the host changes
    /// the count or the tables.
    #[test]
    fn one_operation_allocates_one_object_of_two_words_8002()
    {
        let program = applied(row(RowName("u8.wrapping_add")), &[
            FixedInteger::U8(200),
            FixedInteger::U8(100),
        ]);
        let lowered = lower(&program.0, &Definitions::new(), program.1).expect("the call lowers");
        assert!(lowered.callees.is_empty(), "no call of the host");
        assert!(lowered.literals.is_empty(), "no row of the literal table");
        for &tier in tiers() {
            assert_eq!(
                HeapValue::Literal(Literal::Fixed(FixedInteger::U8(44))),
                ran(tier, &program),
                "the sum on {tier:?}"
            );
            assert_eq!(
                3,
                crate::run::ALLOCATED.get(),
                "the count, the header and the field on {tier:?}"
            );
        }
    }

    /// Each bound of each width crosses the machine as itself on each tier: a
    /// literal returned whole, and a literal that the host reads and answers
    /// through the saturating sum with zero, a call of the host. A form read
    /// as another width, a field read with a bit too many or an answer of the
    /// host in the literal table changes one answer.
    #[test]
    fn each_width_crosses_the_machine_as_itself_8002()
    {
        for (width, name) in WIDTHS {
            let [zero, ..] = bounds(width);
            let saturating = row(RowName(&alloc::format!("{name}.saturating_add")));
            for bound in bounds(width) {
                let returned = focused(&[bound], |core, values| {
                    core.computation_return(values.first().copied().expect("one literal"))
                });
                let hosted = applied(saturating, &[bound, zero]);
                for &tier in tiers() {
                    let expected = HeapValue::Literal(Literal::Fixed(bound));
                    assert_eq!(expected, ran(tier, &returned), "{bound:?} on {tier:?}");
                    assert_eq!(
                        expected,
                        ran(tier, &hosted),
                        "{bound:?} through the host on {tier:?}"
                    );
                }
            }
        }
    }

    /// Each machine row's description compiles for each of the four targets,
    /// on any host: the templates of the targets that this host does not run
    /// are read by their own assembler, and each block holds code for its
    /// own target. A mnemonic that a target lacks, or an immediate that it
    /// spells otherwise, is refused by name.
    #[test]
    fn each_description_compiles_on_each_target_8002()
    {
        let blocks = crate::block::Blocks::new(
            crate::block::Assembler::pinned(),
            crate::block::Cache::Process,
        );
        for row in machine_rows() {
            let operation = row.machine_operation().expect("a machine row");
            for target in crate::block::Target::ALL {
                let block = blocks
                    .compile(&super::description(target, operation))
                    .unwrap_or_else(|refusal| {
                        panic!("{} on {target}: {refusal:?}", row.name().as_ref())
                    });
                assert_eq!(target, block.target, "{} on {target}", row.name().as_ref());
                assert!(
                    !block.code.0.is_empty(),
                    "{} on {target}: no code",
                    row.name().as_ref()
                );
            }
        }
    }
}
