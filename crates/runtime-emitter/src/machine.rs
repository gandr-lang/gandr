//! The blocks of machine code that a run enters: the bytes of each block
//! that the process compiled, by its key, mapped executable one time for the
//! process.
//!
//! A function names each block that it enters by the block's key, and a run
//! resolves each key to an address before it starts. The first resolution of
//! a key maps the block's bytes into an executable region of the process.
//! Each later resolution reads the address that the first wrote, with no lock
//! and no allocation. A region is never unmapped, so an address stays valid
//! for the process. So each block's bytes are mapped one time, however many
//! functions and runs enter it.
//!
//! A key that no compile of the process gave, a block of another target, and
//! a host that refuses executable memory each refuse the resolution by name.
//! So a run that names such a block declines before it starts.
//!
//! # References
//!
//! - `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — lineage: the IO direction
//!   (§ io-direction-block) decides one transition that enters a block on both
//!   tiers, a host with no patcher too.

use alloc::vec::Vec;
use core::fmt;
use std::sync::LazyLock;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;

use gandr_runtime_stencils::Word;

use crate::block::Code;
use crate::block::Key;
use crate::block::Target;
use crate::executable::Address;
use crate::executable::MapFailure;
use crate::executable::Offset;
use crate::executable::Region;

/// The bytes that one region of blocks maps, unless one block needs more.
const REGION_BYTES: usize = 1 << 16;

/// The target of the blocks that run on this host.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub(crate) const HOST: Target = Target::LinuxX86_64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
pub(crate) const HOST: Target = Target::LinuxAarch64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "linux", target_arch = "riscv64"))]
pub(crate) const HOST: Target = Target::LinuxRiscv64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) const HOST: Target = Target::DarwinAarch64;

/// Why a key gives no address.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Unentered
{
    /// No compile of this process gave the key.
    Unknown(Key),
    /// The block runs on this target, and this host runs another.
    Target(Target),
    /// The host refused the executable memory that the block needs.
    Map(MapFailure),
}

impl fmt::Display for Unentered
{
    /// Say why the block gives no address, in a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unknown(key) => write!(f, "no compile of the process gave the block {key}"),
            Self::Target(target) => write!(f, "the block runs on {target}, and not on this host"),
            Self::Map(MapFailure(error)) => {
                write!(
                    f,
                    "the host refused executable memory for a block: error {error}"
                )
            },
        }
    }
}

/// One block that the process compiled: its target, its bytes, and the
/// address of the bytes once mapped.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Entry
{
    /// The target that the bytes run on.
    target: Target,
    /// The bytes.
    code: Code,
    /// The executable address of the bytes, once a run resolved the key.
    address: OnceLock<Address>,
}

/// The blocks of the process and the regions that hold their bytes.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
struct Machine
{
    /// Each block that a compile of the process gave, by its key.
    entries: papaya::HashMap<Key, Entry>,
    /// The regions, the last the one mapped into; the lock serialises each
    /// first mapping of a block.
    regions: Mutex<Vec<Region>>,
}

/// The process's blocks.
static MACHINE: LazyLock<Machine> = LazyLock::new(Machine::default);

/// Record the block of `key`: its target and its code. A key recorded again
/// keeps its first entry, since one key has one code.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the entry of a new key, durable by the key
pub(crate) fn record(
    key: Key,
    target: Target,
    code: &Code,
)
{
    let entries = MACHINE.entries.pin();
    let _entry = entries.get_or_insert_with(key, || Entry {
        target,
        code: code.clone(),
        address: OnceLock::new(),
    });
}

/// The executable address of the block of `key`, its bytes mapped on the
/// first request.
///
/// # Specification
/// - ensures: the address of the key's bytes in an executable region of the
///   process, the same for each request of one key; the bytes are mapped one
///   time.
/// - fails: [`Unentered::Unknown`] for a key that no compile of the process
///   gave, [`Unentered::Target`] for a block of another target than this
///   host's, and [`Unentered::Map`] when the host refuses the region.
/// - panics: none.
/// - executable: none — the address is the host's mapping, observable only by
///   entering it.
///
/// # Cost
/// - allocation: none once the key is mapped; a first request of a key maps a
///   region when no region holds room for its bytes
///
/// # Errors
/// [`Unentered`] naming why the key gives no address.
///
/// # Adequacy
/// - hypothesis: L2 — a block that adds its two words answers their sum on each
///   tier of each host, and a block of another target declines the run by name;
///   a wrong address faults or answers another sum.
/// - witness: `machine::tests::a_block_answers_alike_on_each_tier`
/// - witness: `machine::tests::a_block_no_host_runs_declines_the_run`
#[inline]
pub fn address(key: Key) -> Result<Word, Unentered>
{
    let entries = MACHINE.entries.pin();
    let entry = entries.get(&key).ok_or(Unentered::Unknown(key))?;
    if let Some(&Address(at)) = entry.address.get() {
        return Ok(Word::from(at));
    }
    runs_here(entry.target)?;
    let mut regions = MACHINE
        .regions
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    if let Some(&Address(at)) = entry.address.get() {
        return Ok(Word::from(at));
    }
    let placed = place(&mut regions, &entry.code).map_err(Unentered::Map)?;
    let &Address(at) = entry.address.get_or_init(|| placed);
    Ok(Word::from(at))
}

/// The address of each block of `keys`, in their order.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: one word for each key, none for no key
///
/// # Errors
/// The first key's [`Unentered`], as [`address`] gives it.
pub(crate) fn resolve(keys: &[Key]) -> Result<Vec<Word>, Unentered>
{
    keys.iter().map(|&key| address(key)).collect()
}

/// Refuse a block whose target this host does not run.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Unentered::Target`] for another target than this host's, and for each
/// target on a host that no block runs on.
fn runs_here(target: Target) -> Result<(), Unentered>
{
    #[cfg(gandr_executable)]
    if target == HOST {
        return Ok(());
    }
    Err(Unentered::Target(target))
}

/// Copy `code` into the last region with room for it, or into a region
/// mapped for it, and give its executable address.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: a region's slot when a region is mapped, durable for the
///   process
///
/// # Errors
/// The host's [`MapFailure`] when a region is needed and refused.
fn place(
    regions: &mut Vec<Region>,
    code: &Code,
) -> Result<Address, MapFailure>
{
    let length = Offset(code.0.len());
    let room = regions
        .last_mut()
        .and_then(|region| region.reserve(length).ok());
    let reservation = if let Some(reservation) = room {
        reservation
    }
    else {
        let mut region = Region::map(Offset(REGION_BYTES.max(length.0)))?;
        let reservation = region.reserve(length).map_err(|_full| MapFailure(0))?;
        regions.push(region);
        reservation
    };
    let Some(region) = regions.last()
    else {
        return Err(MapFailure(0));
    };
    region.write(reservation, |bytes| bytes.0.copy_from_slice(&code.0));
    Ok(region.address(reservation))
}

#[cfg(all(test, gandr_executable))]
mod tests
{
    use alloc::boxed::Box;
    use alloc::vec::Vec;

    use gandr_core_sequent::CommandArena;
    use gandr_core_sequent::Definitions;
    use gandr_core_sequent::HeapValue;
    use gandr_core_sequent::Outcome;
    use gandr_core_sequent::Store;
    use gandr_kernel_term::Literal;
    use gandr_runtime_stencils::BLOCK_ANSWERS;
    use gandr_runtime_stencils::INTEGER_HEADER;
    use gandr_runtime_stencils::StencilId;
    use gandr_runtime_stencils::Word;

    use super::HOST;
    use super::Unentered;
    use crate::PATCHER;
    use crate::block::Answer;
    use crate::block::Assembler;
    use crate::block::Blocks;
    use crate::block::Cache;
    use crate::block::Class;
    use crate::block::Description;
    use crate::block::Direction;
    use crate::block::Key;
    use crate::block::Operand as BlockOperand;
    use crate::block::Options;
    use crate::block::Place;
    use crate::block::Target;
    use crate::budget::Budget;
    use crate::function::Alt;
    use crate::function::Function;
    use crate::function::Immediate;
    use crate::function::Instruction;
    use crate::function::Operand;
    use crate::host::integer_literal;
    use crate::lower::Lowered;
    use crate::run::Declined;
    use crate::run::Kept;
    use crate::run::Ran;
    use crate::run::RunInputs;
    use crate::run::Tier;
    use crate::run::on_tier;

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

    /// A block on `target` that adds its two words and answers the sum, or
    /// an empty block that answers nothing.
    ///
    /// # Specification
    /// trivial.
    fn adding(target: Target) -> Description
    {
        let general = Place::Class(Class::General);
        let word = |direction| BlockOperand {
            direction,
            place: general.clone(),
        };
        // x86-64 adds in place: its first word takes the sum, which the
        // answer copies last, so the answer may share the second's register.
        let (template, first) = match target {
            Target::LinuxX86_64 => ("add {0}, {1}\nmov {answer}, {0}", Direction::InOut),
            Target::LinuxAarch64 | Target::LinuxRiscv64 | Target::DarwinAarch64 => {
                ("add {answer}, {0}, {1}", Direction::In)
            },
        };
        Description {
            target,
            template: template.into(),
            operands: Box::new([word(first), word(Direction::In)]),
            answer: Answer::Place(general.clone()),
            clobbers: Box::new([]),
            options: Options::DEFAULT,
        }
    }

    /// The empty block on `target`, which answers nothing.
    ///
    /// # Specification
    /// trivial.
    fn empty(target: Target) -> Description
    {
        Description {
            target,
            template: "".into(),
            operands: Box::new([]),
            answer: Answer::Zero,
            clobbers: Box::new([]),
            options: Options::DEFAULT,
        }
    }

    /// The key of `description`'s block, compiled by the pinned `llc`.
    ///
    /// # Specification
    /// trivial.
    fn compiled(description: &Description) -> Key
    {
        Blocks::new(Assembler::pinned(), Cache::Process)
            .compile(description)
            .expect("the block compiles")
            .key
    }

    /// The function that pushes `words` as machine integers, enters the block
    /// of `key`, and halts with the value in hand.
    ///
    /// # Specification
    /// trivial.
    fn entering(
        key: Key,
        words: &[i64],
        answers: bool,
    ) -> Function
    {
        let mut function = Function::default();
        let step = |function: &mut Function, stencil, a, b| {
            let _at = function.push(Instruction {
                stencil,
                a,
                b,
                alt: Alt::None,
            });
        };
        for &word in words {
            let integer = function.object(&[INTEGER_HEADER, Word::from(word)]);
            step(
                &mut function,
                StencilId::Const,
                Operand::Data(integer),
                Operand::Unused,
            );
            step(
                &mut function,
                StencilId::Push,
                Operand::Unused,
                Operand::Unused,
            );
        }
        let row = function.block(key);
        let count = words.len() | if answers { BLOCK_ANSWERS } else { 0 };
        let count = u32::try_from(count).expect("a count below 2³²");
        step(
            &mut function,
            StencilId::Block,
            Operand::Block(row),
            Operand::Immediate(Immediate::from(count)),
        );
        step(
            &mut function,
            StencilId::Pop,
            Operand::Unused,
            Operand::Unused,
        );
        function
    }

    /// Run `function` on `tier`, and read the value it halts with.
    ///
    /// # Specification
    /// trivial.
    fn run(
        tier: Tier,
        function: Function,
    ) -> Result<HeapValue, Declined>
    {
        let lowered = Lowered {
            function,
            fused: Vec::new(),
            sites: Vec::new(),
            captures: Vec::new(),
            accumulate: None,
            spawned: Vec::new(),
            cells: Vec::new(),
            bounds: Vec::new(),
            heads: Vec::new(),
            literals: Vec::new(),
            codes: Vec::new(),
            callees: Vec::new(),
            handlers: Vec::new(),
            windows: Vec::new(),
            owners: Vec::new(),
            linears: Vec::new(),
            unwinds: Vec::new(),
            unmatched: Vec::new(),
            globals: Vec::new(),
            joined: None,
            marker: None,
            kept: Kept::default(),
        };
        let mut store = Store::new();
        let ran = on_tier(
            tier,
            &lowered,
            (&CommandArena::new(), &Definitions::new()),
            Budget::from(1_usize << 20),
            RunInputs::new(&mut store),
        )?;
        let Ran::Ended(Outcome::Halted(value)) = ran
        else {
            panic!("the function halts on {tier:?}");
        };
        Ok(store
            .value(value)
            .expect("the store holds the answer")
            .clone())
    }

    /// The machine integer `bits` as the store holds it.
    ///
    /// # Specification
    /// trivial.
    fn integer(bits: i64) -> HeapValue
    {
        HeapValue::Literal(Literal::Integer(integer_literal(Word::from(bits))))
    }

    /// A block that adds its two words answers their sum as a machine
    /// integer on each tier, at zero, at a carry into the sign and with a
    /// negative word; and a block that answers nothing leaves the last word
    /// pushed in hand. A word read from the object and not its field, a lost
    /// answer or swapped words change one.
    #[test]
    fn a_block_answers_alike_on_each_tier()
    {
        let adds = compiled(&adding(HOST));
        let nothing = compiled(&empty(HOST));
        for &tier in tiers() {
            for (first, second) in [(0, 0), (2, 40), (i64::MAX, 1), (-7, 3)] {
                assert_eq!(
                    Ok(integer(first.wrapping_add(second))),
                    run(tier, entering(adds, &[first, second], true)),
                    "{first} + {second} on {tier:?}"
                );
            }
            assert_eq!(
                Ok(integer(9)),
                run(tier, entering(nothing, &[5, 9], false)),
                "an empty block on {tier:?}"
            );
        }
    }

    /// A block of another target than this host's, and a key that no compile
    /// gave, decline the run by name on each tier before it starts.
    #[test]
    fn a_block_no_host_runs_declines_the_run()
    {
        let foreign = Target::ALL
            .into_iter()
            .find(|&target| target != HOST)
            .expect("a target other than this host's");
        let elsewhere = compiled(&adding(foreign));
        let unknown = Key(blake3::hash(b"no compile gave this key"));
        for &tier in tiers() {
            assert_eq!(
                Err(Declined::Block(Unentered::Target(foreign))),
                run(tier, entering(elsewhere, &[1, 2], true)),
                "a block of {foreign} on {tier:?}"
            );
            assert_eq!(
                Err(Declined::Block(Unentered::Unknown(unknown))),
                run(tier, entering(unknown, &[1, 2], true)),
                "an unknown key on {tier:?}"
            );
        }
    }
}
