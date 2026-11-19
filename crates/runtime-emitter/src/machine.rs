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
const HOST: Target = Target::LinuxX86_64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const HOST: Target = Target::LinuxAarch64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "linux", target_arch = "riscv64"))]
const HOST: Target = Target::LinuxRiscv64;
/// The target of the blocks that run on this host.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const HOST: Target = Target::DarwinAarch64;

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
/// - witness: `run::tests::a_block_answers_alike_on_each_tier`
/// - witness: `run::tests::a_block_no_host_runs_declines_the_run`
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
