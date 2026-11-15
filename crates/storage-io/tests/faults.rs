//! The simulator of faults: one seed draws one log of faults under each
//! form, and the file holds what the log says.

use alloc::alloc::Global;
use alloc::collections::BTreeSet;
use core::num::NonZeroU32;

use gandr_storage_io::Buffer;
use gandr_storage_io::Chain;
use gandr_storage_io::Count;
use gandr_storage_io::Fault;
use gandr_storage_io::Handle;
use gandr_storage_io::Io;
use gandr_storage_io::Odds;
use gandr_storage_io::Pending;
use gandr_storage_io::Position;
use gandr_storage_io::Seed;
use gandr_storage_io::Segment;

use crate::common::BLOCK;
use crate::common::Scratch;
use crate::common::completions;
use crate::common::forms;

/// The blocks that each run writes, then reads back.
const BLOCKS: u8 = 24;

/// The bytes of a file.
#[repr(transparent)]
#[derive(Debug, PartialEq)]
struct Image(Vec<u8>);

/// What one run under the simulator gives.
#[derive(Debug, PartialEq)]
struct Run
{
    /// Each fault drawn.
    log: Vec<Fault>,
    /// The bytes of the file at the end.
    file: Image,
    /// Each append's key, in the order of the blocks.
    appends: Vec<Pending>,
    /// Each read's key and bytes, in the order of the blocks.
    reads: Vec<(Pending, Vec<u8>)>,
}

impl Run
{
    /// The fault that struck `pending`, if one did.
    ///
    /// # Specification
    /// trivial.
    fn fault(
        &self,
        pending: Pending,
    ) -> Option<Fault>
    {
        self.log.iter().copied().find(|fault| {
            let struck = match *fault {
                Fault::Torn { pending, .. }
                | Fault::Lost { pending }
                | Fault::Misdirected { pending, .. }
                | Fault::Corrupt { pending, .. } => pending,
            };
            struck == pending
        })
    }

    /// The file that the appends leave under the log: each block whole,
    /// torn to its prefix, absent, or at its misdirected position.
    ///
    /// # Specification
    /// trivial.
    fn expected(&self) -> Image
    {
        let mut file = Vec::new();
        for (block, (&pending, byte)) in self.appends.iter().zip(1 ..= BLOCKS).enumerate() {
            let start = block.saturating_mul(BLOCK);
            let (at, kept) = match self.fault(pending) {
                Some(Fault::Torn { kept, .. }) => (
                    start,
                    usize::try_from(u32::from(kept)).expect("a block fits"),
                ),
                Some(Fault::Lost { .. }) => continue,
                Some(Fault::Misdirected { at, .. }) => (
                    usize::try_from(u64::from(at)).expect("the file fits"),
                    BLOCK,
                ),
                Some(Fault::Corrupt { .. }) | None => (start, BLOCK),
            };
            let end = at.saturating_add(kept);
            if file.len() < end {
                file.resize(end, 0_u8);
            }
            if let Some(bytes) = file.get_mut(at .. end) {
                bytes.fill(byte);
            }
        }
        Image(file)
    }
}

/// Append `BLOCKS` blocks through `io`, each filled with its own byte and
/// each completed before the next, then read each block back.
///
/// # Specification
/// trivial.
fn run(
    io: Io<Global>,
    seed: Seed,
) -> Run
{
    let odds = Odds(NonZeroU32::new(3).expect("three is above zero"));
    let mut io = io.with_faults(seed, odds);
    let scratch = Scratch::new();
    let handle = Handle::from(scratch.open());
    let mut segment = Segment::new(handle.clone(), Position::from(0_u64));
    let mut appends = Vec::new();
    for byte in 1 ..= BLOCKS {
        appends.push(
            io.append(&mut segment, Buffer::from(vec![byte; BLOCK]), Chain::Alone)
                .expect("the append stages"),
        );
        let _done = completions(&mut io);
    }
    let mut reads = Vec::new();
    for block in 0 .. u64::from(BLOCKS) {
        let at =
            Position::from(block.saturating_mul(u64::try_from(BLOCK).expect("a block fits a u64")));
        let _read = io
            .read_at(&handle, at, Buffer::from(vec![0_u8; BLOCK]), Chain::Alone)
            .expect("the read stages");
        reads.extend(
            completions(&mut io)
                .into_iter()
                .filter_map(|done| done.buffer.map(|buffer| (done.pending, Vec::from(buffer)))),
        );
    }
    let log = io.faults().to_vec();
    drop(io);
    Run {
        log,
        file: Image(Vec::from(scratch.bytes())),
        appends,
        reads,
    }
}

/// Under each of several seeds, the ring and the blocking form draw one log
/// of faults and leave one file, which holds what the log says. Each read
/// gives the file's bytes, with one byte flipped where the log says so.
/// Across the seeds, each kind of fault strikes.
#[test]
fn a_seed_gives_one_log_and_one_file_under_each_form()
{
    let mut kinds = BTreeSet::new();
    let mut want: Vec<u8> = Vec::with_capacity(BLOCK);
    for seed in [1_u64, 7, 42, 1_729, 9_001] {
        let [ring, blocking] = forms(Count::from(8_u32));
        let under_ring = run(ring, Seed(seed));
        let under_blocking = run(blocking, Seed(seed));
        assert_eq!(
            under_ring, under_blocking,
            "seed {seed} runs alike under each form"
        );
        assert_eq!(
            under_ring.file,
            under_ring.expected(),
            "seed {seed}'s file holds what its log says"
        );
        for (block, &(pending, ref bytes)) in under_ring.reads.iter().enumerate() {
            want.clear();
            want.extend(
                under_ring
                    .file
                    .0
                    .iter()
                    .copied()
                    .skip(block.saturating_mul(BLOCK))
                    .take(BLOCK),
            );
            want.resize(BLOCK, 0_u8);
            if let Some(Fault::Corrupt { at, .. }) = under_ring.fault(pending)
                && let Some(byte) =
                    want.get_mut(usize::try_from(u32::from(at)).expect("a block fits"))
            {
                *byte ^= 0xff_u8;
            }
            assert_eq!(
                *bytes, want,
                "seed {seed}'s read of block {block} holds the file's bytes"
            );
        }
        kinds.extend(under_ring.log.iter().map(|fault| match *fault {
            Fault::Torn { .. } => "torn",
            Fault::Lost { .. } => "lost",
            Fault::Misdirected { .. } => "misdirected",
            Fault::Corrupt { .. } => "corrupt",
        }));
    }
    assert_eq!(
        kinds.into_iter().collect::<Vec<_>>(),
        vec!["corrupt", "lost", "misdirected", "torn"],
        "each kind of fault strikes across the seeds"
    );
}
