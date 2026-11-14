//! The ring: linked submissions complete in the order of their links, and a
//! failed write cancels the sync linked to it.

use std::fs::File;
use std::fs::OpenOptions;
use std::os::fd::AsFd as _;
use std::path::PathBuf;

use gandr_storage_io::Buffer;
use gandr_storage_io::Completion;
use gandr_storage_io::Count;
use gandr_storage_io::Entry;
use gandr_storage_io::Key;
use gandr_storage_io::Position;
use gandr_storage_io::Ring;

/// The bytes of one block that the witnesses write and read.
const BLOCK: usize = 4_096;

/// A fresh file for one witness, removed when the witness ends.
struct Scratch
{
    /// The file's path.
    path: PathBuf,
}

impl Scratch
{
    /// A fresh scratch file named for `witness`.
    fn new(witness: &str) -> Self
    {
        let path =
            std::env::temp_dir().join(format!("gandr-storage-io-{witness}-{}", std::process::id()));
        Self { path }
    }

    /// The file, open to read and to write.
    fn open(&self) -> File
    {
        OpenOptions::new()
            .create(true)
            .truncate(true)
            .read(true)
            .write(true)
            .open(&self.path)
            .expect("the scratch file opens")
    }
}

impl Drop for Scratch
{
    fn drop(&mut self)
    {
        let _removed = std::fs::remove_file(&self.path);
    }
}

/// Each completion that stands, in the order the ring posts them.
fn completions(ring: &mut Ring) -> Vec<Completion>
{
    core::iter::from_fn(|| ring.complete()).collect()
}

/// A write, a sync and a read, linked in that order, complete in that order;
/// the read returns the bytes that the write wrote.
#[test]
fn a_linked_write_sync_and_read_complete_in_order()
{
    let scratch = Scratch::new("linked");
    let file = scratch.open();
    let mut ring = Ring::new(Count::from(8_u32)).expect("the ring sets up");
    let written = Buffer::from(vec![0xa5_u8; BLOCK]);
    let mut read = Buffer::from(vec![0_u8; BLOCK]);
    // SAFETY: the buffer outlives its completion, which the test reaps
    // before it reads the buffers.
    unsafe {
        ring.push(
            Entry::write(
                file.as_fd(),
                &written,
                Position::from(0_u64),
                Key::from(1_u64),
            )
            .linked(),
        )
    }
    .expect("a slot is free");
    // SAFETY: a sync names no buffer.
    unsafe { ring.push(Entry::sync(file.as_fd(), Key::from(2_u64)).linked()) }
        .expect("a slot is free");
    // SAFETY: the buffer outlives its completion, and the test reads it only
    // after it reaps the completion.
    unsafe {
        ring.push(Entry::read(
            file.as_fd(),
            &mut read,
            Position::from(0_u64),
            Key::from(3_u64),
        ))
    }
    .expect("a slot is free");
    ring.submit(Count::from(3_u32))
        .expect("the ring takes the batch");
    let done = completions(&mut ring);
    let keys: Vec<Key> = done.iter().map(|completion| completion.key).collect();
    assert_eq!(
        keys,
        vec![Key::from(1_u64), Key::from(2_u64), Key::from(3_u64)],
        "the links set the order"
    );
    let moved: Vec<u32> = done
        .iter()
        .map(|completion| completion.outcome.map_or(u32::MAX, u32::from))
        .collect();
    assert_eq!(
        moved,
        vec![4_096_u32, 0_u32, 4_096_u32],
        "each operation moves its bytes"
    );
    assert_eq!(
        read, written,
        "the read returns what the linked write wrote"
    );
}

/// A write that fails cancels the sync linked to it: the sync does not run.
#[test]
fn a_failed_write_cancels_its_linked_sync()
{
    let scratch = Scratch::new("cancel");
    drop(scratch.open());
    let readonly = File::open(&scratch.path).expect("the scratch file opens to read");
    let mut ring = Ring::new(Count::from(8_u32)).expect("the ring sets up");
    let written = Buffer::from(vec![0x5a_u8; BLOCK]);
    // SAFETY: the buffer outlives its completion, which the test reaps.
    unsafe {
        ring.push(
            Entry::write(
                readonly.as_fd(),
                &written,
                Position::from(0_u64),
                Key::from(11_u64),
            )
            .linked(),
        )
    }
    .expect("a slot is free");
    // SAFETY: a sync names no buffer.
    unsafe { ring.push(Entry::sync(readonly.as_fd(), Key::from(12_u64))) }.expect("a slot is free");
    ring.submit(Count::from(2_u32))
        .expect("the ring takes the batch");
    let done = completions(&mut ring);
    let outcomes: Vec<(Key, Option<u16>)> = done
        .iter()
        .map(|completion| (completion.key, completion.outcome.err().map(u16::from)))
        .collect();
    assert_eq!(
        outcomes,
        vec![
            (Key::from(11_u64), Some(9_u16)),
            (Key::from(12_u64), Some(125_u16))
        ],
        "the write fails with EBADF and its linked sync completes cancelled"
    );
}
