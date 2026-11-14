//! The `Io`: a buffer moves into each submission and comes back with its
//! completion, under the ring's form and under the blocking form alike.

use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::fs::OpenOptions;
use std::path::PathBuf;

use gandr_storage_io::Buffer;
use gandr_storage_io::Chain;
use gandr_storage_io::Count;
use gandr_storage_io::Done;
use gandr_storage_io::Errno;
use gandr_storage_io::Form;
use gandr_storage_io::Handle;
use gandr_storage_io::Io;
use gandr_storage_io::Moved;
use gandr_storage_io::Position;
use gandr_storage_io::Reason;
use gandr_storage_io::Segment;

/// The bytes of one block that the witnesses write and read.
const BLOCK: usize = 4_096;

/// The scratch files named so far in this process, so each name is fresh.
static NAMED: AtomicU64 = AtomicU64::new(0);

/// A fresh file for one witness, removed when the witness ends.
#[repr(transparent)]
struct Scratch
{
    /// The file's path.
    path: PathBuf,
}

impl Scratch
{
    /// A fresh scratch file, named by the process and a counter.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        let serial = NAMED.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("gandr-storage-io-{}-{serial}", std::process::id()));
        Self { path }
    }

    /// The file, open to read and to write.
    ///
    /// # Specification
    /// trivial.
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

    /// The bytes of the file.
    ///
    /// # Specification
    /// trivial.
    fn bytes(&self) -> Buffer
    {
        Buffer::from(std::fs::read(&self.path).expect("the scratch file reads"))
    }
}

impl Drop for Scratch
{
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let _removed = std::fs::remove_file(&self.path);
    }
}

/// An `Io` of each form at `depth`: the form that the kernel gives, then
/// the blocking form.
///
/// # Specification
/// trivial.
fn forms(depth: Count) -> [Io; 2]
{
    [
        Io::open(depth).expect("an io opens"),
        Io::blocking(depth).expect("the blocking form opens"),
    ]
}

/// Each completion of `io`, until it holds no submission.
///
/// # Specification
/// trivial.
fn completions(io: &mut Io) -> Vec<Done>
{
    core::iter::from_fn(|| io.wait().expect("the wait answers")).collect()
}

/// A write, a sync and a read, linked in that order, complete in that order
/// under each form. Each buffer comes back, and the read holds the bytes
/// that the write wrote.
#[test]
fn a_linked_write_sync_and_read_complete_in_order()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        let handle = Handle::from(scratch.open());
        let mut segment = Segment::new(handle.clone(), Position::from(0_u64));
        let written = vec![0xa5_u8; BLOCK];
        let append = io
            .append(&mut segment, Buffer::from(written.clone()), Chain::Linked)
            .expect("the append stages");
        let sync = io.sync(&segment, Chain::Linked).expect("the sync stages");
        let read = io
            .read_at(
                &handle,
                Position::from(0_u64),
                Buffer::from(vec![0_u8; BLOCK]),
                Chain::Alone,
            )
            .expect("the read stages");
        let form = io.form();
        let done = completions(&mut io);
        let keys: Vec<_> = done.iter().map(|each| each.pending).collect();
        assert_eq!(
            keys,
            vec![append, sync, read],
            "the links set the order under {form:?}"
        );
        let moved: Vec<u32> = done
            .iter()
            .map(|each| {
                each.outcome
                    .map(u32::from)
                    .expect("each operation succeeds")
            })
            .collect();
        assert_eq!(
            moved,
            vec![4_096_u32, 0_u32, 4_096_u32],
            "each operation moves its bytes under {form:?}"
        );
        let buffers: Vec<Option<Vec<u8>>> = done
            .into_iter()
            .map(|each| each.buffer.map(Vec::from))
            .collect();
        assert_eq!(
            buffers,
            vec![Some(written.clone()), None, Some(written)],
            "each buffer comes back, and the read holds the bytes written, under {form:?}"
        );
    }
}

/// A write that fails cancels the sync linked to it, under each form.
#[test]
fn a_failed_write_cancels_its_linked_sync()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        drop(scratch.open());
        let readonly =
            Handle::from(File::open(&scratch.path).expect("the scratch file opens to read"));
        let mut segment = Segment::new(readonly, Position::from(0_u64));
        let append = io
            .append(
                &mut segment,
                Buffer::from(vec![0x5a_u8; BLOCK]),
                Chain::Linked,
            )
            .expect("the append stages");
        let sync = io.sync(&segment, Chain::Alone).expect("the sync stages");
        let form = io.form();
        let outcomes: Vec<_> = completions(&mut io)
            .iter()
            .map(|each| (each.pending, each.outcome.err().map(u16::from)))
            .collect();
        assert_eq!(
            outcomes,
            vec![(append, Some(9_u16)), (sync, Some(125_u16))],
            "the write on a file open to read fails with EBADF, and its linked sync completes with ECANCELED, under {form:?}"
        );
    }
}

/// A cancel of a write that no form holds yet completes the write cancelled,
/// with its buffer, and then the cancel, under each form. The file stays
/// empty.
#[test]
fn a_cancel_before_submission_completes_the_target_cancelled()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        let mut segment = Segment::new(Handle::from(scratch.open()), Position::from(0_u64));
        let append = io
            .append(&mut segment, Buffer::from(vec![1_u8; BLOCK]), Chain::Alone)
            .expect("the append stages");
        let cancel = io.cancel(append).expect("the cancel stages");
        let form = io.form();
        let done = completions(&mut io);
        let outcomes: Vec<_> = done
            .iter()
            .map(|each| (each.pending, each.outcome))
            .collect();
        assert_eq!(
            outcomes,
            vec![
                (append, Err(Errno::CANCELLED)),
                (cancel, Ok(Moved::from(0_u32)))
            ],
            "two completions answer, the target's cancelled, under {form:?}"
        );
        let buffers: Vec<Option<Vec<u8>>> = done
            .into_iter()
            .map(|each| each.buffer.map(Vec::from))
            .collect();
        assert_eq!(
            buffers,
            vec![Some(vec![1_u8; BLOCK]), None],
            "the cancelled write gives its buffer back under {form:?}"
        );
        assert!(
            scratch.bytes() == Buffer::from(Vec::new()),
            "the cancelled write writes nothing under {form:?}"
        );
    }
}

/// A cancel of a write that has completed finds no entry, under each form.
#[test]
fn a_cancel_after_completion_finds_no_entry()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        let mut segment = Segment::new(Handle::from(scratch.open()), Position::from(0_u64));
        let append = io
            .append(&mut segment, Buffer::from(vec![2_u8; BLOCK]), Chain::Alone)
            .expect("the append stages");
        let first = io
            .wait()
            .expect("the wait answers")
            .expect("the append completes");
        assert_eq!(
            (first.pending, first.outcome),
            (append, Ok(Moved::from(4_096_u32)))
        );
        let cancel = io.cancel(append).expect("the cancel stages");
        let form = io.form();
        let outcomes: Vec<_> = completions(&mut io)
            .iter()
            .map(|each| (each.pending, each.outcome))
            .collect();
        assert_eq!(
            outcomes,
            vec![(cancel, Err(Errno::NO_ENTRY))],
            "the cancel finds no entry under {form:?}"
        );
    }
}

/// Two appends write at the start and past the first buffer, the end stands
/// past both, and the file holds both in order, under each form.
#[test]
fn an_append_owns_the_end_of_its_segment()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        let mut segment = Segment::new(Handle::from(scratch.open()), Position::from(0_u64));
        let first = io
            .append(&mut segment, Buffer::from(vec![1_u8; BLOCK]), Chain::Alone)
            .expect("the first append stages");
        let second = io
            .append(&mut segment, Buffer::from(vec![2_u8; BLOCK]), Chain::Alone)
            .expect("the second append stages");
        assert_eq!(
            segment.end(),
            Position::from(8_192_u64),
            "the end stands past both buffers"
        );
        let form = io.form();
        let done = completions(&mut io);
        let at = |pending| {
            done.iter()
                .find(|each| each.pending == pending)
                .map(|each| each.at)
        };
        assert_eq!(
            at(first),
            Some(Position::from(0_u64)),
            "the first append writes at the start under {form:?}"
        );
        assert_eq!(
            at(second),
            Some(Position::from(4_096_u64)),
            "the second writes past the first under {form:?}"
        );
        assert_eq!(
            scratch.bytes(),
            Buffer::from([vec![1_u8; BLOCK], vec![2_u8; BLOCK]].concat()),
            "the file holds both under {form:?}"
        );
    }
}

/// An `Io` of depth 2 parks each append past the depth until a write
/// completes, and takes the completions it parks for. With two completions
/// unread, the fifth append is refused with its buffer, and the end stays.
/// Once the caller reads, the fifth append stages, under each form.
#[test]
fn a_full_io_parks_and_gives_back_what_it_cannot_hold()
{
    for mut io in forms(Count::from(2_u32)) {
        let scratch = Scratch::new();
        let mut segment = Segment::new(Handle::from(scratch.open()), Position::from(0_u64));
        let form = io.form();
        let staged: Vec<_> = (1_u8 ..= 4_u8)
            .map(|fill| {
                io.append(&mut segment, Buffer::from(vec![fill; BLOCK]), Chain::Alone)
                    .expect("a full io parks and stages the append")
            })
            .collect();
        let refused = io
            .append(&mut segment, Buffer::from(vec![5_u8; BLOCK]), Chain::Alone)
            .expect_err("two unread completions refuse the fifth append");
        assert_eq!(
            refused.reason,
            Reason::Unread,
            "the refusal names the unread completions under {form:?}"
        );
        assert_eq!(
            refused.buffer.map(Vec::from),
            Some(vec![5_u8; BLOCK]),
            "the refusal gives the buffer back under {form:?}"
        );
        let four_blocks = Position::from(0x4000_u64);
        assert_eq!(
            segment.end(),
            four_blocks,
            "a refused append leaves the end under {form:?}"
        );
        let done = completions(&mut io);
        assert_eq!(
            done.len(),
            4,
            "each staged append completes once under {form:?}"
        );
        for pending in &staged {
            assert!(
                done.iter().any(|each| each.pending == *pending
                    && each.outcome == Ok(Moved::from(4_096_u32))
                    && each.buffer.is_some()),
                "each append completes with its buffer under {form:?}"
            );
        }
        let fifth = io
            .append(&mut segment, Buffer::from(vec![5_u8; BLOCK]), Chain::Alone)
            .expect("the fifth append stages once the caller reads");
        let last: Vec<_> = completions(&mut io)
            .iter()
            .map(|each| (each.pending, each.at))
            .collect();
        assert_eq!(
            last,
            vec![(fifth, four_blocks)],
            "the fifth append writes at the end under {form:?}"
        );
    }
}

/// An `Io` that drops with a submitted write in flight waits for it, so the
/// write lands in its file, under each form.
#[test]
fn dropping_an_io_completes_its_submitted_writes()
{
    for mut io in forms(Count::from(8_u32)) {
        let scratch = Scratch::new();
        let mut segment = Segment::new(Handle::from(scratch.open()), Position::from(0_u64));
        let form = io.form();
        let _append = io
            .append(&mut segment, Buffer::from(vec![7_u8; BLOCK]), Chain::Alone)
            .expect("the append stages");
        io.submit().expect("the append submits");
        drop(io);
        assert_eq!(
            scratch.bytes(),
            Buffer::from(vec![7_u8; BLOCK]),
            "the submitted write lands under {form:?}"
        );
    }
}

/// A refusal of permission, a kernel with no `io_uring_setup` and a ring
/// without stable submissions each leave the blocking form; any other
/// refusal is an error. A depth of zero opens no `Io`.
#[test]
fn the_blocking_form_follows_a_refusal_of_the_ring()
{
    assert_eq!(Form::after(Errno::PERMISSION), Ok(Form::Blocking));
    assert_eq!(Form::after(Errno::NO_SYSTEM_CALL), Ok(Form::Blocking));
    assert_eq!(Form::after(Errno::NOT_SUPPORTED), Ok(Form::Blocking));
    assert_eq!(Form::after(Errno::INVALID), Err(Errno::INVALID));
    assert_eq!(
        Io::blocking(Count::from(4_u32)).map(|io| io.form()).ok(),
        Some(Form::Blocking)
    );
    assert_eq!(Io::open(Count::from(0_u32)).err(), Some(Errno::INVALID));
}
