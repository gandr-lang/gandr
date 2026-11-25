//! The file operations against each subject: a whole file read in steps of
//! one page, each source of the corpus, a file of no bytes, a read into an
//! empty place, a path with no file, and a closed descriptor. The host's `std`
//! is the oracle of the bytes of a file.

use core::num::NonZeroU16;

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_io::ErrorNumber;
use gandr_boot_io::Operation;
use gandr_boot_io::Refused;

use crate::harness::PAGE;
use crate::harness::Path;
use crate::harness::SUBJECTS;
use crate::harness::Text;
use crate::harness::Whole;
use crate::harness::opened;
use crate::harness::read_whole;
use crate::harness::started;

/// The error number of a path with no file.
const ENOENT: ErrorNumber = ErrorNumber(NonZeroU16::new(2).expect("2 is not zero"));

/// The error number of a descriptor that the process does not hold.
const EBADF: ErrorNumber = ErrorNumber(NonZeroU16::new(9).expect("9 is not zero"));

/// The operation and the error number of `refused`.
///
/// # Specification
/// trivial.
fn named(refused: Refused) -> (Operation, ErrorNumber)
{
    (refused.operation(), refused.number())
}

/// Each `.gandr` file below `corpus`, in the order of the paths.
///
/// # Specification
/// trivial.
fn sources_below(corpus: &std::path::Path) -> Vec<std::path::PathBuf>
{
    let mut sources = Vec::new();
    let mut directories = vec![corpus.to_path_buf()];
    while let Some(directory) = directories.pop() {
        let entries = std::fs::read_dir(&directory)
            .unwrap_or_else(|error| panic!("{}: {error}", directory.display()));
        for entry in entries {
            let path = entry.expect("the host lists the corpus").path();
            if path.is_dir() {
                directories.push(path);
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                sources.push(path);
            }
        }
    }
    sources.sort();
    sources
}

/// A file of the tree reads whole in steps of one page: the bytes equal the
/// bytes that the host reads, the file takes more than one step, and the last
/// read gives the count 0. The handle then closes the file and stops.
#[test]
fn a_file_of_the_tree_reads_whole_in_steps_of_one_page()
{
    let text = concat!(env!("CARGO_MANIFEST_DIR"), "/src/lib.rs");
    let expected = std::fs::read(text).expect("the host reads the source of the crate");
    let path = Path::new(Text(text));
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        let descriptor = opened(subject, &io, &path);
        let mut whole = Vec::with_capacity(expected.len());
        let mut page = [0_u8; PAGE];
        let mut steps = 0_usize;
        loop {
            // SAFETY: the place is a live array, and nothing else reads it
            // during the call.
            let count =
                unsafe { (subject.read)(&io, descriptor, Place::from(page.as_mut_slice())) }
                    .unwrap_or_else(|refused| panic!("{name}: read: {refused}"));
            let Some(bytes) = page.get(.. count.0)
            else {
                panic!("{name}: a count of {} past the page", count.0);
            };
            if bytes.is_empty() {
                break;
            }
            whole.extend_from_slice(bytes);
            steps = steps.saturating_add(1);
        }
        assert_eq!(expected, whole, "{name}: the bytes of the file");
        assert!(steps > 1, "{name}: the file takes more than one step");
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// Each source of the corpus reads whole through each subject, in steps of
/// one page, and its bytes equal the bytes that the host reads. One handle of
/// a subject opens, reads and closes each source.
#[test]
fn each_source_of_the_corpus_reads_equal_through_each_subject()
{
    let corpus = std::path::Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../../corpus"));
    let sources = sources_below(corpus);
    assert!(sources.len() > 10, "the corpus has its sources");
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        for source in &sources {
            let expected = std::fs::read(source).expect("the host reads each source of the corpus");
            let text = source.to_str().expect("the path of a source is UTF-8");
            let descriptor = opened(subject, &io, &Path::new(Text(text)));
            let Whole(whole) = read_whole(subject, &io, descriptor);
            assert!(
                expected == whole,
                "{name}: the bytes of {}",
                source.display()
            );
            assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        }
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A file of no bytes gives the count 0 at the first read.
#[test]
fn a_file_of_no_bytes_gives_the_count_zero_at_the_first_read()
{
    let text = concat!(env!("CARGO_TARGET_TMPDIR"), "/boot-io-no-bytes");
    std::fs::write(text, []).expect("the host writes a file of no bytes");
    let path = Path::new(Text(text));
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        let descriptor = opened(subject, &io, &path);
        let mut page = [7_u8; PAGE];
        // SAFETY: the place is a live array, and nothing else reads it during
        // the call.
        let count = unsafe { (subject.read)(&io, descriptor, Place::from(page.as_mut_slice())) };
        assert_eq!(Ok(Length(0)), count, "{name}: the first read");
        assert!(
            page.iter().all(|&byte| byte == 7),
            "{name}: no byte written"
        );
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A read into an empty place gives the count 0 and takes no byte of the
/// file: the next reads give the whole file. After the close, a read into an
/// empty place is refused under the name `read` with `EBADF`, so the call
/// reaches the kernel also for an empty place.
#[test]
fn a_read_into_an_empty_place_gives_zero_and_takes_no_byte()
{
    let text = concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml");
    let expected = std::fs::read(text).expect("the host reads the manifest of the crate");
    let path = Path::new(Text(text));
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        let descriptor = opened(subject, &io, &path);
        let mut empty: [u8; 0] = [];
        // SAFETY: the place is empty, so the kernel writes no byte of it.
        let count = unsafe { (subject.read)(&io, descriptor, Place::from(empty.as_mut_slice())) };
        assert_eq!(Ok(Length(0)), count, "{name}: the read into an empty place");
        let Whole(whole) = read_whole(subject, &io, descriptor);
        assert_eq!(expected, whole, "{name}: the bytes after the empty read");
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        // SAFETY: the place is empty, so the kernel writes no byte of it.
        let closed = unsafe { (subject.read)(&io, descriptor, Place::from(empty.as_mut_slice())) };
        assert_eq!(
            Err((Operation::Read, EBADF)),
            closed.map_err(named),
            "{name}: the read of a closed descriptor into an empty place"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A path with no file is refused under the name `open`, with the error
/// number `ENOENT` of the kernel.
#[test]
fn a_path_with_no_file_is_refused_with_the_error_number_of_the_kernel()
{
    let text = concat!(env!("CARGO_TARGET_TMPDIR"), "/boot-io-no-such-file");
    let _absent = std::fs::remove_file(text);
    let path = Path::new(Text(text));
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        // SAFETY: the path is a live vector with a zero byte after its range,
        // and no byte of the text is zero.
        let opened = unsafe { (subject.open)(&io, path.range()) };
        assert_eq!(
            Err((Operation::Open, ENOENT)),
            opened.map_err(named),
            "{name}: open"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}

/// A descriptor closes one time. A read of it after the close is refused
/// under the name `read`, and a second close under the name `close`, each
/// with the error number `EBADF`.
#[test]
fn a_closed_descriptor_is_refused_with_ebadf()
{
    let path = Path::new(Text(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml")));
    for subject in &SUBJECTS {
        let name = subject.name;
        let io = started(subject);
        let descriptor = opened(subject, &io, &path);
        assert_eq!(Ok(()), (subject.close)(&io, descriptor), "{name}: close");
        let mut page = [0_u8; PAGE];
        // SAFETY: the place is a live array, and nothing else reads it during
        // the call.
        let read = unsafe { (subject.read)(&io, descriptor, Place::from(page.as_mut_slice())) };
        assert_eq!(
            Err((Operation::Read, EBADF)),
            read.map_err(named),
            "{name}: read"
        );
        assert_eq!(
            Err((Operation::Close, EBADF)),
            (subject.close)(&io, descriptor).map_err(named),
            "{name}: second close"
        );
        assert_eq!(Ok(()), (subject.stop)(io), "{name}: stop");
    }
}
