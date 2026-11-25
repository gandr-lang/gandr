//! The one harness: each test runs its cases against each subject of
//! [`SUBJECTS`]. The crate is the one subject. Its twin in gandr joins as a
//! second subject, so each case states one answer for both.

use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_core::Range;
use gandr_boot_io::Descriptor;
use gandr_boot_io::Io;
use gandr_boot_io::Refused;

/// The operations of one subject, each with the signature of the crate's
/// function.
///
/// # Specification
/// trivial.
pub struct Subject
{
    /// The subject's name, which each failed case states.
    pub name: &'static str,
    /// The start of the IO core.
    pub start: fn() -> Result<Io, Refused>,
    /// The open of a file to read it.
    pub open: unsafe fn(&Io, Range) -> Result<Descriptor, Refused>,
    /// The read of the next bytes of a file.
    pub read: unsafe fn(&Io, Descriptor, Place) -> Result<Length, Refused>,
    /// The close of a descriptor.
    pub close: fn(&Io, Descriptor) -> Result<(), Refused>,
    /// The stop of the IO core.
    pub stop: fn(Io) -> Result<(), Refused>,
}

/// The subjects that each test runs against.
pub const SUBJECTS: [Subject; 1] = [Subject {
    name: "gandr-boot-io",
    start: gandr_boot_io::start,
    open: gandr_boot_io::open,
    read: gandr_boot_io::read,
    close: gandr_boot_io::close,
    stop: gandr_boot_io::stop,
}];

/// The bytes of one page, the step of a read.
pub const PAGE: usize = 4096;

/// The text of a path, with no zero byte.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Text<'text>(pub &'text str);

/// A path: its bytes, then one zero byte.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Path(Vec<u8>);

/// The bytes of a whole file, as a subject reads them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Whole(pub Vec<u8>);

impl Path
{
    /// The path of `text`, with a zero byte after it.
    ///
    /// # Specification
    /// trivial.
    pub fn new(text: Text<'_>) -> Self
    {
        let Text(text) = text;
        let mut bytes = Vec::with_capacity(text.len().saturating_add(1));
        bytes.extend_from_slice(text.as_bytes());
        bytes.push(0);
        Self(bytes)
    }

    /// The range of the path, without its zero byte.
    ///
    /// # Specification
    /// trivial.
    pub fn range(&self) -> Range
    {
        Range {
            base: self.0.as_ptr(),
            length: Length(self.0.len().saturating_sub(1)),
        }
    }
}

/// A started handle of `subject`.
///
/// # Specification
/// trivial.
pub fn started(subject: &Subject) -> Io
{
    (subject.start)().unwrap_or_else(|refused| panic!("{}: start: {refused}", subject.name))
}

/// The descriptor of the file at `path`, opened by `subject`.
///
/// # Specification
/// trivial.
pub fn opened(
    subject: &Subject,
    io: &Io,
    path: &Path,
) -> Descriptor
{
    // SAFETY: the path is a live vector with a zero byte after its range, and
    // no byte of the text is zero.
    unsafe { (subject.open)(io, path.range()) }
        .unwrap_or_else(|refused| panic!("{}: open: {refused}", subject.name))
}

/// The bytes of the file of `descriptor`, read by `subject` in steps of one
/// page up to the count 0.
///
/// # Specification
/// trivial.
pub fn read_whole(
    subject: &Subject,
    io: &Io,
    descriptor: Descriptor,
) -> Whole
{
    let name = subject.name;
    let mut whole = Vec::new();
    let mut page = [0_u8; PAGE];
    loop {
        // SAFETY: the place is a live array, and nothing else reads it during
        // the call.
        let count = unsafe { (subject.read)(io, descriptor, Place::from(page.as_mut_slice())) }
            .unwrap_or_else(|refused| panic!("{name}: read: {refused}"));
        let Some(bytes) = page.get(.. count.0)
        else {
            panic!("{name}: a count of {} past the page", count.0);
        };
        if bytes.is_empty() {
            return Whole(whole);
        }
        whole.extend_from_slice(bytes);
    }
}
