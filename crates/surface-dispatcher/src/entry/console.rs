//! The console of a run: where the lines that `Console.print` and
//! `Stderr.eprint` perform go, where the bytes of `Console.write_bytes` go, and
//! where `Stdin.read_line` and `Stdin.read_bytes` read.
//!
//! A [`Console`] takes each line and each byte that a run writes and gives each
//! line and each byte that it reads. A run takes its console as [`Streams`],
//! the closed set of the known consoles, so the run stage has one instance and
//! each operation is one match. [`Streams::Standard`] writes to standard output
//! or standard error and reads standard input. [`Captured`] keeps the lines and
//! the bytes and answers from the input that it gets, so a test or a corpus
//! expectation reads what the program wrote. [`Closed`] fails each operation,
//! as a stream whose reader is gone does. The run stage serves the three
//! streams on a console (`evaluate::console`). The script and the session give
//! the console to a run, so these types stay below the run stage.
//!
//! A read of a line and a read of bytes read one input: each continues at the
//! byte after the last byte that the other read.

use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec::Vec;
use std::io::BufRead as _;
use std::io::Write as _;

/// Whether a console wrote a line.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Printed
{
    /// The line was written.
    Written,
    /// The console could not write it.
    Failed,
}

/// What reading a line of input came to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Input
{
    /// The next line, its newline kept; the empty string at the end of input.
    Line(String),
    /// The console could not read.
    Failed,
}

/// The number of an error of the host, as `errno` gives it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct ErrorNumber(i32);

impl ErrorNumber
{
    /// The error of a stream whose file is not open for the operation,
    /// `EBADF`.
    pub const NOT_OPEN: Self = Self(9);
    /// The error of a write to a pipe whose reader is gone, `EPIPE`.
    pub const NO_READER: Self = Self(32);
    /// The error of an input or an output that failed with no number of its
    /// own, `EIO`.
    pub const FAILED: Self = Self(5);

    /// The number of `error`, or [`Self::FAILED`] when it holds none.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    fn of(error: &std::io::Error) -> Self
    {
        error.raw_os_error().map_or(Self::FAILED, Self)
    }
}

impl From<ErrorNumber> for i32
{
    /// The number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: ErrorNumber) -> Self
    {
        number.0
    }
}

/// What one read of bytes of input came to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Bytes
{
    /// The bytes of one read, no more than the count asked; none at the end
    /// of input.
    Read(Vec<u8>),
    /// The console could not read, with the number of the error.
    Failed(ErrorNumber),
}

/// Whether a console wrote bytes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Wrote
{
    /// Each byte was written.
    Written,
    /// The console could not write them, with the number of the error.
    Failed(ErrorNumber),
}

/// A line a run prints, without its newline.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Line<'text>(&'text str);

impl<'text> From<&'text str> for Line<'text>
{
    /// The line `text` spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for Line<'_>
{
    /// The line's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// Where a run's printed lines go and where its input comes from.
pub trait Console
{
    /// Write `line` as one line to standard output.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Printed::Written`] once the line is written whole, as one
    ///   line; [`Printed::Failed`] when it could not be.
    /// - executable: none — the trait states the console's obligation; each
    ///   body is an implementor's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a program printing two lines leaves both in
    ///   [`Captured`], in order, and a console failing a line stops the run
    ///   there.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_entry_prints_through_its_console_2279`
    /// - witness: `gandr-surface-evaluate::evaluate::tests::a_printed_line_reaches_the_console_2279`
    fn print(
        &mut self,
        line: Line<'_>,
    ) -> Printed;

    /// Write `line` as one line to standard error.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Printed::Written`] once the line is written whole, as one
    ///   line, apart from the lines [`Self::print`] writes; [`Printed::Failed`]
    ///   when it could not be.
    /// - executable: none — the trait states the console's obligation; each
    ///   body is an implementor's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry writing to both streams leaves each line in
    ///   its own stream of [`Captured`], in order.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
    fn eprint(
        &mut self,
        line: Line<'_>,
    ) -> Printed;

    /// Read the next line of input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Input::Line`] with the next line and its newline, or the
    ///   empty string once the input is spent; [`Input::Failed`] when it could
    ///   not be read.
    /// - executable: none — the trait states the console's obligation; each
    ///   body is an implementor's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry reading two lines from [`Captured`] fed one
    ///   reads it and then the empty string.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
    fn read_line(&mut self) -> Input;

    /// Write each byte of `bytes` to standard output, in the output of
    /// [`Self::print`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Wrote::Written`] once each byte is written, with no newline
    ///   after them; [`Wrote::Failed`] with the number of the error when they
    ///   could not be.
    /// - executable: none — the trait states the console's obligation; each
    ///   body is an implementor's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry writing the bytes 0, 10 and 255 leaves them
    ///   in [`Captured`], in order.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_entry_reads_and_writes_bytes`
    fn write_bytes(
        &mut self,
        bytes: &[u8],
    ) -> Wrote;

    /// Make one read of at most `limit` bytes of input.
    ///
    /// # Specification
    /// - requires: `limit` is at least 1.
    /// - ensures: [`Bytes::Read`] with the next bytes of the input, at least
    ///   one and no more than `limit`, or none once the input is spent;
    ///   [`Bytes::Failed`] with the number of the error when it could not be
    ///   read.
    /// - executable: none — the trait states the console's obligation; each
    ///   body is an implementor's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an entry reading from [`Captured`] fed the bytes 0,
    ///   10 and 255 reads them in order, then none.
    /// - witness: `gandr-surface-evaluate::evaluate::entry::tests::an_entry_reads_and_writes_bytes`
    fn read_bytes(
        &mut self,
        limit: usize,
    ) -> Bytes;
}

/// A console keeping every line and every byte it is handed, in order, each
/// stream apart, and answering reads from the input it was fed.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Captured
{
    /// The lines written to standard output, the first first.
    lines: Vec<String>,
    /// The bytes written to standard output by `write_bytes`, the first first.
    written: Vec<u8>,
    /// The lines written to standard error, the first first.
    errors: Vec<String>,
    /// The input not yet read, the next byte first.
    input: VecDeque<u8>,
}

impl Captured
{
    /// A console reading the bytes of `input`, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn fed(input: &[u8]) -> Self
    {
        Self {
            lines: Vec::new(),
            written: Vec::new(),
            errors: Vec::new(),
            input: input.iter().copied().collect(),
        }
    }

    /// The lines written to standard output, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lines(&self) -> &[String]
    {
        &self.lines
    }

    /// The bytes written to standard output by `write_bytes`, the first
    /// first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn written(&self) -> &[u8]
    {
        &self.written
    }

    /// The lines written to standard error, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn errors(&self) -> &[String]
    {
        &self.errors
    }

    /// Drop every line and every byte written, keeping the input and the room
    /// they took: what lets one console serve the runs of a distribution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn clear(&mut self)
    {
        self.lines.clear();
        self.written.clear();
        self.errors.clear();
    }
}

impl Console for Captured
{
    /// Keep `line`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn print(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        self.lines.push(String::from(line.as_ref()));
        Printed::Written
    }

    /// Keep `line` as standard error's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eprint(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        self.errors.push(String::from(line.as_ref()));
        Printed::Written
    }

    /// The next line fed, its newline kept, or the empty string once the
    /// input is spent. A line that is not UTF-8 fails.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the line, growth within the line
    #[inline]
    fn read_line(&mut self) -> Input
    {
        let length = self
            .input
            .iter()
            .position(|&byte| byte == b'\n')
            .map_or(self.input.len(), |newline| newline.saturating_add(1));
        let line: Vec<u8> = self.input.drain(.. length).collect();
        String::from_utf8(line).map_or(Input::Failed, Input::Line)
    }

    /// Keep `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_bytes(
        &mut self,
        bytes: &[u8],
    ) -> Wrote
    {
        self.written.extend_from_slice(bytes);
        Wrote::Written
    }

    /// The next `limit` bytes fed, or fewer at the end of the input.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the bytes read, growth within the read
    #[inline]
    fn read_bytes(
        &mut self,
        limit: usize,
    ) -> Bytes
    {
        let length = limit.min(self.input.len());
        Bytes::Read(self.input.drain(.. length).collect())
    }
}

/// A count of the lines and the reads asked of a console.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Asked(usize);

impl From<Asked> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(asked: Asked) -> Self
    {
        asked.0
    }
}

/// A console whose streams are closed: each line it is handed fails, as on a
/// pipe whose reader is gone, and each read fails. It counts each line and
/// each read, so a test reads where the run stopped.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Closed
{
    /// The lines and the reads asked of it.
    asked: Asked,
}

impl Closed
{
    /// The lines and the reads asked of the console.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn asked(&self) -> Asked
    {
        self.asked
    }

    /// Count one line or one read more.
    ///
    /// # Specification
    /// trivial.
    const fn ask(&mut self)
    {
        self.asked = Asked(self.asked.0.saturating_add(1));
    }
}

impl Console for Closed
{
    /// Count the line and fail it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn print(
        &mut self,
        _line: Line<'_>,
    ) -> Printed
    {
        self.ask();
        Printed::Failed
    }

    /// Count the line and fail it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eprint(
        &mut self,
        _line: Line<'_>,
    ) -> Printed
    {
        self.ask();
        Printed::Failed
    }

    /// Count the read and fail it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read_line(&mut self) -> Input
    {
        self.ask();
        Input::Failed
    }

    /// Count the bytes and fail them, as on a pipe whose reader is gone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_bytes(
        &mut self,
        _bytes: &[u8],
    ) -> Wrote
    {
        self.ask();
        Wrote::Failed(ErrorNumber::NO_READER)
    }

    /// Count the read and fail it, as on an input that is not open.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read_bytes(
        &mut self,
        _limit: usize,
    ) -> Bytes
    {
        self.ask();
        Bytes::Failed(ErrorNumber::NOT_OPEN)
    }
}

/// The console a host hands a run, one of the known set. The run stage has
/// one instance for the set, and each operation is one match.
#[derive(Debug, Eq, PartialEq)]
pub enum Streams<'console>
{
    /// The process's standard output, standard error and standard input. Each
    /// operation takes its stream's lock, which the thread can hold already,
    /// so the run's lines join the host's own in order.
    Standard,
    /// The lines kept in memory and the input fed ([`Captured`]).
    Captured(&'console mut Captured),
    /// Streams that fail each line and each read ([`Closed`]).
    Closed(&'console mut Closed),
}

impl Streams<'_>
{
    /// The same console, borrowed for a shorter run: what lets a run hand its
    /// console to each step in turn.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reborrow(&mut self) -> Streams<'_>
    {
        match *self {
            Self::Standard => Streams::Standard,
            Self::Captured(ref mut captured) => Streams::Captured(captured),
            Self::Closed(ref mut closed) => Streams::Closed(closed),
        }
    }
}

/// Whether a write of a line to a standard stream came to the whole line.
///
/// # Specification
/// trivial.
const fn written(result: &std::io::Result<()>) -> Printed
{
    match *result {
        Ok(()) => Printed::Written,
        Err(_) => Printed::Failed,
    }
}

impl Console for Streams<'_>
{
    /// Write `line` and a newline to standard output, or hand it to the
    /// console held.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the I/O error's payload, error path
    #[inline]
    fn print(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        match *self {
            Self::Standard => written(&writeln!(std::io::stdout().lock(), "{}", line.as_ref())),
            Self::Captured(ref mut captured) => captured.print(line),
            Self::Closed(ref mut closed) => closed.print(line),
        }
    }

    /// Write `line` and a newline to standard error, or hand it to the
    /// console held.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the I/O error's payload, error path
    #[inline]
    fn eprint(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        match *self {
            Self::Standard => written(&writeln!(std::io::stderr().lock(), "{}", line.as_ref())),
            Self::Captured(ref mut captured) => captured.eprint(line),
            Self::Closed(ref mut closed) => closed.eprint(line),
        }
    }

    /// The next line of standard input, its newline kept, and the empty
    /// string at its end, or the console held's next line. A line of standard
    /// input that is not UTF-8 fails.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the line read from standard input, growth within the line
    #[inline]
    fn read_line(&mut self) -> Input
    {
        match *self {
            Self::Standard => {
                let mut line = String::new();
                let read = std::io::stdin().lock().read_line(&mut line);
                match read {
                    Ok(_) => Input::Line(line),
                    Err(_) => Input::Failed,
                }
            },
            Self::Captured(ref mut captured) => captured.read_line(),
            Self::Closed(ref mut closed) => closed.read_line(),
        }
    }

    /// Write `bytes` to standard output, or hand them to the console held.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the I/O error's payload, error path
    #[inline]
    fn write_bytes(
        &mut self,
        bytes: &[u8],
    ) -> Wrote
    {
        match *self {
            Self::Standard => match std::io::stdout().lock().write_all(bytes) {
                Ok(()) => Wrote::Written,
                Err(error) => Wrote::Failed(ErrorNumber::of(&error)),
            },
            Self::Captured(ref mut captured) => captured.write_bytes(bytes),
            Self::Closed(ref mut closed) => closed.write_bytes(bytes),
        }
    }

    /// One read of at most `limit` bytes of standard input, through the
    /// buffer that a read of a line reads too, or the console held's next
    /// bytes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the bytes read, growth within the read
    #[inline]
    fn read_bytes(
        &mut self,
        limit: usize,
    ) -> Bytes
    {
        match *self {
            Self::Standard => {
                let mut input = std::io::stdin().lock();
                let read = match input.fill_buf() {
                    Ok(buffered) => Bytes::Read(
                        buffered
                            .get(.. limit.min(buffered.len()))
                            .map_or_else(Vec::new, <[u8]>::to_vec),
                    ),
                    Err(error) => Bytes::Failed(ErrorNumber::of(&error)),
                };
                if let Bytes::Read(ref bytes) = read {
                    input.consume(bytes.len());
                }
                drop(input);
                read
            },
            Self::Captured(ref mut captured) => captured.read_bytes(limit),
            Self::Closed(ref mut closed) => closed.read_bytes(limit),
        }
    }
}
