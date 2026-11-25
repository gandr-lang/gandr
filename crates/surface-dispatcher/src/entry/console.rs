//! The console of a run: where the lines that `Console.print` and
//! `Stderr.eprint` perform go, and where `Stdin.read_line` reads.
//!
//! A [`Console`] takes each line that a run prints and gives each line that it
//! reads. A run takes its console as [`Streams`], the closed set of the known
//! consoles, so the run stage has one instance and each operation is one match.
//! [`Streams::Standard`] writes to standard output or standard error and reads
//! standard input. On Linux x86-64 it writes each line by the system call of
//! the IO core of the bootstrap, `gandr-boot-io`, and reads through `std`.
//! [`Captured`] keeps the lines and answers from the input that it gets, so a
//! test or a corpus expectation reads what the program printed. [`Closed`]
//! fails each operation, as a stream whose reader is gone does. The run stage
//! serves the three streams on a console (`evaluate::console`). The script
//! and the session give the console to a run, so these types stay below the
//! run stage.

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
}

/// A console keeping every line it is handed, in order, each stream apart,
/// and answering reads from the input it was fed.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Captured
{
    /// The lines written to standard output, the first first.
    lines: Vec<String>,
    /// The lines written to standard error, the first first.
    errors: Vec<String>,
    /// The input not yet read, the next first.
    input: VecDeque<String>,
}

impl Captured
{
    /// A console reading `input`, each line with its newline, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn fed(input: Vec<String>) -> Self
    {
        Self {
            lines: Vec::new(),
            errors: Vec::new(),
            input: VecDeque::from(input),
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

    /// Drop every line written, keeping the input and the room the lines
    /// took: what lets one console serve the runs of a distribution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn clear(&mut self)
    {
        self.lines.clear();
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

    /// The next line fed, or the empty string once they are spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read_line(&mut self) -> Input
    {
        Input::Line(self.input.pop_front().unwrap_or_default())
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
}

/// The console a host hands a run, one of the known set. The run stage has
/// one instance for the set, and each operation is one match.
#[derive(Debug, Eq, PartialEq)]
pub enum Streams<'console>
{
    /// The process's standard output, standard error and standard input. Each
    /// operation takes its stream's lock of `std`, which the thread can hold
    /// already, so the run's lines join the host's own in order. On Linux
    /// x86-64 a line goes to its descriptor through `gandr-boot-io`, after
    /// the buffer of `std`'s standard output is written out.
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

/// Standard output, as the IO core of the bootstrap names it.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const STANDARD_OUTPUT: gandr_boot_io::Descriptor = gandr_boot_io::Descriptor(1);

/// Standard error, as the IO core of the bootstrap names it.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const STANDARD_ERROR: gandr_boot_io::Descriptor = gandr_boot_io::Descriptor(2);

/// The error number of a call that a signal interrupts, `EINTR`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const INTERRUPTED: u16 = 4;

/// The error number of a descriptor that the process does not hold, `EBADF`.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const NOT_HELD: u16 = 9;

/// The bytes of a line and its newline that one system call writes. A pipe
/// takes a write of at most this count as one piece, so the line of a short
/// write does not mix with the lines of another process.
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const PAGE: usize = 4096;

/// Gives each byte of `bytes` to `descriptor` by the system call of the IO
/// core of the bootstrap. A short write gives the rest in the next call, and
/// an interrupted call is made again, as `std`'s `write_all` does.
///
/// # Specification
/// - ensures: [`Printed::Written`] once the kernel took each byte, or when the
///   process does not hold the descriptor, as `std` takes a write to a closed
///   standard stream. [`Printed::Failed`] for each other refusal, and for a
///   call that takes no byte of a range that is not empty.
/// - panics: none.
/// - executable: none — the kernel takes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — a line reaches a socket with its newline, a line longer
///   than a page reaches it whole, a closed descriptor takes the line, a socket
///   whose reader is gone fails it, and signals while the line waits leave it
///   whole.
/// - witness: `tests::console::a_line_reaches_its_descriptor_with_its_newline`
/// - witness: `tests::console::a_line_longer_than_a_page_reaches_its_descriptor_whole`
/// - witness: `tests::console::a_line_to_a_closed_descriptor_is_written_as_std_writes_it`
/// - witness: `tests::console::a_line_whose_reader_is_gone_fails`
/// - witness: `tests::console::signals_while_a_line_waits_leave_the_line_whole`
///
/// # Cost
/// - allocation: none
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn whole(
    descriptor: gandr_boot_io::Descriptor,
    bytes: &[u8],
) -> Printed
{
    let Ok(io) = gandr_boot_io::start()
    else {
        return Printed::Failed;
    };
    let mut rest = bytes;
    let printed = loop {
        if rest.is_empty() {
            break Printed::Written;
        }
        // SAFETY: `rest` is a live slice of the caller, and nothing writes it
        // during the call.
        let wrote =
            unsafe { gandr_boot_io::write(&io, descriptor, gandr_boot_core::Range::from(rest)) };
        match wrote {
            Ok(gandr_boot_core::Length(0)) => break Printed::Failed,
            Ok(gandr_boot_core::Length(count)) => rest = rest.get(count ..).unwrap_or_default(),
            Err(refused) => match refused.number().0.get() {
                INTERRUPTED => {},
                NOT_HELD => break Printed::Written,
                _ => break Printed::Failed,
            },
        }
    };
    match gandr_boot_io::stop(io) {
        Ok(()) => printed,
        Err(_) => Printed::Failed,
    }
}

/// Writes `line` and a newline to `descriptor` through `gandr-boot-io`.
///
/// A line below one page goes with its newline in one call; a longer line
/// goes in one call and its newline in a second.
///
/// # Specification
/// - ensures: [`Printed::Written`] once the descriptor took the line and its
///   newline, or when the process does not hold the descriptor;
///   [`Printed::Failed`] when the kernel refused a byte of them.
/// - panics: none.
/// - executable: none — the kernel takes the bytes.
///
/// # Adequacy
/// - hypothesis: L3 — a line reaches a socket with its newline, a line longer
///   than a page reaches it whole, a closed descriptor takes the line, a socket
///   whose reader is gone fails it, and signals while the line waits leave it
///   whole.
/// - witness: `tests::console::a_line_reaches_its_descriptor_with_its_newline`
/// - witness: `tests::console::a_line_longer_than_a_page_reaches_its_descriptor_whole`
/// - witness: `tests::console::a_line_to_a_closed_descriptor_is_written_as_std_writes_it`
/// - witness: `tests::console::a_line_whose_reader_is_gone_fails`
/// - witness: `tests::console::signals_while_a_line_waits_leave_the_line_whole`
///
/// # Cost
/// - allocation: none; the line and its newline join in one page on the stack
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[inline]
#[must_use]
pub fn line_to(
    descriptor: gandr_boot_io::Descriptor,
    line: Line<'_>,
) -> Printed
{
    let text = line.as_ref().as_bytes();
    let mut page = [0_u8; PAGE];
    let Some((body, end)) = page
        .get_mut(..= text.len())
        .and_then(|piece| piece.split_at_mut_checked(text.len()))
    else {
        return match whole(descriptor, text) {
            Printed::Written => whole(descriptor, b"\n"),
            Printed::Failed => Printed::Failed,
        };
    };
    body.copy_from_slice(text);
    end.fill(b'\n');
    whole(descriptor, page.get(..= text.len()).unwrap_or_default())
}

/// Writes `line` and a newline to standard output by the IO core of the
/// bootstrap. The thread holds the lock of `std`'s standard output, with its
/// buffer written out, so the line joins the host's own lines in order.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: none
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn standard_output(line: Line<'_>) -> Printed
{
    let mut held = std::io::stdout().lock();
    let printed = match held.flush() {
        Ok(()) => line_to(STANDARD_OUTPUT, line),
        Err(_) => Printed::Failed,
    };
    drop(held);
    printed
}

/// Writes `line` and a newline to standard error by the IO core of the
/// bootstrap. The thread holds the lock of `std`'s standard error, so the line
/// joins the host's own lines in order.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: none
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn standard_error(line: Line<'_>) -> Printed
{
    let held = std::io::stderr().lock();
    let printed = line_to(STANDARD_ERROR, line);
    drop(held);
    printed
}

/// Whether a write of a line to a standard stream came to the whole line.
///
/// # Specification
/// trivial.
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
const fn written(result: &std::io::Result<()>) -> Printed
{
    match *result {
        Ok(()) => Printed::Written,
        Err(_) => Printed::Failed,
    }
}

/// Writes `line` and a newline to standard output through `std`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the I/O error's payload, error path
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
fn standard_output(line: Line<'_>) -> Printed
{
    written(&writeln!(std::io::stdout().lock(), "{}", line.as_ref()))
}

/// Writes `line` and a newline to standard error through `std`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the I/O error's payload, error path
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
fn standard_error(line: Line<'_>) -> Printed
{
    written(&writeln!(std::io::stderr().lock(), "{}", line.as_ref()))
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
    /// - allocation: none on Linux x86-64; elsewhere the I/O error's payload,
    ///   error path
    #[inline]
    fn print(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        match *self {
            Self::Standard => standard_output(line),
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
    /// - allocation: none on Linux x86-64; elsewhere the I/O error's payload,
    ///   error path
    #[inline]
    fn eprint(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        match *self {
            Self::Standard => standard_error(line),
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
}
