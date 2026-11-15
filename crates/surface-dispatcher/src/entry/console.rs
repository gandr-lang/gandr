//! The console of a run: where the lines that `Console.print` and
//! `Stderr.eprint` perform go, and where `Stdin.read_line` reads.
//!
//! A [`Console`] takes each line that a run prints and gives each line that it
//! reads. A run takes its console as [`Streams`], the closed set of the known
//! consoles, so the run stage has one instance and each operation is one match.
//! [`Streams::Standard`] writes to standard output or standard error and reads
//! standard input. [`Captured`] keeps the lines and answers from the input that
//! it gets, so a test or a corpus expectation reads what the program printed.
//! [`Closed`] fails each operation, as a stream whose reader is gone does. The
//! run stage serves the three streams on a console (`evaluate::console`). The
//! script and the session give the console to a run, so these types stay below
//! the run stage.

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
}
