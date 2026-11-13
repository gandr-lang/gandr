//! The console of a run: where the lines that `Console.print` and
//! `Stderr.eprint` perform go, and where `Stdin.read_line` reads.
//!
//! A [`Console`] takes each line that a run prints and gives each line that it
//! reads. The driver's console writes to standard output or standard error and
//! reads standard input. [`Captured`] keeps the lines and answers from the
//! input that it gets, so a test or a corpus expectation reads what the program
//! printed. The run stage serves the three streams on a console
//! (`evaluate::console`). The script and the session give the console to a
//! run, so these types stay below the run stage.

use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec::Vec;

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
    /// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
    /// - witness: `evaluate::tests::a_printed_line_reaches_the_console_2279`
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
    /// - witness: `evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
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
    /// - witness: `evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
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
