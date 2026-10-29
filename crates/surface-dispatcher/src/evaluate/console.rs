//! The console a run writes to and reads from: where the lines `Console.print`
//! and `Stderr.eprint` perform go, and where `Stdin.read_line` reads.
//!
//! The host at a program's entry hands each line to a [`Console`]: the driver's
//! writes it to standard output or standard error and reads standard input,
//! and [`Captured`] keeps the lines and answers from the input it was fed, so a
//! test or a corpus expectation reads what the program printed. Both are
//! models of the three stream interfaces, and a program runs unchanged under
//! either.

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::host::CONSOLE;
use gandr_core_term::effect::host::STDERR;
use gandr_core_term::effect::host::STDIN;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;

/// The operation of [`CONSOLE`] that writes a line.
const PRINT: &str = "print";

/// The operation of [`STDERR`] that writes a line.
const EPRINT: &str = "eprint";

/// The operation of [`STDIN`] that reads a line.
const READ_LINE: &str = "read_line";

/// The standard stream a host operation meets.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stream
{
    /// Standard output, `Console.print`.
    Out,
    /// Standard error, `Stderr.eprint`.
    Err,
    /// Standard input, `Stdin.read_line`.
    In,
}

/// The standard stream `request` meets, or none for any other operation.
///
/// # Specification
/// trivial.
fn stream(request: &HostRequest<'_>) -> Option<Stream>
{
    match (
        request.signature.name().as_ref(),
        request.operation.as_ref(),
    ) {
        (CONSOLE, PRINT) => Some(Stream::Out),
        (STDERR, EPRINT) => Some(Stream::Err),
        (STDIN, READ_LINE) => Some(Stream::In),
        _ => None,
    }
}

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

/// Serve the standard-stream `request` offers on `console`: the reply the host
/// gives, or nothing when the request is another operation.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `Console.print` and `Stderr.eprint` with a string payload,
///   the line handed to `console` on its stream and the unit allocated as the
///   reply; for `Stdin.read_line`, the line `console` reads allocated as the
///   reply. A decline when a written payload is no string, the console failed,
///   or the store refused the reply; nothing for any other operation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Console::print`], [`Console::eprint`] and
///   [`Console::read_line`].
/// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
/// - witness: `evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
#[spec(
    captures: [streaming = stream(&request).is_some()],
    ensures: |ret| ret.is_none() || streaming,
)]
pub(super) fn served<Abort, Printer>(
    console: &mut Printer,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
where
    Printer: Console + ?Sized,
{
    let met = stream(&request)?;
    if met == Stream::In {
        let Input::Line(line) = console.read_line()
        else {
            return Some(HostReply::Decline);
        };
        return Some(
            values
                .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(line))))
                .map_or(HostReply::Decline, HostReply::Resume),
        );
    }
    let Some(&HeapValue::Literal(Literal::Text(ref text))) = values.value(request.payload)
    else {
        return Some(HostReply::Decline);
    };
    let line = Line::from(text.as_ref());
    let written = if met == Stream::Err {
        console.eprint(line)
    }
    else {
        console.print(line)
    };
    if written == Printed::Failed {
        return Some(HostReply::Decline);
    }
    Some(
        values
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                fields: Box::new([]),
            })
            .map_or(HostReply::Decline, HostReply::Resume),
    )
}

/// The host of a run that only meets the standard streams: each of their
/// operations is served on its console, and every other one is declined. A
/// host over a console that crosses threads crosses them too, so a
/// concurrent run's reader may hold it.
#[repr(transparent)]
pub(super) struct PrintingHost<'console, Printer: ?Sized = dyn Console>
{
    /// Where the run's printed lines go.
    console: &'console mut Printer,
}

impl<'console, Printer> PrintingHost<'console, Printer>
where
    Printer: Console + ?Sized,
{
    /// The host writing to `console`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(console: &'console mut Printer) -> Self
    {
        Self { console }
    }
}

impl<Printer> HostHandler for PrintingHost<'_, Printer>
where
    Printer: Console + ?Sized,
{
    type Abort = Infallible;

    /// Serve a standard-stream operation on the console; decline every other
    /// operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        served(&mut *self.console, request, values).unwrap_or(HostReply::Decline)
    }
}
