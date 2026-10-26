//! The console a run writes to: where the lines `Console.print` performs go.
//!
//! The host at a program's entry hands each line to a [`Console`]: the driver's
//! writes it to standard output, and [`Captured`] keeps it, so a test or a
//! corpus expectation reads what the program printed. Both are models of the
//! one `Console` interface, and a program runs unchanged under either.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::host::CONSOLE;
use gandr_kernel_term::Literal;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;

/// The operation of [`CONSOLE`] that writes a line.
const PRINT: &str = "print";

/// Whether a console wrote a line.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Printed
{
    /// The line was written.
    Written,
    /// The console could not write it.
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

/// Where a run's printed lines go.
pub trait Console
{
    /// Write `line` as one line.
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
}

/// A console keeping every line it is handed, in order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Captured
{
    /// The lines written, the first first.
    lines: Vec<String>,
}

impl Captured
{
    /// The lines written, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lines(&self) -> &[String]
    {
        &self.lines
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
}

/// Serve the `Console.print` `request` offers on `console`: the reply the
/// host gives, or nothing when the request is another operation.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `Console.print` with a string payload, the line handed to
///   `console` and the unit allocated as the reply; a decline when the payload
///   is no string, the console failed, or the store refused the reply; nothing
///   for any other operation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Console::print`].
/// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
#[spec(
    captures: [printing = request.signature.name().as_ref() == CONSOLE && request.operation.as_ref() == PRINT],
    ensures: |ret| ret.is_none() || printing,
)]
pub(super) fn served<Abort>(
    console: &mut dyn Console,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    if request.signature.name().as_ref() != CONSOLE || request.operation.as_ref() != PRINT {
        return None;
    }
    let Some(&HeapValue::Literal(Literal::Text(ref text))) = values.value(request.payload)
    else {
        return Some(HostReply::Decline);
    };
    if console.print(Line::from(text.as_ref())) == Printed::Failed {
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

/// The host of a run that only prints: `Console.print` writes to its
/// console, and every other operation is declined.
#[repr(transparent)]
pub(super) struct PrintingHost<'console>
{
    /// Where the run's printed lines go.
    console: &'console mut dyn Console,
}

impl<'console> PrintingHost<'console>
{
    /// The host writing to `console`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(console: &'console mut dyn Console) -> Self
    {
        Self { console }
    }
}

impl HostHandler for PrintingHost<'_>
{
    type Abort = Infallible;

    /// Write a `Console.print` line to the console and resume with the unit;
    /// decline every other operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        served(self.console, request, values).unwrap_or(HostReply::Decline)
    }
}
