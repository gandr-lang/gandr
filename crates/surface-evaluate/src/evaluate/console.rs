//! The standard streams of a run, served on its console: the lines that
//! `Console.print` and `Stderr.eprint` perform go to a [`Console`], and
//! `Stdin.read_line` reads from it.
//!
//! The host at a program's entry hands each line to the console. The console
//! and its models live in [`gandr_surface_dispatcher::Console`], below the run
//! stage. A program runs unchanged under each model.

use alloc::boxed::Box;
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
use gandr_runtime_emitter::TaskOrder;
use gandr_surface_dispatcher::Console;
use gandr_surface_dispatcher::Input;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::Printed;

use super::rand::Draws;
use super::rand::answered;

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
/// concurrent run's reader may hold it. Given the draws of the exact model,
/// it also answers each `Rand.draw` from them, and switches between ready
/// tasks in the order it is given.
pub(super) struct PrintingHost<'console, Printer: ?Sized = dyn Console>
{
    /// Where the run's printed lines go.
    console: &'console mut Printer,
    /// The answers of the exact model, when the run takes them.
    draws: Option<&'console mut Draws>,
    /// The order in which the run's ready tasks take their turns.
    order: TaskOrder,
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
        Self {
            console,
            draws: None,
            order: TaskOrder::Oldest,
        }
    }

    /// The host writing to `console`, answering each draw from `draws`, and
    /// switching between ready tasks in `order`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn drawing(
        console: &'console mut Printer,
        draws: &'console mut Draws,
        order: TaskOrder,
    ) -> Self
    {
        Self {
            console,
            draws: Some(draws),
            order,
        }
    }
}

impl<Printer> HostHandler for PrintingHost<'_, Printer>
where
    Printer: Console + ?Sized,
{
    type Abort = Infallible;

    /// Serve a standard-stream operation on the console, and a draw from the
    /// exact model's answers when the host holds them; decline every other
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
        if let Some(reply) = served(&mut *self.console, request, values) {
            return reply;
        }
        match self.draws {
            Some(ref mut draws) => {
                answered(&mut *self.console, draws, request, values).unwrap_or(HostReply::Decline)
            },
            None => HostReply::Decline,
        }
    }

    /// The order the host was given.
    ///
    /// # Specification
    /// trivial.
    fn task_order(&mut self) -> TaskOrder
    {
        self.order
    }
}
