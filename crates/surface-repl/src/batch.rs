//! The batch face: lines from any reader, a plain transcript to any writer.

use core::fmt;
use std::io;
use std::io::BufRead;
use std::io::Write;

use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_grammar::PbgError;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use rustyline::error::ReadlineError;

use crate::session_loop::LoopError;
use crate::session_loop::LoopEvent;
use crate::session_loop::SessionLoop;

/// What stopped a face before its input ended.
#[derive(Debug)]
pub enum Fault
{
    /// The built-in grammar or its role table did not build.
    Grammar(PbgError),
    /// The input could not be read.
    Input(io::Error),
    /// The line editor failed.
    Editor(ReadlineError),
    /// The session faulted on a revision.
    Session(LoopError),
}

impl fmt::Display for Fault
{
    /// Writes what stopped the face.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Grammar(ref error) => write!(f, "the built-in grammar did not build: {error}"),
            | Self::Input(ref error) => write!(f, "cannot read the input: {error}"),
            | Self::Editor(ref error) => write!(f, "the line editor failed: {error}"),
            | Self::Session(ref error) => write!(f, "{error}"),
        }
    }
}

impl core::error::Error for Fault
{
}

/// How a face's run ended.
#[derive(Debug)]
pub enum Ended
{
    /// The input ended, or the user asked to leave.
    Completed,
    /// A fault stopped the run.
    Faulted(Fault),
}

/// The mark a transcript line opens with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Mark(&'static str);

/// Text written under one mark: an echo or a result line, which may hold
/// several lines.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Marked<'text>(&'text str);

/// The mark a line of `kind` opens with in the plain transcript.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `▸ ` for the echo, `= ` for a value, `? ` for a goal, `· ` for a
///   note or a stuck evaluation, `! ` for blame; nothing for a type line, which
///   spells its own `name : T`, nor for a diagnostic, which opens with its own
///   severity.
/// - provides: the plain face's kind marks, so a transcript without colour
///   still tells its lines apart.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a piped session's transcript is asserted line by line.
/// - witness: `loop::tests::piped_value_prints_a_transcript`
const fn mark(kind: OutKind) -> Mark
{
    Mark(match kind {
        | OutKind::Source => "▸ ",
        | OutKind::Value => "= ",
        | OutKind::Goal => "? ",
        | OutKind::Stuck | OutKind::Info => "· ",
        | OutKind::Blame => "! ",
        | OutKind::Type | OutKind::Diag => "",
    })
}

/// Write `text` under `mark`: the first line after the mark, every later line
/// indented to the mark's width.
///
/// # Specification
/// trivial.
fn write_marked<Output>(
    output: &mut Output,
    Mark(mark): Mark,
    Marked(text): Marked<'_>,
) -> io::Result<()>
where
    Output: Write,
{
    let indent = " ".repeat(mark.chars().count());
    for (index, line) in text.lines().enumerate() {
        match (index, line.is_empty()) {
            | (0, _) => writeln!(output, "{mark}{line}")?,
            | (_, true) => writeln!(output)?,
            | (_, false) => writeln!(output, "{indent}{line}")?,
        }
    }
    Ok(())
}

/// Write `block` as plain text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the echo, then each line in order, each under its kind's mark, a
///   line holding several lines indented to its mark's width after the first;
///   no colour, so the transcript is the same on every terminal.
/// - provides: the plain transcript every face prints.
/// - fails: the writer's error.
/// - panics: none.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — a piped session's transcript is asserted line by line.
/// - witness: `loop::tests::piped_value_prints_a_transcript`
#[inline]
pub fn write_block<Output>(
    output: &mut Output,
    block: &TranscriptBlock,
) -> io::Result<()>
where
    Output: Write,
{
    write_marked(output, mark(OutKind::Source), Marked(&block.source))?;
    for &(kind, ref line) in &block.lines {
        write_marked(output, mark(kind), Marked(line))?;
    }
    Ok(())
}

/// Run the loop over every line of `input`, writing each block to `output`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each line is offered in order and each block written as it is
///   answered; at the end of input, or at `:quit`, a buffer still waiting is
///   submitted and written; then the writer is flushed, whether the run
///   completed or faulted. The transcript is a function of the input alone. A
///   grammar that does not build, an input line that cannot be read, and a
///   session fault each stop the run, which then ends faulted; a refusal is a
///   transcript line, not a fault.
/// - provides: the deterministic face a pipe or a test drives.
/// - fails: the writer's error.
/// - panics: none.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — a piped session over a corpus source's declarations is
///   asserted line by line; an open buffer at the end of a pipe is reported;
///   unreadable input ends faulted.
/// - witness: `loop::tests::piped_value_prints_a_transcript`
/// - witness: `loop::tests::an_unparseable_pipe_reports_rather_than_going_quiet`
/// - witness: `loop::tests::unreadable_input_ends_the_batch_faulted`
#[inline]
pub fn run_batch<Input, Output>(
    input: Input,
    output: &mut Output,
    style: RenderStyle,
) -> io::Result<Ended>
where
    Input: BufRead,
    Output: Write,
{
    let ended = transcribe(input, output, style)?;
    output.flush()?;
    Ok(ended)
}

/// Offer every line of `input` to a fresh loop, writing each block to
/// `output`, without flushing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`run_batch`] states, short of the flush.
/// - provides: the body [`run_batch`] flushes after, on every ending.
/// - fails: the writer's error.
/// - panics: none.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — through [`run_batch`]'s witnesses, each asserting a piped
///   transcript line by line.
/// - witness: `loop::tests::piped_value_prints_a_transcript`
fn transcribe<Input, Output>(
    input: Input,
    output: &mut Output,
    style: RenderStyle,
) -> io::Result<Ended>
where
    Input: BufRead,
    Output: Write,
{
    let mut repl = match SessionLoop::new(style) {
        | Ok(repl) => repl,
        | Err(error) => return Ok(Ended::Faulted(Fault::Grammar(error))),
    };
    for line in input.lines() {
        let line = match line {
            | Ok(line) => line,
            | Err(error) => return Ok(Ended::Faulted(Fault::Input(error))),
        };
        match repl.offer(SourceText::from(line.as_str())) {
            | Ok(LoopEvent::Continue) => {},
            | Ok(LoopEvent::Block(block)) => write_block(output, &block)?,
            | Ok(LoopEvent::Quit) => break,
            | Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
        }
    }
    match repl.finish() {
        | Ok(Maybe::Present(block)) => write_block(output, &block)?,
        | Ok(Maybe::Absent(_)) => {},
        | Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
    }
    Ok(Ended::Completed)
}
