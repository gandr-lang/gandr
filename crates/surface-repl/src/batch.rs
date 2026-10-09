//! The batch face: lines from any reader, a plain transcript to any writer.

use core::fmt;
use std::io;
use std::io::BufRead;
use std::io::Write;

use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_grammar::PbgError;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use rustyline::error::ReadlineError;

use crate::rows::rows;
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

/// Write `block` as plain text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each of the block's [`rows`] on a line of its own, its lead and
///   then its text; no colour, so the transcript is the same on every terminal.
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
    for row in rows(block) {
        writeln!(output, "{}{}", <&str>::from(row.lead), row.text)?;
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
