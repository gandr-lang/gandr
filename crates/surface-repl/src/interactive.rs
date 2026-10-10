//! The terminal face: a line editor feeding the loop.

use alloc::string::String;
use std::io;
use std::io::Write;

use anodized::spec;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

use crate::batch::Ended;
use crate::batch::Fault;
use crate::batch::write_block;
use crate::session_loop::LoopEvent;
use crate::session_loop::Prompt;
use crate::session_loop::SessionLoop;

/// What one read from a line source answered.
#[derive(Debug)]
pub enum Read
{
    /// A line, without its terminator.
    Line(String),
    /// The user interrupted the line being edited.
    Interrupted,
    /// The input ended.
    End,
    /// The source failed.
    Failed(Fault),
}

/// Where a face's lines come from.
pub trait LineSource
{
    /// The next line, read under `prompt`.
    ///
    /// # Specification
    /// - requires: the caller stops this session after an answer of
    ///   [`Read::End`] or [`Read::Failed`].
    /// - ensures: one next input event under the supplied prompt.
    /// - provides: the reads [`drive`] takes.
    /// - fails: never; a failure is [`Read::Failed`].
    /// - panics: none.
    /// - executable: none — this abstract source has no history observer; a
    ///   return-value predicate cannot establish that a caller stops reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scripted source records prompts and retains
    ///   unread events when the driver sees an ending.
    /// - witness: `loop::tests::terminal_endings_stop_reads_and_flush_once`
    fn read(
        &mut self,
        prompt: Prompt,
    ) -> Read;
}

/// The text a terminal prompt shows.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PromptText(&'static str);

/// The prompt `prompt` shows on a terminal.
///
/// # Specification
/// trivial.
const fn prompt_text(prompt: Prompt) -> PromptText
{
    PromptText(match prompt {
        | Prompt::Fresh => "gandr> ",
        | Prompt::Continuing => "  ...> ",
    })
}

/// A terminal read through the line editor, with in-memory history.
#[repr(transparent)]
struct Terminal
{
    /// The editor.
    editor: DefaultEditor,
}

impl LineSource for Terminal
{
    /// The next line the user enters, remembered in the session's history.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a line the editor returns is added to its history and
    ///   answered; an interrupt and the end of input answer as themselves; any
    ///   other editor error, or a history that refuses the line, is a failure.
    /// - provides: the terminal's reads.
    /// - fails: never; a failure is [`Read::Failed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the face it feeds is asserted over a scripted source;
    ///   the editor's own reads, an interrupt and the end of input were
    ///   exercised by hand on a pseudo-terminal.
    /// - witness: `loop::tests::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
    #[spec(ensures: |ret| !matches!(ret,
        Read::Failed(Fault::Grammar(_) | Fault::Input(_) | Fault::Session(_))))]
    fn read(
        &mut self,
        prompt: Prompt,
    ) -> Read
    {
        let PromptText(text) = prompt_text(prompt);
        match self.editor.readline(text) {
            | Ok(line) => match self.editor.add_history_entry(line.as_str()) {
                | Ok(_) => Read::Line(line),
                | Err(error) => Read::Failed(Fault::Editor(error)),
            },
            | Err(ReadlineError::Interrupted) => Read::Interrupted,
            | Err(ReadlineError::Eof) => Read::End,
            | Err(error) => Read::Failed(Fault::Editor(error)),
        }
    }
}

/// Run the loop over the lines `source` answers, writing each block to
/// `output`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each read is made under the loop's prompt; a line is offered and
///   its block written and flushed at once; an interrupt drops the waiting
///   buffer; the end of input, or `:quit`, submits a buffer still waiting and
///   writes its block. A grammar that does not build, a failed read and a
///   session fault each end the run faulted, after a flush.
/// - provides: the interactive half of the faces, over any source.
/// - fails: the writer's error.
/// - panics: none.
/// - executable: none — the generic source and writer expose no transcript or
///   flush observer, and the source may return any fault kind.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — over a scripted source, the prompts asked, an interrupted
///   buffer's absence from the transcript, and the block of a buffer left open
///   at the end are asserted exactly.
/// - witness: `loop::tests::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
/// - witness: `loop::tests::terminal_endings_stop_reads_and_flush_once`
#[inline]
pub fn drive<Source, Output>(
    source: &mut Source,
    output: &mut Output,
    style: RenderStyle,
) -> io::Result<Ended>
where
    Source: LineSource,
    Output: Write,
{
    let ended = converse(source, output, style)?;
    output.flush()?;
    Ok(ended)
}

/// Offer every line `source` answers to a fresh loop, writing each block to
/// `output`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`drive`] states, short of the final flush.
/// - provides: the body [`drive`] flushes after, on every ending.
/// - fails: the writer's error.
/// - panics: none.
/// - executable: none — the generic source and writer expose no transcript or
///   flush observer, and the source may return any fault kind.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — through [`drive`]'s witness, the prompts and the
///   transcript asserted exactly.
/// - witness: `loop::tests::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
/// - witness: `loop::tests::terminal_endings_stop_reads_and_flush_once`
fn converse<Source, Output>(
    source: &mut Source,
    output: &mut Output,
    style: RenderStyle,
) -> io::Result<Ended>
where
    Source: LineSource,
    Output: Write,
{
    let mut repl = match SessionLoop::new(style) {
        | Ok(repl) => repl,
        | Err(error) => return Ok(Ended::Faulted(Fault::Grammar(error))),
    };
    loop {
        match source.read(repl.prompt()) {
            | Read::Line(line) => match repl.offer(SourceText::from(line.as_str())) {
                | Ok(LoopEvent::Continue) => {},
                | Ok(LoopEvent::Block(block)) => {
                    write_block(output, &block)?;
                    output.flush()?;
                },
                | Ok(LoopEvent::Quit) => break,
                | Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
            },
            | Read::Interrupted => repl.discard(),
            | Read::End => break,
            | Read::Failed(fault) => return Ok(Ended::Faulted(fault)),
        }
    }
    match repl.finish() {
        | Ok(Maybe::Present(block)) => write_block(output, &block)?,
        | Ok(Maybe::Absent(_)) => {},
        | Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
    }
    Ok(Ended::Completed)
}

/// Run the loop on the terminal, through the line editor, writing each block
/// to `output`.
///
/// # Specification
/// - requires: standard input is a terminal; the editor falls back to plain
///   reads otherwise.
/// - ensures: as [`drive`] states, over the editor's reads: `gandr> ` prompts a
///   fresh line and `  ...> ` a continued buffer; the editor's keys edit the
///   line; history lives for the run and is never written to disk. An editor
///   that cannot start ends the run faulted.
/// - provides: `gandr repl` on a terminal.
/// - fails: the writer's error.
/// - panics: none.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — the face is asserted over a scripted source through
///   [`drive`]; the editor on a terminal, which the test runner lacks, was
///   exercised by hand on a pseudo-terminal.
/// - witness: `loop::tests::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`
#[spec(ensures: |ret| !matches!(ret, Ok(Ended::Faulted(Fault::Input(_)))))]
#[inline]
pub fn run_interactive<Output>(
    output: &mut Output,
    style: RenderStyle,
) -> io::Result<Ended>
where
    Output: Write,
{
    let editor = match DefaultEditor::new() {
        | Ok(editor) => editor,
        | Err(error) => return Ok(Ended::Faulted(Fault::Editor(error))),
    };
    drive(&mut Terminal { editor }, output, style)
}
