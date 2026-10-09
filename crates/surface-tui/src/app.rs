//! The face's model: the loop, the line being edited, the lines the loop holds
//! for the parser, and the transcript.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_grammar::PbgError;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_repl::LoopError;
use gandr_surface_repl::LoopEvent;
use gandr_surface_repl::Prompt;
use gandr_surface_repl::SessionLoop;
use gandr_surface_syntax::SourceText;

/// One key the face acts on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Key
{
    /// Type a character at the end of the line.
    Char(char),
    /// Remove the line's last character.
    Backspace,
    /// Offer the line to the loop.
    Enter,
    /// Drop the line and the buffer waiting for the parser, as an interrupt
    /// at the line editor's prompt does.
    Interrupt,
    /// Leave the face.
    Quit,
}

/// What a key leaves the face to do.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Handled
{
    /// Draw and read the next key.
    Continue,
    /// Leave: the user asked to, by key or by `:quit`.
    Quit,
}

/// The face's state over one read-evaluate loop.
///
/// The loop owns the buffer the parser waits on; the face keeps the lines it
/// offered into that buffer only to show them above the line being edited.
#[derive(Debug)]
pub struct App
{
    /// The read-evaluate loop every line is offered to.
    repl: SessionLoop,
    /// The line being edited.
    line: String,
    /// The lines offered into the buffer the parser still waits on.
    waiting: Vec<String>,
    /// Every block the loop answered, oldest first.
    transcript: Vec<TranscriptBlock>,
}

impl App
{
    /// A face over a fresh loop, its refusals rendered plainly for the
    /// face to style.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an empty line, nothing waiting and an empty transcript over a
    ///   loop whose refusals carry no terminal escapes, so the face's own
    ///   styles are the only ones painted.
    /// - provides: the model every run of the face starts from.
    /// - fails: [`PbgError`] when the built-in grammar or its role table does
    ///   not build.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError`] when the built-in grammar or its role table does not build.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every face witness starts here.
    /// - witness: `launch::tests::smoke_writes_the_launch_note`
    #[inline]
    pub fn new() -> Result<Self, PbgError>
    {
        let repl = SessionLoop::new(RenderStyle::Plain)?;
        Ok(Self {
            repl,
            line: String::new(),
            waiting: Vec::new(),
            transcript: Vec::new(),
        })
    }

    /// Every block the loop answered, oldest first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transcript(&self) -> &[TranscriptBlock]
    {
        &self.transcript
    }

    /// The lines offered into the buffer the parser still waits on.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn waiting(&self) -> &[String]
    {
        &self.waiting
    }

    /// The line being edited.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn line(&self) -> SourceText<'_>
    {
        SourceText::from(self.line.as_str())
    }

    /// Which prompt the loop stands at.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn prompt(&self) -> Prompt
    {
        self.repl.prompt()
    }

    /// Apply `key`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a character extends the line and a backspace shortens it;
    ///   enter offers the line to the loop and clears it — a line the loop
    ///   holds for the parser is kept to show while it waits, a block joins the
    ///   transcript and ends the wait, and `:quit` answers [`Handled::Quit`];
    ///   an interrupt drops the line and the waiting buffer; quit answers
    ///   [`Handled::Quit`]. Every other key answers [`Handled::Continue`].
    /// - provides: the face's one update step.
    /// - fails: [`LoopError::Fault`] when the session faults on the offered
    ///   line.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults on the offered line.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over scripted keys, a continued buffer shown while it
    ///   waits, an interrupt dropping it, a kept block and `:q` ending the run
    ///   are asserted on the painted frame.
    /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    #[inline]
    pub fn handle(
        &mut self,
        key: Key,
    ) -> Result<Handled, LoopError>
    {
        match key {
            | Key::Char(typed) => self.line.push(typed),
            | Key::Backspace => {
                let _removed = self.line.pop();
            },
            | Key::Enter => {
                let line = core::mem::take(&mut self.line);
                let event = self.repl.offer(SourceText::from(line.as_str()))?;
                match event {
                    | LoopEvent::Continue => {
                        if self.repl.prompt() == Prompt::Continuing {
                            self.waiting.push(line);
                        }
                    },
                    | LoopEvent::Block(block) => {
                        self.waiting.clear();
                        self.transcript.push(block);
                    },
                    | LoopEvent::Quit => return Ok(Handled::Quit),
                }
            },
            | Key::Interrupt => {
                self.repl.discard();
                self.line.clear();
                self.waiting.clear();
            },
            | Key::Quit => return Ok(Handled::Quit),
        }
        Ok(Handled::Continue)
    }
}
