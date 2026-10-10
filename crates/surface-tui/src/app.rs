//! The face's model: the loop, the line being edited, the lines the loop holds
//! for the parser, and the transcript.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
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
    ///   fresh loop whose refusal renderer selects plain styling.
    /// - provides: the model every run of the face starts from.
    /// - fails: [`PbgError`] when the built-in grammar or its role table does
    ///   not build.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError`] when the built-in grammar or its role table does not build.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fresh state and an ASCII type mismatch expose empty
    ///   editing buffers and diagnostic rows without added escapes. Dirty state
    ///   or styled-loop substitution changes an observation;
    ///   grammar-construction failure and literal control-bearing source text
    ///   are excluded.
    /// - witness: `app::tests::unicode_edits_and_empty_backspace_preserve_input_boundaries`
    /// - witness: `app::tests::a_fresh_loop_keeps_refusal_rows_plain`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |app| app.line.is_empty() && app.waiting.is_empty() && app.transcript.is_empty() && app.repl.prompt() == Prompt::Fresh))]
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
    /// - requires: on Enter, the edited line carries no CR or LF terminator, as
    ///   required by the loop's line-oriented offer.
    /// - ensures: a character appends one Unicode scalar; Backspace removes the
    ///   last scalar, or preserves an empty line. Enter clears the line and
    ///   offers it once; a waiting line is retained for display, a block joins
    ///   the transcript and clears waiting lines, and `:quit` answers
    ///   [`Handled::Quit`]. Interrupt drops the edit and waiting buffer while
    ///   preserving accepted history. Quit preserves state and answers
    ///   [`Handled::Quit`]. Other successful keys answer [`Handled::Continue`].
    /// - provides: the face's one update step.
    /// - fails: [`LoopError::Fault`] when the session faults on the offered
    ///   line.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoopError::Fault`] when the session faults on the offered line.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one-, two- and four-byte scalars cover editing and
    ///   empty Backspace; completed and interrupted continuations retain exact
    ///   source and accepted names. Scripted redraw and quit cover loop
    ///   transitions. Lost scalars, duplicated lines, discarded history or
    ///   wrong exit tags change observations; session faults and invalid line
    ///   submissions are outside the witnesses.
    /// - witness: `app::tests::unicode_edits_and_empty_backspace_preserve_input_boundaries`
    /// - witness: `app::tests::completed_and_interrupted_waits_preserve_the_transcript`
    /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    #[spec(
        requires: key != Key::Enter || !self.line.contains(['\r', '\n']),
        captures: [
            line_bytes = self.line.len(),
            last_bytes = self.line.chars().next_back().map_or(0_usize, char::len_utf8),
            waiting = self.waiting.len(),
            blocks = self.transcript.len(),
            prompt = self.repl.prompt(),
        ],
        ensures: |ref ret| match key {
            Key::Char(typed) => matches!(*ret, Ok(Handled::Continue))
                && self.line.len().checked_sub(typed.len_utf8()) == Some(line_bytes)
                && self.line.ends_with(typed) && self.waiting.len() == waiting
                && self.transcript.len() == blocks && self.repl.prompt() == prompt,
            Key::Backspace => matches!(*ret, Ok(Handled::Continue))
                && self.line.len() == line_bytes.saturating_sub(last_bytes)
                && self.waiting.len() == waiting && self.transcript.len() == blocks
                && self.repl.prompt() == prompt,
            Key::Interrupt => matches!(*ret, Ok(Handled::Continue))
                && self.line.is_empty() && self.waiting.is_empty()
                && self.transcript.len() == blocks && self.repl.prompt() == Prompt::Fresh,
            Key::Quit => matches!(*ret, Ok(Handled::Quit))
                && self.line.len() == line_bytes && self.waiting.len() == waiting
                && self.transcript.len() == blocks && self.repl.prompt() == prompt,
            Key::Enter => self.line.is_empty() && match *ret {
                Ok(Handled::Continue) => match (self.transcript.len().checked_sub(blocks), self.repl.prompt()) {
                    (Some(1_usize), Prompt::Fresh) => self.waiting.is_empty(),
                    (Some(0_usize), Prompt::Continuing) => self.waiting.len().checked_sub(waiting) == Some(1_usize),
                    (Some(0_usize), Prompt::Fresh) => self.waiting.len() == waiting,
                    _ => false,
                },
                Ok(Handled::Quit) | Err(_) => self.waiting.len() == waiting && self.transcript.len() == blocks,
            },
        },
    )]
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

#[cfg(test)]
mod tests
{
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_repl::Prompt;

    use super::App;
    use super::Handled;
    use super::Key;

    #[test]
    fn unicode_edits_and_empty_backspace_preserve_input_boundaries()
    {
        let mut app = App::new().expect("the grammar builds");
        assert!(app.line().as_ref().is_empty());
        assert!(app.waiting().is_empty());
        assert!(app.transcript().is_empty());
        assert_eq!(app.prompt(), Prompt::Fresh);
        for typed in "aé𐐀".chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing succeeds"),
                Handled::Continue
            );
        }
        assert_eq!(app.line().as_ref(), "aé𐐀");
        for expected in ["aé", "a", "", ""] {
            assert_eq!(
                app.handle(Key::Backspace).expect("deleting succeeds"),
                Handled::Continue
            );
            assert_eq!(app.line().as_ref(), expected);
            assert!(app.waiting().is_empty());
            assert!(app.transcript().is_empty());
            assert_eq!(app.prompt(), Prompt::Fresh);
        }
        assert_eq!(
            app.handle(Key::Char('é')).expect("typing succeeds"),
            Handled::Continue
        );
        assert_eq!(
            app.handle(Key::Quit).expect("leaving succeeds"),
            Handled::Quit
        );
        assert_eq!(app.line().as_ref(), "é");
    }

    #[test]
    fn completed_and_interrupted_waits_preserve_the_transcript()
    {
        let mut app = App::new().expect("the grammar builds");
        for typed in "def kept = (".chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing succeeds"),
                Handled::Continue
            );
        }
        assert_eq!(
            app.handle(Key::Enter).expect("an open form waits"),
            Handled::Continue
        );
        assert_eq!(app.prompt(), Prompt::Continuing);
        assert!(app.line().as_ref().is_empty());
        assert!(
            app.waiting()
                .iter()
                .map(String::as_str)
                .eq(["def kept = ("])
        );
        assert!(app.transcript().is_empty());
        for typed in "17) ;".chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing succeeds"),
                Handled::Continue
            );
        }
        assert_eq!(
            app.handle(Key::Enter).expect("the form completes"),
            Handled::Continue
        );
        assert_eq!(app.prompt(), Prompt::Fresh);
        assert!(app.waiting().is_empty());
        assert_eq!(app.transcript().len(), 1_usize);
        assert_eq!(app.transcript()[0_usize].source, "def kept = (\n17) ;");
        for typed in "def abandoned = (".chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing succeeds"),
                Handled::Continue
            );
        }
        assert_eq!(
            app.handle(Key::Enter).expect("an open form waits"),
            Handled::Continue
        );
        assert_eq!(
            app.handle(Key::Char('9')).expect("typing succeeds"),
            Handled::Continue
        );
        assert_eq!(
            app.handle(Key::Interrupt).expect("interrupting succeeds"),
            Handled::Continue
        );
        assert!(app.line().as_ref().is_empty());
        assert!(app.waiting().is_empty());
        assert_eq!(app.prompt(), Prompt::Fresh);
        assert_eq!(app.transcript().len(), 1_usize);
        assert_eq!(app.transcript()[0_usize].source, "def kept = (\n17) ;");
        for typed in ":type kept".chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing succeeds"),
                Handled::Continue
            );
        }
        assert_eq!(
            app.handle(Key::Enter).expect("the retained name resolves"),
            Handled::Continue
        );
        assert_eq!(app.transcript().len(), 2_usize);
        assert!(
            app.transcript()[1_usize]
                .lines
                .iter()
                .any(|&(kind, _)| kind == OutKind::Type)
        );
        assert!(
            app.transcript()[1_usize]
                .lines
                .iter()
                .all(|&(kind, _)| kind != OutKind::Diag)
        );
    }

    #[test]
    fn a_fresh_loop_keeps_refusal_rows_plain()
    {
        let mut app = App::new().expect("the grammar builds");
        for line in ["def wrong : Integer ;", "def wrong = \"text\" ;"] {
            for typed in line.chars() {
                assert_eq!(
                    app.handle(Key::Char(typed)).expect("typing succeeds"),
                    Handled::Continue
                );
            }
            assert_eq!(
                app.handle(Key::Enter).expect("the declaration is answered"),
                Handled::Continue
            );
        }
        let refusal = app
            .transcript()
            .last()
            .expect("the mismatch produces a block");
        assert!(refusal.lines.iter().any(|&(kind, _)| kind == OutKind::Diag));
        assert!(refusal.lines.iter().all(|line| !line.1.contains('\u{1b}')));
    }
}
