//! The event loop, over the terminal or off it.

use std::io;
use std::io::Write;

use anodized::spec;
use gandr_surface_repl::Ended;
use gandr_surface_repl::Fault;
use ratatui::Terminal;
use ratatui::backend::Backend;
use ratatui::backend::TestBackend;
use ratatui::crossterm::event::Event;
use ratatui::crossterm::event::KeyCode;
use ratatui::crossterm::event::KeyEvent;
use ratatui::crossterm::event::KeyEventKind;
use ratatui::crossterm::event::KeyModifiers;

use crate::app::App;
use crate::app::Handled;
use crate::app::Key;
use crate::view::draw;

/// The line the smoke face prints.
pub const SMOKE_NOTE: &str = "gandr tui: ready\n";

/// What one read of the face's input answered.
#[derive(Debug)]
pub enum Input
{
    /// A key the face acts on.
    Key(Key),
    /// Nothing to act on — a resize, a release, a key the face does not use —
    /// but the frame is drawn again.
    Redraw,
    /// The input failed.
    Failed(Fault),
}

/// Where the face's input comes from.
pub trait InputSource
{
    /// The next input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one input is returned after the source's wait; failures are
    ///   represented by [`Input::Failed`]. [`drive`] does not read after one.
    /// - provides: the reads [`drive`] takes.
    /// - fails: never; a failure is [`Input::Failed`].
    /// - panics: none.
    /// - executable: none — this abstract source exposes no pending-input or
    ///   read-state observer; the returned variant alone cannot prove progress.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite scripted input includes accepted and abandoned
    ///   declarations, redraw, quit and an input failure followed by unread
    ///   input. Exact final cells, fault kind and queue residue detect
    ///   reordered reads or reading past an ending. OS event timing is outside
    ///   the domain.
    /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
    /// - witness: `launch::tests::a_failed_input_preserves_its_cause_and_stops_reading`
    fn next(&mut self) -> Input;
}

/// The terminal's key events.
struct Keyboard;

impl InputSource for Keyboard
{
    /// The next terminal event, as the face reads it.
    ///
    /// # Specification
    /// - requires: the terminal is in raw mode, so keys arrive one at a time
    ///   and an interrupt arrives as a key rather than a signal.
    /// - ensures: a pressed key the face uses is that key, as [`key`] maps it;
    ///   every other event redraws; an event that cannot be read is
    ///   [`Fault::Input`].
    /// - provides: `gandr tui`'s reads.
    /// - fails: never; a failure is [`Input::Failed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite key/modifier boundaries exercise the pure key
    ///   mapping; scripted outcomes distinguish interruption, redraw and quit.
    ///   An opt-in terminal witness reads real quit keys and observes
    ///   completion and restored settings. OS read failures and non-key events
    ///   are outside this domain.
    /// - witness: `run::tests::key_bindings_respect_modifier_precedence`
    /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
    /// - witness: `launch::tests::the_terminal_face_completes_and_restores_its_settings`
    #[spec(ensures: |ref ret| matches!(*ret,
        Input::Key(_) | Input::Redraw | Input::Failed(Fault::Input(_))))]
    fn next(&mut self) -> Input
    {
        match ratatui::crossterm::event::read() {
            | Ok(Event::Key(event)) if event.kind == KeyEventKind::Press => key(event),
            | Ok(_) => Input::Redraw,
            | Err(error) => Input::Failed(Fault::Input(error)),
        }
    }
}

/// The input a pressed key is.
///
/// # Specification
/// - requires: nothing; event-kind filtering belongs to [`Keyboard`].
/// - ensures: a character without control or alt is preserved; control with
///   lowercase c interrupts even with alt. Enter, backspace and escape keep
///   their meanings regardless of modifiers; every other key redraws.
/// - provides: the face's key bindings.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — letters, Unicode, navigation and editing keys under
///   plain, shift, control and alt modifiers distinguish character loss,
///   accidental control/alt insertion and wrong interrupt precedence. The
///   finite table does not enumerate every named key or modifier combination.
/// - witness: `run::tests::key_bindings_respect_modifier_precedence`
#[spec(ensures: |ref ret| {
    let control = event.modifiers.contains(KeyModifiers::CONTROL);
    let alt = event.modifiers.contains(KeyModifiers::ALT);
    match *ret {
        Input::Key(Key::Interrupt) => event.code == KeyCode::Char('c') && control,
        Input::Key(Key::Char(typed)) => event.code == KeyCode::Char(typed) && !control && !alt,
        Input::Key(Key::Enter) => event.code == KeyCode::Enter,
        Input::Key(Key::Backspace) => event.code == KeyCode::Backspace,
        Input::Key(Key::Quit) => event.code == KeyCode::Esc,
        Input::Redraw => !(matches!(event.code, KeyCode::Enter | KeyCode::Backspace | KeyCode::Esc)
            || event.code == KeyCode::Char('c') && control)
            && (!matches!(event.code, KeyCode::Char(_)) || control || alt),
        Input::Failed(_) => false,
    }
})]
fn key(event: KeyEvent) -> Input
{
    let control = event.modifiers.contains(KeyModifiers::CONTROL);
    let alt = event.modifiers.contains(KeyModifiers::ALT);
    match event.code {
        | KeyCode::Char('c') if control => Input::Key(Key::Interrupt),
        | KeyCode::Char(typed) if !control && !alt => Input::Key(Key::Char(typed)),
        | KeyCode::Enter => Input::Key(Key::Enter),
        | KeyCode::Backspace => Input::Key(Key::Backspace),
        | KeyCode::Esc => Input::Key(Key::Quit),
        | _ => Input::Redraw,
    }
}

/// An input source that asks to leave at once.
struct Leave;

impl InputSource for Leave
{
    /// Leave.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Input
    {
        Input::Key(Key::Quit)
    }
}

/// Run the face over `terminal`, reading `source`, until it ends.
///
/// # Specification
/// - requires: submitted lines contain no line terminator, as [`App::handle`]
///   requires.
/// - ensures: one fresh [`App`] is created and its current frame drawn before
///   every read. Keys go through [`App::handle`]; redraw paints again. The run
///   completes when a key or `:quit` asks to leave; a grammar that does not
///   build, a failed read and a session fault each end it faulted.
/// - provides: the face's one event loop, the same on the terminal, on the
///   smoke face and under a test's scripted keys.
/// - fails: the backend's error when a frame cannot be drawn.
/// - panics: none.
/// - executable: none — neither generic input nor backend exposes immutable
///   queue or painted-state observations. Their effects and arbitrary supplied
///   fault values cannot be recovered from the ending alone.
///
/// # Errors
/// The backend's error when a frame cannot be drawn.
///
/// # Adequacy
/// - hypothesis: L3 — finite scripts cover an interrupted declaration, an
///   accepted declaration, redraw, command quit, and a failed input with a
///   queued successor. Exact backend rows, fault kind and remaining input
///   distinguish reordering, lost events and reads after termination. Backend
///   draw errors and grammar-construction failure are outside these witnesses.
/// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
/// - witness: `launch::tests::a_failed_input_preserves_its_cause_and_stops_reading`
#[inline]
pub fn drive<Screen, Source>(
    terminal: &mut Terminal<Screen>,
    source: &mut Source,
) -> Result<Ended, Screen::Error>
where
    Screen: Backend,
    Source: InputSource,
{
    let mut app = match App::new() {
        | Ok(app) => app,
        | Err(error) => return Ok(Ended::Faulted(Fault::Grammar(error))),
    };
    loop {
        let _frame = terminal.draw(|frame| draw(frame, &app))?;
        match source.next() {
            | Input::Key(key) => match app.handle(key) {
                | Ok(Handled::Continue) => {},
                | Ok(Handled::Quit) => return Ok(Ended::Completed),
                | Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
            },
            | Input::Redraw => {},
            | Input::Failed(fault) => return Ok(Ended::Faulted(fault)),
        }
    }
}

/// Run the face on the process's terminal until the user leaves.
///
/// # Specification
/// - requires: standard input and output are a terminal.
/// - ensures: the terminal is put in raw mode on the alternate screen, the face
///   runs as [`drive`] states over its key events, and the terminal is restored
///   on every ending — completed, faulted, failed, or a panic, whose hook
///   restores it before reporting.
/// - provides: `gandr tui`.
/// - fails: the terminal's error when it cannot be claimed, drawn on or
///   restored; a failure to restore is reported only when the run itself
///   succeeded.
/// - panics: none.
///
/// # Errors
/// The terminal's error when it cannot be claimed, drawn on or restored.
///
/// # Adequacy
/// - hypothesis: L3 — scripted input and failure expose rows, ending and unread
///   suffix. An opt-in terminal witness independently compares settings before
///   and after a real quit. Reordered events, a wrong ending or missing
///   restoration changes those observations. Real backend failure injection and
///   arbitrary terminal configurations remain outside this domain.
/// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
/// - witness: `launch::tests::a_failed_input_preserves_its_cause_and_stops_reading`
/// - witness: `launch::tests::the_terminal_face_completes_and_restores_its_settings`
#[spec(ensures: |ref ret| !matches!(*ret, Ok(Ended::Faulted(Fault::Editor(_)))))]
#[inline]
pub fn run() -> io::Result<Ended>
{
    let ended = match ratatui::try_init() {
        | Ok(mut terminal) => drive(&mut terminal, &mut Keyboard),
        | Err(error) => Err(error),
    };
    let restored = ratatui::try_restore();
    match (ended, restored) {
        | (Ok(ended), Ok(())) => Ok(ended),
        | (Err(error), _) | (Ok(_), Err(error)) => Err(error),
    }
}

/// Run the face once off-screen and print [`SMOKE_NOTE`] to `output`.
///
/// # Specification
/// - requires: nothing; no terminal is touched.
/// - ensures: the face's event loop draws a fresh face on an 80 by 24 headless
///   backend and leaves at its first read; when that completes, [`SMOKE_NOTE`]
///   is written once and flushed. A grammar that does not build ends the run
///   faulted with nothing written.
/// - provides: `gandr tui --smoke`, the face a gate can exercise without a
///   terminal.
/// - fails: the writer's error.
/// - panics: none.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — a capacity-limited writer accepts a prefix and then
///   refuses the rest. Filled capacity and the `WriteZero` error separate
///   ignored partial writes and swallowed failures. Successful terminal-free
///   execution is exercised by the smoke command; grammar and flush failure are
///   outside this witness.
/// - witness: `launch::tests::the_smoke_face_propagates_a_partial_write_failure`
#[spec(ensures: |ref ret| matches!(
    *ret, Err(_) | Ok(Ended::Completed | Ended::Faulted(Fault::Grammar(_)))
))]
#[inline]
pub fn run_smoke<Output>(output: &mut Output) -> io::Result<Ended>
where
    Output: Write,
{
    let Ok(mut terminal) = Terminal::new(TestBackend::new(80, 24));
    let Ok(ended) = drive(&mut terminal, &mut Leave);
    if let Ended::Faulted(_) = ended {
        return Ok(ended);
    }
    output.write_all(SMOKE_NOTE.as_bytes())?;
    output.flush()?;
    Ok(ended)
}

#[cfg(test)]
mod tests
{
    use super::Input;
    use super::Key;
    use super::KeyCode;
    use super::KeyEvent;
    use super::KeyModifiers;
    use super::key;

    #[test]
    fn key_bindings_respect_modifier_precedence()
    {
        for (code, modifiers, expected) in [
            (KeyCode::Char('a'), KeyModifiers::NONE, Key::Char('a')),
            (KeyCode::Char('界'), KeyModifiers::SHIFT, Key::Char('界')),
            (KeyCode::Char('c'), KeyModifiers::CONTROL, Key::Interrupt),
            (
                KeyCode::Char('c'),
                KeyModifiers::CONTROL | KeyModifiers::ALT,
                Key::Interrupt,
            ),
            (KeyCode::Enter, KeyModifiers::ALT, Key::Enter),
            (KeyCode::Backspace, KeyModifiers::CONTROL, Key::Backspace),
            (KeyCode::Esc, KeyModifiers::SHIFT, Key::Quit),
        ] {
            let Input::Key(actual) = key(KeyEvent::new(code, modifiers))
            else {
                panic!("the supported key must be actionable: {code:?} {modifiers:?}");
            };
            assert_eq!(actual, expected);
        }
        for (code, modifiers) in [
            (KeyCode::Char('c'), KeyModifiers::ALT),
            (KeyCode::Char('x'), KeyModifiers::CONTROL),
            (
                KeyCode::Char('C'),
                KeyModifiers::CONTROL | KeyModifiers::SHIFT,
            ),
            (KeyCode::Left, KeyModifiers::NONE),
        ] {
            assert!(matches!(key(KeyEvent::new(code, modifiers)), Input::Redraw));
        }
    }
}
