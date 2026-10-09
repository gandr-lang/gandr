//! The event loop, over the terminal or off it.

use std::io;
use std::io::Write;

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
    /// - ensures: one answer per call, waiting for it as long as the source
    ///   must; a source that answered [`Input::Failed`] is not read again.
    /// - provides: the reads [`drive`] takes.
    /// - fails: never; a failure is [`Input::Failed`].
    /// - panics: none.
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
    /// - hypothesis: L3 — the loop it feeds is asserted over scripted keys; the
    ///   terminal's own events were exercised by hand on a pseudo-terminal.
    /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
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
/// - requires: nothing.
/// - ensures: a character typed without control or alt is that character;
///   control-C interrupts; enter, backspace and escape are themselves, escape
///   quitting; every other key redraws.
/// - provides: the face's key bindings.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the bindings were exercised by hand on a pseudo-terminal;
///   the keys they map to are asserted through the loop.
/// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
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
/// - requires: nothing.
/// - ensures: a fresh [`App`] is drawn before every read and each input
///   applied: a key through [`App::handle`], a redraw by drawing again. The run
///   completes when a key or `:quit` asks to leave; a grammar that does not
///   build, a failed read and a session fault each end it faulted.
/// - provides: the face's one event loop, the same on the terminal, on the
///   smoke face and under a test's scripted keys.
/// - fails: the backend's error when a frame cannot be drawn.
/// - panics: none.
///
/// # Errors
/// The backend's error when a frame cannot be drawn.
///
/// # Adequacy
/// - hypothesis: L3 — over scripted keys on a headless backend, the painted
///   frame and the ending are asserted; the smoke face runs it once.
/// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
/// - witness: `launch::tests::smoke_writes_the_launch_note`
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
/// - hypothesis: L3 — the loop is asserted over scripted keys through
///   [`drive`]; the terminal face itself, which the test runner lacks, was
///   exercised by hand on a pseudo-terminal.
/// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
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
/// - hypothesis: L1 — the whole output is compared with the note; the driver's
///   witness spawns the binary and compares its line and exit code.
/// - witness: `launch::tests::smoke_writes_the_launch_note`
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
