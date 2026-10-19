//! The event loop, over the terminal or off it.
//!
//! # The renderer
//!
//! The face draws with `ratatui` 0.30.2, defaults off, with one feature:
//! `crossterm`, the backend `gandr tui` draws through. Off are `all-widgets`,
//! which adds the calendar widget and `time`; `layout-cache`, an LRU of solved
//! layouts that the face's one three-pane layout does not need; `macros`, a
//! crate of span and layout macros the face does not use; `underline-color`, a
//! style the face does not paint; and the other backends, `serde`, `palette`,
//! `portable-atomic`, `scrolling-regions` and the unstable features, which the
//! face has no use for. `crossterm` 0.29.0 is reached through
//! `ratatui::crossterm` rather than pinned beside it, so the graph holds the
//! one crossterm the backend was built against: raw mode is enabled and
//! restored through a single copy of crossterm's terminal state, and a second
//! pin could not drift from the backend's.
//!
//! ratatui's crossterm backend takes crossterm with its default features and
//! turns its own underline colour on, so crossterm's event reading, bracketed
//! paste and its `derive_more` helpers build whatever the face asks; the
//! feature set above is the smallest ratatui admits.
//!
//! The face brings into the driver ratatui's four crates; crossterm with `mio`,
//! `signal-hook` and `rustix`; `parking_lot`; `kasuari`, the layout solver;
//! `lru`, `compact_str`, `itertools`, `strum` and `unicode-truncate`; and eight
//! procedural macro crates — `instability` with `darling`, `strum_macros`,
//! `thiserror-impl`, `derive_more-impl`, `document-features`, `indoc` and
//! `rustversion`. `kasuari` pins a third `hashbrown` and ratatui's default
//! `hashbrown` a second `foldhash`; the workspace's duplicate-crate allowance
//! names both with their reversal. The face is always built: `gandr tui` needs
//! it, and a feature gate would only make the default binary unable to do what
//! its verb says.
//!
//! The alternatives were `cursive`, which owns the event loop and its own view
//! tree — the face's loop is `gandr-surface-repl`'s and must stay the driver of
//! every submission — and has one maintainer and fewer than two hundred
//! dependents; `termwiz`, the terminal layer of one terminal emulator, with one
//! maintainer and a few dozen dependents; and `crossterm` alone, which would
//! hand-write the layout, the styled text, the frame diffing and the headless
//! backend ratatui provides. ratatui with crossterm is the pair the community's
//! crate guides name for a terminal interface, ratatui maintained by a team and
//! crossterm by some two hundred contributors, with no published advisory
//! against either. The choice reverses on a high-risk advisory or an
//! unmaintained mark against ratatui or crossterm, or when a face needs a
//! backend ratatui does not carry.
//!
//! # The smoke face
//!
//! `run_smoke` drives the same event loop as `gandr tui` over ratatui's
//! headless backend, 80 columns by 24 rows, with an input source that asks to
//! leave at its first read, then prints `gandr tui: ready`. The gate exercises
//! the grammar, the loop's construction, one full paint and the event loop
//! without a terminal, and the driver's witness spawns it as a user would.

use std::io;
use std::io::Write;

use anodized::spec;
use gandr_surface_grammar::Spelling;
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
    /// - witness: `tests::launch::the_face_drives_the_loop_from_its_keys`
    /// - witness: `tests::launch::a_failed_input_preserves_its_cause_and_stops_reading`
    fn next(&mut self) -> Input;
}

/// The terminal's key events.
pub struct Keyboard;

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
    /// - witness: `tests::launch::the_face_drives_the_loop_from_its_keys`
    /// - witness: `tests::launch::the_terminal_face_completes_and_restores_its_settings`
    #[spec(ensures: |ref ret| matches!(*ret,
        Input::Key(_) | Input::Redraw | Input::Failed(Fault::Input(_))))]
    fn next(&mut self) -> Input
    {
        match ratatui::crossterm::event::read() {
            Ok(Event::Key(event)) if event.kind == KeyEventKind::Press => key(event),
            Ok(_) => Input::Redraw,
            Err(error) => Input::Failed(Fault::Input(error)),
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
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "`KeyCode` is crossterm's key enum, wide and growing; every key the face does not \
              bind redraws"
)]
fn key(event: KeyEvent) -> Input
{
    let control = event.modifiers.contains(KeyModifiers::CONTROL);
    let alt = event.modifiers.contains(KeyModifiers::ALT);
    match event.code {
        KeyCode::Char('c') if control => Input::Key(Key::Interrupt),
        KeyCode::Char(typed) if !control && !alt => Input::Key(Key::Char(typed)),
        KeyCode::Enter => Input::Key(Key::Enter),
        KeyCode::Backspace => Input::Key(Key::Backspace),
        KeyCode::Esc => Input::Key(Key::Quit),
        _ => Input::Redraw,
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
/// - ensures: one fresh [`App`] is created, writing its types and values in
///   `spelling`, and its current frame drawn before every read. Keys go through
///   [`App::handle`]; redraw paints again. The run completes when a key or
///   `:quit` asks to leave; a grammar that does not build, a failed read and a
///   session fault each end it faulted.
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
/// - witness: `tests::launch::the_face_drives_the_loop_from_its_keys`
/// - witness: `tests::launch::a_failed_input_preserves_its_cause_and_stops_reading`
#[inline]
pub fn drive<Screen, Source>(
    terminal: &mut Terminal<Screen>,
    source: &mut Source,
    spelling: Spelling,
) -> Result<Ended, Screen::Error>
where
    Screen: Backend,
    Source: InputSource,
{
    let mut app = match App::new(spelling) {
        Ok(app) => app,
        Err(error) => return Ok(Ended::Faulted(Fault::Grammar(error))),
    };
    loop {
        let _frame = terminal.draw(|frame| draw(frame, &app))?;
        match source.next() {
            Input::Key(key) => match app.handle(key) {
                Ok(Handled::Continue) => {},
                Ok(Handled::Quit) => return Ok(Ended::Completed),
                Err(error) => return Ok(Ended::Faulted(Fault::Session(error))),
            },
            Input::Redraw => {},
            Input::Failed(fault) => return Ok(Ended::Faulted(fault)),
        }
    }
}

/// Run the face on the process's terminal until the user leaves.
///
/// # Specification
/// - requires: standard input and output are a terminal.
/// - ensures: the terminal is put in raw mode on the alternate screen, the face
///   runs as [`drive`] states over its key events, in `spelling`, and the
///   terminal is restored on every ending — completed, faulted, failed, or a
///   panic, whose hook restores it before reporting.
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
/// - witness: `tests::launch::the_face_drives_the_loop_from_its_keys`
/// - witness: `tests::launch::a_failed_input_preserves_its_cause_and_stops_reading`
/// - witness: `tests::launch::the_terminal_face_completes_and_restores_its_settings`
#[spec(ensures: |ref ret| !matches!(*ret, Ok(Ended::Faulted(Fault::Editor(_)))))]
#[inline]
pub fn run(spelling: Spelling) -> io::Result<Ended>
{
    let ended = match ratatui::try_init() {
        Ok(mut terminal) => drive(&mut terminal, &mut Keyboard, spelling),
        Err(error) => Err(error),
    };
    let restored = ratatui::try_restore();
    match (ended, restored) {
        (Ok(ended), Ok(())) => Ok(ended),
        (Err(error), _) | (Ok(_), Err(error)) => Err(error),
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
/// - witness: `tests::launch::the_smoke_face_propagates_a_partial_write_failure`
#[spec(ensures: |ref ret| matches!(
    *ret, Err(_) | Ok(Ended::Completed | Ended::Faulted(Fault::Grammar(_)))
))]
#[inline]
pub fn run_smoke<Output>(output: &mut Output) -> io::Result<Ended>
where
    Output: Write,
{
    let Ok(mut terminal) = Terminal::new(TestBackend::new(80, 24));
    let Ok(ended) = drive(&mut terminal, &mut Leave, Spelling::Unicode);
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
