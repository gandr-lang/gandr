//! The terminal face over the read-evaluate loop.
//!
//! An [`App`] holds one `gandr-surface-repl` loop, the line being edited, the
//! lines the loop holds for the parser, and every transcript block the loop
//! answered. [`draw`] paints it full-screen: the transcript pane lays each
//! block out as the loop's rows, the same rows the plain transcript prints,
//! and styles them through [`style_of`], total over the highlight roles, and
//! [`style_of_kind`], total over the line kinds; the input pane holds the
//! waiting lines and the line; a status line says what the keys do.
//!
//! # One loop, three ways to drive it
//!
//! [`drive`] is the event loop: draw, read an [`Input`], apply it. [`run()`]
//! drives it over the terminal's keys in raw mode on the alternate screen;
//! [`run_smoke`] drives it once on a headless backend and prints
//! [`SMOKE_NOTE`]; a test drives it over scripted keys. The face parses,
//! lowers, types and marks nothing: every line goes to the loop, and every
//! block it paints is the loop's.
//!
//! The face owns no part of the loop. Each Enter offers the edited line to
//! `SessionLoop::offer` and acts on its `LoopEvent`: a block joins the
//! transcript, a line the parser waits on stays visible in the input pane until
//! the block arrives, and `:quit` leaves. The loop keeps the buffer and the
//! accepted text, decides completeness, submits to the session, and encodes the
//! block; the face keeps a copy of the waiting lines only to show them, and
//! drops it with the loop's buffer on an interrupt. The layout of a block is
//! the loop's `rows`, which `write_block` also prints, so the face draws the
//! same marks and indents as a pipe.
//!
//! Each submitted line is unterminated, as `SessionLoop::offer` requires;
//! `App::handle` states that precondition for Enter. The waiting lines are
//! display state, not input to offer again. Buffering and resubmitting a whole
//! accumulated source would duplicate pending text and decide completeness
//! outside the shared loop. That alternative becomes appropriate only if the
//! loop changes to accept whole buffers.
//!
//! # The side view
//!
//! [`follow()`] attaches nothing itself: given the two ends of a connection to
//! the engine hub's render bus, it follows the document the hub checked last
//! and paints its cards — each diagnostic at its row and column with its
//! derivation, each hole with its goal — beside an editor that shows the
//! text; [`follow_plain`] prints the same rows to a pipe after each report.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! **Choice.** `gandr view` attaches to the render bus of the workspace's hub
//! and shows what an editor cannot: every diagnostic of the document the hub
//! checked last, each at its one-based row and column with its further lines
//! and its derivation, then each hole with its goal, under a heading naming the
//! document, its version and the counts. The view follows whichever document's
//! report arrived last, so it moves with the editor's focus without being told
//! where the cursor is. It is a renderer and nothing more: the reports are the
//! hub's, read off the diagnostics the editor already shows, and
//! `Following::rows` is the one layout the terminal pane and a pipe print. On a
//! terminal the frames are read on one thread and the keys on another, started
//! once the terminal is raw, both into the one channel `drive_following` waits
//! on, so a report paints while no key is pressed; `q`, Esc and Ctrl-C leave,
//! and leaving sends the hub a detach. Piped, each report prints as its rows
//! followed by a blank line, which is what the driver's witness reads.
//!
//! **Alternatives.** Following the cursor would need the editor to say where it
//! is, a request the protocol does not carry to a second client; following the
//! last check is what an author editing one document sees. Drawing the source
//! with its highlights and marks beside the cards would repeat the editor's own
//! pane; the report carries them for a renderer that has no editor. Polling the
//! hub would show a check late or ask for reports nothing changed; the bus
//! pushes each publication.
//!
//! **Reversal.** An editor extension that reports the focused document moves
//! the view onto it; a renderer with no editor beside it paints the source the
//! report carries.
//!
//! # A verb of the driver
//!
//! The face is reached as `gandr tui`, and its smoke face as `gandr tui
//! --smoke`, verbs of the `gandr` binary beside `check`, `test`, `lsp` and
//! `repl`; bare `gandr` keeps its status report. An explicit verb avoids
//! interpreting a verb as source input. The alternative, making the bare
//! command interactive, becomes appropriate only if the driver's command
//! contract changes.
//!
//! # Specification and evidence
//!
//! The crate specifies 32 nontrivial items: 23 executable predicates and 32
//! bounded adequacy arguments. Transparent accessors, the constant quit source
//! and the side view's frame reader and detach remain trivial. Predicates cover
//! editing transitions, style classifications, text conservation, coordinate
//! saturation, key precedence, fault provenance, the side view's following and
//! layout, and the test harness's transformations.
//!
//! Nine items need effect witnesses instead of predicates:
//!
//! - `draw`, `draw_transcript`, `draw_input` and `draw_following`: ratatui
//!   exposes the frame buffer only through a mutable borrow, which a
//!   predicate's `Fn` closure cannot take; frame cursor state has no getter.
//!   Tests observe the completed backend instead.
//! - `InputSource::next`: the abstract source has no pending-input or
//!   read-state observer.
//! - `drive` and `drive_following`: generic input and backend traits, and a
//!   channel, expose no immutable queue or painted-state observer, and supplied
//!   faults may be arbitrary.
//! - `follow` and `follow_plain`: their effects are a terminal's, a socket's
//!   and a writer's, none read back.
//!
//! The 25 terminal-free tests cover application transitions, complete style
//! classifications, Unicode and coordinate boundaries, malformed highlight
//! precedence, modifier handling, independent frame layouts, transcript
//! scrolling, failed-input termination, partial-write failure, and the side
//! view's following, layout, paint and piped rows. A 26th test,
//! `the_terminal_face_completes_and_restores_its_settings`, is opt-in because
//! it needs an attached terminal: it reads real quit keys and compares terminal
//! settings before and after. The two cursor/tail regression witnesses fail
//! without that clipping and pass with it. Wording-only and implementation-copy
//! checks are not evidence; the frame golden compares literal pane layout
//! rather than rebuilding the painter's algorithm. The side view on a real
//! terminal is exercised by `gandr view` beside an editor's session; the
//! driver's witness runs it piped.
//!
//! `cargo nextest run -p gandr-surface-tui` runs the terminal-free witnesses.
//! With `RUSTFLAGS='--cfg anodized_panic'`, it also executes their predicates.
//! To exercise the native input and terminal predicates, build the `launch`
//! test executable with that flag, then run it on a terminal with `--exact
//! tests::the_terminal_face_completes_and_restores_its_settings --ignored
//! --nocapture` and enter `:quit`. A public rendering probe covers empty panes,
//! wide and combining characters, and a 65,537-character input; `gandr tui
//! --smoke` exercises terminal-free launch. A real terminal session also
//! discards an incomplete definition, evaluates and queries an accepted
//! definition, quits through `:quit`, and restores terminal settings. Real
//! terminal failure injection and font-dependent glyph appearance remain
//! outside the deterministic test domain.
//!
//! # References
//!
//! - The ratatui developers. `ratatui` 0.30.2. <https://docs.rs/ratatui/0.30.2/ratatui/>
//!   — the layout, styled text, widgets, the headless test backend and the
//!   terminal setup the face draws through.
//! - Timon Post and the crossterm contributors. `crossterm` 0.29.0. <https://docs.rs/crossterm/0.29.0/crossterm/>
//!   — raw mode, the alternate screen and key events, reached through ratatui's
//!   re-export.

// Module documentation that predates the shape lint: 8 headings outside the
// vocabulary, 1 decision record and 3 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
extern crate alloc;

mod app;
mod follow;
mod run;
mod theme;
mod view;

pub use crate::app::App;
pub use crate::app::Handled;
pub use crate::app::Key;
pub use crate::follow::Following;
pub use crate::follow::Heard;
pub use crate::follow::Row;
pub use crate::follow::Seen;
pub use crate::follow::draw_following;
pub use crate::follow::drive_following;
pub use crate::follow::follow;
pub use crate::follow::follow_plain;
pub use crate::run::Input;
pub use crate::run::InputSource;
pub use crate::run::SMOKE_NOTE;
pub use crate::run::drive;
pub use crate::run::run;
pub use crate::run::run_smoke;
pub use crate::theme::style_of;
pub use crate::theme::style_of_kind;
pub use crate::view::draw;
