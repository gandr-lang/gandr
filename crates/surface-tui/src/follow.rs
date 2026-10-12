//! The side view: a render-bus client that follows the document the hub
//! checked last and shows its cards, beside an editor that shows the text.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use std::io;
use std::io::BufRead;
use std::io::Write;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;

use anodized::spec;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::DocumentUri;
use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::MarkKind;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::ReportView;
use gandr_surface_render_remote::SourceText;
use gandr_surface_render_remote::pos_of_byte;
use gandr_surface_repl::Ended;
use gandr_surface_repl::Fault;
use ratatui::Frame;
use ratatui::Terminal;
use ratatui::backend::Backend;
use ratatui::layout::Constraint;
use ratatui::layout::Layout;
use ratatui::style::Color;
use ratatui::style::Style;
use ratatui::text::Line;
use ratatui::widgets::Block;
use ratatui::widgets::Paragraph;

use crate::app::Key;
use crate::run::Input;
use crate::run::InputSource as _;
use crate::run::Keyboard;
use crate::theme::style_of_kind;

/// The status line's style.
const STATUS: Style = Style::new().fg(Color::DarkGray);

/// The status line.
const FOLLOWING: &str = "following the document the hub checked last · q or Esc leaves";

/// What the side view knows: the last report of each document it heard, and
/// which one the hub checked last.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Following
{
    /// The last report heard for each document, with the version it reports.
    reports: BTreeMap<DocumentUri, (DocId, ReportView)>,
    /// The document whose report arrived last.
    latest: Option<DocumentUri>,
}

/// What hearing a frame leaves the view to do.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Heard
{
    /// Draw and wait for the next frame.
    Continue,
    /// The hub closed the bus.
    Detached,
}

/// One row of the side view: its kind, which styles it, and its text.
pub type Row = (OutKind, String);

impl Following
{
    /// Take in `frame`, one the hub sent.
    ///
    /// # Specification
    /// - requires: nothing; any frame is admissible input.
    /// - ensures: a report replaces the one held for its document and makes
    ///   that document the one followed; a detach answers [`Heard::Detached`]
    ///   and changes nothing; a greeting and a resync change nothing.
    /// - provides: the view's one update step.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reports of two documents, one after the other, leave
    ///   the second followed; a newer report of the first follows it again with
    ///   its new version; a detach is reported.
    /// - witness: `follow::tests::the_view_follows_the_document_checked_last`
    #[spec(ensures: |ret| matches!(ret, Heard::Continue | Heard::Detached))]
    #[inline]
    pub fn hear(
        &mut self,
        frame: &RenderFrame,
    ) -> Heard
    {
        match (frame.scope(), frame.body()) {
            | (&FrameScope::Document(ref document), &FrameBody::Frame { ref report }) => {
                drop(
                    self.reports
                        .insert(document.uri.clone(), (document.clone(), report.clone())),
                );
                self.latest = Some(document.uri.clone());
                Heard::Continue
            },
            | (_, &FrameBody::Detach) => Heard::Detached,
            | (_, &(FrameBody::Hello { .. } | FrameBody::Frame { .. } | FrameBody::Resync)) => {
                Heard::Continue
            },
        }
    }

    /// The rows of the document followed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: before any report, one line saying the view waits. Otherwise
    ///   a heading naming the document, its version and how many cards and
    ///   holes it carries; then each card's first line, at its one-based
    ///   `row:column` (`-` for a card placed nowhere) and after its code in
    ///   brackets when the code is the registry's own, as a diagnostic, its
    ///   further lines indented under it, and each step of its derivation as an
    ///   indented note; then each hole's message at its position, as a goal.
    /// - provides: the one layout the terminal and a pipe both show.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report with a placed card, an unplaced card with a
    ///   registry code and a hole lays out as exact rows; the empty view waits.
    /// - witness: `follow::tests::a_report_lays_out_its_cards_and_holes`
    #[spec(ensures: |ret| !ret.is_empty())]
    #[must_use]
    #[inline]
    pub fn rows(&self) -> Vec<Row>
    {
        let Some(followed) = self.latest.as_ref().and_then(|uri| self.reports.get(uri))
        else {
            return Vec::from([(
                OutKind::Info,
                String::from("waiting for the hub to check a document"),
            )]);
        };
        let (document, report) = (&followed.0, &followed.1);
        let holes = report
            .marks
            .iter()
            .filter(|mark| mark.kind == MarkKind::EmptyHole);
        let source = SourceText::from(report.source.as_str());
        let at = |start| {
            pos_of_byte(source, start).map_or_else(
                |_| String::from("-"),
                |pos| {
                    alloc::format!(
                        "{}:{}",
                        usize::from(pos.row).saturating_add(1),
                        usize::from(pos.col).saturating_add(1)
                    )
                },
            )
        };
        let counted = |count: usize, noun| {
            if count == 1 {
                alloc::format!("1 {noun}")
            }
            else {
                alloc::format!("{count} {noun}s")
            }
        };
        let mut rows = Vec::from([(
            OutKind::Info,
            alloc::format!(
                "{} at version {}: {}, {}",
                document.uri,
                i32::from(document.version),
                counted(report.diagnostics.len(), "diagnostic"),
                counted(holes.clone().count(), "hole")
            ),
        )]);
        for card in &report.diagnostics {
            let place = card
                .span
                .map_or_else(|| String::from("-"), |span| at(span.start()));
            let mut lines = card.message.lines();
            let code = if card.code == DiagnosticCode::Other {
                String::new()
            }
            else {
                alloc::format!("[{}] ", card.code)
            };
            rows.push((
                OutKind::Diag,
                alloc::format!("{place} {code}{}", lines.next().unwrap_or_default()),
            ));
            rows.extend(lines.map(|line| (OutKind::Diag, alloc::format!("    {line}"))));
            rows.extend(
                card.chain
                    .iter()
                    .map(|step| (OutKind::Info, alloc::format!("    · {step}"))),
            );
        }
        rows.extend(holes.map(|hole| {
            (
                OutKind::Goal,
                alloc::format!("{} {}", at(hole.range.start()), hole.message),
            )
        }));
        rows
    }
}

/// What the side view's loop acts on next.
#[derive(Debug)]
pub enum Seen
{
    /// A frame the hub sent.
    Frame(RenderFrame),
    /// An input from the terminal.
    Input(Input),
    /// The hub's stream ended, or sent a line that is not a frame.
    Closed,
}

/// Draw `following` onto `frame`: its rows in one pane, then a status line.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the pane, titled ` gandr view `, paints the first rows of
///   [`Following::rows`] that fit, each in its kind's style; the status line
///   says what is followed and how to leave.
/// - provides: the side view's one paint.
/// - fails: never.
/// - panics: none.
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure. Backend
///   witnesses observe the paint.
///
/// # Adequacy
/// - hypothesis: L3 — a scripted bus paints the waiting line, then a report's
///   heading and card, observed through backend cells.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
#[inline]
pub fn draw_following(
    frame: &mut Frame<'_>,
    following: &Following,
)
{
    let [pane, status] =
        Layout::vertical([Constraint::Min(3), Constraint::Length(1)]).areas(frame.area());
    let lines: Vec<Line<'_>> = following
        .rows()
        .into_iter()
        .map(|(kind, text)| Line::styled(text, style_of_kind(kind)))
        .collect();
    frame.render_widget(
        Paragraph::new(lines).block(Block::bordered().title(" gandr view ")),
        pane,
    );
    frame.render_widget(Paragraph::new(FOLLOWING).style(STATUS), status);
}

/// Run the side view over `terminal`, acting on what `seen` delivers, until
/// the hub closes the bus or the user leaves.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the view is drawn before every wait. A frame goes through
///   [`Following::hear`]; a detach, the end of the hub's stream, a quit, an
///   interrupt or `q` complete the view; a failed input ends it faulted; every
///   other input redraws. A channel with no sender left completes the view.
/// - provides: the side view's event loop, the same on the terminal and under a
///   test's scripted bus.
/// - fails: the backend's error when a frame cannot be drawn.
/// - panics: none.
/// - executable: none — neither the channel nor the backend exposes what was
///   consumed or painted to a predicate.
///
/// # Errors
/// The backend's error when a frame cannot be drawn.
///
/// # Adequacy
/// - hypothesis: L3 — a scripted bus of a greeting, a report and a quit paints
///   the report and completes; a detach completes.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
#[inline]
pub fn drive_following<Screen>(
    terminal: &mut Terminal<Screen>,
    seen: &Receiver<Seen>,
) -> Result<Ended, Screen::Error>
where
    Screen: Backend,
{
    let mut following = Following::default();
    loop {
        let _frame = terminal.draw(|frame| draw_following(frame, &following))?;
        match seen.recv() {
            | Ok(Seen::Frame(frame)) => {
                if following.hear(&frame) == Heard::Detached {
                    return Ok(Ended::Completed);
                }
            },
            | Ok(
                Seen::Input(Input::Key(Key::Quit | Key::Interrupt | Key::Char('q'))) | Seen::Closed,
            )
            | Err(_) => {
                return Ok(Ended::Completed);
            },
            | Ok(Seen::Input(Input::Failed(fault))) => return Ok(Ended::Faulted(fault)),
            | Ok(Seen::Input(
                Input::Redraw | Input::Key(Key::Char(_) | Key::Backspace | Key::Enter),
            )) => {},
        }
    }
}

/// Send every frame `reading` carries to `seen`, then [`Seen::Closed`].
///
/// # Specification
/// trivial.
fn frames<Reading>(
    reading: Reading,
    seen: &Sender<Seen>,
) where
    Reading: BufRead,
{
    for line in reading.lines() {
        let Ok(frame) = line.map(|line| serde_json::from_str::<RenderFrame>(&line))
        else {
            break;
        };
        let Ok(frame) = frame
        else {
            break;
        };
        if seen.send(Seen::Frame(frame)).is_err() {
            return;
        }
    }
    drop(seen.send(Seen::Closed));
}

/// Follow the render bus `reading` carries on the process's terminal until the
/// hub closes it or the user leaves, then send the hub a detach on `writing`.
///
/// # Specification
/// - requires: standard input and output are a terminal; `reading` and
///   `writing` are the two ends of a connection whose attach was sent.
/// - ensures: the terminal is put in raw mode on the alternate screen, the view
///   runs as [`drive_following`] states over the bus's frames and the
///   terminal's keys, and the terminal is restored on every ending.
/// - provides: `gandr view` on a terminal.
/// - fails: the terminal's error when it cannot be claimed, drawn on or
///   restored.
/// - panics: none.
/// - executable: none — the effects are the terminal's and a socket's.
///
/// # Errors
/// The terminal's error when it cannot be claimed, drawn on or restored.
///
/// # Adequacy
/// - hypothesis: L3 — the loop it runs is witnessed under a scripted bus; the
///   terminal setup and restore are `gandr tui`'s.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
#[inline]
pub fn follow<Reading, Writing>(
    reading: Reading,
    writing: &mut Writing,
) -> io::Result<Ended>
where
    Reading: BufRead + Send + 'static,
    Writing: Write,
{
    let (seen, inbox) = channel();
    let keys = seen.clone();
    drop(thread::spawn(move || frames(reading, &seen)));
    let ended = match ratatui::try_init() {
        | Ok(mut terminal) => {
            // The keyboard is read on its own thread, started once the
            // terminal is raw so crossterm's reader sees each key as it is
            // pressed; frames paint while no key is. The thread ends with the
            // process.
            drop(thread::spawn(move || {
                let mut keyboard = Keyboard;
                loop {
                    let input = keyboard.next();
                    let failed = matches!(input, Input::Failed(_));
                    if keys.send(Seen::Input(input)).is_err() || failed {
                        break;
                    }
                }
            }));
            drive_following(&mut terminal, &inbox)
        },
        | Err(error) => Err(error),
    };
    let restored = ratatui::try_restore();
    drop(detach(writing));
    match (ended, restored) {
        | (Ok(ended), Ok(())) => Ok(ended),
        | (Err(error), _) | (Ok(_), Err(error)) => Err(error),
    }
}

/// Send the hub a detach on `writing`.
///
/// # Specification
/// trivial.
fn detach<Writing>(writing: &mut Writing) -> io::Result<()>
where
    Writing: Write,
{
    let mut line = serde_json::to_string(&RenderFrame::detach()).map_err(io::Error::other)?;
    line.push('\n');
    writing.write_all(line.as_bytes())?;
    writing.flush()
}

/// Follow the render bus `reading` carries as plain text: after each report,
/// the followed document's rows to `output`, one per line, then a blank line.
///
/// # Specification
/// - requires: `reading` carries the bus's frames, one per line.
/// - ensures: each report is heard as [`Following::hear`] states and the rows
///   written and flushed at once; greetings and resyncs write nothing. The view
///   completes at a detach or the end of the stream, and ends faulted when a
///   line is not a frame or cannot be read.
/// - provides: `gandr view` when standard output is not a terminal.
/// - fails: the writer's error.
/// - panics: none.
/// - executable: none — `output` is written, not read back.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — two reports for one document print two blocks of rows,
///   each its version's, and a detach ends the view; the driver's own witness
///   runs it piped through a running hub.
/// - witness: `follow::tests::a_piped_view_prints_each_report`
#[inline]
pub fn follow_plain<Reading, Output>(
    reading: Reading,
    output: &mut Output,
) -> io::Result<Ended>
where
    Reading: BufRead,
    Output: Write,
{
    let mut following = Following::default();
    for line in reading.lines() {
        let line = match line {
            | Ok(line) => line,
            | Err(error) => return Ok(Ended::Faulted(Fault::Input(error))),
        };
        let frame = match serde_json::from_str::<RenderFrame>(&line) {
            | Ok(frame) => frame,
            | Err(error) => {
                return Ok(Ended::Faulted(Fault::Input(io::Error::new(
                    io::ErrorKind::InvalidData,
                    error,
                ))));
            },
        };
        let reported = matches!(*frame.body(), FrameBody::Frame { .. });
        if following.hear(&frame) == Heard::Detached {
            break;
        }
        if reported {
            for (_kind, row) in following.rows() {
                writeln!(output, "{row}")?;
            }
            writeln!(output)?;
            output.flush()?;
        }
    }
    Ok(Ended::Completed)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::sync::mpsc::channel;

    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::DiagCard;
    use gandr_surface_render_remote::DiagnosticCode;
    use gandr_surface_render_remote::DocId;
    use gandr_surface_render_remote::DocVersion;
    use gandr_surface_render_remote::DocumentUri;
    use gandr_surface_render_remote::MarkKind;
    use gandr_surface_render_remote::MarkSpan;
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_render_remote::RenderFrame;
    use gandr_surface_render_remote::ReportView;
    use gandr_surface_repl::Ended;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;

    use super::Following;
    use super::Heard;
    use super::Seen;
    use super::drive_following;
    use super::follow_plain;
    use crate::app::Key;
    use crate::run::Input;

    /// The document `name` at `version`.
    ///
    /// # Specification
    /// trivial.
    fn document(
        name: &DocumentUri,
        version: DocVersion,
    ) -> DocId
    {
        DocId {
            uri: name.clone(),
            version,
        }
    }

    /// The byte range `[start, end)`.
    ///
    /// # Specification
    /// trivial.
    fn bytes(
        start: ByteOffset,
        end: ByteOffset,
    ) -> ByteRange
    {
        ByteRange::new(start, end).expect("an ordered range")
    }

    /// A report over `def f : Integer ;\ndef f = "one" ;\ndef g = ?gap ;\n`:
    /// a refusal at the literal with one derivation step, an unplaced fault
    /// under a registry code, and a hole.
    ///
    /// # Specification
    /// trivial.
    fn refused() -> ReportView
    {
        let source = "def f : Integer ;\ndef f = \"one\" ;\ndef g = ?gap ;\n";
        let literal = source.find("\"one\"").expect("the literal");
        let hole = source.find("?gap").expect("the hole");
        ReportView {
            source: String::from(source),
            diagnostics: Vec::from([
                DiagCard {
                    code: DiagnosticCode::Other,
                    message: String::from("[type-mismatch] mismatched types\nexpected `Integer`"),
                    span: Some(bytes(
                        ByteOffset::from(literal),
                        ByteOffset::from(literal.saturating_add(5_usize)),
                    )),
                    expr: None,
                    elaboration: None,
                    chain: Vec::from([String::from("the type it is checked against")]),
                },
                DiagCard {
                    code: DiagnosticCode::ParseRepair,
                    message: String::from("parse repaired"),
                    span: None,
                    expr: None,
                    elaboration: None,
                    chain: Vec::new(),
                },
            ]),
            marks: Vec::from([MarkSpan {
                range: bytes(
                    ByteOffset::from(hole),
                    ByteOffset::from(hole.saturating_add(4_usize)),
                ),
                kind: MarkKind::EmptyHole,
                message: String::from("goal ?gap : Integer"),
            }]),
            ..ReportView::default()
        }
    }

    #[test]
    fn the_view_follows_the_document_checked_last()
    {
        let (a, b) = (
            DocumentUri::from(String::from("file:///a.gandr")),
            DocumentUri::from(String::from("file:///b.gandr")),
        );
        let mut following = Following::default();
        let heading = |following: &Following| following.rows()[0].1.clone();
        assert_eq!(
            following.hear(&RenderFrame::hello(Vec::from([document(
                &a,
                DocVersion::from(1_i32)
            )]))),
            Heard::Continue
        );
        assert!(
            heading(&following).starts_with("waiting"),
            "a greeting reports nothing"
        );
        for (uri, version) in [(&a, 1_i32), (&b, 4_i32)] {
            assert_eq!(
                following.hear(&RenderFrame::frame(
                    document(uri, DocVersion::from(version)),
                    ReportView::default()
                )),
                Heard::Continue
            );
        }
        assert!(
            heading(&following).starts_with("file:///b.gandr at version 4"),
            "the second report is followed"
        );
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&a, DocVersion::from(2_i32)),
                ReportView::default(),
            )),
            Heard::Continue
        );
        assert!(
            heading(&following).starts_with("file:///a.gandr at version 2"),
            "a newer report of the first document follows it again"
        );
        assert_eq!(following.hear(&RenderFrame::detach()), Heard::Detached);
    }

    #[test]
    fn a_report_lays_out_its_cards_and_holes()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut following = Following::default();
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            )),
            Heard::Continue
        );
        assert_eq!(following.rows(), [
            (
                OutKind::Info,
                String::from("file:///a.gandr at version 3: 2 diagnostics, 1 hole")
            ),
            (
                OutKind::Diag,
                String::from("2:9 [type-mismatch] mismatched types")
            ),
            (OutKind::Diag, String::from("    expected `Integer`")),
            (
                OutKind::Info,
                String::from("    · the type it is checked against")
            ),
            (OutKind::Diag, String::from("- [W0012] parse repaired")),
            (OutKind::Goal, String::from("3:9 goal ?gap : Integer")),
        ]);
    }

    #[test]
    fn the_view_paints_what_the_bus_sends()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let (seen, inbox) = channel();
        for event in [
            Seen::Frame(RenderFrame::hello(Vec::new())),
            Seen::Frame(RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            )),
            Seen::Input(Input::Redraw),
            Seen::Input(Input::Key(Key::Char('x'))),
            Seen::Input(Input::Key(Key::Char('q'))),
            Seen::Frame(RenderFrame::detach()),
        ] {
            seen.send(event).expect("the loop listens");
        }
        let mut terminal = Terminal::new(TestBackend::new(64_u16, 10_u16)).expect("a test backend");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Completed)
        ));
        let buffer = terminal.backend().buffer();
        let screen: Vec<String> = (buffer.area.top() .. buffer.area.bottom())
            .map(|y| {
                (buffer.area.left() .. buffer.area.right())
                    .map(|x| buffer[(x, y)].symbol())
                    .collect()
            })
            .collect();
        assert!(screen[0].contains(" gandr view "), "{screen:#?}");
        assert!(
            screen[1].contains("file:///a.gandr at version 3: 2 diagnostics, 1 hole"),
            "{screen:#?}"
        );
        assert!(
            screen[2].contains("2:9 [type-mismatch] mismatched types"),
            "{screen:#?}"
        );
        assert!(screen[9].starts_with("following"), "{screen:#?}");
        assert!(
            inbox
                .try_recv()
                .is_ok_and(|event| matches!(event, Seen::Frame(_))),
            "the quit ends the loop before the detach is read"
        );
    }

    #[test]
    fn a_piped_view_prints_each_report()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut bus = String::new();
        for frame in [
            RenderFrame::hello(Vec::from([document(&uri, DocVersion::from(1_i32))])),
            RenderFrame::frame(document(&uri, DocVersion::from(1_i32)), refused()),
            RenderFrame::frame(
                document(&uri, DocVersion::from(2_i32)),
                ReportView::default(),
            ),
            RenderFrame::detach(),
            RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                ReportView::default(),
            ),
        ] {
            bus.push_str(&serde_json::to_string(&frame).expect("a frame encodes"));
            bus.push('\n');
        }
        let mut output = Vec::new();
        assert!(matches!(
            follow_plain(bus.as_bytes(), &mut output),
            Ok(Ended::Completed)
        ));
        let printed = String::from_utf8(output).expect("the rows are text");
        assert_eq!(
            printed
                .split("\n\n")
                .map(|report| report.lines().next().unwrap_or_default())
                .collect::<Vec<_>>(),
            [
                "file:///a.gandr at version 1: 2 diagnostics, 1 hole",
                "file:///a.gandr at version 2: 0 diagnostics, 0 holes",
                ""
            ],
            "each report prints once, and nothing after the detach"
        );
        let mut garbled = Vec::new();
        assert!(matches!(
            follow_plain(&b"not a frame\n"[..], &mut garbled),
            Ok(Ended::Faulted(_))
        ));
    }
}
