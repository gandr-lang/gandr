//! The side view: a render-bus client that follows the document the hub
//! checked last and shows its cards, beside an editor that shows the text.
//!
//! The view builds the frame of the document it follows
//! ([`Following::frame`]): one record that names the document, its version
//! and its counts, then one record per card and per hole. [`rendering`] lays
//! the frame out as the visual language's rendering data, which every rule of
//! `gandr_surface_render_remote::RULES` checks. A painter then puts the cells
//! on the terminal or on a pipe and adds nothing: a column is as wide as its
//! widest cell, one space parts two columns, and a hue takes the theme's
//! colour for its warrant.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use std::io;
use std::io::BufRead;
use std::io::Write;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;

use anodized::spec;
use gandr_surface_render_remote::Align;
use gandr_surface_render_remote::Attribute;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::Cell;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::Datum;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::DocumentUri;
use gandr_surface_render_remote::Field;
use gandr_surface_render_remote::FieldName;
use gandr_surface_render_remote::Frame;
use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::Head;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::MarkKind;
use gandr_surface_render_remote::Numeral;
use gandr_surface_render_remote::Pane;
use gandr_surface_render_remote::Place;
use gandr_surface_render_remote::Record;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::Rendering;
use gandr_surface_render_remote::ReportView;
use gandr_surface_render_remote::Revision;
use gandr_surface_render_remote::Row;
use gandr_surface_render_remote::SourceText;
use gandr_surface_render_remote::Unit;
use gandr_surface_render_remote::WARRANTS;
use gandr_surface_repl::Ended;
use gandr_surface_repl::Fault;
use ratatui::Terminal;
use ratatui::backend::Backend;
use ratatui::style::Modifier;
use ratatui::style::Style;
use ratatui::text::Line;
use ratatui::text::Span;
use ratatui::widgets::Paragraph;

use crate::app::Key;
use crate::run::Input;
use crate::run::InputSource as _;
use crate::run::Keyboard;
use crate::theme::hue_of_warrant;

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

/// One cell as a painter puts it on a line: its text, padded to its column's
/// width, and its style.
type Painted = (String, Style);

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
            (&FrameScope::Document(ref document), &FrameBody::Frame { ref report }) => {
                drop(
                    self.reports
                        .insert(document.uri.clone(), (document.clone(), report.clone())),
                );
                self.latest = Some(document.uri.clone());
                Heard::Continue
            },
            (_, &FrameBody::Detach) => Heard::Detached,
            (_, &(FrameBody::Hello { .. } | FrameBody::Frame { .. } | FrameBody::Resync)) => {
                Heard::Continue
            },
        }
    }

    /// The frame of the document followed: what the view shows, as named
    /// fields in the order it shows them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the empty frame before any report. Otherwise a frame at the
    ///   document's version. Its first record holds the document's `uri`, its
    ///   `version`, and the counts of its `diagnostics` and its `holes`. A
    ///   record per card follows: its one-based `span` (absent for a card
    ///   placed nowhere), its `code` (absent when the code is not the
    ///   registry's own), one `message` per line of its message, and one
    ///   `chain` per step of its derivation. A record per hole follows last:
    ///   its `span`, an absent `code` and its `message`. Each text is trimmed,
    ///   and an empty line or step is left out. A span is a row and a column,
    ///   both one-based. Rows end where the language server's rows end, and the
    ///   column counts characters.
    /// - provides: the one model that the terminal and a pipe both render.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report with a placed card, an unplaced card with a
    ///   registry code and a hole builds exact records, and the rendering of
    ///   those records breaks no rule; the empty view builds the empty frame.
    /// - witness: `follow::tests::a_report_lays_out_its_cards_and_holes`
    #[spec(ensures: |ret| ret.records.is_empty() == self.latest.is_none())]
    #[must_use]
    #[inline]
    pub fn frame(&self) -> Frame
    {
        let Some(&(ref document, ref report)) =
            self.latest.as_ref().and_then(|uri| self.reports.get(uri))
        else {
            return Frame::default();
        };
        let revision = Revision(i64::from(i32::from(document.version)));
        let field = |name: &'static str, datum: Datum| Field {
            name: FieldName::from(name),
            datum,
            revision,
        };
        let text = |line: &str| Datum::Text(String::from(line.trim()));
        let rows = LineIndex::new(SourceText::from(report.source.as_str()));
        let span = |start: ByteOffset| {
            let row = rows.row_of_byte(start);
            report
                .source
                .get(usize::from(rows.row_bytes(row).start()) .. usize::from(start))
                .map_or(Datum::Absent, |before| {
                    Datum::Text(spelled(format_args!(
                        "{}:{}",
                        usize::from(row).saturating_add(1),
                        before.chars().count().saturating_add(1)
                    )))
                })
        };
        let count = |count: usize| Datum::Count(Count(u64::try_from(count).unwrap_or(u64::MAX)));
        let holes = report
            .marks
            .iter()
            .filter(|mark| mark.kind == MarkKind::EmptyHole);
        let mut records = Vec::with_capacity(
            report
                .diagnostics
                .len()
                .saturating_add(report.marks.len())
                .saturating_add(1),
        );
        records.push(Record {
            fields: Vec::from([
                field(
                    "uri",
                    Datum::Text(spelled(format_args!("{}", document.uri))),
                ),
                field(
                    "version",
                    Datum::Text(spelled(format_args!("{}", i32::from(document.version)))),
                ),
                field("diagnostics", count(report.diagnostics.len())),
                field("holes", count(holes.clone().count())),
            ]),
        });
        for card in &report.diagnostics {
            let code = if card.code == DiagnosticCode::Other {
                Datum::Absent
            }
            else {
                Datum::Text(spelled(format_args!("{}", card.code)))
            };
            let mut fields = Vec::from([
                field(
                    "span",
                    card.span
                        .map_or(Datum::Absent, |placed| span(placed.start())),
                ),
                field("code", code),
            ]);
            fields.extend(
                card.message
                    .lines()
                    .filter(|line| !line.trim().is_empty())
                    .map(|line| field("message", text(line))),
            );
            fields.extend(
                card.chain
                    .iter()
                    .filter(|step| !step.trim().is_empty())
                    .map(|step| field("chain", text(step))),
            );
            records.push(Record { fields });
        }
        records.extend(holes.map(|hole| Record {
            fields: Vec::from([
                field("span", span(hole.range.start())),
                field("code", Datum::Absent),
                field("message", text(&hole.message)),
            ]),
        }));
        Frame { revision, records }
    }
}

/// The text `arguments` spell: each field of a frame owns its text.
///
/// # Specification
/// trivial.
fn spelled(arguments: fmt::Arguments<'_>) -> String
{
    alloc::fmt::format(arguments)
}

/// The side view's rendering of `frame`, a frame [`Following::frame`] builds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: nothing for the empty frame. Otherwise a pane of one row, which
///   draws each field of the first record as its name beside its datum. Then,
///   when more records follow, a pane under one head per field name that those
///   records use, in the order they first use it. Each record takes a row, and
///   a further row while one name holds more fields; each field sits in its
///   name's column. A text sits at the left and a count is a numeral at the
///   right; any other datum draws nothing, and the view's frame holds none. A
///   row that draws nothing is left out.
/// - provides: the one rendering that the terminal and a pipe both paint.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the rendering of a report with a placed card, an unplaced
///   card and a hole paints exact lines and breaks no rule of the visual
///   language; the driver's witness checks each frame a running hub sends for a
///   corpus source.
/// - witness: `follow::tests::a_report_lays_out_its_cards_and_holes`
#[spec(ensures: |ret| ret.panes.len() == frame.records.len().min(2))]
#[must_use]
#[inline]
pub fn rendering(frame: &Frame) -> Rendering
{
    let Some((first, rest)) = frame.records.split_first()
    else {
        return Rendering::default();
    };
    let value = |place: Place, datum: &Datum| match *datum {
        Datum::Text(ref text) => Cell::text(place, text.clone()),
        Datum::Count(count) => Cell::numeral(place, Numeral::from(count)),
        Datum::Absent
        | Datum::Duration(_)
        | Datum::Bytes(_)
        | Datum::Latency { .. }
        | Datum::Ratio { .. }
        | Datum::Samples(_)
        | Datum::Warrant(_)
        | Datum::Comparison { .. } => Cell {
            place: Some(place),
            ..Cell::blank()
        },
    };
    let mut labelled = Vec::with_capacity(first.fields.len().saturating_mul(2));
    for (index, field) in first.fields.iter().enumerate() {
        let place = Place {
            record: 0,
            field: index,
        };
        labelled.push(Cell::label(place, field.name));
        labelled.push(value(place, &field.datum));
    }
    let mut panes = Vec::from([Pane {
        heads: Vec::new(),
        rows: Vec::from([Row { cells: labelled }]),
    }]);
    if rest.is_empty() {
        return Rendering { panes };
    }
    let mut heads: Vec<Head> = Vec::new();
    let mut columns_of: BTreeMap<FieldName, usize> = BTreeMap::new();
    for field in rest.iter().flat_map(|record| &record.fields) {
        let counted = matches!(field.datum, Datum::Count(_)).then_some(Unit::Count);
        let column = *columns_of.entry(field.name).or_insert_with(|| {
            heads.push(Head {
                name: field.name,
                unit: None,
            });
            heads.len().saturating_sub(1)
        });
        if let Some(head) = heads.get_mut(column) {
            head.unit = head.unit.or(counted);
        }
    }
    // The fields of each column for the record at hand, kept across records.
    let mut columns: Vec<Vec<usize>> = heads.iter().map(|_| Vec::new()).collect();
    let mut rows = Vec::with_capacity(rest.len());
    for (offset, record) in rest.iter().enumerate() {
        columns.iter_mut().for_each(Vec::clear);
        for (index, field) in record.fields.iter().enumerate() {
            if let Some(column) = columns_of
                .get(&field.name)
                .and_then(|&column| columns.get_mut(column))
            {
                column.push(index);
            }
        }
        let depth = columns.iter().map(Vec::len).max().unwrap_or_default();
        for line in 0 .. depth {
            let cells: Vec<Cell> = columns
                .iter()
                .map(|column| {
                    column
                        .get(line)
                        .and_then(|&index| {
                            let place = Place {
                                record: offset.saturating_add(1),
                                field: index,
                            };
                            record
                                .fields
                                .get(index)
                                .map(|field| value(place, &field.datum))
                        })
                        .unwrap_or_else(Cell::blank)
                })
                .collect();
            if cells
                .iter()
                .any(|cell| !cell.text.is_empty() || cell.numeral.is_some())
            {
                rows.push(Row { cells });
            }
        }
    }
    panes.push(Pane { heads, rows });
    Rendering { panes }
}

/// The lines a painter puts down for `rendering`: each pane's heads when it
/// has any, then its rows; each cell padded to its column's width, with the
/// style its attributes name. A head shows its field's name and its unit, and
/// a cell shows its glyph and its text.
///
/// # Specification
/// trivial.
fn laid(rendering: &Rendering) -> Vec<Vec<Painted>>
{
    let measured = |text: &str| Span::raw(text).width();
    let joined = |first: &str, second: &str| {
        let parted = !first.is_empty() && !second.is_empty();
        measured(first)
            .saturating_add(usize::from(parted))
            .saturating_add(measured(second))
    };
    let padded = |first: &str, second: &str, width: usize, align: Align| {
        let gap = width.saturating_sub(joined(first, second));
        let mut padded = String::with_capacity(
            first
                .len()
                .saturating_add(second.len())
                .saturating_add(gap)
                .saturating_add(1),
        );
        if align == Align::Right {
            padded.extend(core::iter::repeat_n(' ', gap));
        }
        padded.push_str(first);
        if !first.is_empty() && !second.is_empty() {
            padded.push(' ');
        }
        padded.push_str(second);
        if align == Align::Left {
            padded.extend(core::iter::repeat_n(' ', gap));
        }
        padded
    };
    let head = |head: &Head| {
        let align = if head.unit.is_some() {
            Align::Right
        }
        else {
            Align::Left
        };
        (
            <&str>::from(head.name),
            head.unit.map_or("", <&str>::from),
            align,
        )
    };
    let mut lines = Vec::new();
    let mut widths: Vec<usize> = Vec::new();
    for pane in &rendering.panes {
        widths.clear();
        let drawn = pane
            .heads
            .iter()
            .map(|held| {
                let (name, unit, _) = head(held);
                joined(name, unit)
            })
            .enumerate()
            .chain(pane.rows.iter().flat_map(|row| {
                row.cells
                    .iter()
                    .map(|held| joined(held.glyph.map_or("", <&str>::from), &held.text))
                    .enumerate()
            }));
        for (column, width) in drawn {
            if widths.len() <= column {
                widths.resize(column.saturating_add(1), 0);
            }
            if let Some(widest) = widths.get_mut(column) {
                *widest = (*widest).max(width);
            }
        }
        let width = |column: usize| widths.get(column).copied().unwrap_or_default();
        if !pane.heads.is_empty() {
            lines.push(
                pane.heads
                    .iter()
                    .enumerate()
                    .map(|(column, held)| {
                        let (name, unit, align) = head(held);
                        (padded(name, unit, width(column), align), Style::new())
                    })
                    .collect(),
            );
        }
        lines.extend(pane.rows.iter().map(|row| {
            row.cells
                .iter()
                .enumerate()
                .map(|(column, held)| {
                    (
                        padded(
                            held.glyph.map_or("", <&str>::from),
                            &held.text,
                            width(column),
                            held.align,
                        ),
                        painted(held),
                    )
                })
                .collect()
        }));
    }
    lines
}

/// The terminal style `cell`'s attributes name: a hue as the theme's colour
/// for its warrant, and the bold and italic weights. The rules refuse every
/// other attribute, so the painter has no paint for it.
///
/// # Specification
/// trivial.
fn painted(cell: &Cell) -> Style
{
    cell.attributes
        .iter()
        .fold(Style::new(), |style, attribute| match *attribute {
            Attribute::Hue(colour) => WARRANTS
                .iter()
                .find(|warrant| warrant.colour() == colour)
                .map_or(style, |&warrant| style.fg(hue_of_warrant(warrant))),
            Attribute::Bold => style.add_modifier(Modifier::BOLD),
            Attribute::Italic => style.add_modifier(Modifier::ITALIC),
            Attribute::Faint
            | Attribute::Opacity
            | Attribute::Background(_)
            | Attribute::Border
            | Attribute::Blink => style,
        })
}

/// The lines of `rendering` as plain text: the cells of a line parted by one
/// space, with no space at the end.
///
/// # Specification
/// trivial.
fn printed(rendering: &Rendering) -> Vec<String>
{
    laid(rendering)
        .into_iter()
        .map(|line| {
            let mut text = String::new();
            for (column, (piece, _)) in line.into_iter().enumerate() {
                if column > 0 {
                    text.push(' ');
                }
                text.push_str(&piece);
            }
            text.truncate(text.trim_end().len());
            text
        })
        .collect()
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

/// Draw `following` onto `screen`: the rendering of its frame, line by line.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first lines of [`rendering`] of [`Following::frame`] that fit
///   are painted from the top, each cell in the style its attributes name, as a
///   pipe prints them; nothing else is painted.
/// - provides: the side view's one paint.
/// - fails: never.
/// - panics: none.
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure. Backend
///   witnesses observe the paint.
///
/// # Adequacy
/// - hypothesis: L3 — a scripted bus paints nothing before a report, then the
///   report's lines exactly as a pipe prints them, observed through backend
///   cells.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
#[inline]
pub fn draw_following(
    screen: &mut ratatui::Frame<'_>,
    following: &Following,
)
{
    let lines: Vec<Line<'_>> = laid(&rendering(&following.frame()))
        .into_iter()
        .map(|line| {
            let mut spans = Vec::with_capacity(line.len().saturating_mul(2));
            for (column, (text, style)) in line.into_iter().enumerate() {
                if column > 0 {
                    spans.push(Span::raw(" "));
                }
                spans.push(Span::styled(text, style));
            }
            Line::from(spans)
        })
        .collect();
    screen.render_widget(Paragraph::new(lines), screen.area());
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
            Ok(Seen::Frame(frame)) => {
                if following.hear(&frame) == Heard::Detached {
                    return Ok(Ended::Completed);
                }
            },
            Ok(
                Seen::Input(Input::Key(Key::Quit | Key::Interrupt | Key::Char('q'))) | Seen::Closed,
            )
            | Err(_) => {
                return Ok(Ended::Completed);
            },
            Ok(Seen::Input(Input::Failed(fault))) => return Ok(Ended::Faulted(fault)),
            Ok(Seen::Input(
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
/// - hypothesis: L3 — the loop it runs is witnessed under a scripted bus. On a
///   pseudo-terminal on Linux, a bus the hub has already closed completes the
///   view, sends one detach line, and leaves the terminal's settings as they
///   were.
/// - witness: `follow::tests::the_view_paints_what_the_bus_sends`
/// - witness: `tests::terminal::the_side_view_claims_and_restores_a_terminal`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the frame reader and the keyboard reader each block on their input for the view's life"
    )
)]
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
        Ok(mut terminal) => {
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
        Err(error) => Err(error),
    };
    let restored = ratatui::try_restore();
    drop(detach(writing));
    match (ended, restored) {
        (Ok(ended), Ok(())) => Ok(ended),
        (Err(error), _) | (Ok(_), Err(error)) => Err(error),
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
/// the lines of the followed document's rendering to `output`, then a blank
/// line.
///
/// # Specification
/// - requires: `reading` carries the bus's frames, one per line.
/// - ensures: each report is heard as [`Following::hear`] states, and the lines
///   of [`rendering`] of [`Following::frame`] are written and flushed at once,
///   each cell padded to its column and parted from the next by one space;
///   greetings and resyncs write nothing. The view completes at a detach or the
///   end of the stream, and ends faulted when a line is not a frame or cannot
///   be read.
/// - provides: `gandr view` when standard output is not a terminal.
/// - fails: the writer's error.
/// - panics: none.
/// - executable: none — `output` is written, not read back.
///
/// # Errors
/// The writer's error.
///
/// # Adequacy
/// - hypothesis: L3 — two reports for one document print two blocks of lines,
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
            Ok(line) => line,
            Err(error) => return Ok(Ended::Faulted(Fault::Input(error))),
        };
        let frame = match serde_json::from_str::<RenderFrame>(&line) {
            Ok(frame) => frame,
            Err(error) => {
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
            for shown in printed(&rendering(&following.frame())) {
                writeln!(output, "{shown}")?;
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
    use std::io;
    use std::sync::mpsc::channel;

    use gandr_surface_render_remote::Breach;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::Datum;
    use gandr_surface_render_remote::DiagCard;
    use gandr_surface_render_remote::DiagnosticCode;
    use gandr_surface_render_remote::DocId;
    use gandr_surface_render_remote::DocVersion;
    use gandr_surface_render_remote::DocumentUri;
    use gandr_surface_render_remote::MarkKind;
    use gandr_surface_render_remote::MarkSpan;
    use gandr_surface_render_remote::RenderFrame;
    use gandr_surface_render_remote::ReportView;
    use gandr_surface_render_remote::Shown;
    use gandr_surface_render_remote::conform;
    use gandr_surface_repl::Ended;
    use gandr_surface_repl::Fault;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;

    use super::Following;
    use super::Heard;
    use super::Seen;
    use super::detach;
    use super::drive_following;
    use super::follow_plain;
    use super::frames;
    use super::printed;
    use super::rendering;
    use crate::app::Key;
    use crate::run::Input;

    /// The lines the view prints for `following`.
    ///
    /// # Specification
    /// trivial.
    fn lines(following: &Following) -> Vec<String>
    {
        printed(&rendering(&following.frame()))
    }

    /// The rules that the rendering of `following`'s frame breaks, after the
    /// frame and the rendering of `before`.
    ///
    /// # Specification
    /// trivial.
    fn breaches(
        following: &Following,
        before: &Following,
    ) -> Vec<Breach>
    {
        let (frame, earlier) = (following.frame(), before.frame());
        conform(&Shown {
            frame: &frame,
            rendering: &rendering(&frame),
            before: Some((&earlier, &rendering(&earlier))),
        })
    }

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
        let heading = |following: &Following| lines(following).first().cloned();
        assert_eq!(
            following.hear(&RenderFrame::hello(Vec::from([document(
                &a,
                DocVersion::from(1_i32)
            )]))),
            Heard::Continue
        );
        assert_eq!(
            heading(&following),
            None,
            "a greeting reports nothing, and an empty frame draws nothing"
        );
        for (uri, version) in [(&a, 1_i32), (&b, 4_i32)] {
            let before = following.clone();
            assert_eq!(
                following.hear(&RenderFrame::frame(
                    document(uri, DocVersion::from(version)),
                    ReportView::default()
                )),
                Heard::Continue
            );
            assert_eq!(breaches(&following, &before), []);
        }
        assert_eq!(
            heading(&following).as_deref(),
            Some("uri file:///b.gandr version 4 diagnostics 0 holes 0"),
            "the second report is followed"
        );
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&a, DocVersion::from(2_i32)),
                ReportView::default(),
            )),
            Heard::Continue
        );
        assert_eq!(
            heading(&following).as_deref(),
            Some("uri file:///a.gandr version 2 diagnostics 0 holes 0"),
            "a newer report of the first document follows it again"
        );
        assert_eq!(following.hear(&RenderFrame::detach()), Heard::Detached);
    }

    #[test]
    fn a_report_lays_out_its_cards_and_holes()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut following = Following::default();
        let before = following.clone();
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            )),
            Heard::Continue
        );
        assert_eq!(lines(&following), [
            "uri file:///a.gandr version 3 diagnostics 2 holes 1",
            "span code  message                          chain",
            "2:9        [type-mismatch] mismatched types the type it is checked against",
            "           expected `Integer`",
            "     W0012 parse repaired",
            "3:9        goal ?gap : Integer",
        ]);
        assert_eq!(
            breaches(&following, &before),
            [],
            "the layout keeps every rule of the visual language"
        );
    }

    #[test]
    fn a_hole_inside_a_character_is_placed_nowhere()
    {
        let uri = DocumentUri::from(String::from("file:///a.gandr"));
        let mut following = Following::default();
        let source = "def é = ?gap ;\n";
        let inside = source
            .find('é')
            .expect("the letter")
            .saturating_add(1_usize);
        let report = ReportView {
            source: String::from(source),
            marks: Vec::from([MarkSpan {
                range: bytes(
                    ByteOffset::from(inside),
                    ByteOffset::from(inside.saturating_add(4_usize)),
                ),
                kind: MarkKind::EmptyHole,
                message: String::from("goal ?gap : Integer"),
            }]),
            ..ReportView::default()
        };
        assert_eq!(
            following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(1_i32)),
                report,
            )),
            Heard::Continue
        );
        assert_eq!(
            following
                .frame()
                .records
                .get(1)
                .and_then(|hole| hole.fields.first())
                .map(|span| &span.datum),
            Some(&Datum::Absent)
        );
        assert_eq!(
            lines(&following).last().map(String::as_str),
            Some("          goal ?gap : Integer")
        );
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
        let piped = lines(&{
            let mut following = Following::default();
            let _heard = following.hear(&RenderFrame::frame(
                document(&uri, DocVersion::from(3_i32)),
                refused(),
            ));
            following
        });
        assert_eq!(
            screen
                .iter()
                .map(|line| String::from(line.trim_end()))
                .collect::<Vec<_>>(),
            piped
                .iter()
                .map(|line| {
                    let mut fitted: String = line.chars().take(64).collect();
                    fitted.truncate(fitted.trim_end().len());
                    fitted
                })
                .chain(core::iter::repeat_n(
                    String::new(),
                    10_usize.saturating_sub(piped.len())
                ))
                .collect::<Vec<_>>(),
            "the terminal paints what a pipe prints, and nothing else"
        );
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
        let printed = String::from_utf8(output).expect("the lines are text");
        assert_eq!(
            printed
                .split("\n\n")
                .map(|report| report.lines().next().unwrap_or_default())
                .collect::<Vec<_>>(),
            [
                "uri file:///a.gandr version 1 diagnostics 2 holes 1",
                "uri file:///a.gandr version 2 diagnostics 0 holes 0",
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

    #[test]
    fn a_detach_or_a_failed_input_ends_the_view()
    {
        let mut terminal = Terminal::new(TestBackend::new(64_u16, 10_u16)).expect("a test backend");
        let (seen, inbox) = channel();
        seen.send(Seen::Frame(RenderFrame::detach()))
            .expect("the loop listens");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Completed)
        ));
        let (seen, inbox) = channel();
        seen.send(Seen::Input(Input::Failed(Fault::Input(io::Error::other(
            "the keyboard is gone",
        )))))
        .expect("the loop listens");
        assert!(matches!(
            drive_following(&mut terminal, &inbox),
            Ok(Ended::Faulted(Fault::Input(ref error))) if error.to_string() == "the keyboard is gone"
        ));
    }

    #[test]
    fn the_bus_reader_forwards_frames_until_a_line_is_not_one()
    {
        let detached = serde_json::to_string(&RenderFrame::detach()).expect("a frame encodes");
        for bad in [&b"not a frame"[..], &b"\xff"[..]] {
            let mut bus = Vec::from(detached.as_bytes());
            bus.push(b'\n');
            bus.extend_from_slice(bad);
            bus.push(b'\n');
            bus.extend_from_slice(detached.as_bytes());
            bus.push(b'\n');
            let (seen, inbox) = channel();
            frames(bus.as_slice(), &seen);
            let heard: Vec<Seen> = inbox.try_iter().collect();
            assert!(
                matches!(heard.as_slice(), [Seen::Frame(_), Seen::Closed]),
                "{heard:?}"
            );
        }
    }

    #[test]
    fn the_view_leaves_the_hub_with_one_detach_line()
    {
        let mut written = Vec::new();
        detach(&mut written).expect("a vector takes the line");
        let line = String::from_utf8(written).expect("the line is text");
        let frame: RenderFrame = serde_json::from_str(line.strip_suffix('\n').expect("one line"))
            .expect("the line is a frame");
        assert_eq!(Following::default().hear(&frame), Heard::Detached);
    }

    #[test]
    fn a_piped_view_faults_on_a_line_that_is_not_text()
    {
        let mut output = Vec::new();
        assert!(matches!(
            follow_plain(&b"\xff\n"[..], &mut output),
            Ok(Ended::Faulted(Fault::Input(ref error))) if error.kind() == io::ErrorKind::InvalidData
        ));
        assert!(output.is_empty());
    }
}
