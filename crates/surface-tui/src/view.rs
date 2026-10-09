//! The frame: the transcript pane, the input pane and the status line.

use alloc::vec::Vec;

use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_repl::Prompt;
use gandr_surface_repl::Row;
use gandr_surface_repl::rows;
use ratatui::Frame;
use ratatui::layout::Constraint;
use ratatui::layout::Layout;
use ratatui::layout::Position;
use ratatui::layout::Rect;
use ratatui::style::Color;
use ratatui::style::Style;
use ratatui::text::Line;
use ratatui::text::Span;
use ratatui::widgets::Block;
use ratatui::widgets::Paragraph;

use crate::app::App;
use crate::theme::style_of;
use crate::theme::style_of_kind;

/// The status line's style.
const STATUS: Style = Style::new().fg(Color::DarkGray);

/// The status line at a fresh prompt.
const FRESH: &str = "Enter submits · :help lists the commands · Ctrl-C clears · Esc quits";

/// The status line while the parser waits for more of a buffer.
const CONTINUING: &str =
    "the parser expects more: Enter adds the line · Ctrl-C drops the buffer · Esc quits";

/// A count of terminal rows or columns.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cells(u16);

impl From<usize> for Cells
{
    /// The cells `count` asks for, saturating at the widest terminal.
    ///
    /// # Specification
    /// trivial.
    fn from(count: usize) -> Self
    {
        Self(u16::try_from(count).unwrap_or(u16::MAX))
    }
}

/// Draw `app` onto `frame`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the frame holds three panes, top to bottom. The transcript pane,
///   titled ` transcript `, paints the newest rows of the transcript that fit,
///   each row as the loop's rows lay it out — the lead in the line kind's
///   style, an echo row's text by its highlight roles and unclassified text at
///   the terminal default, any other row's text in its kind's style. The input
///   pane, titled ` input `, holds the lines waiting for the parser and then
///   the line being edited, the newest that fit, with the cursor after the
///   line's last character. The status line says what Enter and the interrupt
///   do at the loop's prompt.
/// - provides: the face's one paint, the same for the terminal and the headless
///   backend.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a fixed session is painted onto a headless backend and
///   compared cell by cell, symbols and styles, with a golden whose types are
///   spelled by the loop's renderer and whose roles are read off the blocks; L3
///   — a keyword's cells, a refusal's rows, the newest rows of an overflowing
///   transcript and a waiting buffer are each asserted on the painted frame.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
/// - witness: `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`
/// - witness: `launch::tests::the_painted_frame_is_not_uniformly_default`
/// - witness: `launch::tests::an_outcome_refusal_is_visible_in_the_transcript_pane`
/// - witness: `launch::tests::the_transcript_pane_follows_the_newest_rows`
/// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
#[inline]
pub fn draw(
    frame: &mut Frame<'_>,
    app: &App,
)
{
    let Cells(input_rows) = Cells::from(app.waiting().len().saturating_add(1));
    let [transcript, input, status] = Layout::vertical([
        Constraint::Min(3),
        Constraint::Length(input_rows.saturating_add(2)),
        Constraint::Length(1),
    ])
    .areas(frame.area());
    draw_transcript(frame, transcript, app.transcript());
    draw_input(frame, input, app);
    let help = match app.prompt() {
        | Prompt::Fresh => FRESH,
        | Prompt::Continuing => CONTINUING,
    };
    frame.render_widget(Paragraph::new(help).style(STATUS), status);
}

/// Paint the newest rows of `transcript` that fit into the bordered `area`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`draw`] states for the transcript pane.
/// - provides: the transcript pane.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — through [`draw`]'s golden; L3 — an overflowing transcript
///   shows its newest block and not its oldest.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
/// - witness: `launch::tests::the_transcript_pane_follows_the_newest_rows`
fn draw_transcript(
    frame: &mut Frame<'_>,
    area: Rect,
    transcript: &[TranscriptBlock],
)
{
    let pane = Block::bordered().title(" transcript ");
    let height = usize::from(pane.inner(area).height);
    // economy: each frame counts every row of the transcript to find the
    // newest that fit; keep a running row count beside the transcript if a
    // long session lags.
    let all = || {
        transcript
            .iter()
            .flat_map(|block| rows(block).map(move |row| (block, row)))
    };
    let skip = all().count().saturating_sub(height);
    let painted: Vec<Line<'_>> = all()
        .skip(skip)
        .map(|(block, row)| paint(block, row))
        .collect();
    frame.render_widget(Paragraph::new(painted).block(pane), area);
}

/// Paint the waiting lines and the line being edited into the bordered
/// `area`, and place the cursor after the line.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`draw`] states for the input pane; a line wider than the pane
///   scrolls left so its end and the cursor stay inside.
/// - provides: the input pane.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a waiting buffer and the line after it are asserted on
///   the painted frame, and dropped by an interrupt.
/// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
fn draw_input(
    frame: &mut Frame<'_>,
    area: Rect,
    app: &App,
)
{
    let pane = Block::bordered().title(" input ");
    let inner = pane.inner(area);
    let line = Line::raw(<&str>::from(app.line()));
    let Cells(width) = Cells::from(line.width());
    let rows: Vec<Line<'_>> = app
        .waiting()
        .iter()
        .map(|waiting| Line::raw(waiting.as_str()))
        .chain(core::iter::once(line))
        .collect();
    let Cells(count) = Cells::from(rows.len());
    let down = count.saturating_sub(inner.height);
    let across = width.saturating_sub(inner.width.saturating_sub(1));
    frame.render_widget(
        Paragraph::new(rows).block(pane).scroll((down, across)),
        area,
    );
    frame.set_cursor_position(Position {
        x: inner.x.saturating_add(width.saturating_sub(across)),
        y: inner
            .y
            .saturating_add(count.saturating_sub(down).saturating_sub(1)),
    });
}

/// Paint `row` of `block`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the row's lead in its kind's style, then its text: an echo row's
///   by [`paint_echo`], any other row's in its kind's style.
/// - provides: one painted transcript row, borrowing the block's text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — through [`draw`]'s golden, every row of a fixed session
///   compared cell by cell.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
fn paint<'block>(
    block: &'block TranscriptBlock,
    row: Row<'block>,
) -> Line<'block>
{
    let kind = style_of_kind(row.kind);
    let lead = Span::styled(<&'static str>::from(row.lead), kind);
    match row.kind {
        | OutKind::Source => {
            let mut spans = Vec::with_capacity(block.source_hl.len().saturating_add(2));
            spans.push(lead);
            paint_echo(&block.source_hl, row, &mut spans);
            Line::from(spans)
        },
        | OutKind::Type
        | OutKind::Value
        | OutKind::Blame
        | OutKind::Stuck
        | OutKind::Diag
        | OutKind::Goal
        | OutKind::Info => Line::from(Vec::from([lead, Span::styled(row.text, kind)])),
    }
}

/// Paint an echo row's text by the highlight spans over the block's source.
///
/// # Specification
/// - requires: nothing; the highlighter yields `spans` sorted, disjoint and on
///   character boundaries, and a span that is not is passed over.
/// - ensures: the row's text, in order and whole, as pieces pushed onto
///   `painted`: the part of each span inside the row in its role's style,
///   clipped to the row so a span crossing rows paints on each, and every byte
///   no span covers at the terminal default. A span starting before the end of
///   the one painted before it, or not on a character boundary of the row, is
///   passed over and its bytes painted at the default.
/// - provides: the echo's highlighting on one row.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — through [`draw`]'s golden, each echo cell's style
///   compared with the role of the span covering its byte, over a session whose
///   echo crosses a row; L3 — a keyword's cells carry the keyword colour.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
/// - witness: `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`
fn paint_echo<'block>(
    spans: &[HlSpan],
    row: Row<'block>,
    painted: &mut Vec<Span<'block>>,
)
{
    let start = usize::from(row.start);
    let end = start.saturating_add(row.text.len());
    let mut cursor = 0_usize;
    for span in spans {
        let from = usize::from(span.range.start()).max(start);
        let to = usize::from(span.range.end()).min(end);
        if from >= to {
            continue;
        }
        let (from, to) = (from.saturating_sub(start), to.saturating_sub(start));
        if from < cursor {
            continue;
        }
        let (Some(gap), Some(piece)) = (row.text.get(cursor .. from), row.text.get(from .. to))
        else {
            continue;
        };
        if !gap.is_empty() {
            painted.push(Span::raw(gap));
        }
        painted.push(Span::styled(piece, style_of(span.role)));
        cursor = to;
    }
    if let Some(tail) = row.text.get(cursor ..)
        && !tail.is_empty()
    {
        painted.push(Span::raw(tail));
    }
}
