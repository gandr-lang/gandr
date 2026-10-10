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
    /// - requires: nothing.
    /// - ensures: the count is preserved through the terminal maximum and
    ///   saturates, rather than wrapping, above it.
    /// - provides: a bounded terminal coordinate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one, both sides of the terminal maximum and the
    ///   machine maximum separate truncation, wrapping and off-by-one
    ///   saturation. Other counts follow the same conversion branch.
    /// - witness: `view::tests::cell_counts_saturate_without_wrapping`
    #[anodized::spec(ensures: |ret| usize::from(ret.0) == count.min(usize::from(u16::MAX)))]
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
///   the line being edited, the newest that fit. An editable cell is reserved
///   for the cursor after the line's visible tail; an empty inner pane requests
///   no cursor. The status line says what Enter and the interrupt do at the
///   loop's prompt.
/// - provides: the face's one paint, the same for the terminal and the headless
///   backend.
/// - fails: never.
/// - panics: none.
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure; cursor state
///   has no frame getter. Backend witnesses observe these effects after draw.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the fixed-session frame, refusal, keyword, waiting
///   buffer and overflowing transcript are observed through backend cells.
///   Wrong pane order, dropped rows, lost role colour and stale input change
///   these observations. Empty geometry and input beyond the coordinate limit
///   have separate cursor/tail witnesses; arbitrary terminal fonts are outside
///   this finite domain.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
/// - witness: `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`
/// - witness: `launch::tests::an_outcome_refusal_is_visible_in_the_transcript_pane`
/// - witness: `launch::tests::the_transcript_pane_follows_the_newest_rows`
/// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
/// - witness: `view::tests::an_input_pane_without_editable_cells_requests_no_cursor`
/// - witness: `view::tests::input_wider_than_a_terminal_coordinate_keeps_its_actual_tail`
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
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure; cursor state
///   has no frame getter. Backend witnesses observe these effects after draw.
///
/// # Adequacy
/// - hypothesis: L2/L3 — a fixed accepted/refused session and twelve blocks
///   exceeding a small viewport are observed as exact backend rows. Wrong
///   ordering, oldest-first clipping and missing borders alter the fixtures;
///   arbitrary terminal fonts and larger histories are outside this domain.
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
/// - ensures: as [`draw`] states for the input pane. Waiting rows are clipped
///   at the right edge. The edited row keeps the tail fitting before a free
///   cursor cell, even beyond the terminal coordinate limit; an empty inner
///   pane requests no cursor.
/// - provides: the input pane.
/// - fails: never.
/// - panics: none.
/// - executable: none — `Frame` exposes its painted buffer only through a
///   mutable borrow, unavailable to a predicate's `Fn` closure; cursor state
///   has no frame getter. Backend witnesses observe these effects after draw.
///
/// # Adequacy
/// - hypothesis: L3 — a waiting/interrupted buffer, empty inner rectangles,
///   wide and combining characters, and an edited line exceeding 65,535 cells
///   are observed through backend symbols and cursor state. Stale input,
///   byte-based cursor placement, visible out-of-pane cursors and saturating
///   before clipping change these observations. Terminal font differences are
///   outside the headless backend's width model.
/// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
/// - witness: `view::tests::an_input_pane_without_editable_cells_requests_no_cursor`
/// - witness: `view::tests::input_wider_than_a_terminal_coordinate_keeps_its_actual_tail`
/// - witness: `view::tests::input_cursor_counts_cells_not_utf8_bytes`
fn draw_input(
    frame: &mut Frame<'_>,
    area: Rect,
    app: &App,
)
{
    let pane = Block::bordered().title(" input ");
    let inner = pane.inner(area);
    frame.render_widget(pane, area);
    if inner.is_empty() {
        return;
    }
    let waiting_rows = usize::from(inner.height).saturating_sub(1_usize);
    let skip = app.waiting().len().saturating_sub(waiting_rows);
    let mut y = inner.y;
    for waiting in app.waiting().iter().skip(skip) {
        frame.render_widget(
            Span::raw(waiting.as_str()),
            Rect::new(inner.x, y, inner.width, 1),
        );
        y = y.saturating_add(1);
    }
    let line = Line::raw(<&str>::from(app.line()));
    let width = line.width();
    let columns = inner.width.saturating_sub(1);
    let line = if width > usize::from(columns) {
        line.right_aligned()
    }
    else {
        line
    };
    frame.render_widget(line, Rect::new(inner.x, y, columns, 1));
    let Cells(cursor) = Cells::from(width.min(usize::from(columns)));
    frame.set_cursor_position(Position {
        x: inner.x.saturating_add(cursor),
        y,
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
/// - hypothesis: L2/L3 — the fixed-session frame separates lead, payload and
///   row order; a malformed cross-row Unicode highlight fixture independently
///   observes text segments and colours. Missing leads, payload loss, wrong
///   clipping and role substitutions change the observations. Unlisted terminal
///   colour appearance is outside these deterministic fixtures.
/// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
/// - witness: `view::tests::echo_clipping_keeps_utf8_gaps_and_first_accepted_spans`
#[anodized::spec(ensures: |ref ret| ret.spans.iter().flat_map(|span| span.content.bytes())
    .eq(<&'static str>::from(row.lead).bytes().chain(row.text.bytes())))]
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
/// - requires: nothing; malformed highlight spans are admissible.
/// - ensures: the row's text, in order and whole, is appended to `painted`,
///   without changing its prefix. Valid spans are clipped to this row and
///   painted in their role's style. A span whose clipped start precedes the end
///   of the last accepted span, or whose clipped endpoints split a character,
///   is ignored. Earlier accepted styling remains; uncovered text retains the
///   terminal default.
/// - provides: the echo's highlighting on one row.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two rows containing multi-byte text, a cross-row span, a
///   split-character endpoint, unsorted and overlapping spans, and a seeded
///   output prefix are compared as literal segments and colours. Lost bytes,
///   overwritten prefixes, wrong clipping and last-span-wins mutations differ.
///   These cases do not enumerate arbitrary span lists or terminal fonts.
/// - witness: `view::tests::echo_clipping_keeps_utf8_gaps_and_first_accepted_spans`
/// - witness: `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`
#[anodized::spec(
    captures: [prefix = painted.len()],
    ensures: painted.len() >= prefix && painted.iter().skip(prefix)
        .flat_map(|span| span.content.bytes()).eq(row.text.bytes()),
)]
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

#[cfg(test)]
mod tests
{
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;
    use ratatui::layout::Position;

    use super::draw;
    use crate::app::App;
    use crate::app::Key;

    #[test]
    fn an_input_pane_without_editable_cells_requests_no_cursor()
    {
        for (width, height, visible) in [
            (0_u16, 0_u16, false),
            (1, 1, false),
            (2, 5, false),
            (20, 4, false),
            (20, 7, true),
        ] {
            let app = App::new().expect("the grammar builds");
            let mut terminal =
                Terminal::new(TestBackend::new(width, height)).expect("the backend opens");
            terminal
                .draw(|frame| draw(frame, &app))
                .expect("the frame draws");
            assert_eq!(
                terminal.backend().cursor_visible(),
                visible,
                "{width} by {height}"
            );
            if visible {
                let position = terminal.backend().cursor_position();
                assert!(position.x < width && position.y < height);
            }
        }
    }

    #[test]
    fn input_wider_than_a_terminal_coordinate_keeps_its_actual_tail()
    {
        let mut app = App::new().expect("the grammar builds");
        for _ in 0_usize ..= usize::from(u16::MAX) {
            let _handled = app.handle(Key::Char('x')).expect("typing succeeds");
        }
        let _handled = app.handle(Key::Char('Z')).expect("typing succeeds");
        let mut terminal = Terminal::new(TestBackend::new(12, 8)).expect("the backend opens");
        terminal
            .draw(|frame| draw(frame, &app))
            .expect("the frame draws");
        let buffer = terminal.backend().buffer();
        assert_eq!(
            buffer[(9_u16, 5_u16)].symbol(),
            "Z",
            "the source tail precedes the cursor"
        );
        assert_eq!(
            buffer[(10_u16, 5_u16)].symbol(),
            " ",
            "the cursor owns a free cell"
        );
        assert_eq!(terminal.backend().cursor_position(), Position::new(10, 5));
    }

    #[test]
    fn cell_counts_saturate_without_wrapping()
    {
        let maximum = usize::from(u16::MAX);
        for (offered, expected) in [
            (0_usize, 0_u16),
            (1, 1),
            (maximum.saturating_sub(1), u16::MAX.saturating_sub(1)),
            (maximum, u16::MAX),
            (maximum.saturating_add(1), u16::MAX),
            (usize::MAX, u16::MAX),
        ] {
            assert_eq!(super::Cells::from(offered).0, expected);
        }
    }

    #[test]
    fn input_cursor_counts_cells_not_utf8_bytes()
    {
        let mut app = App::new().expect("the grammar builds");
        for typed in "界e\u{301}".chars() {
            let _handled = app.handle(Key::Char(typed)).expect("typing succeeds");
        }
        let mut terminal = Terminal::new(TestBackend::new(12, 8)).expect("the backend opens");
        terminal
            .draw(|frame| draw(frame, &app))
            .expect("the frame draws");
        let buffer = terminal.backend().buffer();
        assert_eq!(buffer[(1_u16, 5_u16)].symbol(), "界");
        assert_eq!(buffer[(3_u16, 5_u16)].symbol(), "e\u{301}");
        assert_eq!(terminal.backend().cursor_position(), Position::new(4, 5));
    }

    #[test]
    fn echo_clipping_keeps_utf8_gaps_and_first_accepted_spans()
    {
        use gandr_surface_render_remote::ByteOffset;
        use gandr_surface_render_remote::ByteRange;
        use gandr_surface_render_remote::HlRole;
        use ratatui::style::Color;
        use ratatui::style::Style;
        use ratatui::text::Span;

        let block = super::TranscriptBlock {
            source: "αb\ncdé".into(),
            source_hl: [
                (1_usize, 2_usize, HlRole::Number),
                (2, 6, HlRole::Keyword),
                (4, 8, HlRole::StringLit),
                (0, 2, HlRole::Comment),
            ]
            .into_iter()
            .map(|(start, end, role)| super::HlSpan {
                range: ByteRange::new(ByteOffset::from(start), ByteOffset::from(end))
                    .expect("ordered range"),
                role,
            })
            .collect(),
            lines: super::Vec::new(),
        };
        let actual: super::Vec<_> = super::rows(&block)
            .map(|row| {
                let mut pieces =
                    super::Vec::from([Span::styled("prefix", Style::new().fg(Color::Blue))]);
                super::paint_echo(&block.source_hl, row, &mut pieces);
                pieces
                    .into_iter()
                    .map(|piece| (piece.content, piece.style.fg))
                    .collect::<super::Vec<_>>()
            })
            .collect();
        assert_eq!(
            actual,
            super::Vec::from([
                super::Vec::from([
                    ("prefix".into(), Some(Color::Blue)),
                    ("α".into(), None),
                    ("b".into(), Some(Color::Magenta))
                ]),
                super::Vec::from([
                    ("prefix".into(), Some(Color::Blue)),
                    ("cd".into(), Some(Color::Magenta)),
                    ("é".into(), None)
                ]),
            ])
        );
    }
}
