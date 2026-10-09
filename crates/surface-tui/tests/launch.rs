//! The terminal face observed from outside: keys offered, frames painted on a
//! headless backend.
//!
//! Every type a case expects is spelled by the loop's renderer, and the
//! source a case types spells its types the same way; every role a case
//! expects is read off the blocks the loop answered, and every refusal is the
//! loop's own text. No case restates a spelling the surface owns.

extern crate alloc;

/// The face's cases, in a `cfg(test)` module so the crate's lint wall reads
/// them as test code rather than as shipping code.
#[cfg(test)]
mod tests
{
    use alloc::collections::VecDeque;

    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::NodeIndex;
    use gandr_kernel_term::BaseType;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::OutKind;
    use gandr_surface_repl::Ended;
    use gandr_surface_repl::rows;
    use gandr_surface_repl::spell;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_tui::App;
    use gandr_surface_tui::Handled;
    use gandr_surface_tui::Input;
    use gandr_surface_tui::InputSource;
    use gandr_surface_tui::Key;
    use gandr_surface_tui::SMOKE_NOTE;
    use gandr_surface_tui::draw;
    use gandr_surface_tui::drive;
    use gandr_surface_tui::run_smoke;
    use gandr_surface_tui::style_of;
    use gandr_surface_tui::style_of_kind;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;
    use ratatui::buffer::Buffer;
    use ratatui::layout::Rect;
    use ratatui::style::Color;
    use ratatui::style::Modifier;
    use ratatui::style::Style;

    /// Keys a case scripts, answered in order.
    #[repr(transparent)]
    struct Script(VecDeque<Input>);

    impl InputSource for Script
    {
        /// The next scripted input, or quit once the script is spent.
        ///
        /// # Specification
        /// trivial.
        fn next(&mut self) -> Input
        {
            self.0.pop_front().unwrap_or(Input::Key(Key::Quit))
        }
    }

    impl Script
    {
        /// The keys that type `line` and enter it.
        ///
        /// # Specification
        /// trivial.
        fn entered<'line, Line>(
            mut self,
            line: Line,
        ) -> Self
        where
            Line: Into<SourceText<'line>>,
        {
            let line = <&str>::from(line.into());
            self.0
                .extend(line.chars().map(|typed| Input::Key(Key::Char(typed))));
            self.0.push_back(Input::Key(Key::Enter));
            self
        }

        /// The script with `input` after it.
        ///
        /// # Specification
        /// trivial.
        fn then(
            mut self,
            input: Input,
        ) -> Self
        {
            self.0.push_back(input);
            self
        }
    }

    /// A fresh face.
    ///
    /// # Specification
    /// trivial.
    fn app() -> App
    {
        App::new().expect("the face starts")
    }

    /// Type `line` into `app` and enter it.
    ///
    /// # Specification
    /// trivial.
    fn enter<'line, Line>(
        app: &mut App,
        line: Line,
    ) -> Handled
    where
        Line: Into<SourceText<'line>>,
    {
        let line = <&str>::from(line.into());
        for typed in line.chars() {
            assert_eq!(
                app.handle(Key::Char(typed)).expect("typing does not fault"),
                Handled::Continue,
                "typing goes on"
            );
        }
        app.handle(Key::Enter).expect("the session does not fault")
    }

    /// The renderer's spelling of the base type `base`.
    ///
    /// # Specification
    /// trivial.
    fn base(base: BaseType) -> String
    {
        spell(&[ContentNode::Base(base)], NodeIndex::from(0))
            .expect("a base type lays out")
            .to_string()
    }

    /// The frame `app` paints onto a headless backend over `area`.
    ///
    /// # Specification
    /// trivial.
    fn painted(
        app: &App,
        area: Rect,
    ) -> Buffer
    {
        let mut terminal = Terminal::new(TestBackend::new(area.width, area.height))
            .expect("the headless backend opens");
        terminal
            .draw(|frame| draw(frame, app))
            .expect("the headless backend draws");
        terminal.backend().buffer().clone()
    }

    /// Each row of `buffer` as the text its cells spell.
    ///
    /// Rows are compared as text only after the frame is read cell by cell:
    /// the pane borders are multi-byte glyphs, so a byte offset into a joined
    /// row is not the column a cell was painted at.
    ///
    /// # Specification
    /// trivial.
    fn screen(buffer: &Buffer) -> Vec<String>
    {
        let area = buffer.area;
        (area.top() .. area.bottom())
            .map(|y| {
                (area.left() .. area.right())
                    .map(|x| buffer[(x, y)].symbol())
                    .collect()
            })
            .collect()
    }

    /// The text inside a pane's side borders on each row of `buffer` that
    /// has them, without trailing blanks.
    ///
    /// # Specification
    /// trivial.
    fn pane_rows(buffer: &Buffer) -> Vec<String>
    {
        screen(buffer)
            .iter()
            .filter_map(|row| row.strip_prefix('│')?.strip_suffix('│'))
            .map(|inside| inside.trim_end().to_owned())
            .collect()
    }

    /// The foreground of each cell spelling `word`, at every place on
    /// `buffer` it is spelled.
    ///
    /// # Specification
    /// trivial.
    fn colours_of<'word, Word>(
        buffer: &Buffer,
        word: Word,
    ) -> Vec<Vec<Color>>
    where
        Word: Into<SourceText<'word>>,
    {
        let symbols: Vec<String> = <&str>::from(word.into())
            .chars()
            .map(String::from)
            .collect();
        let area = buffer.area;
        let mut found = Vec::new();
        for y in area.top() .. area.bottom() {
            let cells: Vec<_> = (area.left() .. area.right())
                .map(|x| &buffer[(x, y)])
                .collect();
            for window in cells.windows(symbols.len()) {
                if window
                    .iter()
                    .zip(&symbols)
                    .all(|(cell, symbol)| cell.symbol() == symbol)
                {
                    found.push(window.iter().map(|cell| cell.fg).collect());
                }
            }
        }
        found
    }

    /// The smoke face prints its launch note and nothing else, and completes.
    #[test]
    fn smoke_writes_the_launch_note()
    {
        let mut output = Vec::new();
        let ended = run_smoke(&mut output).expect("the note is written");
        assert!(matches!(ended, Ended::Completed), "{ended:?}");
        assert_eq!(
            output.as_slice(),
            SMOKE_NOTE.as_bytes(),
            "the launch note is the smoke observable"
        );
        assert_eq!(SMOKE_NOTE, "gandr tui: ready\n", "the note's one line");
    }

    /// A definition the checker refuses against an earlier signature reaches
    /// the transcript pane as the loop's refusal, row for row.
    #[test]
    fn an_outcome_refusal_is_visible_in_the_transcript_pane()
    {
        let string = base(BaseType::String);
        let mut app = app();
        let _goal = enter(&mut app, format!("def wrong : {string} ;").as_str());
        let _refused = enter(&mut app, "def wrong = 42 ;");
        let block = app
            .transcript()
            .last()
            .expect("the refused definition answers a block");
        let refusal: Vec<String> = rows(block)
            .filter(|row| row.kind == OutKind::Diag)
            .map(|row| {
                format!("{}{}", <&str>::from(row.lead), row.text)
                    .trim_end()
                    .to_owned()
            })
            .collect();
        assert!(!refusal.is_empty(), "the definition is refused: {block:?}");
        let pane = pane_rows(&painted(&app, Rect::new(0, 0, 120, 40)));
        assert!(
            pane.windows(refusal.len()).any(|window| window == refusal),
            "the refusal's rows are painted in order: {refusal:#?} in {pane:#?}"
        );
    }

    /// A submitted definition is drawn with its keyword in the keyword
    /// colour: the terminal end of the highlighter's wiring, stated against
    /// the role map, so a wrong role fails as loudly as no role.
    #[test]
    fn a_submitted_keyword_is_painted_in_the_keyword_colour()
    {
        let mut app = app();
        assert_eq!(
            enter(&mut app, "def one = 1 ;"),
            Handled::Continue,
            "submitting does not stop the face"
        );
        let block = app
            .transcript()
            .last()
            .expect("a complete definition submits");
        assert!(
            block
                .source_hl
                .iter()
                .any(|span| span.role == HlRole::Keyword),
            "the loop classifies the keyword: {block:?}"
        );
        let keyword = style_of(HlRole::Keyword).fg.expect("keywords are coloured");
        let painted = colours_of(&painted(&app, Rect::new(0, 0, 60, 12)), "▸ def");
        assert_eq!(painted.len(), 1, "the echo is drawn once: {painted:?}");
        assert!(
            painted
                .iter()
                .all(|colours| colours.get(2 ..) == Some(&[keyword; 3][..])),
            "the def keyword is painted in the keyword colour: {painted:?} against {keyword:?}"
        );
    }

    /// The painted echo carries more than one foreground. With no spans every
    /// echo cell is drawn at the terminal default, so this sees the
    /// difference the highlighter's wiring makes; the echo row is read alone
    /// because the status line is styled whatever the transcript holds.
    #[test]
    fn the_painted_frame_is_not_uniformly_default()
    {
        let mut app = app();
        let _kept = enter(&mut app, "def one = 1 ;");
        let buffer = painted(&app, Rect::new(0, 0, 60, 12));
        let echo = screen(&buffer)
            .iter()
            .position(|row| row.starts_with("│▸ def"))
            .expect("the echo is drawn");
        let row = u16::try_from(echo).expect("the row is on screen");
        let mut colours: Vec<Color> = (buffer.area.left() .. buffer.area.right())
            .map(|x| buffer[(x, row)].fg)
            .collect();
        colours.sort_by_key(ToString::to_string);
        colours.dedup();
        assert!(
            colours.len() > 1,
            "a classified echo is painted in more than one colour: {colours:?}"
        );
    }

    /// A fixed session painted on a headless backend, against its golden:
    /// every symbol of the frame, and every style of the transcript pane —
    /// each lead in its kind's style, each echo character in the style of the
    /// role whose span covers its byte, the rest of a row's text in its
    /// kind's style. The session's second echo crosses a row, and each checked
    /// definition prints the value it runs to under its type.
    #[test]
    fn a_fixed_session_paints_as_the_golden()
    {
        let integer = base(BaseType::Integer);
        let string = base(BaseType::String);
        let mut app = app();
        for line in [
            String::from("def answer = 42 ;"),
            format!("def later : {string} ;"),
            String::from("def copy = ("),
            String::from("answer) ;"),
            String::from(":type answer"),
        ] {
            assert_eq!(enter(&mut app, line.as_str()), Handled::Continue, "{line}");
        }
        let area = Rect::new(0, 0, 48, 18);
        let buffer = painted(&app, area);

        let inside = |text: String| format!("│{text:<46}│");
        let border = |left: &str, title: &str, right: &str| {
            let rule = "─".repeat(46_usize.saturating_sub(title.chars().count()));
            format!("{left}{title}{rule}{right}")
        };
        let mut expected = Vec::from([border("┌", " transcript ", "┐")]);
        for row in [
            String::from("▸ def answer = 42 ;"),
            format!("answer : {integer}"),
            String::from("= 42"),
            format!("▸ def later : {string} ;"),
            format!("? later : {string}"),
            String::from("▸ def copy = ("),
            String::from("  answer) ;"),
            format!("copy : {integer}"),
            String::from("= 42"),
            String::from("▸ :type answer"),
            format!(": {integer}"),
            String::new(),
        ] {
            expected.push(inside(row));
        }
        expected.push(border("└", "", "┘"));
        expected.push(border("┌", " input ", "┐"));
        expected.push(inside(String::new()));
        expected.push(border("└", "", "┘"));
        let status: String = screen(&buffer).last().cloned().unwrap_or_default();
        assert!(!status.trim().is_empty(), "the status line is drawn");
        expected.push(status);
        assert_eq!(screen(&buffer), expected, "the frame's symbols");

        let mut y = 1_u16;
        for block in app.transcript() {
            for row in rows(block) {
                let lead = <&str>::from(row.lead);
                let mut cells = Vec::new();
                for _ in lead.chars() {
                    cells.push(style_of_kind(row.kind));
                }
                for (offset, _) in row.text.char_indices() {
                    let byte = usize::from(row.start).saturating_add(offset);
                    let style = match row.kind {
                        | OutKind::Source => block
                            .source_hl
                            .iter()
                            .find(|span| {
                                span.range.start() <= ByteOffset::from(byte)
                                    && ByteOffset::from(byte) < span.range.end()
                            })
                            .map_or(Style::new(), |span| style_of(span.role)),
                        | _ => style_of_kind(row.kind),
                    };
                    cells.push(style);
                }
                for x in 1 .. area.width.saturating_sub(1) {
                    let want = cells
                        .get(usize::from(x.saturating_sub(1)))
                        .copied()
                        .unwrap_or_default();
                    let cell = &buffer[(x, y)];
                    assert_eq!(
                        (cell.fg, cell.modifier),
                        (
                            want.fg.unwrap_or(Color::Reset),
                            want.add_modifier.difference(Modifier::empty())
                        ),
                        "the style of cell {x}, {y}, in `{lead}{}`",
                        row.text
                    );
                }
                y = y.saturating_add(1);
            }
        }
        assert_eq!(y, 12, "eleven rows painted");
    }

    /// Scripted keys drive the loop: a buffer left open is dropped by an
    /// interrupt, a complete line is kept and painted with its type, a redraw
    /// changes nothing, and `:q` ends the run, completed, with the script
    /// spent.
    #[test]
    fn the_face_drives_the_loop_from_its_keys()
    {
        let mut script = Script(VecDeque::new())
            .entered("def a = (")
            .then(Input::Key(Key::Interrupt))
            .entered("def b = 2 ;")
            .then(Input::Redraw)
            .entered(":q");
        let mut terminal =
            Terminal::new(TestBackend::new(60, 14)).expect("the headless backend opens");
        let ended = drive(&mut terminal, &mut script).expect("the headless backend draws");
        assert!(matches!(ended, Ended::Completed), "{ended:?}");
        assert!(script.0.is_empty(), "`:q` ended the run, not the script");
        let pane = pane_rows(terminal.backend().buffer());
        let integer = base(BaseType::Integer);
        assert_eq!(
            pane.get(.. 2),
            Some(&[String::from("▸ def b = 2 ;"), format!("b : {integer}")][..]),
            "{pane:#?}"
        );
        assert!(
            pane.iter().all(|row| !row.contains("def a")),
            "the interrupted buffer is gone: {pane:#?}"
        );
        assert!(
            pane.iter().any(|row| row == ":q"),
            "the last frame shows the line being entered: {pane:#?}"
        );
    }

    /// A buffer the parser still waits on shows in the input pane above the
    /// line being edited, and an interrupt drops both.
    #[test]
    fn a_waiting_buffer_shows_in_the_input_pane()
    {
        let mut app = app();
        assert_eq!(enter(&mut app, "def a = ("), Handled::Continue);
        assert!(app.transcript().is_empty(), "nothing is submitted yet");
        assert_eq!(
            app.handle(Key::Char('1')).expect("typing does not fault"),
            Handled::Continue
        );
        let area = Rect::new(0, 0, 40, 12);
        let pane = pane_rows(&painted(&app, area));
        assert!(
            pane.windows(2)
                .any(|window| window == [String::from("def a = ("), String::from("1")]),
            "the waiting line, then the line being edited: {pane:#?}"
        );
        assert_eq!(
            app.handle(Key::Interrupt)
                .expect("an interrupt does not fault"),
            Handled::Continue
        );
        let pane = pane_rows(&painted(&app, area));
        assert!(
            pane.iter().all(String::is_empty),
            "the interrupt leaves both panes empty: {pane:#?}"
        );
    }

    /// When the transcript outgrows its pane, the pane shows the newest rows:
    /// the last block's echo, type line and value line at the bottom, the
    /// first block's gone.
    #[test]
    fn the_transcript_pane_follows_the_newest_rows()
    {
        let mut app = app();
        for index in 0_u8 .. 12 {
            let _kept = enter(&mut app, format!("def v{index} = {index} ;").as_str());
        }
        let pane = pane_rows(&painted(&app, Rect::new(0, 0, 40, 12)));
        let integer = base(BaseType::Integer);
        let transcript: Vec<&String> = pane.iter().take(6).collect();
        assert_eq!(
            transcript.get(3 ..),
            Some(
                &[
                    &String::from("▸ def v11 = 11 ;"),
                    &format!("v11 : {integer}"),
                    &String::from("= 11")
                ][..]
            ),
            "the newest rows close the pane: {pane:#?}"
        );
        assert!(
            pane.iter().all(|row| row != "▸ def v0 = 0 ;"),
            "the oldest rows scrolled away: {pane:#?}"
        );
    }
}
