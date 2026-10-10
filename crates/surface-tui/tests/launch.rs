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
    use std::io;

    use gandr_core_incremental::ContentNode;
    use gandr_core_incremental::NodeIndex;
    use gandr_kernel_term::BaseType;
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
    use gandr_surface_tui::draw;
    use gandr_surface_tui::drive;
    use gandr_surface_tui::run_smoke;
    use gandr_surface_tui::style_of;
    use ratatui::Terminal;
    use ratatui::backend::TestBackend;
    use ratatui::buffer::Buffer;
    use ratatui::layout::Rect;
    use ratatui::style::Color;

    /// Keys a case scripts, answered in order.
    #[repr(transparent)]
    struct Script(VecDeque<Input>);

    impl InputSource for Script
    {
        /// The next scripted input, or quit once the script is spent.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: removes the oldest queued input, or returns quit for an
        ///   empty queue.
        /// - provides: deterministic input without terminal I/O.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a failed read followed by an unread key and a
        ///   complete script independently expose order and queue residue.
        ///   Popping the wrong end, not consuming, or continuing past failure
        ///   changes these finite traces.
        /// - witness: `launch::tests::a_failed_input_preserves_its_cause_and_stops_reading`
        /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
        #[anodized::spec(captures: [before = self.0.len()], ensures: |ref ret|
        self.0.len() == before.saturating_sub(1) && (before != 0 || matches!(*ret, Input::Key(Key::Quit))))]
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
        /// - requires: the offered line has no line terminator.
        /// - ensures: preserves the existing script, appending each character
        ///   in order and then one Enter.
        /// - provides: a submitted-line input sequence.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — scripted incomplete and complete declarations and
        ///   command quit produce exact backend rows and the expected ending.
        ///   Missing, reordered or extra submitted characters change those
        ///   observations; arbitrary inputs are outside this finite session.
        /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
        #[anodized::spec(captures: [before = self.0.len()], ensures: |ref ret|
            ret.0.len() > before && matches!(ret.0.back(), Some(&Input::Key(Key::Enter)))
            && ret.0.iter().skip(before).take(ret.0.len().saturating_sub(before).saturating_sub(1))
                .all(|input| matches!(*input, Input::Key(Key::Char(_)))))]
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
        /// - requires: nothing.
        /// - ensures: appends exactly the offered input after the existing
        ///   sequence.
        /// - provides: explicit interrupt and redraw boundaries in a script.
        /// - fails: never.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — interrupt and redraw between submitted
        ///   declarations are observed through final rows and completion.
        ///   Losing, moving or replacing these boundaries changes the finite
        ///   script; arbitrary input failures are covered separately through
        ///   direct queue construction.
        /// - witness: `launch::tests::the_face_drives_the_loop_from_its_keys`
        #[anodized::spec(captures: [before = self.0.len(), tag = core::mem::discriminant(&input)],
            ensures: |ref ret| ret.0.len() == before.saturating_add(1)
                && ret.0.back().is_some_and(|last| core::mem::discriminant(last) == tag))]
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
    /// - requires: the built-in grammar constructs successfully.
    /// - ensures: the line, waiting buffer and transcript start empty at a
    ///   fresh prompt.
    /// - provides: an isolated application for a case.
    /// - fails: never.
    /// - panics: if the built-in grammar cannot construct.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — waiting, interruption and fixed-session frame
    ///   fixtures start independently and compare their exact visible state.
    ///   Stale source or transcript entries change those observations; grammar
    ///   failure is excluded.
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    /// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
    #[anodized::spec(ensures: |ref ret| ret.transcript().is_empty())]
    fn app() -> App
    {
        App::new().expect("the face starts")
    }

    /// Type `line` into `app` and enter it.
    ///
    /// # Specification
    /// - requires: the current and offered lines contain no line terminator,
    ///   and the submitted source does not fault the session.
    /// - ensures: types the offered characters and submits once, clearing the
    ///   edit line and returning the application's continuation or quit
    ///   decision.
    /// - provides: complete and continued source input to frame fixtures.
    /// - fails: never.
    /// - panics: if typing or submission faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete declarations, an incomplete buffer and
    ///   subsequent continuation are observed in independent pane rows. Missing
    ///   characters, duplicate submission or failure to clear editing changes
    ///   those fixtures. Session faults and arbitrary source syntax are outside
    ///   this domain.
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    /// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
    #[anodized::spec(captures: [before = app.transcript().len()], ensures: |ret|
        app.transcript().len() >= before && app.transcript().len() <= before.saturating_add(1)
            && (ret != Handled::Quit || app.transcript().len() == before))]
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
    /// - requires: nothing.
    /// - ensures: returns the renderer's single-line spelling of the base atom.
    /// - provides: type spelling for layout fixtures without pinning
    ///   typography.
    /// - fails: never.
    /// - panics: if a base atom cannot be rendered.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — integer and string declarations are compared with
    ///   actual application frames, independently of this helper. Wrong type
    ///   selection or corrupted spelling changes the golden; other base atoms
    ///   are not enumerated.
    /// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
    #[anodized::spec(ensures: |ref ret| !ret.contains(['\r', '\n']))]
    fn base(base: BaseType) -> String
    {
        spell(&[ContentNode::Base(base)], NodeIndex::from(0))
            .expect("a base type lays out")
            .to_string()
    }

    /// The frame `app` paints onto a headless backend over `area`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the completed frame at origin zero, using the offered
    ///   width and height; the offered origin does not offset the backend.
    /// - provides: an owned, stable snapshot of application output.
    /// - fails: never.
    /// - panics: if the headless backend cannot open or draw.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — fixed-session layout, refusal and waiting-buffer
    ///   fixtures inspect exact symbols and roles at bounded viewport sizes.
    ///   Wrong dimensions, missing paint or stale snapshots change those
    ///   observations; backend failures are outside this infallible backend's
    ///   domain.
    /// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    #[anodized::spec(ensures: |ref ret| ret.area.x == 0 && ret.area.y == 0
        && ret.area.width == area.width && ret.area.height == area.height)]
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
    /// - requires: a valid backend buffer.
    /// - ensures: returns one string per buffer row, concatenating cell symbols
    ///   left to right and preserving row order.
    /// - provides: text observations independent of byte-width assumptions.
    /// - fails: never.
    /// - panics: if buffer dimensions do not address its cells.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a bordered fixed-session frame contains multi-byte
    ///   box glyphs, continued echoes and output rows. Dropped, reordered or
    ///   byte-indexed cells change the independent golden. Hidden
    ///   wide-character cells are not interpreted as additional displayed
    ///   glyphs by this text-only observer.
    /// - witness: `launch::tests::a_fixed_session_paints_as_the_golden`
    #[anodized::spec(ensures: |ref ret| ret.len() == usize::from(buffer.area.height))]
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
    /// - requires: a valid backend buffer.
    /// - ensures: keeps rows enclosed by side borders, removes those borders
    ///   and trailing whitespace, and preserves the order of retained rows.
    /// - provides: pane-content observations independent of padding.
    /// - fails: never.
    /// - panics: if buffer dimensions do not address its cells.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — waiting, interruption and transcript overflow are
    ///   compared as exact content rows. Border leakage, stale padding or row
    ///   reordering changes those observations; arbitrary non-pane layouts are
    ///   outside them.
    /// - witness: `launch::tests::a_waiting_buffer_shows_in_the_input_pane`
    /// - witness: `launch::tests::the_transcript_pane_follows_the_newest_rows`
    #[anodized::spec(ensures: |ref ret| ret.len() <= usize::from(buffer.area.height)
        && ret.iter().all(|row| row.chars().next_back().is_none_or(|last| !last.is_whitespace())))]
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
    /// - requires: a valid buffer and a nonempty word whose characters each
    ///   occupy one cell, without combining sequences.
    /// - ensures: returns every matching row-local window's foregrounds in
    ///   order.
    /// - provides: a colour observation for visible keywords.
    /// - fails: never.
    /// - panics: for an empty word or inconsistent buffer dimensions.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unique echoed definition keyword is located and
    ///   its three cells compared with the semantic keyword colour. Missing
    ///   hits, wrong window offsets or colours change this observation; wide
    ///   and combining characters are excluded from this helper's domain.
    /// - witness: `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`
    #[anodized::spec(ensures: |ref ret| ret.iter().all(|colours|
        !colours.is_empty() && colours.len() <= usize::from(buffer.area.width)))]
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

    /// A partially accepting writer reports its failure instead of completing.
    #[test]
    fn the_smoke_face_propagates_a_partial_write_failure()
    {
        let mut output = io::Cursor::new([0_u8; 5]);
        let error = run_smoke(&mut output).expect_err("five bytes cannot hold the launch note");
        assert_eq!(error.kind(), io::ErrorKind::WriteZero);
        assert_eq!(
            output.position(),
            5_u64,
            "the full capacity was accepted before refusal"
        );
    }

    #[test]
    fn a_failed_input_preserves_its_cause_and_stops_reading()
    {
        let mut script = Script(VecDeque::from([
            Input::Failed(gandr_surface_repl::Fault::Input(
                io::ErrorKind::ConnectionReset.into(),
            )),
            Input::Key(Key::Char('x')),
        ]));
        let mut terminal = Terminal::new(TestBackend::new(40, 12)).expect("the backend opens");
        let ended = drive(&mut terminal, &mut script).expect("the backend draws");
        let Ended::Faulted(gandr_surface_repl::Fault::Input(error)) = ended
        else {
            panic!("the input failure must remain an input failure");
        };
        assert_eq!(error.kind(), io::ErrorKind::ConnectionReset);
        assert_eq!(script.0.len(), 1);
        assert!(matches!(
            script.0.front(),
            Some(&Input::Key(Key::Char('x')))
        ));
        assert_eq!(
            terminal.get_frame().count(),
            1,
            "the initial frame precedes the failed read"
        );
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

    /// A fixed session paints ordered, continued and queried declarations in
    /// separate bordered panes. Status wording and the painter's algorithm are
    /// not part of this independent text-layout fixture.
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
        assert_eq!(
            screen(&buffer).get(.. expected.len()),
            Some(expected.as_slice()),
            "the pane symbols"
        );
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

    /// Run this witness alone on a terminal and enter :quit.
    #[cfg(unix)]
    #[test]
    #[ignore = "requires an attached terminal; enter :quit"]
    fn the_terminal_face_completes_and_restores_its_settings()
    {
        use std::io::IsTerminal as _;
        use std::process::Command;
        use std::process::Stdio;

        assert!(io::stdin().is_terminal() && io::stdout().is_terminal());
        let before = Command::new("stty")
            .arg("-g")
            .stdin(Stdio::inherit())
            .output()
            .expect("terminal settings can be read");
        assert!(before.status.success());
        let ended = gandr_surface_tui::run().expect("the terminal face runs");
        let after = Command::new("stty")
            .arg("-g")
            .stdin(Stdio::inherit())
            .output()
            .expect("terminal settings can be read again");
        assert!(after.status.success());
        assert_eq!(
            after.stdout, before.stdout,
            "the original terminal settings are restored"
        );
        assert!(matches!(ended, Ended::Completed));
    }
}
