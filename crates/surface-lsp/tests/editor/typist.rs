//! A writer at the keyboard: reaches a target text through the keystrokes a
//! person makes in an assisting editor.
//!
//! Under assisted typing the editor inserts material the writer did not type:
//! a closer after each opener, indentation after each newline. The writer
//! works with it as a person does — types a closer over the one the editor
//! inserted, steps down onto a closer the editor moved to its own line,
//! deletes a closer left where none was wanted, and corrects the indentation
//! the editor guessed — so the text converges on the target, and every
//! intermediate text is one a person would pass through.

use alloc::string::String;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use super::buffer::Closer;
use super::buffer::Key;
use super::buffer::Offset;
use super::buffer::Text;
use super::buffer::closer_of;
use super::buffer::opener_of;
use super::editing::Session;

/// How many bytes at the end of the text a typing keeps after what it types.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Kept(usize);

/// A count of indenting spaces.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Width(usize);

impl Session
{
    /// Type `insertion` at the cursor, keystroke by keystroke.
    ///
    /// # Specification
    /// - requires: nothing; the cursor may stand anywhere.
    /// - ensures: the text is the text before the cursor, then `insertion`,
    ///   then the text that was after the cursor; every keystroke on the way
    ///   was synchronised and checked, and the final text was held to the
    ///   oracle; before each keystroke the text up to the cursor is the text
    ///   before the cursor followed by the part of `insertion` typed so far.
    /// - provides: the replay of a writer typing `insertion`.
    /// - panics: a keystroke's check fails, or the text does not converge on
    ///   the target.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus replay types every corpus source from an
    ///   empty buffer and the final text must equal the source; a typist that
    ///   loses, duplicates or misplaces material fails that equality or the
    ///   per-keystroke prefix check.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::defining_a_missing_name_clears_its_diagnostic`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body types every character, comparing the text up to the cursor at each keystroke; the check compares the final text once"
        )
    )]
    #[spec(captures: [target = {
            let text = self.buffer().text().0;
            let (before, after) = text.split_at(self.buffer().cursor().0);
            format!("{before}{}{after}", insertion.0)
        }],
        ensures: self.buffer().text().0 == target)]
    pub fn type_in(
        &mut self,
        insertion: Text<'_>,
    )
    {
        let text = String::from(self.buffer().text().0);
        let (before, after) = text.split_at(self.buffer().cursor().0);
        let kept = Kept(after.len());
        loop {
            let done = self.buffer().cursor().0.saturating_sub(before.len());
            assert_eq!(
                self.buffer().text().0.get(.. self.buffer().cursor().0),
                insertion
                    .0
                    .get(.. done)
                    .map(|typed| format!("{before}{typed}"))
                    .as_deref(),
                "the text up to the cursor is what was typed"
            );
            let Some(rest) = insertion.0.get(done ..)
            else {
                break;
            };
            let Some(typed) = rest.chars().next()
            else {
                break;
            };
            let junk = self.junk(kept);
            if typed == '\n' {
                self.newline(Text(&junk), Text(rest.get(1 ..).unwrap_or_default()));
                continue;
            }
            if matches!(opener_of(Key(typed)), Maybe::Present(_)) && junk.starts_with(typed) {
                if self.buffer().closer() == Closer::Pending {
                    self.type_char(Key(typed));
                }
                else {
                    let past = self.buffer().cursor().0.saturating_add(typed.len_utf8());
                    self.move_to(Offset(past));
                }
                continue;
            }
            self.type_char(Key(typed));
            if matches!(typed, '}' | ')') {
                let typed_so_far = insertion
                    .0
                    .get(.. done.saturating_add(typed.len_utf8()))
                    .expect("typing stops on boundaries");
                self.repair_outdent(Text(&format!("{before}{typed_so_far}")));
            }
        }
        while !self.junk(kept).is_empty() {
            self.delete();
        }
        assert_eq!(
            self.buffer().text().0,
            format!("{before}{}{after}", insertion.0),
            "the typed text converges on the target"
        );
        self.verify();
    }

    /// Delete the text's last line, one keystroke at a time, until the text
    /// is empty.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text is empty; each keystroke deleted one line with the
    ///   newline before it, the last first.
    /// - provides: the replay of a writer deleting a document line by line.
    /// - panics: a keystroke's check fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the erasure deletes every corpus source to nothing; a
    ///   deletion spanning newlines that the server applied differently shows
    ///   in the differential answers of the next keystroke.
    /// - witness: `editor::editor::scenarios::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    #[spec(ensures: self.buffer().text().0.is_empty())]
    pub fn erase_lines(&mut self)
    {
        while !self.buffer().text().0.is_empty() {
            let text = self.buffer().text().0;
            let body = text.strip_suffix('\n').unwrap_or(text);
            let start = body
                .rfind('\n')
                .map_or(0_usize, |newline| newline.saturating_add(1));
            let end = text.len();
            self.replace(Offset(start), Offset(end), Text(""));
        }
    }

    /// What the editor inserted between the cursor and the last `kept` bytes
    /// of the text: the closers the writer has not reached.
    ///
    /// # Specification
    /// trivial.
    fn junk(
        &self,
        kept: Kept,
    ) -> String
    {
        let text = self.buffer().text().0;
        let cursor = self.buffer().cursor().0;
        let end = text.len().saturating_sub(kept.0).max(cursor);
        String::from(
            text.get(cursor .. end)
                .expect("the inserted material is on boundaries"),
        )
    }

    /// Press Enter towards a target whose text after the newline is
    /// `following`, with `junk` inserted after the cursor.
    ///
    /// # Specification
    /// - requires: the text up to the cursor is the target's up to the newline.
    /// - ensures: when the editor already moved a closer the target's next line
    ///   starts with onto the line below, the cursor steps onto that line, its
    ///   indentation is corrected and the cursor passes the closer; otherwise a
    ///   closer left on the cursor's line is deleted unless Enter splits it
    ///   from its opener, Enter is pressed, and the new line is indented as the
    ///   target's next line is. Either way the cursor is past one more newline
    ///   of the target.
    /// - provides: the target's newline and the indentation after it, typed.
    /// - panics: a keystroke's check fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every line of every corpus source passes here; a
    ///   wrong step leaves the text off its target, which the per-keystroke
    ///   prefix check and the final equality reveal.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    #[spec(captures: [newlines = self.buffer().text().0.get(.. self.buffer().cursor().0)
            .map_or(0_usize, |before| before.matches('\n').count())],
        ensures: self.buffer().text().0.get(.. self.buffer().cursor().0)
            .is_some_and(|before| before.matches('\n').count() == newlines.saturating_add(1)))]
    fn newline(
        &mut self,
        junk: Text<'_>,
        following: Text<'_>,
    )
    {
        let wanted = following.0.split('\n').next().unwrap_or_default();
        let wanted_content = wanted.trim_start_matches(' ');
        let indent = Width(wanted.len().saturating_sub(wanted_content.len()));
        if let Some(below) = junk.0.strip_prefix('\n') {
            let line = below.split('\n').next().unwrap_or_default();
            let content = line.trim_start_matches(' ');
            if !content.is_empty() && wanted_content.starts_with(content) {
                let line_start = self.buffer().cursor().0.saturating_add(1);
                let content_start =
                    line_start.saturating_add(line.len().saturating_sub(content.len()));
                self.move_to(Offset(content_start));
                self.indent_to(indent);
                let past = self.buffer().cursor().0.saturating_add(content.len());
                self.move_to(Offset(past));
                return;
            }
        }
        let on_line = junk.0.split('\n').next().unwrap_or_default();
        let splits = match self.buffer().previous_char() {
            | Maybe::Present(previous) => {
                previous != Key('"')
                    && matches!(closer_of(previous), Maybe::Present(Key(closer))
                        if on_line.starts_with(closer) && on_line.len() == closer.len_utf8())
            },
            | Maybe::Absent(_) => false,
        };
        if !splits {
            for _ in on_line.chars() {
                self.delete();
            }
        }
        self.enter();
        self.indent_to(indent);
    }

    /// Restore the indentation of the cursor's line to the one the target
    /// text up to the cursor, `target`, gives it, after the editor outdented
    /// a typed closer.
    ///
    /// # Specification
    /// - requires: the text before the cursor's line is `target`'s, and the
    ///   line's content after its indentation is `target`'s last line's.
    /// - ensures: the text up to the cursor is `target`, the cursor where it
    ///   was relative to the line's content.
    /// - provides: the writer's correction of an outdent.
    /// - panics: a keystroke's check fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every indented closer of the corpus passes here; a
    ///   wrong correction leaves the text off its target, which the
    ///   per-keystroke prefix check reveals.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    #[spec(ensures: self.buffer().text().0.get(.. self.buffer().cursor().0) == Some(target.0))]
    fn repair_outdent(
        &mut self,
        target: Text<'_>,
    )
    {
        let wanted = target.0.rsplit('\n').next().unwrap_or_default();
        let line = String::from(self.buffer().line_before_cursor().0);
        let want = Width(
            wanted
                .len()
                .saturating_sub(wanted.trim_start_matches(' ').len()),
        );
        let have = line
            .len()
            .saturating_sub(line.trim_start_matches(' ').len());
        if want == Width(have) {
            return;
        }
        let line_start = self.buffer().cursor().0.saturating_sub(line.len());
        self.move_to(Offset(line_start.saturating_add(have)));
        self.indent_to(want);
        let content = line.len().saturating_sub(have);
        let past = self.buffer().cursor().0.saturating_add(content);
        self.move_to(Offset(past));
    }

    /// Correct the indentation before the cursor to `width` spaces, with
    /// backspaces and spaces.
    ///
    /// # Specification
    /// - requires: the cursor's line holds only spaces before the cursor.
    /// - ensures: the cursor's line holds exactly `width` spaces before the
    ///   cursor.
    /// - provides: the writer's correction of a guessed indentation.
    /// - panics: the line holds anything but spaces before the cursor, or a
    ///   keystroke's check fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every indented corpus line passes here; a wrong width
    ///   shows as a text off its target.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body reads the line before the cursor at every keystroke; the check reads it once before and twice after"
        )
    )]
    #[spec(requires: self.buffer().line_before_cursor().0.chars().all(|character| character == ' '),
        ensures: self.buffer().line_before_cursor().0.len() == width.0
            && self.buffer().line_before_cursor().0.chars().all(|character| character == ' '))]
    fn indent_to(
        &mut self,
        width: Width,
    )
    {
        loop {
            let line = self.buffer().line_before_cursor().0;
            assert!(
                line.chars().all(|character| character == ' '),
                "only indentation stands before the cursor"
            );
            let current = Width(line.len());
            if current == width {
                return;
            }
            if current > width {
                self.backspace();
            }
            else {
                self.type_char(Key(' '));
            }
        }
    }
}
