//! The editor's side of a session: a buffer, a cursor, and the edit each
//! keystroke sends, as an editor that closes pairs and indents lines sends
//! it.
//!
//! The rules follow the editor defaults the gandr extension's language
//! configuration selects: `(`, `[`, `{` and `"` close themselves before
//! layout or punctuation, a typed closer steps over the one the editor
//! inserted, backspace inside an empty pair deletes both halves, Enter between
//! a pair opens an indented line between them, and a line ending in an
//! unclosed `{` or `(` indents the next. Positions are counted here, in UTF-16
//! code units, independently of the server's own line index.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde_json::Value;
use serde_json::json;

/// The indentation one nesting level adds: two spaces, as the corpus writes.
const UNIT: &str = "  ";

/// The characters before which a typed opener is closed: the editor default.
const CLOSE_BEFORE: &str = ";:.,=}])> \n\t";

quenchant_shape::reason_enum! {
    /// Why no character neighbours the cursor on one side.
    pub mod neighbour {
        /// The reason no character is there.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The cursor is at that edge of the text.
            Edge,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a character has no partner in a pair.
    pub mod paired {
        /// The reason no partner exists.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The character belongs to no pair on that side.
            Unpaired,
        }
    }
}

/// A byte offset into a buffer's text, on a character boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Offset(pub usize);

/// A run of text: what a buffer holds, or what a writer types or pastes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Text<'text>(pub &'text str);

/// One character as a writer types it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Key(pub char);

/// Whether the closer at the cursor was inserted by the editor for the
/// writer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Closer
{
    /// The editor inserted it: a typed closer steps over it.
    Pending,
    /// No inserted closer waits at the cursor.
    Settled,
}

/// Whether an undo would revert anything.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum History
{
    /// No edit is left to undo.
    Empty,
    /// At least one edit can be undone.
    Undoable,
}

/// Whether the cursor stands inside a string literal on its line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Quoting
{
    /// An odd count of unescaped quotes precedes it.
    Inside,
    /// An even count does.
    Outside,
}

/// The range on which two texts differ: from `start`, up to `old_end` in the
/// first and `new_end` in the second.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Difference
{
    /// Where the texts start to differ.
    start: Offset,
    /// Where the differing range ends in the first text.
    old_end: Offset,
    /// Where it ends in the second.
    new_end: Offset,
}

/// A position as the protocol counts it: a line and a UTF-16 column, both
/// from zero.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position
{
    /// The line.
    pub line: u32,
    /// The UTF-16 code units before the position on its line.
    pub character: u32,
}

impl Position
{
    /// The position of byte `at` of `text`.
    ///
    /// # Specification
    /// - requires: `at` is a character boundary of `text`.
    /// - ensures: the line counts the newlines before `at`; the character
    ///   counts the UTF-16 code units between the last of them and `at`.
    /// - provides: the protocol's spelling of a byte offset.
    /// - panics: `at` is not a character boundary, or a count passes
    ///   `u32::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every keystroke of the corpus replay and of the
    ///   scripts with non-ASCII text sends positions the server applies to the
    ///   same text the buffer holds; a miscounted line or column desynchronises
    ///   the two, which the differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::positions_count_utf16_code_units`
    #[spec(requires: text.0.is_char_boundary(at.0),
        ensures: |ret| text.0.get(.. at.0).is_some_and(|before|
            u32::try_from(before.matches('\n').count()) == Ok(ret.line)
                && u32::try_from(before.rsplit('\n').next().unwrap_or_default().encode_utf16().count())
                    == Ok(ret.character)))]
    pub fn of(
        text: Text<'_>,
        at: Offset,
    ) -> Self
    {
        let before = text
            .0
            .get(.. at.0)
            .expect("a position falls on a character boundary");
        let line_start = before
            .rfind('\n')
            .map_or(0_usize, |newline| newline.saturating_add(1));
        let column = before
            .get(line_start ..)
            .expect("a line starts after a newline")
            .encode_utf16()
            .count();
        Self {
            line: u32::try_from(before.matches('\n').count()).expect("a line count fits u32"),
            character: u32::try_from(column).expect("a column fits u32"),
        }
    }

    /// The position as the protocol's JSON writes it.
    ///
    /// # Specification
    /// trivial.
    pub fn json(self) -> Value
    {
        json!({ "line": self.line, "character": self.character })
    }
}

/// One edit an editor sends: the range it replaces, counted in the text
/// before it, and the text replacing it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Change
{
    /// Where the replaced range starts.
    pub start: Position,
    /// Where the replaced range ends.
    pub end: Position,
    /// The replacement.
    pub text: String,
}

impl Change
{
    /// The change as a `didChange` content change writes it.
    ///
    /// # Specification
    /// trivial.
    pub fn json(&self) -> Value
    {
        json!({
            "range": { "start": self.start.json(), "end": self.end.json() },
            "text": self.text,
        })
    }
}

/// How the buffer meets a typed bracket, quote or newline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Typing
{
    /// Every keystroke inserts exactly its character.
    Plain,
    /// Pairs close themselves and lines indent, as an editor assists.
    Assisted,
}

/// The state an undo returns to.
#[derive(Clone, Debug)]
struct Snapshot
{
    /// The text.
    text: String,
    /// The cursor.
    cursor: Offset,
    /// The closers the editor inserted and may step over.
    pending: Vec<Offset>,
}

/// An editor's buffer: its text, its cursor and its undo history.
#[derive(Clone, Debug)]
pub struct Buffer
{
    /// The text.
    text: String,
    /// The cursor, on a character boundary.
    cursor: Offset,
    /// How keystrokes are assisted.
    typing: Typing,
    /// The offsets of the closers the editor inserted for the writer, which a
    /// typed closer steps over and a backspace deletes with its opener.
    pending: Vec<Offset>,
    /// The states before each edit, latest last.
    history: Vec<Snapshot>,
}

impl Buffer
{
    /// A buffer holding `text`, the cursor at its end.
    ///
    /// # Specification
    /// trivial.
    pub fn holding(
        text: Text<'_>,
        typing: Typing,
    ) -> Self
    {
        Self {
            text: String::from(text.0),
            cursor: Offset(text.0.len()),
            typing,
            pending: Vec::new(),
            history: Vec::new(),
        }
    }

    /// The text.
    ///
    /// # Specification
    /// trivial.
    pub fn text(&self) -> Text<'_>
    {
        Text(&self.text)
    }

    /// The cursor.
    ///
    /// # Specification
    /// trivial.
    pub const fn cursor(&self) -> Offset
    {
        self.cursor
    }

    /// The cursor as the protocol counts it.
    ///
    /// # Specification
    /// trivial.
    pub fn position(&self) -> Position
    {
        Position::of(self.text(), self.cursor)
    }

    /// Whether an undo would revert an edit.
    ///
    /// # Specification
    /// trivial.
    pub const fn history(&self) -> History
    {
        if self.history.is_empty() {
            History::Empty
        }
        else {
            History::Undoable
        }
    }

    /// Move the cursor to `at`, as an arrow key or a click does; no edit.
    ///
    /// # Specification
    /// - requires: `at` is a character boundary of the text.
    /// - ensures: the cursor is `at`; the closers the editor would step over
    ///   are forgotten when the cursor leaves their line.
    /// - provides: navigation without an edit.
    /// - panics: `at` is not a character boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the random scripts move the cursor between edits, and
    ///   the corpus replay steps over closers on lines below; a cursor left off
    ///   a boundary or a stale closer misplaces the next edit, which the
    ///   differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
    #[spec(requires: self.text.is_char_boundary(at.0), ensures: self.cursor == at)]
    pub fn move_to(
        &mut self,
        at: Offset,
    )
    {
        assert!(
            self.text.is_char_boundary(at.0),
            "the cursor stays on a character boundary"
        );
        if line_start(self.text(), at) != line_start(self.text(), self.cursor) {
            self.pending.clear();
        }
        self.cursor = at;
    }

    /// The character after the cursor.
    ///
    /// # Specification
    /// trivial.
    pub fn next_char(&self) -> Maybe<Key, neighbour::Absent>
    {
        self.text
            .get(self.cursor.0 ..)
            .and_then(|rest| rest.chars().next())
            .map_or(Maybe::Absent(neighbour::Absent::Edge), |next| {
                Maybe::Present(Key(next))
            })
    }

    /// The character before the cursor.
    ///
    /// # Specification
    /// trivial.
    pub fn previous_char(&self) -> Maybe<Key, neighbour::Absent>
    {
        self.text
            .get(.. self.cursor.0)
            .and_then(|before| before.chars().next_back())
            .map_or(Maybe::Absent(neighbour::Absent::Edge), |previous| {
                Maybe::Present(Key(previous))
            })
    }

    /// Whether the editor inserted the closer at the cursor for the writer.
    ///
    /// # Specification
    /// trivial.
    pub fn closer(&self) -> Closer
    {
        if self.pending.contains(&self.cursor) {
            Closer::Pending
        }
        else {
            Closer::Settled
        }
    }

    /// The text from the start of the cursor's line to the cursor.
    ///
    /// # Specification
    /// trivial.
    pub fn line_before_cursor(&self) -> Text<'_>
    {
        let start = line_start(self.text(), self.cursor);
        Text(
            self.text
                .get(start.0 .. self.cursor.0)
                .expect("a line starts before its cursor"),
        )
    }

    /// Type `typed`, as one keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: plain typing inserts `typed` at the cursor. Assisted typing
    ///   steps over a closer or quote the editor inserted when `typed` is that
    ///   character; closes an opener, or a quote outside a string, when the
    ///   next character is layout, punctuation or the end; and outdents a `}`
    ///   or `)` typed first on an indented line by one level.
    /// - provides: the edits the keystroke sends: none when it only moved the
    ///   cursor.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus replay types every source and its final
    ///   text equals the source, so a rule that inserts too much or too little
    ///   shows as a divergent buffer; each edit is also held to the server's
    ///   text through the differential answers.
    /// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::assisted_typing_closes_and_steps_over_pairs`
    #[spec(captures: [length = self.text.len()],
        ensures: |ret| ret.len() <= 1
            && self.text.len() <= length.saturating_add(typed.0.len_utf8().saturating_mul(2))
            && self.text.is_char_boundary(self.cursor.0))]
    pub fn type_char(
        &mut self,
        typed: Key,
    ) -> Vec<Change>
    {
        let mut spelled = [0_u8; 4];
        let spelled = Text(typed.0.encode_utf8(&mut spelled));
        if self.typing == Typing::Plain {
            return vec![self.insert(spelled)];
        }
        let next = self.next_char();
        if matches!(opener_of(typed), Maybe::Present(_))
            && next == Maybe::Present(typed)
            && self.closer() == Closer::Pending
        {
            let at = Offset(self.cursor.0.saturating_add(typed.0.len_utf8()));
            let cursor = self.cursor;
            self.pending.retain(|&pending| pending != cursor);
            self.cursor = at;
            return Vec::new();
        }
        let closes_before = match next {
            Maybe::Present(Key(next)) => CLOSE_BEFORE.contains(next),
            Maybe::Absent(_) => true,
        };
        if let Maybe::Present(Key(closes)) = closer_of(typed)
            && closes_before
            && !(typed == Key('"') && quoting(self.line_before_cursor()) == Quoting::Inside)
        {
            let mut pair = String::from(spelled.0);
            pair.push(closes);
            let closer = Offset(self.cursor.0.saturating_add(typed.0.len_utf8()));
            let change = self.splice(self.cursor, self.cursor, Text(&pair), closer);
            self.pending.push(closer);
            return vec![change];
        }
        if matches!(typed, Key('}' | ')')) {
            let line = self.line_before_cursor().0;
            if !line.is_empty() && line.chars().all(|character| character == ' ') {
                let kept = line.len().saturating_sub(UNIT.len());
                let start = line_start(self.text(), self.cursor);
                let mut replaced = " ".repeat(kept);
                replaced.push(typed.0);
                let cursor = Offset(start.0.saturating_add(replaced.len()));
                return vec![self.splice(start, self.cursor, Text(&replaced), cursor)];
            }
        }
        vec![self.insert(spelled)]
    }

    /// Press Enter, as one keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: plain typing inserts a newline. Assisted typing carries the
    ///   line's indentation onto the new line, one level deeper after an
    ///   unclosed `{` or `(`; between an opener and its closer it opens an
    ///   indented line and moves the closer to the line after it.
    /// - provides: the edit the keystroke sends.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus replay presses Enter for every line of
    ///   every source and re-indents to the source's indentation, so a wrong
    ///   indentation or a lost closer shows as extra keystrokes or a divergent
    ///   final text.
    /// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::assisted_typing_closes_and_steps_over_pairs`
    #[spec(ensures: |ret| ret.text.starts_with('\n') && ret.start == ret.end
        && self.text.is_char_boundary(self.cursor.0))]
    pub fn enter(&mut self) -> Change
    {
        if self.typing == Typing::Plain {
            return self.insert(Text("\n"));
        }
        let line = self.line_before_cursor().0;
        let indent: String = line
            .chars()
            .take_while(|&character| character == ' ')
            .collect();
        let deeper = deepening(Text(line)).0;
        if let Maybe::Present(previous) = self.previous_char()
            && previous != Key('"')
            && let Maybe::Present(closes) = closer_of(previous)
            && self.next_char() == Maybe::Present(closes)
        {
            let mut inserted = format!("\n{indent}{UNIT}");
            let cursor = Offset(self.cursor.0.saturating_add(inserted.len()));
            inserted.push('\n');
            inserted.push_str(&indent);
            return self.splice(self.cursor, self.cursor, Text(&inserted), cursor);
        }
        self.insert(Text(&format!("\n{indent}{deeper}")))
    }

    /// Press backspace, as one keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: at the start of the text nothing changes. Otherwise plain
    ///   typing deletes the character before the cursor; assisted typing
    ///   deletes an empty pair the editor closed whole, and the indentation
    ///   before the cursor back to the previous level.
    /// - provides: the edits the keystroke sends: none at the start.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus replay backspaces surplus indentation and
    ///   the random scripts backspace anywhere, pairs included; a wrong
    ///   deletion width desynchronises the buffer from the server, which the
    ///   differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::assisted_typing_closes_and_steps_over_pairs`
    #[spec(captures: [length = self.text.len(), cursor = self.cursor],
        ensures: |ret| ret.len() <= 1 && ret.iter().all(|change| change.text.is_empty())
            && self.text.len() <= length && self.cursor <= cursor)]
    pub fn backspace(&mut self) -> Vec<Change>
    {
        let Maybe::Present(previous) = self.previous_char()
        else {
            return Vec::new();
        };
        let start = Offset(self.cursor.0.saturating_sub(previous.0.len_utf8()));
        if self.typing == Typing::Assisted {
            if let Maybe::Present(closes) = closer_of(previous)
                && self.next_char() == Maybe::Present(closes)
                && self.closer() == Closer::Pending
            {
                let end = Offset(self.cursor.0.saturating_add(closes.0.len_utf8()));
                return vec![self.splice(start, end, Text(""), start)];
            }
            let line = self.line_before_cursor().0;
            if !line.is_empty() && line.chars().all(|character| character == ' ') {
                let width = line
                    .len()
                    .saturating_sub(1)
                    .checked_rem(UNIT.len())
                    .expect("the indentation unit is not empty")
                    .saturating_add(1);
                let start = Offset(self.cursor.0.saturating_sub(width));
                return vec![self.splice(start, self.cursor, Text(""), start)];
            }
        }
        vec![self.splice(start, self.cursor, Text(""), start)]
    }

    /// Press delete, as one keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the character after the cursor is deleted; at the end of the
    ///   text nothing changes.
    /// - provides: the edits the keystroke sends: none at the end.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the random scripts delete forward anywhere, and the
    ///   corpus replay deletes the closers it leaves unused; a wrong width
    ///   desynchronises the buffer, which the differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
    #[spec(captures: [length = self.text.len(), cursor = self.cursor],
        ensures: |ret| ret.len() <= 1 && ret.iter().all(|change| change.text.is_empty())
            && self.cursor == cursor
            && (ret.is_empty() == (self.text.len() == length)))]
    pub fn delete(&mut self) -> Vec<Change>
    {
        let Maybe::Present(next) = self.next_char()
        else {
            return Vec::new();
        };
        let end = Offset(self.cursor.0.saturating_add(next.0.len_utf8()));
        vec![self.splice(self.cursor, end, Text(""), self.cursor)]
    }

    /// Replace the bytes `start .. end` with `text`, as a paste over a
    /// selection does, leaving the cursor after the replacement.
    ///
    /// # Specification
    /// - requires: `start <= end`, both character boundaries of the text.
    /// - ensures: the text holds `text` in place of the range.
    /// - provides: the edit the replacement sends.
    /// - panics: a bound is not a character boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the random scripts paste and delete whole lines, the
    ///   erasure deletes a line per step; a misplaced range desynchronises the
    ///   buffer, which the differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::sweeps::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    #[spec(requires: start <= end && self.text.is_char_boundary(start.0) && self.text.is_char_boundary(end.0),
        ensures: |ret| ret.text == text.0
            && self.text.get(start.0 .. self.cursor.0) == Some(text.0))]
    pub fn replace(
        &mut self,
        start: Offset,
        end: Offset,
        text: Text<'_>,
    ) -> Change
    {
        let cursor = Offset(start.0.saturating_add(text.0.len()));
        self.splice(start, end, text, cursor)
    }

    /// Undo the latest edit, as one keystroke.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text, the cursor and the closers return to their state
    ///   before the latest edit not yet undone; with none left nothing changes.
    /// - provides: the edit the undo sends: the one range on which the two
    ///   texts differ, as an editor sends it; none when nothing changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the random scripts undo every edit they made and the
    ///   final publication must equal the opening one; a wrong range leaves a
    ///   different text, which that comparison and the differential answers
    ///   reveal.
    /// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
    #[spec(captures: [restored = self.history.last().map(|snapshot| snapshot.text.clone())],
        ensures: |ret| ret.len() <= 1
            && restored.as_ref().is_none_or(|text| *text == self.text))]
    pub fn undo(&mut self) -> Vec<Change>
    {
        let Some(snapshot) = self.history.pop()
        else {
            return Vec::new();
        };
        let difference = difference(self.text(), Text(&snapshot.text));
        let replacement = snapshot
            .text
            .get(difference.start.0 .. difference.new_end.0)
            .expect("the differing range is on character boundaries");
        let change = Change {
            start: Position::of(self.text(), difference.start),
            end: Position::of(self.text(), difference.old_end),
            text: String::from(replacement),
        };
        self.text = snapshot.text;
        self.cursor = snapshot.cursor;
        self.pending = snapshot.pending;
        if change.start == change.end && change.text.is_empty() {
            return Vec::new();
        }
        vec![change]
    }

    /// Insert `text` at the cursor, leaving the cursor after it.
    ///
    /// # Specification
    /// trivial.
    fn insert(
        &mut self,
        text: Text<'_>,
    ) -> Change
    {
        let cursor = Offset(self.cursor.0.saturating_add(text.0.len()));
        self.splice(self.cursor, self.cursor, text, cursor)
    }

    /// Replace `start .. end` with `text` and put the cursor at `cursor`,
    /// recording the state before for an undo.
    ///
    /// # Specification
    /// - requires: `start <= end`, both character boundaries; `cursor` is a
    ///   character boundary of the text after the replacement.
    /// - ensures: the text holds `text` in place of the range; each pending
    ///   closer after the range moves with it and each inside it is forgotten;
    ///   the state before is the latest undo entry.
    /// - provides: the edit, counted in the text before it.
    /// - panics: a bound is not a character boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every edit of every scenario goes through here and
    ///   the server applies the change it returns; a miscounted range or a lost
    ///   closer desynchronises the two, which the differential answers reveal.
    /// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    #[spec(requires: start <= end && self.text.is_char_boundary(start.0) && self.text.is_char_boundary(end.0),
        captures: [edits = self.history.len()],
        ensures: |ret| ret.text == text.0 && self.cursor == cursor
            && self.history.len() == edits.saturating_add(1)
            && self.text.get(start.0 ..).is_some_and(|after| after.starts_with(text.0)))]
    fn splice(
        &mut self,
        start: Offset,
        end: Offset,
        text: Text<'_>,
        cursor: Offset,
    ) -> Change
    {
        self.history.push(Snapshot {
            text: self.text.clone(),
            cursor: self.cursor,
            pending: self.pending.clone(),
        });
        let change = Change {
            start: Position::of(self.text(), start),
            end: Position::of(self.text(), end),
            text: String::from(text.0),
        };
        self.text.replace_range(start.0 .. end.0, text.0);
        let removed = end.0.saturating_sub(start.0);
        self.pending.retain_mut(|pending| {
            if *pending >= end {
                *pending = Offset(
                    pending
                        .0
                        .saturating_sub(removed)
                        .saturating_add(text.0.len()),
                );
                true
            }
            else {
                *pending < start
            }
        });
        assert!(
            self.text.is_char_boundary(cursor.0),
            "an edit leaves the cursor on a character boundary"
        );
        self.cursor = cursor;
        change
    }
}

/// The closer an opener or a quote takes.
///
/// # Specification
/// trivial.
pub const fn closer_of(opener: Key) -> Maybe<Key, paired::Absent>
{
    match opener {
        Key('(') => Maybe::Present(Key(')')),
        Key('[') => Maybe::Present(Key(']')),
        Key('{') => Maybe::Present(Key('}')),
        Key('"') => Maybe::Present(Key('"')),
        _ => Maybe::Absent(paired::Absent::Unpaired),
    }
}

/// The opener a closer or a quote ends.
///
/// # Specification
/// trivial.
pub const fn opener_of(closer: Key) -> Maybe<Key, paired::Absent>
{
    match closer {
        Key(')') => Maybe::Present(Key('(')),
        Key(']') => Maybe::Present(Key('[')),
        Key('}') => Maybe::Present(Key('{')),
        Key('"') => Maybe::Present(Key('"')),
        _ => Maybe::Absent(paired::Absent::Unpaired),
    }
}

/// Where the line holding `at` starts.
///
/// # Specification
/// trivial.
fn line_start(
    text: Text<'_>,
    at: Offset,
) -> Offset
{
    Offset(
        text.0
            .get(.. at.0)
            .and_then(|before| before.rfind('\n'))
            .map_or(0_usize, |newline| newline.saturating_add(1)),
    )
}

/// Whether the cursor after `line` stands inside a string: an odd count of
/// unescaped quotes before it on its line.
///
/// # Specification
/// trivial.
fn quoting(line: Text<'_>) -> Quoting
{
    let mut inside = false;
    let mut escaped = false;
    for character in line.0.chars() {
        match character {
            '\\' if inside => escaped = !escaped,
            '"' if !escaped => inside = !inside,
            _ => escaped = false,
        }
    }
    if inside {
        Quoting::Inside
    }
    else {
        Quoting::Outside
    }
}

/// The indentation a line ending at the cursor adds to the next: one level
/// when its last `{` or `(` is followed by no closer and no quote, the
/// editor's increase pattern, and none otherwise.
///
/// # Specification
/// trivial.
fn deepening(line: Text<'_>) -> Text<'static>
{
    let opens = [('{', '}'), ('(', ')')]
        .into_iter()
        .any(|(opener, closer)| {
            line.0.rfind(opener).is_some_and(|at| {
                line.0
                    .get(at ..)
                    .is_some_and(|rest| !rest.contains([closer, '"', '\'']))
            })
        });
    Text(if opens { UNIT } else { "" })
}

/// The one range on which `old` and `new` differ: the longest common prefix
/// and the longest common suffix that does not overlap it, both on character
/// boundaries.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `old` and `new` agree before `start` and after their ends, and
///   `start` is at most either end.
/// - provides: the range an editor sends for an undo.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every undo of the random scripts sends this range; a
///   range too wide still applies, but one too narrow or misplaced leaves the
///   server's text different from the buffer's, which the differential answers
///   reveal.
/// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
#[spec(ensures: |ret| {
    let agreed_before = old.0.get(.. ret.start.0) == new.0.get(.. ret.start.0);
    let old_after = old.0.get(ret.old_end.0 ..);
    let new_after = new.0.get(ret.new_end.0 ..);
    ret.start <= ret.old_end && ret.start <= ret.new_end && agreed_before && old_after == new_after
})]
fn difference(
    old: Text<'_>,
    new: Text<'_>,
) -> Difference
{
    let start = old
        .0
        .char_indices()
        .zip(new.0.chars())
        .find(|&((_, ours), theirs)| ours != theirs)
        .map_or_else(|| old.0.len().min(new.0.len()), |((at, _), _)| at);
    let limit = old.0.len().min(new.0.len()).saturating_sub(start);
    let mut suffix = 0_usize;
    for (ours, theirs) in old.0.chars().rev().zip(new.0.chars().rev()) {
        let next = suffix.saturating_add(ours.len_utf8());
        if ours != theirs || next > limit {
            break;
        }
        suffix = next;
    }
    Difference {
        start: Offset(start),
        old_end: Offset(old.0.len().saturating_sub(suffix)),
        new_end: Offset(new.0.len().saturating_sub(suffix)),
    }
}
