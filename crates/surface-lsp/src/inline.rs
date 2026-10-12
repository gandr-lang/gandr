//! Inline completion: the material the parser expects at the cursor, as the
//! ghost text an editor shows there.
//!
//! The parser closes the input at a prefix without changing its state:
//! [`Completion::innermost`] is the material that closes the innermost open
//! form, with the holes of the operators above it. [`ghost()`] reads that
//! material at the cursor and spells it as a snippet: a tile as its text, a
//! lexical class or a hole as a tab stop.

use alloc::string::String;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_parser::CandidateLabel;
use gandr_surface_parser::Completion;
use gandr_surface_parser::Expected;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::TileSpelling;
use gandr_surface_parser::label;
use gandr_surface_parser::tile_spelling;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// A snippet in the protocol's snippet syntax: literal text with tab stops.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Snippet(String);

impl From<Snippet> for String
{
    /// The snippet's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(snippet: Snippet) -> Self
    {
        snippet.0
    }
}

impl AsRef<str> for Snippet
{
    /// The snippet's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

quenchant_shape::reason_enum! {
    /// Why no ghost text is shown at a cursor.
    pub mod ghost {
        /// The reason none is shown.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Text follows the cursor on its line: the expected material may
            /// already be written there.
            LineContinues,
            /// The cursor ends or sits inside a comment.
            InComment,
            /// The form at the cursor expects nothing more.
            Complete,
        }
    }
}

/// The ghost text the parser expects at byte `at` of `text`, under
/// `grammar`.
///
/// # Specification
/// - requires: nothing; an offset past the text or inside a character is read
///   as the nearest character boundary at or before it.
/// - ensures: [`ghost::Absent::LineContinues`] when anything but whitespace
///   follows the cursor before the line ends; [`ghost::Absent::InComment`] when
///   the text before the cursor ends in a line comment, a shebang or an
///   unterminated block comment; otherwise the innermost material of the
///   top-level form the cursor ends, molded alone up to the cursor and read
///   through [`Completion::innermost`], spelled as [`spell`] states, or
///   [`ghost::Absent::Complete`] when that material is empty.
/// - provides: the answer to `textDocument/inlineCompletion`.
/// - fails: never.
/// - panics: none.
/// - intension: one labelling of the text before the cursor and one molding of
///   the form the cursor ends; the text after the cursor is never read past its
///   line, so it cannot answer for the parser's lookahead.
///
/// # Adequacy
/// - hypothesis: L3 — cursors after an open bracket, a parameter list, a
///   binding arrow, an unfinished `case`, an unsaturated operator, a string,
///   inside a comment, before trailing text and after a finished form, each
///   asserted at the exact snippet or reason. Reading past the cursor, molding
///   from the document start rather than the form, or showing the whole
///   material rather than the innermost changes one of them.
/// - witness: `inline::tests::ghost_text_closes_the_innermost_form`
/// - witness: `inline::tests::no_ghost_text_where_text_or_a_comment_stands`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref snippet) => !snippet.0.is_empty(),
    Maybe::Absent(_) => true,
})]
pub fn ghost(
    grammar: &Pbg,
    text: SourceText<'_>,
    at: ByteOffset,
) -> Maybe<Snippet, ghost::Absent>
{
    let text = <&str>::from(text);
    let at = text.floor_char_boundary(usize::from(at));
    let (before, after) = text.split_at(at);
    let rest_of_line = after.split(['\n', '\r']).next().unwrap_or_default();
    if !rest_of_line.trim().is_empty() {
        return Maybe::Absent(ghost::Absent::LineContinues);
    }
    let tokens = label(SourceFragment::from(before));
    if let Some(last) = tokens.last()
        && last.lexeme == Lexeme::Space
    {
        let start = usize::try_from(last.start).unwrap_or(usize::MAX);
        let layout = before.get(start ..).unwrap_or_default();
        if layout.starts_with("//")
            || layout.starts_with("#!")
            || (layout.starts_with("/*") && !layout.ends_with("*/"))
        {
            return Maybe::Absent(ghost::Absent::InComment);
        }
    }
    let source = SourceText::from(before);
    let mut molder = Molder::new(grammar);
    let mut state = MeldState::new(grammar);
    if let Some(&form) = molder.form_runs(&tokens, source).last() {
        molder.mold_run(&mut state, &tokens, form, source);
    }
    let completion: Completion = state.expected();
    let snippet = spell(completion.innermost(), source);
    if snippet.0.is_empty() {
        return Maybe::Absent(ghost::Absent::Complete);
    }
    Maybe::Present(snippet)
}

/// `material` spelled as a snippet to insert after `before`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each item in order: a tile as the text [`tile_spelling`] gives
///   it, escaped for the snippet syntax; a lexical class as a tab stop naming
///   the class; a hole of an expression, a pattern or a type as a tab stop
///   holding `?`, the hole a gandr source writes, and a hole of any other sort
///   as a tab stop naming the sort; grout as nothing. Tab stops are numbered
///   from 1 in order. Items are separated by one space, and the first from
///   `before` by one, except after an opening bracket or whitespace and before
///   a closing bracket, a comma, a semicolon or a quote.
/// - provides: the ghost text's snippet.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ghost-text witness asserts tiles, classes, holes,
///   escapes and each spacing rule at exact snippets.
/// - witness: `inline::tests::ghost_text_closes_the_innermost_form`
#[spec(ensures: |ret| !material.is_empty() || ret.0.is_empty())]
fn spell(
    material: &[Expected],
    before: SourceText<'_>,
) -> Snippet
{
    let joins = |last: Option<char>| match last {
        | Some(character) if !character.is_whitespace() && !matches!(character, '(' | '[') => {
            Spacing::Spaced
        },
        | Some(_) | None => Spacing::Tight,
    };
    let mut snippet = String::new();
    let mut stop = 0_u32;
    let mut joint = joins(<&str>::from(before).chars().next_back());
    for &item in material {
        let piece = match item {
            | Expected::Tile(label) => match tile_spelling(CandidateLabel::from(label)) {
                | TileSpelling::Literal(text) => Piece::Text(text),
                | TileSpelling::Class(class) => Piece::Stop(class),
            },
            | Expected::Hole(sort) => placeholder(sort),
            | Expected::Grout(_) => continue,
        };
        if joint == Spacing::Spaced && piece.spacing() == Spacing::Spaced {
            snippet.push(' ');
        }
        match piece {
            | Piece::Text(text) => {
                for character in text.chars() {
                    if matches!(character, '$' | '}' | '\\') {
                        snippet.push('\\');
                    }
                    snippet.push(character);
                }
                joint = joins(text.chars().next_back());
            },
            | Piece::Stop(name) => {
                stop = stop.saturating_add(1);
                let _written = write!(snippet, "${{{stop}:{name}}}");
                joint = Spacing::Spaced;
            },
        }
    }
    Snippet(snippet)
}

/// Whether a space separates two pieces of a snippet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spacing
{
    /// The pieces are written against each other.
    Tight,
    /// One space separates them.
    Spaced,
}

/// One item of a snippet: literal text, or a tab stop's placeholder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Piece<'text>
{
    /// Text inserted as written.
    Text(&'text str),
    /// A tab stop holding this placeholder.
    Stop(&'text str),
}

impl Piece<'_>
{
    /// How the piece meets what comes before it: against a closing bracket,
    /// a comma, a semicolon or a quote, with a space otherwise.
    ///
    /// # Specification
    /// trivial.
    fn spacing(self) -> Spacing
    {
        match self {
            | Self::Text(")" | "]" | "," | ";" | "\"" | "'") => Spacing::Tight,
            | Self::Text(_) | Self::Stop(_) => Spacing::Spaced,
        }
    }
}

/// The tab stop a hole of `sort` shows.
///
/// # Specification
/// trivial.
const fn placeholder(sort: Sort) -> Piece<'static>
{
    Piece::Stop(match sort {
        | Sort::Expression | Sort::Pattern | Sort::Type => "?",
        | Sort::Item => "item",
        | Sort::Instantiation => "instantiation",
        | Sort::ModuleMember => "member",
    })
}

#[cfg(test)]
mod tests
{
    use gandr_surface_grammar::built_in;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::ghost;

    /// The ghost text between `before` and `after`.
    ///
    /// # Specification
    /// trivial.
    fn at_end(
        before: SourceText<'_>,
        after: SourceText<'_>,
    ) -> Maybe<String, ghost::Absent>
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let before = <&str>::from(before);
        let text = format!("{before}{}", <&str>::from(after));
        let at = ByteOffset::from(before.len());
        match super::ghost(&grammar, SourceText::from(text.as_str()), at) {
            | Maybe::Present(snippet) => Maybe::Present(String::from(snippet)),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    #[test]
    fn ghost_text_closes_the_innermost_form()
    {
        let hole = format!("${{{}:?}}", 1_u8);
        for (before, want) in [
            ("def x = f(1", ")".to_owned()),
            ("def x = (", ")".to_owned()),
            ("def x = [1, 2", "]".to_owned()),
            ("def x =", format!(" {hole};")),
            ("def x = 1 +", format!(" {hole};")),
            ("def x = 1 + (2", ")".to_owned()),
            ("def x = \"abc", "\"".to_owned()),
            ("def x = \"abc ", "\"".to_owned()),
            (
                "def f(x: Nat) -> -F Nat {\n  run y <-",
                format!(" {hole}; \\}}"),
            ),
            ("def f(x: Nat) -> -F Nat {\n  case x {", " \\}".to_owned()),
            ("def x = 1;\ndef y = (", ")".to_owned()),
            ("def x = #!{ echo hi", " \\}".to_owned()),
            (
                "def",
                format!(" ${{{}:identifier}} : ${{{}:?}};", 1_u8, 2_u8),
            ),
        ] {
            assert_eq!(
                Maybe::Present(want),
                at_end(SourceText::from(before), SourceText::from("")),
                "after `{before}`"
            );
        }
    }

    #[test]
    fn no_ghost_text_where_text_or_a_comment_stands()
    {
        for (before, after, reason) in [
            ("def x = (", " 1)", ghost::Absent::LineContinues),
            ("def x = 1; // (", "", ghost::Absent::InComment),
            ("def x = 1; /* (", "", ghost::Absent::InComment),
            ("def x = 1;", "", ghost::Absent::Complete),
            ("", "", ghost::Absent::Complete),
        ] {
            assert_eq!(
                Maybe::Absent(reason),
                at_end(SourceText::from(before), SourceText::from(after)),
                "`{before}` before `{after}`"
            );
        }
        assert_eq!(
            Maybe::Present(")".to_owned()),
            at_end(
                SourceText::from("def x = ("),
                SourceText::from("   \ndef y = 2;")
            ),
            "whitespace after the cursor and the lines below it are not read"
        );
    }
}
