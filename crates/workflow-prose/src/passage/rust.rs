//! The comments of a Rust source, cut into the passages the sentence rules
//! read.
//!
//! A Rust comment holds prose by default. Each paragraph of `///`, `//!` or
//! `//` lines is a passage, and so is each list item. The reader names a part
//! that holds no prose by its marks, never by a guess. A lexer follows the
//! strings, the characters and the block comments of the source, so a `//`
//! inside a string opens no comment.
//!
//! No passage holds these parts:
//!
//! - A fenced code block, from a line that opens with three backticks to the
//!   next such line.
//! - An indented code block: a line indented by four spaces or a tab outside a
//!   list item.
//! - A heading, such as `# Safety`. The text under it is prose.
//! - A table row, which opens with `|`.
//! - A link footer, which opens with `[label]:`.
//! - A clause line of the specification attribute, with the indented lines that
//!   continue it. The clauses are `- ensures:`, `- requires:`, `- hypothesis:`,
//!   `- witness:`, `- executable:` and `- allocation:`, with the reference
//!   lines `- see:`, `- owes:` and `- cites:`. Each has a grammar and a check
//!   of its own.
//! - A `#[doc = …]` attribute's string and a block comment. They are no line
//!   comment, and the reader does not read them.
//! - Code in a comment: a `//` paragraph whose first line opens with the syntax
//!   of Rust. A keyword, a mark that opens or closes code, or a word joined to
//!   a call, a macro or a path opens it. The reader counts these lines.
//!
//! Text inside backticks stays in its passage, so the sentence parses whole.
//! It is code, and no rule reads it as prose.

use super::Cut;
use super::Line;
use super::Paragraph;
use super::Source;
use super::Text;
use super::footer_label;
use super::itemised;
use super::unlabelled;

/// The labels of the clause lines and the reference lines, whose list items
/// hold no prose.
const CLAUSES: [&str; 9] = [
    "ensures",
    "requires",
    "hypothesis",
    "witness",
    "executable",
    "allocation",
    "see",
    "owes",
    "cites",
];

/// The keywords of Rust. Each opens code when it opens a `//` paragraph.
const KEYWORDS: [&str; 38] = [
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
    "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
    "unsafe", "use", "where", "while",
];

/// The marks that open or close code. Each opens code when it opens a `//`
/// paragraph.
const MARKS: [&str; 11] = ["{", "}", ")", "]", ";", "&", "#[", "#![", "::", "=>", "->"];

/// The marks that join a word to a call, a macro or a path.
const JOINS: [&str; 5] = ["(", "!(", "![", "!{", "::"];

/// The marker a comment line opens with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Marker
{
    /// `///`, an outer doc comment.
    Outer,
    /// `//!`, an inner doc comment.
    Inner,
    /// `//`, a line comment.
    Line,
}

/// Where the lexer stands at the end of a line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State
{
    /// In code.
    Code,
    /// In a string, which a `"` with no escape closes.
    Quoted,
    /// In a raw string, which a `"` and this count of `#` close.
    Raw(usize),
    /// In block comments, at this depth.
    Block(usize),
}

/// The comment of one line.
#[derive(Clone, Copy, Debug)]
enum Found<'line>
{
    /// No comment, or one inside a string or a block comment.
    Nothing,
    /// A comment that opens its line, with its marker and the text after it.
    Opening(Marker, Text<'line>),
    /// A comment after code on its line, with the text after its `//`.
    Trailing(Text<'line>),
}

/// How a `//` paragraph opens.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opening
{
    /// With prose.
    Prose,
    /// With the syntax of Rust: code in a comment.
    Code,
}

/// What the open list item holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Item
{
    /// No list item is open.
    Closed,
    /// A list item of prose.
    Prose,
    /// A clause line or a reference line, which holds no prose.
    Clause,
}

/// The comment of `line`, read from `state`. The lexer moves `state` to where
/// the line ends.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a `//` in a string, in a raw string over three lines,
///   after a quote character, after a lifetime, in a block comment over three
///   lines and after a byte with an escape; a string, a character or a block
///   read as code finds a comment the source does not hold.
/// - witness: `passage::rust::tests::a_string_holds_no_comment`
fn found<'line>(
    state: &mut State,
    line: Text<'line>,
) -> Found<'line>
{
    let mut chars = line.0.char_indices().peekable();
    let mut word = false;
    while let Some((at, c)) = chars.next() {
        match *state {
            State::Block(depth) => {
                if c == '*' && chars.next_if(|&(_, next)| next == '/').is_some() {
                    *state = match depth.saturating_sub(1) {
                        0 => State::Code,
                        rest => State::Block(rest),
                    };
                }
                else if c == '/' && chars.next_if(|&(_, next)| next == '*').is_some() {
                    *state = State::Block(depth.saturating_add(1));
                }
            },
            State::Quoted => {
                if c == '\\' {
                    chars.next();
                }
                else if c == '"' {
                    *state = State::Code;
                }
            },
            State::Raw(hashes) => {
                if c == '"' {
                    let mut ahead = chars.clone();
                    if (0 .. hashes).all(|_| ahead.next_if(|&(_, next)| next == '#').is_some()) {
                        chars = ahead;
                        *state = State::Code;
                    }
                }
            },
            State::Code => {
                if c == '/' && chars.next_if(|&(_, next)| next == '/').is_some() {
                    let rest = Text(line.0.get(at.saturating_add(2) ..).unwrap_or_default());
                    let before = line.0.get(.. at).unwrap_or_default();
                    return if before.trim().is_empty() {
                        opened(rest)
                    }
                    else {
                        Found::Trailing(rest)
                    };
                }
                if c == '/' && chars.next_if(|&(_, next)| next == '*').is_some() {
                    *state = State::Block(1);
                }
                else if c == '"' {
                    *state = State::Quoted;
                }
                else if c == '\'' {
                    let mut ahead = chars.clone();
                    let literal = match ahead.next() {
                        Some((_, '\\')) => {
                            ahead.next();
                            ahead.any(|(_, next)| next == '\'')
                        },
                        Some(_) => ahead.next_if(|&(_, next)| next == '\'').is_some(),
                        None => false,
                    };
                    if literal {
                        chars = ahead;
                    }
                }
                else if !word && matches!(c, 'r' | 'b' | 'c') {
                    let mut ahead = chars.clone();
                    if c == 'r' || ahead.next_if(|&(_, next)| next == 'r').is_some() {
                        let mut hashes = 0_usize;
                        while ahead.next_if(|&(_, next)| next == '#').is_some() {
                            hashes = hashes.saturating_add(1);
                        }
                        if ahead.next_if(|&(_, next)| next == '"').is_some() {
                            chars = ahead;
                            *state = State::Raw(hashes);
                        }
                    }
                }
                word = c.is_alphanumeric() || c == '_';
            },
        }
    }
    Found::Nothing
}

/// The comment that opens its line with `//` and then `rest`, by its marker.
/// A fourth slash makes a line comment, as rustdoc reads it.
///
/// # Specification
/// trivial.
fn opened(rest: Text<'_>) -> Found<'_>
{
    match rest.0.strip_prefix('/') {
        Some(outer) if !outer.starts_with('/') => Found::Opening(Marker::Outer, Text(outer)),
        Some(_) => Found::Opening(Marker::Line, rest),
        None => rest
            .0
            .strip_prefix('!')
            .map_or(Found::Opening(Marker::Line, rest), |inner| {
                Found::Opening(Marker::Inner, Text(inner))
            }),
    }
}

/// How the `//` text `text` opens: with the syntax of Rust, or with prose. A
/// word joins a call when a `.`, a method's name and a `(` or a `::<` follow
/// it.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a `let`, a method call, a closing brace, an attribute, a
///   macro, a path and a `for` each open code, and a sentence, a continued line
///   and a keyword with a hyphen open prose; a missing mark or a wider one
///   changes the count and the passages.
/// - witness: `passage::rust::tests::code_in_a_comment_is_skipped_and_counted`
fn opening(text: Text<'_>) -> Opening
{
    let named = |text: &str| {
        text.find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(text.len())
    };
    let text = text.0;
    let (word, after) = text.split_at_checked(named(text)).unwrap_or((text, ""));
    let keyword =
        KEYWORDS.contains(&word) && !after.starts_with(|c: char| c == '-' || c == '\'' || c == '’');
    let method = after.strip_prefix('.').is_some_and(|rest| {
        let end = named(rest);
        end > 0
            && rest
                .get(end ..)
                .is_some_and(|tail| tail.starts_with('(') || tail.starts_with("::<"))
    });
    let joined = !word.is_empty() && (method || JOINS.iter().any(|join| after.starts_with(join)));
    if keyword || joined || MARKS.iter().any(|mark| text.starts_with(mark)) {
        Opening::Code
    }
    else {
        Opening::Prose
    }
}

/// The comment passages of a Rust source, and the code lines in its `//`
/// comments.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of the comment lines of one marker that
///   open their lines, `///`, `//!` or `//`, and one per list item. A paragraph
///   ends at a blank comment line, a line of another marker, a line that is no
///   comment, a list item and each part of the module docs' list. A list item's
///   indented lines join it, and its text after a label of lowercase words and
///   a colon is the passage. Each comment after code on its line is a passage
///   of one line. A `//` paragraph, or a comment after code, that [`opening`]
///   reads as code is no passage, and its lines are the count. Each passage
///   starts on its first line.
/// - provides: the Rust comments the sentence rules read under the base.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Cost
/// - allocation: the passages, growth within the source
///
/// # Adequacy
/// - hypothesis: L3 — a hand-written comment for each part the module docs
///   list, beside the prose that stays; a part read as prose, prose left out,
///   two paragraphs joined or a code line not counted changes the passages or
///   the count.
/// - witness: `passage::rust::tests::a_doc_comment_cuts_into_paragraphs_and_items`
/// - witness: `passage::rust::tests::the_marked_parts_hold_no_prose`
/// - witness: `passage::rust::tests::code_in_a_comment_is_skipped_and_counted`
/// - witness: `passage::rust::tests::a_string_holds_no_comment`
#[inline]
#[must_use]
pub fn comments(
    path: Text<'_>,
    text: Text<'_>,
) -> Cut
{
    let mut paragraph = Paragraph::new(path, Source::Rust);
    let mut state = State::Code;
    let mut marker = None;
    let mut fenced = false;
    let mut item = Item::Closed;
    let mut skipping = false;
    let mut code = 0_usize;
    for (index, raw) in text.0.lines().enumerate() {
        let line = Line(index.saturating_add(1));
        let (kind, content) = match found(&mut state, Text(raw)) {
            Found::Opening(kind, content) => (kind, content.0),
            other @ (Found::Nothing | Found::Trailing(_)) => {
                paragraph.close();
                marker = None;
                fenced = false;
                item = Item::Closed;
                skipping = false;
                if let Found::Trailing(trailing) = other {
                    let trailing = trailing.0.trim();
                    if opening(Text(trailing)) == Opening::Code {
                        code = code.saturating_add(1);
                    }
                    else if !trailing.is_empty() {
                        paragraph.push(line, Text(trailing));
                        paragraph.close();
                    }
                }
                continue;
            },
        };
        if marker != Some(kind) {
            paragraph.close();
            marker = Some(kind);
            fenced = false;
            item = Item::Closed;
            skipping = false;
        }
        let content = content.strip_prefix(' ').unwrap_or(content);
        let trimmed = content.trim();
        if skipping {
            if trimmed.is_empty() {
                skipping = false;
            }
            else {
                code = code.saturating_add(1);
            }
            continue;
        }
        if trimmed.starts_with("```") || trimmed.starts_with("~~~") {
            paragraph.close();
            item = Item::Closed;
            fenced = !fenced;
            continue;
        }
        if fenced {
            continue;
        }
        if trimmed.is_empty() {
            paragraph.close();
            item = Item::Closed;
            continue;
        }
        let indented = content.starts_with([' ', '\t']);
        if indented && item != Item::Closed {
            if item == Item::Prose {
                paragraph.push(line, Text(trimmed));
            }
            continue;
        }
        if item != Item::Closed {
            paragraph.close();
            item = Item::Closed;
        }
        let heading = trimmed.trim_start_matches('#');
        let headed = trimmed.starts_with('#') && (heading.is_empty() || heading.starts_with(' '));
        if content.starts_with("    ")
            || content.starts_with('\t')
            || headed
            || trimmed.starts_with('|')
            || footer_label(Text(trimmed)).is_some()
        {
            paragraph.close();
            continue;
        }
        if let Some(listed) = itemised(Text(trimmed)) {
            paragraph.close();
            let clause = listed
                .0
                .split_once(':')
                .is_some_and(|(label, _)| CLAUSES.contains(&label));
            if clause {
                item = Item::Clause;
            }
            else {
                item = Item::Prose;
                paragraph.push(line, unlabelled(listed).unwrap_or(listed));
            }
            continue;
        }
        if kind == Marker::Line
            && paragraph.open.is_empty()
            && opening(Text(trimmed)) == Opening::Code
        {
            skipping = true;
            code = code.saturating_add(1);
            continue;
        }
        paragraph.push(line, Text(trimmed));
    }
    paragraph.close();
    Cut {
        passages: paragraph.passages,
        code,
    }
}

#[cfg(test)]
mod tests
{
    use super::Source;
    use super::Text;
    use super::comments;

    /// The line and the text of each passage of `text`, and the count of code
    /// lines.
    ///
    /// # Specification
    /// trivial.
    fn read(text: Text<'_>) -> (Vec<(String, String)>, usize)
    {
        let cut = comments(Text("crates/a/src/lib.rs"), text);
        assert!(
            cut.passages
                .iter()
                .all(|passage| passage.source == Source::Rust
                    && passage.path == "crates/a/src/lib.rs")
        );
        (
            cut.passages
                .iter()
                .map(|passage| (passage.line.to_string(), passage.text.clone()))
                .collect(),
            cut.code,
        )
    }

    /// Owned copies of the pairs of line and text `pairs`.
    ///
    /// # Specification
    /// trivial.
    fn owned<const N: usize>(pairs: [(&str, &str); N]) -> Vec<(String, String)>
    {
        pairs
            .into_iter()
            .map(|(line, text)| (line.to_owned(), text.to_owned()))
            .collect()
    }

    #[test]
    fn a_doc_comment_cuts_into_paragraphs_and_items()
    {
        let text = r"/// The first paragraph
/// wraps here.
///
/// - provides: the prose of the item.
/// - a plain item
///   continues here.
/// The last paragraph.
//! Inner.
// Line.
fn x() {}
";
        assert_eq!(
            read(Text(text)),
            (
                owned([
                    ("1", "The first paragraph wraps here."),
                    ("4", "the prose of the item."),
                    ("5", "a plain item continues here."),
                    ("7", "The last paragraph."),
                    ("8", "Inner."),
                    ("9", "Line."),
                ]),
                0
            )
        );
    }

    #[test]
    fn the_marked_parts_hold_no_prose()
    {
        let text = r#"/// # Safety
///
/// The body is prose.
///
/// ```
/// let past = 1;
/// The kernel reduced it.
/// ```
///
///     The kernel reduced it.
///
/// | The kernel | reduced it |
/// | - | - |
///
/// [label]: https://example.invalid "A title"
///
/// - ensures: the kernel reduced it.
///   It wrapped here.
/// - requires: the kernel reduced it.
/// - hypothesis: L3 — the kernel reduced it.
/// - witness: `tests::x`
/// - executable: none — the kernel reduced it.
/// - allocation: the kernel's text, setup
/// - see: the kernel reduced it.
/// - owes: the kernel reduced it.
/// - cites: [label]
#[doc = "The kernel reduced it."]
/* The kernel reduced it.
// The kernel reduced it.
*/
fn x() {}
"#;
        assert_eq!(read(Text(text)), (owned([("3", "The body is prose.")]), 0));
    }

    #[test]
    fn code_in_a_comment_is_skipped_and_counted()
    {
        let text = r"// let x = 1;
// x.push(2);
//
// The prose returns, and
// let it wrap.
//
// }
// #[cfg(test)]
// assert_eq!(a, b);
// Self::new()
//
// for x in xs {
//
// self-check holds.
let y = 2; // y.push(3);
let z = 3; // The note after code.
";
        assert_eq!(
            read(Text(text)),
            (
                owned([
                    ("4", "The prose returns, and let it wrap."),
                    ("14", "self-check holds."),
                    ("16", "The note after code."),
                ]),
                8
            )
        );
    }

    #[test]
    fn a_string_holds_no_comment()
    {
        let text = r###"let a = "// The kernel reduced it.";
let b = r#"
/// The kernel reduced it.
"#;
let c = '"'; // The note after a quote character.
let d = "two lines
// The kernel reduced it.
";
fn f<'a>(x: &'a str) {} // The note after a lifetime.
/* A block
// The kernel reduced it.
*/
/// The doc after the block.
let e = b'\''; // The note after a byte.
let g = "\"// The kernel reduced it.";
"###;
        assert_eq!(
            read(Text(text)),
            (
                owned([
                    ("5", "The note after a quote character."),
                    ("9", "The note after a lifetime."),
                    ("13", "The doc after the block."),
                    ("14", "The note after a byte."),
                ]),
                0
            )
        );
    }
}
