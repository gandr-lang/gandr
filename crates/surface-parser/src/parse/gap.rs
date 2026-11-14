//! Where a separator, a closer or a keyword left out or misspelt is minted:
//! the gap, sibling-separator and edit-distance signals of #4696, judged by
//! the melder.
//!
//! Inside a bracketed group whose items stand one a line, the gap before a
//! line tells where an item ends. In
//!
//! ```text
//! def lcSyntax : *{
//!   empty : () -> con,
//!   subTm :
//!   extendTm : con -> con,
//! } = …;
//! ```
//!
//! the field `subTm` waits for its type, and the next line stands at the
//! column of the record's fields. The melder reads `extendTm` as the type of
//! `subTm`, so the next `:` cannot stand, and the misreading takes every form
//! after it down with it. The gap says that a new field begins there, and the
//! `,` before it is left out. Under juxtaposition a word left alone at a
//! line's end reads the next line as its argument in the same way.
//!
//! The search reads the labelled tokens with a stack of the brackets open at
//! each one. A group opened by `(`, `[`, `*{`, `+{`, `&{` or `#{` takes `,`
//! between its items. Its items' column is that of the first token after the
//! opener, when that token begins a line. Its limit is the column of the line
//! that opens it. A token that begins a line, other than a closer or a
//! separator, after a token that opens nothing, gives a place:
//!
//! |the line stands|the place mints|
//! |---|---|
//! |at or left of an open group's limit|that group's closer, innermost first|
//! |then, right of the group's limit and at or left of its items' column|a `,` |
//!
//! Each place is written at the end of the token before the line, so the
//! repair it owes stands on the line the item leaves. A line at column zero
//! gives no place, since the layout pass closes every bracket there. A brace
//! block and a layout block take no `,`, and a shell block or an
//! interpolation hides its contents from the search.
//!
//! A written closer can close a bracket that is not the innermost open one,
//! as the `}` of a block can meet a `(` that a line of the block leaves open.
//! Each bracket opened inside that bracket is then left open. When each of
//! them is a written bracket, the place at the end of the token before the
//! closer mints the closer of each of them, innermost first. The scan still
//! reads the closer as the close of the innermost bracket, so every other
//! place stays as it is. The search tries this place with the places before
//! each line.
//!
//! Three more signals give places on one line:
//!
//! |signal|the place|it mints|
//! |---|---|---|
//! |sibling separators|between two operands side by side, directly inside a group|a `,`|
//! |a returner after an operand|between an operand and a `-F` after it, which juxtaposition takes as no argument|a `->`|
//! |edit distance|a word that is no keyword, with a keyword near it in [`misspelt`]|the keyword, over the word|
//!
//! The melder judges each place, as its dry run judges a candidate. The
//! places before each line are tried in source order. Then the sibling,
//! arrow and keyword places are tried nearest an obligation first, where an
//! obligation before a place counts at twice its distance. The search tries
//! [`COPIES`] places in all. Each place is judged in a copy of the top-level
//! form it stands in, from a line at column zero to the next, with every
//! place kept there before it. The form alone is melded once for its count,
//! so a trial never melds the rest of the source. A place is kept when its
//! copy owes fewer obligations than the form alone, each minted tile counting
//! as one. A closer, a sibling separator, an arrow or a keyword is kept only
//! when its copy owes nothing but its minted tiles. A `)` deleted inside a
//! line reads as well at the line's end with a repair left over, and a `,`
//! between the wrong two operands of a parameter list reads with a repair
//! left over. The source with every kept place written in is melded once more
//! for the tree. The tree is the copy's, each written tile read back at its
//! place: a closer as a minted close, a `,` as an empty postfix grout and a
//! `->` as an empty infix grout, each owing one [`Oblig::MissingTile`], and a
//! keyword as a prefix grout over the misspelt word, owing one
//! [`Oblig::IncompleteTile`]. The lowering refuses each grout and each minted
//! close where it stands. A source that owes nothing runs no search.
//!
//! - Alternatives: a hard rule in the layout pass, which writes the `,` at
//!   every such line, changes a valid source that continues an item at its
//!   items' column; the placement search of `place.rs`, which takes a copy only
//!   when it owes nothing, takes none while the line being typed is unfinished.
//! - Reversal: when the melder's own dry run can read a soft separator before a
//!   line, the places become its candidates and this search goes.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RESERVED_WORDS;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::edit_distance;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::CloseReach;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use super::ParseResult;
use super::molded;
use super::molded_moving;
use super::spliced;
use crate::label::Bracket;
use crate::label::Lexeme;
use crate::label::Move;
use crate::label::SourceBytes;
use crate::label::Token;
use crate::label::bracket;
use crate::label::cut_in;
use crate::label::label;
use crate::meld::Splice;
use crate::meld::Stands;
use crate::meld::declaration_head;
use crate::mold::STATEMENT_LEADS;
use crate::oblig::Oblig;
use crate::oblig::ObligationInstance;

/// The most places the search tries, in source order.
const COPIES: usize = 16;

/// What an open bracket is to the search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A group whose items `,` separates, closed by its closer.
    Group(&'static str),
    /// A brace or layout block, whose items `;` separates.
    Block,
    /// A shell block or an interpolation, whose contents the search does not
    /// read.
    Opaque,
}

/// Where a group's items stand.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Items
{
    /// No token follows the opener yet.
    Unread,
    /// The first token follows the opener on its line.
    Inline,
    /// The first token begins a line at this column.
    At(u32),
}

/// One open bracket.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// What the bracket is.
    kind: Kind,
    /// The column of the line that opens it.
    limit: u32,
    /// Where its items stand.
    items: Items,
    /// The closer its written opener takes: none for a layout block, a shell
    /// block or an interpolation.
    closer: Option<&'static str>,
    /// For each of `)`, `]` and `}`, in that order, the index in the stack of
    /// the nearest frame, this one included, whose written opener takes that
    /// closer.
    nearest: [Option<usize>; 3],
    /// Whether its first item is a label, as `.A` in `Path[.A = T]`.
    labelled: bool,
}

/// What a place does to the copy that judges it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Act
{
    /// The tiles written at the end of a token, in order, or one tile written
    /// in place of a misspelt word.
    Writes
    {
        /// The tiles, each its own token.
        tiles: Vec<&'static str>,
        /// How many source bytes from the place the tile replaces: none for a
        /// tile left out.
        over: usize,
    },
    /// The line that begins at the place stays in a layout block that its
    /// column closes.
    Moves
    {
        /// How many of the blocks that the line's column closes the line
        /// closes, innermost first.
        closes: u32,
    },
}

/// One place, and what it does to the copy that judges it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Gap
{
    /// Where the tiles are written, or where the moved line begins.
    at: ByteOffset,
    /// What the place writes or moves.
    act: Act,
    /// Whether the place is kept only when its copy owes nothing in the
    /// top-level form it stands in: a closer, a sibling separator, an arrow,
    /// an attribute opener, a keyword or a move. A `,` alone before a line is
    /// kept by its count.
    cleared: bool,
}

/// The places the signals give: the gap's before each line, the sibling
/// separators' between two operands side by side, the arrows' between an
/// operand and a returner, the attribute openers' before a line that a `]`
/// with no `[` ends or a keyword follows, and the words a keyword may stand
/// for.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Places<'text>
{
    /// The gap before a line, in source order.
    lines: Vec<Gap>,
    /// A `,` between two operands side by side in a group, in source order.
    siblings: Vec<Gap>,
    /// A `->` between an operand and a `-F` after it on its line, in source
    /// order.
    arrows: Vec<Gap>,
    /// A `@[` before the first word of a line that holds a `]` with no open
    /// `[` before it, when the `]` ends the line or a keyword follows it, in
    /// source order.
    openers: Vec<Gap>,
    /// Each word of two or more characters that is no keyword, where it
    /// stands, in source order.
    words: Vec<(ByteOffset, SourceText<'text>)>,
}

/// The spelling of `token` in `text`.
///
/// # Specification
/// trivial.
fn spelling(
    text: SourceText<'_>,
    token: Token,
) -> SourceText<'_>
{
    SourceText::from(
        usize::try_from(token.start)
            .ok()
            .zip(usize::try_from(token.end).ok())
            .and_then(|(start, end)| <&str>::from(text).get(start .. end))
            .unwrap_or_default(),
    )
}

/// The bracket a token opens or closes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Bracketing
{
    /// It opens a bracket of this kind.
    Opens(Kind),
    /// It closes the innermost bracket.
    Closes,
    /// It opens and closes no bracket.
    #[default]
    Neither,
}

/// How a token stands to an operand it is part of.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Edge
{
    /// It can begin an operand and end one: a word that is no keyword, or a
    /// literal.
    Both,
    /// It can begin an operand: a bare `(`, `*{` or `#[`.
    Begins,
    /// It can end an operand: a closer.
    Ends,
    /// It neither begins nor ends an operand.
    #[default]
    Neither,
}

/// What one token is to the search.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Class
{
    /// The bracket the token opens or closes.
    bracketing: Bracketing,
    /// How the token stands to an operand.
    edge: Edge,
    /// Whether it is a `,` or a `;`, a separator a line may begin with.
    separates: bool,
    /// Whether it is a lower-case word of two or more bytes that is no
    /// keyword, which a keyword may stand for.
    word: bool,
    /// Whether it is `-F`, the returner. Its band is looser than a type's
    /// juxtaposition, so it is no argument of the operand before it.
    returner: bool,
}

/// What `token` is to the search. A keyword opens a form rather than
/// standing as an operand, so a word that is a keyword neither begins nor
/// ends one.
///
/// # Specification
/// trivial.
fn class(
    text: SourceText<'_>,
    token: Token,
) -> Class
{
    let spelled = <&str>::from(spelling(text, token));
    match token.lexeme {
        Lexeme::LowerWord | Lexeme::UpperWord => {
            let operand = !RESERVED_WORDS.contains(&spelled) && !STATEMENT_LEADS.contains(&spelled);
            Class {
                edge: if operand { Edge::Both } else { Edge::Neither },
                word: operand && token.lexeme == Lexeme::LowerWord && spelled.len() >= 2,
                ..Class::default()
            }
        },
        Lexeme::Number | Lexeme::TypedNumber | Lexeme::Character => Class {
            edge: Edge::Both,
            ..Class::default()
        },
        Lexeme::Punct => Class {
            bracketing: match bracket(token, SourceBytes::from(<&str>::from(text).as_bytes())) {
                Bracket::Open => Bracketing::Opens(match spelled {
                    "{" => Kind::Block,
                    "*{" | "+{" | "&{" | "#{" => Kind::Group("}"),
                    _ if spelled.ends_with('{') => Kind::Opaque,
                    _ if spelled.ends_with('(') => Kind::Group(")"),
                    _ => Kind::Group("]"),
                }),
                Bracket::Close => Bracketing::Closes,
                Bracket::Neither => Bracketing::Neither,
            },
            edge: match spelled {
                ")" | "]" | "}" => Edge::Ends,
                "(" | "*{" | "#[" => Edge::Begins,
                _ => Edge::Neither,
            },
            separates: matches!(spelled, "," | ";"),
            word: false,
            returner: spelled == "-F",
        },
        Lexeme::LayoutOpen => Class {
            bracketing: Bracketing::Opens(Kind::Block),
            ..Class::default()
        },
        Lexeme::SubshellOpen => Class {
            bracketing: Bracketing::Opens(Kind::Opaque),
            ..Class::default()
        },
        Lexeme::LayoutClose | Lexeme::SubshellClose => Class {
            bracketing: Bracketing::Closes,
            ..Class::default()
        },
        Lexeme::Quote
        | Lexeme::StringFragment
        | Lexeme::ShellStringFragment
        | Lexeme::EscapeSequence
        | Lexeme::ShellWord
        | Lexeme::EnvAssign
        | Lexeme::SingleQuotedContent
        | Lexeme::VariableName
        | Lexeme::FileDescriptor
        | Lexeme::ArmBar
        | Lexeme::LayoutSemi
        | Lexeme::Space
        | Lexeme::Unknown => Class::default(),
    }
}

/// The places the gap before each line, the layout closers before it, the
/// sibling separators, the arrows before a returner and the attribute
/// openers before a stray `]` give in `text`, labelled as `tokens`, and the
/// words a keyword may stand for.
///
/// # Specification
/// - requires: `tokens` label `text`.
/// - ensures: in `lines`, one place per line that begins, right of column zero,
///   with a token that neither closes nor separates, after a token that opens
///   nothing, with no shell block or interpolation open, where the line stands
///   at or left of an open group's limit or at or left of the innermost group's
///   items' column: the closer of each group whose limit the line reaches,
///   innermost first, then a `,` when the line stands right of the next group's
///   limit and at or left of its items' column and the token before the line is
///   no `,`. In `siblings`, a `,` between each two tokens on one line, apart,
///   the first ending an operand and the second beginning one, directly inside
///   a group. In `arrows`, a `->` between each two tokens on one line, apart,
///   the first ending an operand and the second `-F`, with no shell block or
///   interpolation open. Each place stands at the end of the token before it,
///   in source order. In `openers`, a `@[` at the first token of the line or of
///   the block member that holds each `]` with no shell block or interpolation
///   open and with a brace or layout block or no bracket innermost, when that
///   first token is a lower-case word of two or more bytes that is no keyword
///   and stands before the `]`, and when the `]` is the last significant token,
///   the next one begins a line, or the next one is a keyword. A block member
///   begins after a block opens and after a written `;`. Also in `lines`, `k`
///   moves at the first token of each line before which the layout pass closes
///   `k > 0` blocks, one for each count of closes from 0 to `k - 1`, when the
///   token neither closes nor separates, no shell block or interpolation is
///   open, and the innermost open frame is none or a layout block whose items
///   stand at another column. Also in `lines`, at the end of the token before
///   each written closer that closes an open bracket other than the innermost,
///   with no shell block or interpolation open and only written brackets opened
///   inside that bracket: the closer of each of those brackets, innermost
///   first. The scan reads the closer as the close of the innermost bracket, as
///   it reads every closer. In `words`, each lower-case word of two or more
///   bytes that is no keyword, outside a shell block or an interpolation, in
///   source order.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — a field left without its type before the next field, a
///   field whose `(` the line leaves open, a `(` left open before a block's
///   `}`, a block's `{` left open before a `)`, a valid record, a line at
///   column zero, two parameters side by side in a parameter list, a type
///   beside a returner, an attribute without its `@[` on its own line or after
///   a block's `{`, a whole attribute, a stray `]` before an operator, and a
///   misspelt keyword each give their places or none.
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
/// - witness: `parse::gap::tests::a_separator_left_out_between_siblings_is_minted_5433`
/// - witness: `parse::gap::tests::an_arrow_left_out_before_a_returner_is_minted_5501`
/// - witness: `parse::gap::tests::an_attribute_opener_left_out_is_minted_4398`
/// - witness: `parse::gap::tests::a_misspelt_keyword_owes_its_word_5433`
/// - witness: `parse::gap::tests::a_source_that_owes_nothing_keeps_its_parse_5433`
/// - witness: `parse::gap::tests::a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434`
/// - witness: `parse::gap::tests::a_bracket_left_open_before_a_closer_of_another_family_is_closed_there_6103`
fn gaps<'text>(
    text: SourceText<'text>,
    tokens: &[Token],
) -> Places<'text>
{
    let mut places = Places::default();
    let mut stack: Vec<Frame> = Vec::new();
    // How many frames of `stack` are a shell block or an interpolation, whose
    // contents the search does not read.
    let mut opaque = 0_usize;
    let mut line_start = 0_u32;
    let mut line_column = 0_u32;
    let mut broken = false;
    // How many layout blocks the pass closes after the last significant
    // token.
    let mut closing = 0_u32;
    // The token before the current one: where it ends, whether it opens a
    // bracket, whether it is a `,`, and whether it ends an operand.
    let mut previous: Option<(u32, bool, bool, bool)> = None;
    // Whether the previous token is a word, and where the `]` before the
    // current token ends when it closes a labelled bracket.
    let mut previous_word = false;
    let mut closed_labelled: Option<u32> = None;
    // The first token of the current line or block member: where it starts,
    // and whether it is a word that an attribute may begin with.
    let mut head: Option<(u32, bool)> = None;
    // Whether the next significant token begins a block member: after a
    // block opens, or after a written `;`. The layout pass writes its `;`
    // where a line ends, and the next line's first token begins it.
    let mut member = false;
    // The first word of the member that holds a `]` that may close an
    // attribute without its `@[`. The token after the `]` decides it: an
    // attribute's `]` ends its line or comes before a keyword, and a `]` before
    // an operator or an operand closes an expression.
    let mut attribute: Option<u32> = None;
    // Whether a keyword at the top level starts the head the scan reads, and
    // where the `)` before the current token ends when it closes a group at
    // the top level. `sort_named` counts the tokens of `sort <name>` read so
    // far, so that its `=` stays inside the head's type.
    let mut keyword_head = false;
    let mut closed_head: Option<u32> = None;
    let mut sort_named = 0_u8;
    let opener = |start: u32| Gap {
        at: ByteOffset::from(usize::try_from(start).unwrap_or(usize::MAX)),
        act: Act::Writes {
            tiles: alloc::vec!["@["],
            over: 0,
        },
        cleared: true,
    };
    // The index of a closer among `)`, `]` and `}`, the closers a written
    // opener takes.
    let family = |closer: &str| match closer {
        ")" => Some(0_usize),
        "]" => Some(1),
        "}" => Some(2),
        _ => None,
    };
    // A frame links to the nearest frame of each family from the one below
    // it, so a closer finds the bracket it closes with no search.
    let open =
        |stack: &[Frame], kind: Kind, limit: u32, items: Items, closer: Option<&'static str>| {
            let mut nearest = stack.last().map_or([None; 3], |top| top.nearest);
            if let Some(slot) = closer.and_then(family).and_then(|at| nearest.get_mut(at)) {
                *slot = Some(stack.len());
            }
            Frame {
                kind,
                limit,
                items,
                closer,
                nearest,
                labelled: false,
            }
        };
    for &token in tokens {
        match token.lexeme {
            Lexeme::Space => {
                if let Some(last) = <&str>::from(spelling(text, token)).rfind('\n') {
                    broken = true;
                    line_start = token
                        .start
                        .saturating_add(u32::try_from(last).unwrap_or(u32::MAX))
                        .saturating_add(1);
                }
                continue;
            },
            Lexeme::LayoutSemi => continue,
            Lexeme::LayoutOpen => {
                stack.push(open(&stack, Kind::Block, line_column, Items::Unread, None));
                member = true;
                continue;
            },
            Lexeme::LayoutClose => {
                closing = closing.saturating_add(1);
                if stack.pop().is_some_and(|frame| frame.kind == Kind::Opaque) {
                    opaque = opaque.saturating_sub(1);
                }
                continue;
            },
            Lexeme::LowerWord
            | Lexeme::UpperWord
            | Lexeme::Number
            | Lexeme::TypedNumber
            | Lexeme::Character
            | Lexeme::Quote
            | Lexeme::StringFragment
            | Lexeme::ShellStringFragment
            | Lexeme::EscapeSequence
            | Lexeme::Punct
            | Lexeme::ShellWord
            | Lexeme::EnvAssign
            | Lexeme::SingleQuotedContent
            | Lexeme::VariableName
            | Lexeme::SubshellOpen
            | Lexeme::SubshellClose
            | Lexeme::FileDescriptor
            | Lexeme::ArmBar
            | Lexeme::Unknown => {},
        }
        let class = class(text, token);
        let column = token.start.saturating_sub(line_start);
        let leads = core::mem::replace(&mut broken, false);
        if leads {
            line_column = column;
        }
        if let Some(start) = attribute.take()
            && (leads || RESERVED_WORDS.contains(&<&str>::from(spelling(text, token))))
        {
            places.openers.push(opener(start));
        }
        if leads || core::mem::replace(&mut member, false) {
            head = Some((token.start, class.word));
        }
        // A keyword at the top level starts a head, and its `=`, a `;` or a
        // block ends it. The `=` of `with sort <name> = <type>` stays inside
        // the head's type.
        if stack.is_empty() && opaque == 0 {
            let spelled = <&str>::from(spelling(text, token));
            let sort_equation = sort_named == 2 && spelled == "=";
            sort_named = match (sort_named, spelled) {
                (_, "sort") => 1,
                (1, _) if matches!(class.edge, Edge::Both) => 2,
                _ => 0,
            };
            if token.lexeme == Lexeme::LowerWord && RESERVED_WORDS.contains(&spelled) {
                keyword_head = true;
            }
            else if !sort_equation
                && (matches!(spelled, "=" | ";")
                    || class.bracketing == Bracketing::Opens(Kind::Block))
            {
                keyword_head = false;
            }
        }
        // A line before which the layout pass closes blocks, and which stands
        // at no column of a block left open, may stay in each block it closes.
        // A word at column zero begins a form, so no form holds one after its
        // first line.
        if leads
            && closing > 0
            && opaque == 0
            && class.bracketing != Bracketing::Closes
            && !class.separates
            && match stack.last() {
                None => true,
                Some(&Frame {
                    kind: Kind::Block,
                    items: Items::At(items),
                    ..
                }) => items != column,
                Some(_) => false,
            }
        {
            let at = ByteOffset::from(usize::try_from(token.start).unwrap_or(usize::MAX));
            places.lines.extend((0 .. closing).map(|closes| Gap {
                at,
                act: Act::Moves { closes },
                cleared: true,
            }));
        }
        if leads
            && column > 0
            && opaque == 0
            && class.bracketing != Bracketing::Closes
            && !class.separates
            && let Some((end, false, comma, _)) = previous
        {
            let mut tiles = Vec::new();
            while let Some(&Frame {
                kind: Kind::Group(closer),
                limit,
                ..
            }) = stack.last()
                && column <= limit
            {
                tiles.push(closer);
                let _closed = stack.pop();
            }
            if let Some(&Frame {
                kind: Kind::Group(_),
                limit,
                items: Items::At(items),
                ..
            }) = stack.last()
                && limit < column
                && column <= items
                && !comma
            {
                tiles.push(",");
            }
            if !tiles.is_empty() {
                let cleared = tiles.iter().any(|&tile| tile != ",");
                places.lines.push(Gap {
                    at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                    act: Act::Writes { tiles, over: 0 },
                    cleared,
                });
            }
        }
        if !leads
            && opaque == 0
            && let Some((end, false, false, true)) = previous
            && end < token.start
            && matches!(class.edge, Edge::Begins | Edge::Both)
            && let Some(&Frame {
                kind: Kind::Group(_),
                ..
            }) = stack.last()
        {
            places.siblings.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec![","],
                    over: 0,
                },
                cleared: true,
            });
        }
        // `-F` binds looser than a type's juxtaposition, so it cannot be the
        // argument of the operand before it. Read as its row form, it takes
        // down the form around it. A `->` between the two reads the operand
        // as a domain and the returner as its codomain.
        if !leads
            && opaque == 0
            && class.returner
            && let Some((end, false, false, true)) = previous
            && end < token.start
        {
            places.arrows.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec!["->"],
                    over: 0,
                },
                cleared: true,
            });
        }
        // A declaration's head writes its result type after the `)` of its
        // parameter list, with a `->` between them. Without the `->`, the
        // type reads as a second parameter list or an argument of the head.
        // A `->` after the `)` reads the type as the head's result again.
        if !leads
            && opaque == 0
            && keyword_head
            && stack.is_empty()
            && let Some(end) = closed_head
            && end < token.start
            && matches!(class.edge, Edge::Begins | Edge::Both)
        {
            places.arrows.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec!["->"],
                    over: 0,
                },
                cleared: true,
            });
        }
        // A declaration's head ends at its `=`, before the body. A `*{` opens
        // a value, never a type, so a head whose `=` is left out reads the
        // body as an argument of the type before it. An `=` before the `*{`
        // ends the type there again.
        if !leads
            && opaque == 0
            && keyword_head
            && stack.is_empty()
            && <&str>::from(spelling(text, token)) == "*{"
            && let Some((end, false, false, true)) = previous
            && end < token.start
        {
            places.arrows.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec!["="],
                    over: 0,
                },
                cleared: true,
            });
        }
        // An attribute whose `@[` the source leaves out leaves its words and a
        // `]` that closes no `[` in its block. The words read as a type or a
        // call, and the `]` takes down the block around them. A `@[` before
        // the member's first word reads them as the attribute again.
        if opaque == 0
            && <&str>::from(spelling(text, token)) == "]"
            && matches!(
                stack.last(),
                None | Some(&Frame {
                    kind: Kind::Block,
                    ..
                })
            )
            && let Some((start, true)) = head
            && start < token.start
        {
            attribute = Some(start);
        }
        if let Some(frame) = stack.last_mut()
            && frame.items == Items::Unread
        {
            frame.items = if leads {
                Items::At(column)
            }
            else {
                Items::Inline
            };
            frame.labelled = <&str>::from(spelling(text, token)).starts_with('.');
        }
        // A labelled argument in brackets, as `.A = T` in `Path[.A = T](x, y)`,
        // holds a type, and the `(` written against the type's last word
        // opens the arguments after the `]`. Without the `]`, the arguments
        // read as an application of the type, and the bracket stays open to
        // the end of the form. A `]` before the `(` closes the bracket there.
        if opaque == 0
            && previous_word
            && <&str>::from(spelling(text, token)) == "("
            && let Some((end, false, false, true)) = previous
            && end == token.start
            && let Some(&Frame {
                kind: Kind::Group("]"),
                labelled: true,
                ..
            }) = stack.last()
        {
            places.arrows.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec!["]"],
                    over: 0,
                },
                cleared: true,
            });
        }
        // The arguments after a labelled bracket open with a `(`. A word
        // written against the `]` shows that the `(` is left out, and the
        // word joins the type as an argument. A `(` after the `]` opens the
        // arguments there again.
        if opaque == 0
            && matches!(token.lexeme, Lexeme::LowerWord | Lexeme::UpperWord)
            && let Some(end) = closed_labelled
            && end == token.start
        {
            places.arrows.push(Gap {
                at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                act: Act::Writes {
                    tiles: alloc::vec!["("],
                    over: 0,
                },
                cleared: true,
            });
        }
        if class.word && opaque == 0 {
            places.words.push((
                ByteOffset::from(usize::try_from(token.start).unwrap_or(usize::MAX)),
                spelling(text, token),
            ));
        }
        let mut labelled = false;
        match class.bracketing {
            Bracketing::Opens(kind) => {
                if kind == Kind::Opaque {
                    opaque = opaque.saturating_add(1);
                }
                let closer = match kind {
                    Kind::Group(closer) => Some(closer),
                    Kind::Block => Some("}"),
                    Kind::Opaque => None,
                };
                stack.push(open(&stack, kind, line_column, Items::Unread, closer));
            },
            Bracketing::Closes => {
                // A written closer of another family than the innermost
                // bracket shows that each bracket opened inside the one it
                // closes is left open. Their closers stand before it. The
                // scan still reads the closer as the close of the innermost
                // bracket, so that each place it gives without this one
                // stays.
                let spelled = <&str>::from(spelling(text, token));
                let matched = stack
                    .last()
                    .zip(family(spelled))
                    .and_then(|(top, at)| top.nearest.get(at).copied().flatten())
                    .filter(|_| token.lexeme == Lexeme::Punct && opaque == 0);
                let above = matched
                    .and_then(|at| stack.get(at.saturating_add(1) ..))
                    .unwrap_or_default();
                let tiles: Vec<&'static str> =
                    above.iter().rev().map_while(|frame| frame.closer).collect();
                if let Some((end, ..)) = previous
                    && !tiles.is_empty()
                    && tiles.len() == above.len()
                {
                    places.lines.push(Gap {
                        at: ByteOffset::from(usize::try_from(end).unwrap_or(usize::MAX)),
                        act: Act::Writes { tiles, over: 0 },
                        cleared: true,
                    });
                }
                let popped = stack.pop();
                labelled = popped.is_some_and(|frame| {
                    frame.labelled && frame.kind == Kind::Group("]") && spelled == "]"
                });
                if popped.is_some_and(|frame| frame.kind == Kind::Opaque) {
                    opaque = opaque.saturating_sub(1);
                }
            },
            Bracketing::Neither => {},
        }
        member = class.separates && <&str>::from(spelling(text, token)) == ";"
            || class.bracketing == Bracketing::Opens(Kind::Block);
        closed_head = (class.bracketing == Bracketing::Closes
            && stack.is_empty()
            && <&str>::from(spelling(text, token)) == ")")
            .then_some(token.end);
        closed_labelled = labelled.then_some(token.end);
        previous_word = matches!(token.lexeme, Lexeme::LowerWord | Lexeme::UpperWord);
        previous = Some((
            token.end,
            matches!(class.bracketing, Bracketing::Opens(_)),
            class.separates,
            matches!(class.edge, Edge::Ends | Edge::Both),
        ));
        closing = 0;
    }
    if let Some(start) = attribute {
        places.openers.push(opener(start));
    }
    places
}

/// What separates the operand after a head that is no function from the
/// head, in the repair a refusal of their application names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Separation
{
    /// A `,` between two items of a group.
    Item,
    /// The operand's line at its layout block's column, where it starts a
    /// statement.
    Statement,
}

/// The repair a refusal of an application whose head is no function names:
/// the bytes it replaces and the text written in their place.
///
/// # Specification
/// - requires: nothing to construct this data; [`juxtaposed`] makes it over the
///   text it reads.
/// - ensures: the span lies inside that text, and the replacement is a `,` or a
///   slice of that text.
/// - fails: not applicable to the data item.
/// - panics: not applicable to the data item.
///
/// # Adequacy
/// - hypothesis: L3 — as [`juxtaposed`].
/// - witness: `parse::gap::tests::a_head_that_is_no_function_names_what_separates_its_operand_5474`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Juxtaposition<'text>
{
    /// What the repair separates the operand from the head by.
    pub separation: Separation,
    /// The bytes it replaces: none, at the head's end, for a `,`; the
    /// indentation of the operand's line for a statement.
    pub span: ByteSpan,
    /// The text written in their place: a `,`, or the indentation of the
    /// block's first line.
    pub replacement: SourceText<'text>,
}

/// The repair a refusal names when the head at `head` is no function.
///
/// Two operands side by side directly inside a group take the `,` the
/// sibling signal places between them. An operand that begins a line right of
/// its layout block's column continues the statement above it, and it takes
/// that line moved to the block's column, where it starts a statement.
///
/// # Specification
/// - requires: `head` lies in `text`.
/// - ensures: [`Separation::Item`], an empty span at `head`'s end and `,`, when
///   [`gaps`] gives a sibling place at `head`'s end in the top-level form
///   [`form_around`] gives for `head`'s start. Otherwise
///   [`Separation::Statement`] when the first token after `head` begins a line,
///   the layout pass writes no token between them, and the innermost open
///   bracket there is a layout block whose first token begins its own line at a
///   column left of that token's: the span from that line's start to the token,
///   and the indentation of the block's first line. Otherwise `None`.
/// - fails: never.
/// - panics: none.
/// - intension: labels the one top-level form the head stands in.
///
/// # Adequacy
/// - hypothesis: L3 — `7` in `#[7 8]` names a `,` after it; `x` in a `let`
///   whose next line continues it one column right names that line at the
///   block's column; a head whose operand stands on its own line inside no
///   group, and a head in a bracket that its operand's line continues, name
///   nothing.
/// - witness: `parse::gap::tests::a_head_that_is_no_function_names_what_separates_its_operand_5474`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.is_none_or(|found| usize::from(found.span.end()) <= <&str>::from(text).len()
    && (found.separation == Separation::Statement || <&str>::from(found.replacement) == ",")))]
pub fn juxtaposed<'text>(
    text: SourceText<'text>,
    head: ByteSpan,
) -> Option<Juxtaposition<'text>>
{
    let (start, end) = form_around(text, head.start());
    let region =
        SourceText::from(<&'text str>::from(text).get(usize::from(start) .. usize::from(end))?);
    let at = ByteOffset::from(usize::from(head.end()).checked_sub(usize::from(start))?);
    let tokens = label(SourceFragment::from(<&str>::from(region)));
    if gaps(region, &tokens)
        .siblings
        .iter()
        .any(|gap| gap.at == at)
    {
        return Some(Juxtaposition {
            separation: Separation::Item,
            span: ByteSpan::new(head.end(), head.end()).ok()?,
            replacement: SourceText::from(","),
        });
    }
    let (indentation, replacement) = continued(region, &tokens, at)?;
    let shift = |offset: ByteOffset| {
        ByteOffset::from(usize::from(offset).saturating_add(usize::from(start)))
    };
    Some(Juxtaposition {
        separation: Separation::Statement,
        span: ByteSpan::new(shift(indentation.start()), shift(indentation.end())).ok()?,
        replacement,
    })
}

/// Where a layout block's first token stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum First
{
    /// No token follows the block's opener yet.
    Unread,
    /// The first token begins a line: where the line starts, and where the
    /// token does.
    Leads(u32, u32),
    /// The first token follows the opener on its line.
    Inline,
}

/// One open bracket, as [`continued`] reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opened
{
    /// A bracket the source writes.
    Written,
    /// A block the layout pass opens.
    Laid(First),
}

/// The indentation of the line the first token at or after `at` begins, and
/// the indentation of its layout block's first line, when that line
/// continues the statement above it in the block.
///
/// # Specification
/// - requires: `tokens` label `text`.
/// - ensures: as [`juxtaposed`]'s statement, over `text`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`juxtaposed`].
/// - witness: `parse::gap::tests::a_head_that_is_no_function_names_what_separates_its_operand_5474`
fn continued<'text>(
    text: SourceText<'text>,
    tokens: &[Token],
    at: ByteOffset,
) -> Option<(ByteSpan, SourceText<'text>)>
{
    let at = u32::try_from(usize::from(at)).ok()?;
    let mut open: Vec<Opened> = Vec::new();
    let mut line_start = 0_u32;
    let mut broken = false;
    for &token in tokens {
        match token.lexeme {
            Lexeme::Space => {
                if let Some(last) = <&str>::from(spelling(text, token)).rfind('\n') {
                    broken = true;
                    line_start = token
                        .start
                        .saturating_add(u32::try_from(last).unwrap_or(u32::MAX))
                        .saturating_add(1);
                }
                continue;
            },
            Lexeme::LayoutOpen | Lexeme::LayoutSemi | Lexeme::LayoutClose if token.start >= at => {
                return None;
            },
            Lexeme::LayoutOpen => {
                open.push(Opened::Laid(First::Unread));
                continue;
            },
            Lexeme::LayoutSemi => continue,
            Lexeme::LayoutClose => {
                let _closed = open.pop();
                continue;
            },
            Lexeme::LowerWord
            | Lexeme::UpperWord
            | Lexeme::Number
            | Lexeme::TypedNumber
            | Lexeme::Character
            | Lexeme::Quote
            | Lexeme::StringFragment
            | Lexeme::ShellStringFragment
            | Lexeme::EscapeSequence
            | Lexeme::Punct
            | Lexeme::ShellWord
            | Lexeme::EnvAssign
            | Lexeme::SingleQuotedContent
            | Lexeme::VariableName
            | Lexeme::SubshellOpen
            | Lexeme::SubshellClose
            | Lexeme::FileDescriptor
            | Lexeme::ArmBar
            | Lexeme::Unknown => {},
        }
        let leads = core::mem::replace(&mut broken, false);
        if token.start >= at {
            let Some(&Opened::Laid(First::Leads(first_line, first))) = open.last()
            else {
                return None;
            };
            let column = token.start.checked_sub(line_start)?;
            if !leads || column <= first.checked_sub(first_line)? {
                return None;
            }
            let indentation = ByteSpan::new(
                ByteOffset::from(usize::try_from(line_start).ok()?),
                ByteOffset::from(usize::try_from(token.start).ok()?),
            )
            .ok()?;
            let block = <&'text str>::from(text)
                .get(usize::try_from(first_line).ok()? .. usize::try_from(first).ok()?)?;
            return Some((indentation, SourceText::from(block)));
        }
        if let Some(&mut Opened::Laid(ref mut first)) = open.last_mut()
            && *first == First::Unread
        {
            *first = if leads {
                First::Leads(line_start, token.start)
            }
            else {
                First::Inline
            };
        }
        match class(text, token).bracketing {
            Bracketing::Opens(_) => open.push(Opened::Written),
            Bracketing::Closes => {
                let _closed = open.pop();
            },
            Bracketing::Neither => {},
        }
    }
    None
}

/// A copy of a form or of the source with places written in, as [`written`]
/// answers it.
#[derive(Debug)]
struct Written
{
    /// The copy.
    copy: String,
    /// One splice per tile written, in copy order, each beside where its tile
    /// starts in the copy.
    splices: Vec<(Splice, ByteOffset)>,
    /// One move per moved line, in copy order, at the line's start in the
    /// copy.
    moves: Vec<Move>,
}

/// `text` with the tiles of each of `gaps` written in, and their splices,
/// each read back as minted, and the moves of the lines `gaps` moves.
///
/// # Specification
/// - requires: `gaps` stand in source order, a move before a tile at one place.
/// - ensures: the copy and one splice per tile, in copy order, each with an
///   empty postfix grout of the source boundary's sort as its label until
///   [`minted`] reads the copy's molds. A place that replaces a word writes its
///   tile in place of the word's bytes, with no space around it. Each move
///   names where its line starts in the copy.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the concatenation.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gapped`].
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
/// - witness: `parse::gap::tests::a_misspelt_keyword_owes_its_word_5433`
/// - witness: `parse::gap::tests::a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434`
fn written(
    region: SourceText<'_>,
    base: ByteOffset,
    gaps: &[&Gap],
) -> Option<Written>
{
    let text = <&str>::from(region);
    let base = usize::from(base);
    let mut copy = String::with_capacity(text.len().saturating_add(gaps.len().saturating_mul(4)));
    let mut splices = Vec::new();
    let mut moves = Vec::new();
    let mut from = 0_usize;
    for gap in gaps {
        let at = usize::from(gap.at).checked_sub(base)?;
        copy.push_str(text.get(from .. at)?);
        from = at;
        let (tiles, over) = match gap.act {
            Act::Moves { closes } => {
                moves.push(Move {
                    line: u32::try_from(copy.len()).ok()?,
                    closes,
                });
                continue;
            },
            Act::Writes { ref tiles, over } => (tiles, over),
        };
        let after = at.checked_add(over)?;
        let mut word = text.get(at .. after)?;
        for &tile in tiles {
            let spelled = if word.is_empty() {
                cut_in(region, ByteOffset::from(at), SourceText::from(tile))
            }
            else {
                String::from(tile)
            };
            let pad = spelled.find(tile)?;
            let splice = Splice::replacing(
                ByteOffset::from(copy.len()),
                SourceText::from(spelled.as_str()),
                SourceText::from(word),
            )?;
            splices.push((splice, ByteOffset::from(copy.len().checked_add(pad)?)));
            copy.push_str(&spelled);
            word = "";
        }
        from = after;
    }
    copy.push_str(text.get(from ..)?);
    Some(Written {
        copy,
        splices,
        moves,
    })
}

/// The keyword a misspelt `word` stands for: the keyword nearest it, when
/// fewer than half the keyword's characters are edited.
///
/// A keyword that heads a declaration is the head search's to mint (#2440,
/// #5199), which reads the misspelt word as a stray word the lowering marks.
/// Read as a repair over the word, it leaves the lowering to refuse an
/// attributed member at its name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first keyword or statement lead, none of whose molds under
///   `pbg` heads a declaration, at the least nonzero [`edit_distance`] from
///   `word`, when twice that distance is less than the keyword's length in
///   characters; `None` otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a keyword with one character left out stands for it, a
///   declaration keyword stands for none, and a word no keyword stands near
///   stands for none.
/// - witness: `parse::gap::tests::a_misspelt_keyword_owes_its_word_5433`
fn misspelt(
    pbg: &Pbg,
    word: SourceText<'_>,
) -> Option<TileLabel>
{
    let word = <&str>::from(word);
    let length = word.chars().count();
    RESERVED_WORDS
        .iter()
        .chain(STATEMENT_LEADS)
        .filter_map(|&keyword| {
            let size = keyword.chars().count();
            // The distance is at least the difference in length, so a keyword
            // that far from the word in length is never measured.
            (length.abs_diff(size).saturating_mul(2) < size).then(|| {
                (
                    edit_distance(LabelText(word), LabelText(keyword)).0,
                    size,
                    keyword,
                )
            })
        })
        .filter_map(|(edits, size, keyword)| {
            (edits > 0 && edits.saturating_mul(2) < size).then_some((edits, keyword))
        })
        .filter(|&(_, keyword)| {
            !pbg.candidates(TileLabel(keyword))
                .iter()
                .any(|&mold| bool::from(declaration_head(pbg, mold)))
        })
        .min_by_key(|&(edits, _)| edits)
        .map(|(_, keyword)| TileLabel(keyword))
}

/// The places of one top-level form the search keeps, and what the form owes
/// with them written in.
#[derive(Clone, Debug)]
struct Form<'gap>
{
    /// What the form alone owes with the kept places written in, each minted
    /// tile counting as one.
    best: usize,
    /// The places kept, in source order.
    kept: Vec<&'gap Gap>,
}

/// `parsed`, with each place a signal gives minted where the copy that writes
/// it owes fewer obligations, if one does, and, where `inside` is given, if a
/// place kept before a line stands inside it and the parse owes nothing but
/// its minted tiles.
///
/// # Specification
/// - requires: `parsed` is a parse under `pbg`.
/// - ensures: `None` when `parsed` owes nothing, no place the search tries is
///   kept, `inside` is given and no place kept before a line stands inside it,
///   ends included, `inside` is given and the parse owes an obligation besides
///   one for each minted tile and each moved line, or the copy with every kept
///   place written in owes no fewer obligations; otherwise the parse of that
///   copy, with each kept line moved, read back over the source with each
///   written tile minted at its place, its obligations those of the copy,
///   shifted back over the tiles, one [`Oblig::MissingTile`] at each minted
///   tile's place and at the start of each moved line, and one
///   [`Oblig::IncompleteTile`] over each misspelt word. The scan reads only the
///   top-level forms, [`form_around`], that hold an obligation. The search
///   tries their places before each line in source order, each move of a line
///   innermost block first, then their sibling, arrow and attribute opener
///   places and the keywords [`misspelt`] gives for the [`COPIES`] words
///   nearest an obligation, nearest first, [`COPIES`] places in all. Each place
///   is judged in a copy of its form with the places kept there before it, a
///   move in place of a move of its own line. A place is kept when that copy
///   owes fewer obligations than the form alone, each minted tile and each
///   moved line counting as one. A closer, a sibling separator, an arrow, an
///   attribute opener, a keyword or a move is kept only when the copy owes
///   nothing but its minted tiles and its moved lines.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a field left without its type before the next field owes
///   one `,` on its own line and nothing after it; a field whose `(` the line
///   leaves open owes the `)` and the `,` there; a `(` that a line of a block
///   leaves open owes its `)` before the block's `}` alone, and a block left
///   open before the `)` of the group around it owes its `}` there alone; two
///   arguments side by side owe the `,` between them; a type beside a returner
///   owes the `->` between them; an attribute without its `@[` owes the `@[`
///   alone; a misspelt `matc` owes its word alone; a `)` deleted inside a line
///   with a repair after it is not minted at the line's end; a line at column
///   zero inside nested blocks owes only its own line; a source that owes
///   nothing, and one whose places all owe more, keep their parse.
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
/// - witness: `parse::gap::tests::a_separator_left_out_between_siblings_is_minted_5433`
/// - witness: `parse::gap::tests::an_arrow_left_out_before_a_returner_is_minted_5501`
/// - witness: `parse::gap::tests::an_attribute_opener_left_out_is_minted_4398`
/// - witness: `parse::gap::tests::a_misspelt_keyword_owes_its_word_5433`
/// - witness: `parse::gap::tests::a_closer_deleted_inside_a_line_is_not_minted_at_its_end_5433`
/// - witness: `parse::gap::tests::a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434`
/// - witness: `parse::gap::tests::a_source_that_owes_nothing_keeps_its_parse_5433`
/// - witness: `parse::gap::tests::a_bracket_left_open_before_a_closer_of_another_family_is_closed_there_6103`
pub(super) fn gapped<'source>(
    pbg: &Pbg,
    parsed: &ParseResult<'source>,
    inside: Option<ByteSpan>,
) -> Option<ParseResult<'source>>
{
    if parsed.obligations.is_empty() {
        return None;
    }
    let source = parsed.tree.source();
    let text = <&str>::from(source);
    // Only a form that owes can owe less, so the scan labels those forms
    // alone, each from its own line at column zero.
    let mut owing: Vec<(ByteOffset, ByteOffset)> = parsed
        .obligations
        .iter()
        .map(|obligation| form_around(source, obligation.span.start()))
        .collect();
    owing.sort_unstable();
    owing.dedup();
    let mut lines = Vec::new();
    let mut near = Vec::new();
    let mut words = Vec::new();
    for &(start, end) in &owing {
        let Some(region) = text.get(usize::from(start) .. usize::from(end))
        else {
            continue;
        };
        let shift =
            |at: ByteOffset| ByteOffset::from(usize::from(at).saturating_add(usize::from(start)));
        let found = gaps(
            SourceText::from(region),
            &label(SourceFragment::from(region)),
        );
        lines.extend(found.lines.into_iter().map(|gap| Gap {
            at: shift(gap.at),
            ..gap
        }));
        near.extend(found.siblings.into_iter().map(|gap| Gap {
            at: shift(gap.at),
            ..gap
        }));
        near.extend(found.arrows.into_iter().map(|gap| Gap {
            at: shift(gap.at),
            ..gap
        }));
        near.extend(found.openers.into_iter().map(|gap| Gap {
            at: shift(gap.at),
            ..gap
        }));
        words.extend(found.words.into_iter().map(|(at, word)| (shift(at), word)));
    }
    // An omission shows as a repair at or after its place, so a repair
    // before a place counts at twice its distance.
    let distance = |at: ByteOffset| {
        let at = usize::from(at);
        parsed
            .obligations
            .iter()
            .map(|obligation| {
                let start = usize::from(obligation.span.start());
                start
                    .checked_sub(at)
                    .unwrap_or_else(|| at.saturating_sub(start).saturating_mul(2))
            })
            .min()
            .unwrap_or(usize::MAX)
    };
    words.sort_by_key(|&(at, _)| distance(at));
    near.extend(words.iter().take(COPIES).filter_map(|&(at, word)| {
        misspelt(pbg, word).map(|keyword| Gap {
            at,
            act: Act::Writes {
                tiles: alloc::vec![keyword.0],
                over: <&str>::from(word).len(),
            },
            cleared: true,
        })
    }));
    near.sort_by_key(|gap| distance(gap.at));
    // Each form a place stands in, by where the form starts.
    let mut forms: BTreeMap<ByteOffset, Form<'_>> = BTreeMap::new();
    for place in lines.iter().chain(&near).take(COPIES) {
        let (start, end) = form_around(source, place.at);
        let Some(region) = text
            .get(usize::from(start) .. usize::from(end))
            .map(SourceText::from)
        else {
            continue;
        };
        let form = forms.entry(start).or_insert_with(|| Form {
            best: molded(pbg, region).owed().len(),
            kept: Vec::new(),
        });
        let mut trial = form.kept.clone();
        // A move competes with a move of its own line kept before it.
        if let Act::Moves { .. } = place.act {
            trial.retain(|kept| kept.at != place.at || matches!(kept.act, Act::Writes { .. }));
        }
        trial.push(place);
        trial.sort_by_key(|gap| (gap.at, matches!(gap.act, Act::Writes { .. })));
        let Some(copy) = written(region, start, &trial)
        else {
            continue;
        };
        let own = molded_moving(pbg, SourceText::from(copy.copy.as_str()), &copy.moves)
            .owed()
            .len();
        let owed = own
            .saturating_add(copy.splices.len())
            .saturating_add(copy.moves.len());
        if owed < form.best && (own == 0 || !place.cleared) {
            form.best = owed;
            form.kept = trial;
        }
    }
    let mut kept: Vec<&Gap> = forms.into_values().flat_map(|form| form.kept).collect();
    if kept.is_empty() {
        return None;
    }
    // A search held to a form keeps its places only where a line inside the
    // form shows one of them, and only where its parse owes nothing but the
    // tiles it mints: the condition the search puts on a closer, a separator,
    // a keyword and a move.
    let shown = |inside: ByteSpan| {
        kept.iter().any(|&gap| {
            inside.start() <= gap.at
                && gap.at <= inside.end()
                && lines
                    .iter()
                    .any(|line| core::ptr::eq(core::ptr::from_ref(line), core::ptr::from_ref(gap)))
        })
    };
    if inside.is_some_and(|inside| !shown(inside)) {
        return None;
    }
    kept.sort_by_key(|gap| (gap.at, matches!(gap.act, Act::Writes { .. })));
    let tiles: usize = kept
        .iter()
        .map(|gap| match gap.act {
            Act::Writes { ref tiles, over: 0 } => tiles.len(),
            Act::Writes { .. } | Act::Moves { .. } => 1,
        })
        .sum();
    minted(pbg, source, &kept).filter(|repaired| {
        repaired.obligations.len() < parsed.obligations.len()
            && (inside.is_none() || repaired.obligations.len() == tiles)
    })
}

/// The top-level form `at` stands in: from the start of the last line at or
/// before `at` that begins a form to the start of the next such line. A line
/// begins a form when its first byte is a lower-case letter, `_`, `@` or `/`:
/// the start of a declaration's keyword, of an attribute or of a comment
/// before a declaration. The labeler resets only at a word or an attribute
/// at column zero, so a line that a closer, a `|` or an upper-case word
/// begins continues the form before it. An arm typed before it is indented
/// thus stays in its declaration's form, where a move can keep it in its
/// block.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `(start, end)` with `start <= at <= end`, each the start of a
///   line whose first byte is a lower-case ASCII letter, `_`, `@` or `/`, the
///   start of `text` or its end.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gapped`]: a record type whose `}` stands at column
///   zero is one form with the field the line leaves open, and an arm at column
///   zero is one form with its declaration.
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
/// - witness: `parse::gap::tests::a_closer_deleted_inside_a_line_is_not_minted_at_its_end_5433`
/// - witness: `parse::gap::tests::a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434`
fn form_around(
    text: SourceText<'_>,
    at: ByteOffset,
) -> (ByteOffset, ByteOffset)
{
    let text = <&str>::from(text);
    let leads = |line: usize| {
        text.as_bytes()
            .get(line)
            .is_some_and(|&byte| matches!(byte, b'a' ..= b'z' | b'_' | b'@' | b'/'))
    };
    let line_of = |offset: usize| {
        text.get(.. offset)
            .and_then(|before| before.rfind('\n'))
            .map_or(0, |newline| newline.saturating_add(1))
    };
    let mut start = line_of(usize::from(at));
    while start > 0 && !leads(start) {
        start = line_of(start.saturating_sub(1));
    }
    let mut end = usize::from(at);
    while let Some(newline) = text.get(end ..).and_then(|after| after.find('\n')) {
        end = end.saturating_add(newline).saturating_add(1);
        if leads(end) {
            return (ByteOffset::from(start), ByteOffset::from(end));
        }
    }
    (ByteOffset::from(start), ByteOffset::from(text.len()))
}

/// The parse of `source` with the tiles of `kept` written in and read back as
/// minted, and with each line `kept` moves kept in its block: a closer as a
/// minted close, a `,` as an empty postfix grout, a `->` as an empty infix
/// grout between the two operands it joins, a `@[` as an empty prefix grout
/// before the attribute's words, and a keyword written over a misspelt word
/// as a prefix grout over the word.
///
/// # Specification
/// - requires: `kept` stand in source order, a move before a tile at one place.
/// - ensures: as [`gapped`] for its kept places; `None` when a written tile
///   reads as no tile of the copy, when documentation holds a written tile
///   ([`undocumented`]), or when the commit fails.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the commit.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gapped`].
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
/// - witness: `parse::gap::tests::an_arrow_left_out_before_a_returner_is_minted_5501`
/// - witness: `parse::gap::tests::an_attribute_opener_left_out_is_minted_4398`
/// - witness: `parse::gap::tests::a_misspelt_keyword_owes_its_word_5433`
/// - witness: `parse::gap::tests::a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434`
fn minted<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
    kept: &[&Gap],
) -> Option<ParseResult<'source>>
{
    let Written {
        copy,
        splices: written,
        moves,
    } = written(source, ByteOffset::from(0_usize), kept)?;
    let text = SourceText::from(copy.as_str());
    let state = molded_moving(pbg, text, &moves);
    let mut splices = Vec::with_capacity(written.len());
    for &(splice, at) in &written {
        let tile = <&str>::from(splice.tile(text)?).trim_matches(' ');
        let end = ByteOffset::from(usize::from(at).checked_add(tile.len())?);
        let mold = state.tile_spanning(ByteSpan::new(at, end).ok()?)?;
        let sort = pbg.mold(mold).ok()?.sort.grout_sort();
        let ghost = match splice.stands() {
            Stands::Misspelt => NodeLabel::Grout {
                sort,
                shape: GroutShape::Prefix,
            },
            Stands::LeftOut => ClosingClass::closing(DelimSpelling::from(tile)).map_or(
                NodeLabel::Grout {
                    sort,
                    shape: match tile {
                        "->" => GroutShape::Infix,
                        "@[" => GroutShape::Prefix,
                        _ => GroutShape::Postfix,
                    },
                },
                |class| NodeLabel::GhostClose {
                    sort,
                    class,
                    reach: CloseReach::from(0_u32),
                },
            ),
        };
        splices.push(splice.read_as(ghost));
    }
    let mut owed = Vec::with_capacity(kept.len());
    for gap in kept {
        match gap.act {
            Act::Writes { ref tiles, over: 0 } => {
                let place = ByteSpan::new(gap.at, gap.at).ok()?;
                for _tile in tiles {
                    owed.push(ObligationInstance::new(Oblig::MissingTile, place));
                }
            },
            Act::Writes { over, .. } => {
                let word = ByteSpan::new(
                    gap.at,
                    ByteOffset::from(usize::from(gap.at).checked_add(over)?),
                )
                .ok()?;
                owed.push(ObligationInstance::new(Oblig::IncompleteTile, word));
            },
            Act::Moves { .. } => {
                let line = ByteSpan::new(gap.at, gap.at).ok()?;
                owed.push(ObligationInstance::new(Oblig::MissingTile, line));
            },
        }
    }
    undocumented(spliced(state, source, &splices, owed)?, kept)
}

/// `parsed` when no documentation in it holds a tile that `kept` writes in.
/// The melder reads an attribute block of `doc` entries as documentation,
/// with a `@[` written in before the entries too. The lowering reads no
/// repair in documentation, so it refuses no such tile, and the source
/// checks clean.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `None` exactly when a [`NodeLabel::Grout`] or a
///   [`NodeLabel::GhostClose`] node that starts at the place of one of `kept`
///   stands inside a [`NodeLabel::Doc`] node of `parsed`'s tree; otherwise
///   `parsed` as it is.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk.
///
/// # Adequacy
/// - hypothesis: L3 — a `doc` entry left without its `@[` in a module, on the
///   member's line and on its own line, holds no minted `@[` in documentation.
/// - witness: `parse::gap::tests::an_attribute_opener_left_out_is_minted_4398`
fn undocumented<'source>(
    parsed: ParseResult<'source>,
    kept: &[&Gap],
) -> Option<ParseResult<'source>>
{
    let tree = &parsed.tree;
    let mut pending: Vec<(NodeIndex, bool)> =
        tree.roots().iter().map(|&root| (root, false)).collect();
    // The starts of the repairs that documentation holds. Most parses hold
    // none, and an empty vector allocates nothing.
    let mut held: Vec<ByteOffset> = Vec::new();
    while let Some((next, documented)) = pending.pop() {
        let Some(node) = tree.node(next)
        else {
            continue;
        };
        let label = node.label();
        let documented = documented || label == NodeLabel::Doc;
        if documented
            && matches!(
                label,
                NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. }
            )
        {
            held.push(node.span().start());
        }
        pending.extend(tree.children(next).map(|child| (child, documented)));
    }
    held.sort_unstable();
    kept.iter()
        .all(|gap| held.binary_search(&gap.at).is_err())
        .then_some(parsed)
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::string::String;
    use core::error::Error;

    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;

    use super::Separation;
    use super::juxtaposed;
    use crate::oblig::Oblig;
    use crate::parse;

    /// A line of a source, counted from one.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Line(usize);

    /// What the record type of `corpus/model/desc/lc/model-record.gandr`
    /// owes, cut down, with the line after its `empty` field replaced by
    /// `typed`.
    ///
    /// # Specification
    /// trivial.
    fn record_owes(typed: SourceText<'_>)
    -> Result<alloc::vec::Vec<(Oblig, Line)>, Box<dyn Error>>
    {
        let typed = <&str>::from(typed);
        let source = alloc::format!(
            include_str!("gap/unformatted/record-owes.gandr"),
            typed = typed
        );
        owed(SourceText::from(source.as_str()))
    }

    /// Where each obligation of `source`'s parse stands: its class and the
    /// line it starts on.
    ///
    /// # Specification
    /// trivial.
    fn owed(source: SourceText<'_>) -> Result<alloc::vec::Vec<(Oblig, Line)>, Box<dyn Error>>
    {
        let pbg = built_in()?;
        let parsed = parse(&pbg, source)?;
        let source = <&str>::from(source);
        assert_eq!(
            crate::testing::reconstruct(&parsed.tree),
            source,
            "the tree spells the source"
        );
        Ok(parsed
            .obligations()
            .iter()
            .map(|obligation| {
                let start = usize::from(obligation.span.start());
                (
                    obligation.class,
                    Line(
                        source
                            .get(.. start)
                            .map_or(0, |before| before.matches('\n').count().saturating_add(1)),
                    ),
                )
            })
            .collect())
    }

    #[test]
    fn a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433()
    -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            record_owes(SourceText::from("  subTm :"))?,
            [(Oblig::MissingTile, Line(4))],
            "a field left without its type owes the `,` on its own line alone"
        );
        assert_eq!(
            record_owes(SourceText::from("  subTm : (g : con, tm(g)"))?,
            [(Oblig::MissingTile, Line(4)), (Oblig::MissingTile, Line(4))],
            "a field whose `(` its line leaves open owes the `)` and the `,` on its own line"
        );
        Ok(())
    }

    #[test]
    fn a_separator_left_out_between_siblings_is_minted_5433() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        for (source, after) in [
            (
                "def swap(m : Integer n : Integer) -> Integer = m;\n",
                "m : Integer",
            ),
            (
                "def divmod(m : Integer) -> (q : Integer r : Integer) { m }\n",
                "q : Integer",
            ),
        ] {
            let parsed = parse(&pbg, SourceText::from(source))?;
            let at = source
                .find(after)
                .map(|start| start.saturating_add(after.len()));
            assert_eq!(
                parsed
                    .obligations()
                    .iter()
                    .map(|obligation| (
                        obligation.class,
                        usize::from(obligation.span.start()),
                        usize::from(obligation.span.end())
                    ))
                    .collect::<alloc::vec::Vec<_>>(),
                at.map(|at| (Oblig::MissingTile, at, at))
                    .into_iter()
                    .collect::<alloc::vec::Vec<_>>(),
                "two parameters side by side owe the `,` between them alone: {source}"
            );
        }
        Ok(())
    }

    #[test]
    fn an_arrow_left_out_before_a_returner_is_minted_5501() -> Result<(), Box<dyn Error>>
    {
        // Row 19 of `fragment/shape-refusal.gandr`'s recovery record: the
        // signature with its `->` dropped.
        let source = "def returned : +U (Integer  -F Integer);\n";
        let at = source
            .find("(Integer")
            .map_or_default(|start| start.saturating_add("(Integer".len()));
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        let tree = parsed.tree();
        assert_eq!(
            crate::testing::reconstruct(tree),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::MissingTile, at, at)],
            "a type beside a returner owes the `->` between them alone"
        );
        assert!(
            tree.positions()
                .filter_map(|position| tree.node(position))
                .any(|node| {
                    matches!(node.label(), gandr_surface_syntax::NodeLabel::Grout {
                        shape: gandr_surface_syntax::GroutShape::Infix,
                        ..
                    }) && usize::from(node.span().start()) == at
                        && usize::from(node.span().end()) == at
                }),
            "the `->` stands as a repair between its two operands"
        );
        Ok(())
    }

    #[test]
    fn an_arrow_left_out_after_a_parameter_list_is_minted_6323() -> Result<(), Box<dyn Error>>
    {
        // Row 217 of `model/sessions/type-quote.gandr`'s recovery record: a
        // declaration's head with the `->` before its result type dropped,
        // after a doc comment, so that `def` begins no line of the scan.
        let source = include_str!(
            "gap/unformatted/an-arrow-left-out-after-a-parameter-list-is-minted-6323.gandr"
        );
        let at = source
            .find("end))")
            .map_or_default(|start| start.saturating_add("end))".len()));
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        let tree = parsed.tree();
        assert_eq!(
            crate::testing::reconstruct(tree),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::MissingTile, at, at)],
            "a result type after the parameter list owes the `->` between them alone"
        );
        Ok(())
    }

    #[test]
    fn an_equals_left_out_before_a_record_body_is_minted_6364() -> Result<(), Box<dyn Error>>
    {
        // Row 410 of `model/modules/model-manifest-type.gandr`'s recovery
        // record: the `=` between a head's sort equation and its record body
        // dropped. The `=` of `with sort C = …` stays inside the type.
        let source = include_str!(
            "gap/unformatted/an-equals-left-out-before-a-record-body-is-minted-6364.gandr"
        );
        let at = source.find("  *{").unwrap_or_default();
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        assert_eq!(
            crate::testing::reconstruct(parsed.tree()),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::MissingTile, at, at)],
            "a record body after the head's type owes the `=` between them alone"
        );
        Ok(())
    }

    #[test]
    fn a_bracket_left_open_before_a_call_of_its_type_is_closed_there_6364()
    -> Result<(), Box<dyn Error>>
    {
        // Row 199 of `model/identity/atom-identity.gandr`'s recovery record:
        // the `]` of `Path[.A = Point.T](Point.origin, y)` dropped, so that
        // the endpoints read as an application of the type.
        let source = include_str!(
            "gap/unformatted/a-bracket-left-open-before-a-call-of-its-type-is-closed-there-6364.gandr"
        );
        let at = source
            .find("Point.T(")
            .map_or_default(|start| start.saturating_add("Point.T".len()));
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        assert_eq!(
            crate::testing::reconstruct(parsed.tree()),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::MissingTile, at, at)],
            "the endpoints after a labelled type owe the `]` before them alone"
        );
        Ok(())
    }

    #[test]
    fn an_opener_left_out_after_a_labelled_bracket_is_minted_6364() -> Result<(), Box<dyn Error>>
    {
        // Row 200 of `model/identity/atom-identity.gandr`'s recovery record:
        // the `(` after `Path[.A = Point.T]` dropped, so that the first
        // endpoint reads as an argument of the type.
        let source = include_str!(
            "gap/unformatted/an-opener-left-out-after-a-labelled-bracket-is-minted-6364.gandr"
        );
        let at = source
            .find("Point.T]")
            .map_or_default(|start| start.saturating_add("Point.T]".len()));
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        assert_eq!(
            crate::testing::reconstruct(parsed.tree()),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::MissingTile, at, at)],
            "the endpoints written against a labelled bracket owe the `(` before them alone"
        );
        Ok(())
    }

    #[test]
    fn a_misspelt_keyword_owes_its_word_5433() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        assert_eq!(
            super::misspelt(&pbg, SourceText::from("matc")).map(|keyword| keyword.0),
            Some("match"),
            "one character left out"
        );
        assert_eq!(
            super::misspelt(&pbg, SourceText::from("wher")).map(|keyword| keyword.0),
            Some("where"),
            "one character left out"
        );
        assert_eq!(
            super::misspelt(&pbg, SourceText::from("xs")).map(|keyword| keyword.0),
            None,
            "no keyword stands near a short name"
        );
        assert_eq!(
            super::misspelt(&pbg, SourceText::from("de")).map(|keyword| keyword.0),
            None,
            "a declaration keyword is the head search's"
        );
        let source = include_str!("gap/unformatted/a-misspelt-keyword-owes-its-word-5433.gandr");
        let start = source.find("matc").unwrap_or_default();
        let parsed = parse(&pbg, SourceText::from(source))?;
        let tree = parsed.tree();
        assert_eq!(
            crate::testing::reconstruct(tree),
            source,
            "the tree spells the source"
        );
        assert_eq!(
            parsed
                .obligations()
                .iter()
                .map(|obligation| (
                    obligation.class,
                    usize::from(obligation.span.start()),
                    usize::from(obligation.span.end())
                ))
                .collect::<alloc::vec::Vec<_>>(),
            [(Oblig::IncompleteTile, start, start.saturating_add(4))],
            "the misspelt `matc` owes its word alone"
        );
        assert!(
            tree.positions()
                .filter_map(|position| tree.node(position))
                .any(|node| {
                    matches!(node.label(), gandr_surface_syntax::NodeLabel::Grout {
                        shape: gandr_surface_syntax::GroutShape::Prefix,
                        ..
                    }) && usize::from(node.span().start()) == start
                        && usize::from(node.span().end()) == start.saturating_add(4)
                }),
            "the word stands as a repair the lowering refuses"
        );
        Ok(())
    }

    #[test]
    fn a_source_that_owes_nothing_keeps_its_parse_5433() -> Result<(), Box<dyn Error>>
    {
        assert_eq!(
            record_owes(SourceText::from("  subTm : (g : con) -> con,"))?,
            [],
            "a whole record owes nothing"
        );
        assert_eq!(
            owed(SourceText::from(include_str!(
                "gap/fixtures/a-source-that-owes-nothing-keeps-its-parse-5433.gandr"
            )))?,
            [],
            "an application across a line at its items' column owes nothing, so no place is tried"
        );
        Ok(())
    }

    #[test]
    fn a_closer_deleted_inside_a_line_is_not_minted_at_its_end_5433() -> Result<(), Box<dyn Error>>
    {
        let source = include_str!(
            "gap/unformatted/a-closer-deleted-inside-a-line-is-not-minted-at-its-end-5433.gandr"
        );
        let end = source.find("]\n").map(|at| at.saturating_add(1));
        let pbg = built_in()?;
        let parsed = parse(&pbg, SourceText::from(source))?;
        assert!(
            parsed.obligations().iter().all(|obligation| {
                Some(usize::from(obligation.span.start())) != end
                    || obligation.span.start() != obligation.span.end()
            }),
            "the `)` the line leaves open is not minted at its end, where the copy owes more: {:?}",
            parsed.obligations()
        );
        Ok(())
    }

    #[test]
    fn a_bracket_left_open_before_a_closer_of_another_family_is_closed_there_6103()
    -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        for (source, before, left) in [
            (
                include_str!(
                    "gap/unformatted/a-group-left-open-before-a-closer-of-another-family-is-closed-there-6103.gandr"
                ),
                ")\n    })",
                "the `(` of `(Done` that the `}` meets open owes its `)` before the `}` alone",
            ),
            (
                include_str!(
                    "gap/unformatted/a-block-left-open-before-a-closer-of-another-family-is-closed-there-6103.gandr"
                ),
                ")\n    ) :",
                "the `{` of the inner `fun` that the `)` meets open owes its `}` before the `)` alone",
            ),
        ] {
            let place = source
                .find(before)
                .map(|at| ByteOffset::from(at.saturating_add(1)))
                .map(|at| ByteSpan::new(at, at))
                .transpose()?;
            let parsed = parse(&pbg, SourceText::from(source))?;
            assert_eq!(
                parsed
                    .obligations()
                    .iter()
                    .map(|obligation| (obligation.class, Some(obligation.span)))
                    .collect::<alloc::vec::Vec<_>>(),
                [(Oblig::MissingTile, place)],
                "{left}"
            );
        }
        Ok(())
    }

    #[test]
    fn a_line_at_column_zero_inside_nested_blocks_stays_in_a_block_5434()
    -> Result<(), Box<dyn Error>>
    {
        // `pick` of `corpus/model/specification/niche-realizability.gandr`,
        // its arms in two nested arm blocks.
        let lines = [
            "def rec pick(a : Nat, b : Nat, yes : Maybe(Nat), no : Maybe(Nat)) -> Maybe(Nat) =",
            "  match a where",
            "    | Zero => match b where",
            "      | Zero => yes",
            "      | Succ(_q) => no",
            "    | Succ(p) => match b where",
            "      | Zero => no",
            "      | Succ(q) => pick[<] p q yes no",
            "",
            "def next = 1;",
        ];
        assert_eq!(
            owed(SourceText::from(lines.join("\n").as_str()))?,
            [],
            "the arms at their columns owe nothing"
        );
        // Each arm typed at column zero: the first and last arms of each inner
        // block, and both arms of the outer block.
        for at in [2_usize, 3, 4, 5, 6, 7] {
            let typed: alloc::vec::Vec<&str> = lines
                .iter()
                .enumerate()
                .map(|(line, &text)| if line == at { text.trim_start() } else { text })
                .collect();
            assert_eq!(
                owed(SourceText::from(typed.join("\n").as_str()))?,
                [(Oblig::MissingTile, Line(at.saturating_add(1)))],
                "the arm on line {} at column zero owes one repair, on its own line",
                at.saturating_add(1)
            );
        }
        // A word at column zero begins a declaration. The body closes before
        // it and owes its statement, so the line owes two repairs. A move
        // would keep the line in the body with one repair, but no move keeps
        // a word at column zero.
        let body = [
            "def g(a : Nat) -> Nat =",
            "  let b = a;",
            "  b",
            "",
            "def next = 1;",
        ];
        assert_eq!(owed(SourceText::from(body.join("\n").as_str()))?, []);
        let reset = [
            "def g(a : Nat) -> Nat =",
            "let b = a;",
            "  b",
            "",
            "def next = 1;",
        ];
        assert_eq!(
            owed(SourceText::from(reset.join("\n").as_str()))?,
            [(Oblig::MissingTile, Line(2)), (Oblig::MissingTile, Line(2))],
            "a word at column zero stays a declaration's first line"
        );
        Ok(())
    }

    #[test]
    fn a_head_that_is_no_function_names_what_separates_its_operand_5474()
    -> Result<(), Box<dyn Error>>
    {
        // The head is the first byte of the first place `context` is written.
        let repaired =
            |source: &str, context: &str| -> Result<Option<(Separation, String)>, Box<dyn Error>> {
                let start = source.find(context).ok_or("the head is written")?;
                let head = ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(1)),
                )?;
                Ok(juxtaposed(SourceText::from(source), head).map(|found| {
                    let mut copy = String::from(source);
                    copy.replace_range(
                        usize::from(found.span.start()) .. usize::from(found.span.end()),
                        <&str>::from(found.replacement),
                    );
                    (found.separation, copy)
                }))
            };
        assert_eq!(
            repaired(
                include_str!(
                    "gap/unformatted/a-head-that-is-no-function-names-what-separates-its-operand-5474-1.gandr"
                ),
                "7 8"
            )?,
            Some((
                Separation::Item,
                String::from("def two() -> Integer =\n  shortLength (#[7, 8])\n")
            )),
            "two items side by side in a list take the `,` between them"
        );
        assert_eq!(
            repaired(
                include_str!(
                    "gap/unformatted/a-head-that-is-no-function-names-what-separates-its-operand-5474-2.gandr"
                ),
                "x\n"
            )?,
            Some((
                Separation::Statement,
                String::from(
                    "def g(x : Integer, y : Integer) -> Integer =\n  let a = x\n  y\n  a\n"
                )
            )),
            "a line that continues a statement one column right moves to its block's column"
        );
        assert_eq!(
            repaired(
                include_str!(
                    "gap/unformatted/a-head-that-is-no-function-names-what-separates-its-operand-5474-3.gandr"
                ),
                "x y"
            )?,
            None,
            "an operand on its head's line inside no group names nothing"
        );
        assert_eq!(
            repaired(
                include_str!(
                    "gap/unformatted/a-head-that-is-no-function-names-what-separates-its-operand-5474-4.gandr"
                ),
                "x\n"
            )?,
            None,
            "an operand whose line a bracket continues names nothing"
        );
        Ok(())
    }

    #[test]
    fn a_semicolon_after_a_missing_left_operand_ends_the_member_5502() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        for source in [
            include_str!(
                "gap/unformatted/a-semicolon-after-a-missing-left-operand-ends-the-member-5502-1.gandr"
            ),
            include_str!(
                "gap/unformatted/a-semicolon-after-a-missing-left-operand-ends-the-member-5502-2.gandr"
            ),
        ] {
            let operator = source.find("+ 1").ok_or("the operator is written")?;
            let parsed = parse(&pbg, SourceText::from(source))?;
            let owed: alloc::vec::Vec<(Oblig, usize, usize)> = parsed
                .obligations()
                .iter()
                .map(|obligation| {
                    (
                        obligation.class,
                        usize::from(obligation.span.start()),
                        usize::from(obligation.span.end()),
                    )
                })
                .collect();
            assert_eq!(
                owed,
                [(Oblig::MissingMeld, operator, operator)],
                "{source}: the `;` ends `first`, so the parse owes only the left operand of `+`"
            );
        }
        Ok(())
    }

    #[test]
    fn an_attribute_opener_left_out_is_minted_4398() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        // Row 4 of `pathological/module-duplicate-member.gandr`'s recovery
        // record, an attribute on its own line, and row 4 of
        // `pathological/module-linker-no-run-target.gandr`'s, an attribute
        // after a block's `{` on the block's line.
        for (source, word) in [
            (
                include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-1.gandr"),
                "refuses",
            ),
            ("module Only where {  runs(\"1\") ] def x = 1; }\n", "runs"),
        ] {
            let at = source.find(word).ok_or("the attribute's word is written")?;
            let parsed = parse(&pbg, SourceText::from(source))?;
            let tree = parsed.tree();
            assert_eq!(
                crate::testing::reconstruct(tree),
                source,
                "{source}: the tree spells the source"
            );
            assert_eq!(
                parsed
                    .obligations()
                    .iter()
                    .map(|obligation| (
                        obligation.class,
                        usize::from(obligation.span.start()),
                        usize::from(obligation.span.end())
                    ))
                    .collect::<alloc::vec::Vec<_>>(),
                [(Oblig::MissingTile, at, at)],
                "{source}: the attribute owes its `@[` alone"
            );
            assert!(
                tree.positions()
                    .filter_map(|position| tree.node(position))
                    .any(|node| {
                        matches!(node.label(), gandr_surface_syntax::NodeLabel::Grout {
                            shape: gandr_surface_syntax::GroutShape::Prefix,
                            ..
                        }) && usize::from(node.span().start()) == at
                            && usize::from(node.span().end()) == at
                    }),
                "{source}: the `@[` stands as a repair before the attribute's words"
            );
        }
        // `corpus/ledger/syntax/block.gandr` with an index's `.#[` left out
        // and with its `]` written twice. Each stray `]` comes before an
        // operator, so it closes an expression and no attribute.
        for source in [
            include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-2.gandr"),
            include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-3.gandr"),
            include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-4.gandr"),
        ] {
            assert_eq!(
                super::gaps(
                    SourceText::from(source),
                    &crate::label::label(gandr_surface_syntax::SourceFragment::from(source))
                )
                .openers,
                [],
                "{source}: a `]` that closes its `@[` or comes before an operator gives no place"
            );
        }
        // `corpus/ledger/syntax/attributed-module-member.gandr` with its `@[`
        // left out, the entry on the member's line and on its own line. The
        // melder reads a block of `doc` entries as documentation, where the
        // lowering refuses no repair, so every repair stands outside it.
        for source in [
            include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-5.gandr"),
            include_str!("gap/unformatted/an-attribute-opener-left-out-is-minted-4398-6.gandr"),
        ] {
            let parsed = parse(&pbg, SourceText::from(source))?;
            let tree = parsed.tree();
            let mut pending: alloc::vec::Vec<(gandr_surface_syntax::NodeIndex, bool)> =
                tree.roots().iter().map(|&root| (root, false)).collect();
            while let Some((next, documented)) = pending.pop() {
                let node = tree.node(next).ok_or("a root or a child is a node")?;
                let documented = documented || node.label() == gandr_surface_syntax::NodeLabel::Doc;
                assert!(
                    !(documented
                        && matches!(
                            node.label(),
                            gandr_surface_syntax::NodeLabel::Grout { .. }
                                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                        )),
                    "{source}: the repair at {:?} stands inside documentation",
                    node.span()
                );
                pending.extend(tree.children(next).map(|child| (child, documented)));
            }
        }
        Ok(())
    }
}
