//! The layout pass: a column stack over the labeled stream, which writes the
//! braces and separators a block's indentation implies.
//!
//! A layout block opens at an opener whose line ends with it, at the column
//! of the next line's first token. A line at the block's column begins a new
//! item, and a line left of the column closes the block. A word at column
//! zero closes every block and every open bracket, so a fault stays in its
//! own declaration.
//!
//! Two repairs keep a block open past a line that stands left of its column
//! at no column of an open block. The pass reads one line ahead for them:
//!
//! | the line | it stays in the block when | the block's column |
//! | --- | --- | --- |
//! | a dent | the next line stands at the block's column again | stays |
//! | the block's second item, the first too far right | the block holds one item and stands right of this line by less than this line stands right of the enclosing block, and the next line stands at this line's column or left of it, or no line follows | moves to this line's column |
//!
//! A line that the next line continues never stays, nor a line that leaves
//! open a bracket it opens, nor a line that closes a bracket an earlier line
//! opened, nor a line at column zero. A `)` with no open bracket to close
//! leaves every block open, so the melder marks it where it stands.
//!
//! A line at column zero inside nested blocks gives the column rule no block
//! to choose, so it closes every block. The melder's dry run judges the line
//! in each block that its column closes, and it gives the pass the block it
//! keeps as a [`Move`]: the line closes fewer blocks and stays in that block,
//! as a line at the block's column does. A block's first line at column zero
//! closes its block at once. A move that closes nothing opens the block at
//! the least column of the lines after it, with the moved line as its first
//! item (#4853, #5434).
//!
//! | opener | block | separator |
//! | --- | --- | --- |
//! | `=` ending a `def` head that has a `->` result | a statement body | `;` |
//! | `match` whose head ends its line with no `{` | an arm list | none: a line-leading `\|` separates arms |
//! | `where` ending its line | a declaration body | `;`, and one before the block's close |
//! | an explicit `{` | a statement block | `;` |
//! | an explicit `{` after `where` | a declaration body | `;`, and one before the `}` |
//! | the source | its declarations | `;` after a `def` only, none at the end |
//!
//! The pass writes zero-width tokens the molder reads as `{`, `;` and `}`, so
//! the grammar takes them as the braces it already knows. A body's `=` is
//! relabeled as the block's `{`, and the body is then the braced body.
//!
//! An item ends with a separator only when it needs one. An item a
//! line-leading `|` begins is a constructor, a clause or an arm, which the
//! next item's head ends. An item already ends at a `;`, a `,`, an opening
//! brace or an explicit `}`, and a declaration also ends at a block's
//! virtual close, as a braced declaration ends at its brace. A declaration
//! body ends only an item a word begins that holds more than that word, so
//! a stray token stays in its own item. The top level ends only a `def`, the
//! one top-level form a layout body writes without its `;`, and the end of
//! the source ends nothing, so a source cut short stays open where it stops.
//! No separator is written before a closer or a line-leading `|`, or after an
//! attribute.
//!
//! Inside parentheses, brackets, shell blocks, attributes and the other
//! bracketed forms no opener opens and no separator is written.

use alloc::vec::Vec;

use anodized::spec;

use super::Bracket;
use super::Lexeme;
use super::SourceBytes;
use super::Token;
use super::bracket;
use crate::meld::primitive_copy_wrapper;

/// What ends the items of a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sep
{
    /// Statements: `;` between them.
    Semi,
    /// Declarations in a body: `;` after each, the last one included.
    Decl,
    /// The source's declarations: `;` after a `def`.
    Top,
    /// Arms: nothing, as a line-leading `|` separates arms.
    Arms,
}

/// What kind of bracket or block a frame is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A layout block at its column.
    Layout
    {
        /// The column of the block's first token.
        column: u32,
    },
    /// An explicit host brace `{`, with the column of its first token once
    /// one is read.
    Brace
    {
        /// The column its items stand at.
        column: Option<u32>,
    },
    /// A parenthesis, a bracket, a shell block, an attribute, or a brace
    /// some sigil leads.
    Plain,
}

/// How far a `def` head has read toward its body's `=`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Opener
{
    /// No `def` head waits for its `=`.
    #[default]
    None,
    /// A `def` began the item.
    Def,
    /// The `def` head has met `->` after its parameters.
    Arrow,
}

/// What began an item.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Lead
{
    /// Any other token.
    #[default]
    Other,
    /// A line-leading `|`: a constructor, a clause or an arm.
    Bar,
    /// A word, as a declaration's keyword is.
    Word,
}

/// What the current item of a block has read.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Head
{
    /// How far its `def` head has read.
    opener: Opener,
    /// The item is a `def`.
    defined: bool,
    /// What began the item.
    lead: Lead,
    /// The item holds a token after its first.
    more: bool,
}

impl Head
{
    /// The head of an item whose first token is of `lexeme`.
    ///
    /// # Specification
    /// trivial.
    fn begun(lexeme: Lexeme) -> Self
    {
        Self {
            lead: if lexeme == Lexeme::ArmBar {
                Lead::Bar
            }
            else if lexeme == Lexeme::LowerWord {
                Lead::Word
            }
            else {
                Lead::Other
            },
            ..Self::default()
        }
    }
}

/// One open bracket or layout block, and its current item.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Frame
{
    /// The bracket or block.
    kind: Kind,
    /// What ends its items.
    sep: Sep,
    /// Its current item.
    head: Head,
    /// How many items it has begun.
    items: u32,
}

impl Frame
{
    /// A frame of `kind` whose items `sep` ends, before its first item.
    ///
    /// # Specification
    /// trivial.
    fn new(
        kind: Kind,
        sep: Sep,
    ) -> Self
    {
        Self {
            kind,
            sep,
            head: Head::default(),
            items: 0,
        }
    }
}

/// What follows the tokens [`lay_out`] lays out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Next
{
    /// The end of the source, which ends no top-level item.
    End,
    /// A word or an attribute at column zero, which closes every block and
    /// ends the top-level item before it.
    Reset,
}

/// An opener waiting for the next significant token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pending
{
    /// Nothing waits.
    None,
    /// A `def` body's `=`, at its index in the stream.
    Body
    {
        /// The `=`'s index.
        at: usize,
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `where` that opens a declaration body.
    Members
    {
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `match` whose arms may open at the next line at its depth.
    Arms
    {
        /// The frame depth the `match` stands at.
        depth: usize,
        /// The indentation of the opener's line.
        indent: u32,
    },
}

/// The last significant token the pass met or wrote.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Prev<'bytes>
{
    /// No token yet.
    Start,
    /// A token the pass wrote, or a `=` it relabeled as an opener.
    Virtual(Lexeme),
    /// A token of the source, with its bytes.
    Written(Lexeme, &'bytes [u8]),
}

/// A zero-width token the pass writes before the token at `before`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Insertion
{
    /// The index in the stream the token goes before.
    before: usize,
    /// The token.
    token: Token,
}

primitive_copy_wrapper!(
    /// A column of a line, counted from zero.
    struct Column(u32);
);

/// A line that the melder's dry run keeps in a layout block that its column
/// closes. The block's virtual `}` moves past the line (#4853, #5434).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Move
{
    /// Where the line's first token starts.
    pub line: u32,
    /// How many of the blocks that the line's column closes the line closes,
    /// innermost first. With none, the line stays in the innermost block.
    pub closes: u32,
}

primitive_copy_wrapper!(
    /// Whether an item needs a separator to end it.
    struct Unended(bool);
);

/// The insertions the pass plans, and where the last significant token ends.
#[derive(Debug)]
struct Plan<'bytes>
{
    /// The insertions, by ascending `before`.
    planned: Vec<Insertion>,
    /// The index after the last significant token.
    after: usize,
    /// The byte offset where the last significant token ends.
    end: u32,
    /// The last significant token met or written.
    prev: Prev<'bytes>,
}

impl Plan<'_>
{
    /// Plan a zero-width `lexeme` right after the last significant token,
    /// before the space that follows it, so a block ends where its last token
    /// does and a comment after it stays outside.
    ///
    /// # Specification
    /// trivial.
    fn place(
        &mut self,
        lexeme: Lexeme,
    )
    {
        self.planned.push(Insertion {
            before: self.after,
            token: Token {
                lexeme,
                start: self.end,
                end: self.end,
            },
        });
        self.prev = Prev::Virtual(lexeme);
    }

    /// Whether `frame`'s current item needs a separator to end it, after the
    /// last significant token.
    ///
    /// # Specification
    /// trivial.
    fn unended(
        &self,
        frame: &Frame,
    ) -> Unended
    {
        let item = frame.head;
        let declaration = matches!(frame.sep, Sep::Decl | Sep::Top);
        let ended = match self.prev {
            Prev::Start => true,
            Prev::Virtual(lexeme) => {
                matches!(lexeme, Lexeme::LayoutOpen | Lexeme::LayoutSemi)
                    || (declaration && lexeme == Lexeme::LayoutClose)
            },
            Prev::Written(lexeme, spelled) => {
                (lexeme == Lexeme::Punct && matches!(spelled, b";" | b"," | b"{" | b"}"))
                    // A string left open: its interior ends nothing.
                    || matches!(
                        lexeme,
                        Lexeme::StringFragment
                            | Lexeme::ShellStringFragment
                            | Lexeme::EscapeSequence
                    )
            },
        };
        let wanted = match frame.sep {
            Sep::Semi => true,
            Sep::Decl => item.lead == Lead::Word && item.more,
            Sep::Top => item.defined,
            Sep::Arms => false,
        };
        Unended(wanted && item.lead != Lead::Bar && !ended)
    }

    /// Close the layout block `frame` is: a declaration body's last item
    /// takes its `;` first.
    ///
    /// # Specification
    /// trivial.
    fn close(
        &mut self,
        frame: &Frame,
    )
    {
        if frame.sep == Sep::Decl && bool::from(self.unended(frame)) {
            self.place(Lexeme::LayoutSemi);
        }
        self.place(Lexeme::LayoutClose);
    }
}

/// Write the layout blocks of `bytes` into its labeled and arm-marked
/// `tokens`, in place, with each line of `moves` kept in a block that its
/// column closes.
///
/// # Specification
/// - requires: `tokens` are [`super::label`]'s tokens of `bytes` before layout,
///   arm bars marked, and `moves` ascend by line.
/// - ensures: every token of `tokens` stays, in order, with its span; a `=`
///   that opens a body is relabeled [`Lexeme::LayoutOpen`]; every other added
///   token is a zero-width [`Lexeme::LayoutOpen`], [`Lexeme::LayoutSemi`] or
///   [`Lexeme::LayoutClose`] at the end of the significant token before it, so
///   the spans still tile the source. A line whose first token starts at a
///   move's line, and which neither resets nor closes a bracket, closes only
///   the move's count of the blocks its column closes, and then stays in the
///   next block as a line at that block's column does. The first of those
///   blocks is the block an opener waits to open, when the line stands at or
///   left of the opener's line. A move that closes nothing opens that block at
///   the least column of the lines after the moved line that stand right of the
///   opener's line, up to the first line at or left of it, and the moved line
///   is its first item.
/// - panics: none.
/// - executable: none — the clauses compare the stream with itself before the
///   pass, which the witnesses do over each rule.
///
/// # Adequacy
/// - hypothesis: L3 — each opener, the column rule in a layout block, in a
///   brace and at the top level, a dedent, a word at column zero, each place a
///   separator is left out, a declaration body's last `;` and a moved line
///   write their tokens; a rule left out or misplaced changes a witness's
///   marks.
/// - witness: `label::layout::tests::a_line_final_opener_opens_a_block_at_the_next_column`
/// - witness: `label::layout::tests::a_line_at_the_column_ends_a_statement`
/// - witness: `label::layout::tests::a_declaration_ends_where_its_form_needs_its_semicolon`
/// - witness: `label::layout::tests::a_word_at_column_zero_closes_every_block`
/// - witness: `label::layout::tests::a_moved_line_stays_in_the_block_its_move_names_5434`
/// - witness: `label::tests::an_edit_relabels_as_the_edited_source_labels`
#[expect(clippy::too_many_lines, reason = "one column-stack state machine")]
pub(super) fn lay_out(
    bytes: SourceBytes<'_>,
    tokens: &mut Vec<Token>,
    next: Next,
    mut moves: &[Move],
)
{
    let text = |token: &Token| {
        bytes
            .0
            .get(
                usize::try_from(token.start).unwrap_or(usize::MAX)
                    .. usize::try_from(token.end).unwrap_or(usize::MAX),
            )
            .unwrap_or_default()
    };
    let mut plan = Plan {
        planned: Vec::new(),
        after: 0,
        end: 0,
        prev: Prev::Start,
    };
    let mut frames: Vec<Frame> = alloc::vec![Frame::new(Kind::Layout { column: 0 }, Sep::Top)];
    let mut line_start;
    let mut line_begin = 0_u32;
    let mut line_indent = 0_u32;
    let mut pending = Pending::None;
    let mut before_arrow: &[u8] = b"";
    let mut attribute: Option<usize> = None;
    let mut after_attribute = false;
    let mut restart = false;
    for index in 0 .. tokens.len() {
        let Some(&token) = tokens.get(index)
        else {
            break;
        };
        if token.lexeme == Lexeme::Space {
            continue;
        }
        // A line starts at this token when a newline stands in the space
        // since the last significant token. The search runs back from the
        // token and stops at the first newline, past the indentation only.
        let newline = if token.start == plan.end {
            None
        }
        else {
            let gap = usize::try_from(plan.end).unwrap_or(usize::MAX)
                .. usize::try_from(token.start).unwrap_or(usize::MAX);
            bytes
                .0
                .get(gap.clone())
                .unwrap_or_default()
                .iter()
                .rposition(|&byte| byte == b'\n')
                .map(|newline| gap.start.saturating_add(newline).saturating_add(1))
        };
        line_start = newline.is_some() || plan.after == 0;
        if let Some(begin) = newline {
            line_begin = u32::try_from(begin).unwrap_or(u32::MAX);
        }
        let punct = matches!(
            token.lexeme,
            Lexeme::Punct | Lexeme::SubshellOpen | Lexeme::SubshellClose
        );
        // A token inside a line that is no bracket, no punctuation and no
        // opener's keyword, met while no opener waits, only extends the item.
        if !line_start
            && !punct
            && (token.lexeme != Lexeme::LowerWord
                || !matches!(token.end.saturating_sub(token.start), 3 | 5))
            && !restart
            && pending == Pending::None
            && let Some(frame) = frames.last_mut()
            && !matches!(frame.kind, Kind::Brace { column: None })
        {
            frame.head.more = true;
            after_attribute = false;
            plan.prev = Prev::Written(token.lexeme, b"");
            plan.after = index.saturating_add(1);
            plan.end = token.end;
            before_arrow = b"";
            continue;
        }
        let column = token.start.saturating_sub(line_begin);
        let spelled = text(&token);
        let nesting = bracket(token, bytes);
        let closer = nesting == Bracket::Close;
        let brace = token.lexeme == Lexeme::Punct && spelled == b"{";
        let members = matches!(pending, Pending::Members { .. });
        let mut opened = false;
        // The move the melder's dry run asks for at this line, and the column
        // a moved first line opens its opener's block at.
        let mut step = if line_start && !closer {
            next_move(&mut moves, token)
        }
        else {
            None
        };
        let waiting = match pending {
            Pending::Body { indent, .. }
            | Pending::Members { indent }
            | Pending::Arms { indent, .. } => Some(Column(indent)),
            Pending::None => None,
        };
        let below = step
            .and(waiting)
            .and_then(|indent| {
                block_column(bytes, tokens.get(index ..).unwrap_or_default(), indent)
            })
            .map(u32::from);
        let mut open = |frames: &mut Vec<Frame>, plan: &mut Plan<'_>, indent: u32, sep: Sep| {
            if column > indent {
                frames.push(Frame::new(Kind::Layout { column }, sep));
                opened = true;
            }
            // A moved line at or left of its opener's line, whose move closes
            // nothing, is the block's first line, at the least column of the
            // lines the block holds after it.
            else if let Some(Move { closes: 0, .. }) = step
                && let Some(below) = below
            {
                frames.push(Frame::new(Kind::Layout { column: below }, sep));
                opened = true;
            }
            else {
                plan.place(Lexeme::LayoutClose);
                // The block's close is the first close the move counts.
                if let Some(Move { ref mut closes, .. }) = step {
                    *closes = closes.saturating_sub(1);
                }
            }
        };
        match pending {
            Pending::Body { at, indent } => {
                pending = Pending::None;
                if line_start {
                    if let Some(equals) = tokens.get_mut(at) {
                        equals.lexeme = Lexeme::LayoutOpen;
                    }
                    plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Semi);
                }
            },
            Pending::Members { indent } => {
                pending = Pending::None;
                if line_start && !brace {
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Decl);
                }
            },
            Pending::Arms { depth, indent } => {
                if line_start && frames.len() == depth && !brace {
                    pending = Pending::None;
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Arms);
                }
            },
            Pending::None => {},
        }
        // A word or an attribute at column zero resets: it closes every
        // block and every bracket, a brace that waits for its first item
        // included.
        let reset = bool::from(super::resets(bytes, token));
        if !reset
            && let Some(&mut Frame {
                kind:
                    Kind::Brace {
                        column: ref mut first @ None,
                    },
                ..
            }) = frames.last_mut()
        {
            *first = Some(column);
            opened = true;
        }
        // A block's first line begins its first item.
        let mut begins = opened;
        if reset {
            // A declaration at column zero closes every block, a bracket left
            // open included, so a fault stays in its own declaration.
            while frames.len() > 1
                && let Some(frame) = frames.pop()
            {
                if matches!(frame.kind, Kind::Layout { .. }) {
                    plan.close(&frame);
                }
            }
            attribute = None;
            pending = Pending::None;
        }
        if line_start {
            line_indent = column;
        }
        if line_start && !opened {
            let line = LineStart {
                rest: tokens.get(index ..).unwrap_or_default(),
                column,
            };
            let stays = match step {
                Some(step) => bool::from(moved(&mut plan, &mut frames, line, step)),
                None => !closer && bool::from(dented(bytes, line, &mut frames)),
            };
            while !stays
                && frames.len() > 1
                && let Some(&frame) = frames.last()
                && let Kind::Layout { column: block } = frame.kind
                && column < block
            {
                plan.close(&frame);
                frames.pop();
            }
            if let Some(&frame) = frames.last()
                && match frame.kind {
                    Kind::Layout { column: block } => block == column || stays,
                    Kind::Brace {
                        column: Some(block),
                    } => block == column,
                    Kind::Brace { column: None } | Kind::Plain => false,
                }
                && !closer
            {
                if frame.sep != Sep::Arms
                    && !after_attribute
                    && token.lexeme != Lexeme::ArmBar
                    && bool::from(plan.unended(&frame))
                {
                    plan.place(Lexeme::LayoutSemi);
                }
                begins = true;
            }
        }
        if let Some(frame) = frames.last_mut() {
            if begins || restart {
                frame.head = Head::begun(token.lexeme);
                frame.items = frame.items.saturating_add(1);
            }
            else {
                frame.head.more = true;
            }
        }
        restart = false;
        let opener_allowed = frames
            .last()
            .is_some_and(|frame| matches!(frame.kind, Kind::Layout { .. } | Kind::Brace { .. }));
        // A `)` with no open bracket to close is stray. It leaves every layout
        // block open, and the melder marks it where it stands. A stray `}` or
        // `]` still closes the blocks: the melder pairs it with a block's
        // virtual brace when the block stays open.
        if closer
            && (spelled != b")"
                || frames
                    .iter()
                    .skip(1)
                    .any(|frame| !matches!(frame.kind, Kind::Layout { .. })))
        {
            while frames.len() > 1
                && let Some(&frame) = frames.last()
                && matches!(frame.kind, Kind::Layout { .. })
            {
                plan.close(&frame);
                frames.pop();
            }
            if frames.len() > 1
                && let Some(frame) = frames.pop()
                && frame.sep == Sep::Decl
                && bool::from(plan.unended(&frame))
            {
                plan.place(Lexeme::LayoutSemi);
            }
            if let Pending::Arms { depth, .. } = pending
                && frames.len() < depth
            {
                pending = Pending::None;
            }
        }
        else if nesting == Bracket::Open {
            if attribute.is_none() && matches!(spelled, b"@[" | b"@![") {
                attribute = Some(frames.len());
            }
            frames.push(if brace {
                Frame::new(
                    Kind::Brace { column: None },
                    if members { Sep::Decl } else { Sep::Semi },
                )
            }
            else {
                Frame::new(Kind::Plain, Sep::Semi)
            });
            if let Pending::Arms { depth, .. } = pending
                && frames.len() == depth.saturating_add(1)
                && brace
            {
                pending = Pending::None;
            }
        }
        else if token.lexeme == Lexeme::LowerWord && opener_allowed {
            match spelled {
                b"def" => {
                    if let Some(frame) = frames.last_mut() {
                        frame.head.opener = Opener::Def;
                        frame.head.defined = true;
                    }
                },
                b"match" => {
                    pending = Pending::Arms {
                        depth: frames.len(),
                        indent: line_indent,
                    };
                },
                b"where" => {
                    pending = Pending::Members {
                        indent: line_indent,
                    };
                },
                _ => {},
            }
        }
        else if token.lexeme == Lexeme::Punct {
            match spelled {
                b"->" => {
                    if let Some(frame) = frames.last_mut()
                        && frame.head.opener == Opener::Def
                        && matches!(before_arrow, b")" | b"]")
                    {
                        frame.head.opener = Opener::Arrow;
                    }
                },
                b"=" => {
                    if let Some(frame) = frames.last_mut() {
                        if frame.head.opener == Opener::Arrow && opener_allowed {
                            pending = Pending::Body {
                                at: index,
                                indent: line_indent,
                            };
                        }
                        frame.head.opener = Opener::None;
                    }
                },
                b";" | b"," => {
                    // A `;` ends the item, and the next token begins the
                    // next. A `,` separates within an item: a clause's
                    // patterns, a call's arguments.
                    restart = spelled == b";";
                    if let Pending::Arms { depth, .. } = pending
                        && depth == frames.len()
                    {
                        pending = Pending::None;
                    }
                },
                _ => {},
            }
        }
        after_attribute = closer && attribute == Some(frames.len());
        if after_attribute {
            attribute = None;
        }
        plan.prev = Prev::Written(token.lexeme, spelled);
        plan.after = index.saturating_add(1);
        plan.end = token.end;
        before_arrow = spelled;
    }
    // A reset settles a waiting opener as any line at column zero does: no
    // block opens left of its opener's line, so the block closes at once.
    if next == Next::Reset {
        match pending {
            Pending::Body { at, .. } => {
                if let Some(equals) = tokens.get_mut(at) {
                    equals.lexeme = Lexeme::LayoutOpen;
                }
                plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                plan.place(Lexeme::LayoutClose);
            },
            Pending::Members { .. } => {
                plan.place(Lexeme::LayoutOpen);
                plan.place(Lexeme::LayoutClose);
            },
            Pending::Arms { depth, .. } if frames.len() == depth => {
                plan.place(Lexeme::LayoutOpen);
                plan.place(Lexeme::LayoutClose);
            },
            Pending::Arms { .. } | Pending::None => {},
        }
    }
    // What follows closes every block. The end of the source ends no
    // top-level item, so a source cut short stays open where it stops, for
    // the closings and the continuations an editor reads there. A reset ends
    // the item before it as the column rule does.
    while frames.len() > 1
        && let Some(frame) = frames.pop()
    {
        if matches!(frame.kind, Kind::Layout { .. }) {
            plan.close(&frame);
        }
    }
    if next == Next::Reset
        && !after_attribute
        && let Some(base) = frames.first()
        && bool::from(plan.unended(base))
    {
        plan.place(Lexeme::LayoutSemi);
    }
    insert(tokens, &plan.planned);
}

primitive_copy_wrapper!(
    /// Whether a line left of its block stays in the block.
    struct Stays(bool);
);

/// A line's first token, as [`dented`] reads it.
#[derive(Clone, Copy, Debug)]
struct LineStart<'tokens>
{
    /// The line's first token and every token after it.
    rest: &'tokens [Token],
    /// The column of the line's first token.
    column: u32,
}

/// Whether `line` stays in the innermost layout block although it stands
/// left of the block's column. The line stays when it stands at no column of
/// an open block, it ends with no token that the next line continues, and one
/// of two readings holds:
///
/// | reading | the next line | the block | the block's column |
/// | --- | --- | --- | --- |
/// | a dent: one line left of its block | at the block's column | any | stays |
/// | the block's first line stood too far right | at this line's column or left of it, or none | holds one item, and stands right of this line by less than this line stands right of the enclosing block | moves to this line's column |
///
/// A line at column zero aligns with the source's own block, so it never
/// stays. A dent there cannot tell which nested block it leaves. A line one
/// column right of the enclosing block, after a block one column right of the
/// line, closes the block. A deleted keyword leaves an item of the enclosing
/// block there more often than a block's first line.
///
/// # Specification
/// - requires: `line` begins at the first token of its line, and `frames` are
///   the open frames before it.
/// - ensures: true only when the innermost frame is a layout block right of the
///   line's column, and then the block's column is the one the table names.
/// - panics: none.
/// - executable: none — the clauses read the frames before the call and the
///   lines around the token, which the witnesses fix for each reading.
///
/// # Adequacy
/// - hypothesis: L3 — a dent, a first line too far right and a line that the
///   next line continues each take their own reading; a reading left out or
///   misapplied changes a witness's marks.
/// - witness: `label::layout::tests::a_line_left_of_its_block_stays_when_the_next_line_returns`
/// - witness: `label::layout::tests::a_block_moves_left_to_the_column_its_lines_keep`
/// - witness: `label::layout::tests::a_line_that_another_line_continues_never_stays`
fn dented(
    bytes: SourceBytes<'_>,
    line: LineStart<'_>,
    frames: &mut [Frame],
) -> Stays
{
    let column = line.column;
    let Some((top, below)) = frames.split_last_mut()
    else {
        return Stays(false);
    };
    let Kind::Layout { column: block } = top.kind
    else {
        return Stays(false);
    };
    let at = |frame: &Frame| match frame.kind {
        Kind::Layout { column }
        | Kind::Brace {
            column: Some(column),
        } => Some(column),
        Kind::Brace { column: None } | Kind::Plain => None,
    };
    if column >= block || below.iter().any(|frame| at(frame) == Some(column)) {
        return Stays(false);
    }
    let NextLine {
        column: next,
        continued,
    } = next_line(bytes, line.rest);
    if continued {
        return Stays(false);
    }
    let landing = below.last().and_then(at).unwrap_or(0);
    if next == Some(block) {
        return Stays(true);
    }
    if top.items == 1
        && column > landing
        && block.saturating_sub(column) < column.saturating_sub(landing)
        && next.is_none_or(|next| next <= column)
    {
        top.kind = Kind::Layout { column };
        return Stays(true);
    }
    Stays(false)
}

/// The column of the block that a moved line opens, as its first line, when
/// it stands at or left of its opener's line at `indent`: the least column of
/// the lines after the first of `rest` that stand right of `indent`, up to
/// the first line at or left of it.
///
/// # Specification
/// trivial.
fn block_column(
    bytes: SourceBytes<'_>,
    rest: &[Token],
    indent: Column,
) -> Option<Column>
{
    let mut least: Option<Column> = None;
    for column in following(bytes, rest).filter_map(|after| after.begins) {
        if column <= indent {
            break;
        }
        least = Some(least.map_or(column, |least| least.min(column)));
    }
    least
}

/// A significant token after a line's first token, as [`following`] reads
/// it.
#[derive(Clone, Copy, Debug)]
struct Following
{
    /// The token.
    token: Token,
    /// The column of the line that the token begins, none when the token does
    /// not begin a line.
    begins: Option<Column>,
}

/// Each significant token after the first of `rest`, in order, with the
/// column of the line it begins: the one place the layout pass finds a line
/// start after a token.
///
/// # Specification
/// trivial.
fn following<'rest>(
    bytes: SourceBytes<'rest>,
    rest: &'rest [Token],
) -> impl Iterator<Item = Following> + 'rest
{
    let mut last = rest.first().map_or(0, |first| first.end);
    rest.iter()
        .skip(1)
        .filter(|token| token.lexeme != Lexeme::Space)
        .map(move |&token| {
            let gap = usize::try_from(last).unwrap_or(usize::MAX)
                .. usize::try_from(token.start).unwrap_or(usize::MAX);
            let begins = bytes
                .0
                .get(gap.clone())
                .unwrap_or_default()
                .iter()
                .rposition(|&byte| byte == b'\n')
                .map(|newline| {
                    let begin = u32::try_from(gap.start.saturating_add(newline).saturating_add(1))
                        .unwrap_or(u32::MAX);
                    Column(token.start.saturating_sub(begin))
                });
            last = token.end;
            Following { token, begins }
        })
}

/// The move of the line that `token` begins, when `moves` holds one, with
/// `moves` advanced past it and past each move of an earlier line.
///
/// # Specification
/// trivial.
fn next_move(
    moves: &mut &[Move],
    token: Token,
) -> Option<Move>
{
    while let Some((&first, rest)) = moves.split_first()
        && first.line <= token.start
    {
        *moves = rest;
        if first.line == token.start {
            return Some(first);
        }
    }
    None
}

/// Close the layout blocks that `line` stands left of, at most `step.closes`
/// of them, innermost first, and answer whether the line then stays in the
/// innermost frame left open: a layout block that the line's column closes.
///
/// # Specification
/// - requires: `frames` are the open frames before the line.
/// - ensures: each frame closed is a layout block right of the line's column,
///   at most `step.closes` of them, and the base frame stays; true only when
///   the innermost frame left open is a layout block right of the line's
///   column.
/// - panics: none.
/// - executable: none — the clauses read the frames before the call, which the
///   witness fixes for each count.
///
/// # Adequacy
/// - hypothesis: L3 — a line at column zero in two nested blocks stays in the
///   inner block with no close, in the outer block with one, and in neither
///   with two; a count off by one moves a witness's line.
/// - witness: `label::layout::tests::a_moved_line_stays_in_the_block_its_move_names_5434`
fn moved(
    plan: &mut Plan<'_>,
    frames: &mut Vec<Frame>,
    line: LineStart<'_>,
    step: Move,
) -> Stays
{
    let right =
        |frame: &Frame| matches!(frame.kind, Kind::Layout { column } if line.column < column);
    let mut closed = 0_u32;
    while closed < step.closes
        && frames.len() > 1
        && let Some(&frame) = frames.last()
        && right(&frame)
    {
        plan.close(&frame);
        frames.pop();
        closed = closed.saturating_add(1);
    }
    Stays(frames.len() > 1 && frames.last().is_some_and(right))
}

/// What the lines after a line's first token hold, as [`dented`] reads them.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NextLine
{
    /// The column of the next line's first significant token, none when no
    /// line follows.
    column: Option<u32>,
    /// The line belongs to an item before it or after it: it leaves open a
    /// bracket it opens, it ends with a token the next line continues (an
    /// opener, a separator, an arrow or a `:`), or it closes a bracket an
    /// earlier line opened.
    continued: bool,
}

/// The line after the first of `rest`, and whether the line the first of
/// `rest` stands on belongs to an item before it.
///
/// # Specification
/// trivial.
fn next_line(
    bytes: SourceBytes<'_>,
    rest: &[Token],
) -> NextLine
{
    let spelled = |token: &Token| {
        bytes
            .0
            .get(
                usize::try_from(token.start).unwrap_or(usize::MAX)
                    .. usize::try_from(token.end).unwrap_or(usize::MAX),
            )
            .unwrap_or_default()
    };
    let continues = |token: &Token| {
        matches!(
            (token.lexeme, spelled(token)),
            (Lexeme::LowerWord, b"where" | b"match")
                | (Lexeme::Punct, b"=" | b"," | b"->" | b"=>" | b":")
        )
    };
    let Some(&first) = rest.first()
    else {
        return NextLine {
            column: None,
            continued: false,
        };
    };
    // How deep the line stands in brackets it opens itself, and whether it
    // closed one it did not open.
    let mut depth = 0_u32;
    let mut closes_earlier = false;
    let nest = |token: Token, depth: &mut u32, closes_earlier: &mut bool| {
        if token.lexeme == Lexeme::Punct {
            match bracket(token, bytes) {
                Bracket::Open => *depth = depth.saturating_add(1),
                Bracket::Close => {
                    *closes_earlier |= *depth == 0;
                    *depth = depth.saturating_sub(1);
                },
                Bracket::Neither => {},
            }
        }
    };
    nest(first, &mut depth, &mut closes_earlier);
    let mut last = first;
    for Following { token, begins } in following(bytes, rest) {
        if let Some(column) = begins {
            return NextLine {
                column: Some(u32::from(column)),
                continued: closes_earlier || depth > 0 || continues(&last),
            };
        }
        nest(token, &mut depth, &mut closes_earlier);
        last = token;
    }
    NextLine {
        column: None,
        continued: closes_earlier || depth > 0 || continues(&last),
    }
}

/// Write each of `planned` into `tokens` before the token it names, in place:
/// the vector grows once and every token moves at most once.
///
/// # Specification
/// - requires: `planned` is ascending by `before`, each at most `tokens.len()`.
/// - ensures: `tokens` is its old tokens with each insertion before the old
///   token at its `before`, insertions at one place in their order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`lay_out`], whose witnesses place several tokens at
///   one place and tokens at the stream's end.
/// - witness: `label::layout::tests::a_word_at_column_zero_closes_every_block`
#[spec(captures: before = tokens.len(), ensures: |_| tokens.len() == before.saturating_add(planned.len()))]
fn insert(
    tokens: &mut Vec<Token>,
    planned: &[Insertion],
)
{
    let Some(&filler) = planned.first().map(|insertion| &insertion.token)
    else {
        return;
    };
    let mut read = tokens.len();
    tokens.resize(read.saturating_add(planned.len()), filler);
    for (shift, insertion) in (1 ..= planned.len()).rev().zip(planned.iter().rev()) {
        let before = insertion.before.min(read);
        tokens.copy_within(before .. read, before.saturating_add(shift));
        if let Some(slot) = tokens.get_mut(before.saturating_add(shift).saturating_sub(1)) {
            *slot = insertion.token;
        }
        read = before;
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;

    use gandr_surface_syntax::SourceFragment;

    use super::Lexeme;
    use super::Move;
    use crate::label::label_moving;

    /// `src` with each layout token marked where it stands.
    ///
    /// # Specification
    /// trivial.
    fn marked<'text>(src: impl Into<SourceFragment<'text>>) -> String
    {
        marked_moving(src, &[])
    }

    /// `src` with each layout token marked where it stands, each line of
    /// `moves` kept in the block its move names.
    ///
    /// # Specification
    /// trivial.
    fn marked_moving<'text>(
        src: impl Into<SourceFragment<'text>>,
        moves: &[Move],
    ) -> String
    {
        let src: SourceFragment<'text> = src.into();
        let text = AsRef::<str>::as_ref(&src);
        let mut out = String::new();
        for token in label_moving(src, moves) {
            let spelled = text
                .get(
                    usize::try_from(token.start).unwrap_or(usize::MAX)
                        .. usize::try_from(token.end).unwrap_or(usize::MAX),
                )
                .unwrap_or_default();
            if token.lexeme == Lexeme::LayoutOpen && token.start < token.end {
                out.push('⟪');
                out.push_str(spelled);
                out.push_str("→{⟫");
            }
            else if token.lexeme == Lexeme::LayoutOpen {
                out.push_str("⟪{⟫");
            }
            else if token.lexeme == Lexeme::LayoutSemi {
                out.push_str("⟪;⟫");
            }
            else if token.lexeme == Lexeme::LayoutClose {
                out.push_str("⟪}⟫");
            }
            else {
                out.push_str(spelled);
            }
        }
        out
    }

    #[test]
    fn a_line_final_opener_opens_a_block_at_the_next_column()
    {
        // A body's `=` is the block's brace.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n  y\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  let y = x⟪;⟫\n  y⟪}⟫\n"
        );
        // A `=` with its body on its own line opens nothing.
        assert_eq!(
            marked("def f(x : A) -> A = x;\n"),
            "def f(x : A) -> A = x;\n"
        );
        // A `match` head ending its line opens its arms, which take no
        // separator.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x\n    | a => a\n    | b => b\n}\n"),
            "def f(x : A) -> A {\n  match x⟪{⟫\n    | a => a\n    | b => b⟪}⟫\n}\n"
        );
        // A `match` whose head takes its brace opens nothing.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x {\n    | a => a\n  }\n}\n"),
            "def f(x : A) -> A {\n  match x {\n    | a => a\n  }\n}\n"
        );
        // A `where` ending its line opens a declaration body.
        assert_eq!(
            marked("theory S where\n  sort A : Type\n  sort B : Type\n"),
            "theory S where⟪{⟫\n  sort A : Type⟪;⟫\n  sort B : Type⟪;⟫⟪}⟫\n"
        );
        // A line no further right than the opener's closes the block it
        // opens at once.
        assert_eq!(
            marked("def f(x : A) -> A =\ndef g(x : A) -> A = x;\n"),
            "def f(x : A) -> A ⟪=→{⟫⟪}⟫\ndef g(x : A) -> A = x;\n"
        );
    }

    #[test]
    fn a_line_at_the_column_ends_a_statement()
    {
        // Inside an explicit brace the column rule separates statements, and
        // a `;` already written takes no second one.
        assert_eq!(
            marked("def f(x : A) -> A {\n  let y = x;\n  let z = y\n  z\n}\n"),
            "def f(x : A) -> A {\n  let y = x;\n  let z = y⟪;⟫\n  z\n}\n"
        );
        // A block-like statement ends at its brace; a continuation indented
        // past the column continues it; a comment after a statement stays
        // outside the separator.
        assert_eq!(
            marked("def f(x : A) -> A {\n  if x { a } else { b }\n  g x\n    y // c\n  z\n}\n"),
            "def f(x : A) -> A {\n  if x { a } else { b }\n  g x\n    y⟪;⟫ // c\n  z\n}\n"
        );
        // A line-leading bar and a closer take no separator; a sigil's brace
        // is no statement block.
        assert_eq!(
            marked("data D {\n  | a\n  | b\n}\ndef r() -> R { *{\n  x = 1\n  y = 2\n} }\n"),
            "data D {\n  | a\n  | b\n}\ndef r() -> R { *{\n  x = 1\n  y = 2\n} }\n"
        );
    }

    #[test]
    fn a_declaration_ends_where_its_form_needs_its_semicolon()
    {
        // In a brace after `where` a constructor is ended by the next
        // member's head, a member after a `;` is not ended twice, and the last
        // member takes its `;` before the brace.
        assert_eq!(
            marked(
                "data D : Type where {\n  | A : D\n  oper p : D;\n  rule : A ==> p\n  rule : p ==> A\n}\n"
            ),
            "data D : Type where {\n  | A : D\n  oper p : D;\n  rule : A ==> p⟪;⟫\n  rule : p ==> A⟪;⟫\n}\n"
        );
        // Members on one line stay one item.
        assert_eq!(
            marked("theory S where {\n  sort A : Type sort B : Type\n}\n"),
            "theory S where {\n  sort A : Type sort B : Type⟪;⟫\n}\n"
        );
        // A declaration at column zero ends a `def` before it, whose value
        // form takes a `;`, and nothing else: an attribute, a lone word and a
        // form that takes no `;` stay whole.
        assert_eq!(
            marked(
                "def f(x : A) -> A = x\n@[checks]\ndef g(x : A) -> A = x\noper h : A\n§\nrelease x ;\n"
            ),
            "def f(x : A) -> A = x⟪;⟫\n@[checks]\ndef g(x : A) -> A = x⟪;⟫\noper h : A\n§\nrelease x ;\n"
        );
        // The end of the source ends nothing, so a source cut short stays
        // open where it stops.
        assert_eq!(marked("def f(x : A) -> A = x"), "def f(x : A) -> A = x");
    }

    #[test]
    fn a_word_at_column_zero_closes_every_block()
    {
        // A dedent closes the blocks right of the line, and a word at column
        // zero closes every block, a bracket left open included.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x\n    | a => g(a\n  y\ndef h(x : A) -> A = x;\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫\n    | a => g(a\n  y⟪}⟫⟪}⟫\ndef h(x : A) -> A = x;\n"
        );
        // The end of the source closes every block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x\n    | a => a"),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫\n    | a => a⟪}⟫⟪}⟫"
        );
    }

    #[test]
    fn a_line_left_of_its_block_stays_when_the_next_line_returns()
    {
        // A dent: the line after it stands at the block's column again, so
        // the dented line is one more item of the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n let z = y\n  z\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  let y = x⟪;⟫\n let z = y⟪;⟫\n  z⟪}⟫\n"
        );
        // A line left of a block of two items, with no line after it at the
        // block's column, closes the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n  let z = y\n z\ndef g(x : A) -> A = x;\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  let y = x⟪;⟫\n  let z = y⟪}⟫\n z⟪;⟫\ndef g(x : A) -> A = x;\n"
        );
    }

    #[test]
    fn a_block_moves_left_to_the_column_its_lines_keep()
    {
        // The block's first line stands right of the lines after it, as a
        // deleted `let` leaves it, so the block takes their column.
        assert_eq!(
            marked("def f(x : A) -> A =\n   y = x\n  let z = y\n  z\n"),
            "def f(x : A) -> A ⟪=→{⟫\n   y = x⟪;⟫\n  let z = y⟪;⟫\n  z⟪}⟫\n"
        );
        // The block's last line moves it too.
        assert_eq!(
            marked("def f(x : A) -> A =\n   y = x\n  y\n"),
            "def f(x : A) -> A ⟪=→{⟫\n   y = x⟪;⟫\n  y⟪}⟫\n"
        );
        // A line one column right of the enclosing block, after a block one
        // column right of the line, is an item whose keyword is gone. The
        // block closes before it.
        assert_eq!(
            marked("def f(x : A) -> A =\n  x\n g(x : A) -> A = x;\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  x⟪}⟫\n g(x : A) -> A = x;\n"
        );
    }

    #[test]
    fn a_line_that_another_line_continues_never_stays()
    {
        // A line that opens a block of its own leaves the block before it.
        assert_eq!(
            marked("theory S where\n  sort A : Type\n T where\n  sort B : Type\n"),
            "theory S where⟪{⟫\n  sort A : Type⟪;⟫⟪}⟫\n T where⟪{⟫\n  sort B : Type⟪;⟫⟪}⟫\n"
        );
        // A line that closes a bracket it never opened belongs to an item
        // before it.
        assert_eq!(
            marked("theory S where\n  sort A : Type\n checks ]\ntheory T where\n  sort B : Type\n"),
            "theory S where⟪{⟫\n  sort A : Type⟪;⟫⟪}⟫\n checks ]\ntheory T where⟪{⟫\n  sort B : Type⟪;⟫⟪}⟫\n"
        );
        // A line at column zero closes every block, though the next line
        // stands at a block's column.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x\n    | a => a\n| b => b\n    | c => c\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫\n    | a => a⟪}⟫⟪}⟫\n| b => b\n    | c => c\n"
        );
    }

    #[test]
    fn a_stray_parenthesis_leaves_the_blocks_open()
    {
        // A `)` with no bracket to close stays inside the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = g x)\n  y\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  let y = g x)⟪;⟫\n  y⟪}⟫\n"
        );
        // A stray `}` still closes the blocks before it.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x}\n  y\n"),
            "def f(x : A) -> A ⟪=→{⟫\n  let y = x⟪}⟫}\n  y\n"
        );
    }

    #[test]
    fn a_moved_line_stays_in_the_block_its_move_names_5434()
    {
        // An arm at column zero inside two arm blocks and a body closes all
        // three. A move keeps it in the block its count of closes leaves.
        let source =
            "def f(x : A) -> A =\n  match x\n    | a => match a\n      | b => b\n| c => c\n";
        let line = u32::try_from(source.find("| c").unwrap_or_default()).unwrap_or(u32::MAX);
        let moved = |closes: u32| marked_moving(source, &[Move { line, closes }]);
        let head = "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫\n    | a => match a⟪{⟫\n      | b => b";
        assert_eq!(marked(source), format!("{head}⟪}}⟫⟪}}⟫⟪}}⟫\n| c => c\n"));
        assert_eq!(moved(0), format!("{head}\n| c => c⟪}}⟫⟪}}⟫⟪}}⟫\n"));
        assert_eq!(moved(1), format!("{head}⟪}}⟫\n| c => c⟪}}⟫⟪}}⟫\n"));
        assert_eq!(moved(2), format!("{head}⟪}}⟫⟪}}⟫\n| c => c⟪}}⟫\n"));
        // A count past the blocks the column closes closes every one of them.
        assert_eq!(moved(3), marked(source));
        // A word at column zero resets, and no move keeps it.
        let reset = source.replace("| c => c", "c");
        assert_eq!(
            marked_moving(reset.as_str(), &[Move { line, closes: 0 }]),
            marked(reset.as_str())
        );
        // A first arm at column zero closes its arms block at once. A move
        // that closes nothing opens the block at the least column of the
        // lines after it, and a move that closes one keeps the arm in the
        // body.
        let first = "def f(x : A) -> A =\n  match x\n| a => a\n    | b => b\n";
        let line = u32::try_from(first.find("| a").unwrap_or_default()).unwrap_or(u32::MAX);
        let first_moved = |closes: u32| marked_moving(first, &[Move { line, closes }]);
        assert_eq!(
            marked(first),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫⟪}⟫⟪}⟫\n| a => a\n    | b => b\n"
        );
        assert_eq!(
            first_moved(0),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫\n| a => a\n    | b => b⟪}⟫⟪}⟫\n"
        );
        assert_eq!(
            first_moved(1),
            "def f(x : A) -> A ⟪=→{⟫\n  match x⟪{⟫⟪}⟫\n| a => a\n    | b => b⟪}⟫\n"
        );
    }
}
