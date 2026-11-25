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
//! | `=` ending a `def` head | a statement block after the `=` | `;` |
//! | `=` ending the line of a `let`, a `var` or an assignment in a statement block | a statement block after the `=` | `;` |
//! | `=>` ending the line of an item that a line-leading `\|` begins: an arm, a clause | a statement block after the `=>` | `;` |
//! | `where` ending a `match` head or an `offer` head | an arm list | none: a line-leading `\|` separates arms |
//! | `do` ending a line | a statement block | `;` |
//! | `then` ending the line of an `if` head | the conditional's first block | `;` |
//! | `else` ending a line | the conditional's last block, after the `else` | `;` |
//! | `handle` ending a line | a handler's clauses, after the `handle` | none: a line-leading `\|` separates clauses |
//! | `where` ending the line of `rec` | its declarations, as the source's | `;` after a declaration that a keyword begins, and one before the block's close |
//! | `where` ending any other line | a declaration body | `;`, and one before the block's close |
//! | an explicit `{` | a statement block | `;` |
//! | an explicit `{` after a declaration's `where` | a declaration body | `;`, and one before the `}` |
//! | an explicit `{` after `rec`, or after the `where` of `rec` | its declarations, as the source's | `;` after a declaration that a keyword begins, and one before the `}` |
//! | the source | its declarations | `;` after a declaration that a keyword begins; at the end, one only after a `def` whose `=` opened a block |
//!
//! A `match` or `offer` head that ends its line with no `where` and no `{`
//! opens its arm list too, with an open of no width, so the parse stays
//! whole: the lowering refuses that head by name, as a head in layout form
//! with no `where` (`OutOfFragment.BareArms`).
//!
//! The pass writes zero-width tokens the molder reads as `{`, `;` and `}`, so
//! the grammar takes them as the braces it already knows. The line-final
//! `where` of a `match` head or of an `offer` head is relabeled as the arms'
//! `{`, so neither rule has a `where` of its own,
//! and a `where` that does not end the head's line is no part of the form.
//! The `where` of `rec` keeps its tile, as the `where` of a declaration does,
//! and its block opens after it. A line-final `do` is relabeled as the `{`
//! of a statement block, as the `where` of a `match` head is, after the head
//! of a loop, a thunk, a lambda, a fork or a migration. The grammar
//! has no tile for `do`, so a `do` that does not end its line, or that stands
//! inside a bracket, is a word that no form reads.
//!
//! A statement's `=` keeps its tile, because the grammar reads the block as
//! the expression after it. The pass writes an open of no width after the `=`
//! when the next line stands right of the statement's line. A line that stands
//! at the statement's column or left of it opens nothing. The `=` after the
//! name of a `type`, a `sort`, a `module` or a `face` opens nothing, because
//! its right side is no expression. A `{` after `glob` or `Cap` holds fields,
//! so no `=` in it opens. A line that starts with an explicit `{` opens
//! nothing, because a source in braces keeps its reading. The `=>` of an arm
//! or of a clause keeps its tile in the same way, and its block closes at the
//! next line that stands at the column of the arms or left of it.
//!
//! A line-final `then` of an `if` head is relabeled as the `{` of the first
//! block, as a `do` is. The grammar has no tile for `then`, so a `then` that
//! does not end its line is a word that no form reads. An `else` keeps its
//! tile, as the `=>` of an arm does. A line that starts with `else` closes the
//! blocks right of it by the column rule, and it continues the conditional:
//! the pass writes no separator before it.
//!
//! A handler opens its body by the `do` of its `effect` head. Its `handle`
//! keeps its tile, and when it ends its line, the clauses open after it as
//! an arm list. A line that starts with the `handle` of an `effect` above it
//! closes the body by the column rule and continues the handler, as a line
//! that starts with `else` continues the conditional.
//!
//! The `=` of a `def` keeps its tile in the same way, with a `->` result or
//! with none, and the `def` takes its `;` after the block's close. A `;` that
//! ends the last line of that block ends the `def`: the block closes before
//! it. The lowering reads a block of one expression there as that expression.
//!
//! An item ends with a separator only when it needs one. An item a
//! line-leading `|` begins is a constructor, a clause or an arm, which the
//! next item's head ends. An item already ends at a `;`, a `,` or an opening
//! brace. A declaration also ends at an explicit `}` and at the virtual close
//! of a body, as a braced declaration ends at its brace. A statement ends at
//! no `}`: its line end writes its separator, as after any other token. The
//! virtual close of
//! an arm list ends no declaration, since a `match` is an expression: `def f
//! (x : A) = match x where …` takes its `;` after its arms. An arm list takes
//! no separator, so an explicit `;` in a layout arm list closes that arm list
//! and each arm list then innermost before it, and the `;` is the enclosing
//! block's. An arm list in braces and a bracket keep their `;`. A `}` whose `{`
//! stands right after `=` closes a block expression, and it ends no item, so
//! `def f() -> T = { … }` takes its `;` as `def f() -> T = e` does. A
//! declaration body ends only an item a word begins that holds more than that
//! word, so a stray token stays in its own item. The top level ends an item
//! that a declaration's keyword begins and that holds more than that word: a
//! `def`, an `import`, a `type`. So a word at column zero ends the
//! declaration before it, and an `import` takes no `;`. A form at the top
//! level that no such keyword begins is a stray, and the top level ends no
//! stray, so the lowering refuses the stray alone. A `pub` alone on its line
//! marks the declaration after it, as an attribute does, and takes no
//! separator. The end of the source ends nothing, so a source cut short stays
//! open where it stops, but for a top-level `def` whose `=` opened a block:
//! the end of the source closes that block, as a word at column zero does,
//! and the `def` takes its `;`.
//! No separator is written before a closer or a line-leading `|`, or after an
//! attribute.
//!
//! Inside parentheses, brackets, attributes and the other
//! bracketed forms no opener opens and no separator is written.
//!
//! # References
//!
//! - `vault:01a1dd3c-1111-7400-ae8f-fb22f062f5fd` — newest: the layout design
//!   (§ layout-decision) — a line at the block's column ends the statement
//!   before it, whatever its last token is.

use alloc::vec::Vec;

use anodized::spec;

use super::Bracket;
use super::Lexeme;
use super::SourceBytes;
use super::Token;
use super::bracket;
use crate::meld::primitive_copy_wrapper;
use crate::mold::DECLARATION_LEADS;

/// What ends the items of a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sep
{
    /// Statements: `;` between them.
    Semi,
    /// Declarations in a body: `;` after each, the last one included.
    Decl,
    /// The declarations of the source or of a `rec` block: `;` after a
    /// declaration that a keyword begins.
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
    /// A parenthesis, a bracket, an attribute, or a brace
    /// some sigil leads.
    Plain,
}

/// Whether a `def` head waits for its body's `=`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Opener
{
    /// No `def` head waits for its `=`.
    #[default]
    None,
    /// A `def` began the item. Its `=` keeps its tile, and a block opens after
    /// it.
    Def,
    /// A `def` began the item, and a result arrow follows its parameters.
    Function,
}

/// The `def` whose `=` opens a block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Body
{
    /// A `def` with no result arrow. A `;` that ends the block's last line
    /// ends the `def`.
    Value,
    /// A `def` with a result arrow. A `;` that ends the block's last line
    /// stays in the block: the block runs that statement and returns the
    /// unit.
    Function,
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
    /// A word, as a member's keyword is.
    Word,
    /// A word of [`DECLARATION_LEADS`] at the top level.
    Keyword,
}

/// The form whose next word the current item waits for.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Awaits
{
    /// No form.
    #[default]
    Nothing,
    /// The item has met an `if`, so a `then` that ends its line opens the
    /// first block of the conditional.
    Then,
    /// The item has met an `effect` whose clauses no line has opened yet, so
    /// a line that starts with `handle` continues it.
    Handle,
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
    /// The form whose next word the item waits for.
    awaits: Awaits,
}

impl Head
{
    /// The head of an item whose first token is of `lexeme` and spelled
    /// `spelled`, in a block whose items `sep` ends.
    ///
    /// # Specification
    /// trivial.
    fn begun(
        lexeme: Lexeme,
        spelled: &[u8],
        sep: Sep,
    ) -> Self
    {
        Self {
            lead: if lexeme == Lexeme::ArmBar {
                Lead::Bar
            }
            else if lexeme != Lexeme::LowerWord {
                Lead::Other
            }
            else if sep == Sep::Top
                && DECLARATION_LEADS
                    .iter()
                    .any(|word| word.as_bytes() == spelled)
            {
                Lead::Keyword
            }
            else {
                Lead::Word
            },
            ..Self::default()
        }
    }
}

/// Whether the close of a block, an explicit `}` or a virtual one, ends the
/// item that the block stands in.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Ending
{
    /// It ends the item, as the `}` of a brace body after a head does.
    #[default]
    Ends,
    /// It continues the item, as the `}` of a block expression after `=`
    /// does, and the close of a block after a `do`.
    Continues,
}

/// What the items of an explicit `{` are.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Holds
{
    /// Statements, or the items that the frame's separator names.
    #[default]
    Statements,
    /// The fields of a `glob` block or of a `Cap` block. No statement's `=`
    /// opens a block in it.
    Fields,
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
    /// Whether its close ends the item that the block stands in.
    ending: Ending,
    /// What its items are, when it is an explicit `{`.
    holds: Holds,
    /// The `def` whose `=` opens the block, if one does.
    defines: Option<Body>,
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
            ending: Ending::Ends,
            holds: Holds::Statements,
            defines: None,
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
    /// The `=` of a `let`, a `var` or an assignment in a statement block, at
    /// its index in the stream. It keeps its tile, and its block opens after
    /// it.
    Statement
    {
        /// The `=`'s index.
        at: usize,
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// The `=` of a `def`, at its index in the stream. It keeps its tile, and
    /// its block opens after it.
    Definition
    {
        /// The `=`'s index.
        at: usize,
        /// The indentation of the opener's line.
        indent: u32,
        /// The `def` whose `=` it is.
        body: Body,
    },
    /// The `=>` of an arm or of a clause, or an `else`. It keeps its tile, and
    /// its block opens after it.
    Kept
    {
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `handle` that ends its line, after the body of an `effect`. It keeps
    /// its tile, and the clauses open after it, with no separator, as arms do.
    Clauses
    {
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `where` that opens a declaration body, or the declarations of a
    /// `rec` block.
    Members
    {
        /// The indentation of the opener's line.
        indent: u32,
        /// What ends the items of the block it opens.
        sep: Sep,
    },
    /// A `match` whose arms may open at the next line at its depth. A
    /// `where` at its depth makes it [`Pending::ArmsWhere`].
    Arms
    {
        /// The frame depth the `match` stands at.
        depth: usize,
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `match` head's `where`, at its index in the stream: when it ends its
    /// line, it becomes the arms' open, as a body's `=` becomes the body's.
    ArmsWhere
    {
        /// The `where`'s index.
        at: usize,
        /// The indentation of the opener's line.
        indent: u32,
    },
    /// A `do`, or the `then` of an `if` head, at its index in the stream:
    /// when it ends its line, it becomes the open of a statement block, as a
    /// `match` head's `where` becomes the arms' open.
    Do
    {
        /// The `do`'s index.
        at: usize,
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
    /// A block's virtual close that the pass wrote, with the separator of the
    /// block it closes.
    Closed(Sep),
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
    /// Whether the last significant token, when it is a `}`, ends its item.
    ending: Ending,
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
            Prev::Virtual(lexeme) => matches!(lexeme, Lexeme::LayoutOpen | Lexeme::LayoutSemi),
            // An arm list closes inside an expression, and so does a block
            // that an expression opens, so neither close ends a declaration.
            Prev::Closed(sep) => declaration && sep != Sep::Arms && self.ending == Ending::Ends,
            // A `}` ends a declaration, as a brace body after its head does.
            // It ends no statement: the statement ends at its line end, as
            // after any other token (#8326).
            Prev::Written(lexeme, spelled) => {
                (lexeme == Lexeme::Punct
                    && (matches!(spelled, b";" | b"," | b"{")
                        || (spelled == b"}" && declaration && self.ending == Ending::Ends)))
                    // A string left open: its interior ends nothing.
                    || matches!(
                        lexeme,
                        Lexeme::StringFragment
                            | Lexeme::EscapeSequence
                    )
            },
        };
        let wanted = match frame.sep {
            Sep::Semi => true,
            Sep::Decl => item.lead == Lead::Word && item.more,
            Sep::Top => item.defined || (item.lead == Lead::Keyword && item.more),
            Sep::Arms => false,
        };
        Unended(wanted && item.lead != Lead::Bar && !ended)
    }

    /// Close the layout block `frame` is: the last item of a block of
    /// declarations takes its `;` first.
    ///
    /// # Specification
    /// trivial.
    fn close(
        &mut self,
        frame: &Frame,
    )
    {
        if matches!(frame.sep, Sep::Decl | Sep::Top) && bool::from(self.unended(frame)) {
            self.place(Lexeme::LayoutSemi);
        }
        self.shut(frame.sep, frame.ending);
    }

    /// Write the virtual close of a layout block whose items `sep` ends, and
    /// whose close `ending` reads as a `}` of a brace does.
    ///
    /// # Specification
    /// trivial.
    fn shut(
        &mut self,
        sep: Sep,
        ending: Ending,
    )
    {
        self.place(Lexeme::LayoutClose);
        self.prev = Prev::Closed(sep);
        self.ending = ending;
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
///   that opens a body, a `where` that opens arms and a `do` that opens a block
///   are relabeled [`Lexeme::LayoutOpen`]; every other added token is a
///   zero-width [`Lexeme::LayoutOpen`], [`Lexeme::LayoutSemi`] or
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
/// # Cost
/// - allocation: the stack of open blocks, growth within the source's nesting
///   depth
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
/// - witness: `label::layout::tests::a_statement_s_line_final_equals_opens_a_block_after_it`
/// - witness: `label::layout::tests::an_arm_s_line_final_arrow_opens_a_block_after_it`
/// - witness: `label::layout::tests::a_line_final_do_opens_a_statement_block`
/// - witness: `label::layout::tests::a_def_s_line_final_equals_opens_a_block_with_or_with_no_arrow`
/// - witness: `label::layout::tests::a_then_and_an_else_open_the_blocks_of_a_conditional`
/// - witness: `label::layout::tests::an_effect_s_do_and_a_line_final_handle_open_a_handler`
/// - witness: `label::layout::tests::a_where_opens_the_arms_of_an_offer_and_the_declarations_of_a_rec`
/// - witness: `label::layout::tests::a_word_at_column_zero_ends_the_declaration_before_it`
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
        ending: Ending::Ends,
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
        let punct = matches!(token.lexeme, Lexeme::Punct);
        // A token inside a line that is no bracket, no punctuation and no
        // opener's keyword, met while no opener waits, only extends the item.
        // Each such keyword is two to six bytes long.
        if !line_start
            && !punct
            && (token.lexeme != Lexeme::LowerWord
                || !matches!(token.end.saturating_sub(token.start), 2 ..= 6))
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
        // A layout word right after a `.` is a member's name: `Flow.then`.
        let token = if token.lexeme == Lexeme::LowerWord
            && matches!(spelled, b"do" | b"then")
            && before_arrow == b"."
            && token.start == plan.end
        {
            let member = Token {
                lexeme: Lexeme::MemberWord,
                ..token
            };
            if let Some(written) = tokens.get_mut(index) {
                *written = member;
            }
            member
        }
        else {
            token
        };
        let nesting = bracket(token, bytes);
        let closer = nesting == Bracket::Close;
        let brace = token.lexeme == Lexeme::Punct && spelled == b"{";
        let members = if let Pending::Members { sep, .. } = pending {
            Some(sep)
        }
        else {
            None
        };
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
            Pending::Members { indent, .. }
            | Pending::Arms { indent, .. }
            | Pending::ArmsWhere { indent, .. }
            | Pending::Do { indent, .. } => Some(Column(indent)),
            Pending::Statement { .. }
            | Pending::Definition { .. }
            | Pending::Kept { .. }
            | Pending::Clauses { .. }
            | Pending::None => None,
        };
        let below = step
            .and(waiting)
            .and_then(|indent| {
                block_column(bytes, tokens.get(index ..).unwrap_or_default(), indent)
            })
            .map(u32::from);
        // A block that an expression opens, after a statement's `=`, an arm's
        // `=>` or a `do`, continues the item its close stands in, as a `{`
        // right after `=` does.
        let mut open = |frames: &mut Vec<Frame>,
                        plan: &mut Plan<'_>,
                        indent: u32,
                        sep: Sep,
                        ending: Ending| {
            if column > indent {
                frames.push(Frame {
                    ending,
                    ..Frame::new(Kind::Layout { column }, sep)
                });
                opened = true;
            }
            // A moved line at or left of its opener's line, whose move closes
            // nothing, is the block's first line, at the least column of the
            // lines the block holds after it.
            else if let Some(Move { closes: 0, .. }) = step
                && let Some(below) = below
            {
                frames.push(Frame {
                    ending,
                    ..Frame::new(Kind::Layout { column: below }, sep)
                });
                opened = true;
            }
            else {
                plan.shut(sep, ending);
                // The block's close is the first close the move counts.
                if let Some(Move { ref mut closes, .. }) = step {
                    *closes = closes.saturating_sub(1);
                }
            }
        };
        match pending {
            Pending::Statement { at, indent } => {
                pending = Pending::None;
                if line_start
                    && !brace
                    && column > indent
                    && !bool::from(names_no_expression(bytes, tokens, at))
                {
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Semi, Ending::Continues);
                }
            },
            Pending::Definition { at, indent, body } => {
                pending = Pending::None;
                if line_start
                    && !brace
                    && column > indent
                    && !bool::from(names_no_expression(bytes, tokens, at))
                {
                    let depth = frames.len();
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Semi, Ending::Continues);
                    if frames.len() > depth
                        && let Some(frame) = frames.last_mut()
                    {
                        frame.defines = Some(body);
                    }
                }
            },
            Pending::Kept { indent } => {
                pending = Pending::None;
                if line_start && !brace && column > indent {
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Semi, Ending::Continues);
                }
            },
            Pending::Clauses { indent } => {
                pending = Pending::None;
                if line_start && !brace && column > indent {
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Arms, Ending::Ends);
                }
            },
            Pending::Members { indent, sep } => {
                pending = Pending::None;
                if line_start && !brace {
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, sep, Ending::Ends);
                }
            },
            Pending::Arms { depth, indent } => {
                if line_start && frames.len() == depth && !brace {
                    pending = Pending::None;
                    plan.place(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Arms, Ending::Ends);
                }
            },
            Pending::ArmsWhere { at, indent } => {
                pending = Pending::None;
                if line_start {
                    if let Some(word) = tokens.get_mut(at) {
                        word.lexeme = Lexeme::LayoutOpen;
                    }
                    plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Arms, Ending::Ends);
                }
            },
            Pending::Do { at, indent } => {
                pending = Pending::None;
                if line_start {
                    if let Some(word) = tokens.get_mut(at) {
                        word.lexeme = Lexeme::LayoutOpen;
                    }
                    plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                    open(&mut frames, &mut plan, indent, Sep::Semi, Ending::Continues);
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
            // A line that starts with `else`, or with the `handle` of an
            // `effect` above it, continues the form above it: it ends no item
            // and begins none.
            if let Some(&frame) = frames.last()
                && match frame.kind {
                    Kind::Layout { column: block } => block == column || stays,
                    Kind::Brace {
                        column: Some(block),
                    } => block == column,
                    Kind::Brace { column: None } | Kind::Plain => false,
                }
                && !closer
                && !(token.lexeme == Lexeme::LowerWord
                    && (spelled == b"else"
                        || (spelled == b"handle" && frame.head.awaits == Awaits::Handle)))
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
                frame.head = Head::begun(token.lexeme, spelled, frame.sep);
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
        // virtual brace when the block stays open. A stray closer that closes
        // the block a top-level `def`'s `=` opened ends the `def` there, as
        // the end of the source does, so the `def` takes its `;` before it.
        let mut ending = Ending::Ends;
        if closer
            && (spelled != b")"
                || frames
                    .iter()
                    .skip(1)
                    .any(|frame| !matches!(frame.kind, Kind::Layout { .. })))
        {
            let mut defined = false;
            while frames.len() > 1
                && let Some(&frame) = frames.last()
                && matches!(frame.kind, Kind::Layout { .. })
            {
                plan.close(&frame);
                frames.pop();
                defined = frame.defines.is_some() && frames.len() == 1;
            }
            if defined
                && let Some(base) = frames.first()
                && bool::from(plan.unended(base))
            {
                plan.place(Lexeme::LayoutSemi);
            }
            if frames.len() > 1
                && let Some(frame) = frames.pop()
            {
                ending = frame.ending;
                if matches!(frame.sep, Sep::Decl | Sep::Top) && bool::from(plan.unended(&frame)) {
                    plan.place(Lexeme::LayoutSemi);
                }
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
            // A `{` after `glob` or `Cap` holds fields, as a bracket does.
            let fields = brace
                && plan
                    .after
                    .checked_sub(1)
                    .and_then(|last| tokens.get(last))
                    .is_some_and(|last| matches!(text(last), b"glob" | b"Cap"));
            frames.push(if brace {
                Frame {
                    // A `{` right after `=` opens a block expression, and
                    // its `}` does not end the item.
                    ending: if before_arrow == b"=" {
                        Ending::Continues
                    }
                    else {
                        Ending::Ends
                    },
                    holds: if fields {
                        Holds::Fields
                    }
                    else {
                        Holds::Statements
                    },
                    // A `{` after a declaration's `where` opens a declaration
                    // body. A `{` after `rec`, or after the `where` of `rec`,
                    // holds declarations as the source does, so a `def` in it
                    // takes its `;`.
                    ..Frame::new(
                        Kind::Brace { column: None },
                        members.unwrap_or(if before_arrow == b"rec" {
                            Sep::Top
                        }
                        else {
                            Sep::Semi
                        }),
                    )
                }
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
                // An `offer` opens its arms as a `match` does.
                b"match" | b"offer" => {
                    pending = Pending::Arms {
                        depth: frames.len(),
                        indent: line_indent,
                    };
                },
                // The `where` of a match head opens its arms, not a
                // declaration body. The `where` of `rec` opens declarations
                // that end as the source's do.
                b"where" => {
                    pending = match pending {
                        Pending::Arms { depth, indent } if depth == frames.len() => {
                            Pending::ArmsWhere { at: index, indent }
                        },
                        Pending::None
                        | Pending::Members { .. }
                        | Pending::Arms { .. }
                        | Pending::Statement { .. }
                        | Pending::Definition { .. }
                        | Pending::Kept { .. }
                        | Pending::Clauses { .. }
                        | Pending::ArmsWhere { .. }
                        | Pending::Do { .. } => Pending::Members {
                            indent: line_indent,
                            sep: if before_arrow == b"rec" {
                                Sep::Top
                            }
                            else {
                                Sep::Decl
                            },
                        },
                    };
                },
                // A `do` that ends its line opens a statement block, and so
                // does the `then` of an `if` head. Either word inside a line
                // stays a word, which no form reads.
                b"do" => {
                    pending = Pending::Do {
                        at: index,
                        indent: line_indent,
                    };
                },
                b"if" => {
                    if let Some(frame) = frames.last_mut() {
                        frame.head.awaits = Awaits::Then;
                    }
                },
                b"then" => {
                    if frames
                        .last()
                        .is_some_and(|frame| frame.head.awaits == Awaits::Then)
                    {
                        pending = Pending::Do {
                            at: index,
                            indent: line_indent,
                        };
                    }
                },
                // An `else` keeps its tile. Its block opens after it, when
                // the `else` ends its line.
                b"else" if pending == Pending::None => {
                    pending = Pending::Kept {
                        indent: line_indent,
                    };
                },
                b"effect" => {
                    if let Some(frame) = frames.last_mut() {
                        frame.head.awaits = Awaits::Handle;
                    }
                },
                // A `handle` keeps its tile. The clauses open after it, when
                // the `handle` ends its line.
                b"handle" => {
                    if let Some(frame) = frames.last_mut() {
                        frame.head.awaits = Awaits::Nothing;
                    }
                    if pending == Pending::None {
                        pending = Pending::Clauses {
                            indent: line_indent,
                        };
                    }
                },
                _ => {},
            }
        }
        else if token.lexeme == Lexeme::Punct {
            match spelled {
                // A result arrow after a `def`'s parameters: `->`, or the
                // linear arrow `⊸` or its ASCII spelling `-o`.
                b"->" | b"-o" | b"\xE2\x8A\xB8" => {
                    if let Some(frame) = frames.last_mut()
                        && frame.head.opener == Opener::Def
                        && matches!(before_arrow, b")" | b"]")
                    {
                        frame.head.opener = Opener::Function;
                    }
                },
                b"=" => {
                    if let Some(frame) = frames.last_mut() {
                        // A `def`'s `=` keeps its tile, with a result arrow
                        // or with none. Its block opens after it, when the
                        // `=` ends its line.
                        if matches!(frame.head.opener, Opener::Def | Opener::Function)
                            && opener_allowed
                            && pending == Pending::None
                        {
                            pending = Pending::Definition {
                                at: index,
                                indent: line_indent,
                                body: if frame.head.opener == Opener::Function {
                                    Body::Function
                                }
                                else {
                                    Body::Value
                                },
                            };
                        }
                        // A statement's `=` keeps its tile. Its block opens
                        // after it, when the `=` ends its line.
                        else if frame.sep == Sep::Semi
                            && frame.holds == Holds::Statements
                            && !frame.head.defined
                            && opener_allowed
                            && pending == Pending::None
                        {
                            pending = Pending::Statement {
                                at: index,
                                indent: line_indent,
                            };
                        }
                        frame.head.opener = Opener::None;
                    }
                },
                // The `=>` of an arm or of a clause keeps its tile. Its block
                // opens after it, when the `=>` ends its line.
                b"=>" => {
                    if let Some(frame) = frames.last()
                        && frame.head.lead == Lead::Bar
                        && frame.holds == Holds::Statements
                        && opener_allowed
                        && pending == Pending::None
                    {
                        pending = Pending::Kept {
                            indent: line_indent,
                        };
                    }
                },
                b";" | b"," => {
                    // A `;` ends the item, and the next token begins the
                    // next. A `,` separates within an item: a clause's
                    // patterns, a call's arguments.
                    restart = spelled == b";";
                    // A `;` that ends the last line of the block of a `def`
                    // with no result arrow ends the `def`, as it does after a
                    // `=` that opens nothing: the block closes before it.
                    if restart
                        && let Some(&frame) = frames.last()
                        && frame.defines == Some(Body::Value)
                        && let Kind::Layout { column: block } = frame.kind
                        && bool::from(ends_its_block(bytes, tokens, index, block))
                    {
                        plan.close(&frame);
                        frames.pop();
                    }
                    // An arm list takes no separator, so a `;` in a layout arm
                    // list belongs to the block around it: each arm list that
                    // is innermost closes before the `;`. A brace or a bracket
                    // keeps its `;`.
                    while restart
                        && frames.len() > 1
                        && let Some(&frame) = frames.last()
                        && frame.sep == Sep::Arms
                        && matches!(frame.kind, Kind::Layout { .. })
                    {
                        plan.close(&frame);
                        frames.pop();
                    }
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
        plan.ending = ending;
        plan.after = index.saturating_add(1);
        plan.end = token.end;
        before_arrow = spelled;
    }
    // A reset settles a waiting opener as any line at column zero does: no
    // block opens left of its opener's line, so the block closes at once.
    if next == Next::Reset {
        match pending {
            Pending::Do { at, .. } => {
                if let Some(opener) = tokens.get_mut(at) {
                    opener.lexeme = Lexeme::LayoutOpen;
                }
                plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                plan.shut(Sep::Semi, Ending::Continues);
            },
            Pending::ArmsWhere { at, .. } => {
                if let Some(opener) = tokens.get_mut(at) {
                    opener.lexeme = Lexeme::LayoutOpen;
                }
                plan.prev = Prev::Virtual(Lexeme::LayoutOpen);
                plan.shut(Sep::Arms, Ending::Ends);
            },
            Pending::Members { sep, .. } => {
                plan.place(Lexeme::LayoutOpen);
                plan.shut(sep, Ending::Ends);
            },
            Pending::Arms { depth, .. } if frames.len() == depth => {
                plan.place(Lexeme::LayoutOpen);
                plan.shut(Sep::Arms, Ending::Ends);
            },
            Pending::Arms { .. }
            | Pending::Statement { .. }
            | Pending::Definition { .. }
            | Pending::Kept { .. }
            | Pending::Clauses { .. }
            | Pending::None => {},
        }
    }
    // What follows closes every block. The end of the source ends no
    // top-level item, so a source cut short stays open where it stops, for
    // the closings and the continuations an editor reads there. A reset ends
    // the item before it as the column rule does. The one exception is the
    // block a top-level `def`'s `=` opens: the end of the source closes it as
    // a line at column zero would, and the `def` takes its `;`, as a `def`
    // whose body follows its `=` on one line does.
    let mut defined = false;
    while frames.len() > 1
        && let Some(frame) = frames.pop()
    {
        if matches!(frame.kind, Kind::Layout { .. }) {
            plan.close(&frame);
            defined = frame.defines.is_some() && frames.len() == 1;
        }
    }
    if (next == Next::Reset || defined)
        && !after_attribute
        && let Some(base) = frames.first()
        && bool::from(plan.unended(base))
    {
        plan.place(Lexeme::LayoutSemi);
    }
    insert(tokens, &plan.planned);
}

primitive_copy_wrapper!(
    /// Whether the right side of a `=` is no expression.
    struct Unopened(bool);
);

/// Whether the `=` at `at` stands after the name of a `type`, a `sort`, a
/// `module` or a `face`. Its right side is no expression, so no block opens
/// after it, and the line to its right continues it.
///
/// # Specification
/// trivial.
fn names_no_expression(
    bytes: SourceBytes<'_>,
    tokens: &[Token],
    at: usize,
) -> Unopened
{
    let mut before = tokens
        .get(.. at)
        .unwrap_or_default()
        .iter()
        .rev()
        .filter(|token| token.lexeme != Lexeme::Space);
    let _name = before.next();
    Unopened(before.next().is_some_and(|word| {
        word.lexeme == Lexeme::LowerWord
            && matches!(
                bytes.0.get(
                    usize::try_from(word.start).unwrap_or(usize::MAX)
                        .. usize::try_from(word.end).unwrap_or(usize::MAX),
                ),
                Some(b"type" | b"sort" | b"module" | b"face")
            )
    }))
}

primitive_copy_wrapper!(
    /// Whether a token ends the last line of its block.
    struct EndsBlock(bool);
);

/// Whether the token at `at` is the last of its line, and the next line
/// stands left of `column`, so the column rule closes the block whose items
/// stand at `column` before that line. With no token after `at`, what follows
/// the run closes every block.
///
/// # Specification
/// trivial.
fn ends_its_block(
    bytes: SourceBytes<'_>,
    tokens: &[Token],
    at: usize,
    column: u32,
) -> EndsBlock
{
    let Some(token) = tokens.get(at)
    else {
        return EndsBlock(false);
    };
    let Some(next) = tokens
        .get(at.saturating_add(1) ..)
        .unwrap_or_default()
        .iter()
        .find(|token| token.lexeme != Lexeme::Space)
    else {
        return EndsBlock(true);
    };
    let gap = bytes
        .0
        .get(
            usize::try_from(token.end).unwrap_or(usize::MAX)
                .. usize::try_from(next.start).unwrap_or(usize::MAX),
        )
        .unwrap_or_default();
    EndsBlock(
        gap.iter()
            .rposition(|&byte| byte == b'\n')
            .is_some_and(|newline| {
                u32::try_from(gap.len().saturating_sub(newline).saturating_sub(1))
                    .is_ok_and(|indent| indent < column)
            }),
    )
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
            (
                Lexeme::LowerWord,
                b"where" | b"match" | b"do" | b"then" | b"else" | b"handle"
            ) | (Lexeme::Punct, b"=" | b"," | b"->" | b"=>" | b":")
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
    fn a_semicolon_closes_the_layout_arm_lists_before_it_1057()
    {
        // The `;` on the last arm's line is the definition's, so the arm list
        // closes before it, inside a `rec` block too.
        assert_eq!(
            marked("def f(x : A) = match x where\n  | a => x\n  | b => x ;\ndef g : A = x;\n"),
            "def f(x : A) = match x ⟪where→{⟫\n  | a => x\n  | b => x⟪}⟫ ;\ndef g : A = x;\n"
        );
        assert_eq!(
            marked(
                "rec {\n  def f(x : A) = match x where\n    | a => x\n    | b => x ;\n  def g : A = x;\n}\n"
            ),
            "rec {\n  def f(x : A) = match x ⟪where→{⟫\n    | a => x\n    | b => x⟪}⟫ ;\n  def g : A = x;\n}\n"
        );
        // Two arm lists that end on one line both close before the `;`.
        assert_eq!(
            marked(
                "def f(x : A) = match x where\n  | a => match y where\n    | c => x ;\ndef g : A = x;\n"
            ),
            "def f(x : A) = match x ⟪where→{⟫\n  | a => match y ⟪where→{⟫\n    | c => x⟪}⟫⟪}⟫ ;\ndef g : A = x;\n"
        );
        // An arm list in braces keeps its `;`, and so does a bracket of an
        // arm.
        assert_eq!(
            marked("def f(x : A) = match x {\n  | a => x ;\n}\n"),
            "def f(x : A) = match x {\n  | a => x ;\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) = match x where\n  | a => g(x ; y)\ndef g : A = x;\n"),
            "def f(x : A) = match x ⟪where→{⟫\n  | a => g(x ; y)⟪}⟫⟪;⟫\ndef g : A = x;\n"
        );
    }

    #[test]
    fn a_line_final_opener_opens_a_block_at_the_next_column()
    {
        // A body's `=` keeps its tile, and the block opens after it.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n  y\n"),
            "def f(x : A) -> A =⟪{⟫\n  let y = x⟪;⟫\n  y⟪}⟫⟪;⟫\n"
        );
        // A `=` with its body on its own line opens nothing.
        assert_eq!(
            marked("def f(x : A) -> A = x;\n"),
            "def f(x : A) -> A = x;\n"
        );
        // The `where` ending a `match` head is the arms' brace: the arms take
        // no separator, after an answer type too.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x where\n    | a => a\n    | b => b\n}\n"),
            "def f(x : A) -> A {\n  match x ⟪where→{⟫\n    | a => a\n    | b => b⟪}⟫\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x -> A where\n    | a => a\n}\n"),
            "def f(x : A) -> A {\n  match x -> A ⟪where→{⟫\n    | a => a⟪}⟫\n}\n"
        );
        // A line no further right than the head's closes its arms at once.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x where\ndef g(x : A) -> A = x;\n"),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫⟪}⟫⟪}⟫⟪;⟫\ndef g(x : A) -> A = x;\n"
        );
        // A bare `match` head ending its line opens its arms too, so the parse
        // stays whole and the lowering refuses the head by name.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x\n    | a => a\n}\n"),
            "def f(x : A) -> A {\n  match x⟪{⟫\n    | a => a⟪}⟫\n}\n"
        );
        // A `match` whose head takes its brace opens nothing, and a `where`
        // that does not end the head's line stays a word, no part of the
        // match.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x {\n    | a => a\n  }\n}\n"),
            "def f(x : A) -> A {\n  match x {\n    | a => a\n  }\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x where {\n    | a => a\n  }\n}\n"),
            "def f(x : A) -> A {\n  match x where {\n    | a => a\n  }\n}\n"
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
            "def f(x : A) -> A =⟪;⟫\ndef g(x : A) -> A = x;\n"
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
        // A statement that ends in a brace ends at its line end, as any other
        // does (#8326); a continuation indented past the column continues
        // it; a comment after a statement stays outside the separator.
        assert_eq!(
            marked("def f(x : A) -> A {\n  if x { a } else { b }\n  g x\n    y // c\n  z\n}\n"),
            "def f(x : A) -> A {\n  if x { a } else { b }⟪;⟫\n  g x\n    y⟪;⟫ // c\n  z\n}\n"
        );
        // A line-leading bar and a closer take no separator; a sigil's brace
        // is no statement block.
        assert_eq!(
            marked("data D {\n  | a\n  | b\n}\ndef r() -> R { *{\n  x = 1\n  y = 2\n} }\n"),
            "data D {\n  | a\n  | b\n}\ndef r() -> R { *{\n  x = 1\n  y = 2\n} }\n"
        );
    }

    #[test]
    fn a_line_that_ends_in_a_brace_ends_its_statement_8326()
    {
        // #8326: the `}` of a product, of a `match` that a `let` binds and of
        // a `fork` block ends no statement, so the line end writes its
        // separator, in a layout block and in braces.
        assert_eq!(
            marked("def f() -> A =\n  let *{b, n} = *{true, 2}\n  n\n"),
            "def f() -> A =⟪{⟫\n  let *{b, n} = *{true, 2}⟪;⟫\n  n⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            marked("def f() -> A {\n  let p = *{true, 2}\n  p\n}\n"),
            "def f() -> A {\n  let p = *{true, 2}⟪;⟫\n  p\n}\n"
        );
        assert_eq!(
            marked("def f(b : B) -> A =\n  let n = match b { | t => 1 | f => 2 }\n  n\n"),
            "def f(b : B) -> A =⟪{⟫\n  let n = match b { | t => 1 | f => 2 }⟪;⟫\n  n⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            marked("def f() -> A =\n  let h = fork (t : S) {\n    close t\n  }\n  recv h\n"),
            "def f() -> A =⟪{⟫\n  let h = fork (t : S) {\n    close t\n  }⟪;⟫\n  recv h⟪}⟫⟪;⟫\n"
        );
        // A `loop` that its own brace closes takes the separator too, and a
        // `}` before the block's close takes none.
        assert_eq!(
            marked("def f() -> A {\n  loop { break }\n  return 1\n}\n"),
            "def f() -> A {\n  loop { break }⟪;⟫\n  return 1\n}\n"
        );
    }

    #[test]
    fn a_statement_s_line_final_equals_opens_a_block_after_it()
    {
        // The `=` of a `let` keeps its tile, and the block opens after it. The
        // block's close ends no statement, so the line end writes the `let`'s
        // separator.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let a =\n    let b = x\n    b\n  a\n"),
            "def f(x : A) -> A =⟪{⟫\n  let a =⟪{⟫\n    let b = x⟪;⟫\n    b⟪}⟫⟪;⟫\n  a⟪}⟫⟪;⟫\n"
        );
        // A `var` and an assignment open in the same way, in braces too.
        assert_eq!(
            marked("def f(x : A) -> A {\n  var n : A =\n    g x\n  n =\n    h n\n  n\n}\n"),
            "def f(x : A) -> A {\n  var n : A =⟪{⟫\n    g x⟪}⟫⟪;⟫\n  n =⟪{⟫\n    h n⟪}⟫⟪;⟫\n  n\n}\n"
        );
        // A line at the statement's column or left of it opens nothing.
        assert_eq!(
            marked("def f(x : A) -> A {\n  let a =\n  x\n}\n"),
            "def f(x : A) -> A {\n  let a =⟪;⟫\n  x\n}\n"
        );
        // A `=` that does not end its line opens nothing, and the line to its
        // right continues the statement.
        assert_eq!(
            marked("def f(x : A) -> A {\n  let a = g\n    x\n  a\n}\n"),
            "def f(x : A) -> A {\n  let a = g\n    x⟪;⟫\n  a\n}\n"
        );
        // The `=` after the name of a `module` or of a `sort` opens nothing.
        assert_eq!(
            marked("def f(x : A) -> A {\n  module m =\n    M\n  x\n}\n"),
            "def f(x : A) -> A {\n  module m =\n    M⟪;⟫\n  x\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  handle c : S.Eff with sort T =\n    A { x }\n}\n"),
            "def f(x : A) -> A {\n  handle c : S.Eff with sort T =\n    A { x }\n}\n"
        );
        // No `=` opens inside a bracket, in a `glob` block or before a line
        // that starts with an explicit `{`.
        assert_eq!(
            marked("def f(x : A) -> A {\n  let a = *{ b =\n    x }\n  a\n}\n"),
            "def f(x : A) -> A {\n  let a = *{ b =\n    x }⟪;⟫\n  a\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  glob {\n    cells =\n      A\n  }\n}\n"),
            "def f(x : A) -> A {\n  glob {\n    cells =\n      A\n  }\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  let a =\n    { x }\n  a\n}\n"),
            "def f(x : A) -> A {\n  let a =\n    { x }⟪;⟫\n  a\n}\n"
        );
    }

    #[test]
    fn an_arm_s_line_final_arrow_opens_a_block_after_it()
    {
        // The `=>` of an arm keeps its tile, and the block opens after it. The
        // next arm's bar at the column of the arms closes the block and takes
        // no separator.
        assert_eq!(
            marked(
                "def f(x : A) -> A =\n  match x where\n    | a =>\n      let y = x\n      y\n    | b => x\n"
            ),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n    | a =>⟪{⟫\n      let y = x⟪;⟫\n      y⟪}⟫\n    | b => x⟪}⟫⟪}⟫⟪;⟫\n"
        );
        // An arm in braces opens in the same way, and so does a clause of a
        // handler.
        assert_eq!(
            marked(
                "def f(x : A) -> A {\n  match x {\n    | a =>\n      let y = x\n      y\n    | b => x\n  }\n}\n"
            ),
            "def f(x : A) -> A {\n  match x {\n    | a =>⟪{⟫\n      let y = x⟪;⟫\n      y⟪}⟫\n    | b => x\n  }\n}\n"
        );
        assert_eq!(
            marked(
                "def f() -> A {\n  handle c : S.Eff { c.get } with {\n    | oper get(k) =>\n      let y = g\n      k y\n  }\n}\n"
            ),
            "def f() -> A {\n  handle c : S.Eff { c.get } with {\n    | oper get(k) =>⟪{⟫\n      let y = g⟪;⟫\n      k y⟪}⟫\n  }\n}\n"
        );
        // The last arm's block closes with the arms, and the statement that
        // binds the match takes its separator.
        assert_eq!(
            marked(
                "def f(x : A) -> A {\n  let n = match x where\n    | a =>\n      let y = x\n      y\n  n\n}\n"
            ),
            "def f(x : A) -> A {\n  let n = match x ⟪where→{⟫\n    | a =>⟪{⟫\n      let y = x⟪;⟫\n      y⟪}⟫⟪}⟫⟪;⟫\n  n\n}\n"
        );
        // A line at the arm's column opens nothing, nor a line that starts
        // with an explicit `{`, nor a `=>` inside a bracket.
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x {\n    | a =>\n    | b => x\n  }\n}\n"),
            "def f(x : A) -> A {\n  match x {\n    | a =>\n    | b => x\n  }\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  match x {\n    | a =>\n      { x }\n  }\n}\n"),
            "def f(x : A) -> A {\n  match x {\n    | a =>\n      { x }\n  }\n}\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  &{ .get =>\n    x }\n}\n"),
            "def f(x : A) -> A {\n  &{ .get =>\n    x }\n}\n"
        );
    }

    #[test]
    fn a_where_opens_the_arms_of_an_offer_and_the_declarations_of_a_rec()
    {
        // The `where` ending an `offer` head is the arms' brace, as after a
        // `match` head, and a bare `offer` head opens its arms with an open
        // of no width, which the lowering refuses.
        assert_eq!(
            marked("def f() -> A {\n  offer c where\n    | l => x\n    | r => y\n}\n"),
            "def f() -> A {\n  offer c ⟪where→{⟫\n    | l => x\n    | r => y⟪}⟫\n}\n"
        );
        assert_eq!(
            marked("def f() -> A {\n  offer c\n    | l => x\n}\n"),
            "def f() -> A {\n  offer c⟪{⟫\n    | l => x⟪}⟫\n}\n"
        );
        // The `where` of `rec` keeps its tile, and its block holds
        // declarations that end as the source's do, the last one before the
        // block's close.
        assert_eq!(
            marked(
                "rec where\n  def f(x : A) -> A = g x\n  def g(x : A) -> A = f x\ndef h : A = x;\n"
            ),
            "rec where⟪{⟫\n  def f(x : A) -> A = g x⟪;⟫\n  def g(x : A) -> A = f x⟪;⟫⟪}⟫\ndef h : A = x;\n"
        );
        assert_eq!(
            marked("rec where {\n  def f(x : A) -> A = g x\n  def g(x : A) -> A = f x\n}\n"),
            "rec where {\n  def f(x : A) -> A = g x⟪;⟫\n  def g(x : A) -> A = f x⟪;⟫\n}\n"
        );
    }

    #[test]
    fn a_line_final_do_opens_a_statement_block()
    {
        // A line-final `do` is the block's brace, after each head that ends
        // in an expression or in a group. The block's close ends no
        // statement, so the line end writes the separator of the statement
        // that holds it.
        assert_eq!(
            marked(
                "def f(n : Integer) -> Integer {\n  while n > 0 do\n    let m = n\n    g m\n  n\n}\n"
            ),
            "def f(n : Integer) -> Integer {\n  while n > 0 ⟪do→{⟫\n    let m = n⟪;⟫\n    g m⟪}⟫⟪;⟫\n  n\n}\n"
        );
        assert_eq!(
            marked(
                "def f() -> A =\n  let desk = fork (seat : S) do\n    send seat x\n    close seat\n  recv desk\n"
            ),
            "def f() -> A =⟪{⟫\n  let desk = fork (seat : S) ⟪do→{⟫\n    send seat x⟪;⟫\n    close seat⟪}⟫⟪;⟫\n  recv desk⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            marked(
                "def f() -> A =\n  let g = fun (x : A) do\n    x\n  let t = thunk do\n    g y\n  force t\n"
            ),
            "def f() -> A =⟪{⟫\n  let g = fun (x : A) ⟪do→{⟫\n    x⟪}⟫⟪;⟫\n  let t = thunk ⟪do→{⟫\n    g y⟪}⟫⟪;⟫\n  force t⟪}⟫⟪;⟫\n"
        );
        // The close of the block ends no declaration, so a definition whose
        // value the block ends takes its `;` before the next word at column
        // zero.
        assert_eq!(
            marked("def a = thunk do\n  let m = x\n  return m\n\ndef b = 1;\n"),
            "def a = thunk ⟪do→{⟫\n  let m = x⟪;⟫\n  return m⟪}⟫⟪;⟫\n\ndef b = 1;\n"
        );
        // A line no further right than the head's closes the block at once.
        assert_eq!(
            marked("def f() -> A {\n  loop do\n  x\n}\n"),
            "def f() -> A {\n  loop ⟪do→{⟫⟪}⟫⟪;⟫\n  x\n}\n"
        );
        // A `do` inside a line, or inside a bracket, stays a word.
        assert_eq!(
            marked("def f(n : Integer) -> Integer {\n  while n > 0 do g n\n  n\n}\n"),
            "def f(n : Integer) -> Integer {\n  while n > 0 do g n⟪;⟫\n  n\n}\n"
        );
        assert_eq!(
            marked("def f() -> A {\n  g (thunk do\n    x)\n  y\n}\n"),
            "def f() -> A {\n  g (thunk do\n    x)⟪;⟫\n  y\n}\n"
        );
    }

    #[test]
    fn a_def_s_line_final_equals_opens_a_block_with_or_with_no_arrow()
    {
        // The `=` of a `def` with no result arrow keeps its tile, and the
        // block opens after it. The block's close ends no declaration, so the
        // `def` takes its `;` before the next word at column zero.
        assert_eq!(
            marked("def three : Integer =\n  3\ndef four : Integer = 4;\n"),
            "def three : Integer =⟪{⟫\n  3⟪}⟫⟪;⟫\ndef four : Integer = 4;\n"
        );
        assert_eq!(
            marked("def twice(x : A) =\n  let y = x\n  y\n"),
            "def twice(x : A) =⟪{⟫\n  let y = x⟪;⟫\n  y⟪}⟫⟪;⟫\n"
        );
        // The `=` of a `def` with a result arrow keeps its tile in the same
        // way.
        assert_eq!(
            marked("def f() -> A =\n  x\ndef b = 1;\n"),
            "def f() -> A =⟪{⟫\n  x⟪}⟫⟪;⟫\ndef b = 1;\n"
        );
        // In the block of a `def` with no result arrow, a `;` that ends the
        // block's last line ends the `def`: the block closes before it. A `;`
        // before a line of the block stays in it.
        assert_eq!(marked("def k =\n  1 ;\n"), "def k =⟪{⟫\n  1⟪}⟫ ;\n");
        assert_eq!(
            marked("def k =\n  let a = 1;\n  a;\ndef b = 1;\n"),
            "def k =⟪{⟫\n  let a = 1;\n  a⟪}⟫;\ndef b = 1;\n"
        );
        // In the block of a `def` with a result arrow, that `;` stays in the
        // block, and the `def` takes its own `;` after the block (#7733).
        assert_eq!(
            marked("def f() -> A =\n  g;\ndef b = 1;\n"),
            "def f() -> A =⟪{⟫\n  g;⟪}⟫⟪;⟫\ndef b = 1;\n"
        );
        // A line that starts with a written `{`, and a `=` that does not end
        // its line, open nothing.
        assert_eq!(
            marked("def three : Integer =\n  { 3 };\n"),
            "def three : Integer =\n  { 3 };\n"
        );
        assert_eq!(
            marked("def three : Integer = g\n  3;\n"),
            "def three : Integer = g\n  3;\n"
        );
    }

    #[test]
    fn an_effect_s_do_and_a_line_final_handle_open_a_handler()
    {
        // The `do` of an `effect` head opens the body. A line that starts
        // with `handle` closes the body and continues the handler, and a
        // `handle` that ends its line opens the clauses, which take no
        // separator, as arms do.
        assert_eq!(
            marked(
                "def f() -> Unit =\n  effect r : T do\n    let b = r.alloc 4\n    r.free b\n  handle\n    | pure(x) => pure x\n    | oper free(b, k) => k *{}\n"
            ),
            "def f() -> Unit =⟪{⟫\n  effect r : T ⟪do→{⟫\n    let b = r.alloc 4⟪;⟫\n    r.free b⟪}⟫\n  handle⟪{⟫\n    | pure(x) => pure x\n    | oper free(b, k) => k *{}⟪}⟫⟪}⟫⟪;⟫\n"
        );
        // A handler by name needs no block, and the close of the clauses
        // ends no statement.
        assert_eq!(
            marked("def f() -> Integer =\n  effect st : S.Eff do\n    st.get\n  handle Counting\n"),
            "def f() -> Integer =⟪{⟫\n  effect st : S.Eff ⟪do→{⟫\n    st.get⟪}⟫\n  handle Counting⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            marked(
                "def f() -> Unit =\n  effect r : T do\n    r.free b\n  handle\n    | pure(x) => pure x\n  g\n"
            ),
            "def f() -> Unit =⟪{⟫\n  effect r : T ⟪do→{⟫\n    r.free b⟪}⟫\n  handle⟪{⟫\n    | pure(x) => pure x⟪}⟫⟪;⟫\n  g⟪}⟫⟪;⟫\n"
        );
        // A `handle` at the column of the body is a statement of the body.
        assert_eq!(
            marked(
                "def f() -> Unit =\n  effect r : T do\n    r.free b\n    handle\n      | pure(x) => pure x\n"
            ),
            "def f() -> Unit =⟪{⟫\n  effect r : T ⟪do→{⟫\n    r.free b⟪;⟫\n    handle⟪{⟫\n      | pure(x) => pure x⟪}⟫⟪}⟫⟪}⟫⟪;⟫\n"
        );
    }

    #[test]
    fn a_then_and_an_else_open_the_blocks_of_a_conditional()
    {
        // A line-final `then` of an `if` head is the first block's brace. A
        // line that starts with `else` closes that block and continues the
        // conditional, and an `else` that ends its line opens the last block
        // after it.
        assert_eq!(
            marked("def f(b : Bool) -> Integer =\n  if b then\n    1\n  else\n    2\n"),
            "def f(b : Bool) -> Integer =⟪{⟫\n  if b ⟪then→{⟫\n    1⟪}⟫\n  else⟪{⟫\n    2⟪}⟫⟪}⟫⟪;⟫\n"
        );
        // A chain: `else if c then` opens the block of the second test.
        assert_eq!(
            marked(
                "def f(n : Integer) -> Integer =\n  if n > 1 then\n    2\n  else if n > 0 then\n    1\n  else\n    0\n"
            ),
            "def f(n : Integer) -> Integer =⟪{⟫\n  if n > 1 ⟪then→{⟫\n    2⟪}⟫\n  else if n > 0 ⟪then→{⟫\n    1⟪}⟫\n  else⟪{⟫\n    0⟪}⟫⟪}⟫⟪;⟫\n"
        );
        // The conditional's last close ends no statement, so the line end
        // writes the separator of the statement that holds it.
        assert_eq!(
            marked(
                "def f(b : Bool) -> Integer =\n  let n = if b then\n    1\n  else\n    2\n  n\n"
            ),
            "def f(b : Bool) -> Integer =⟪{⟫\n  let n = if b ⟪then→{⟫\n    1⟪}⟫\n  else⟪{⟫\n    2⟪}⟫⟪;⟫\n  n⟪}⟫⟪;⟫\n"
        );
        // A line that starts with `else` after a block in braces continues
        // the conditional too.
        assert_eq!(
            marked("def f(b : Bool) -> Integer {\n  if b { 1 }\n  else { 2 }\n}\n"),
            "def f(b : Bool) -> Integer {\n  if b { 1 }\n  else { 2 }\n}\n"
        );
        // A `then` inside a line, or after no `if`, stays a word.
        assert_eq!(
            marked("def f(b : Bool) -> Integer =\n  if b then 1 else 2\n"),
            "def f(b : Bool) -> Integer =⟪{⟫\n  if b then 1 else 2⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            marked("def f() -> A =\n  g then\n    x\n"),
            "def f() -> A =⟪{⟫\n  g then\n    x⟪}⟫⟪;⟫\n"
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
        // A line at column zero ends the declaration before it, when a
        // declaration's keyword begins that declaration, as `def` and `oper`
        // do. An attribute and a token that is no word end nothing after them.
        assert_eq!(
            marked(
                "def f(x : A) -> A = x\n@[checks]\ndef g(x : A) -> A = x\noper h : A\n§\nrelease x ;\n"
            ),
            "def f(x : A) -> A = x⟪;⟫\n@[checks]\ndef g(x : A) -> A = x⟪;⟫\noper h : A⟪;⟫\n§\nrelease x ;\n"
        );
        // A `{` right after `=` opens a block expression, whose `}` ends no
        // item: the `def` takes its `;` at the next item, in a source and in a
        // statement block. A brace body after a head ends its item.
        assert_eq!(
            marked("def f(x : A) -> A = { x }\ndef g(x : A) -> A { x }\ndef h(x : A) -> A = x;\n"),
            "def f(x : A) -> A = { x }⟪;⟫\ndef g(x : A) -> A { x }\ndef h(x : A) -> A = x;\n"
        );
        assert_eq!(
            marked("def f(x : A) -> A {\n  let y = { x }\n  y\n}\n"),
            "def f(x : A) -> A {\n  let y = { x }⟪;⟫\n  y\n}\n"
        );
        // The end of the source ends nothing, so a source cut short stays
        // open where it stops.
        assert_eq!(marked("def f(x : A) -> A = x"), "def f(x : A) -> A = x");
    }

    #[test]
    fn a_word_at_column_zero_ends_the_declaration_before_it()
    {
        // An `import`, a `type`, a `module` and a `world` end at the next
        // word at column zero, as a `def` does. The end of the source ends
        // nothing.
        assert_eq!(
            marked(
                "import std.process\nimport std.io (a,\n  b)\ntype T = A\nmodule N = M\nworld w\ndef f(x : T) -> T = x\n"
            ),
            "import std.process⟪;⟫\nimport std.io (a,\n  b)⟪;⟫\ntype T = A⟪;⟫\nmodule N = M⟪;⟫\nworld w⟪;⟫\ndef f(x : T) -> T = x\n"
        );
        // A written `;` takes no second one, and an attribute at column zero
        // ends the declaration before it.
        assert_eq!(
            marked("import std.process;\nimport std.io\n@[checks]\ndef f(x : A) -> A = x;\n"),
            "import std.process;\nimport std.io⟪;⟫\n@[checks]\ndef f(x : A) -> A = x;\n"
        );
        // A `pub` alone on its line marks the declaration after it. A form
        // that no declaration's keyword begins is a stray, whether a name
        // begins it or a reserved word of an expression. None takes a
        // separator.
        assert_eq!(
            marked("pub\ndef f(x : A) -> A = x;\nprint x\nreturn x\ndef g(x : A) -> A = x;\n"),
            "pub\ndef f(x : A) -> A = x;\nprint x\nreturn x\ndef g(x : A) -> A = x;\n"
        );
        // A declaration whose body closes has its end.
        assert_eq!(
            marked("data D : Type where\n  | A : D\ndef f(x : A) -> A { x }\ndef g : A = x;\n"),
            "data D : Type where⟪{⟫\n  | A : D⟪}⟫\ndef f(x : A) -> A { x }\ndef g : A = x;\n"
        );
        // A declaration in a `rec` block ends as a declaration of the source
        // does.
        assert_eq!(
            marked("rec {\n  type T = A\n  def f(x : T) -> T = x\n}\n"),
            "rec {\n  type T = A⟪;⟫\n  def f(x : T) -> T = x⟪;⟫\n}\n"
        );
    }

    #[test]
    fn an_arm_list_or_a_rec_block_leaves_its_definition_its_semicolon_7957()
    {
        // #7957: the virtual close of an arm list ends no declaration, so a
        // `def` whose body after `=` is a `match` takes its `;` after it.
        assert_eq!(
            marked("def f(x : A) = match x where\n  | a => x\n  | b => x\ndef g : A = x;\n"),
            "def f(x : A) = match x ⟪where→{⟫\n  | a => x\n  | b => x⟪}⟫⟪;⟫\ndef g : A = x;\n"
        );
        // #7957: a `rec { … }` block is a declaration body, so its last
        // member takes its `;` before the `}`, as each member before it does.
        assert_eq!(
            marked("rec {\n  def f(x : A) -> A = x\n  def g(x : A) -> A = x\n}\n"),
            "rec {\n  def f(x : A) -> A = x⟪;⟫\n  def g(x : A) -> A = x⟪;⟫\n}\n"
        );
    }

    #[test]
    fn a_word_at_column_zero_closes_every_block()
    {
        // A dedent closes the blocks right of the line, and a word at column
        // zero closes every block, a bracket left open included.
        assert_eq!(
            marked(
                "def f(x : A) -> A =\n  match x where\n    | a => g(a\n  y\ndef h(x : A) -> A = x;\n"
            ),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n    | a => g(a\n  y⟪}⟫⟪}⟫⟪;⟫\ndef h(x : A) -> A = x;\n"
        );
        // The end of the source closes every block, and a top-level `def`
        // whose `=` opened one takes its `;`.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x where\n    | a => a"),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n    | a => a⟪}⟫⟪}⟫⟪;⟫"
        );
    }

    #[test]
    fn a_line_left_of_its_block_stays_when_the_next_line_returns()
    {
        // A dent: the line after it stands at the block's column again, so
        // the dented line is one more item of the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n let z = y\n  z\n"),
            "def f(x : A) -> A =⟪{⟫\n  let y = x⟪;⟫\n let z = y⟪;⟫\n  z⟪}⟫⟪;⟫\n"
        );
        // A line left of a block of two items, with no line after it at the
        // block's column, closes the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x\n  let z = y\n z\ndef g(x : A) -> A = x;\n"),
            "def f(x : A) -> A =⟪{⟫\n  let y = x⟪;⟫\n  let z = y⟪}⟫\n z⟪;⟫\ndef g(x : A) -> A = x;\n"
        );
    }

    #[test]
    fn a_block_moves_left_to_the_column_its_lines_keep()
    {
        // The block's first line stands right of the lines after it, as a
        // deleted `let` leaves it, so the block takes their column.
        assert_eq!(
            marked("def f(x : A) -> A =\n   y = x\n  let z = y\n  z\n"),
            "def f(x : A) -> A =⟪{⟫\n   y = x⟪;⟫\n  let z = y⟪;⟫\n  z⟪}⟫⟪;⟫\n"
        );
        // The block's last line moves it too.
        assert_eq!(
            marked("def f(x : A) -> A =\n   y = x\n  y\n"),
            "def f(x : A) -> A =⟪{⟫\n   y = x⟪;⟫\n  y⟪}⟫⟪;⟫\n"
        );
        // A line one column right of the enclosing block, after a block one
        // column right of the line, is an item whose keyword is gone. The
        // block closes before it.
        assert_eq!(
            marked("def f(x : A) -> A =\n  x\n g(x : A) -> A = x;\n"),
            "def f(x : A) -> A =⟪{⟫\n  x⟪}⟫\n g(x : A) -> A = x;\n"
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
        // before it, and the word at column zero after it ends that item.
        assert_eq!(
            marked("theory S where\n  sort A : Type\n checks ]\ntheory T where\n  sort B : Type\n"),
            "theory S where⟪{⟫\n  sort A : Type⟪;⟫⟪}⟫\n checks ]⟪;⟫\ntheory T where⟪{⟫\n  sort B : Type⟪;⟫⟪}⟫\n"
        );
        // A line at column zero closes every block, though the next line
        // stands at a block's column.
        assert_eq!(
            marked("def f(x : A) -> A =\n  match x where\n    | a => a\n| b => b\n    | c => c\n"),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n    | a => a⟪}⟫⟪}⟫\n| b => b\n    | c => c\n"
        );
    }

    #[test]
    fn a_stray_parenthesis_leaves_the_blocks_open()
    {
        // A `)` with no bracket to close stays inside the block.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = g x)\n  y\n"),
            "def f(x : A) -> A =⟪{⟫\n  let y = g x)⟪;⟫\n  y⟪}⟫⟪;⟫\n"
        );
        // A stray `}` still closes the blocks before it. When it closes the
        // block of a top-level `def`, the `def` takes its `;` before it.
        assert_eq!(
            marked("def f(x : A) -> A =\n  let y = x}\n  y\n"),
            "def f(x : A) -> A =⟪{⟫\n  let y = x⟪}⟫⟪;⟫}\n  y\n"
        );
    }

    #[test]
    fn a_moved_line_stays_in_the_block_its_move_names_5434()
    {
        // An arm at column zero inside two arm blocks and a body closes all
        // three. A move keeps it in the block its count of closes leaves.
        let source = "def f(x : A) -> A =\n  match x where\n    | a => match a where\n      | b => b\n| c => c\n";
        let line = u32::try_from(source.find("| c").unwrap_or_default()).unwrap_or(u32::MAX);
        let moved = |closes: u32| marked_moving(source, &[Move { line, closes }]);
        let head = "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n    | a => match a ⟪where→{⟫\n      | b => b";
        assert_eq!(marked(source), format!("{head}⟪}}⟫⟪}}⟫⟪}}⟫\n| c => c\n"));
        assert_eq!(moved(0), format!("{head}\n| c => c⟪}}⟫⟪}}⟫⟪}}⟫⟪;⟫\n"));
        assert_eq!(moved(1), format!("{head}⟪}}⟫\n| c => c⟪}}⟫⟪}}⟫⟪;⟫\n"));
        assert_eq!(moved(2), format!("{head}⟪}}⟫⟪}}⟫\n| c => c⟪}}⟫⟪;⟫\n"));
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
        let first = "def f(x : A) -> A =\n  match x where\n| a => a\n    | b => b\n";
        let line = u32::try_from(first.find("| a").unwrap_or_default()).unwrap_or(u32::MAX);
        let first_moved = |closes: u32| marked_moving(first, &[Move { line, closes }]);
        assert_eq!(
            marked(first),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫⟪}⟫⟪}⟫\n| a => a\n    | b => b\n"
        );
        assert_eq!(
            first_moved(0),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫\n| a => a\n    | b => b⟪}⟫⟪}⟫⟪;⟫\n"
        );
        assert_eq!(
            first_moved(1),
            "def f(x : A) -> A =⟪{⟫\n  match x ⟪where→{⟫⟪}⟫\n| a => a\n    | b => b⟪}⟫⟪;⟫\n"
        );
    }
}
