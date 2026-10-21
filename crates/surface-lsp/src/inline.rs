//! Inline completion: what may be written at the cursor, as ranked ghost
//! texts an editor shows there.
//!
//! [`ghost()`] molds the form the cursor is in up to the cursor, asks the
//! parser's completion query what may follow
//! ([`MeldState::continuations`]), subtracts what is already written after
//! the cursor, ranks what remains and spells each candidate as a snippet: a
//! tile as its text, a lexical class or a hole as a tab stop naming what fills
//! it.
//!
//! # Every cursor has a ghost text
//!
//! An inline-completion request reads the text's labeling, relabeled around
//! the cursor for the text before it, splits that at its predicted top-level
//! form boundaries and molds the last form alone. The
//! completion query names the hole the operator nearest the cursor owes and
//! the cheapest ways to close the innermost open form — each a path through
//! the grammar's same-form adjacency to a tile that ends the form, from every
//! reading of the frontier's tile, an empty bracket pair holding the hole its
//! grammar admits. Those are the candidates: the cheapest is the form's
//! closing, the others are its alternatives (another parameter, the return
//! type, another arm, another constructor). Where the cursor stands at an
//! empty slot, each form the slot's sort can open fills it too — its opening
//! token, its own cheapest closing, then the rest of the slot's closing; at
//! the top level, after a complete form or in an empty document, the slot is
//! the next declaration. The forms are read off the grammar once, as
//! [`Forms`]: every form-first mold typed as its own text that continues no
//! operand, with its cheapest closing that ends no list in a trailing comma.
//! The answer is the ranked candidates, at most eight, each inserted at the
//! empty range at the cursor; it is never empty, and its last resort is the
//! placeholder of the slot at the cursor.
//!
//! The text after the cursor is input, never a refusal. The whole text's
//! labeling is read, and the significant tokens after the cursor, up to the
//! first closer of a bracket open at the cursor, are what is already written. A
//! candidate is cut where the written text takes over: at its first tile the
//! next token spells, at its first closer that a written closer of the same
//! family pairs with — counting brackets opened and closed on the way, by the
//! grammar's closing classes — or at its first hole that the next tokens fill:
//! a run starting at an operand and ending, at its own depth, before a
//! separator, a closer, a declaration's head or a keyword. So a closer already
//! written, on the cursor's line or below it, is neither repeated nor
//! required, and a cursor inside an auto-closed `{}`, `()` or `[]` answers for
//! the pair's contents. A candidate wholly written is dropped; where the
//! written text fills the slot, a form that ends in a hole — `return`,
//! `force`, a prefix operator — takes it as that hole's filling. Inside a
//! line comment a ghost text begins with the line end that closes the
//! comment, inside an unclosed block comment with `*/`, and a ghost text ends
//! in a space where the written text would otherwise run into it.
//!
//! - Alternatives: refusing a cursor followed by text on its line, which leaves
//!   an editor that auto-closes pairs without an answer; molding the whole form
//!   with the text after the cursor as lookahead, whose molding cannot tell a
//!   closer the author wrote for this form from one of an outer form;
//!   trial-molding each candidate followed by the written text, which costs a
//!   molding per candidate per request.
//! - Reversal: a measured case where the token alignment cuts a candidate
//!   wrongly moves the subtraction onto trial molding of the candidate and the
//!   written text up to the form's end.
//!
//! # A text is labeled once for all its cursors
//!
//! A [`Labeled`] text holds the text and its labeling. The text before a
//! cursor is labeled by relabeling that labeling around the cut
//! ([`Labeling::relabel`]), which rescans only from the cursor's previous
//! line, and the written tokens are read off the whole labeling from the
//! cursor on. [`ghost()`] labels its text once; a caller asking at many
//! cursors of one text, the corpus sweep among them, labels it once for all
//! of them, so a cursor costs a rescan of its line and a molding of its form,
//! not a labeling of the text twice.
//!
//! - Alternatives: labeling the text before the cursor and the whole text
//!   afresh on every request, which costs a request two scans of the text and a
//!   sweep over a source a number of scans quadratic in its length; a labeling
//!   cached on the server's documents, which the editor's session does not hand
//!   this module.
//! - Reversal: a session that keeps each document's labeling hands it to
//!   [`Labeled`] directly, and the server stops labeling per request.
//!
//! # A hole is spelled as what fills it
//!
//! A tile is written as `tile_spelling` gives it, escaped for the snippet
//! syntax; a lexical class such as `identifier` is a tab stop naming the
//! class; a hole is a tab stop naming its syntactic category, and the forms
//! that can fill it are offered as candidates of their own, each a concrete
//! token followed by its own closing. The category of an expression hole is
//! read off the tile whose right context faces it, the call-by-push-value
//! position the grammar's molds already encode:
//!
//! | The hole follows | Category |
//! |---|---|
//! | `{`, `;`, `<-`, `=>`, `become`, `#!{` | `computation` |
//! | any other tile or operator: `return`, `pure`, `=`, `(`, `,`, an operator | `value` |
//!
//! Every other sort names itself: `type`, `pattern`, `item`, `member`,
//! `instantiation`. No ghost text holds `?`, the hole a gandr source writes:
//! accepting a ghost text leaves tab stops for the editor, never a goal.
//!
//! - Alternatives: the checker's synthetic hole, whose goal type is the
//!   stronger category but is determined only at a checking position and costs
//!   a typing pass per request; `?` for every expression, pattern and type
//!   hole, which says nothing about what fills it.
//! - Reversal: the typed tier ranks the same candidates against the goal the
//!   checker reads at the cursor, behind the same ranking function.
//!
//! # The ranking is one function
//!
//! [`rank`] orders candidates by a key built from the candidate and the slot at
//! the cursor, lower first:
//!
//! 1. the fit with the written text: cut where the written text takes over,
//!    then nothing written that it meets, then a candidate ending in a closer
//!    or a separator right before written operand text;
//! 2. the tier: the form's cheapest closing; the cheapest closing that names
//!    the slot's hole, when the cheapest does not; the other closings and the
//!    forms that yield the slot's category; the forms that yield another;
//! 3. the turn: a candidate's position among those of its tier and kind, the
//!    closings cheapest first and the forms in the grammar's declaration order;
//! 4. a form before a closing, so a tier alternates the two.
//!
//! A form yields a computation when it opens with `return`, `pure`,
//! `become`, `case`, `if`, `fn`, `force`, `while`, `for`, `loop`, `break`,
//! `continue`, a block's `{`, `#!{` or `&`, and a value otherwise. A closing
//! that differs from a better candidate only by separators, or holds a `,`
//! right before a closer, is not offered.
//!
//! - Alternatives: ranking by cost alone, which puts literal atoms and a lone
//!   attribute above `return` and `def`; the forms before every alternative
//!   closing, which hides a block's statements behind its expression forms; a
//!   fixed preference per form.
//! - Reversal: a ranker built from corpus statistics or a learned model
//!   replaces [`rank`] behind the same signature, and the ranking golden
//!   changes with it.

use alloc::string::String;
use alloc::vec::Vec;
use core::cell::OnceCell;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TileLabel;
use gandr_surface_parser::CandidateLabel;
use gandr_surface_parser::ClosingLimit;
use gandr_surface_parser::Continuations;
use gandr_surface_parser::HeadForm;
use gandr_surface_parser::Labeling;
use gandr_surface_parser::LeadingSlot;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::Step;
use gandr_surface_parser::TileSpelling;
use gandr_surface_parser::Token;
use gandr_surface_parser::TokenText;
use gandr_surface_parser::candidate_labels;
use gandr_surface_parser::closings;
use gandr_surface_parser::label;
use gandr_surface_parser::tile_spelling;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

/// How many closings of the innermost open form the query walks.
/// Nine holds the equation arrow beside the attributed constructor.
const CLOSINGS: usize = 9;

/// How many ghost texts an answer holds at most.
const SHOWN: usize = 8;

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a snippet of several words and a tab stop, read back,
    ///   differs from the empty text and from any fixed one.
    /// - witness: `inline::tests::a_snippet_lends_the_text_it_inserts`
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// The ghost texts at a cursor, best first: never empty, at most eight.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Ghosts(Vec<Snippet>);

impl AsRef<[Snippet]> for Ghosts
{
    /// The ghost texts, best first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[Snippet]
    {
        &self.0
    }
}

impl IntoIterator for Ghosts
{
    type IntoIter = alloc::vec::IntoIter<Snippet>;
    type Item = Snippet;

    /// The ghost texts, best first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.0.into_iter()
    }
}

/// The syntactic category a hole shows: what fills it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Category
{
    /// A value: a returned, bound or passed expression.
    Value,
    /// A computation: a body, a statement, or what `run` binds.
    Computation,
    /// A type.
    Type,
    /// A pattern.
    Pattern,
    /// A top-level declaration.
    Item,
    /// A member of a module body.
    Member,
    /// A resident of an instantiation slot.
    Instantiation,
}

impl Category
{
    /// The category of a hole of `sort` faced by the right context of the mold
    /// `after`.
    ///
    /// # Specification
    /// - ensures: for an expression, [`Category::Computation`] after `{`, `;`,
    ///   `<-`, `=>`, `become`, `run` or `#!{`, [`Category::Value`] after any
    ///   other tile, an unknown mold included; every other sort's own category.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value after `return`, a computation in a thunk body
    ///   and after `<-`, a type after `:`, a pattern in an arm and an item at
    ///   the top level each show their exact placeholder. Reading the sort
    ///   alone, or the wrong side's tile, changes one of them.
    /// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
    #[spec(ensures: |ret| ret.sort() == sort && (sort != Sort::Expression || grammar.mold(after).is_ok() || ret == Self::Value))]
    fn of_hole(
        grammar: &Pbg,
        sort: Sort,
        after: MoldId,
    ) -> Self
    {
        match sort {
            Sort::Expression => {
                let before = grammar.mold(after).map(|def| def.label);
                match before {
                    Ok("{" | ";" | "<-" | "=>" | "become" | "run" | "#!{") => Self::Computation,
                    Ok(_) | Err(_) => Self::Value,
                }
            },
            Sort::Pattern => Self::Pattern,
            Sort::Type => Self::Type,
            Sort::Item => Self::Item,
            Sort::ModuleMember => Self::Member,
            Sort::Instantiation => Self::Instantiation,
        }
    }

    /// The category the form a mold of `sort` labeled `opener` opens yields.
    ///
    /// # Specification
    /// - ensures: for an expression, [`Category::Computation`] for the forms
    ///   `return`, `pure`, `become`, `case`, `if`, `fn`, `force`, `while`,
    ///   `for`, `loop`, `break`, `continue`, a block `{`, a shell block `#!{`
    ///   and a lazy record `&` open, [`Category::Value`] for every other; every
    ///   other sort's own category.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ranking golden ranks `return` among a computation
    ///   slot's forms and `thunk` among a value slot's. Swapping the two yields
    ///   changes that order.
    /// - witness: `inline::tests::the_ranking_is_pinned`
    #[spec(ensures: |ret| ret.sort() == sort)]
    fn yielded(
        sort: Sort,
        opener: TileLabel,
    ) -> Self
    {
        match (sort, opener.0) {
            (
                Sort::Expression,
                "return" | "pure" | "become" | "case" | "if" | "fn" | "force" | "while" | "for"
                | "loop" | "break" | "continue" | "{" | "#!{" | "&",
            ) => Self::Computation,
            (Sort::Expression, _) => Self::Value,
            (Sort::Pattern, _) => Self::Pattern,
            (Sort::Type, _) => Self::Type,
            (Sort::Item, _) => Self::Item,
            (Sort::ModuleMember, _) => Self::Member,
            (Sort::Instantiation, _) => Self::Instantiation,
        }
    }

    /// The grammar sort whose holes the category names.
    ///
    /// # Specification
    /// trivial.
    const fn sort(self) -> Sort
    {
        match self {
            Self::Value | Self::Computation => Sort::Expression,
            Self::Type => Sort::Type,
            Self::Pattern => Sort::Pattern,
            Self::Item => Sort::Item,
            Self::Member => Sort::ModuleMember,
            Self::Instantiation => Sort::Instantiation,
        }
    }

    /// The tab stop a hole of the category shows.
    ///
    /// # Specification
    /// trivial.
    const fn placeholder(self) -> Piece<'static>
    {
        Piece::Stop(match self {
            Self::Value => "value",
            Self::Computation => "computation",
            Self::Type => "type",
            Self::Pattern => "pattern",
            Self::Item => "item",
            Self::Member => "member",
            Self::Instantiation => "instantiation",
        })
    }
}

/// One part of a candidate's material.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Part
{
    /// A tile, by its label.
    Tile(TileLabel),
    /// A hole of a category.
    Hole(Category),
}

/// Where a candidate comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Origin
{
    /// The cheapest closing of the innermost open form.
    Closing,
    /// The cheapest other closing that starts with a hole at the cursor, when
    /// the cheapest does not.
    Slot,
    /// Another closing of it.
    Alternative,
    /// A form that fills the slot at the cursor, yielding this category.
    Opener(Category),
}

/// How a candidate meets the text written after the cursor.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Fit
{
    /// The candidate is cut where the written text takes over.
    Meets,
    /// Nothing written after the cursor continues it.
    Free,
    /// It ends in a closer or a separator right before written operand text.
    Collides,
}

/// The slot at the cursor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Slot
{
    /// A hole of this category stands at the cursor.
    Open(Category),
    /// Something already stands there.
    Filled,
}

/// What the slot's closing inserts after its hole.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Rest
{
    /// The written text already fills the slot.
    Written,
    /// These parts, meeting the written text so.
    Unwritten(Vec<Part>, Fit),
}

/// `parts` without their separators.
///
/// # Specification
/// trivial.
fn skeleton(parts: &[Part]) -> Vec<Part>
{
    parts
        .iter()
        .copied()
        .filter(|part| !matches!(part, Part::Tile(tile) if matches!(tile.0, ";" | ",")))
        .collect()
}

/// One ghost text before it is spelled.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Candidate
{
    /// Where it comes from.
    origin: Origin,
    /// The parts it inserts, in source order.
    parts: Vec<Part>,
    /// How it meets the written text.
    fit: Fit,
    /// Its turn among the candidates placed as it is.
    turn: Turn,
}

/// A candidate's position among the candidates placed as it is, in the order
/// they were produced: cheapest first for closings, declaration order for
/// forms.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Turn(usize);

/// A candidate's tier: how directly it answers the cursor.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Tier
{
    /// The cheapest closing of the innermost open form.
    Closing,
    /// The closing that names the slot at the cursor.
    Slot,
    /// Another closing, or a form yielding the slot's category.
    Menu,
    /// A form yielding another category.
    Aside,
}

/// What kind of candidate it is, the tie-break within a turn.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Kind
{
    /// A form that fills the slot.
    Form,
    /// A closing.
    Closing,
}

/// The tier and the kind of a candidate from `origin` at a cursor whose slot
/// is `slot`.
///
/// # Specification
/// - ensures: the closing, the slot's closing and the other closings are
///   closings in their own tiers; a form is in [`Tier::Menu`] when it yields
///   the open slot's category and in [`Tier::Aside`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ranking golden places a value slot's forms above its
///   computations and a computation slot's the other way round; comparing
///   yields wrongly swaps them.
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| matches!(ret, (_, Kind::Form)) == matches!(origin, Origin::Opener(_))
    && matches!(ret, (Tier::Closing, _)) == matches!(origin, Origin::Closing))]
fn place(
    origin: Origin,
    slot: Slot,
) -> (Tier, Kind)
{
    match (origin, slot) {
        (Origin::Closing, _) => (Tier::Closing, Kind::Closing),
        (Origin::Slot, _) => (Tier::Slot, Kind::Closing),
        (Origin::Alternative, _) => (Tier::Menu, Kind::Closing),
        (Origin::Opener(yields), Slot::Open(wanted)) if yields == wanted => {
            (Tier::Menu, Kind::Form)
        },
        (Origin::Opener(_), Slot::Open(_) | Slot::Filled) => (Tier::Aside, Kind::Form),
    }
}

/// The key a candidate ranks by, lower first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Rank
{
    /// Its fit with the written text.
    fit: Fit,
    /// Its tier.
    tier: Tier,
    /// Its turn among the candidates placed as it is.
    turn: Turn,
    /// Its kind.
    kind: Kind,
}

/// The ranking key of `candidate` at a cursor whose slot is `slot`: the one
/// function a corpus-derived or learned ranker replaces.
///
/// # Specification
/// - ensures: the fit, then the tier [`place`] gives, then the candidate's
///   turn, then a form before a closing — so within a tier the forms and the
///   alternatives alternate, each in its own order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the pinned ranking golden orders candidates at a handful
///   of cursors; reordering the key's fields or misplacing a tier changes the
///   golden.
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| ret.fit == candidate.fit && ret.turn == candidate.turn && (ret.tier, ret.kind) == place(candidate.origin, slot))]
fn rank(
    candidate: &Candidate,
    slot: Slot,
) -> Rank
{
    let (tier, kind) = place(candidate.origin, slot);
    Rank {
        fit: candidate.fit,
        tier,
        turn: candidate.turn,
        kind,
    }
}

/// The role a written token plays in cutting a candidate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role
{
    /// It opens a bracket of this family.
    Opens(ClosingClass),
    /// It closes a bracket of this family.
    Closes(ClosingClass),
    /// It is `;` or `,`.
    Separates,
    /// It opens a top-level declaration.
    Heads,
    /// It can start an operand: one of its labels opens a form.
    Operand,
    /// Anything else: a keyword or an operator inside a form.
    Keyword,
}

/// What a written token's text alone says of it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Punctuation
{
    /// It opens a bracket of this family.
    Opens(ClosingClass),
    /// It closes a bracket of this family.
    Closes(ClosingClass),
    /// It is `;` or `,`.
    Separates,
    /// It is a word or an operator, classified through the grammar.
    Word,
}

/// One significant token written after the cursor.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Word<'text>
{
    /// Its lexical class.
    lexeme: Lexeme,
    /// Its text.
    text: &'text str,
    /// What its text alone says of it.
    punctuation: Punctuation,
    /// Its role, classified on first use.
    role: OnceCell<Role>,
}

impl Word<'_>
{
    /// The word's role under `grammar`.
    ///
    /// # Specification
    /// - ensures: a bracket or a separator as its punctuation says; otherwise
    ///   [`classify`]'s answer, computed once.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect fixtures cut at a written `}` and keep a
    ///   written `=` out of a hole; misreading either changes their answers.
    /// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
    #[spec(ensures: |ret| matches!(self.punctuation, Punctuation::Word) == matches!(ret, Role::Heads | Role::Operand | Role::Keyword))]
    fn role(
        &self,
        grammar: &Pbg,
    ) -> Role
    {
        match self.punctuation {
            Punctuation::Opens(family) => Role::Opens(family),
            Punctuation::Closes(family) => Role::Closes(family),
            Punctuation::Separates => Role::Separates,
            Punctuation::Word => *self
                .role
                .get_or_init(|| classify(grammar, self.lexeme, TokenText::from(self.text))),
        }
    }
}

/// The significant tokens written after the cursor, in source order, up to
/// the first closer of a bracket open at the cursor.
#[derive(Clone, Debug)]
struct Written<'grammar, 'text>
{
    /// The grammar the words are classified under.
    grammar: &'grammar Pbg,
    /// The words.
    words: Vec<Word<'text>>,
}

impl<'grammar, 'text> Written<'grammar, 'text>
{
    /// The significant tokens of `labeled` that start at or after `at`, up to
    /// and including the first closer at the cursor's bracket depth, read off
    /// the whole text's labeling so a token after the cursor reads in its own
    /// lexical mode.
    ///
    /// # Specification
    /// - ensures: every token of `labeled`'s labeling that is not layout and
    ///   starts at or after `at`, in order, ending at the first one that closes
    ///   a bracket no earlier one of them opened; a token the cursor splits is
    ///   not among them.
    /// - panics: none.
    /// - intension: what a candidate is cut against ends there: a hole stops at
    ///   that closer and a pairing reads no further, so no word past it is
    ///   classified.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect fixtures place a closer on the cursor's
    ///   line, on the next line, past a nested pair and none at all; reading
    ///   the cursor's split token or layout, or stopping at the nested pair's
    ///   closer, changes their answers.
    /// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
    #[spec(ensures: |ret| ret.words.iter().all(|word| !word.text.is_empty())
        && ret.words.iter().filter(|word| matches!(word.punctuation, Punctuation::Closes(_))).count()
            <= ret.words.iter().filter(|word| matches!(word.punctuation, Punctuation::Opens(_))).count().saturating_add(1))]
    fn after(
        grammar: &'grammar Pbg,
        labeled: &Labeled<'text>,
        at: ByteOffset,
    ) -> Self
    {
        let whole = <&'text str>::from(labeled.text);
        let at = usize::from(at);
        let tokens = labeled.labeling.tokens();
        let first = tokens
            .partition_point(|token| usize::try_from(token.start).is_ok_and(|start| start < at));
        let mut words = Vec::new();
        let mut depth = 0_usize;
        for token in tokens.get(first ..).unwrap_or_default() {
            let (Ok(start), Ok(end)) = (usize::try_from(token.start), usize::try_from(token.end))
            else {
                continue;
            };
            let Some(text) = whole.get(start .. end)
            else {
                continue;
            };
            if token.lexeme == Lexeme::Space {
                continue;
            }
            let punctuation = punctuation(token.lexeme, TokenText::from(text));
            words.push(Word {
                lexeme: token.lexeme,
                text,
                punctuation,
                role: OnceCell::new(),
            });
            match punctuation {
                Punctuation::Opens(_) => depth = depth.saturating_add(1),
                Punctuation::Closes(_) if depth == 0 => break,
                Punctuation::Closes(_) => depth = depth.saturating_sub(1),
                Punctuation::Separates | Punctuation::Word => {},
            }
        }
        Self { grammar, words }
    }
}

/// A text and its labeling, read once for the ghost texts at any of its
/// cursors.
///
/// # Specification
/// - requires: constructed by [`new`](Self::new) or [`cut`](Self::cut).
/// - ensures: the labeling is [`Labeling::new`]'s of the text.
/// - panics: none.
/// - executable: none — this data type has no call boundary; its constructors
///   carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — every cursor of a corpus source holding comments, strings
///   and an interpolation cuts to the labeling of the text before it and
///   answers as that text labeled afresh; a cut that kept a token the cursor
///   splits, or read a mode the prefix does not stand in, changes one.
/// - witness: `inline::tests::a_cut_answers_as_its_text_labeled_afresh_594`
#[derive(Clone, Debug)]
pub struct Labeled<'text>
{
    /// The text.
    text: SourceText<'text>,
    /// Its labeling.
    labeling: Labeling,
}

impl<'text> Labeled<'text>
{
    /// Label `text` from its start.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `text` with [`Labeling::new`]'s labeling of it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cut witness compares every cut of a labeled
    ///   source with the text before the cursor labeled by this constructor.
    /// - witness: `inline::tests::a_cut_answers_as_its_text_labeled_afresh_594`
    #[must_use]
    #[spec(ensures: |ret| ret.text == text)]
    pub fn new(text: SourceText<'text>) -> Self
    {
        Self {
            text,
            labeling: Labeling::new(SourceFragment::from(<&str>::from(text))),
        }
    }

    /// The text before byte `at`, its labeling relabeled from this one around
    /// the cut.
    ///
    /// # Specification
    /// - requires: any offset, one past the text or inside a character read as
    ///   the nearest character boundary at or before it.
    /// - ensures: the text before that boundary, labeled as [`new`](Self::new)
    ///   labels it.
    /// - panics: none.
    /// - economy: copies the tokens and rescans from the cut's previous line
    ///   ([`Labeling::relabel`]), never the whole text.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every cursor of a corpus source holding comments,
    ///   strings and an interpolation cuts to the labeling of the text before
    ///   it; a cut that kept the token the cursor splits changes one.
    /// - witness: `inline::tests::a_cut_answers_as_its_text_labeled_afresh_594`
    #[must_use]
    #[spec(ensures: |ret| <&str>::from(self.text).starts_with(<&str>::from(ret.text)))]
    pub fn cut(
        &self,
        at: ByteOffset,
    ) -> Self
    {
        let whole = <&'text str>::from(self.text);
        let before = whole
            .get(.. whole.floor_char_boundary(usize::from(at)))
            .unwrap_or_default();
        Self {
            text: SourceText::from(before),
            labeling: self
                .labeling
                .clone()
                .relabel(SourceFragment::from(whole), SourceFragment::from(before)),
        }
    }
}

/// What a token's text alone says of it.
///
/// # Specification
/// - ensures: a punctuation token that opens or closes a bracket family as
///   that; `;` and `,` as separating; anything else as a word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect fixtures pair a written `)` past a nested pair
///   and cut at a written `}`; misreading a bracket changes them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
#[spec(ensures: |ret| lexeme == Lexeme::Punct || matches!(ret, Punctuation::Word))]
fn punctuation(
    lexeme: Lexeme,
    text: TokenText<'_>,
) -> Punctuation
{
    let spelled = <&str>::from(text);
    if lexeme != Lexeme::Punct {
        return Punctuation::Word;
    }
    if let Some(family) = ClosingClass::opening(DelimSpelling::from(spelled)) {
        return Punctuation::Opens(family);
    }
    if let Some(family) = ClosingClass::closing(DelimSpelling::from(spelled)) {
        return Punctuation::Closes(family);
    }
    if matches!(spelled, ";" | ",") {
        Punctuation::Separates
    }
    else {
        Punctuation::Word
    }
}

/// The role a written word or operator, of `lexeme` and written as `text`,
/// plays in cutting a candidate.
///
/// # Specification
/// - ensures: [`Role::Heads`] when one of its labels opens a top-level
///   declaration; [`Role::Operand`] when one opens a form of another sort;
///   [`Role::Keyword`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the server witness keeps a ghost text from absorbing a
///   written `=` into a type hole, and the category witness reads a following
///   declaration as a boundary; reading `=` as an operand changes them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `server::tests::inline_completion_answers_the_expected_closer`
#[spec(ensures: |ret| matches!(ret, Role::Heads | Role::Operand | Role::Keyword))]
fn classify(
    grammar: &Pbg,
    lexeme: Lexeme,
    text: TokenText<'_>,
) -> Role
{
    let mut role = Role::Keyword;
    for &offered in &candidate_labels(lexeme, text) {
        let Some(tile) = grammar.tile_label(LabelText(<&str>::from(offered)))
        else {
            continue;
        };
        for &mold in grammar.candidates(tile) {
            if !bool::from(grammar.mold_is_form_first(mold)) {
                continue;
            }
            match grammar.mold(mold).map(|def| def.sort) {
                Ok(Sort::Item) => return Role::Heads,
                Ok(_) => role = Role::Operand,
                Err(_) => {},
            }
        }
    }
    role
}

/// Whether a written word is the tile a part names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spelled
{
    /// The word is the tile.
    Written,
    /// It is not.
    Unwritten,
}

/// Whether `word` is a tile labeled `tile`: the tile's own text, or a token of
/// the lexical class it names.
///
/// # Specification
/// - ensures: [`Spelled::Written`] exactly when one of the labels the word's
///   token offers is `tile`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect fixtures cut at a written `}` and at a written
///   `)`; comparing classes as literal text never cuts at an identifier.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
#[spec(ensures: |ret| matches!(ret, Spelled::Written)
    == candidate_labels(word.lexeme, TokenText::from(word.text)).iter().any(|&label| <&str>::from(label) == tile.0))]
fn spelled(
    word: &Word<'_>,
    tile: TileLabel,
) -> Spelled
{
    let offered = candidate_labels(word.lexeme, TokenText::from(word.text));
    if offered.iter().any(|&label| <&str>::from(label) == tile.0) {
        Spelled::Written
    }
    else {
        Spelled::Unwritten
    }
}

/// Cut `parts` where the text written after the cursor takes over, and say
/// how what remains meets it.
///
/// # Specification
/// - ensures: `parts` is cut before its first part from which the written text
///   takes over: a tile the next word spells; a closer that a written closer of
///   its family pairs with, brackets opened and closed on the way counted; or a
///   hole the next words fill — a run starting at an operand and ending, at its
///   own depth, before a separator, a closer, a declaration's head or a keyword
///   — when the word after the run is the tile that follows the hole or no
///   operand. The answer is [`Fit::Meets`] when it was cut; otherwise
///   [`Fit::Collides`] when it ends in a closer or a separator and the next
///   word starts an operand, and [`Fit::Free`] when it does not.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect fixtures cut a written `}` on the cursor's
///   line and on the next, the totality witness cuts a written `)` after a
///   nested pair, and the ranking golden keeps an uncut closing; a part `)`
///   meets a written `[1])` past its nested pair, and not a written `]`.
///   Cutting at a closer of another family, or not counting nested brackets,
///   changes them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::the_ranking_is_pinned`
/// - witness: `inline::tests::a_written_closer_pairs_only_past_the_brackets_written_before_it`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: `parts` is one candidate's material, which the caller builds afresh for this call alone; the check copies it once and compares the kept prefix once, no more than building it cost"
    )
)]
#[spec(captures: before = parts.clone(), ensures: |ret| before.starts_with(parts.as_slice())
    && matches!(ret, Fit::Meets) == (parts.len() < before.len()))]
fn subtract(
    parts: &mut Vec<Part>,
    written: &Written<'_, '_>,
) -> Fit
{
    let words = written.words.as_slice();
    let role = |word: &Word<'_>| word.role(written.grammar);
    let next_spells = |tile: TileLabel, at: usize| {
        words
            .get(at)
            .is_some_and(|word| spelled(word, tile) == Spelled::Written)
    };
    // How many words a hole at the cursor takes: a bracket-balanced run
    // starting at an operand that stops at a separator, a closer, a
    // declaration's head or a keyword at its own depth.
    let filled = || {
        let mut depth = 0_usize;
        let mut taken = 0_usize;
        if words
            .first()
            .is_none_or(|word| !matches!(role(word), Role::Operand | Role::Opens(_)))
        {
            return 0;
        }
        for word in words {
            match role(word) {
                Role::Opens(_) => depth = depth.saturating_add(1),
                Role::Closes(_) | Role::Separates | Role::Heads | Role::Keyword if depth == 0 => {
                    break;
                },
                Role::Closes(_) => depth = depth.saturating_sub(1),
                Role::Separates | Role::Heads | Role::Keyword | Role::Operand => {},
            }
            taken = taken.saturating_add(1);
        }
        taken
    };
    // Whether a written closer of `family` pairs with an open bracket at the
    // cursor: the last word, when it closes one no earlier word opened.
    let pairs = |family: ClosingClass| {
        let mut depth = 0_usize;
        for word in words {
            match word.punctuation {
                Punctuation::Opens(_) => depth = depth.saturating_add(1),
                Punctuation::Closes(closed) if depth == 0 => return closed == family,
                Punctuation::Closes(_) => depth = depth.saturating_sub(1),
                Punctuation::Separates | Punctuation::Word => {},
            }
        }
        false
    };
    let cut = parts
        .iter()
        .enumerate()
        .position(|(index, &part)| match part {
            Part::Tile(tile) => {
                next_spells(tile, 0)
                    || ClosingClass::closing(DelimSpelling::from(tile.0)).is_some_and(&pairs)
            },
            Part::Hole(_) => {
                let taken = filled();
                taken > 0
                    && match parts.get(index.saturating_add(1)) {
                        Some(&Part::Tile(tile)) => {
                            next_spells(tile, taken)
                                || words
                                    .get(taken)
                                    .is_none_or(|word| role(word) != Role::Operand)
                        },
                        Some(&Part::Hole(_)) | None => true,
                    }
            },
        });
    if let Some(cut) = cut {
        parts.truncate(cut);
        return Fit::Meets;
    }
    whole_fit(parts, written)
}

/// How `parts`, inserted whole, meet the text written after the cursor.
///
/// # Specification
/// - ensures: [`Fit::Collides`] when `parts` ends in a closer or a separator
///   and the next written word starts an operand or opens a bracket;
///   [`Fit::Free`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the totality witness's cursors before written operands
///   rank a closer below a form that fills the slot; reading the last part's
///   kind wrongly reverses them; a closer before a written operand collides,
///   and the same closer at the end of the text, or an opener before an
///   operand, is free.
/// - witness: `inline::tests::the_ranking_is_pinned`
/// - witness: `inline::tests::parts_inserted_whole_collide_only_when_they_end_closed_before_an_operand`
#[spec(ensures: |ret| !matches!(ret, Fit::Meets) && (matches!(ret, Fit::Free) || !parts.is_empty()))]
fn whole_fit(
    parts: &[Part],
    written: &Written<'_, '_>,
) -> Fit
{
    let operand_next = written
        .words
        .first()
        .is_some_and(|word| matches!(word.role(written.grammar), Role::Operand | Role::Opens(_)));
    let ends_closed = matches!(parts.last(), Some(&Part::Tile(tile))
        if ClosingClass::closing(DelimSpelling::from(tile.0)).is_some() || matches!(tile.0, ";" | ","));
    if operand_next && ends_closed {
        Fit::Collides
    }
    else {
        Fit::Free
    }
}

/// The parts `steps` write, each hole named by its category.
///
/// # Specification
/// - ensures: each tile as its label and each hole as [`Category::of_hole`]
///   names it, in order; a tile of an unknown mold is left out.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the category witness asserts each placeholder; naming a
///   hole by its sort alone changes them.
/// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
#[spec(ensures: |ret| ret.len() <= steps.len()
    && ret.iter().filter(|part| matches!(part, Part::Hole(_))).count()
        == steps.iter().filter(|step| matches!(step, Step::Hole { .. })).count())]
fn parts(
    grammar: &Pbg,
    steps: &[Step],
) -> Vec<Part>
{
    steps
        .iter()
        .filter_map(|&step| match step {
            Step::Tile(mold) => grammar
                .mold(mold)
                .ok()
                .map(|def| Part::Tile(TileLabel(def.label))),
            Step::Hole { sort, after } => Some(Part::Hole(Category::of_hole(grammar, sort, after))),
        })
        .collect()
}

/// Whether the tile `tile` is typed as its own text: its label read back
/// whole as one token that offers it, a word only when reserved, and not a
/// separator or a closer.
///
/// # Specification
/// - ensures: [`Spelled::Written`] exactly when labeling the tile's label
///   yields one significant token spanning it whose candidate labels include it
///   — only it, for a word — and the label is not `;`, `,` or a closer.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ranking golden lists the forms the top level and a
///   value slot offer; a grammar-internal name such as `line_comment` or
///   `newline`, or a lone `;`, read as typed changes it; each separator and
///   closer reads as unwritten, an opener as written.
/// - witness: `inline::tests::the_ranking_is_pinned`
/// - witness: `inline::tests::a_separator_or_a_closer_is_never_typed_as_its_own_text`
#[spec(ensures: |ret| matches!(ret, Spelled::Unwritten) || (!tile.0.is_empty() && !matches!(tile.0, ";" | ",")))]
fn typed(tile: TileLabel) -> Spelled
{
    let text = tile.0;
    let tokens = label(SourceFragment::from(text));
    let &[token] = tokens.as_slice()
    else {
        return Spelled::Unwritten;
    };
    let whole = usize::try_from(token.start).is_ok_and(|start| start == 0)
        && usize::try_from(token.end).is_ok_and(|end| end == text.len());
    let offered = candidate_labels(token.lexeme, TokenText::from(text));
    let offers = match token.lexeme {
        Lexeme::LowerWord | Lexeme::UpperWord => offered.len() == 1,
        Lexeme::Punct => offered.iter().any(|&label| <&str>::from(label) == text),
        Lexeme::Number
        | Lexeme::TypedNumber
        | Lexeme::Character
        | Lexeme::Quote
        | Lexeme::StringFragment
        | Lexeme::ShellStringFragment
        | Lexeme::EscapeSequence
        | Lexeme::ShellWord
        | Lexeme::EnvAssign
        | Lexeme::SingleQuotedContent
        | Lexeme::VariableName
        | Lexeme::SubshellOpen
        | Lexeme::SubshellClose
        | Lexeme::FileDescriptor
        | Lexeme::Space
        | Lexeme::Unknown => false,
    };
    let punctuates =
        matches!(text, ";" | ",") || ClosingClass::closing(DelimSpelling::from(text)).is_some();
    if whole && offers && !punctuates {
        Spelled::Written
    }
    else {
        Spelled::Unwritten
    }
}

/// One form a hole can open: its sort, the category it yields, and its
/// opening tile followed by its cheapest closing.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Form
{
    /// The sort of the hole it fills.
    sort: Sort,
    /// The category it yields.
    yields: Category,
    /// Its opening tile and closing.
    material: Vec<Part>,
}

/// Every form a hole of each sort can open, read off a grammar once: what an
/// inline completion offers to fill the slot at the cursor.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Forms(Vec<Form>);

impl Forms
{
    /// The forms of `grammar`.
    ///
    /// # Specification
    /// - ensures: one form per form-first mold whose label is [`typed`], is not
    ///   the `?` hole, and continues no operand before it; each its label
    ///   followed by the parts of its cheapest closing without a trailing comma
    ///   among the cheapest three, none when all three trail one; in mold
    ///   order.
    /// - panics: none.
    /// - intension: one closing walk per such mold, paid once per grammar
    ///   rather than per request.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ranking golden lists the forms a computation, a
    ///   value, a pattern and an item slot offer; offering a call's argument
    ///   list, a `?` or a grammar-internal name there changes it.
    /// - witness: `inline::tests::the_ranking_is_pinned`
    #[must_use]
    #[spec(ensures: |ret| ret.0.len() <= grammar.form_first().len()
        && ret.0.iter().all(|form| matches!(form.material.first(), Some(&Part::Tile(_))) && trailing(&form.material) == Trailing::Clean))]
    pub fn new(grammar: &Pbg) -> Self
    {
        let state = MeldState::new(grammar);
        let mut found = Vec::new();
        for &mold in grammar.form_first() {
            let Ok(def) = grammar.mold(mold)
            else {
                continue;
            };
            let tile = TileLabel(def.label);
            let operand_before = bool::from(state.continues_operand(mold));
            if typed(tile) == Spelled::Unwritten || def.label == "?" || operand_before {
                continue;
            }
            let mut material = Vec::from([Part::Tile(tile)]);
            let shapes = closings(
                grammar,
                mold,
                LeadingSlot::Empty,
                ClosingLimit::from(3_usize),
            );
            let clean = shapes
                .iter()
                .map(|closing| parts(grammar, closing.steps()))
                .find(|closing| trailing(closing) == Trailing::Clean);
            match clean {
                Some(closing) => material.extend(closing),
                None if shapes.is_empty() => {},
                None => continue,
            }
            found.push(Form {
                sort: def.sort,
                yields: Category::yielded(def.sort, tile),
                material,
            });
        }
        Self(found)
    }

    /// The forms a hole of `sort` can open, in mold order.
    ///
    /// # Specification
    /// trivial.
    fn of(
        &self,
        sort: Sort,
    ) -> impl Iterator<Item = &Form>
    {
        self.0.iter().filter(move |form| form.sort == sort)
    }

    /// The keywords that open a form filling a hole of `category`: the
    /// opening tile of each form of its sort that is spelled as a word, with
    /// that form, in mold order.
    ///
    /// # Specification
    /// - ensures: the opening tile of each form of `category`'s sort whose
    ///   label starts with a letter, with the form's material, in mold order.
    /// - panics: none.
    /// - executable: none — the answer is a lazy iterator over the forms.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an item slot offers `def` and `data`, a computation
    ///   slot `return` and `case`; offering a bracket or another sort's keyword
    ///   changes the completion witnesses.
    /// - witness: `complete::tests::each_slot_offers_its_own_names`
    pub fn keywords(
        &self,
        category: Category,
    ) -> impl Iterator<Item = KeywordForm<'_>> + '_
    {
        self.of(category.sort())
            .filter_map(|form| match form.material.first() {
                Some(&Part::Tile(tile)) if tile.0.starts_with(char::is_alphabetic) => {
                    Some(KeywordForm {
                        word: tile.0,
                        material: &form.material,
                    })
                },
                Some(&(Part::Tile(_) | Part::Hole(_))) | None => None,
            })
    }
}

/// A keyword and the form it opens: what a completion of the keyword inserts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct KeywordForm<'forms>
{
    /// The keyword.
    word: &'static str,
    /// The form's material: the keyword's tile, then its cheapest closing.
    material: &'forms [Part],
}

impl KeywordForm<'_>
{
    /// The keyword.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn word(&self) -> SourceText<'static>
    {
        SourceText::from(self.word)
    }

    /// The form spelled as a snippet to insert where `before` ends and
    /// `after` begins, its holes tab stops; none when the keyword is the whole
    /// form, which inserts as its word.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: none exactly when the form is its keyword alone; otherwise
    ///   the material spelled as an inline completion spells it in code.
    /// - provides: what a keyword's completion inserts to a client that takes
    ///   snippets.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `def` inserts its declaration with a tab stop per
    ///   hole, and a keyword that is its whole form inserts no snippet.
    /// - witness: `complete::tests::a_keyword_inserts_its_form_as_a_snippet`
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == (self.material.len() > 1_usize))]
    pub fn snippet(
        &self,
        before: SourceText<'_>,
        after: SourceText<'_>,
    ) -> Option<Snippet>
    {
        (self.material.len() > 1_usize).then(|| spell(self.material, Lead::Code, before, after))
    }
}

/// Whether a candidate's material ends a list with a trailing comma.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Trailing
{
    /// A `,` stands right before a closer.
    Comma,
    /// None does.
    Clean,
}

/// Whether `parts` holds a `,` right before a closer: a variant of the list it
/// ends that adds nothing an author asks for.
///
/// # Specification
/// - ensures: [`Trailing::Comma`] exactly when a `,` tile is immediately
///   followed by a tile that closes a bracket family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ranking golden holds a tuple pattern and a
///   parenthesized value without their one-element trailing-comma variants;
///   missing the check offers `(${1:pattern},)`.
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| matches!(ret, Trailing::Clean) || parts.iter().any(|part| matches!(part, Part::Tile(tile) if tile.0 == ",")))]
fn trailing(parts: &[Part]) -> Trailing
{
    let comma = parts.windows(2).any(|pair| {
        matches!(pair, [Part::Tile(comma), Part::Tile(closer)]
            if comma.0 == "," && ClosingClass::closing(DelimSpelling::from(closer.0)).is_some())
    });
    if comma {
        Trailing::Comma
    }
    else {
        Trailing::Clean
    }
}

/// The material of each closing of `menu`, in its order, each after the
/// pending parts `pending`; the pending parts alone when no closing is known
/// and some are pending.
///
/// # Specification
/// - ensures: one material per closing, `pending` followed by the closing's
///   steps; `[pending]` when there is no closing and `pending` is not empty;
///   nothing otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`candidates`] and [`slot_of`].
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
#[spec(ensures: |ret| ret.iter().all(|material| material.starts_with(pending)))]
fn closing_materials(
    grammar: &Pbg,
    menu: &Continuations,
    pending: &[Part],
) -> Vec<Vec<Part>>
{
    let mut materials: Vec<Vec<Part>> = menu
        .closings()
        .iter()
        .map(|closing| {
            let mut material = pending.to_vec();
            material.extend(parts(grammar, closing.steps()));
            material
        })
        .collect();
    if materials.is_empty() && !pending.is_empty() {
        materials.push(pending.to_vec());
    }
    materials
}

/// The slot at a cursor whose continuations are `menu`, the pending parts
/// `pending`, and `slotted`, the first closing's material that starts with a
/// hole.
///
/// # Specification
/// - ensures: the slot open in the category of `slotted`'s first hole; else
///   [`Category::Item`] open when no form is open and nothing is pending; else
///   [`Slot::Filled`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the category witness names the slot at a value, a
///   computation, a type, a pattern and the top level; the completion witnesses
///   offer each slot's names.
/// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
/// - witness: `complete::tests::each_slot_offers_its_own_names`
#[spec(ensures: |ret| slotted.is_none() || matches!(ret, Slot::Open(_)) || !matches!(slotted.and_then(<[Part]>::first), Some(&Part::Hole(_))))]
fn slot_of(
    menu: &Continuations,
    pending: &[Part],
    slotted: Option<&[Part]>,
) -> Slot
{
    match slotted.and_then(<[Part]>::first) {
        Some(&Part::Hole(category)) => Slot::Open(category),
        None if menu.head() == HeadForm::Closed && pending.is_empty() => Slot::Open(Category::Item),
        Some(&Part::Tile(_)) | None => Slot::Filled,
    }
}

/// The first of `materials` that starts with a hole, with its position.
///
/// # Specification
/// trivial.
fn first_slotted(materials: &[Vec<Part>]) -> Option<(MaterialAt, &[Part])>
{
    materials
        .iter()
        .enumerate()
        .find(|&(_, material)| matches!(material.first(), Some(&Part::Hole(_))))
        .map(|(at, material)| (MaterialAt(at), material.as_slice()))
}

/// A material's position among a menu's closings.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MaterialAt(usize);

/// The candidates at a cursor whose continuations are `menu`, cut against
/// `written`, with the slot at the cursor.
///
/// # Specification
/// - ensures: the pending hole followed by each closing — the cheapest as
///   [`Origin::Closing`], the cheapest other one that starts with a hole, when
///   the cheapest does not, as [`Origin::Slot`], the rest as
///   [`Origin::Alternative`] — each cut by [`subtract`]; an alternative that
///   inserts only separators, and any candidate cut to nothing, is dropped. The
///   slot is the category of the first hole of the cheapest closing that starts
///   with one, or [`Category::Item`] when no form is open and no operator
///   waits, and [`Slot::Filled`] otherwise. An open slot adds one
///   [`Origin::Opener`] per form of its sort, that form's material followed by
///   what the slot's closing inserts after its hole; where the written text
///   fills the slot, a form ending in a hole leaves that hole to it
///   ([`Fit::Meets`]) and any other form collides. Each candidate's turn is its
///   position among those [`place`] places as it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect, category and ranking witnesses assert the
///   candidates at an open body, an open signature, a value slot, an arm and
///   the top level; dropping the slot's openers or keeping a wholly written
///   candidate changes them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| ret.0.iter().all(|candidate| !candidate.parts.is_empty()))]
fn candidates(
    grammar: &Pbg,
    forms: &Forms,
    menu: &Continuations,
    written: &Written<'_, '_>,
) -> (Vec<Candidate>, Slot)
{
    let pending = parts(grammar, menu.pending());
    let closings = closing_materials(grammar, menu, &pending);
    let found_slot = first_slotted(&closings);
    let slot = slot_of(menu, &pending, found_slot.map(|(_, material)| material));
    let slotted_at = found_slot.map(|(at, _)| at.0);
    let slotted = found_slot.map(|(_, material)| material.to_vec());
    let mut materials: Vec<(Origin, Vec<Part>)> = closings
        .into_iter()
        .map(|material| (Origin::Alternative, material))
        .collect();
    if let Some(&mut (ref mut origin, _)) = materials.first_mut() {
        *origin = Origin::Closing;
    }
    if let Some(&mut (ref mut origin @ Origin::Alternative, _)) =
        slotted_at.and_then(|at| materials.get_mut(at))
    {
        *origin = Origin::Slot;
    }
    let mut found: Vec<Candidate> = Vec::new();
    let push = |found: &mut Vec<Candidate>, origin: Origin, parts: Vec<Part>, fit: Fit| {
        let placed = place(origin, slot);
        let turn = Turn(
            found
                .iter()
                .filter(|other| place(other.origin, slot) == placed)
                .count(),
        );
        found.push(Candidate {
            origin,
            parts,
            fit,
            turn,
        });
    };
    for (origin, mut material) in materials {
        let trailing = trailing(&material);
        let fit = subtract(&mut material, written);
        let separators_only = material
            .iter()
            .all(|part| matches!(part, Part::Tile(tile) if matches!(tile.0, ";" | ",")));
        let variant = origin != Origin::Closing && (separators_only || trailing == Trailing::Comma);
        if material.is_empty() || variant {
            continue;
        }
        push(&mut found, origin, material, fit);
    }
    if let Slot::Open(category) = slot {
        // What the slot's closing inserts after its hole, once cut against the
        // written text; nothing when the written text already fills the slot.
        let rest = slotted.map(|mut material| {
            let fit = subtract(&mut material, written);
            let after = material.get(1 ..).map(<[Part]>::to_vec).unwrap_or_default();
            if material.is_empty() {
                Rest::Written
            }
            else {
                Rest::Unwritten(after, fit)
            }
        });
        for form in forms.of(category.sort()) {
            let mut material = form.material.clone();
            let fit = match rest {
                Some(Rest::Unwritten(ref after, fit)) => {
                    material.extend(after.iter().copied());
                    fit
                },
                // The written text fills the slot: a form ending in a hole
                // takes it as that hole's filling, any other form collides.
                Some(Rest::Written) => {
                    if let Some(&Part::Hole(_)) = material.last() {
                        material.pop();
                        Fit::Meets
                    }
                    else {
                        Fit::Collides
                    }
                },
                None => whole_fit(&material, written),
            };
            push(&mut found, Origin::Opener(form.yields), material, fit);
        }
    }
    (found, slot)
}

/// What the text before the cursor ends in, which a ghost text must close
/// before code can follow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Lead
{
    /// Code: nothing to close.
    Code,
    /// A line comment or a shebang line, closed by the line end.
    Line,
    /// A block comment not yet closed.
    Block,
}

/// What `before`, labeled as `tokens`, ends in.
///
/// # Specification
/// - ensures: [`Lead::Line`] when the last token is layout starting with `//`
///   or `#!`; [`Lead::Block`] when it starts with `/*` and does not end with
///   `*/`; [`Lead::Code`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the comment witness asserts a line comment's line end and
///   a block comment's `*/`; reading a closed block comment as open adds a
///   stray `*/`.
/// - witness: `inline::tests::a_comment_is_closed_before_code_follows`
#[spec(ensures: |ret| matches!(ret, Lead::Code) || tokens.last().is_some_and(|last| last.lexeme == Lexeme::Space))]
fn lead(
    before: SourceText<'_>,
    tokens: &[Token],
) -> Lead
{
    let before = <&str>::from(before);
    let Some(last) = tokens.last().filter(|last| last.lexeme == Lexeme::Space)
    else {
        return Lead::Code;
    };
    let start = usize::try_from(last.start).unwrap_or(usize::MAX);
    let layout = before.get(start ..).unwrap_or_default();
    if layout.starts_with("//") || layout.starts_with("#!") {
        Lead::Line
    }
    else if layout.starts_with("/*") && !layout.ends_with("*/") {
        Lead::Block
    }
    else {
        Lead::Code
    }
}

impl Labeled<'_>
{
    /// The ghost texts `grammar`, whose forms are `forms`, offers at byte `at`
    /// of this text, best first.
    ///
    /// # Specification
    /// - requires: `forms` is [`Forms::new`] of `grammar`; any offset, one past
    ///   the text or inside a character read as the nearest character boundary
    ///   at or before it.
    /// - ensures: between one and eight snippets, none holding a `?` tab stop:
    ///   the candidates of the top-level form the cursor ends, molded alone up
    ///   to the cursor, cut against the significant tokens after the cursor and
    ///   ordered by [`rank`], each spelled once as [`spell`] states; the
    ///   placeholder of the slot at the cursor when no candidate remains.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one relabeling of the text before the cursor from this
    ///   labeling, which rescans from the cursor's previous line, then
    ///   [`ghost_before`](Self::ghost_before)'s work at that cut.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect rows, one cursor per category, comments
    ///   and the ranking golden assert exact answers, and every cursor of a
    ///   corpus source cut from its labeled text answers as the text before it
    ///   labeled afresh; L2 — every cursor of every corpus source, with and
    ///   without the text after it, answers at least one snippet and none with
    ///   `?`. Refusing a continued line, spelling a hole as `?`, repeating a
    ///   written closer or answering nothing changes one of them.
    /// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
    /// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
    /// - witness: `inline::tests::a_comment_is_closed_before_code_follows`
    /// - witness: `inline::tests::the_ranking_is_pinned`
    /// - witness: `inline::tests::a_cut_answers_as_its_text_labeled_afresh_594`
    /// - witness: `inline::tests::sweeps::every_corpus_cursor_has_a_ghost_text`
    #[must_use]
    #[spec(ensures: |ret| (1 ..= SHOWN).contains(&ret.0.len()) && ret.0.iter().all(|snippet| !snippet.0.contains(":?}")))]
    pub fn ghost(
        &self,
        grammar: &Pbg,
        forms: &Forms,
        at: ByteOffset,
    ) -> Ghosts
    {
        let whole = <&str>::from(self.text);
        let at = whole.floor_char_boundary(usize::from(at));
        if at == whole.len() {
            self.ghost_before(self, grammar, forms)
        }
        else {
            self.ghost_before(&self.cut(ByteOffset::from(at)), grammar, forms)
        }
    }

    /// The ghost texts `grammar`, whose forms are `forms`, offers where
    /// `before` ends in this text, best first: [`ghost`](Self::ghost) at that
    /// byte, its cut given.
    ///
    /// A caller asking at one cursor of a text with and without the text
    /// after it cuts once and asks both here. Under specification
    /// enforcement [`Labeling::relabel`]'s contract labels both texts whole,
    /// so a cut costs two labelings, and a second cut at the same cursor two
    /// more.
    ///
    /// # Specification
    /// - requires: `forms` is [`Forms::new`] of `grammar`; `before` is this
    ///   text or its [`cut`](Self::cut) at a character boundary.
    /// - ensures: [`ghost`](Self::ghost)'s answer at the byte where `before`
    ///   ends.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one molding of the form the cursor ends, one bounded walk
    ///   of its open form, and grammar reads only for the words a candidate is
    ///   cut against; the written tokens are read off this labeling and the
    ///   forms the slot can open off `forms`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the defect rows, one cursor per category, comments
    ///   and the ranking golden assert [`ghost`](Self::ghost)'s exact answers
    ///   through this function; L2 — every cursor of every corpus source, cut
    ///   once and asked with and without the text after it, answers at least
    ///   one snippet and none with `?`.
    /// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
    /// - witness: `inline::tests::the_ranking_is_pinned`
    /// - witness: `inline::tests::sweeps::every_corpus_cursor_has_a_ghost_text`
    #[must_use]
    #[spec(
        requires: <&str>::from(self.text).starts_with(<&str>::from(before.text)),
        ensures: |ret| (1 ..= SHOWN).contains(&ret.0.len()) && ret.0.iter().all(|snippet| !snippet.0.contains(":?}")),
    )]
    pub fn ghost_before(
        &self,
        before: &Labeled<'_>,
        grammar: &Pbg,
        forms: &Forms,
    ) -> Ghosts
    {
        let whole = <&str>::from(self.text);
        let at = <&str>::from(before.text).len();
        let tokens = before.labeling.tokens();
        let source = before.text;
        let after = SourceText::from(whole.get(at ..).unwrap_or_default());
        let lead = lead(source, tokens);
        let mut molder = Molder::new(grammar);
        let mut state = MeldState::new(grammar);
        if let Some(&form) = molder.form_runs(tokens, source).last() {
            molder.mold_run(&mut state, tokens, form, source);
        }
        let written = Written::after(grammar, self, ByteOffset::from(at));
        let menu = state.continuations(ClosingLimit::from(CLOSINGS));
        let (mut found, slot) = candidates(grammar, forms, &menu, &written);
        found.sort_by_key(|candidate| rank(candidate, slot));
        // At most `SHOWN` ghost texts are kept, so each search below reads an
        // array of that length.
        let mut shown: [Option<Snippet>; SHOWN] = [const { None }; SHOWN];
        // A candidate that differs from a better one only by separators — a
        // trailing `,` or `;` — adds nothing an author asks for.
        let mut skeletons: [Option<Vec<Part>>; SHOWN] = [const { None }; SHOWN];
        let mut kept = 0_usize;
        for candidate in &found {
            let skeleton = skeleton(&candidate.parts);
            if skeletons
                .iter()
                .any(|held| held.as_ref() == Some(&skeleton))
            {
                continue;
            }
            let snippet = spell(&candidate.parts, lead, source, after);
            if shown.iter().any(|held| held.as_ref() == Some(&snippet)) {
                continue;
            }
            let (Some(shown_at), Some(skeleton_at)) =
                (shown.get_mut(kept), skeletons.get_mut(kept))
            else {
                break;
            };
            *shown_at = Some(snippet);
            *skeleton_at = Some(skeleton);
            kept = kept.saturating_add(1);
            if kept == SHOWN {
                break;
            }
        }
        let mut ghosts: Vec<Snippet> = Vec::with_capacity(kept.max(1));
        ghosts.extend(shown.into_iter().flatten());
        if ghosts.is_empty() {
            let category = match (slot, menu.head()) {
                (Slot::Open(category), _) => category,
                (Slot::Filled, HeadForm::Open { mold, .. }) => {
                    Category::of_hole(grammar, state.expected_operand_sort(), mold)
                },
                (Slot::Filled, HeadForm::Closed) => Category::Item,
            };
            ghosts.push(spell(&[Part::Hole(category)], lead, source, after));
        }
        Ghosts(ghosts)
    }

    /// Where the word this text ends in starts: the start of its last token
    /// when that token is a word ending where the text ends, else the text's
    /// end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: at most the text's length; the start of the last token when
    ///   it is a lowercase- or an uppercase-led word ending at the text's end.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the completion witnesses complete `de` from its start
    ///   and offer every name after an open bracket; reading the word from its
    ///   end, or a bracket as a word, changes them.
    /// - witness: `complete::tests::a_prefix_offers_only_what_starts_with_it`
    #[must_use]
    #[spec(ensures: |ret| usize::from(ret) <= <&str>::from(self.text).len())]
    pub fn word_start(&self) -> ByteOffset
    {
        let end = <&str>::from(self.text).len();
        let start = self
            .labeling
            .tokens()
            .last()
            .filter(|token| {
                matches!(token.lexeme, Lexeme::LowerWord | Lexeme::UpperWord)
                    && usize::try_from(token.end).is_ok_and(|ended| ended == end)
            })
            .and_then(|token| usize::try_from(token.start).ok())
            .unwrap_or(end);
        ByteOffset::from(start)
    }

    /// The slot where this text ends: the category of the hole standing
    /// there, when one does and the text ends in code.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Slot::Filled`] when the text ends in a comment, a string or
    ///   a shebang line; otherwise the slot [`ghost`](Self::ghost) reads at the
    ///   text's end, from the top-level form the text ends molded alone.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one molding of the form the text ends and one bounded walk
    ///   of its open form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the completion witnesses read a value, a computation,
    ///   a type, a pattern and an item slot, and a binding name's slot filled.
    /// - witness: `complete::tests::each_slot_offers_its_own_names`
    #[must_use]
    #[spec(ensures: |ret| lead(self.text, self.labeling.tokens()) == Lead::Code || ret == Slot::Filled)]
    pub fn slot(
        &self,
        grammar: &Pbg,
    ) -> Slot
    {
        let tokens = self.labeling.tokens();
        if lead(self.text, tokens) != Lead::Code {
            return Slot::Filled;
        }
        let mut molder = Molder::new(grammar);
        let mut state = MeldState::new(grammar);
        if let Some(&form) = molder.form_runs(tokens, self.text).last() {
            molder.mold_run(&mut state, tokens, form, self.text);
        }
        let menu = state.continuations(ClosingLimit::from(CLOSINGS));
        let pending = parts(grammar, menu.pending());
        let closings = closing_materials(grammar, &menu, &pending);
        slot_of(
            &menu,
            &pending,
            first_slotted(&closings).map(|(_, material)| material),
        )
    }
}

/// The ghost texts `grammar`, whose forms are `forms`, offers at byte `at` of
/// `text`, best first.
///
/// # Specification
/// - requires: `forms` is [`Forms::new`] of `grammar`.
/// - ensures: [`Labeled::ghost`]'s answer at `at` of `text` labeled once.
/// - provides: the answer to `textDocument/inlineCompletion`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect rows, one cursor per category, comments and
///   the ranking golden assert this function's exact answers.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| (1 ..= SHOWN).contains(&ret.0.len()))]
pub fn ghost(
    grammar: &Pbg,
    forms: &Forms,
    text: SourceText<'_>,
    at: ByteOffset,
) -> Ghosts
{
    Labeled::new(text).ghost(grammar, forms, at)
}

/// Append `text` to `snippet` as literal text: each character the snippet
/// syntax reads specially (`$`, `}` and `\`) behind a backslash.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `snippet` grows by `text` with a `\` before each `$`, `}` and
///   `\`, and by nothing else.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a keyword's form and a call's parameters reach it with
///   and without characters to escape.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `complete::tests::a_call_fills_its_parameters_as_tab_stops`
#[spec(
    captures: before = snippet.len(),
    ensures: before
        .checked_add(<&str>::from(text).len())
        .and_then(|grown| grown.checked_add(<&str>::from(text).matches(['$', '}', '\\']).count()))
        == Some(snippet.len()),
)]
pub fn escape_into(
    snippet: &mut String,
    text: SourceText<'_>,
)
{
    for character in <&str>::from(text).chars() {
        if matches!(character, '$' | '}' | '\\') {
            snippet.push('\\');
        }
        snippet.push(character);
    }
}

/// `parts` spelled as a snippet to insert between `before` and `after`,
/// behind `lead`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the lead's closer first — a line end for [`Lead::Line`], `*/` for
///   [`Lead::Block`] — then each part in order: a tile as the text
///   [`tile_spelling`] gives it, escaped for the snippet syntax; a lexical
///   class as a tab stop naming the class; a hole as a tab stop naming its
///   category; a string the closing leaves empty, a tab stop naming its content
///   between its quotes. Tab stops are numbered from 1 in order. Parts are
///   separated by one space, and the first from what precedes it by one, except
///   after a line end, an opening bracket or whitespace and before a closing
///   bracket, a comma, a semicolon or a quote; one space ends the snippet when
///   `after` begins with text the same rule would space from its last part.
/// - provides: one ghost text's snippet.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the defect, category, comment and ranking witnesses
///   assert tiles, classes, holes, escapes, leads and each spacing rule at
///   exact snippets; the ranking golden spaces `hold` from a written operand.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::a_comment_is_closed_before_code_follows`
/// - witness: `inline::tests::the_ranking_is_pinned`
#[spec(ensures: |ret| !ret.0.contains(":?}") && (parts.is_empty() || !ret.0.is_empty())
    && (!matches!(lead, Lead::Line) || ret.0.starts_with('\n')))]
fn spell(
    parts: &[Part],
    lead: Lead,
    before: SourceText<'_>,
    after: SourceText<'_>,
) -> Snippet
{
    let joins = |last: Option<char>| match last {
        Some(character) if !character.is_whitespace() && !matches!(character, '(' | '[') => {
            Spacing::Spaced
        },
        Some(_) | None => Spacing::Tight,
    };
    let mut snippet = String::new();
    let mut joint = joins(<&str>::from(before).chars().next_back());
    match lead {
        Lead::Code => {},
        Lead::Line => {
            snippet.push('\n');
            joint = Spacing::Tight;
        },
        Lead::Block => {
            if joint == Spacing::Spaced {
                snippet.push(' ');
            }
            snippet.push_str("*/");
            joint = Spacing::Spaced;
        },
    }
    let mut stop = 0_u32;
    let mut quoting = Quoting::Outside;
    // Whether the last piece opened a string, which a closing quote next would
    // leave empty.
    let mut hollow = false;
    for &part in parts {
        let piece = match part {
            Part::Tile(tile) => match tile_spelling(CandidateLabel::from(tile.0)) {
                TileSpelling::Literal(text) => Piece::Text(text),
                TileSpelling::Class(class) => Piece::Stop(class),
            },
            Part::Hole(category) => category.placeholder(),
        };
        // A quote opens a string where none is open, and closes it otherwise:
        // the opening quote stands apart, the string's contents against it.
        let quote = matches!(piece, Piece::Text("\"" | "'"));
        let spacing = match (quote, quoting) {
            (true, Quoting::Outside) => Spacing::Spaced,
            (true, Quoting::Inside) | (false, _) => piece.spacing(),
        };
        if joint == Spacing::Spaced && spacing == Spacing::Spaced {
            snippet.push(' ');
        }
        if quote && hollow {
            stop = stop.saturating_add(1);
            let _written = write!(snippet, "${{{stop}:string_fragment}}");
        }
        hollow = matches!(piece, Piece::Text("\"")) && quoting == Quoting::Outside;
        match piece {
            Piece::Text(text) => {
                escape_into(&mut snippet, SourceText::from(text));
                joint = joins(text.chars().next_back());
            },
            Piece::Stop(name) => {
                stop = stop.saturating_add(1);
                let _written = write!(snippet, "${{{stop}:{name}}}");
                joint = Spacing::Spaced;
            },
        }
        if quote {
            quoting = match quoting {
                Quoting::Outside => {
                    joint = Spacing::Tight;
                    Quoting::Inside
                },
                Quoting::Inside => Quoting::Outside,
            };
        }
    }
    let next = <&str>::from(after).chars().next();
    let next_spaced = next.is_some_and(|character| {
        !character.is_whitespace() && !matches!(character, ')' | ']' | '}' | ',' | ';' | '"' | '\'')
    });
    if !parts.is_empty() && joint == Spacing::Spaced && next_spaced {
        snippet.push(' ');
    }
    Snippet(snippet)
}

/// Whether a string is open at a point of a snippet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Quoting
{
    /// No string is open.
    Outside,
    /// A string is open.
    Inside,
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
            Self::Text(")" | "]" | "," | ";" | "\"" | "'") => Spacing::Tight,
            Self::Text(_) | Self::Stop(_) => Spacing::Spaced,
        }
    }
}

#[cfg(test)]
mod tests
{
    use core::fmt::Write as _;

    use expect_test::expect;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_syntax::SourceText;

    use super::Fit;
    use super::Forms;
    use super::Labeled;
    use super::Part;
    use super::Spelled;
    use super::TileLabel;
    use super::Written;
    use super::ghost;
    use super::subtract;
    use super::typed;
    use super::whole_fit;

    /// The built-in grammar and its forms.
    struct Tools
    {
        /// The grammar.
        grammar: Pbg,
        /// Its forms.
        forms: Forms,
    }

    /// The built-in grammar and its forms, built.
    ///
    /// # Specification
    /// trivial.
    fn tools() -> Tools
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let forms = Forms::new(&grammar);
        Tools { grammar, forms }
    }

    /// The ghost texts between `before` and `after`, best first.
    ///
    /// # Specification
    /// trivial.
    fn between(
        tools: &Tools,
        before: SourceText<'_>,
        after: SourceText<'_>,
    ) -> Vec<String>
    {
        let before = <&str>::from(before);
        let text = format!("{before}{}", <&str>::from(after));
        let at = ByteOffset::from(before.len());
        ghost(
            &tools.grammar,
            &tools.forms,
            SourceText::from(text.as_str()),
            at,
        )
        .into_iter()
        .map(String::from)
        .collect()
    }

    #[test]
    fn a_separator_or_a_closer_is_never_typed_as_its_own_text()
    {
        for label in [";", ",", ")", "]", "}"] {
            assert_eq!(typed(TileLabel(label)), Spelled::Unwritten, "{label:?}");
        }
        assert_eq!(
            typed(TileLabel("(")),
            Spelled::Written,
            "an opener is typed"
        );
    }

    #[test]
    fn parts_inserted_whole_collide_only_when_they_end_closed_before_an_operand()
    {
        let tools = tools();
        let written = |text: &'static str| {
            Written::after(
                &tools.grammar,
                &Labeled::new(SourceText::from(text)),
                ByteOffset::from(0_usize),
            )
        };
        let closed = [Part::Tile(TileLabel(")"))];
        let open = [Part::Tile(TileLabel("("))];
        assert_eq!(whole_fit(&closed, &written("1")), Fit::Collides);
        assert_eq!(
            whole_fit(&closed, &written("")),
            Fit::Free,
            "nothing written after"
        );
        assert_eq!(
            whole_fit(&open, &written("1")),
            Fit::Free,
            "an opener before an operand"
        );
    }

    #[test]
    fn a_written_closer_pairs_only_past_the_brackets_written_before_it()
    {
        let tools = tools();
        let mut parts = Vec::from([Part::Tile(TileLabel(")"))]);
        let written = Written::after(
            &tools.grammar,
            &Labeled::new(SourceText::from("[1])")),
            ByteOffset::from(0_usize),
        );
        assert_eq!(subtract(&mut parts, &written), Fit::Meets);
        assert_eq!(
            parts,
            [],
            "the written `)` closes the bracket the part would"
        );
        let mut parts = Vec::from([Part::Tile(TileLabel(")"))]);
        let written = Written::after(
            &tools.grammar,
            &Labeled::new(SourceText::from("1]")),
            ByteOffset::from(0_usize),
        );
        assert_ne!(
            subtract(&mut parts, &written),
            Fit::Meets,
            "a `]` is not its pair"
        );
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "a snippet's tab stop is spelled `${n:name}`, which reads as a format argument"
    )]
    fn the_defect_rows_answer_as_wanted()
    {
        let tools = tools();
        let body = "def f(x: Integer) -> -F Integer {";
        // The body's closer is written, on the cursor's line or the next: the
        // body's contents are what is missing, and no `}` is repeated.
        for after in ["}", "\n}"] {
            let found = between(&tools, SourceText::from(body), SourceText::from(after));
            assert_eq!(
                found.first().map(String::as_str),
                Some(" ${1:computation}"),
                "{after:?} after the open body"
            );
            assert!(
                found.iter().all(|ghost| !ghost.contains("\\}")),
                "{after:?}: no ghost text repeats the written closer: {found:?}"
            );
        }
        // An open signature offers the body, and the return type before it.
        let found = between(
            &tools,
            SourceText::from("def f(x: Integer"),
            SourceText::from(""),
        );
        assert_eq!(
            found.first().map(String::as_str),
            Some(") { ${1:computation} \\}")
        );
        assert!(
            found
                .iter()
                .any(|ghost| ghost == ") -> ${1:type} { ${2:computation} \\}"),
            "the return type is offered: {found:?}"
        );
        // Inside an auto-closed pair the answer is the pair's contents: no
        // ghost text closes more than it opens, nor ends the definition.
        let unbalanced = |ghost: &String| ghost.matches(')').count() > ghost.matches('(').count();
        let found = between(
            &tools,
            SourceText::from("def x = ("),
            SourceText::from(");"),
        );
        assert_eq!(found.first().map(String::as_str), Some("${1:value}"));
        assert!(
            found
                .iter()
                .all(|ghost| !unbalanced(ghost) && !ghost.ends_with(';')),
            "no ghost text repeats the written `);`: {found:?}"
        );
        // A closer past a nested pair still pairs with the open one.
        let found = between(
            &tools,
            SourceText::from("def x = ( 1"),
            SourceText::from(" + (2))"),
        );
        assert!(
            found.iter().all(|ghost| !unbalanced(ghost)),
            "the written `)` after a nested pair is not repeated: {found:?}"
        );
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "a snippet's tab stop is spelled `${n:name}`, which reads as a format argument"
    )]
    fn each_category_is_named_where_its_hole_stands()
    {
        let tools = tools();
        for (before, after, first) in [
            ("def x = thunk { return", " }", " ${1:value}"),
            ("def x = thunk {", " }", " ${1:computation}"),
            (
                "def f(x: Nat) -> -F Nat { run y <-",
                "",
                " ${1:computation}; \\}",
            ),
            ("def g :", "", " ${1:type};"),
            ("def g : Integer ≃", "", " ${1:type};"),
            ("def g : Integer <~>", "", " ${1:type};"),
            ("def g : Integer ≅", "", " ${1:type};"),
            ("def g : Integer ⇝", "", " ${1:type};"),
            ("def g : Integer ~~>", "", " ${1:type};"),
            (
                "def f(x: Nat) -> -F Nat {\n  case x {",
                " }\n}",
                " ${1:pattern} => ${2:computation}",
            ),
            ("module M {", "\n}", " ${1:member}"),
            ("", "", "def ${1:identifier} : ${2:type};"),
        ] {
            let found = between(&tools, SourceText::from(before), SourceText::from(after));
            assert_eq!(
                found.first().map(String::as_str),
                Some(first),
                "{before:?} ‸ {after:?}: {found:?}"
            );
        }
    }

    /// #594: a cut of a labeled text is the text before the cursor labeled
    /// afresh, at every byte of a source whose lexical modes nest — a doc
    /// comment, a block comment over two lines, a string with an escape and
    /// interpolations, a character wider than a byte and a block comment left
    /// open — so a ghost text read off the cut answers as before.
    #[test]
    fn a_cut_answers_as_its_text_labeled_afresh_594()
    {
        let text = concat!(
            "/// A doc line.\n",
            "def greet(name: String) -> -F String {\n",
            "  /* a block\n",
            "     comment */ return \"hello ${name}, \\\"quoted\\\" ${ { 1 } }\";\n",
            "}\n",
            "def g : Integer ⇝ Integer; // a trailing comment\n",
            "def x = (1 + [2, 3]) /* open",
        );
        let whole = Labeled::new(SourceText::from(text));
        for at in 0 ..= text.len() {
            let before = text
                .get(.. text.floor_char_boundary(at))
                .expect("a floor is a character boundary");
            let cut = whole.cut(ByteOffset::from(at));
            assert_eq!(cut.text, SourceText::from(before), "{at}");
            assert_eq!(
                cut.labeling,
                Labeled::new(SourceText::from(before)).labeling,
                "{at}: the cut relabels as the text before it labels"
            );
        }
    }

    /// A ghost text lends the text it inserts: the snippet a declaration's
    /// type hole offers reads back as written.
    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "a snippet's tab stop is spelled `${n:name}`, which reads as a format argument"
    )]
    fn a_snippet_lends_the_text_it_inserts()
    {
        let tools = tools();
        let ghosts = ghost(
            &tools.grammar,
            &tools.forms,
            SourceText::from("def g :"),
            ByteOffset::from(7_usize),
        );
        assert_eq!(
            ghosts.as_ref().first().map(AsRef::as_ref),
            Some(" ${1:type};")
        );
    }

    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "a snippet's tab stop is spelled `${n:name}`, which reads as a format argument"
    )]
    fn a_comment_is_closed_before_code_follows()
    {
        let tools = tools();
        for (before, first) in [
            ("def x = 1; // note", "\ndef ${1:identifier} : ${2:type};"),
            ("def x = 1; /* note", " */ def ${1:identifier} : ${2:type};"),
            ("def x = 1; /* note */", " def ${1:identifier} : ${2:type};"),
            ("def x = // note", "\n${1:value};"),
        ] {
            let found = between(&tools, SourceText::from(before), SourceText::from(""));
            assert_eq!(
                found.first().map(String::as_str),
                Some(first),
                "{before:?}: {found:?}"
            );
        }
    }

    #[test]
    #[expect(
        clippy::use_debug,
        reason = "the golden shows each cursor and snippet as its string literal, layout and \
                  escapes visible"
    )]
    fn the_ranking_is_pinned()
    {
        let tools = tools();
        let mut rendered = String::new();
        for (before, after) in [
            ("def f(x: Integer) -> -F Integer {", "\n}"),
            ("def f(x: Integer", ""),
            ("def x = (", ")"),
            ("def x = ", "answer;"),
            ("def f(x: Nat) -> -F Nat {\n  case x {", " }\n}"),
            ("data Nat : Type {\n  Zero : Nat;", "\n}"),
            ("def x = (", ") + 1;"),
            ("def x = (", "1 + 2)"),
            ("def x = (", "(1))"),
            ("def x = (", "(1), 2)"),
            ("def x = [", "1, 2]"),
            ("def x = thunk {", " return 1 }"),
            ("def x = thunk { return", " 1; }"),
            ("def x = ", "(1) 2;"),
            ("def x = ", "def"),
            ("def x = (", "[1])"),
            ("def x = 1 +", ";"),
            ("def x = 1 +", ""),
            ("def x = (1 +", ""),
            ("1 +", ""),
            ("", ""),
        ] {
            let _written = writeln!(rendered, "{before:?} ‸ {after:?}");
            for ghost in between(&tools, SourceText::from(before), SourceText::from(after)) {
                let _written = writeln!(rendered, "  {ghost:?}");
            }
        }
        expect![[r#"
            "def f(x: Integer) -> -F Integer {" ‸ "\n}"
              " ${1:computation}"
              " pure ${1:value}"
              " return ${1:value}"
              " val ${1:pattern} = ${2:value};"
              " become ${1:computation}"
              " run ${1:pattern} <- ${2:computation};"
              " force ${1:value}"
              " leta ${1:identifier} = ${2:value};"
            "def f(x: Integer" ‸ ""
              ") { ${1:computation} \\}"
              ") -> ${1:type} { ${2:computation} \\}"
              ", ${1:identifier}) { ${2:computation} \\}"
              ", ${1:type_variable}) { ${2:computation} \\}"
              ", ${1:type_identifier}) { ${2:computation} \\}"
            "def x = (" ‸ ")"
              "${1:value}"
              "- ${1:value}"
              "${1:value} : ${2:type}"
              "run ${1:computation}"
              "hold ${1:value}"
              "()"
              "type(${1:type})"
              "[${1:value}]"
            "def x = " ‸ "answer;"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def f(x: Nat) -> -F Nat {\n  case x {" ‸ " }\n}"
              " ${1:pattern} => ${2:computation}"
              " _ => ${1:computation}"
              " | ${1:pattern} => ${2:computation}"
              " #{ ${1:pattern} \\} => ${2:computation}"
              " ${1:pattern} => ${2:computation}, ${3:pattern} => ${4:computation}"
              " + { . ${1:identifier} = ${2:pattern} \\} => ${3:computation}"
              " ${1:pattern} => ${2:computation}, | ${3:pattern} => ${4:computation}"
              " [${1:pattern}] => ${2:computation}"
            "data Nat : Type {\n  Zero : Nat;" ‸ "\n}"
              " ${1:constructor}"
              " ${1:constructor} : ${2:type}"
              " rule ${1:value} ==> ${2:value}"
              " rule ${1:value} <=> ${2:value}"
              " rule ${1:value} ~> ${2:value}"
              " ${1:constructor} [${2:identifier}]"
            "def x = (" ‸ ") + 1;"
              "${1:value}"
              "- ${1:value}"
              "${1:value} : ${2:type}"
              "run ${1:computation}"
              "hold ${1:value}"
              "()"
              "type(${1:type})"
              "[${1:value}]"
            "def x = (" ‸ "1 + 2)"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = (" ‸ "(1))"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = (" ‸ "(1), 2)"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = [" ‸ "1, 2]"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = thunk {" ‸ " return 1 }"
              " pure"
              " val"
              " return"
              " run"
              " become"
              " leta ${1:identifier} ="
              " force"
              " hold ${1:identifier} ="
            "def x = thunk { return" ‸ " 1; }"
              " -"
              " run"
              " hold"
              " pure"
              " return"
              " become"
              " force"
              " ()"
            "def x = " ‸ "(1) 2;"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = " ‸ "def"
              "${1:value}; "
              "- ${1:value}; "
              "run ${1:computation}; "
              "hold ${1:value}; "
              "(); "
              "type(${1:type}); "
              "[${1:value}]; "
              "thunk { ${1:computation} \\}; "
            "def x = (" ‸ "[1])"
              "- "
              "run "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
            "def x = 1 +" ‸ ";"
              " ${1:value}"
              " - ${1:value}"
              " run ${1:computation}"
              " hold ${1:value}"
              " ()"
              " type(${1:type})"
              " [${1:value}]"
              " thunk { ${1:computation} \\}"
            "def x = 1 +" ‸ ""
              " ${1:value};"
              " - ${1:value};"
              " run ${1:computation};"
              " hold ${1:value};"
              " ();"
              " type(${1:type});"
              " [${1:value}];"
              " thunk { ${1:computation} \\};"
            "def x = (1 +" ‸ ""
              " ${1:value})"
              " - ${1:value})"
              " ${1:value} : ${2:type})"
              " run ${1:computation})"
              " hold ${1:value})"
              " ())"
              " type(${1:type}))"
              " [${1:value}])"
            "1 +" ‸ ""
              " ${1:value}"
              " - ${1:value}"
              " run ${1:computation}"
              " hold ${1:value}"
              " ()"
              " type(${1:type})"
              " [${1:value}]"
              " thunk { ${1:computation} \\}"
            "" ‸ ""
              "def ${1:identifier} : ${2:type};"
              "data ${1:type_identifier} { \\}"
              "codata ${1:type_identifier} { \\}"
              "module ${1:type_identifier} { ${2:member} \\}"
              "import \"${1:string_fragment}\";"
              "world ${1:identifier};"
              "op infixl ${1:number} \"${2:string_fragment}\";"
              "rec { ${1:item} \\}"
        "#]]
        .assert_eq(&rendered);
    }

    /// The ghost-text sweep: every cursor of each corpus source, in the whole
    /// text and in the prefix before it, each source labeled once; a pull
    /// request reads a long source's cursors further apart (`MOLDED_BYTES`).
    mod sweeps
    {
        use gandr_surface_grammar::Pbg;
        use gandr_surface_render_remote::ByteOffset;
        use gandr_surface_syntax::SourceText;
        use gandr_workflow_sweep::Coverage;
        use gandr_workflow_sweep::Sample;
        use gandr_workflow_sweep::SampleName;
        use gandr_workflow_sweep::SampleSize;
        use gandr_workflow_sweep::Sweep;
        use gandr_workflow_sweep::corpus;

        use super::super::Labeled;
        use super::super::Molder;
        use super::tools;

        /// The sample: twenty-four sources, ranked by their BLAKE3 digest under
        /// this name, at least one of each corpus class — `strict` and each
        /// directory below `fixture` — and every source the change adds or
        /// modifies (`gandr-workflow-sweep`). The `sweeps` profile reads every
        /// source.
        const SAMPLE: Sample = Sample {
            name: SampleName("every_corpus_cursor_has_a_ghost_text"),
            size: SampleSize(24),
        };

        /// Every source's cursors are read without specification enforcement;
        /// the enforcing build checks every contract on every call and reads
        /// every sixth cursor, in every run.
        const CURSOR_STRIDE: usize = if cfg!(anodized_panic) { 6 } else { 1 };

        /// The most bytes a sampled run lets the requests over one source
        /// mold. A request molds the form its cursor ends, from the form's
        /// start to the cursor, so a form of `n` bytes costs its cursors
        /// `n (n + 1) / 2` bytes and a source the sum over its forms: about
        /// half a microsecond a byte without enforcement, so the λ-calculus's
        /// syntax model, 3.1 MB molded, took 1.3 s at every cursor and the
        /// corpus's median source a few milliseconds. A source past it is read
        /// at cursors as many times further apart as keep it within; the
        /// `sweeps` profile reads every source at the stride above.
        const MOLDED_BYTES: usize = 0x0004_0000;

        /// The bytes the requests over a source mold.
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
        struct Molded(usize);

        /// The bytes the requests at every cursor of `whole` mold, each from
        /// the start of the form its cursor ends.
        ///
        /// # Specification
        /// trivial.
        fn molded(
            whole: &Labeled<'_>,
            grammar: &Pbg,
        ) -> Molded
        {
            let text = <&str>::from(whole.text);
            let tokens = whole.labeling.tokens();
            let starts: Vec<usize> = Molder::new(grammar)
                .form_runs(tokens, whole.text)
                .iter()
                .filter_map(|run| tokens.get(usize::from(run.start())))
                .filter_map(|token| usize::try_from(token.start).ok())
                .chain([text.len()])
                .collect();
            Molded(
                starts
                    .windows(2)
                    .map(|pair| match *pair {
                        [from, to] => {
                            let length = to.saturating_sub(from);
                            length
                                .saturating_mul(length.saturating_add(1))
                                .div_euclid(2)
                        },
                        _ => 0,
                    })
                    .fold(0, usize::saturating_add),
            )
        }

        /// How many cursors apart a run reads a source; at least one.
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Stride(usize);

        /// How many cursors apart a run reads `whole`: [`CURSOR_STRIDE`] under
        /// the `sweeps` profile, and as many times that as keep a sampled
        /// source's molding within [`MOLDED_BYTES`].
        ///
        /// # Specification
        /// trivial.
        fn stride(
            whole: &Labeled<'_>,
            grammar: &Pbg,
        ) -> Stride
        {
            match Coverage::asked() {
                Coverage::Full => Stride(CURSOR_STRIDE),
                Coverage::Sampled => Stride(
                    CURSOR_STRIDE
                        .saturating_mul(molded(whole, grammar).0.div_ceil(MOLDED_BYTES).max(1)),
                ),
            }
        }

        #[test]
        fn every_corpus_cursor_has_a_ghost_text()
        {
            let tools = tools();
            let sweep = Sweep::asked().expect("the run's sweep resolves");
            let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
            assert!(
                sources.len() >= SAMPLE.size.0,
                "the sample is drawn: {}",
                sources.len()
            );
            for source in sources {
                let text = std::fs::read_to_string(&source.path).expect("a corpus source reads");
                let whole = Labeled::new(SourceText::from(text.as_str()));
                let Stride(stride) = stride(&whole, &tools.grammar);
                let cursors = text.char_indices().map(|(at, _)| at).chain([text.len()]);
                for at in cursors.step_by(stride) {
                    let prefix = whole.cut(ByteOffset::from(at));
                    for labeled in [&whole, &prefix] {
                        let found = labeled.ghost_before(&prefix, &tools.grammar, &tools.forms);
                        let found = found.as_ref();
                        assert!(
                            !found.is_empty() && found.len() <= 8,
                            "{}:{at}: {} ghost texts",
                            source.name,
                            found.len()
                        );
                        assert!(
                            found
                                .iter()
                                .all(|ghost| !ghost.as_ref().contains(":?}")
                                    && ghost.as_ref() != "?"),
                            "{}:{at}: a `?` hole is offered: {found:?}",
                            source.name
                        );
                    }
                }
            }
        }
    }
}
