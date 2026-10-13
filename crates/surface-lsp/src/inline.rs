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
//! An inline-completion request labels the text before the cursor, splits it at
//! its predicted top-level form boundaries and molds the last form alone. The
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
//! The text after the cursor is input, never a refusal. The whole text is
//! labeled, and the significant tokens after the cursor, up to the first
//! closer of a bracket open at the cursor, are what is already written. A
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
const CLOSINGS: usize = 8;

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
enum Category
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
    ///   `<-`, `=>`, `become` or `#!{`, [`Category::Value`] after any other
    ///   tile, an unknown mold included; every other sort's own category.
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
            | Sort::Expression => {
                let before = grammar.mold(after).map(|def| def.label);
                match before {
                    | Ok("{" | ";" | "<-" | "=>" | "become" | "#!{") => Self::Computation,
                    | Ok(_) | Err(_) => Self::Value,
                }
            },
            | Sort::Pattern => Self::Pattern,
            | Sort::Type => Self::Type,
            | Sort::Item => Self::Item,
            | Sort::ModuleMember => Self::Member,
            | Sort::Instantiation => Self::Instantiation,
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
            | (
                Sort::Expression,
                "return" | "pure" | "become" | "case" | "if" | "fn" | "force" | "while" | "for"
                | "loop" | "break" | "continue" | "{" | "#!{" | "&",
            ) => Self::Computation,
            | (Sort::Expression, _) => Self::Value,
            | (Sort::Pattern, _) => Self::Pattern,
            | (Sort::Type, _) => Self::Type,
            | (Sort::Item, _) => Self::Item,
            | (Sort::ModuleMember, _) => Self::Member,
            | (Sort::Instantiation, _) => Self::Instantiation,
        }
    }

    /// The grammar sort whose holes the category names.
    ///
    /// # Specification
    /// trivial.
    const fn sort(self) -> Sort
    {
        match self {
            | Self::Value | Self::Computation => Sort::Expression,
            | Self::Type => Sort::Type,
            | Self::Pattern => Sort::Pattern,
            | Self::Item => Sort::Item,
            | Self::Member => Sort::ModuleMember,
            | Self::Instantiation => Sort::Instantiation,
        }
    }

    /// The tab stop a hole of the category shows.
    ///
    /// # Specification
    /// trivial.
    const fn placeholder(self) -> Piece<'static>
    {
        Piece::Stop(match self {
            | Self::Value => "value",
            | Self::Computation => "computation",
            | Self::Type => "type",
            | Self::Pattern => "pattern",
            | Self::Item => "item",
            | Self::Member => "member",
            | Self::Instantiation => "instantiation",
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
enum Slot
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
        | (Origin::Closing, _) => (Tier::Closing, Kind::Closing),
        | (Origin::Slot, _) => (Tier::Slot, Kind::Closing),
        | (Origin::Alternative, _) => (Tier::Menu, Kind::Closing),
        | (Origin::Opener(yields), Slot::Open(wanted)) if yields == wanted => {
            (Tier::Menu, Kind::Form)
        },
        | (Origin::Opener(_), Slot::Open(_) | Slot::Filled) => (Tier::Aside, Kind::Form),
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
            | Punctuation::Opens(family) => Role::Opens(family),
            | Punctuation::Closes(family) => Role::Closes(family),
            | Punctuation::Separates => Role::Separates,
            | Punctuation::Word => *self
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
    /// The significant tokens of `text` that start at or after `at`, up to and
    /// including the first closer at the cursor's bracket depth, the whole
    /// text labeled so a token after the cursor reads in its own lexical mode.
    ///
    /// # Specification
    /// - ensures: every token of `text`'s labeling that is not layout and
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
        text: SourceText<'text>,
        at: ByteOffset,
    ) -> Self
    {
        let whole = <&'text str>::from(text);
        let at = usize::from(at);
        let mut words = Vec::new();
        let mut depth = 0_usize;
        for token in label(SourceFragment::from(whole)) {
            let (Ok(start), Ok(end)) = (usize::try_from(token.start), usize::try_from(token.end))
            else {
                continue;
            };
            let Some(text) = whole.get(start .. end)
            else {
                continue;
            };
            if token.lexeme == Lexeme::Space || start < at {
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
                | Punctuation::Opens(_) => depth = depth.saturating_add(1),
                | Punctuation::Closes(_) if depth == 0 => break,
                | Punctuation::Closes(_) => depth = depth.saturating_sub(1),
                | Punctuation::Separates | Punctuation::Word => {},
            }
        }
        Self { grammar, words }
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
                | Ok(Sort::Item) => return Role::Heads,
                | Ok(_) => role = Role::Operand,
                | Err(_) => {},
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
///   nested pair, and the ranking golden keeps an uncut closing. Cutting at a
///   closer of another family, or not counting nested brackets, changes them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::the_ranking_is_pinned`
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
                | Role::Opens(_) => depth = depth.saturating_add(1),
                | Role::Closes(_) | Role::Separates | Role::Heads | Role::Keyword if depth == 0 => {
                    break;
                },
                | Role::Closes(_) => depth = depth.saturating_sub(1),
                | Role::Separates | Role::Heads | Role::Keyword | Role::Operand => {},
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
                | Punctuation::Opens(_) => depth = depth.saturating_add(1),
                | Punctuation::Closes(closed) if depth == 0 => return closed == family,
                | Punctuation::Closes(_) => depth = depth.saturating_sub(1),
                | Punctuation::Separates | Punctuation::Word => {},
            }
        }
        false
    };
    let cut = parts
        .iter()
        .enumerate()
        .position(|(index, &part)| match part {
            | Part::Tile(tile) => {
                next_spells(tile, 0)
                    || ClosingClass::closing(DelimSpelling::from(tile.0)).is_some_and(&pairs)
            },
            | Part::Hole(_) => {
                let taken = filled();
                taken > 0
                    && match parts.get(index.saturating_add(1)) {
                        | Some(&Part::Tile(tile)) => {
                            next_spells(tile, taken)
                                || words
                                    .get(taken)
                                    .is_none_or(|word| role(word) != Role::Operand)
                        },
                        | Some(&Part::Hole(_)) | None => true,
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
///   kind wrongly reverses them.
/// - witness: `inline::tests::the_ranking_is_pinned`
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
            | Step::Tile(mold) => grammar
                .mold(mold)
                .ok()
                .map(|def| Part::Tile(TileLabel(def.label))),
            | Step::Hole { sort, after } => {
                Some(Part::Hole(Category::of_hole(grammar, sort, after)))
            },
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
///   `newline`, or a lone `;`, read as typed changes it.
/// - witness: `inline::tests::the_ranking_is_pinned`
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
        | Lexeme::LowerWord | Lexeme::UpperWord => offered.len() == 1,
        | Lexeme::Punct => offered.iter().any(|&label| <&str>::from(label) == text),
        | _ => false,
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
                | Some(closing) => material.extend(closing),
                | None if shapes.is_empty() => {},
                | None => continue,
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
    let mut materials: Vec<(Origin, Vec<Part>)> = menu
        .closings()
        .iter()
        .map(|closing| {
            let mut material = pending.clone();
            material.extend(parts(grammar, closing.steps()));
            (Origin::Alternative, material)
        })
        .collect();
    if materials.is_empty() && !pending.is_empty() {
        materials.push((Origin::Alternative, pending.clone()));
    }
    let slotted = materials
        .iter()
        .position(|entry| matches!(entry.1.first(), Some(&Part::Hole(_))));
    if let Some(&mut (ref mut origin, _)) = materials.first_mut() {
        *origin = Origin::Closing;
    }
    if let Some(&mut (ref mut origin @ Origin::Alternative, _)) =
        slotted.and_then(|at| materials.get_mut(at))
    {
        *origin = Origin::Slot;
    }
    let slotted = slotted
        .and_then(|at| materials.get(at))
        .map(|entry| entry.1.clone());
    let slot = match slotted.as_ref().and_then(|material| material.first()) {
        | Some(&Part::Hole(category)) => Slot::Open(category),
        | None if menu.head() == HeadForm::Closed && pending.is_empty() => {
            Slot::Open(Category::Item)
        },
        | Some(&Part::Tile(_)) | None => Slot::Filled,
    };
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
                | Some(Rest::Unwritten(ref after, fit)) => {
                    material.extend(after.iter().copied());
                    fit
                },
                // The written text fills the slot: a form ending in a hole
                // takes it as that hole's filling, any other form collides.
                | Some(Rest::Written) => {
                    if let Some(&Part::Hole(_)) = material.last() {
                        material.pop();
                        Fit::Meets
                    }
                    else {
                        Fit::Collides
                    }
                },
                | None => whole_fit(&material, written),
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

/// The ghost texts `grammar`, whose forms are `forms`, offers at byte `at` of
/// `text`, best first.
///
/// # Specification
/// - requires: `forms` is [`Forms::new`] of `grammar`; any offset, one past the
///   text or inside a character read as the nearest character boundary at or
///   before it.
/// - ensures: between one and eight snippets, none holding a `?` tab stop: the
///   candidates of the top-level form the cursor ends, molded alone up to the
///   cursor, cut against the significant tokens after the cursor and ordered by
///   [`rank`], each spelled once as [`spell`] states; the placeholder of the
///   slot at the cursor when no candidate remains.
/// - provides: the answer to `textDocument/inlineCompletion`.
/// - fails: never.
/// - panics: none.
/// - intension: one labelling of the text before the cursor and one of the
///   whole text, one molding of the form the cursor ends, one bounded walk of
///   its open form, and grammar reads only for the words a candidate is cut
///   against; the forms the slot can open are read off `forms`.
///
/// # Adequacy
/// - hypothesis: L3 — the defect rows, one cursor per category, comments and
///   the ranking golden assert exact answers; L2 — every cursor of every corpus
///   source, with and without the text after it, answers at least one snippet
///   and none with `?`. Refusing a continued line, spelling a hole as `?`,
///   repeating a written closer or answering nothing changes one of them.
/// - witness: `inline::tests::the_defect_rows_answer_as_wanted`
/// - witness: `inline::tests::each_category_is_named_where_its_hole_stands`
/// - witness: `inline::tests::a_comment_is_closed_before_code_follows`
/// - witness: `inline::tests::the_ranking_is_pinned`
/// - witness: `inline::tests::every_corpus_cursor_has_a_ghost_text`
#[spec(ensures: |ret| (1 ..= SHOWN).contains(&ret.0.len()) && ret.0.iter().all(|snippet| !snippet.0.contains(":?}")))]
pub fn ghost(
    grammar: &Pbg,
    forms: &Forms,
    text: SourceText<'_>,
    at: ByteOffset,
) -> Ghosts
{
    let whole = <&str>::from(text);
    let at = whole.floor_char_boundary(usize::from(at));
    let before = whole.get(.. at).unwrap_or_default();
    let tokens = label(SourceFragment::from(before));
    let source = SourceText::from(before);
    let after = SourceText::from(whole.get(at ..).unwrap_or_default());
    let lead = lead(source, &tokens);
    let mut molder = Molder::new(grammar);
    let mut state = MeldState::new(grammar);
    if let Some(&form) = molder.form_runs(&tokens, source).last() {
        molder.mold_run(&mut state, &tokens, form, source);
    }
    let written = Written::after(grammar, text, ByteOffset::from(at));
    let menu = state.continuations(ClosingLimit::from(CLOSINGS));
    let (mut found, slot) = candidates(grammar, forms, &menu, &written);
    found.sort_by_key(|candidate| rank(candidate, slot));
    let mut shown: Vec<Snippet> = Vec::with_capacity(SHOWN);
    // A candidate that differs from a better one only by separators — a
    // trailing `,` or `;` — adds nothing an author asks for.
    let mut skeletons: Vec<Vec<Part>> = Vec::with_capacity(SHOWN);
    for candidate in &found {
        let skeleton = skeleton(&candidate.parts);
        if skeletons.contains(&skeleton) {
            continue;
        }
        let snippet = spell(&candidate.parts, lead, source, after);
        if !shown.contains(&snippet) {
            shown.push(snippet);
            skeletons.push(skeleton);
        }
        if shown.len() == SHOWN {
            break;
        }
    }
    if shown.is_empty() {
        let category = match (slot, menu.head()) {
            | (Slot::Open(category), _) => category,
            | (Slot::Filled, HeadForm::Open { mold, .. }) => {
                Category::of_hole(grammar, state.expected_operand_sort(), mold)
            },
            | (Slot::Filled, HeadForm::Closed) => Category::Item,
        };
        shown.push(spell(&[Part::Hole(category)], lead, source, after));
    }
    Ghosts(shown)
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
///   category. Tab stops are numbered from 1 in order. Parts are separated by
///   one space, and the first from what precedes it by one, except after a line
///   end, an opening bracket or whitespace and before a closing bracket, a
///   comma, a semicolon or a quote; one space ends the snippet when `after`
///   begins with text the same rule would space from its last part.
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
        | Some(character) if !character.is_whitespace() && !matches!(character, '(' | '[') => {
            Spacing::Spaced
        },
        | Some(_) | None => Spacing::Tight,
    };
    let mut snippet = String::new();
    let mut joint = joins(<&str>::from(before).chars().next_back());
    match lead {
        | Lead::Code => {},
        | Lead::Line => {
            snippet.push('\n');
            joint = Spacing::Tight;
        },
        | Lead::Block => {
            if joint == Spacing::Spaced {
                snippet.push(' ');
            }
            snippet.push_str("*/");
            joint = Spacing::Spaced;
        },
    }
    let mut stop = 0_u32;
    let mut quoting = Quoting::Outside;
    for &part in parts {
        let piece = match part {
            | Part::Tile(tile) => match tile_spelling(CandidateLabel::from(tile.0)) {
                | TileSpelling::Literal(text) => Piece::Text(text),
                | TileSpelling::Class(class) => Piece::Stop(class),
            },
            | Part::Hole(category) => category.placeholder(),
        };
        // A quote opens a string where none is open, and closes it otherwise:
        // the opening quote stands apart, the string's contents against it.
        let quote = matches!(piece, Piece::Text("\"" | "'"));
        let spacing = match (quote, quoting) {
            | (true, Quoting::Outside) => Spacing::Spaced,
            | (true, Quoting::Inside) | (false, _) => piece.spacing(),
        };
        if joint == Spacing::Spaced && spacing == Spacing::Spaced {
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
        if quote {
            quoting = match quoting {
                | Quoting::Outside => {
                    joint = Spacing::Tight;
                    Quoting::Inside
                },
                | Quoting::Inside => Quoting::Outside,
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
            | Self::Text(")" | "]" | "," | ";" | "\"" | "'") => Spacing::Tight,
            | Self::Text(_) | Self::Stop(_) => Spacing::Spaced,
        }
    }
}

#[cfg(test)]
mod tests
{
    use core::fmt::Write as _;
    use std::path::Path;
    use std::path::PathBuf;

    use expect_test::expect;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_syntax::SourceText;

    use super::Forms;
    use super::ghost;

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

    /// Every `.gandr` source under the corpus's strict and fixture roots, in
    /// path order.
    ///
    /// # Specification
    /// trivial.
    fn corpus_sources() -> Vec<(PathBuf, String)>
    {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
        let mut pending = vec![root.join("strict"), root.join("fixture")];
        let mut paths = Vec::new();
        while let Some(directory) = pending.pop() {
            for entry in std::fs::read_dir(&directory).expect("a corpus directory lists") {
                let path = entry.expect("a corpus entry reads").path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
                {
                    paths.push(path);
                }
            }
        }
        paths.sort();
        paths
            .into_iter()
            .map(|path| {
                let text = std::fs::read_to_string(&path).expect("a corpus source reads");
                (path, text)
            })
            .collect()
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
              "hold ${1:value}"
              "()"
              "[${1:value}]"
              "thunk { ${1:computation} \\}"
              "co { ${1:identifier} = ${2:value} \\}"
            "def x = " ‸ "answer;"
              "- "
              "hold "
              "pure "
              "return "
              "become "
              "force "
              "() "
              "[${1:value}] "
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
              " rule ${1:value} ~> ${2:value}"
              " ${1:constructor} [${2:identifier}]"
            "" ‸ ""
              "def ${1:identifier} : ${2:type};"
              "data ${1:type_identifier} { \\}"
              "codata ${1:type_identifier} { \\}"
              "module ${1:type_identifier} { ${2:member} \\}"
              "import \"\" as ${1:identifier};"
              "op infixl ${1:number} \"\";"
              "rec { \\}"
              "@[${1:identifier}]"
        "#]]
        .assert_eq(&rendered);
    }

    #[test]
    fn every_corpus_cursor_has_a_ghost_text()
    {
        let tools = tools();
        // The enforcing build checks every contract on every call; it reads
        // every sixth cursor.
        let stride = if cfg!(anodized_panic) { 6 } else { 1 };
        for (path, text) in corpus_sources() {
            let cursors = text.char_indices().map(|(at, _)| at).chain([text.len()]);
            for at in cursors.step_by(stride) {
                let prefix = text.get(.. at).expect("a cursor is a character boundary");
                for whole in [text.as_str(), prefix] {
                    let found = ghost(
                        &tools.grammar,
                        &tools.forms,
                        SourceText::from(whole),
                        ByteOffset::from(at),
                    );
                    let found = found.as_ref();
                    assert!(
                        !found.is_empty() && found.len() <= 8,
                        "{}:{at}: {} ghost texts",
                        path.display(),
                        found.len()
                    );
                    assert!(
                        found
                            .iter()
                            .all(|ghost| !ghost.as_ref().contains(":?}") && ghost.as_ref() != "?"),
                        "{}:{at}: a `?` hole is offered: {found:?}",
                        path.display()
                    );
                }
            }
        }
    }
}
