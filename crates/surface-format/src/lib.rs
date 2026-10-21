//! The source formatter: a parsed gandr source laid out at a page width.
//!
//! [`format`] reads the concrete syntax tree, never the core, so every token
//! and comment the source wrote is kept, in order, and only the layout
//! between them changes. Each top-level form is laid out on its own: its
//! brackets nest as groups, a group stays on one line when it fits and
//! breaks one item per line when it does not. A form the parser repaired, a
//! string, a shell block and a hole are copied byte for byte.
//!
//! The formatted text is parsed again before it is returned: its content
//! digest must equal the source's, its tokens and comments must be the
//! source's, and each comment must belong to the node it belonged to, or
//! [`format`] refuses with [`FormatError::Changed`] and returns nothing.
//!
//! # Every comment belongs to a node
//!
//! The parser places each comment among the children of the node it
//! describes. [`comments`] reads that placement back as a record beside the
//! tree: for each comment its [`CommentKind`] — line, block or
//! documentation — its [`Role`] among its owner's children, its owner and the
//! owner's cross-tree key (its top-level form's digest and its rank there),
//! its source column and the width of its text. A comment on its own line
//! before material of its owner leads it; one after material on that
//! material's line trails it; one on its own line with nothing of its owner
//! after it but a closing bracket dangles on it. [`format`] reads the record
//! of the source and of its own text and refuses with
//! [`Change::Attachment`] when a comment would leave its owner or change its
//! role, so a layout that breaks a group or joins one moves each comment with
//! the node it describes.
//!
//! - Choice: a record beside the tree, keyed by the owner's cross-tree key, so
//!   the tree, its losslessness and every digest are untouched, and the record
//!   read from the formatted text compares with the source's.
//! - Alternative: comments re-homed into the tree as leading and trailing
//!   trivia of tokens, as Rowan's green trees hold them, which every reader of
//!   a form's children would have to learn.
//! - Reversal: a reader that needs the attachment inside the tree, at which
//!   point the parser places trivia there and the record reads it.
//!
//! Comment reflow is accounted for here and not built. A reflow pass would
//! rewrap each comment's text at the page width — paragraph breaks and code
//! fences kept, a URL never broken, where `rustfmt`'s `wrap_comments` goes
//! wrong — running over the attached comments before layout and reading the
//! column each comment is laid at and its width. No layout here rewraps a
//! comment.
//!
//! # The form a source is spelled in
//!
//! A source is spelled in the surface's sugared form, `A * B`, `(a, b)`,
//! `A => B`, or in the explicit form, every former the sugar stands for
//! written out: `#{A, B}`, `#{a, b}`, `+U (A -> -F B)`. [`FormatOptions::form`]
//! asks for a [`Form`] — [`Form::Explicit`] or [`Form::Sugared`], or
//! [`Form::Source`], the source's own spelling, by default — and a source
//! states its own at its head, as an entry of an attribute block on its first
//! declaration, after its imports: `@[ form(explicit) ]` or
//! `@[ form(sugared) ]`, an attribute the lowering registers and files
//! without lowering its word. The declaration wins over the option, so one
//! command lays out sources of both spellings.
//!
//! [`Form::Source`] keeps every token: the layout is the only change, and
//! the content digest is its check. Either other form runs the rewrites of
//! its direction from [`REWRITES`], the table of every pair of spellings the
//! presentation printer (`gandr-surface-pretty`) tells apart — the eager
//! product, the sum, the lazy product, the tuple, the value function, the
//! path composite, the path inverse and a map's action on a path — each
//! moving one form between its two spellings, and the default grade `ω` of a
//! thunk type, which the printer writes in neither form and both leave
//! unwritten, so a value function written with it is sugared as one written
//! without. The sugared form also leaves out a tail's `return` where the
//! lowering would infer it, as the printer's canonical body does: a `return`
//! of a value where a path through its body ends, which the lowering lists
//! (`gandr_surface_lowering::ElidableExit`). An early `return`, one of a
//! computation, one an `explicit_exits` attribute asks for and every written
//! `become` keep their keyword, and the explicit form writes none it was not
//! given. A value-function alias written longer than the printer writes it,
//! `(A) => B` or `(x : A) => B` where nothing reads `x`, is sugared to its
//! shortest, `A => B`. The `run x <- c ;` statements ending a block whose
//! binders its tail reads once each, first and in order, are written away,
//! each `c` at its `x`'s read (`gandr_surface_lowering::LinearRun`). A
//! `thunk { e }` of one computation, no grade and no statement written, is
//! written `e` where the checker would insert the thunk: where it checks `e`
//! against a thunk type. Each moves its form on the concrete syntax tree: its
//! operands and their comments are kept, its own tiles are the other
//! spelling's, each comment it owns goes before the operand it preceded, and
//! an operand is parenthesised or unwrapped as its new position's binding
//! needs, as the printer writes it. [`Selection`] narrows the rewrites by
//! [`RewriteName`]; there is no other knob.
//!
//! | rewrite          | explicit                | sugared         |
//! | ---------------- | ----------------------- | --------------- |
//! | `product`        | `#{A, B, …}`            | `A * B * …`     |
//! | `sum`            | `+{A, B, …}`            | `A + B + …`     |
//! | `lazy-product`   | `&{C, D}`               | `C & D`         |
//! | `tuple`          | `#{a, b, …}`            | `(a, b, …)`     |
//! | `value-function` | `+U ((x : A) -> B -> -F C)` | `(x : A, B) => C` |
//! | `default-grade`  | `+U B`, from `+U[ω] B`  | `+U B`, from `+U[ω] B` |
//! | `path-composite` | `transport(\y. Path(A, a, y), q, p)` | `p then q` |
//! | `path-inverse`   | `transport(\y. Path(A, y, a), p, here(a))` | `back(p)` |
//! | `path-action`    | `transport(\y. Path(B, f(a), f(y)), p, here(f(a)))` | `cong(f, p)` |
//! | `tail-return`    | `return v`, as written  | `v`, where a path ends |
//! | `short-alias`    | `(x : A) => B`, as written | `A => B`, `x` unread |
//! | `linear-run`     | `run x <- c ; f(x)`, as written | `f(c)`, beside a checker |
//! | `inserted-thunk` | `thunk { e }`, as written | `e`, beside a checker |
//!
//! A rewrite changes tokens, so its check is the meaning, never the digest:
//! the source and the rewritten text are each lowered into one core arena
//! and every declaration must lower to the same core. A declaration that
//! lowers otherwise has its top-level forms — signature and definition —
//! written again without rewrites, until every declaration agrees. One that
//! still lowers otherwise, written as it was, reads a rewritten declaration's
//! spelling rather than its type (#812): each respelled declaration whose
//! name it writes is written again too, reported for that reader
//! ([`Withdrawn::Read`]). Text whose declarations do not pair up, or that
//! still disagrees with no such declaration left, is refused with
//! [`Change::Meaning`]. A withdrawal is never silent:
//! [`Formatted::withdrawn`] names each such declaration, its span and the
//! reason ([`Withdrawn`]), and `gandr fmt` prints one line for each. A
//! rewrite never applies where its other spelling reads otherwise: a
//! parenthesised list after a rule's `<=>` is the rule's outputs, not a
//! tuple, and the value-function alias is written where the printer writes
//! it: in a type, a static abstraction's body among them, and `A => B` over
//! one bare domain in a value, never as a call's argument.
//! The value-function alias names a domain's binder where a later domain or
//! the result reads it and writes it bare otherwise, as the printer does. A
//! declaration the lowering refuses in the source has no meaning to compare,
//! so no rewrite enters its forms, and it is reported where a rewrite would
//! have. A labelled entry, a comment inside a chain of arrows and a thunk
//! with a grade keep their spelling too, since no sugar spells them.
//!
//! - Choice: rewrites on the tree, each named, checked by meaning and withdrawn
//!   from a declaration whose meaning they would change, so every comment is
//!   kept, no spelling changes what a source means, and the sugar a source may
//!   write grows rule by rule until it is the printer's.
//! - Alternative: printing each declaration through the presentation printer,
//!   one printing per form; the printer reads the core, so a comment inside a
//!   declaration, a binder's written name and every spelling the core does not
//!   keep would be lost. Refusing the whole source on one disagreeing
//!   declaration was the other alternative; it leaves a source with one such
//!   declaration unformattable in either form.
//! - Reversal: a printer that carries the source's comments and names, at which
//!   point one printing serves both and this table retires.
//!
//! A linear run and an inserted thunk are the rewrites whose two spellings
//! lower to different cores: a bind, and a nested call the checker elaborates
//! to that bind; a thunk, and the computation the checker wraps in one. Their
//! meaning check is the checker's, through [`Elaborate`], which a caller that
//! judges modules supplies to [`format_beside`] (the crate depends on no
//! checker): where the lowerings differ, a declaration agrees when the
//! checker elaborates both to equal bodies. The source is elaborated at most
//! once: up front when the lowering lists a run, and otherwise only when a
//! rewritten source first lowers otherwise. Without a checker no statement
//! is written away and no thunk left out, and in a declaration the checker
//! refuses as written no statement is written away; a thunk left out there
//! elaborates to nothing on either side, so the declaration keeps it. A
//! nested call the checker would suspend rather than run, at a thunk-typed
//! parameter, elaborates otherwise and is withdrawn as any rewrite is. A
//! declaration that elaborates otherwise with its thunks left out keeps them
//! and is formatted again, unreported: there the checker inserts no thunk —
//! a returned one, one around a value — so the rewrite does not apply, as a
//! `return` the lowering would not infer stays.
//!
//! - Choice: the checker's elaboration as the oracle, so the sugar is written
//!   exactly where the checker reads the nested call as the run it replaces,
//!   and the bare computation as the thunk it leaves out.
//! - Alternative: a syntactic rule in the lowering alone, which cannot see the
//!   expected type that decides whether a nested call runs or is suspended, or
//!   whether a computation is checked against a thunk type.
//! - Reversal: a lowering that writes the bind for a nested call and the thunk
//!   around a checked computation itself, so the two spellings lower alike and
//!   the core comparison suffices.
//!
//! A source that imports a sibling is lowered beside it: alone, every
//! declaration that reads an imported name is refused and none could be
//! rewritten. [`format_beside`] takes the text its imports reach, laid out
//! before it, and the lowering unit that admits them ([`Beside`]); `gandr fmt`
//! lays the closure out as `gandr check` does. [`format`] formats a source
//! alone.
//!
//! `p then q` is the transport `transport(\y. Path(A, a, y), q, p)`, and the
//! syntax holds neither the carrier `A` nor the fixed endpoint `a`: they are
//! the type of `p`, which the lowering derives. So the explicit form reads the
//! motive from the lowering — the transport it minted at the composite — and
//! spells it through the presentation printer under the names the source
//! writes for the binders around the composite, as
//! `gandr-surface-diagnostics` names the module's constants and binders for
//! it. A composite whose motive the printer cannot spell, one under a binder
//! the source names nothing, keeps `then` and is reported; a composite of
//! flows is its own explicit spelling and stays. The sugared form writes
//! `then` for the same transports, those the lowering returns at a
//! composite, as the printer does: a transport a body runs as written stays
//! `transport(…)`.
//!
//! - Choice: the motive spelled by the shared printer from the lowering the
//!   meaning check already runs, so the explicit spelling is the printer's
//!   token for token.
//! - Alternative: inferring `A` and `a` from the syntax, a second type reader
//!   beside the lowering's, wrong wherever the operand's type is not written.
//! - Reversal: a lowering that keeps the composite's motive in the syntax it
//!   records, at which point the rewrite reads it there and the printer
//!   dependency goes.
//!
//! | item              | what it is                                              |
//! | ----------------- | ------------------------------------------------------- |
//! | [`format`]        | a parsed source formatted at a page width               |
//! | [`format_beside`] | the same, lowered beside the sources it imports         |
//! | [`Beside`]        | the sources a source's rewrites are checked beside      |
//! | [`Formatted`]     | the formatted text and where each top-level form landed |
//! | [`Withdrawal`]    | a declaration that kept its spelling, and why           |
//! | [`Piece`]         | one top-level form's source span and formatted span     |
//! | [`FormatOptions`] | the page width, the form and the rewrites               |
//! | [`Form`]          | the spelling a source is laid out in                    |
//! | [`REWRITES`]      | every rewrite: its name, direction, form and spellings  |
//! | [`Selection`]     | the rewrites a form runs                                |
//! | [`FormatError`]   | why a source was not formatted                          |
//! | [`comments`]      | every comment of a source beside the node it belongs to |
//! | [`Comment`]       | one comment, its owner, role, kind, column and width    |

// Module documentation that predates the shape lint: 2 headings outside the
// vocabulary, 3 decision records, 3 issue references and 1 budget exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod attach;

mod composite;

mod layout;

mod leaf;

mod linear;

mod meaning;

mod rewrite;

mod tail;

mod thunk;

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_surface_grammar::Pbg;
use gandr_surface_layout::ComputationWidth;
use gandr_surface_layout::LayoutOptions;
pub use gandr_surface_layout::PageWidth;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_layout::RenderError;
use gandr_surface_layout::error::BuildError;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::Unit as LoweringUnit;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

pub use crate::attach::Attachment;
pub use crate::attach::Column;
pub use crate::attach::Comment;
pub use crate::attach::CommentKind;
pub use crate::attach::Role;
pub use crate::attach::Width;
pub use crate::attach::comments;
use crate::layout::Gap;
use crate::leaf::Integrity;
use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::leaf::Owner;
use crate::meaning::Agreement;
pub use crate::meaning::Elaborate;
use crate::rewrite::Chosen;
pub use crate::rewrite::Direction;
pub use crate::rewrite::Enabled;
pub use crate::rewrite::MoldName;
pub use crate::rewrite::REWRITES;
use crate::rewrite::Respelled;
pub use crate::rewrite::Rewrite;
pub use crate::rewrite::RewriteName;
pub use crate::rewrite::Selection;
pub use crate::rewrite::Spelling;

/// How a source is formatted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FormatOptions
{
    /// The width a line is laid out to fit.
    pub page: PageWidth,
    /// The spelling the source is laid out in, unless its head declares one.
    pub form: Form,
    /// The rewrites of the form's direction that run.
    pub rewrites: Selection,
}

impl Default for FormatOptions
{
    /// A page of 100 columns, in the source's own spelling, every rewrite
    /// selected.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            page: PageWidth::from(100_u32),
            form: Form::Source,
            rewrites: Selection::Every,
        }
    }
}

/// The spelling a source is laid out in.
///
/// [`Form::Source`] keeps every token the source wrote; the other two run
/// the rewrites of their direction (crate docs, § The form a source is
/// spelled in). A source states its spelling with `@[ form(explicit) ]` or
/// `@[ form(sugared) ]` in an attribute block of its first form; the
/// declaration wins over [`FormatOptions::form`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Form
{
    /// The source's own spelling, every token kept.
    #[default]
    Source,
    /// The explicit spelling: every former a sugar stands for written out.
    Explicit,
    /// The surface's sugared spelling.
    Sugared,
}

impl fmt::Display for Form
{
    /// The form's name, as the option and the declaration spell it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Source => "source",
            Self::Explicit => "explicit",
            Self::Sugared => "sugared",
        })
    }
}

/// Why a source was not formatted.
#[derive(Debug, Eq, PartialEq)]
pub enum FormatError
{
    /// A form's brackets do not pair.
    Unbalanced,
    /// Building a form's layout document reached a ceiling.
    Build(BuildError),
    /// Laying a form's document out reached a ceiling.
    Render(RenderError),
    /// The formatted text did not parse.
    Reparse(MeldError),
    /// The formatted text would have changed the source.
    Changed(Change),
}

/// What formatting would have changed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Change
{
    /// What the source means: its content digest under [`Form::Source`], its
    /// lowering under a rewrite.
    Meaning,
    /// The tokens or comments, or their order.
    Material,
    /// A comment's owner or its role among the owner's children.
    Attachment,
}

impl From<BuildError> for FormatError
{
    /// A build ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: BuildError) -> Self
    {
        Self::Build(error)
    }
}

impl From<RenderError> for FormatError
{
    /// A render ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: RenderError) -> Self
    {
        Self::Render(error)
    }
}

impl fmt::Display for FormatError
{
    /// One line naming the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unbalanced => write!(f, "a form's brackets do not pair"),
            Self::Build(ref error) => write!(f, "the layout could not be built: {error}"),
            Self::Render(ref error) => write!(f, "the layout could not be rendered: {error}"),
            Self::Reparse(ref error) => write!(f, "the formatted text does not parse: {error}"),
            Self::Changed(Change::Meaning) => {
                write!(f, "formatting would change what the source means")
            },
            Self::Changed(Change::Material) => {
                write!(f, "formatting would change the source's tokens or comments")
            },
            Self::Changed(Change::Attachment) => {
                write!(
                    f,
                    "formatting would move a comment off the node it belongs to"
                )
            },
        }
    }
}

/// The formatted text of one source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Formatted
{
    /// The text.
    text: String,
    /// Each top-level form, in source order.
    pieces: Vec<Piece>,
    /// Each declaration whose rewrites were withdrawn, in the order the
    /// checks found them.
    withdrawn: Vec<Withdrawal>,
}

impl Formatted
{
    /// The formatted text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(self.text.as_str())
    }

    /// Each top-level form's source span and formatted span, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pieces(&self) -> &[Piece]
    {
        &self.pieces
    }

    /// Each declaration that keeps the source's spelling because a rewrite
    /// would have changed what it lowers to: never silent, so a caller can
    /// say which declarations kept their spelling and why.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn withdrawn(&self) -> &[Withdrawal]
    {
        &self.withdrawn
    }

    /// The formatted text, owned.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_text(self) -> String
    {
        self.text
    }
}

/// A declaration whose rewrites were withdrawn: its top-level forms keep the
/// source's spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Withdrawal
{
    /// The declaration's name.
    pub declaration: String,
    /// The span, in the source, of the form that introduced it.
    pub span: ByteSpan,
    /// Why its rewrites were withdrawn.
    pub reason: Withdrawn,
}

/// Why a declaration's rewrites were withdrawn.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Withdrawn
{
    /// Rewritten, the declaration is refused: the refusal, as the lowering
    /// writes it.
    Refused(String),
    /// Rewritten, the declaration lowers to other core.
    Lowered,
    /// As written, the declaration is refused, so no rewrite's meaning can be
    /// checked: the refusal, as the lowering writes it.
    Unchecked(String),
    /// A path composite it writes keeps its spelling: the lowering derived no
    /// motive the printer spells for it.
    Unspelled,
    /// Rewritten, a declaration that reads it — named here — would lower
    /// otherwise, though the declaration's own meaning holds: that reader
    /// reads its spelling, not only its type.
    Read(String),
}

impl fmt::Display for Withdrawn
{
    /// Why the declaration kept its spelling, in one clause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Refused(ref refusal) => write!(f, "rewritten, it is refused: {refusal}"),
            Self::Lowered => f.write_str("rewritten, it would lower to other core"),
            Self::Unchecked(ref refusal) => {
                write!(
                    f,
                    "as written, it is refused, so no rewrite can be checked: {refusal}"
                )
            },
            Self::Unspelled => f.write_str(
                "a path composite it writes has no motive the printer spells, so it keeps `then`",
            ),
            Self::Read(ref reader) => write!(
                f,
                "rewritten, `{reader}`, which reads it, would lower to other core"
            ),
        }
    }
}

/// Where one top-level form was and where it landed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Piece
{
    /// Its span in the source: its first token, comment or documentation to
    /// its last.
    pub source: ByteSpan,
    /// Its span in the formatted text.
    pub formatted: ByteSpan,
    /// Whether it was laid out or copied as written.
    pub layout: Layout,
}

/// Whether a top-level form was laid out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layout
{
    /// It was laid out.
    Formatted,
    /// The parser repaired it, so it was copied as written.
    Repaired,
}

/// Format the source `parsed` was parsed from.
///
/// # Errors
/// Returns [`FormatError::Changed`] when the formatted text would mean
/// something else or spell other tokens or comments, and
/// [`FormatError::Reparse`] when it does not parse; either is a defect in
/// the formatter, and no text is returned. A form whose brackets do not pair
/// is [`FormatError::Unbalanced`]; a layout ceiling is
/// [`FormatError::Build`] or [`FormatError::Render`].
///
/// # Specification
/// - requires: `parsed` was parsed under `grammar`.
/// - ensures: the form is the one the source's head declares, else
///   `options.form`. Under [`Form::Source`], the text keeps every token and
///   comment of the source, in order, each comment with the node it belongs to
///   and in its role there, and parses under `grammar` to the source's root
///   digest. Under either other form, each form a selected rewrite of its
///   direction reads is respelled, every comment kept in order and in its role,
///   outside the top-level forms of the declarations the lowering refuses in
///   the source or would lower otherwise once respelled; the text lowers to the
///   source's lowering, declaration by declaration, and each declaration that
///   would have lowered otherwise is in [`Formatted::withdrawn`] with its name,
///   span and reason, none under [`Form::Source`]. Either way, each top-level
///   form starts on a line of its own, and the source's blank lines between
///   them are kept, one at most; a comment the source wrote on a top-level
///   form's last line stays there, as does a separator ending a top-level
///   statement; the text ends in one line break unless it is empty, and uses
///   the line ending most of the source's breaks use. A form the parser
///   repaired, or that an obligation touches, is copied as written. Each other
///   form is laid out at `options.page` as the crate root describes, and
///   formatting the text again returns it unchanged. One piece per top-level
///   form, in order, spans it in the source and in the text.
/// - provides: the text `gandr fmt` writes and the language server's formatting
///   edits.
/// - fails: as `# Errors` states.
/// - panics: none.
/// - intension: one walk of the tree, one layout per top-level form, one parse
///   of the result; under a rewrite, one walk per form respelled and two
///   lowerings.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source is formatted at three widths and
///   formatted again unchanged, the formatter checking each against the
///   source's digest and material, and into either form, the formatter checking
///   each against the source's lowering; goldens fix each layout rule at a
///   narrow and a wide page and each rewrite both ways, and exact texts fix the
///   top-level joins, the verbatim forms, a repaired form, the line ending, the
///   pieces and the declaration's precedence over the option.
/// - witness: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`
/// - witness: `tests::format::a_block_breaks_one_item_per_line_when_it_does_not_fit`
/// - witness: `tests::format::top_level_forms_and_comments_keep_their_lines`
/// - witness: `tests::format::a_repaired_form_is_copied_as_written`
/// - witness: `tests::format::the_source_line_ending_is_kept`
/// - witness: `tests::format::pieces_place_each_top_level_form`
/// - witness: `tests::format::a_form_written_against_the_one_before_starts_its_own_line`
/// - witness: `tests::format::a_separator_written_on_the_next_line_joins_its_statement`
/// - witness: `tests::format::a_source_split_evenly_between_endings_keeps_line_feeds`
/// - witness: `tests::format::an_explicit_source_keeps_its_explicit_spelling`
/// - witness: `tests::attach::a_layout_that_breaks_or_joins_a_group_keeps_each_comment_with_its_owner`
/// - witness: `tests::rewrite::each_rewrite_moves_its_pair_both_ways`
/// - witness: `tests::rewrite::a_sugared_source_keeps_every_comment_with_its_construct`
/// - witness: `tests::rewrite::a_declared_form_wins_over_the_option`
/// - witness: `tests::rewrite::a_selection_runs_only_the_rewrites_it_names`
/// - witness: `tests::rewrite::sweeps::every_source_formats_into_either_form_and_keeps_its_meaning`
/// - witness: `rewrite::tests::a_rewrite_that_changes_what_a_source_means_is_withdrawn`
/// - witness: `tests::rewrite::a_match_over_a_stated_sum_is_sugared_791`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |formatted| formatted.pieces.windows(2).all(|pair| matches!(pair, [left, right] if left.source.end() <= right.source.start() && left.formatted.end() <= right.formatted.start()))))]
#[inline]
pub fn format(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
    options: FormatOptions,
) -> Result<Formatted, FormatError>
{
    format_beside(grammar, parsed, options, (Beside::Alone, None))
}

/// The form the source `parsed` was parsed from declares at its head, which
/// [`format`] writes it in whatever its options ask.
///
/// # Specification
/// - requires: `parsed` was parsed under `grammar`.
/// - ensures: the form the first `form(explicit)` or `form(sugared)` entry of
///   an attribute block before the source's first declaration names, after its
///   imports and inside a leading `rec` group; none when there is none.
/// - fails: never.
/// - panics: none.
/// - executable: none — the declaration is read from the source's leaves, which
///   a predicate over the answer would read again.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus's explicit subset is held to its declared form
///   by the printer parity sweeps.
/// - witness: `tests::format::an_explicit_source_keeps_its_explicit_spelling`
#[inline]
#[must_use]
pub fn declared_form(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
) -> Option<Form>
{
    declared(&leaf::flatten(grammar, parsed.tree(), parsed.obligations()).leaves)
}

/// Format the source `parsed` was parsed from, its rewrites checked by a
/// lowering `beside` the sources it imports and, where two spellings lower
/// otherwise, by the bodies `checker` elaborates.
///
/// # Errors
/// As [`format`].
///
/// # Specification
/// - requires: `parsed` was parsed under `grammar`; under [`Beside::Imports`],
///   `before` is the text `unit` lays out before the source, and the source is
///   the unit's last.
/// - ensures: as [`format`], each lowering the meaning check reads lowered in
///   `beside`'s unit, so a declaration that reads an imported name is rewritten
///   as one that does not; a withdrawal's span is in the source's own text.
///   With `checker`, the sugared form also writes away each `run` statement the
///   lowering lists as linear, and a declaration whose two lowerings differ
///   agrees when `checker` elaborates both to one body; without it, no
///   statement is written away.
/// - provides: the formatting `gandr fmt` runs, beside a source's imports.
/// - fails: as [`format`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source importing the declaration its signature names is
///   sugared beside the import and kept alone; a linear run is written away
///   where the checker elaborates both spellings alike, withdrawn where it
///   elaborates them otherwise, and kept where it refuses the source.
/// - witness: `tests::rewrite::an_importing_source_is_rewritten_beside_its_imports`
/// - witness: `tests::rewrite::a_linear_run_follows_the_checker_s_elaborations`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |formatted| formatted.pieces.windows(2).all(|pair| matches!(pair, [left, right] if left.source.end() <= right.source.start() && left.formatted.end() <= right.formatted.start()))))]
#[inline]
pub fn format_beside(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
    options: FormatOptions,
    (beside, checker): (Beside<'_>, Option<&dyn Elaborate>),
) -> Result<Formatted, FormatError>
{
    let tree = parsed.tree();
    let source = tree.source();
    let flat = leaf::flatten(grammar, tree, parsed.obligations());
    let chosen = Chosen::of(
        declared(&flat.leaves).unwrap_or(options.form),
        options.rewrites,
    );
    let alone = LoweringUnit::single();
    let (before, unit) = match beside {
        Beside::Alone => ("", &alone),
        Beside::Imports { before, unit } => (<&str>::from(before), unit),
    };
    let base = ByteOffset::from(before.len());
    let whole = (!before.is_empty()).then(|| alloc::format!("{before}{}", <&str>::from(source)));
    let whole = whole
        .as_deref()
        .and_then(|text| parse(grammar, SourceText::from(text)).ok());
    let mut arena = CoreArena::new();
    let lowered = chosen.and_then(|_| {
        meaning::lowered(
            grammar,
            whole.as_ref().map_or(tree, ParseResult::tree),
            unit,
            &mut arena,
        )
    });
    let refused = lowered
        .as_ref()
        .map(|module| meaning::refused(module, base))
        .unwrap_or_default();
    let mut withdrawn: Vec<NodeKey> = refused
        .iter()
        .flat_map(|declaration| declaration.keys.iter().copied())
        .collect();
    let mut held: BTreeSet<NodeKey> = withdrawn.iter().copied().collect();
    let motives = match (chosen, lowered.as_ref()) {
        (Some(_), Some(module)) => composite::motives(
            module,
            &arena,
            whole.as_ref().map_or(tree, ParseResult::tree).source(),
            base,
        ),
        (Some(_) | None, _) => composite::Motives::default(),
    };
    let tails = match (chosen, lowered.as_ref()) {
        (Some(_), Some(module)) => tail::Tails::of(module, base),
        (Some(_) | None, _) => tail::Tails::default(),
    };
    // A linear run lowers otherwise than the call written at its read, and a
    // thunk otherwise than the computation the checker wraps in it, so each is
    // written away only where a checker can compare the two. The source is
    // elaborated at most once: here when the lowering lists a run, which is
    // written only in a declaration the checker elaborates as written, and
    // otherwise only once a rewritten source lowers otherwise — a thunk left
    // out of a declaration the checker refuses elaborates to nothing on
    // either side, and that declaration keeps its thunks.
    let checker = chosen.and(lowered.as_ref()).and(checker);
    let mut elaborations: Option<Vec<Option<ValueId>>> = match (lowered.as_ref(), checker) {
        (Some(module), Some(checker)) if !module.linear_runs().is_empty() => {
            Some(checker.definitions(&mut arena, module))
        },
        (Some(_) | None, _) => None,
    };
    let unchecked = match (lowered.as_ref(), elaborations.as_ref()) {
        (Some(module), Some(elaborations)) => {
            forms_of(tree, &meaning::unelaborated(module, elaborations))
        },
        (Some(_) | None, _) => Vec::new(),
    };
    let runs = match (lowered.as_ref(), elaborations.as_ref()) {
        (Some(module), Some(_)) => linear::Runs::of(module, base, unchecked.clone()),
        (Some(_) | None, _) => linear::Runs::default(),
    };
    let mut thunks = match checker {
        Some(_) if thunk::thunked(&flat.leaves, None) == thunk::Thunked::Written => {
            thunk::Thunks::outside(unchecked)
        },
        Some(_) | None => thunk::Thunks::default(),
    };
    let ending = Ending::of(source);
    let layout = LayoutOptions::try_new(
        options.page,
        ComputationWidth::from(u32::from(options.page).saturating_mul(2_u32)),
        ending.physical(),
    )?;
    let mut reports: Vec<Withdrawal> = Vec::new();
    if let (Some(chosen), false) = (chosen, refused.is_empty()) {
        let any = composite::Motives::any();
        let every = tail::Tails::any();
        // A refused declaration has no lowering to list its linear runs from,
        // so none is reported for one.
        let unlisted = linear::Runs::default();
        let unthunked = thunk::Thunks::default();
        let unchecked = write(
            grammar,
            tree,
            &flat,
            Some(rewrite::Rewrites {
                chosen,
                withdrawn: &[],
                motives: &any,
                tails: &every,
                runs: &unlisted,
                thunks: &unthunked,
            }),
            &layout,
            ending,
        )?;
        let respelled: BTreeSet<NodeIndex> = unchecked.respelled.iter().copied().collect();
        for declaration in refused {
            if top_forms(tree, &declaration.keys)
                .iter()
                .any(|form| respelled.contains(form))
            {
                reports.push(declaration.withdrawal);
            }
        }
    }
    let mut stuck = Vec::new();
    let mut fresh: Vec<NodeKey> = Vec::new();
    let mut retried: Vec<ByteSpan> = Vec::new();
    loop {
        let spans = forms_of(tree, &withdrawn);
        let rewrites = match (chosen, lowered.as_ref()) {
            (Some(chosen), Some(_)) => Some(rewrite::Rewrites {
                chosen,
                withdrawn: spans.as_slice(),
                motives: &motives,
                tails: &tails,
                runs: &runs,
                thunks: &thunks,
            }),
            (Some(_) | None, _) => None,
        };
        let laid = write(grammar, tree, &flat, rewrites, &layout, ending)?;
        let text = SourceText::from(laid.text.as_str());
        let Some(ref lowered) = lowered
        else {
            verify(grammar, parsed, &flat.leaves, text)?;
            return Ok(laid.formatted(reports));
        };
        if laid.respelled.is_empty() {
            verify(grammar, parsed, &flat.leaves, text)?;
            unspelled(tree, lowered, (&laid.unspelled, base), &mut reports);
            return Ok(laid.formatted(reports));
        }
        let agreement = verify_rewritten(
            grammar,
            (parsed, &laid.leaves, text),
            (SourceText::from(before), unit),
            (&mut arena, lowered),
            checker.map(|checker| (checker, &mut elaborations)),
        )?;
        match agreement {
            Agreement::Same => {
                unspelled(tree, lowered, (&laid.unspelled, base), &mut reports);
                return Ok(laid.formatted(reports));
            },
            Agreement::Declarations(differing) => {
                let before = withdrawn.len();
                // A declaration elaborating otherwise with its thunks left out
                // keeps them, unreported, and is tried again: there the checker
                // inserts none.
                retried.clear();
                stuck.clear();
                for declaration in differing {
                    let forms = forms_of(tree, &declaration.keys);
                    if checker.is_some()
                        && thunk::thunked(&flat.leaves, Some(&forms)) == thunk::Thunked::Written
                        && thunks.kept(&forms) == thunk::Thunk::Inserted
                    {
                        retried.extend(forms);
                        continue;
                    }
                    fresh.clear();
                    fresh.extend(
                        declaration
                            .keys
                            .iter()
                            .copied()
                            .filter(|key| !held.contains(key)),
                    );
                    if fresh.is_empty() {
                        stuck.push(declaration);
                    }
                    else {
                        held.extend(fresh.iter().copied());
                        withdrawn.append(&mut fresh);
                        reports.push(declaration.withdrawal);
                    }
                }
                if !retried.is_empty() {
                    thunks.keep(&retried);
                    continue;
                }
                if withdrawn.len() == before {
                    for callee in read(
                        tree,
                        (&flat.leaves, &laid.respelled),
                        lowered,
                        (&stuck, &held),
                        base,
                    ) {
                        held.extend(callee.keys.iter().copied());
                        withdrawn.extend(callee.keys);
                        reports.push(callee.withdrawal);
                    }
                }
                if withdrawn.len() == before {
                    return Err(FormatError::Changed(Change::Meaning));
                }
            },
            Agreement::Unpaired => return Err(FormatError::Changed(Change::Meaning)),
        }
    }
}

/// The declarations whose rewrites the declarations `stuck` read: each kept
/// as written and still lowering otherwise, so the change is in a
/// declaration a rewrite respelled — among the `respelled` forms and outside
/// those `withdrawn` — whose name a stuck declaration's tokens, among
/// `leaves`, write. Each is withdrawn for the first such reader.
///
/// # Specification
/// trivial.
fn read(
    tree: &SyntaxTree<'_>,
    (leaves, respelled): (&[Leaf<'_>], &[NodeIndex]),
    lowered: &LoweredModule<'_>,
    (stuck, withdrawn): (&[meaning::Differing], &BTreeSet<NodeKey>),
    base: ByteOffset,
) -> Vec<meaning::Differing>
{
    let respelled: BTreeSet<NodeIndex> = respelled.iter().copied().collect();
    let readers: Vec<(&str, Vec<ByteSpan>)> = stuck
        .iter()
        .map(|declaration| {
            (
                declaration.withdrawal.declaration.as_str(),
                forms_of(tree, &declaration.keys),
            )
        })
        .collect();
    meaning::read(
        lowered,
        base,
        |keys| {
            !keys.iter().all(|key| withdrawn.contains(key))
                && top_forms(tree, keys)
                    .iter()
                    .any(|form| respelled.contains(form))
        },
        |name| {
            readers.iter().find_map(|&(reader, ref spans)| {
                leaves
                    .iter()
                    .any(|leaf| {
                        leaf.material == Material::Token
                            && <&str>::from(leaf.text) == name
                            && spans.iter().any(|span| {
                                span.start() <= leaf.span.start() && leaf.span.end() <= span.end()
                            })
                    })
                    .then(|| String::from(reader))
            })
        },
    )
}

/// Report, beside `reports`, each declaration of `module` holding one of the
/// path composites at `spans` that kept its spelling, no motive derived for
/// it, once.
///
/// # Specification
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "bounded: `reports` holds the withdrawals of one source's formatting"
    )
)]
fn unspelled(
    tree: &SyntaxTree<'_>,
    module: &gandr_surface_lowering::LoweredModule<'_>,
    (spans, base): (&[ByteSpan], ByteOffset),
    reports: &mut Vec<Withdrawal>,
)
{
    for &span in spans {
        let Some(form) = tree.children(tree.root()).find(|&form| {
            tree.node(form).is_some_and(|node| {
                node.span().start() <= span.start() && span.end() <= node.span().end()
            })
        })
        else {
            continue;
        };
        let held = meaning::holding(module, base, &Withdrawn::Unspelled, |keys| {
            top_forms(tree, keys).contains(&form)
        });
        if let Some(withdrawal) = held
            && !reports.contains(&withdrawal)
        {
            reports.push(withdrawal);
        }
    }
}

/// What a source's rewrites are checked beside: the source alone, or the
/// sources its imports reach, laid out before it as one unit.
#[derive(Clone, Copy, Debug, Default)]
pub enum Beside<'unit>
{
    /// The source alone: an import resolves to nothing, so a declaration that
    /// reads an imported name is refused and no rewrite enters it.
    #[default]
    Alone,
    /// The sources the source's imports reach, laid out before it.
    Imports
    {
        /// The unit's text before the source.
        before: SourceText<'unit>,
        /// The unit: every source it lays out, the source last.
        unit: &'unit LoweringUnit,
    },
}

/// The top-level forms of `tree` holding a form, at any depth, whose key is
/// among `keys`: a declaration's rules and clauses may sit beside the form
/// the lowering keys it by, so the top-level form is the unit a rewrite is
/// withdrawn from.
///
/// # Specification
/// trivial.
fn top_forms(
    tree: &SyntaxTree<'_>,
    keys: &[NodeKey],
) -> Vec<NodeIndex>
{
    let mut forms = Vec::new();
    if keys.is_empty() {
        return forms;
    }
    let keys: BTreeSet<NodeKey> = keys.iter().copied().collect();
    for form in tree.children(tree.root()) {
        let mut pending = Vec::from([form]);
        while let Some(at) = pending.pop() {
            if tree.key(at).is_some_and(|key| keys.contains(&key)) {
                forms.push(form);
                break;
            }
            pending.extend(tree.children(at));
        }
    }
    forms
}

/// The spans of [`top_forms`].
///
/// # Specification
/// trivial.
fn forms_of(
    tree: &SyntaxTree<'_>,
    keys: &[NodeKey],
) -> Vec<ByteSpan>
{
    top_forms(tree, keys)
        .into_iter()
        .filter_map(|form| tree.node(form).map(gandr_surface_syntax::Node::span))
        .collect()
}

/// One writing of a source: its text, its pieces, the leaves it was laid out
/// from, and the forms a rewrite respelled.
struct Written<'source>
{
    /// The text.
    text: String,
    /// Where each top-level form landed.
    pieces: Vec<Piece>,
    /// The leaves laid out, in order.
    leaves: Vec<Leaf<'source>>,
    /// The top-level forms a rewrite respelled, in order.
    respelled: Vec<NodeIndex>,
    /// The path composites kept, no motive derived for them, in order.
    unspelled: Vec<ByteSpan>,
}

impl Written<'_>
{
    /// The writing as the caller receives it, beside the declarations whose
    /// rewrites were withdrawn.
    ///
    /// # Specification
    /// trivial.
    fn formatted(
        self,
        withdrawn: Vec<Withdrawal>,
    ) -> Formatted
    {
        Formatted {
            text: self.text,
            pieces: self.pieces,
            withdrawn,
        }
    }
}

/// The source whose leaves are `flat` written at `layout`, each clean form
/// respelled by `rewrites` — the rewrites chosen and the spans they do not
/// enter — when given.
///
/// # Specification
/// trivial.
fn write<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    flat: &leaf::Leaves<'source>,
    rewrites: Option<rewrite::Rewrites<'_, 'source>>,
    layout: &LayoutOptions,
    ending: Ending,
) -> Result<Written<'source>, FormatError>
{
    let source = tree.source();
    let breaks = <&str>::from(ending.spelling());
    let mut text = String::with_capacity(<&str>::from(source).len());
    let mut pieces = Vec::new();
    let mut written: Vec<Leaf<'source>> = Vec::with_capacity(flat.leaves.len());
    let mut respelled = Vec::new();
    let mut unspelled = Vec::new();
    for unit in units(&flat.leaves) {
        let Some(first) = unit.leaves.first()
        else {
            continue;
        };
        if !text.is_empty() {
            match (unit.joins, unit.gap) {
                (Joins::Touching, _) => {},
                (Joins::SameLine, _) => text.push(' '),
                (Joins::OwnLine, Gap::Blank) => {
                    text.push_str(breaks);
                    text.push_str(breaks);
                },
                (Joins::OwnLine, Gap::Adjacent | Gap::Space | Gap::Break) => {
                    text.push_str(breaks);
                },
            }
        }
        let start = text.len();
        let span = unit.span;
        let Owner::Form(form) = first.owner
        else {
            text.push_str(<&str>::from(first.text));
            written.extend_from_slice(unit.leaves);
            continue;
        };
        let laid = match flat.integrity(form) {
            Integrity::Clean => {
                let (respelling, kept) = rewrites.map_or_else(
                    || (Respelled::Kept, rewrite::Unspelled::default()),
                    |rewrites| rewrite::respell(grammar, tree, form, unit.leaves, rewrites),
                );
                unspelled.extend(kept.0);
                let leaves = match respelling {
                    Respelled::Changed(ref leaves) => {
                        respelled.push(form);
                        leaves.as_slice()
                    },
                    Respelled::Kept => unit.leaves,
                };
                text.push_str(&layout::lay_out(leaves, layout, ending.spelling())?);
                written.extend_from_slice(leaves);
                Layout::Formatted
            },
            Integrity::Repaired => {
                if let Ok(as_written) = source.fragment(span) {
                    text.push_str(<&str>::from(as_written));
                }
                written.extend_from_slice(unit.leaves);
                Layout::Repaired
            },
        };
        if let Ok(formatted) = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(text.len()))
        {
            pieces.push(Piece {
                source: span,
                formatted,
                layout: laid,
            });
        }
    }
    if !text.is_empty() {
        text.push_str(breaks);
    }
    Ok(Written {
        text,
        pieces,
        leaves: written,
        respelled,
        unspelled,
    })
}

/// One top-level unit of the source: a form, or a comment or shebang at the
/// root, beside the layout before it.
#[derive(Clone, Copy, Debug)]
struct Unit<'leaves, 'source>
{
    /// The unit's leaves, from its first token or comment to its last.
    leaves: &'leaves [Leaf<'source>],
    /// The span from its first leaf to its last.
    span: ByteSpan,
    /// The layout the source wrote before it.
    gap: Gap,
    /// How it joins the unit before it.
    joins: Joins,
}

/// How a top-level unit joins the unit before it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Joins
{
    /// On its own line: a form, or a comment the source wrote on its own.
    OwnLine,
    /// After one space: a comment the source wrote on the line before it
    /// ended, or a separator the source spaced off.
    SameLine,
    /// Touching: a separator the source wrote against the form it ends.
    Touching,
}

/// The top-level units of `leaves`, in order.
///
/// # Specification
/// trivial.
fn units<'leaves, 'source>(leaves: &'leaves [Leaf<'source>]) -> Vec<Unit<'leaves, 'source>>
{
    let mut units = Vec::new();
    let mut gap = Gap::Adjacent;
    let mut rest = leaves;
    while let Some((first, after)) = rest.split_first() {
        if first.material == Material::Whitespace {
            gap = gap.widen(Gap::of(first.text));
            rest = after;
            continue;
        }
        let mut length = 1_usize;
        if first.owner != Owner::Root {
            for (offset, leaf) in after.iter().enumerate() {
                if leaf.material == Material::Whitespace {
                    continue;
                }
                if leaf.owner != first.owner {
                    break;
                }
                length = offset.saturating_add(2);
            }
        }
        let (unit, remaining) = rest.split_at(length.min(rest.len()));
        let separator = matches!(unit, [only] if only.material == Material::Token
            && layout::SEPARATORS.contains(&<&str>::from(only.text)));
        let comment = matches!(
            first.material,
            Material::LineComment | Material::BlockComment
        );
        let joins = match gap {
            Gap::Adjacent if separator => Joins::Touching,
            Gap::Adjacent | Gap::Space if comment || separator => Joins::SameLine,
            Gap::Break | Gap::Blank if separator => Joins::SameLine,
            Gap::Adjacent | Gap::Space | Gap::Break | Gap::Blank => Joins::OwnLine,
        };
        let last = unit.last().map_or(first.span, |last| last.span);
        units.push(Unit {
            leaves: unit,
            span: first.span.join(last),
            gap,
            joins,
        });
        gap = Gap::Adjacent;
        rest = remaining;
    }
    units
}

/// The line ending a source's line breaks mostly use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ending
{
    /// A line feed.
    Lf,
    /// A carriage return and a line feed.
    CrLf,
}

impl Ending
{
    /// The ending of `source`: a carriage return and line feed when more of
    /// its line breaks are spelled so than not, a line feed otherwise.
    ///
    /// # Specification
    /// trivial.
    fn of(source: SourceText<'_>) -> Self
    {
        let source = <&str>::from(source);
        let breaks = source.bytes().filter(|&byte| byte == b'\n').count();
        let crlf = source.matches("\r\n").count();
        if crlf.saturating_mul(2) > breaks {
            Self::CrLf
        }
        else {
            Self::Lf
        }
    }

    /// The ending's bytes.
    ///
    /// # Specification
    /// trivial.
    fn spelling(self) -> SourceFragment<'static>
    {
        SourceFragment::from(match self {
            Self::Lf => "\n",
            Self::CrLf => "\r\n",
        })
    }

    /// The ending as the layout engine names it.
    ///
    /// # Specification
    /// trivial.
    const fn physical(self) -> PhysicalLineEnding
    {
        match self {
            Self::Lf => PhysicalLineEnding::Lf,
            Self::CrLf => PhysicalLineEnding::CrLf,
        }
    }
}

/// Check that `text` parses to the root digest of `parsed`, spells the
/// tokens and comments of `leaves`, its leaves, in order, and keeps each
/// comment with its owner in its role.
///
/// # Specification
/// trivial.
fn verify(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
    leaves: &[Leaf<'_>],
    text: SourceText<'_>,
) -> Result<(), FormatError>
{
    let reparsed = parse(grammar, text).map_err(FormatError::Reparse)?;
    let digest = |result: &ParseResult<'_>| result.tree().digest();
    if digest(&reparsed) != digest(parsed) {
        return Err(FormatError::Changed(Change::Meaning));
    }
    let again = leaf::flatten(grammar, reparsed.tree(), reparsed.obligations());
    if material(leaves).ne(material(&again.leaves)) {
        return Err(FormatError::Changed(Change::Material));
    }
    let before = comments(parsed.tree());
    let after = comments(reparsed.tree());
    if before
        .iter()
        .map(Comment::attachment)
        .ne(after.iter().map(Comment::attachment))
    {
        return Err(FormatError::Changed(Change::Attachment));
    }
    Ok(())
}

/// The checker's elaborations of a source, by declaration in the lowering's
/// order, once made: none until a rewritten source lowers otherwise.
type Elaborations = Option<Vec<Option<ValueId>>>;

/// Check that `text`, the source rewritten, spells the tokens and comments of
/// `written`, the leaves it was laid out from, in order, and keeps each
/// comment in its role; then lower it after `before` in `unit` into `arena`
/// beside `lowered`, the source's lowering, and say which declarations
/// lowered otherwise — where some did and `checked` gives a checker, those it
/// does not elaborate alike, the source elaborated into `checked`'s slot the
/// first time one does.
///
/// # Specification
/// trivial.
fn verify_rewritten(
    grammar: &Pbg,
    (parsed, written, text): (&ParseResult<'_>, &[Leaf<'_>], SourceText<'_>),
    (before, unit): (SourceText<'_>, &LoweringUnit),
    (arena, lowered): (&mut CoreArena, &LoweredModule<'_>),
    checked: Option<(&dyn Elaborate, &mut Elaborations)>,
) -> Result<Agreement, FormatError>
{
    let reparsed = parse(grammar, text).map_err(FormatError::Reparse)?;
    let again = leaf::flatten(grammar, reparsed.tree(), reparsed.obligations());
    if material(written).ne(material(&again.leaves)) {
        return Err(FormatError::Changed(Change::Material));
    }
    if comments(parsed.tree())
        .iter()
        .map(kept)
        .ne(comments(reparsed.tree()).iter().map(kept))
    {
        return Err(FormatError::Changed(Change::Attachment));
    }
    let before = <&str>::from(before);
    let whole = (!before.is_empty()).then(|| alloc::format!("{before}{}", <&str>::from(text)));
    let whole = match whole {
        Some(ref whole) => {
            Some(parse(grammar, SourceText::from(whole.as_str())).map_err(FormatError::Reparse)?)
        },
        None => None,
    };
    let tree = whole
        .as_ref()
        .map_or_else(|| reparsed.tree(), ParseResult::tree);
    let Some(respelled) = meaning::lowered(grammar, tree, unit, arena)
    else {
        return Err(FormatError::Changed(Change::Meaning));
    };
    let base = ByteOffset::from(before.len());
    let agreement = meaning::agree(arena, (lowered, &respelled), base, None);
    // Only a declaration that lowered otherwise asks the checker: a source no
    // rewrite moved between such spellings is never checked here.
    let (&Agreement::Declarations(_), Some((checker, source))) = (&agreement, checked)
    else {
        return Ok(agreement);
    };
    let source = source.get_or_insert_with(|| checker.definitions(arena, lowered));
    let elaborated = meaning::Elaborated {
        before: source,
        after: checker.definitions(arena, &respelled),
    };
    Ok(meaning::agree(
        arena,
        (lowered, &respelled),
        base,
        Some(&elaborated),
    ))
}

/// What a rewrite keeps of a comment: its text, its kind and its role, the
/// owner being a node the rewrite may have replaced.
///
/// # Specification
/// trivial.
fn kept<'source>(comment: &Comment<'source>) -> (SourceFragment<'source>, CommentKind, Role)
{
    let attachment = comment.attachment();
    (attachment.text, attachment.kind, attachment.role)
}

/// The tokens and comments of `leaves`, in order.
///
/// # Specification
/// trivial.
fn material<'leaves, 'source>(
    leaves: &'leaves [Leaf<'source>]
) -> impl Iterator<Item = (Material, SourceFragment<'source>)> + 'leaves
{
    leaves
        .iter()
        .filter(|leaf| leaf.material != Material::Whitespace)
        .map(|leaf| (leaf.material, leaf.text))
}

/// The form the source's head declares: `form(explicit)` or `form(sugared)`
/// as an entry of an attribute block written before the source's first
/// declaration, after its imports — the one place a block before a
/// declaration stands, since a block before an import refuses the module.
/// A source that opens with a `rec { … }` group declares it on the group's
/// first declaration, since a block before `rec` refuses the module too.
///
/// # Specification
/// - requires: `leaves` are a source's, in offset order.
/// - ensures: the form named by the first `form` entry of the attribute blocks
///   before the first token, outside an import, that no block holds, where the
///   `rec {` that opens a leading group holds none; none when there is none, or
///   it names neither form.
/// - fails: never.
/// - panics: none.
/// - executable: none — the declaration is read from the leaves' text, which a
///   predicate over the answer would read again.
///
/// # Adequacy
/// - hypothesis: L3 — a source declaring the explicit form keeps it under
///   either option, after an import as at its first line and on a leading `rec`
///   group's first declaration; a source declaring either form is written in it
///   whatever the option asks.
/// - witness: `tests::format::an_explicit_source_keeps_its_explicit_spelling`
/// - witness: `tests::rewrite::a_declared_form_wins_over_the_option`
fn declared(leaves: &[Leaf<'_>]) -> Option<Form>
{
    let tokens: Vec<&str> = leaves
        .iter()
        .filter(|leaf| matches!(leaf.owner, Owner::Form(_)) && leaf.material == Material::Token)
        .map(|leaf| <&str>::from(leaf.text))
        .collect();
    let mut depth = 0_usize;
    let mut importing = false;
    let mut grouped = None;
    for (at, &token) in tokens.iter().enumerate() {
        match token {
            ";" if importing => importing = false,
            _ if importing => {},
            "import" if depth == 0 && grouped.is_none() => importing = true,
            "rec"
                if depth == 0
                    && grouped.is_none()
                    && tokens.get(at.saturating_add(1)) == Some(&"{") =>
            {
                grouped = Some(at.saturating_add(1));
            },
            "{" if depth == 0 && grouped == Some(at) => {},
            "@[" => depth = depth.saturating_add(1),
            "[" if depth > 0 => depth = depth.saturating_add(1),
            "]" if depth > 0 => depth = depth.saturating_sub(1),
            _ if depth == 0 => return None,
            "form" if depth == 1 => {
                if let (Some(&"("), Some(&word), Some(&")")) = (
                    tokens.get(at.saturating_add(1)),
                    tokens.get(at.saturating_add(2)),
                    tokens.get(at.saturating_add(3)),
                ) {
                    return match word {
                        "explicit" => Some(Form::Explicit),
                        "sugared" => Some(Form::Sugared),
                        _ => None,
                    };
                }
            },
            _ => {},
        }
    }
    None
}
