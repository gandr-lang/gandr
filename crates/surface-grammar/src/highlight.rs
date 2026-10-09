//! The mold highlighter: every tile of a molded tree classified by its mold
//! into a highlight role, emitted as the renderer seam's spans.
//!
//! A mold is a tile occurrence's zipper into the grammar, so a role is a
//! function of the mold alone: its label, the named kind of its rule, the
//! symbols its form places beside it, and the bracket of its form it stands
//! inside. [`RoleTable::build`] reads that function off a grammar once, one
//! role per mold, and [`RoleTable::highlight`] reads a tree's tiles through
//! the table. Layout carries no mold: a comment and a shebang take their role
//! from the bytes the labeler cut them by, and whitespace takes no span.

use alloc::vec;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;

use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::InvertedRange;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_graphs::Dir;

use crate::model::Pbg;
use crate::model::PbgError;
use crate::model::RegexShape;
use crate::model::RegexView;
use crate::model::Rule;
use crate::model::Sym;
use crate::model::TileLabel;
use crate::mold::RCtxStep;
use crate::mold::StepSym;
use crate::parity::NamedKind;

/// The tiles that open a bracket: every tile after one, up to its closer,
/// stands inside it.
const OPENERS: &[&str] = &[
    "#!{",
    "#{",
    "${",
    "(",
    "@[",
    "[",
    "command_substitution_start",
    "subshell_open",
    "{",
];

/// The tiles that close the innermost open bracket.
const CLOSERS: &[&str] = &[")", "]", "subshell_close", "}"];

/// The words the surface reads as keywords where a form molds them, the
/// compound bridge tiles included.
const KEYWORDS: &[&str] = &[
    "+U", "-F", "acquire", "as", "at", "break", "case", "close", "co", "codata", "continue",
    "data", "def", "drop", "dup", "else", "end", "extern", "feed", "fn", "for", "forall", "force",
    "fork", "from", "glob", "hold", "if", "import", "in", "infix", "infixl", "infixr", "leta",
    "loop", "migrate", "module", "mu", "node", "offer", "op", "oper", "pack", "package", "postfix",
    "prefix", "rec", "recv", "release", "ret", "rule", "run", "select", "send", "sign", "sort",
    "tail", "then", "thunk", "type", "unpack", "val", "while", "with",
];

/// The operators of terms, types, sessions, circuits and shell control, the
/// shell's separator and negation labels included.
const OPERATORS: &[&str] = &[
    "!=",
    "&",
    "&&",
    "*",
    "+",
    "++",
    "-",
    "-->",
    "->",
    "..",
    "/\\",
    ":>",
    "<",
    "<&",
    "<-",
    "<->",
    "<=",
    "<=>",
    "<>",
    "==",
    "==>",
    "=>",
    ">",
    ">&",
    ">=",
    ">>",
    "\\",
    "list_operator",
    "negation",
    "newline",
    "|",
    "|&",
    "||",
    "~>",
];

/// The primitive type spellings, and the universe.
const PRIMITIVE_TYPES: &[&str] = &[
    "Any", "Boolean", "Char", "Integer", "Never", "Path", "String", "Symbol", "Type", "Unit",
    "Unknown", "Void", "f32", "f64", "i32", "i64", "u32", "u64",
];

/// The keywords whose next identifier names what the declaration defines.
const DEFINERS: &[&str] = &["data", "def", "op", "oper", "rec", "rule"];

/// The keywords whose next identifier binds a name.
const BINDERS: &[&str] = &["as", "feed", "for", "leta", "module", "node", "unpack"];

/// The bracket a tile occurrence stands inside within its own form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Enclosure
{
    /// No bracket of the form is open at the occurrence.
    Form,
    /// The innermost open bracket, named by its opener's mold.
    Bracket(MoldId),
}

/// One tile occurrence of a grammar's forms, met in mold-id order.
#[derive(Clone, Copy, Debug)]
struct Occurrence<'pbg>
{
    /// The rule whose form holds the occurrence.
    rule: &'pbg Rule,
    /// The occurrence's label.
    label: TileLabel,
    /// The bracket of the form it stands inside.
    enclosure: Enclosure,
}

/// One frame of the occurrence walk.
enum Frame<'pbg>
{
    /// Visit a subform.
    Enter(RegexView<'pbg>),
    /// Reset the open brackets before the next branch of an alternative.
    Restore(Vec<MoldId>),
}

/// The bracket a mold stands inside, as its role reads it.
#[derive(Clone, Copy)]
enum Opener<'pbg>
{
    /// No bracket of the form.
    Form,
    /// The innermost open bracket.
    Bracket
    {
        /// The opener's label.
        label: TileLabel,
        /// The symbols that can stand left of the opener.
        left: Side<'pbg>,
    },
}

/// One side of a context: the symbols that can stand next to it there.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Side<'pbg>(&'pbg [RCtxStep]);

/// Whether a side of a context steps across a tile.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Crossing(bool);

impl From<Crossing> for bool
{
    /// Unwraps the answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(crossing: Crossing) -> Self
    {
        crossing.0
    }
}

impl Side<'_>
{
    /// Whether this side steps across a tile labelled `tile`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: whether some step crosses a tile labelled `tile`; a hole
    ///   never matches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — read by every context-dependent role the goldens pin,
    ///   and L3 by the pinned identifier places, each separated from its
    ///   neighbours by the tile beside it.
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    fn crosses(
        self,
        tile: TileLabel,
    ) -> Crossing
    {
        Crossing(
            self.0
                .iter()
                .any(|step| matches!(step.crossed, StepSym::Tile(crossed) if crossed == tile.0)),
        )
    }
}

/// Everything the role of one mold is read from.
#[derive(Clone, Copy)]
struct MoldFacts<'pbg>
{
    /// The tile's label.
    label: TileLabel,
    /// The named kind of the mold's rule.
    kind: NamedKind<'static>,
    /// The symbols that can stand left of the tile in its form.
    left: Side<'pbg>,
    /// The symbols that can stand right of it.
    right: Side<'pbg>,
    /// The bracket of its form it stands inside.
    opener: Opener<'pbg>,
}

/// What one layout token is, by the bytes it opens with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Layout
{
    /// A line or block comment.
    Comment,
    /// A shebang line.
    Directive,
    /// A run of whitespace.
    Whitespace,
}

/// The highlight role of every mold of one grammar.
///
/// # Specification
/// - ensures: one role per mold of the grammar the table was built from, by id,
///   and that grammar's fingerprint, so a tree molded under another grammar is
///   refused rather than misread.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RoleTable
{
    /// The fingerprint of the grammar the roles were read off.
    grammar: GrammarFingerprint,
    /// One role per mold, by id.
    roles: Vec<HlRole>,
}

impl RoleTable
{
    /// Reads the role of every mold of `pbg`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one role per mold of `pbg`, by id, and `pbg`'s fingerprint. A
    ///   mold's role is a function of the mold alone — its label, its rule's
    ///   named kind, the symbols its form places beside it and the bracket of
    ///   its form it stands inside — never of a tree it occurs in.
    /// - fails: a lookup `pbg`'s own tables refuse, which a grammar
    ///   [`Pbg::build`] produced never does.
    /// - panics: none.
    /// - intension: one walk over the rules' forms in mold-id order, on an
    ///   explicit frame stack.
    ///
    /// # Errors
    /// [`PbgError::MoldOverflow`] for an occurrence past the 32-bit mold
    /// identity; [`PbgError::UnknownMold`] or [`PbgError::UnknownRCtx`] for an
    /// occurrence or a context the mold table does not hold.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the role goldens pin, source by source, the role of
    ///   every mold the corpus exercises, and name every mold it does not with
    ///   its role, so a misclassified mold or a walk out of step with the mold
    ///   table moves a golden line; L3 — the context-free classes are pinned
    ///   pointwise, and the walk is checked against the mold table occurrence
    ///   by occurrence. The refusals are unreachable for a grammar
    ///   [`Pbg::build`] produced and carry no witness.
    /// - witness: `highlight::tests::mold_provenance_alignment`
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    /// - witness: `tests::highlight::corpus_roles_match_the_golden`
    /// - witness: `tests::highlight::every_mold_has_a_role`
    #[inline]
    pub fn build(pbg: &Pbg) -> Result<Self, PbgError>
    {
        let occurrences = occurrences(pbg)?;
        let mut roles = Vec::with_capacity(occurrences.len());
        for (index, occurrence) in occurrences.iter().enumerate() {
            let id = MoldId::try_from(index).map_err(|_overflow| PbgError::MoldOverflow)?;
            let def = pbg.mold(id)?;
            let left = Side(pbg.step(def.rctx, Dir::Left)?);
            let right = Side(pbg.step(def.rctx, Dir::Right)?);
            let opener = match occurrence.enclosure {
                | Enclosure::Form => Opener::Form,
                | Enclosure::Bracket(opener) => {
                    let opener_def = pbg.mold(opener)?;
                    let opener_left = pbg.step(opener_def.rctx, Dir::Left)?;
                    Opener::Bracket {
                        label: TileLabel(opener_def.label),
                        left: Side(opener_left),
                    }
                },
            };
            roles.push(classify(&MoldFacts {
                label: occurrence.label,
                kind: NamedKind(occurrence.rule.provenance),
                left,
                right,
                opener,
            }));
        }
        Ok(Self {
            grammar: pbg.fingerprint(),
            roles,
        })
    }

    /// The role of `mold`.
    ///
    /// # Specification
    /// - requires: nothing; an id past the table is admissible input.
    /// - ensures: the role [`RoleTable::build`] read off the grammar for
    ///   `mold`.
    /// - provides: the context-free classification: a mold has one role,
    ///   whatever tree it occurs in.
    /// - fails: [`PbgError::UnknownMold`] for an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — the answer is an [`HlRole`], never an absence, so
    ///   every mold of the inventory has a role by type; L3 boundary — every id
    ///   of the built-in inventory answers, and the first id past it is refused
    ///   with that id.
    /// - witness: `tests::highlight::every_mold_has_a_role`
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    #[inline]
    pub fn role_of(
        &self,
        mold: MoldId,
    ) -> Result<HlRole, PbgError>
    {
        let index = usize::try_from(u32::from(mold))
            .map_err(|_overflow| PbgError::UnknownMold { id: mold })?;
        self.roles
            .get(index)
            .copied()
            .ok_or(PbgError::UnknownMold { id: mold })
    }

    /// The highlight spans of `tree`, in source order.
    ///
    /// # Specification
    /// - requires: nothing; a tree molded under another grammar is admissible
    ///   input and is refused.
    /// - ensures: one span per tile, covering exactly the tile's bytes, with
    ///   its mold's role; one span per comment, [`HlRole::Comment`], and per
    ///   shebang, [`HlRole::Directive`]; no span for whitespace, grout, a
    ///   minted close or an interior node. The spans are sorted by range and
    ///   pairwise disjoint, so the tile spans partition the bytes the tiles
    ///   cover.
    /// - provides: the spans a renderer paints, one per token: two adjacent
    ///   tiles of one role stay two spans.
    /// - fails: [`HighlightError::GrammarMismatch`] when the tree's fingerprint
    ///   is not the table's; [`HighlightError::UnknownMold`] for a tile whose
    ///   mold the table does not hold; [`HighlightError::InvertedSpan`] for a
    ///   node span the seam's range refuses, which no tree holds, since a
    ///   [`ByteSpan`] is ordered.
    /// - panics: none.
    /// - intension: one pass over the tree's positions in level order, then one
    ///   sort by range; the tree's root lists its layout after its forms, so
    ///   the sort, not the walk, puts the spans in source order.
    ///
    /// # Errors
    /// [`HighlightError::GrammarMismatch`], [`HighlightError::UnknownMold`],
    /// [`HighlightError::InvertedSpan`], each as above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — over every corpus source, the bytes no span covers
    ///   are whitespace, every span's text is one tile's or one comment's, the
    ///   spans are sorted and disjoint, and the spans match the source's
    ///   golden; L3 — a tree under another grammar and a tile past the table
    ///   are each refused with the exact variant, and the layout classes are
    ///   asserted pointwise. The inverted-span refusal is unreachable and
    ///   carries no witness.
    /// - witness: `tests::highlight::spans_partition_the_tile_bytes`
    /// - witness: `tests::highlight::corpus_roles_match_the_golden`
    /// - witness: `tests::highlight::a_tree_under_another_grammar_is_refused`
    /// - witness: `tests::highlight::a_tile_past_the_table_is_refused`
    /// - witness: `tests::highlight::layout_takes_a_role_only_as_a_comment_or_a_shebang`
    ///
    /// [`ByteSpan`]: gandr_surface_syntax::ByteSpan
    #[inline]
    pub fn highlight(
        &self,
        tree: &SyntaxTree<'_>,
    ) -> Result<Vec<HlSpan>, HighlightError>
    {
        if tree.grammar() != self.grammar {
            return Err(HighlightError::GrammarMismatch {
                tree: tree.grammar(),
                table: self.grammar,
            });
        }
        let mut spans = Vec::new();
        for position in tree.positions() {
            let Some(node) = tree.node(position)
            else {
                continue;
            };
            let role = match node.label() {
                | NodeLabel::Tile(mold) => match self.role_of(mold) {
                    | Ok(role) => role,
                    | Err(_unknown) => return Err(HighlightError::UnknownMold { id: mold }),
                },
                | NodeLabel::Space => {
                    match tree
                        .fragment(position)
                        .map_or(Layout::Whitespace, layout_of)
                    {
                        | Layout::Comment => HlRole::Comment,
                        | Layout::Directive => HlRole::Directive,
                        | Layout::Whitespace => continue,
                    }
                },
                | NodeLabel::Wald
                | NodeLabel::Meld(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. } => continue,
            };
            let span = node.span();
            let start = ByteOffset::from(usize::from(span.start()));
            let end = ByteOffset::from(usize::from(span.end()));
            let range = ByteRange::new(start, end).map_err(HighlightError::InvertedSpan)?;
            spans.push(HlSpan { range, role });
        }
        spans.sort_unstable_by_key(|span| span.range);
        Ok(spans)
    }
}

/// Every refusal of [`RoleTable::highlight`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HighlightError
{
    /// The tree was molded under another grammar than the one the table was
    /// read off.
    GrammarMismatch
    {
        /// The fingerprint the tree records.
        tree: GrammarFingerprint,
        /// The fingerprint the table was read off.
        table: GrammarFingerprint,
    },
    /// A tile names a mold past the table.
    UnknownMold
    {
        /// The tile's mold.
        id: MoldId,
    },
    /// A node's span is not an ordered range.
    InvertedSpan(InvertedRange),
}

impl Display for HighlightError
{
    /// Writes the refusal with the values it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::GrammarMismatch { tree, table } => write!(
                f,
                "the tree was molded under grammar {:#018x}, the role table read off grammar {:#018x}",
                u64::from(tree),
                u64::from(table)
            ),
            | Self::UnknownMold { id } => {
                write!(f, "tile mold {} is past the role table", u32::from(id))
            },
            | Self::InvertedSpan(ref error) => Display::fmt(error, f),
        }
    }
}

impl Error for HighlightError
{
    /// The wrapped refusal, for the variant that wraps one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        match *self {
            | Self::InvertedSpan(ref error) => Some(error),
            | Self::GrammarMismatch { .. } | Self::UnknownMold { .. } => None,
        }
    }
}

/// Every tile occurrence of `pbg`'s forms, in the order the mold table
/// numbers them, each with the bracket of its form it stands inside.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the rules in order, each form left to right, one occurrence per
///   tile symbol — the pre-order the mold table assigns ids in, so occurrence
///   `i` is mold `i`. An occurrence's enclosure is the innermost opener of its
///   own form left open on the walk to it; each branch of an alternative starts
///   from the brackets open before the alternative, and a closer shuts the
///   innermost open one.
/// - fails: [`PbgError::MoldOverflow`] for an occurrence past the 32-bit mold
///   identity.
/// - panics: none.
/// - intension: an explicit frame stack; the open brackets are one stack the
///   walk restores before each branch.
///
/// # Errors
/// [`PbgError::MoldOverflow`] past the 32-bit identity.
///
/// # Adequacy
/// - hypothesis: L2 — the walk is cross-checked against the mold table
///   occurrence by occurrence: one occurrence per mold, each with the mold's
///   label and its rule's sort, precedence and named kind, and every enclosure
///   an opener of the same rule met before the occurrence.
/// - witness: `highlight::tests::mold_provenance_alignment`
fn occurrences(pbg: &Pbg) -> Result<Vec<Occurrence<'_>>, PbgError>
{
    let mut out = Vec::with_capacity(pbg.mold_count().0);
    let mut open: Vec<MoldId> = Vec::new();
    for rule in pbg.rules() {
        open.clear();
        let mut frames = vec![Frame::Enter(rule.regex().view())];
        while let Some(frame) = frames.pop() {
            match frame {
                | Frame::Restore(brackets) => open = brackets,
                | Frame::Enter(view) => match view.shape() {
                    | RegexShape::Empty | RegexShape::Sym(Sym::Sort(_)) => {},
                    | RegexShape::Sym(Sym::Tile(tile)) => {
                        let id = MoldId::try_from(out.len())
                            .map_err(|_overflow| PbgError::MoldOverflow)?;
                        let enclosure = open
                            .last()
                            .copied()
                            .map_or(Enclosure::Form, Enclosure::Bracket);
                        out.push(Occurrence {
                            rule,
                            label: TileLabel(tile.label),
                            enclosure,
                        });
                        if OPENERS.contains(&tile.label) {
                            open.push(id);
                        }
                        else if CLOSERS.contains(&tile.label) {
                            open.pop();
                        }
                    },
                    | RegexShape::Seq(items) => {
                        frames.extend(items.into_iter().rev().map(Frame::Enter));
                    },
                    | RegexShape::Alt(items) => {
                        for item in items.into_iter().rev() {
                            frames.push(Frame::Enter(item));
                            frames.push(Frame::Restore(open.clone()));
                        }
                    },
                    | RegexShape::Optional(inner) | RegexShape::Repeat(inner) => {
                        frames.push(Frame::Enter(inner));
                    },
                },
            }
        }
    }
    Ok(out)
}

/// The role of one mold, read from its facts.
///
/// # Specification
/// - requires: nothing; a label no class names is admissible input.
/// - ensures: the tiles of the comment rules are [`HlRole::Comment`] and the
///   shebang rule's [`HlRole::Directive`]; every tile of a shell list separator
///   or a redirection is [`HlRole::Operator`]. Otherwise by label: `identifier`
///   takes the role of the place it names ([`identifier_role`]); `_` is a
///   parameter inside a parenthesised list and a variable elsewhere; `!` is
///   part of the keyword after `fork` and an operator elsewhere; `?` is a hole
///   under the hole rule, the gradual type under its rule and an operator
///   elsewhere; `+` and `-` are the sort literals, keywords, inside a universe
///   and operators elsewhere; literals, string pieces, escapes, constructors,
///   type names, type variables, hole names, shell variables, environment
///   assignments and shell words take their class; keywords, operators and
///   primitive types take theirs by spelling; every other tile — a bracket, a
///   separator, a delimiter, a label no class names — is [`HlRole::Other`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one mold per class is pinned to its exact role,
///   label-shared molds told apart by their rule; L2 — every mold's role stands
///   in a golden line, so a label moved between classes moves the lines of
///   every mold it labels.
/// - witness: `highlight::tests::role_of_pins_context_free_classes`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
fn classify(facts: &MoldFacts<'_>) -> HlRole
{
    let label = facts.label.0;
    match facts.kind.0 {
        | "line_comment" | "block_comment" => return HlRole::Comment,
        | "shebang" => return HlRole::Directive,
        | "list_operator" | "redirection_operator" => return HlRole::Operator,
        | _ => {},
    }
    let left_crosses = |tile: &'static str| bool::from(facts.left.crosses(TileLabel(tile)));
    match label {
        | "identifier" => identifier_role(facts),
        | "_" => match facts.opener {
            | Opener::Bracket {
                label: TileLabel("("),
                ..
            } => HlRole::VariableParam,
            | Opener::Bracket { .. } | Opener::Form => HlRole::Variable,
        },
        | "!" if left_crosses("fork") => HlRole::Keyword,
        | "!" => HlRole::Operator,
        | "+" | "-" if facts.kind.0 == "universe_type" => HlRole::Keyword,
        | "?" => match facts.kind.0 {
            | "hole" => HlRole::Hole,
            | "unknown_type" => HlRole::TypeBuiltin,
            | _ => HlRole::Operator,
        },
        | "true" | "false" => HlRole::Boolean,
        | "character" => HlRole::Character,
        | "number" | "typed_number" | "ω" | "file_descriptor" => HlRole::Number,
        | "\"" | "'" | "string_fragment" | "double_string_fragment" | "single_quoted_content" => {
            HlRole::StringLit
        },
        | "escape_sequence" => HlRole::Escape,
        | "constructor" => HlRole::Constructor,
        | "type_identifier" => HlRole::Type,
        | "type_variable" => HlRole::TypeVariable,
        | "hole_name" => HlRole::Label,
        | "variable_name" => HlRole::Variable,
        | "environment_assignment" => HlRole::VariableParam,
        | "shell_word" => HlRole::Path,
        | _ if KEYWORDS.contains(&label) => HlRole::Keyword,
        | _ if OPERATORS.contains(&label) => HlRole::Operator,
        | _ if PRIMITIVE_TYPES.contains(&label) => HlRole::TypeBuiltin,
        | _ => HlRole::Other,
    }
}

/// The role of an `identifier` mold: what its place in its form names.
///
/// # Specification
/// - requires: `facts` is an `identifier` mold's.
/// - ensures: the reference atom's identifier is a variable. A member: in a
///   projection, after `.`, inside a record bracket `#{`, and inside a block
///   `{` of fields or observations. A label: a world, a session branch, the
///   label a `select` names. A named instantiation argument is a parameter, and
///   an attribute name is [`HlRole::Other`]. The operation a circuit node
///   applies, between `:` and `(`, is a call. A name after a defining keyword
///   is a function definition and after a binding keyword a variable
///   definition, either one a parameter inside a parenthesised list. Inside
///   `@[…]` a binder before `:` is a parameter and any other name an attribute;
///   inside `[…]` a grade word is a number, a migration's world a label, and a
///   decoration [`HlRole::Other`]; every other identifier inside a
///   parenthesised list is a parameter. An identifier none of these reach is a
///   variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each place is pinned on one mold of the built-in surface;
///   L2 — every identifier mold's role stands in a golden line.
/// - witness: `highlight::tests::role_of_pins_context_free_classes`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
fn identifier_role(facts: &MoldFacts<'_>) -> HlRole
{
    let kind = facts.kind.0;
    match kind {
        | "identifier" => return HlRole::Variable,
        | "projection_expression" => return HlRole::Member,
        | "at_type" | "offer_session_type" | "select_session_type" => return HlRole::Label,
        | "attribute_block" => return HlRole::Other,
        | "instantiation_expression" => return HlRole::VariableParam,
        | _ => {},
    }
    let left_crosses = |tile: &'static str| bool::from(facts.left.crosses(TileLabel(tile)));
    let right_crosses = |tile: &'static str| bool::from(facts.right.crosses(TileLabel(tile)));
    if left_crosses(".") {
        return HlRole::Member;
    }
    if left_crosses(":") && right_crosses("(") {
        return HlRole::FunctionCall;
    }
    let in_parens = matches!(facts.opener, Opener::Bracket {
        label: TileLabel("("),
        ..
    });
    if DEFINERS.iter().any(|&keyword| left_crosses(keyword)) {
        return if in_parens {
            HlRole::VariableParam
        }
        else {
            HlRole::FunctionDef
        };
    }
    if BINDERS.iter().any(|&keyword| left_crosses(keyword)) {
        return if in_parens {
            HlRole::VariableParam
        }
        else {
            HlRole::VariableDef
        };
    }
    match facts.opener {
        | Opener::Form => HlRole::Variable,
        | Opener::Bracket { label, left } => match label.0 {
            | "#{" | "{" => HlRole::Member,
            | "@[" if right_crosses(":") => HlRole::VariableParam,
            | "@[" => HlRole::Other,
            | "[" => match kind {
                | "u_type" | "thunk_expression" => HlRole::Number,
                | "migrate_expression" => HlRole::Label,
                | _ => HlRole::Other,
            },
            | "(" if bool::from(left.crosses(TileLabel("select"))) => HlRole::Label,
            | "(" => HlRole::VariableParam,
            | _ => HlRole::Variable,
        },
    }
}

/// What one layout token is, by the bytes it opens with.
///
/// # Specification
/// - requires: `text` is one layout token as the labeler cut it: one comment,
///   one shebang line or one run of whitespace.
/// - ensures: [`Layout::Comment`] for text opening with `//` or `/*`,
///   [`Layout::Directive`] for `#!`, [`Layout::Whitespace`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a line comment, a block comment, a shebang and
///   whitespace, each asserted as its exact role or as no span.
/// - witness: `tests::highlight::layout_takes_a_role_only_as_a_comment_or_a_shebang`
fn layout_of(text: SourceFragment<'_>) -> Layout
{
    let text = <&str>::from(text);
    if text.starts_with("//") || text.starts_with("/*") {
        Layout::Comment
    }
    else if text.starts_with("#!") {
        Layout::Directive
    }
    else {
        Layout::Whitespace
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::*;
    use crate::surface::built_in;

    /// The molds labelled `label` whose rule realises `kind`, in id order.
    ///
    /// # Specification
    /// trivial.
    fn molds_of(
        pbg: &Pbg,
        label: TileLabel,
        kind: NamedKind<'_>,
    ) -> Vec<MoldId>
    {
        pbg.candidates(label)
            .iter()
            .copied()
            .filter(|&id| pbg.named_kind(id).is_ok_and(|named| named.0 == kind.0))
            .collect()
    }

    /// The highlighter reads a mold's rule and enclosing bracket off its own
    /// walk of the forms, not off the mold table, so the walk must meet the
    /// table tile for tile: one occurrence per mold, each with the mold's
    /// label, its rule and that rule's named kind. An enclosure is an opener
    /// of the same rule met earlier, and a closer's enclosure is an opener it
    /// closes, so the bracket stack is checked where it pops; a closer never
    /// stands outside every bracket.
    #[test]
    fn mold_provenance_alignment()
    {
        let pbg = built_in().expect("the built-in surface builds");
        let walk = occurrences(&pbg).expect("the walk numbers every tile");
        assert_eq!(pbg.mold_count().0, walk.len(), "one occurrence per mold");
        let closes: &[(&str, &[&str])] = &[
            (")", &["("]),
            ("]", &["@[", "["]),
            ("}", &["#!{", "#{", "${", "command_substitution_start", "{"]),
            ("subshell_close", &["subshell_open"]),
        ];
        for ((id, def), occurrence) in pbg.iter_molds().zip(&walk) {
            let at = u32::from(id);
            assert_eq!(def.label, occurrence.label.0, "mold {at}: label");
            let rule = pbg.rule_of(id).expect("every mold has a rule");
            assert_eq!(rule.name, occurrence.rule.name, "mold {at}: rule");
            assert_eq!(
                pbg.named_kind(id).expect("every mold has a named kind").0,
                occurrence.rule.provenance,
                "mold {at}: named kind"
            );
            let Enclosure::Bracket(opener) = occurrence.enclosure
            else {
                assert!(
                    !CLOSERS.contains(&def.label),
                    "mold {at}: `{}` closes no bracket",
                    def.label
                );
                continue;
            };
            assert!(u32::from(opener) < at, "mold {at}: its opener comes first");
            let opener_rule = pbg.rule_of(opener).expect("the opener has a rule");
            assert_eq!(
                opener_rule.name, rule.name,
                "mold {at}: an opener of its own form"
            );
            let opener_label = pbg.mold(opener).expect("the opener is a mold").label;
            assert!(
                OPENERS.contains(&opener_label),
                "mold {at}: `{opener_label}` opens a bracket"
            );
            if let Some(&(closer, openers)) =
                closes.iter().find(|&&(closer, _)| closer == def.label)
            {
                assert!(
                    openers.contains(&opener_label),
                    "mold {at}: `{closer}` closes `{opener_label}`"
                );
            }
        }
    }

    /// One mold class at a time, pinned to its exact role: the comment and
    /// shebang rules, literals, string pieces, keywords, operators and
    /// primitive types by spelling, a label shared by several rules told apart
    /// by its rule (`?` a hole, the gradual type, a receive; `!` after `fork`
    /// and as a send), and every identifier place by the tile beside it. Every
    /// mold matching a row is pinned, not only the first. The last id answers
    /// and the first id past the table is refused with that id.
    #[test]
    fn role_of_pins_context_free_classes()
    {
        let pbg = built_in().expect("the built-in surface builds");
        let table = RoleTable::build(&pbg).expect("the role table builds");
        let classes: &[(&str, &str, HlRole)] = &[
            ("def", "def_value", HlRole::Keyword),
            ("val", "let_statement", HlRole::Keyword),
            ("->", "function_type", HlRole::Operator),
            ("<>", "redirection_operator", HlRole::Operator),
            ("list_operator", "shell_list", HlRole::Operator),
            ("String", "primitive_type", HlRole::TypeBuiltin),
            ("type_identifier", "type_identifier", HlRole::Type),
            ("type_variable", "def_value", HlRole::TypeVariable),
            ("constructor", "constructor", HlRole::Constructor),
            ("number", "number", HlRole::Number),
            ("typed_number", "typed_number", HlRole::Number),
            ("ω", "u_type", HlRole::Number),
            ("file_descriptor", "file_descriptor", HlRole::Number),
            ("true", "boolean", HlRole::Boolean),
            ("character", "character", HlRole::Character),
            ("\"", "string", HlRole::StringLit),
            ("\"", "double_quoted_string", HlRole::StringLit),
            ("escape_sequence", "string", HlRole::Escape),
            ("?", "hole", HlRole::Hole),
            ("hole_name", "hole", HlRole::Label),
            ("?", "unknown_type", HlRole::TypeBuiltin),
            ("?", "receive_session_type", HlRole::Operator),
            ("!", "fork_statement", HlRole::Keyword),
            ("!", "send_session_type", HlRole::Operator),
            ("+U", "u_type", HlRole::Keyword),
            ("-F", "f_type", HlRole::Keyword),
            ("Type", "universe_type", HlRole::TypeBuiltin),
            ("+", "universe_type", HlRole::Keyword),
            ("-", "universe_type", HlRole::Keyword),
            ("+", "sum_type", HlRole::Operator),
            ("_", "wildcard", HlRole::Variable),
            ("shell_word", "shell_word", HlRole::Path),
            ("variable_name", "variable_name", HlRole::Variable),
            (
                "environment_assignment",
                "environment_assignment",
                HlRole::VariableParam,
            ),
            ("line_comment", "line_comment", HlRole::Comment),
            ("shebang", "shebang", HlRole::Directive),
            ("(", "parenthesized_expression", HlRole::Other),
            (";", "import_declaration", HlRole::Other),
            ("identifier", "identifier", HlRole::Variable),
            ("identifier", "projection_expression", HlRole::Member),
            (
                "identifier",
                "instantiation_expression",
                HlRole::VariableParam,
            ),
        ];
        for &(label, kind, role) in classes {
            let molds = molds_of(&pbg, TileLabel(label), NamedKind(kind));
            assert!(!molds.is_empty(), "`{label}` occurs under {kind}");
            for id in molds {
                assert_eq!(
                    Ok(role),
                    table.role_of(id),
                    "`{label}` under {kind}, mold {}",
                    u32::from(id)
                );
            }
        }

        let crosses = |id: MoldId, dir: Dir, tile: &str| {
            pbg.mold(id)
                .and_then(|def| pbg.step(def.rctx, dir))
                .is_ok_and(|steps| {
                    steps.iter().any(
                        |step| matches!(step.crossed, StepSym::Tile(crossed) if crossed == tile),
                    )
                })
        };
        let places: &[(&str, &str, Option<&str>, HlRole)] = &[
            ("def_value", "def", None, HlRole::FunctionDef),
            ("def_value", "rec", None, HlRole::FunctionDef),
            ("data_declaration", "op", None, HlRole::FunctionDef),
            ("lambda_expression", "(", Some(")"), HlRole::VariableParam),
            ("fork_statement", "(", None, HlRole::VariableParam),
            ("def_value", "@[", Some(":"), HlRole::VariableParam),
            ("def_value", "@[", Some("("), HlRole::Other),
            ("data_declaration", "[", None, HlRole::Other),
            ("import_declaration", "as", None, HlRole::VariableDef),
            ("for_expression", "for", None, HlRole::VariableDef),
            ("module_declaration", "module", None, HlRole::VariableDef),
            ("sign_declaration", "node", None, HlRole::VariableDef),
            ("circuit_declaration", ":", Some("("), HlRole::FunctionCall),
            ("def_value", ".", None, HlRole::Member),
            ("record_type", "#{", None, HlRole::Member),
            ("glob_expression", "{", None, HlRole::Member),
            ("codata_declaration", "{", None, HlRole::Member),
            ("select_expression", ",", None, HlRole::Label),
            ("at_type", "at", None, HlRole::Label),
            ("offer_session_type", "{", None, HlRole::Label),
            ("migrate_expression", "[", None, HlRole::Label),
            ("thunk_expression", "[", None, HlRole::Number),
        ];
        for &(kind, left, right, role) in places {
            let molds: Vec<MoldId> = molds_of(&pbg, TileLabel("identifier"), NamedKind(kind))
                .into_iter()
                .filter(|&id| {
                    crosses(id, Dir::Left, left)
                        && right.is_none_or(|tile| crosses(id, Dir::Right, tile))
                })
                .collect();
            assert!(
                !molds.is_empty(),
                "an identifier under {kind} after `{left}` before {right:?}"
            );
            for id in molds {
                assert_eq!(
                    Ok(role),
                    table.role_of(id),
                    "identifier under {kind} after `{left}`, mold {}",
                    u32::from(id)
                );
            }
        }

        let count = pbg.mold_count().0;
        let last = MoldId::try_from(count.checked_sub(1).expect("the surface has molds"))
            .expect("the last id fits the identity");
        assert!(table.role_of(last).is_ok(), "the last mold answers");
        let past = MoldId::try_from(count).expect("the first id past the table fits the identity");
        assert_eq!(
            Err(PbgError::UnknownMold { id: past }),
            table.role_of(past),
            "the first id past the table is refused"
        );
    }
}
