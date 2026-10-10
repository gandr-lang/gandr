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

use anodized::spec;
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
    /// - hypothesis: For empty, mixed and duplicate context steps, L3 exact
    ///   membership observations catch first-only searches and treating a sort
    ///   hole as a tile; the built-in role matrix covers its use in context.
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    /// - witness: `highlight::tests::crossings_distinguish_tiles_from_holes`
    #[spec(ensures: |ret| ret.0 == self.0.iter().any(|step| matches!(step.crossed, StepSym::Tile(label) if label == tile.0)))]
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
///
/// # Adequacy
/// - hypothesis: For the built-in grammar, L3 complete role lookup and
///   foreign-grammar refusals catch incomplete identity tables and stale
///   fingerprint acceptance; this is a constructor and observer invariant, not
///   parser language equivalence.
/// - witness: `tests::highlight::every_mold_has_a_role`
/// - witness: `tests::highlight::a_tree_under_another_grammar_is_refused`
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
    /// - hypothesis: The built-in inventory and corpus provide an L2 finite
    ///   census of mold roles and L3 classification and provenance
    ///   observations, catching omitted molds, wrong grammar identity and
    ///   context misclassification. Arbitrary custom grammars are not
    ///   exhausted; the lookup refusals are unreachable for a grammar
    ///   constructed by `Pbg::build`.
    /// - witness: `highlight::tests::mold_provenance_alignment`
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    /// - witness: `tests::highlight::corpus_roles_match_the_golden`
    /// - witness: `tests::highlight::every_mold_has_a_role`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|table| table.grammar == pbg.fingerprint() && table.roles.len() == pbg.mold_count().0))]
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
    /// - hypothesis: Over the complete built-in inventory and its first-invalid
    ///   identity, L3 exact class and refusal observations catch off-by-one
    ///   lookup, substituted roles and wrong error identities; arbitrary custom
    ///   tables and integer widths are not exhausted.
    /// - witness: `tests::highlight::every_mold_has_a_role`
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    #[spec(ensures: |ret| ret == usize::try_from(u32::from(mold)).ok().and_then(|index| self.roles.get(index)).copied().ok_or(PbgError::UnknownMold { id: mold }))]
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
    ///   minted close, a Wald or a Meld node. The spans are sorted by range.
    ///   Tile spans preserve their input multiplicity and overlap; disjoint
    ///   input tiles yield a partition of exactly the bytes those tiles cover.
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
    /// - hypothesis: The parser-produced corpus supplies L2 finite token
    ///   coverage and L3 exact range, role and partition observations. The
    ///   admitted-tree overlap fixture catches clamping, deduplication and
    ///   wrong range order; fingerprint and mold boundaries catch incorrect
    ///   refusal identity. The predicate checks token observations, count and
    ///   order. Arbitrary tree shapes are not exhausted; disjointness belongs
    ///   to the input, and ordered spans exclude an inverted-range refusal.
    /// - witness: `tests::highlight::spans_partition_the_tile_bytes`
    /// - witness: `tests::highlight::corpus_roles_match_the_golden`
    /// - witness: `tests::highlight::a_tree_under_another_grammar_is_refused`
    /// - witness: `tests::highlight::a_tile_past_the_table_is_refused`
    /// - witness: `tests::highlight::layout_takes_a_role_only_as_a_comment_or_a_shebang`
    /// - witness: `tests::highlight::highlight_preserves_overlapping_tile_spans`
    ///
    /// [`ByteSpan`]: gandr_surface_syntax::ByteSpan
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| match *error {
            HighlightError::GrammarMismatch { tree: recorded, table } => recorded == tree.grammar() && table == self.grammar && recorded != table,
            HighlightError::UnknownMold { id } => tree.grammar() == self.grammar && self.role_of(id).is_err() && tree.positions().any(|position| tree.node(position).is_some_and(|node| node.label() == NodeLabel::Tile(id))),
            HighlightError::InvertedSpan(_) => false,
        },
        |spans| {
            let mut expected_count = 0_usize;
            tree.grammar() == self.grammar && spans.iter().is_sorted_by(|left, right| left.range <= right.range) && tree.positions().all(|position| tree.node(position).is_none_or(|node| {
                let role = match node.label() {
                    NodeLabel::Tile(id) => self.role_of(id).map(Some),
                    NodeLabel::Space => Ok(match tree.fragment(position).map_or(Layout::Whitespace, layout_of) {
                        Layout::Comment => Some(HlRole::Comment),
                        Layout::Directive => Some(HlRole::Directive),
                        Layout::Whitespace => None,
                    }),
                    NodeLabel::Wald | NodeLabel::Meld(_) | NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => Ok(None),
                };
                role.is_ok_and(|role| role.is_none_or(|role| {
                    expected_count = expected_count.saturating_add(1);
                    let start = usize::from(node.span().start());
                    let end = usize::from(node.span().end());
                    let first = spans.partition_point(|span| usize::from(span.range.start()) < start);
                    spans.iter().skip(first).take_while(|span| usize::from(span.range.start()) == start).any(|span| usize::from(span.range.end()) == end && span.role == role)
                }))
            })) && spans.len() == expected_count
        }
    ))]
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
    /// - requires: nothing.
    /// - ensures: the refusal is distinguished and its identities or range
    ///   endpoints are shown.
    /// - fails: the formatter refuses a write.
    /// - panics: none.
    /// - executable: none — `Formatter` is write-only and exposes neither the
    ///   emitted bytes nor the sink failure that formatting must preserve.
    ///
    /// # Adequacy
    /// - hypothesis: For each refusal variant and a one-byte sink, L3 payload
    ///   and write-failure observations catch omitted identities, lost range
    ///   endpoints and swallowed formatter errors; wording and other sink
    ///   implementations are not pinned.
    /// - witness: `highlight::tests::highlight_error_messages_preserve_values_and_sink_failure`
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
    /// - requires: nothing.
    /// - ensures: an inverted range exposes its original typed cause; local
    ///   refusals have no cause.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all three refusal classes, L3 typed downcast and
    ///   absence observations catch a hidden, substituted or invented cause;
    ///   recursive causes outside these variants are not represented.
    /// - witness: `highlight::tests::highlight_error_sources_preserve_the_range_cause`
    #[spec(ensures: |ret| match *self { Self::InvertedSpan(ref error) => ret.and_then(|source| source.downcast_ref::<InvertedRange>()) == Some(error), Self::GrammarMismatch { .. } | Self::UnknownMold { .. } => ret.is_none() })]
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
/// - hypothesis: The complete built-in inventory and an explicit branching form
///   supply L3 exact occurrence and enclosure observations, catching changed
///   numbering, wrong owners and bracket state leaking between alternatives or
///   rules. Huge identities and arbitrary unbalanced forms are not exhausted.
/// - witness: `highlight::tests::mold_provenance_alignment`
/// - witness: `highlight::tests::alternative_brackets_restore_before_each_branch`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|items| items.len() == pbg.mold_count().0 && items.iter().enumerate().all(|(index, occurrence)| MoldId::try_from(index).is_ok_and(|id| pbg.mold(id).is_ok_and(|mold| mold.label == occurrence.label.0) && pbg.rule_of(id).is_ok_and(|rule| core::ptr::eq(core::ptr::from_ref(rule), core::ptr::from_ref(occurrence.rule))) && match occurrence.enclosure { Enclosure::Form => true, Enclosure::Bracket(opener) => opener < id && pbg.mold(opener).is_ok_and(|mold| OPENERS.contains(&mold.label)) && pbg.rule_of(opener).is_ok_and(|rule| core::ptr::eq(core::ptr::from_ref(rule), core::ptr::from_ref(occurrence.rule))) }))))]
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
/// - hypothesis: The built-in role matrix and finite competing context fixtures
///   supply L3 exact class observations, catching misplaced rule overrides,
///   omitted labels and changed context priority. Corpus goldens cover every
///   inventoried mold; arbitrary custom combinations are not exhausted.
/// - witness: `highlight::tests::role_of_pins_context_free_classes`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
/// - witness: `highlight::tests::role_priorities_distinguish_competing_contexts`
#[spec(ensures: |ret| ret == match facts.kind.0 {
    "line_comment" | "block_comment" => HlRole::Comment,
    "shebang" => HlRole::Directive,
    "list_operator" | "redirection_operator" => HlRole::Operator,
    _ => match facts.label.0 {
        "identifier" => identifier_role(facts),
        "_" if matches!(facts.opener, Opener::Bracket { label: TileLabel("("), .. }) => HlRole::VariableParam,
        "!" if facts.left.crosses(TileLabel("fork")).0 => HlRole::Keyword,
        "+" | "-" if facts.kind.0 == "universe_type" => HlRole::Keyword,
        "?" if facts.kind.0 == "hole" => HlRole::Hole,
        "?" if facts.kind.0 == "unknown_type" => HlRole::TypeBuiltin,
        "!" | "?" => HlRole::Operator,
        "true" | "false" => HlRole::Boolean,
        "character" => HlRole::Character,
        "number" | "typed_number" | "ω" | "file_descriptor" => HlRole::Number,
        "\"" | "'" | "string_fragment" | "double_string_fragment" | "single_quoted_content" => HlRole::StringLit,
        "escape_sequence" => HlRole::Escape,
        "constructor" => HlRole::Constructor,
        "type_identifier" => HlRole::Type,
        "type_variable" => HlRole::TypeVariable,
        "hole_name" => HlRole::Label,
        "_" | "variable_name" => HlRole::Variable,
        "environment_assignment" => HlRole::VariableParam,
        "shell_word" => HlRole::Path,
        label if KEYWORDS.contains(&label) => HlRole::Keyword,
        label if OPERATORS.contains(&label) => HlRole::Operator,
        label if PRIMITIVE_TYPES.contains(&label) => HlRole::TypeBuiltin,
        _ => HlRole::Other,
    }
})]
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
/// - hypothesis: Built-in identifier places and explicit competing contexts
///   provide L3 exact role observations, catching reversed kind, neighbor and
///   enclosure priority; every built-in mold is covered by a golden, but
///   arbitrary custom context combinations are not exhausted.
/// - witness: `highlight::tests::role_of_pins_context_free_classes`
/// - witness: `tests::highlight::corpus_roles_match_the_golden`
/// - witness: `highlight::tests::role_priorities_distinguish_competing_contexts`
#[spec(requires: facts.label.0 == "identifier", ensures: |ret| ret == match facts.kind.0 {
    "identifier" => HlRole::Variable,
    "projection_expression" => HlRole::Member,
    "at_type" | "offer_session_type" | "select_session_type" => HlRole::Label,
    "attribute_block" => HlRole::Other,
    "instantiation_expression" => HlRole::VariableParam,
    _ if facts.left.crosses(TileLabel(".")).0 => HlRole::Member,
    _ if facts.left.crosses(TileLabel(":")).0 && facts.right.crosses(TileLabel("(")).0 => HlRole::FunctionCall,
    _ if DEFINERS.iter().any(|&label| facts.left.crosses(TileLabel(label)).0) => if matches!(facts.opener, Opener::Bracket { label: TileLabel("("), .. }) { HlRole::VariableParam } else { HlRole::FunctionDef },
    _ if BINDERS.iter().any(|&label| facts.left.crosses(TileLabel(label)).0) => if matches!(facts.opener, Opener::Bracket { label: TileLabel("("), .. }) { HlRole::VariableParam } else { HlRole::VariableDef },
    _ => match facts.opener {
        Opener::Form => HlRole::Variable,
        Opener::Bracket { label, left } => match label.0 {
            "#{" | "{" => HlRole::Member,
            "@[" if facts.right.crosses(TileLabel(":")).0 => HlRole::VariableParam,
            "[" if matches!(facts.kind.0, "u_type" | "thunk_expression") => HlRole::Number,
            "[" if facts.kind.0 == "migrate_expression" => HlRole::Label,
            "@[" | "[" => HlRole::Other,
            "(" if left.crosses(TileLabel("select")).0 => HlRole::Label,
            "(" => HlRole::VariableParam,
            _ => HlRole::Variable,
        }
    }
})]
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
/// - hypothesis: For line comments, nested block comments, shebangs and
///   whitespace produced by the labeler, L3 exact role and no-span observations
///   catch wrong prefix priority and highlighting whitespace; arbitrary
///   non-layout text is outside the caller domain.
/// - witness: `tests::highlight::layout_takes_a_role_only_as_a_comment_or_a_shebang`
#[spec(ensures: |ret| { let bytes = <&str>::from(text); ret == if bytes.starts_with("//") || bytes.starts_with("/*") { Layout::Comment } else if bytes.starts_with("#!") { Layout::Directive } else { Layout::Whitespace } })]
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
    extern crate std;

    use alloc::string::ToString as _;
    use std::io::Write as _;

    use gandr_theory_graphs::Assoc;
    use gandr_theory_graphs::PrecDag;
    use gandr_theory_graphs::PrecSpec;

    use super::*;
    use crate::model::Regex;
    use crate::model::RuleName;
    use crate::model::Sort;
    use crate::surface::built_in;

    /// The molds labelled `label` whose rule realises `kind`, in id order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the label candidates with matching named kind, in
    ///   mold order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For the built-in class matrix and missing label and kind
    ///   boundaries, L3 exact roles and empty selections catch unfiltered or
    ///   reordered candidates; arbitrary grammars are not exhausted.
    /// - witness: `highlight::tests::role_of_pins_context_free_classes`
    #[spec(ensures: |ret| ret.iter().copied().eq(pbg.candidates(label).iter().copied().filter(|&id| pbg.named_kind(id).is_ok_and(|named| named.0 == kind.0))))]
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
        assert!(molds_of(&pbg, TileLabel("number"), NamedKind("absent-kind")).is_empty());
        assert!(molds_of(&pbg, TileLabel("absent-label"), NamedKind("number")).is_empty());
    }

    #[test]
    fn crossings_distinguish_tiles_from_holes()
    {
        let steps = [
            RCtxStep {
                crossed: StepSym::Sort(Sort::Expression),
            },
            RCtxStep {
                crossed: StepSym::Tile("first"),
            },
            RCtxStep {
                crossed: StepSym::Tile("last"),
            },
            RCtxStep {
                crossed: StepSym::Tile("first"),
            },
        ];
        for (label, expected) in [
            ("first", true),
            ("last", true),
            ("missing", false),
            ("expression", false),
        ] {
            assert_eq!(Crossing(expected), Side(&steps).crosses(TileLabel(label)));
            assert_eq!(Crossing(false), Side(&[]).crosses(TileLabel(label)));
        }
    }

    #[test]
    fn alternative_brackets_restore_before_each_branch()
    {
        let mut spec = PrecSpec::new();
        let base = spec.insert("base", Assoc::Non).expect("one group");
        let pbg = Pbg::build(PrecDag::build(&spec).expect("acyclic"), vec![
            Rule::new(
                RuleName("branch"),
                Sort::Expression,
                base,
                Regex::seq([
                    Regex::tile(TileLabel("(")),
                    Regex::alt([
                        Regex::seq([Regex::tile(TileLabel("[")), Regex::tile(TileLabel("x"))]),
                        Regex::seq([
                            Regex::tile(TileLabel("{")),
                            Regex::tile(TileLabel("y")),
                            Regex::tile(TileLabel("}")),
                        ]),
                    ]),
                    Regex::tile(TileLabel(")")),
                ]),
            ),
            Rule::new(
                RuleName("plain"),
                Sort::Expression,
                base,
                Regex::tile(TileLabel("z")),
            ),
        ])
        .expect("unique operator forms");
        let walked = occurrences(&pbg).expect("finite occurrences");
        let observed: Vec<_> = walked
            .iter()
            .map(|occurrence| (occurrence.label.0, occurrence.enclosure))
            .collect();
        assert_eq!(
            vec![
                ("(", Enclosure::Form),
                ("[", Enclosure::Bracket(MoldId::from(0))),
                ("x", Enclosure::Bracket(MoldId::from(1))),
                ("{", Enclosure::Bracket(MoldId::from(0))),
                ("y", Enclosure::Bracket(MoldId::from(3))),
                ("}", Enclosure::Bracket(MoldId::from(3))),
                (")", Enclosure::Bracket(MoldId::from(0))),
                ("z", Enclosure::Form),
            ],
            observed
        );
        assert_eq!(
            Some(RuleName("plain")),
            walked.last().map(|occurrence| occurrence.rule.name())
        );
    }

    #[test]
    fn role_priorities_distinguish_competing_contexts()
    {
        let definition = [RCtxStep {
            crossed: StepSym::Tile("def"),
        }];
        let dot_and_definition = [
            RCtxStep {
                crossed: StepSym::Tile("."),
            },
            definition[0],
        ];
        let call_and_definition = [
            RCtxStep {
                crossed: StepSym::Tile(":"),
            },
            definition[0],
        ];
        let binder = [RCtxStep {
            crossed: StepSym::Tile("as"),
        }];
        let definer_and_binder = [definition[0], binder[0]];
        let opening = [RCtxStep {
            crossed: StepSym::Tile("("),
        }];
        let selection = [RCtxStep {
            crossed: StepSym::Tile("select"),
        }];
        let parens = Opener::Bracket {
            label: TileLabel("("),
            left: Side(&[]),
        };
        let record = Opener::Bracket {
            label: TileLabel("#{"),
            left: Side(&[]),
        };
        for (kind, expected) in [
            ("line_comment", HlRole::Comment),
            ("block_comment", HlRole::Comment),
            ("shebang", HlRole::Directive),
            ("redirection_operator", HlRole::Operator),
        ] {
            for label in ["identifier", "number", "+", "unknown"] {
                assert_eq!(
                    expected,
                    classify(&MoldFacts {
                        label: TileLabel(label),
                        kind: NamedKind(kind),
                        left: Side(&definition),
                        right: Side(&[]),
                        opener: parens
                    })
                );
            }
        }
        let cases = [
            (
                "identifier",
                Side(&dot_and_definition),
                Side(&opening),
                parens,
                HlRole::Variable,
            ),
            (
                "projection_expression",
                Side(&definition),
                Side(&[]),
                parens,
                HlRole::Member,
            ),
            (
                "at_type",
                Side(&dot_and_definition),
                Side(&[]),
                record,
                HlRole::Label,
            ),
            (
                "attribute_block",
                Side(&definition),
                Side(&[]),
                parens,
                HlRole::Other,
            ),
            (
                "instantiation_expression",
                Side(&call_and_definition),
                Side(&opening),
                Opener::Form,
                HlRole::VariableParam,
            ),
            (
                "custom",
                Side(&dot_and_definition),
                Side(&opening),
                Opener::Form,
                HlRole::Member,
            ),
            (
                "custom",
                Side(&call_and_definition),
                Side(&opening),
                Opener::Form,
                HlRole::FunctionCall,
            ),
            (
                "custom",
                Side(&definer_and_binder),
                Side(&[]),
                Opener::Form,
                HlRole::FunctionDef,
            ),
            (
                "custom",
                Side(&definer_and_binder),
                Side(&[]),
                parens,
                HlRole::VariableParam,
            ),
            (
                "custom",
                Side(&binder),
                Side(&[]),
                record,
                HlRole::VariableDef,
            ),
            ("custom", Side(&[]), Side(&[]), record, HlRole::Member),
            (
                "custom",
                Side(&[]),
                Side(&[]),
                Opener::Bracket {
                    label: TileLabel("("),
                    left: Side(&selection),
                },
                HlRole::Label,
            ),
            (
                "custom",
                Side(&[]),
                Side(&[]),
                parens,
                HlRole::VariableParam,
            ),
            (
                "custom",
                Side(&[]),
                Side(&[]),
                Opener::Form,
                HlRole::Variable,
            ),
        ];
        for (kind, left, right, opener, expected) in cases {
            assert_eq!(
                expected,
                classify(&MoldFacts {
                    label: TileLabel("identifier"),
                    kind: NamedKind(kind),
                    left,
                    right,
                    opener
                })
            );
        }
        assert_eq!(
            HlRole::Other,
            classify(&MoldFacts {
                label: TileLabel("unclassified"),
                kind: NamedKind("custom"),
                left: Side(&[]),
                right: Side(&[]),
                opener: Opener::Form
            })
        );
    }

    #[test]
    fn highlight_error_sources_preserve_the_range_cause()
    {
        let cause = ByteRange::new(ByteOffset::from(19_usize), ByteOffset::from(7_usize))
            .expect_err("inverted range");
        let wrapped = HighlightError::InvertedSpan(cause);
        assert_eq!(
            Some(&cause),
            wrapped
                .source()
                .and_then(|source| source.downcast_ref::<InvertedRange>())
        );
        for local in [
            HighlightError::GrammarMismatch {
                tree: GrammarFingerprint::from(7_u64),
                table: GrammarFingerprint::from(9_u64),
            },
            HighlightError::UnknownMold {
                id: MoldId::from(17),
            },
        ] {
            assert!(local.source().is_none());
        }
    }

    #[test]
    fn highlight_error_messages_preserve_values_and_sink_failure()
    {
        let cause = ByteRange::new(ByteOffset::from(19_usize), ByteOffset::from(7_usize))
            .expect_err("inverted range");
        let cases: &[(HighlightError, &[&str])] = &[
            (
                HighlightError::GrammarMismatch {
                    tree: GrammarFingerprint::from(7_u64),
                    table: GrammarFingerprint::from(9_u64),
                },
                &["0x0000000000000007", "0x0000000000000009"],
            ),
            (
                HighlightError::UnknownMold {
                    id: MoldId::from(17),
                },
                &["17"],
            ),
            (HighlightError::InvertedSpan(cause), &["19", "7"]),
        ];
        for &(error, values) in cases {
            let message = error.to_string();
            for value in values {
                assert!(message.contains(value));
            }
            let mut bytes = [0_u8; 1];
            let mut sink = bytes.as_mut_slice();
            assert!(write!(&mut sink, "{error}").is_err());
        }
    }
}
