//! The molder: obligation-minimizing mold selection over labeled tokens.
//!
//! For each non-space [`Token`] the molder resolves the grammar
//! candidate molds to the one the melder should push. It is the
//! disambiguation layer between the labeler (lexical classes only) and the
//! melder (which needs a resolved [`MoldId`]):
//!
//! * **Candidate menu.** A lexeme maps to grammar tile labels
//!   ([`candidate_labels`]): a lowercase word tries its own text (catching
//!   keywords like `def`) then `identifier` / `type_variable`; an uppercase
//!   word tries its text (catching primitives like `Integer` and the `Type`
//!   keyword) then `constructor` / `type_identifier`; punctuation is its exact
//!   text. The candidate [`MoldId`]s are gathered into a sorted, de-duplicated
//!   set — no hash-iteration or allocation-address order reaches the decision.
//!   The uppercase-word reservation (`UPPER_KEYWORDS`) is a preference, not a
//!   ban: when no reserved candidate is admissible at the live frontier (a
//!   primitive-type spelling at a declaration-NAME slot, where only
//!   `type_identifier` molds), the menu widens to the class's generic labels
//!   (`Molder::gather_reserved_fallback`).
//! * **Candidate pre-filter.** [`MeldState::admits_at`] discards every
//!   structurally-inadmissible candidate against a once-per-token [`Frontier`]
//!   — a form-continuation tile with no matching open frontier, an operator
//!   with no left operand — before any dry-run. Most tokens collapse to a lone
//!   admissible candidate, taken with no dry-run at all (the batch-budget fast
//!   path).
//! * **Local key.** When several candidates survive, each is dry-run inside a
//!   [`mark`](crate::MeldState::mark) /
//!   [`rollback_to`](crate::MeldState::rollback_to) transaction and ranked by
//!   `(streaming Delta, continuation, sort)` — the melder's totality makes
//!   every push well-defined.
//! * **Shared-prefix lookahead.** The residual ambiguity is a shared-prefix
//!   form family whose openers tie on the local key and diverge only at a later
//!   tile (an `Inl` atom vs an `Inl(x)` constructor pattern, a `List` type
//!   identifier vs a `List(T)` application). It is settled by a bounded greedy
//!   lookahead over the next tokens; the grammar factors the wider families
//!   (`def`, `val`, `fn`, the `(` group, and the `#{` record) so they need
//!   none.
//! * **Determinism is HARD.** Candidates are visited in ascending [`MoldId`]
//!   order under a strict `<`, so an exact tie keeps the smaller `MoldId`
//!   (canonical grammar order). Nothing process-varying reaches the decision,
//!   so the molder is a pure function of the token stream — asserted identical
//!   across 100 randomized runs.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::CandidateCount;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_theory_graphs::Dir;

use crate::Frontier;
use crate::MeldState;
use crate::label::Lexeme;
use crate::label::Token;
use crate::meld::CandidateLabels;
use crate::meld::DeclarationStart;
use crate::meld::FormUnit;
use crate::meld::Mark;
use crate::meld::SpaceText;
use crate::meld::TileText;
use crate::meld::UnitSeam;
use crate::meld::declaration_head;
use crate::meld::primitive_copy_wrapper;
use crate::oblig::Delta;

/// The most candidate labels a single lexeme can map to (a lowercase word: its
/// own keyword tile spelling, `identifier`, `type_variable`, and `hole_name`).
const MAX_LABELS: usize = 4;

/// The bounded lookahead window (non-space tokens) that resolves a
/// shared-prefix form-variant tie.
///
/// After the admissibility pre-filter collapses the menu, the only residual
/// ambiguity is a shared-prefix form family whose opener molds tie on the local
/// key — a `constructor` atom vs a `constructor(…)` pattern, a
/// `type_identifier` vs a `type_identifier(T)` application (the `def` / `val` /
/// `fn` / `(` / `#{` families are factored, so they never reach here). Each is
/// LL(k) decidable within a few tiles of the shared prefix, so the molder
/// dry-runs each tied opener followed by a greedy molding of the next window
/// tokens and keeps the reading whose window completes with the fewest
/// obligations. The window is a single greedy continuation per candidate (beam
/// width one, no branching) so the cost stays bounded and the choice
/// deterministic.
const LOOKAHEAD: usize = 8;

/// Exact text of one labeled token.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TokenText<'text>(&'text str);

impl<'text> From<&'text str> for TokenText<'text>
{
    /// Adopt a token's borrowed text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'text str) -> Self
    {
        Self(value)
    }
}

impl<'text> From<TokenText<'text>> for &'text str
{
    /// Read the token text back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TokenText<'text>) -> Self
    {
        value.0
    }
}

/// Candidate grammar label spelling considered for one token.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CandidateLabel<'label>(&'label str);

impl<'label> From<&'label str> for CandidateLabel<'label>
{
    /// Adopt a label spelling as a candidate label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'label str) -> Self
    {
        Self(value)
    }
}

impl<'label> From<TokenText<'label>> for CandidateLabel<'label>
{
    /// Use a token's text as the label it spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TokenText<'label>) -> Self
    {
        Self(<&str>::from(value))
    }
}

impl<'text> From<TokenText<'text>> for TileText<'text>
{
    /// Carry a token's text into the melder as tile text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TokenText<'text>) -> Self
    {
        Self::from(<&str>::from(value))
    }
}

impl<'label> From<CandidateLabel<'label>> for &'label str
{
    /// Read the label spelling back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CandidateLabel<'label>) -> Self
    {
        value.0
    }
}

primitive_copy_wrapper!(
    /// Whether direct circuit-rule binder reading is admitted at its opener.
    struct DirectRuleBinderAdmission(bool);
);

/// Dense token-stream position used by bounded lookahead and form runs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TokenIndex(usize);

impl From<usize> for TokenIndex
{
    /// Adopt a host position as a token index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<TokenIndex> for usize
{
    /// Read the token index back as a host position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TokenIndex) -> Self
    {
        value.0
    }
}

/// A half-open run of token-stream positions: the tokens one molding pass
/// pushes, inside a stream whose later tokens it still reads as lookahead.
///
/// # Specification
/// - requires: nothing.
/// - ensures: names the positions from `start` up to, not including, `end`; an
///   `end` before `start` names no position.
/// - panics: none.
/// - executable: none — this data type has no call boundary; its constructor
///   and observers carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a stream molded as consecutive runs commits the state the
///   whole stream does, and a run's lookahead reads past its end; an off-by-one
///   bound pushes a token twice or drops one.
/// - witness: `mold::tests::runs_mold_as_the_whole_stream`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TokenRun
{
    /// The first position pushed.
    start: TokenIndex,
    /// The position after the last one pushed.
    end: TokenIndex,
}

impl TokenRun
{
    /// The run from `start` up to, not including, `end`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        start: TokenIndex,
        end: TokenIndex,
    ) -> Self
    {
        Self { start, end }
    }

    /// The first position the run pushes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(self) -> TokenIndex
    {
        self.start
    }

    /// The position after the last one the run pushes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(self) -> TokenIndex
    {
        self.end
    }
}

/// Binary rank component in a molder candidate key.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CandidateRank(u8);

impl From<bool> for CandidateRank
{
    /// Rank one criterion: `false` ranks before `true`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: bool) -> Self
    {
        Self(u8::from(value))
    }
}

/// Local candidate minimization key: `(Delta, continuation, sort, operand
/// continuation)`.
///
/// * `Delta` is the obligation change the push itself flags — the **streaming**
///   delta only. It deliberately excludes the `finalize` completion penalty: a
///   form-start (`Inl` opening a constructor pattern, `def` opening an item)
///   momentarily leaves the slope incomplete, and penalizing that would make
///   the bare atom always strictly cheaper, so the two would never tie and the
///   shared-prefix lookahead ([`Molder::choose_stream`]) would never fire to
///   see the discriminating tile. Completion is measured in the lookahead
///   window, where it belongs.
/// * The **continuation** rank is `0` when the candidate `≐`-continues the open
///   form frontier and `1` otherwise, so a `def`'s name reads as the form's
///   name tile rather than a bare variable.
/// * The **sort** rank is `0` when the candidate's grammar sort matches the
///   slot the head expects ([`MeldState::expected_operand_sort`]) and `1`
///   otherwise, so `"hi"` reads as the expression string at an expression slot
///   and the pattern string in a pattern slot.
/// * The **operand continuation** rank is `0` when the candidate extends the
///   operand at the head and `1` otherwise.
///
/// An exact key tie keeps the smaller [`MoldId`] — the documented,
/// process-invariant tie-break.
///
/// # Specification
/// - ensures: compares obligation delta before form continuation, expected sort
///   and operand continuation, in that order; lower ranks win.
/// - panics: none.
/// - executable: none — derived ordering has no handwritten invocation boundary
///   on this record; candidate scoring supplies executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — adjacent priority levels disagree in paired keys;
///   comparisons expose the winning criterion. Swapping fields or reversing any
///   rank changes a pair even when all lower-priority ranks disagree.
/// - witness: `mold::tests::candidate_key_priorities_are_lexicographic`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CandidateKey
{
    /// Streaming obligation delta.
    delta: Delta,
    /// Rank for whether the tile continues the open form.
    continuation: CandidateRank,
    /// Rank for whether the tile sort matches the expected operand sort.
    sort: CandidateRank,
    /// Rank for whether the tile continues the left operand.
    operand_continuation: CandidateRank,
}

/// Every candidate floor key — the empty delta with each combination of the
/// three ranks — in ascending order.
const RANK_FLOORS: [CandidateKey; 8] = [
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(0),
        sort: CandidateRank(0),
        operand_continuation: CandidateRank(0),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(0),
        sort: CandidateRank(0),
        operand_continuation: CandidateRank(1),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(0),
        sort: CandidateRank(1),
        operand_continuation: CandidateRank(0),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(0),
        sort: CandidateRank(1),
        operand_continuation: CandidateRank(1),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(1),
        sort: CandidateRank(0),
        operand_continuation: CandidateRank(0),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(1),
        sort: CandidateRank(0),
        operand_continuation: CandidateRank(1),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(1),
        sort: CandidateRank(1),
        operand_continuation: CandidateRank(0),
    },
    CandidateKey {
        delta: Delta::empty(),
        continuation: CandidateRank(1),
        sort: CandidateRank(1),
        operand_continuation: CandidateRank(1),
    },
];

/// Candidate menu scope used by the gather step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CandidateMenu
{
    /// Fresh-slot candidates plus the open form's matching successors.
    Fresh,
    /// Full declared candidate menu.
    Declared,
}

/// The delta a tied opener's lookahead window must stay below to win.
///
/// # Specification
/// - ensures: `Below` carries the least delta an earlier opener's window
///   reached; a later opener wins only with a strictly smaller one.
/// - panics: none.
/// - executable: none — a plain value; [`Molder::mold_window`] carries the
///   executable clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WindowBound
{
    /// No earlier opener's window has finished: the window runs to its end.
    Unbounded,
    /// The least delta an earlier opener's window reached.
    Below(Delta),
}

/// How a lookahead window ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WindowEnd
{
    /// Every token the window covers was molded.
    Molded,
    /// The window's obligations reached its bound before it finished, so its
    /// opener cannot win; the remaining tokens were not molded.
    Dominated,
}

/// Wrap the molder's source view for the labeler token-text API.
///
/// # Specification
/// trivial.
#[inline]
fn source_slice(src: SourceText<'_>) -> SourceFragment<'_>
{
    SourceFragment::from(<&str>::from(src))
}

/// The reserved lowercase keywords (the tree-sitter grammar's `KW`, the wired
/// subset).
///
/// A reserved keyword is never an ordinary `identifier` (tree-sitter's `word`
/// reservation), so a lowercase word matching one molds only to its own
/// keyword tile — not the wide identifier menu that would let, say, `ret` be
/// read as a variable.
///
/// The fold-in globally reserves the thirteen new
/// keyword-led forms' leads — `data` / `codata` declarations, `def rec`
/// (`rec`), `data` / `codata` operation and 2-cell members (`op` / `rule`),
/// the `for … in` / `while` / `loop` / `break` / `continue` control forms,
/// the `case … with …` view, the `import` declaration, and the `module`
/// declaration. A corpus + fixture sweep found no collision with any existing
/// identifier, so all reserve globally (the keyword table is provisional; a
/// real collision would move the offender to a contextual keyword). `codata`
/// reserves as one whole word — the labeler munches the maximal
/// `[A-Za-z0-9_]` run, so `codata` never lexes as `co` + `data` (the
/// longest-match hazard is a non-issue here). The operator-declaration fixity
/// classes (`infixl` / `infixr` / `infix` / `prefix` / `postfix`) are
/// deliberately NOT reserved: they mold as contextual tiles only where the
/// `op`-led fixity form expects them, so they remain ordinary identifiers
/// everywhere else.
/// `run` and `val` are reserved as the distinct leads of computation-result
/// and value-binding statements; neither enters the ordinary identifier menu.
/// The retired standalone `let` spelling is deliberately not reserved.
///
/// The circuit block form reserves exactly its two **item-position**
/// leads, `sign` and `oper`: at a fresh top-level slot a lowercase word is
/// otherwise an expression statement, so an unreserved form-first lead would
/// tie its own tile against `identifier` at every declaration. Its four other
/// leads stay **contextual** — the member keyword `sort` (beside the already-
/// reserved `data` / `rule`) and the body statements `node` / `feed` are
/// `≐`-successors inside an open `sign` block or circuit body, so a user
/// program may still bind `sort`, `node`, or `feed` as an ordinary name;
/// `sign` and `oper` it may not. `sort` in particular could not be reserved
/// even if wanted: `list.sort` is a live projection in the corpus. Contextual
/// is not the same as inadmissible-elsewhere, and the circuit grammar module
/// records the one slot where `sort`'s mold does collide with a type variable.
const KEYWORDS: &[&str] = &[
    "def", "val", "run", "leta", "as", "extern", "from", "type", "fn", "ret", "thunk", "force",
    "case", "if", "else", "co", "hold", "dup", "drop", "send", "recv", "close", "select", "offer",
    "fork", "acquire", "release", "migrate", "at", "true", "false", "forall", "mu", "end", "data",
    "codata", "rec", "op", "rule", "for", "in", "while", "loop", "break", "continue", "with",
    "import", "module", "sign", "oper",
];

/// Return the grammar tile labels to enumerate for a labeled token.
///
/// The returned slice is in a fixed order; the molder unions the `candidates`
/// of every label into a sorted set, so the order here does not affect the
/// decision — only which molds are considered. A space or unknown lexeme maps
/// to no labels (it never molds).
///
/// # Specification
/// - requires: `text` is the token's exact source slice.
/// - ensures: returns the deterministic label menu for the lexeme; empty for
///   [`Lexeme::Space`] and [`Lexeme::Unknown`].
/// - provides: the molder's per-token candidate-label source.
/// - fails: never.
/// - panics: none.
///
///
/// # Adequacy
/// - hypothesis: L3 — every lexeme menu, reserved and ordinary words, and
///   canonical versus dialect shell openers expose exact label sequences.
///   Dropping a generic alternative, widening a keyword or losing the source
///   spelling changes the menu.
/// - witness: `mold::tests::keyword_and_identifier_share_a_word_menu`
/// - witness: `mold::tests::literal_and_shell_menus_are_exact`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.is_empty() == matches!(lexeme, Lexeme::Space | Lexeme::Unknown) && ret.len() <= MAX_LABELS && (!matches!(lexeme, Lexeme::LowerWord | Lexeme::UpperWord | Lexeme::Punct) || ret.first().is_some_and(|label| label.0 == text.0)))]
pub fn candidate_labels<'text>(
    lexeme: Lexeme,
    text: TokenText<'text>,
) -> Vec<CandidateLabel<'text>>
{
    let text = <&str>::from(text);
    let mut labels: Vec<CandidateLabel<'text>> = Vec::with_capacity(MAX_LABELS);
    match lexeme {
        | Lexeme::LowerWord => {
            labels.push(CandidateLabel::from(text));
            // A reserved keyword is never an identifier; only its keyword tile
            // is a candidate (tree-sitter `word` reservation).
            if !KEYWORDS.contains(&text) {
                labels.push(CandidateLabel::from("identifier"));
                labels.push(CandidateLabel::from("type_variable"));
                // A `hole_name` is a lowercase word too, but it only occurs as
                // the optional name after a `?` hole (`?name`). Its mold is a
                // form-end with a `≐`-predecessor (`?`), so it is admissible
                // *only* while a `?` frontier is open and inadmissible at every
                // other lowercase-word slot — the pre-filter drops it there, so
                // adding it here lets `?name` attach without competing with a
                // bare `identifier` anywhere else.
                labels.push(CandidateLabel::from("hole_name"));
            }
        },
        | Lexeme::UpperWord => {
            labels.push(CandidateLabel::from(text));
            // A reserved primitive/type keyword is never a constructor or a
            // type identifier; only its own tile is a candidate.
            if !UPPER_KEYWORDS.contains(&text) {
                labels.push(CandidateLabel::from("constructor"));
                labels.push(CandidateLabel::from("type_identifier"));
            }
        },
        | Lexeme::Number => labels.push(CandidateLabel::from("number")),
        | Lexeme::TypedNumber => labels.push(CandidateLabel::from("typed_number")),
        | Lexeme::Character => labels.push(CandidateLabel::from("character")),
        | Lexeme::Quote => labels.push(CandidateLabel::from("\"")),
        | Lexeme::StringFragment => {
            labels.push(CandidateLabel::from("string_fragment"));
            labels.push(CandidateLabel::from("double_string_fragment"));
        },
        | Lexeme::EscapeSequence => labels.push(CandidateLabel::from("escape_sequence")),
        // ONE label: the grammar's single shell-word atom class.
        // The former `command_name` / `argument` labels rode the
        // dead composite shell rules; with those folded away, a shell word has
        // exactly one mold and takes the molder's sole-admissible fast path —
        // no dry-run, no lookahead, per word.
        | Lexeme::ShellWord => labels.push(CandidateLabel::from("shell_word")),
        // ONE label, like the shell word: the labeler has already decided the
        // `NAME=value` shape, so the assignment takes the sole-admissible fast
        // path too (no dry-run, no lookahead). The mold and its walk-index entry
        // already existed — only the tile was missing.
        | Lexeme::EnvAssign => labels.push(CandidateLabel::from("environment_assignment")),
        | Lexeme::SingleQuotedContent => {
            labels.push(CandidateLabel::from("single_quoted_content"));
        },
        | Lexeme::VariableName => labels.push(CandidateLabel::from("variable_name")),
        | Lexeme::SubshellOpen => labels.push(CandidateLabel::from("subshell_open")),
        | Lexeme::SubshellClose => labels.push(CandidateLabel::from("subshell_close")),
        | Lexeme::FileDescriptor => labels.push(CandidateLabel::from("file_descriptor")),
        | Lexeme::Punct => {
            labels.push(CandidateLabel::from(text));
            // A dialect-bearing shell opener (`#!sh{`, `$!py{`) lexes as one
            // punctuation token; map it to the canonical opener label.
            if text.starts_with("#!") && text.ends_with('{') {
                labels.push(CandidateLabel::from("#!{"));
            }
            else if text.starts_with("$!") && text.ends_with('{') {
                labels.push(CandidateLabel::from("command_substitution_start"));
            }
        },
        | Lexeme::Space | Lexeme::Unknown => {},
    }
    labels
}

/// The reserved uppercase words (the tree-sitter grammar's `KW` / primitive
/// type names).
///
/// A reserved uppercase word (a primitive type `Integer` / `String` / …, or the
/// universe `Type`) PREFERS its own tile — the
/// `constructor` / `type_identifier` menu would leave `Integer` tied between
/// the primitive-type atom and a spurious `type_identifier` reading at every
/// type slot. The reservation is a preference, not a ban: at a slot where the
/// reserved tile is structurally inadmissible (a declaration's NAME position),
/// [`Molder::gather_reserved_fallback`] re-admits the generic labels so the
/// word can still name the declaration (`sign Unknown`). `U` and `F` are not
/// reserved: the bridges are the compound tiles `+U` and `-F`, and the bare
/// letters are names like any other.
const UPPER_KEYWORDS: &[&str] = &[
    "Any", "Unknown", "Never", "Boolean", "Integer", "Char", "String", "Symbol", "Unit", "Void",
    "Path", "Type",
];

/// Return the next non-space token after `index`.
///
/// # Specification
/// - requires: `index` indexes the same token stream as `tokens`.
/// - ensures: returns the next significant token and its index, or `None` at
///   the end of the stream.
/// - provides: bounded lexical lookahead for shared-prefix mold choices.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — adjacent significant tokens, intervening spaces, a
///   trailing space run and an exhausted or host-ceiling cursor expose the
///   first successor. Returning the current token or skipping a significant
///   token changes its position and class.
/// - witness: `mold::tests::lookahead_skips_only_space_and_never_the_current_token`
#[spec(ensures: |ret| ret == tokens.iter().copied().enumerate().skip(index.0.saturating_add(1)).find(|&(_, token)| token.lexeme != Lexeme::Space).map(|(position, token)| (TokenIndex::from(position), token)))]
fn next_significant(
    tokens: &[Token],
    index: TokenIndex,
) -> Option<(TokenIndex, Token)>
{
    let mut next = usize::from(index).saturating_add(1);
    while let Some(&token) = tokens.get(next) {
        if !matches!(token.lexeme, Lexeme::Space) {
            return Some((TokenIndex::from(next), token));
        }
        next = next.saturating_add(1);
    }
    None
}

/// The obligation-minimizing mold selector over a checked PBG.
///
/// The molder owns a reusable candidate buffer so the per-token dry-run loop
/// allocates nothing on the happy path. It is stateless beyond
/// that buffer: a single molder can drive any number of independent melds.
///
/// # Specification
/// - requires: `pbg` is the grammar the driven [`MeldState`] was built over.
/// - ensures: [`mold`](Molder::mold) pushes exactly one tile per non-space
///   token, choosing the admissible `(Delta, continuation, sort, MoldId)`
///   minimum candidate; a token with no candidate molds takes the
///   totally-defined unmolded path.
/// - provides: the deterministic labeler→melder bridge.
/// - fails: never; the melder push is total.
/// - panics: none.
/// - executable: none — this state carrier has no invocation boundary;
///   candidate operations carry its executable menu invariants.
///
/// # Adequacy
/// - hypothesis: L3 — the minimum-key choice, the tie-break, and the
///   no-candidate path are each observed.
/// - witness: `mold::tests::molding_is_deterministic_across_runs`
pub struct Molder<'pbg>
{
    /// The grammar whose candidate menus the molder reads.
    pbg: &'pbg Pbg,
    /// Reused candidate-mold buffer, sorted and de-duplicated per token.
    candidates: Vec<MoldId>,
    /// Static candidate labels declared by this grammar, sorted by label text.
    labels: Vec<TileLabel>,
    /// Reused per-token candidates that survive the pre-filter (or the whole
    /// menu when none does), in ascending `MoldId` order.
    eligible: Vec<MoldId>,
    /// Reused floor keys of the eligible candidates, beside each mold.
    ranked: Vec<(CandidateKey, MoldId)>,
    /// Reused candidates holding the least key, in ascending `MoldId` order.
    tied: Vec<MoldId>,
    /// Reused tied lookahead openers; separate from `tied` because each
    /// opener's window scores its own tokens.
    openers: Vec<MoldId>,
}

impl<'pbg> Molder<'pbg>
{
    /// Create a molder over `pbg`.
    ///
    /// # Specification
    /// - requires: `pbg` is a checked PBG.
    /// - ensures: returns a molder with an empty candidate buffer.
    /// - provides: the molder constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh molder resolves the first and last declared
    ///   labels and rejects an absent label before any token is gathered. Dirty
    ///   buffers, an unsorted label index or omitted endpoints change the
    ///   queries.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.candidates.is_empty() && ret.eligible.is_empty() && ret.ranked.is_empty() && ret.tied.is_empty() && ret.openers.is_empty() && ret.labels.iter().zip(ret.labels.iter().skip(1)).all(|(left, right)| left.as_ref() < right.as_ref()))]
    pub fn new(pbg: &'pbg Pbg) -> Self
    {
        let labels = pbg
            .candidate_counts()
            .into_iter()
            .map(|(label, _count)| label)
            .collect();
        Self {
            pbg,
            candidates: Vec::new(),
            labels,
            eligible: Vec::new(),
            ranked: Vec::new(),
            tied: Vec::new(),
            openers: Vec::new(),
        }
    }

    /// The grammar this molder molds against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn pbg(&self) -> &'pbg Pbg
    {
        self.pbg
    }

    /// Resolve a candidate label spelling to this grammar's static tile label.
    ///
    /// # Specification
    /// - ensures: returns the declared label with exactly this spelling, or
    ///   none when absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last declared spellings and an absent
    ///   neighbor expose the optional label. Off-by-one binary-search bounds or
    ///   a spurious fallback label change the answer.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[spec(ensures: |ret| ret == self.labels.iter().copied().find(|candidate| candidate.as_ref() == label.0))]
    fn candidate_label(
        &self,
        label: CandidateLabel<'_>,
    ) -> Option<TileLabel>
    {
        let label = <&str>::from(label);
        let index = self
            .labels
            .binary_search_by(|candidate| candidate.as_ref().cmp(label))
            .ok()?;
        self.labels.get(index).copied()
    }

    /// Return the number of candidate molds considered for a labeled token.
    ///
    /// This is the molder's per-token cost signal (the candidate-loop
    /// profile); it does not mutate any melder state.
    ///
    /// # Specification
    /// - requires: `token` came from the labeler over `src`.
    /// - ensures: returns the size of the de-duplicated candidate set (0 for a
    ///   space or unmoldable token).
    /// - provides: the candidate-count cost probe for benchmarks and reports.
    /// - fails: never.
    /// - panics: none.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a wide identifier menu, narrow punctuation, space and
    ///   unknown tokens expose exact canonical-union cardinality. Duplicate
    ///   candidates or retaining the preceding token menu changes the count.
    /// - witness: `mold::tests::identifier_menu_is_wide`
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[inline]
    #[spec(ensures: |ret| ret.0 == self.candidates.len() && self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    pub fn candidate_count(
        &mut self,
        token: Token,
        src: SourceText<'_>,
    ) -> CandidateCount
    {
        // The bench probe reports the full declared menu (no live frontier).
        let source = source_slice(src);
        self.gather_menu(token, &source, None, CandidateMenu::Declared);
        CandidateCount(self.candidates.len())
    }

    /// Mold and push one labeled token into `state`, choosing the minimum.
    ///
    /// A space token is ignored here (the batch driver records it directly). A
    /// token whose candidate set is empty takes the melder's totally-defined
    /// unmolded path ([`crate::Oblig::UnmoldedTok`]).
    ///
    /// # Specification
    /// - requires: `state` was built over this molder's `pbg`; `token` came
    ///   from the labeler over `src`.
    /// - ensures: pushes exactly the `(Delta, MoldId)`-minimum candidate mold,
    ///   or the unmolded path when no candidate exists; a space token is a
    ///   no-op.
    /// - provides: the molder's push operation.
    /// - fails: never; the underlying push is total.
    /// - panics: none.
    /// - intension: candidates are dry-run in ascending `MoldId` order inside a
    ///   `mark`/`rollback_to` transaction; the first strict delta improvement
    ///   wins, so equal deltas keep the smaller `MoldId`.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-valid tokens include complete and bare holes,
    ///   ordinary atoms, unknown bytes and layout. Committed structure and
    ///   exact checkpoint bytes expose premature hole closure, unmolded-path
    ///   loss and a non-no-op space.
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    /// - witness: `mold::tests::unmoldable_token_takes_the_unmolded_path`
    /// - witness: `mold::tests::space_and_empty_stream_are_exact_noops`
    #[inline]
    #[spec(requires: <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
    pub fn mold(
        &mut self,
        state: &mut MeldState<'_>,
        token: Token,
        src: SourceText<'_>,
    )
    {
        if matches!(token.lexeme, Lexeme::Space) {
            return;
        }
        let source = source_slice(src);
        let slice = token.text(&source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        self.settle_shadowing(state, token, &source);
        self.gather(state, token, &source);
        state.settle_declaration_boundary(&self.candidates);
        let best = self.choose(state, text);
        Self::push_choice(state, best, text);
    }

    /// Mold and push a whole labeled token stream (the batch driver).
    ///
    /// This is the batch driver's molder ([`crate::parse`](fn@crate::parse)).
    /// It molds each non-space token by the admissibility-filtered
    /// `(Delta, continuation, sort, MoldId)` order (see
    /// [`choose`](Self::choose)) and records each space verbatim. The
    /// pre-filter ([`MeldState::admits`]) is what lets a single greedy pass
    /// find the globally-consistent zero-obligation molding: a
    /// form-continuation candidate that no open frontier accepts is
    /// discarded before it can strand the parse, and shared-prefix form
    /// variants are factored at the grammar so their discriminating tile
    /// continues exactly one open frontier.
    ///
    /// # Specification
    /// - requires: `state` was built over this molder's `pbg`; `tokens` came
    ///   from the labeler over `src`.
    /// - ensures: pushes exactly one tile per non-space token — the
    ///   admissibility-filtered minimum — and records each space; deterministic
    ///   (the choice is a pure function of the token stream and grammar table).
    /// - provides: the batch molder.
    /// - fails: never; every push is total.
    /// - panics: none.
    /// - intension: each token is molded by [`choose`](Self::choose) against
    ///   the live slope, in a single left-to-right pass with no backtracking.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty input, interleaved trivia, malformed input and
    ///   complete grammar forms expose exact source reconstruction and repair
    ///   classes. Dropped space, extra pushes or a different candidate decision
    ///   changes the tree or obligations.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    /// - witness: `mold::tests::space_and_empty_stream_are_exact_noops`
    /// - witness: `parse::tests::parse_is_lossless_and_hash_stable`
    #[inline]
    #[spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()))]
    pub fn mold_stream(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        src: SourceText<'_>,
    )
    {
        let whole = TokenRun::new(TokenIndex::from(0_usize), TokenIndex::from(tokens.len()));
        self.mold_run(state, tokens, whole, src);
    }

    /// Mold and push the tokens of `run`, reading the stream past the run's
    /// end as lookahead only.
    ///
    /// Each token is molded exactly as [`mold_stream`](Self::mold_stream)
    /// molds it, lookahead windows included, so a stream molded as
    /// consecutive runs into one state leaves the state the whole stream does.
    ///
    /// # Specification
    /// - requires: `state` was built over this molder's `pbg`; `tokens` came
    ///   from the labeler over `src`.
    /// - ensures: pushes exactly one tile per non-space token of `run` and
    ///   records each of its spaces, choosing each tile as
    ///   [`mold_stream`](Self::mold_stream) would at that position; never
    ///   pushes a token outside `run`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus source molded as two runs split at every
    ///   significant position commits the whole stream's checkpoint bytes; a
    ///   lookahead that stopped at the run's end, or a bound off by one,
    ///   changes a choice or a pushed token.
    /// - witness: `mold::tests::runs_mold_as_the_whole_stream`
    #[inline]
    #[spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()))]
    pub fn mold_run(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        run: TokenRun,
        src: SourceText<'_>,
    )
    {
        let source = source_slice(src);
        let end = usize::from(run.end()).min(tokens.len());
        let mut index = usize::from(run.start());
        while index < end {
            let Some(&token) = tokens.get(index)
            else {
                break;
            };
            let slice = token.text(&source);
            if matches!(token.lexeme, Lexeme::Space) {
                state.space(SpaceText::from(AsRef::<str>::as_ref(&slice)));
            }
            else {
                let text = TokenText::from(AsRef::<str>::as_ref(&slice));
                self.settle_shadowing(state, token, &source);
                self.gather(state, token, &source);
                state.settle_declaration_boundary(&self.candidates);
                let best = self.choose_stream(state, tokens, TokenIndex::from(index), &source);
                Self::push_choice(state, best, text);
            }
            index = index.saturating_add(1);
        }
    }

    /// Split a labeled stream into form runs at its predicted top-level
    /// declaration boundaries.
    ///
    /// A boundary is predicted before a significant token that some
    /// fresh-slot reading of opens an item-position declaration
    /// ([`declaration_head`]), when the token before it is a `;` or a `}`
    /// and no bracket opened before it is still unclosed. The prediction
    /// reads tokens alone, so it is cheap and may be wrong: a `def` that a
    /// keyword form without brackets still holds is predicted too.
    /// [`join_unit`](Self::join_unit) re-molds a run whose seam does not
    /// hold, so a wrong prediction costs time, never the parse.
    ///
    /// # Specification
    /// - requires: `tokens` came from the labeler over `src`.
    /// - ensures: returns consecutive runs covering every position of `tokens`
    ///   exactly once, the first starting at position zero, each later one
    ///   starting at a predicted declaration head; one empty run for an empty
    ///   stream.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of declarations, one decorated by an
    ///   attribute, one a module holding members, splits before each top-level
    ///   head and nowhere else; a run that skipped or repeated a token, a cut
    ///   inside brackets or between an attribute and its declaration, changes
    ///   the runs.
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    #[inline]
    #[must_use]
    #[spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()), ensures: |ret| ret.first().is_some_and(|run| usize::from(run.start()) == 0) && ret.last().is_some_and(|run| usize::from(run.end()) == tokens.len()) && ret.windows(2).all(|pair| matches!(pair, [left, right] if left.end() == right.start())) && (tokens.is_empty() || ret.iter().all(|run| run.start() < run.end())))]
    pub fn form_runs(
        &self,
        tokens: &[Token],
        src: SourceText<'_>,
    ) -> Vec<TokenRun>
    {
        let source = source_slice(src);
        let mut runs = Vec::new();
        let mut start = 0_usize;
        let mut depth = 0_usize;
        let mut after_terminator = false;
        for (index, &token) in tokens.iter().enumerate() {
            if matches!(token.lexeme, Lexeme::Space) {
                continue;
            }
            if depth == 0 && after_terminator && bool::from(self.heads_declaration(token, &source))
            {
                runs.push(TokenRun::new(
                    TokenIndex::from(start),
                    TokenIndex::from(index),
                ));
                start = index;
            }
            let slice = token.text(&source);
            let text = AsRef::<str>::as_ref(&slice);
            let bracket = matches!(
                token.lexeme,
                Lexeme::Punct | Lexeme::SubshellOpen | Lexeme::SubshellClose
            );
            if bracket && text.ends_with(['(', '[', '{']) {
                depth = depth.saturating_add(1);
            }
            else if bracket && matches!(text, ")" | "]" | "}") {
                depth = depth.saturating_sub(1);
            }
            after_terminator = matches!(token.lexeme, Lexeme::Punct) && matches!(text, ";" | "}");
        }
        runs.push(TokenRun::new(
            TokenIndex::from(start),
            TokenIndex::from(tokens.len()),
        ));
        runs
    }

    /// Return whether some fresh-slot reading of `token` opens an
    /// item-position declaration.
    ///
    /// # Specification
    /// - requires: the token bounds identify its exact source fragment.
    /// - ensures: true exactly when one of the token's candidate labels has a
    ///   fresh-slot mold that [`declaration_head`] accepts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — declaration keywords, an attribute opener, an
    ///   identifier and a terminator distinguish heads from the rest; reading
    ///   the declared menu instead of the fresh one, or one label of several,
    ///   moves a predicted boundary.
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    #[spec(requires: source.as_ref().get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
    fn heads_declaration<'src>(
        &self,
        token: Token,
        source: &'src SourceFragment<'src>,
    ) -> DeclarationStart
    {
        let slice = token.text(source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        let heads = candidate_labels(token.lexeme, text).iter().any(|&label| {
            self.candidate_label(label).is_some_and(|label| {
                self.pbg
                    .fresh_candidates(label)
                    .iter()
                    .any(|&mold| bool::from(declaration_head(self.pbg, mold)))
            })
        });
        DeclarationStart::from(heads)
    }

    /// Mold `run` of `tokens` into a fresh form unit.
    ///
    /// The unit begins from the empty slope when `run` starts the stream and
    /// from the form-boundary checkpoint otherwise
    /// ([`FormUnit::new`]); either way its tokens are molded as
    /// [`mold_run`](Self::mold_run) molds them, lookahead past the run
    /// included.
    ///
    /// # Specification
    /// - requires: `tokens` came from the labeler over `src`.
    /// - ensures: returns the unit for `run`, every token of `run` molded into
    ///   it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
    ///   four fragments, molded unit by unit and joined, parse as the whole
    ///   source; a unit begun from the wrong base, or molded without its
    ///   lookahead, changes a joined tree.
    /// - witness: `parse::tests::form_split_parses_as_the_whole_source`
    /// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
    #[inline]
    #[must_use]
    #[spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()), ensures: |ret| ret.run() == run)]
    pub fn mold_unit(
        &mut self,
        tokens: &[Token],
        run: TokenRun,
        src: SourceText<'_>,
    ) -> FormUnit<'pbg>
    {
        let mut unit = FormUnit::new(self.pbg, run);
        self.mold_run(unit.state_mut(), tokens, run, src);
        unit
    }

    /// Join `unit` to `whole`, the state the runs before it left, re-molding
    /// the unit's run onto `whole` when the seam does not hold.
    ///
    /// # Specification
    /// - requires: `whole` holds exactly the runs before `unit`'s, molded or
    ///   joined in order, with no mark live; `tokens` came from the labeler
    ///   over `src`.
    /// - ensures: `whole` then holds the runs through `unit`'s exactly as
    ///   [`mold_run`](Self::mold_run) over each in turn would leave it; returns
    ///   how the seam stood.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
    ///   four fragments, split at every predicted boundary, join to the whole
    ///   parse whether their seams hold or break; skipping the re-mold on a
    ///   broken seam drops the run's tokens.
    /// - witness: `parse::tests::form_split_parses_as_the_whole_source`
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    /// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
    #[inline]
    #[spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()))]
    pub fn join_unit<'state>(
        &mut self,
        whole: &mut MeldState<'state>,
        unit: FormUnit<'state>,
        tokens: &[Token],
        src: SourceText<'_>,
    ) -> UnitSeam
    {
        let run = unit.run();
        let seam = whole.join_unit(unit);
        if matches!(seam, UnitSeam::Broken(_)) {
            self.mold_run(whole, tokens, run, src);
        }
        seam
    }

    /// Eagerly settle any completable `?` hole frontier the upcoming `token`
    /// cannot continue, before it is gathered / chosen.
    ///
    /// A pass-through to
    /// [`MeldState::settle_shadowing_frontiers`](crate::MeldState::settle_shadowing_frontiers)
    /// over the token's candidate labels: it keeps a bare hole from shadowing
    /// an enclosing form in the molder's frontier queries. A hole before a
    /// `hole_name` word stays open so the name attaches.
    ///
    /// # Specification
    /// - requires: the token bounds identify its exact source fragment.
    /// - ensures: settles shadowing holes only when the incoming label cannot
    ///   continue them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-valid tokens include complete and bare holes,
    ///   ordinary atoms, unknown bytes and layout. Committed structure and
    ///   exact checkpoint bytes expose premature hole closure, unmolded-path
    ///   loss and a non-no-op space.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[inline]
    #[spec(requires: source.as_ref().get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
    fn settle_shadowing<'src>(
        &self,
        state: &mut MeldState<'_>,
        token: Token,
        source: &'src SourceFragment<'src>,
    )
    {
        let slice = token.text(source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        let labels = candidate_labels(token.lexeme, text);
        let mut raw_labels = [""; MAX_LABELS];
        let mut count = 0_usize;
        for &label in &labels {
            let Some(label) = self.candidate_label(label)
            else {
                continue;
            };
            if let Some(slot) = raw_labels.get_mut(count) {
                *slot = label.0;
                count = count.saturating_add(1);
            }
        }
        state.settle_shadowing_frontiers(CandidateLabels::from(
            raw_labels.get(.. count).unwrap_or(&[]),
        ));
    }

    /// Push the molder's choice, or the unmolded path when there is none.
    ///
    /// # Specification
    /// - ensures: pushes the selected mold; an absent choice preserves text
    ///   through an unmolded-token obligation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a valid atom and an absent candidate expose the
    ///   committed text and unmolded obligation. Treating absence as no-op or
    ///   using a real fallback mold changes those observations.
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    /// - witness: `mold::tests::unmoldable_token_takes_the_unmolded_path`
    #[spec(ensures: |_| choice.is_some() || state.obligations().last().is_some_and(|obligation| obligation.class == crate::Oblig::UnmoldedTok))]
    fn push_choice(
        state: &mut MeldState<'_>,
        choice: Option<MoldId>,
        text: TokenText<'_>,
    )
    {
        match choice {
            | Some(mold) => state.push_text(mold, TileText::from(text)),
            // No candidate mold: the totally-defined unmolded path. An
            // out-of-range mold id routes `push` to `UnmoldedTok` (grammar-total
            // fallback) while preserving the token text.
            | None => state.push_text(MoldId::from(u32::MAX), TileText::from(text)),
        }
    }

    /// Gather the sorted, de-duplicated candidate molds for `token`, restricted
    /// to the fresh-slot menu when no form is open.
    ///
    /// With no open form the wide form-mid tail of a label's menu is
    /// inadmissible (a `≐`-continuation with nothing to continue), so the
    /// molder gathers only
    /// [`Pbg::fresh_candidates`](gandr_surface_grammar::Pbg::fresh_candidates),
    /// collapsing the ~130-mold `identifier` menu to its two atoms at the
    /// common fresh operand position. A token whose fresh menu is empty (a
    /// stray closer / mid with no open frontier) falls back to the full
    /// menu, so the melder still flags the exact stray-tile obligation it
    /// would on the full menu.
    ///
    /// # Specification
    /// - requires: the token bounds identify its exact source fragment.
    /// - ensures: gathers the applicable menu in ascending order without
    ///   duplicate molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate labels, empty and absent menus, fresh
    ///   versus declared candidates and a reserved word in name versus type
    ///   position expose the canonical candidate union and committed form.
    ///   Duplicate or unsorted entries, stale menus and an unconditional
    ///   fallback change them.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    /// - witness: `tests::acceptance::a_sign_block_may_be_named_with_a_primitive_type_spelling`
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather<'src>(
        &mut self,
        state: &MeldState<'_>,
        token: Token,
        source: &'src SourceFragment<'src>,
    )
    {
        let open = state.open_form_mold();
        self.gather_menu(token, source, open, CandidateMenu::Fresh);
        if self.candidates.is_empty() {
            // A stray form-continuation with no matching frontier: the full menu
            // supplies the tile the melder pushes to flag the exact obligation.
            self.gather_menu(token, source, open, CandidateMenu::Declared);
        }
        self.gather_reserved_fallback(state, token, source, open);
    }

    /// Widen a **reserved uppercase word**'s menu to its lexical class's
    /// generic labels when its own tile cannot mold at this position.
    ///
    /// The `UPPER_KEYWORDS` reservation is a disambiguation preference, never
    /// a ban on declaration names: at a type slot the reserved tile (`Unknown`
    /// the primitive type) molds and the generic labels stay out, so the
    /// primitive/type-identifier tie the reservation exists to prevent never
    /// forms. But the reservation also fires at slots that admit ONLY
    /// `constructor` / `type_identifier` — a `sign` block's name, a `sort`
    /// member's colour, a `data` head — where the reserved tile is
    /// structurally inadmissible, and there it repaired the whole declaration
    /// (`sign Unknown` molded nothing). When no gathered
    /// candidate is admissible at the live frontier, the molder re-gathers
    /// with the class's generic labels appended; the reserved candidates stay
    /// in the menu so the last-resort path still flags the exact obligation
    /// when nothing admissible exists either way.
    ///
    /// # Specification
    /// - requires: `token` came from the labeler over `source`; the reserved
    ///   menu was already gathered into `self.candidates`.
    /// - ensures: leaves `self.candidates` sorted and de-duplicated; widens it
    ///   with the generic-label menus exactly when the token is a reserved
    ///   uppercase word with no admissible candidate at the live frontier;
    ///   otherwise leaves it unchanged.
    /// - provides: the reservation-as-preference half of the candidate menu.
    /// - fails: never.
    /// - panics: none.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate labels, empty and absent menus, fresh
    ///   versus declared candidates and a reserved word in name versus type
    ///   position expose the canonical candidate union and committed form.
    ///   Duplicate or unsorted entries, stale menus and an unconditional
    ///   fallback change them.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    /// - witness: `tests::acceptance::a_sign_block_may_be_named_with_a_primitive_type_spelling`
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_reserved_fallback<'src>(
        &mut self,
        state: &MeldState<'_>,
        token: Token,
        source: &'src SourceFragment<'src>,
        open: Option<MoldId>,
    )
    {
        if !matches!(token.lexeme, Lexeme::UpperWord) {
            return;
        }
        let slice = token.text(source);
        if !UPPER_KEYWORDS.contains(&AsRef::<str>::as_ref(&slice)) {
            return;
        }
        let frontier = state.admissibility_frontier();
        if self
            .candidates
            .iter()
            .any(|&mold| bool::from(state.admits_at(mold, &frontier)))
        {
            return;
        }
        let reserved = core::mem::take(&mut self.candidates);
        let generic = [
            CandidateLabel::from("constructor"),
            CandidateLabel::from("type_identifier"),
        ];
        self.gather_labels(&generic, open, CandidateMenu::Fresh);
        if self.candidates.is_empty() {
            self.gather_labels(&generic, open, CandidateMenu::Declared);
        }
        self.candidates.extend_from_slice(&reserved);
        self.candidates.sort_unstable();
        self.candidates.dedup();
    }

    /// Gather the candidate molds for `token`, from the fresh-slot menu plus
    /// the open form's `≐`-successors ([`CandidateMenu::Fresh`]) or the full
    /// declared menu ([`CandidateMenu::Declared`]).
    ///
    /// # Specification
    /// - requires: the token bounds identify its exact source fragment.
    /// - ensures: gathers the applicable menu in ascending order without
    ///   duplicate molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate labels, empty and absent menus, fresh
    ///   versus declared candidates and a reserved word in name versus type
    ///   position expose the canonical candidate union and committed form.
    ///   Duplicate or unsorted entries, stale menus and an unconditional
    ///   fallback change them.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    /// - witness: `tests::acceptance::a_sign_block_may_be_named_with_a_primitive_type_spelling`
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_menu<'src>(
        &mut self,
        token: Token,
        source: &'src SourceFragment<'src>,
        open: Option<MoldId>,
        menu: CandidateMenu,
    )
    {
        self.candidates.clear();
        let slice = token.text(source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        let labels = candidate_labels(token.lexeme, text);
        self.gather_labels(&labels, open, menu);
    }

    /// Gather the candidate molds for `labels`, from the fresh-slot menu plus
    /// the open form's `≐`-successors ([`CandidateMenu::Fresh`]) or the full
    /// declared menu ([`CandidateMenu::Declared`]). The buffer is NOT cleared:
    /// callers stage menus (the reserved-word fallback unions its widened
    /// menu over the reserved one).
    ///
    /// # Specification
    /// - requires: `labels` are candidate spellings for the current token.
    /// - ensures: appends the labels' menu to `self.candidates`, then sorts and
    ///   de-duplicates it (ascending [`MoldId`]; no hash-iteration or
    ///   allocation order reaches the decision).
    /// - provides: the shared gather step of [`Self::gather_menu`] and
    ///   [`Self::gather_reserved_fallback`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate labels, empty and absent menus, fresh
    ///   versus declared candidates and a reserved word in name versus type
    ///   position expose the canonical candidate union and committed form.
    ///   Duplicate or unsorted entries, stale menus and an unconditional
    ///   fallback change them.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    /// - witness: `tests::acceptance::a_sign_block_may_be_named_with_a_primitive_type_spelling`
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_labels(
        &mut self,
        labels: &[CandidateLabel<'_>],
        open: Option<MoldId>,
        menu: CandidateMenu,
    )
    {
        for &label in labels {
            let Some(label) = self.candidate_label(label)
            else {
                continue;
            };
            let candidates = match menu {
                | CandidateMenu::Fresh => self.pbg.fresh_candidates(label),
                | CandidateMenu::Declared => self.pbg.candidates(label),
            };
            for &mold in candidates {
                self.candidates.push(mold);
            }
        }
        // With a form open, its `≐`-successors (the form's next tiles) are
        // admissible form-mids / ends that the fresh menu drops; add the ones
        // whose label matches this token so a form continuation still molds.
        if matches!(menu, CandidateMenu::Fresh)
            && let Some(open) = open
        {
            self.push_form_successors(labels, open);
        }
        // Deterministic candidate order: ascending MoldId, de-duplicated. No
        // hash-iteration or allocation order reaches the decision.
        self.candidates.sort_unstable();
        self.candidates.dedup();
    }

    /// Append the `≐`-successors of open form `open` whose label matches one in
    /// `labels` to the candidate buffer (the open form's next tiles).
    ///
    /// The `pbg` reference is copied out so the successor scan borrows the
    /// grammar, not `self`, leaving `self.candidates` free to push into.
    ///
    /// # Specification
    /// - ensures: appends exactly matching grammar successors, retaining the
    ///   existing prefix.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open form, matching and absent labels and a
    ///   preexisting candidate expose the exact appended adjacency set.
    ///   Dropping the prefix, crossing to another form or ignoring the label
    ///   changes it.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[spec(captures: before = self.candidates.len(), ensures: |_| self.candidates.get(before ..).is_some_and(|tail| tail.iter().all(|right| self.pbg.adjacencies().binary_search(&(open, *right)).is_ok() && self.pbg.mold(*right).is_ok_and(|def| labels.iter().any(|label| label.0 == def.label)))))]
    fn push_form_successors(
        &mut self,
        labels: &[CandidateLabel<'_>],
        open: MoldId,
    )
    {
        let pbg = self.pbg;
        for &(_open, right) in pbg.mold_successors(open) {
            if pbg
                .mold(right)
                .is_ok_and(|def| labels.contains(&CandidateLabel::from(def.label)))
            {
                self.candidates.push(right);
            }
        }
    }

    /// The least key `mold` can have: its continuation, sort and operand
    /// ranks over an empty delta, read without a dry-run.
    ///
    /// # Specification
    /// - ensures: returns the candidate's [`CandidateKey`] with its delta
    ///   replaced by the empty delta, so the returned key is at most the full
    ///   key; reads `state` without changing it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ranks are the full key's; a floor above a found
    ///   key is what lets [`least_candidates`](Self::least_candidates) skip a
    ///   candidate's dry-run. A floor carrying a nonempty delta, or ranks that
    ///   differ from the key's, changes which candidates are kept.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    #[spec(ensures: |ret| bool::from(ret.delta.is_empty()))]
    fn floor_key(
        &self,
        state: &MeldState<'_>,
        mold: MoldId,
        expected: Sort,
    ) -> CandidateKey
    {
        let continuation = CandidateRank::from(!bool::from(state.would_continue_form(mold)));
        let mold_sort = self.pbg.mold(mold).map_or(Sort::Item, |def| def.sort);
        let sort_rank = CandidateRank::from(mold_sort != expected);
        // Operand-continuation tiebreak: with the head an operand, a call `(` /
        // projection `.` / infix operator that extends it beats a fresh atom or
        // paren over the same lexeme, so the molder settles that family (the `(`
        // call-vs-parenthesised tie, `>` comparison-vs-redirection) with no
        // lookahead window. It ranks below sort so it never overrides a
        // sort-correct reading.
        let continue_rank = CandidateRank::from(!bool::from(state.continues_operand(mold)));
        CandidateKey {
            delta: Delta::empty(),
            continuation,
            sort: sort_rank,
            operand_continuation: continue_rank,
        }
    }

    /// The obligations pushing `mold` flags, read by a dry-run.
    ///
    /// # Specification
    /// - ensures: returns the streaming delta of pushing `mold` with `text` and
    ///   restores the melder exactly.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the dry-run of a valid and an invalid mold over a
    ///   state with prior obligations; checkpoint bytes before and after expose
    ///   leakage, and the unmolded class exposes the delta.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    #[spec(captures: before = (state.admissibility_frontier(), state.obligations().len()), ensures: |_| state.admissibility_frontier() == before.0 && state.obligations().len() == before.1)]
    fn push_delta(
        state: &mut MeldState<'_>,
        mold: MoldId,
        text: TokenText<'_>,
    ) -> Delta
    {
        let mark = state.mark();
        state.push_text(mold, TileText::from(text));
        let delta = state.delta_since(&mark);
        state.rollback_to(&mark);
        delta
    }

    /// Gather into `self.tied` every eligible candidate whose key is least, in
    /// ascending [`MoldId`] order.
    ///
    /// Candidates are visited by their [`floor_key`](Self::floor_key), least
    /// floor first, and within one floor in ascending `MoldId` order. A
    /// candidate's key is at least its floor, so once the least key found has
    /// an empty delta and the next floor lies above it, no remaining candidate
    /// can reach it and their dry-runs are skipped. The keys found are the
    /// [`CandidateKey`] of each visited candidate, so the least key and its
    /// ties are exactly those of scoring every candidate.
    ///
    /// # Specification
    /// - requires: `self.eligible` holds distinct molds in ascending order.
    /// - ensures: `self.tied` holds, in ascending order, exactly the eligible
    ///   candidates whose [`CandidateKey`] is the least among all eligible
    ///   candidates; it is empty exactly when none is eligible; the melder is
    ///   restored exactly.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — menus whose least key has an empty delta, a nonempty
    ///   delta, and ties across one floor; the chosen molds and the corpus
    ///   moldings expose a skipped candidate that could have tied or won.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    #[spec(captures: before = state.obligations().len(), ensures: |_| state.obligations().len() == before && self.tied.iter().all(|mold| self.eligible.contains(mold)) && self.tied.is_empty() == self.eligible.is_empty() && self.tied.iter().zip(self.tied.iter().skip(1)).all(|(left, right)| left < right))]
    fn least_candidates(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
        expected: Sort,
    )
    {
        self.ranked.clear();
        for slot in 0 .. self.eligible.len() {
            let Some(&mold) = self.eligible.get(slot)
            else {
                break;
            };
            let floor = self.floor_key(state, mold, expected);
            self.ranked.push((floor, mold));
        }
        self.tied.clear();
        let mut least: Option<CandidateKey> = None;
        for floor in RANK_FLOORS {
            if least.is_some_and(|least| floor > least) {
                break;
            }
            for slot in 0 .. self.ranked.len() {
                let Some(&(ranks, mold)) = self.ranked.get(slot)
                else {
                    break;
                };
                // Every floor carries the empty delta: the ranks decide.
                if (ranks.continuation, ranks.sort, ranks.operand_continuation)
                    != (floor.continuation, floor.sort, floor.operand_continuation)
                {
                    continue;
                }
                let key = CandidateKey {
                    delta: Self::push_delta(state, mold, text),
                    ..floor
                };
                match least {
                    | Some(found) if key > found => {},
                    | Some(found) if key == found => self.tied.push(mold),
                    | _ => {
                        least = Some(key);
                        self.tied.clear();
                        self.tied.push(mold);
                    },
                }
            }
        }
    }

    /// The single-token completion penalty of a candidate: the obligations a
    /// committed `finalize` would insert if the input ended right after this
    /// push.
    ///
    /// This is the tiebreak that settles a shared-prefix decision when no
    /// deeper lookahead runs (the single-token [`mold`](Self::mold), or a
    /// candidate the lookahead cannot separate): it prefers the reading that
    /// leaves the slope closest to complete. It is deliberately kept OUT of the
    /// [`CandidateKey`] tie-detection so a form-start (which momentarily
    /// leaves the slope incomplete) still ties the bare atom on the local key
    /// and triggers the lookahead — completion breaks the tie only among
    /// candidates the window cannot.
    ///
    /// # Specification
    /// - ensures: computes the completion obligation penalty and restores the
    ///   melder exactly.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live state with prior obligations is dry-run
    ///   through a valid and invalid mold. Checkpoint bytes before and after
    ///   expose source, slope, cache or obligation leakage; streaming and
    ///   completion deltas distinguish their scoring boundaries.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    #[spec(captures: before = (state.admissibility_frontier(), state.obligations().len()), ensures: |_| state.admissibility_frontier() == before.0 && state.obligations().len() == before.1)]
    fn completion(
        state: &mut MeldState<'_>,
        mold: MoldId,
        text: TokenText<'_>,
    ) -> Delta
    {
        let mark = state.mark();
        state.push_text(mold, TileText::from(text));
        let delta = state.completion_delta(Delta::empty());
        state.rollback_to(&mark);
        delta
    }

    /// Choose the admissibility-filtered `(key, completion, MoldId)`-minimum
    /// candidate.
    ///
    /// The candidate pre-filter: [`MeldState::admits`] discards
    /// every structurally-inadmissible candidate before any dry-run, collapsing
    /// the wide identifier / quote menus to a handful and preventing the greedy
    /// molder from committing a form-continuation tile with no matching open
    /// frontier. If the filter would empty the menu, the full menu is kept so
    /// molding stays total. Among survivors the order is the local
    /// [`CandidateKey`] then the [`completion`](Self::completion) penalty
    /// then ascending [`MoldId`] — the completion penalty is the greedy
    /// stand-in for the lookahead the single-token path cannot run.
    ///
    /// # Specification
    /// - requires: the candidate menu is canonical and belongs to this grammar.
    /// - ensures: selects a menu member, minimizing admissible key then
    ///   completion then identity; an empty menu yields none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, sole and ambiguous menus, including a
    ///   no-admissible fallback, expose the selected mold and final repairs.
    ///   Dropped candidates, choosing outside the menu or changing priority
    ///   changes those observations; dry-run state is compared byte-for-byte.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), ensures: |ret| ret.map_or_else(|| self.candidates.is_empty(), |mold| self.candidates.contains(&mold)))]
    fn choose(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
    ) -> Option<MoldId>
    {
        // Fast path: the pre-filter usually collapses the menu to
        // a lone admissible candidate, which needs no dry-run at all — the whole
        // point of the filter, and what keeps the batch cost inside budget. The
        // admissibility frontier is computed once and reused for every candidate.
        let frontier = state.admissibility_frontier();
        self.eligible.clear();
        for slot in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(slot)
            else {
                break;
            };
            if bool::from(state.admits_at(mold, &frontier)) {
                self.eligible.push(mold);
            }
        }
        if let [sole] = *self.eligible.as_slice() {
            return Some(sole);
        }
        // Keep the pre-filter only when at least one candidate survives it; an
        // empty admissible set falls back to the full menu (push is total on any
        // mold, so a last resort always exists).
        if self.eligible.is_empty() {
            self.eligible.extend_from_slice(&self.candidates);
        }
        // Pass one: the least local `(Delta, continuation, sort)` key and its
        // ties, in ascending `MoldId` order. The expensive `completion` finalize
        // only breaks a residual key-tie, and the overwhelming majority of
        // tokens have a unique key minimum, so the finalize never runs for them.
        self.least_candidates(state, text, frontier.expected);
        if self.tied.len() <= 1 {
            return self.tied.first().copied();
        }
        // Pass two: break the key-tie by the single-token completion penalty,
        // keeping the smaller `MoldId` on a further tie (ascending visitation).
        // An empty completion is the least there is, so no later tie can beat
        // it.
        let mut best: Option<(Delta, MoldId)> = None;
        for slot in 0 .. self.tied.len() {
            let Some(&mold) = self.tied.get(slot)
            else {
                break;
            };
            let completion = Self::completion(state, mold, text);
            if best
                .as_ref()
                .is_none_or(|&(best_completion, _mold)| completion < best_completion)
            {
                best = Some((completion, mold));
            }
            if bool::from(completion.is_empty()) {
                break;
            }
        }
        best.map(|(_, mold)| mold)
    }

    /// Return whether a direct circuit-rule binder opener has a binder-shaped
    /// next token in the batch stream.
    ///
    /// The circuit grammar deliberately keeps the binder's direct `(` / `)`
    /// shape so the description route can read its telescope. At the same
    /// lexical position, the shared expression family owns parenthesized
    /// endpoints. The opener alone cannot distinguish those forms; the first
    /// token inside the group does. A `rule` / `data` binder or an identifier
    /// followed by `:` is the direct form, while an expression head such as
    /// `assoc(` must remain in the shared family.
    ///
    /// # Specification
    /// - requires: `tokens` is the labeler output for `source`; `index` names
    ///   the current `(` token.
    /// - ensures: returns `true` only for the direct circuit binder opener when
    ///   the next significant tokens have its binder prefix.
    /// - provides: batch-only disambiguation for the direct circuit binder.
    /// - fails: never; missing lookahead rejects the direct reading.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct binder prefixes and expression heads following
    ///   the same parenthesis, including missing lookahead, expose the selected
    ///   grammar form. Admitting an otherwise forbidden mold or confusing a
    ///   colon-bearing binder with a call changes the committed structure.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[spec(ensures: |ret| !bool::from(ret) || bool::from(state.admits_at(mold, frontier)))]
    fn direct_rule_binder_admits(
        &self,
        state: &MeldState<'_>,
        mold: MoldId,
        frontier: &Frontier,
        tokens: &[Token],
        index: TokenIndex,
        source: &SourceFragment<'_>,
    ) -> DirectRuleBinderAdmission
    {
        if !bool::from(state.admits_at(mold, frontier)) {
            return DirectRuleBinderAdmission::from(false);
        }
        if frontier.expected != Sort::Expression || bool::from(frontier.head_operand) {
            return DirectRuleBinderAdmission::from(true);
        }
        let Some(def) = self.pbg.mold(mold).ok()
        else {
            return DirectRuleBinderAdmission::from(false);
        };
        if def.label != "(" || def.sort != Sort::Item {
            return DirectRuleBinderAdmission::from(true);
        }
        let Some(steps) = self.pbg.step(def.rctx, Dir::Right).ok()
        else {
            return DirectRuleBinderAdmission::from(false);
        };
        let direct_prefix = [
            StepSym::Tile("data"),
            StepSym::Tile("identifier"),
            StepSym::Tile("rule"),
        ];
        // Both readings begin with the same `(` prefix; only the first
        // interior token separates the direct binder from an expression endpoint.
        if steps.len() != direct_prefix.len()
            || !direct_prefix
                .iter()
                .all(|&step| steps.iter().any(|candidate| candidate.crossed == step))
        {
            return DirectRuleBinderAdmission::from(true);
        }
        let Some((first_index, first)) = next_significant(tokens, index)
        else {
            return DirectRuleBinderAdmission::from(false);
        };
        let first_text = first.text(source);
        if matches!(AsRef::<str>::as_ref(&first_text), "rule" | "data") {
            return DirectRuleBinderAdmission::from(true);
        }
        if !matches!(first.lexeme, Lexeme::LowerWord) {
            return DirectRuleBinderAdmission::from(false);
        }
        DirectRuleBinderAdmission::from(
            next_significant(tokens, first_index)
                .is_some_and(|(_, colon)| AsRef::<str>::as_ref(&colon.text(source)) == ":"),
        )
    }
    /// Choose token `index`'s mold, breaking a shared-prefix tie by lookahead.
    ///
    /// The admissibility-filtered local [`CandidateKey`] settles every
    /// decision with a unique minimum. What survives is a **shared-prefix**
    /// tie: a bare atom versus a form-start over the same lexeme (`Inl` alone
    /// versus `Inl(x)` opening a constructor pattern, `List` versus `List(T)`
    /// opening a type application) — the wider form families (`def`, `val`,
    /// `fn`, the `(` group, the `#{` record) are factored at the grammar, so
    /// they tie on the local key (zero
    /// streaming delta, equal continuation and sort ranks). The completion
    /// penalty [`choose`](Self::choose) would use resolves such a tie the
    /// *wrong* way (it prefers the shorter, already-complete reading), so it is
    /// deliberately excluded from the tie set here and the decision is made by
    /// a bounded greedy lookahead instead: each tied candidate is dry-run
    /// and its window molded greedily by [`choose`](Self::choose) (which IS
    /// completion aware, so the window itself molds well), and the reading
    /// whose window closes with the fewest obligations wins —
    /// deterministically, keeping the smaller [`MoldId`] on an exact window
    /// tie. When the local minimum is unique the fast path returns it
    /// directly.
    ///
    /// # Specification
    /// - requires: candidates are canonical for the current token.
    /// - ensures: returns no choice for an absent token or empty menu;
    ///   otherwise selects a grammar mold by bounded lookahead.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete shared-prefix families, exhausted input and
    ///   an empty menu expose selection and absence. Losing a tied opener or
    ///   looking beyond the bounded window changes the committed form; dry-run
    ///   mutations change the checkpoint bytes.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    /// - witness: `mold::tests::lookahead_window_stops_after_eight_significant_tokens`
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = (self.candidates.len(), tokens.get(index.0).is_some()), ensures: |ret| ret.is_some() == (before.1 && before.0 > 0) && ret.is_none_or(|mold| self.pbg.mold(mold).is_ok()))]
    fn choose_stream<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        index: TokenIndex,
        source: &'src SourceFragment<'src>,
    ) -> Option<MoldId>
    {
        let token = *tokens.get(usize::from(index))?;
        let slice = token.text(source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        // `self.candidates` is already gathered by the caller for this token.
        // Fast path: a lone admissible candidate needs no dry-run.
        // The admissibility frontier is computed once and reused per candidate.
        let frontier = state.admissibility_frontier();
        self.eligible.clear();
        for slot in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(slot)
            else {
                break;
            };
            if bool::from(
                self.direct_rule_binder_admits(state, mold, &frontier, tokens, index, source),
            ) {
                self.eligible.push(mold);
            }
        }
        if let [sole] = *self.eligible.as_slice() {
            return Some(sole);
        }
        if self.eligible.is_empty() {
            self.eligible.extend_from_slice(&self.candidates);
        }
        // The surviving candidates' least local key and its ties, in ascending
        // MoldId order (the process-invariant tie-break). Each tied opener's
        // window scores its own tokens into `self.tied`, so the openers move
        // to their own buffer.
        self.least_candidates(state, text, frontier.expected);
        if self.tied.len() <= 1 {
            return self.tied.first().copied();
        }
        core::mem::swap(&mut self.tied, &mut self.openers);

        // A shared-prefix family: break the tie by a bounded greedy lookahead.
        // Windows run in ascending MoldId order and a later opener wins only
        // with a strictly smaller delta, so each window after the first is
        // bounded by the best delta so far: a window delta never shrinks as
        // tokens are molded, and one that reaches the bound cannot win.
        let start = TokenIndex::from(usize::from(index).saturating_add(1));
        let mut best: Option<(Delta, MoldId)> = None;
        for slot in 0 .. self.openers.len() {
            let Some(&mold) = self.openers.get(slot)
            else {
                break;
            };
            let mark = state.mark();
            state.push_text(mold, TileText::from(text));
            let bound = best.map_or(WindowBound::Unbounded, |(delta, _mold)| {
                WindowBound::Below(delta)
            });
            let end = self.mold_window(state, tokens, start, source, &mark, bound);
            if end == WindowEnd::Molded {
                let delta = state.completion_delta(state.delta_since(&mark));
                // Ascending MoldId visitation with a strict `<` keeps the
                // smaller MoldId on an exact window tie — the documented
                // tie-break.
                if best
                    .as_ref()
                    .is_none_or(|&(best_delta, _mold)| delta < best_delta)
                {
                    best = Some((delta, mold));
                }
            }
            state.rollback_to(&mark);
        }
        best.map(|(_, mold)| mold)
    }

    /// Mold the next [`LOOKAHEAD`] non-space tokens from `start` for a window.
    ///
    /// The window molds each token with the completion-aware greedy
    /// [`choose`](Self::choose) (no nested lookahead), so its cost is bounded
    /// at one greedy pass per tied candidate — beam width one. Each token is
    /// settled, gathered and bounded at its declaration exactly as
    /// [`mold`](Self::mold) does, so a frontier the stream would close before
    /// the token — a filled required tail, a bare hole — is closed in the
    /// window too. Nested shared-prefix families inside a window still mold
    /// correctly because the pre-filter, with the spurious form-first helper
    /// molds folded away, leaves a lone admissible candidate at the common
    /// positions; the window only exists to expose whether a tied opener's own
    /// form completes.
    ///
    /// # Specification
    /// - requires: start is within the token stream or its end sentinel; `mark`
    ///   was taken from `state` before the tied opener was pushed.
    /// - ensures: molds at most eight non-space tokens and records
    ///   preceding/intervening trivia, leaving the following token untouched;
    ///   returns [`WindowEnd::Dominated`] exactly when `bound` is
    ///   [`WindowBound::Below`] and the obligations flagged since `mark` reach
    ///   it before a token is molded, and stops molding there.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty suffix and nine significant tokens separated
    ///   by spaces expose the exact committed prefix. Counting spaces against
    ///   the window, using seven or nine tokens, or consuming trailing trivia
    ///   after the eighth token changes the preserved source. A bound the
    ///   window's obligations reach stops it before its next token; one they
    ///   stay below leaves the window whole.
    /// - witness: `mold::tests::lookahead_window_stops_after_eight_significant_tokens`
    /// - witness: `mold::tests::a_dominated_window_stops_before_its_next_token`
    #[spec(requires: start.0 <= tokens.len(), ensures: |ret| ret == WindowEnd::Molded || matches!(bound, WindowBound::Below(least) if state.delta_since(mark) >= least))]
    fn mold_window<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        start: TokenIndex,
        source: &'src SourceFragment<'src>,
        mark: &Mark,
        bound: WindowBound,
    ) -> WindowEnd
    {
        let mut molded = 0_usize;
        let mut index = usize::from(start);
        while index < tokens.len() && molded < LOOKAHEAD {
            let Some(&token) = tokens.get(index)
            else {
                break;
            };
            let slice = token.text(source);
            if matches!(token.lexeme, Lexeme::Space) {
                state.space(SpaceText::from(AsRef::<str>::as_ref(&slice)));
            }
            else {
                if let WindowBound::Below(least) = bound
                    && state.delta_since(mark) >= least
                {
                    return WindowEnd::Dominated;
                }
                let text = TokenText::from(AsRef::<str>::as_ref(&slice));
                self.settle_shadowing(state, token, source);
                self.gather(state, token, source);
                state.settle_declaration_boundary(&self.candidates);
                let choice = self.choose(state, text);
                Self::push_choice(state, choice, text);
                molded = molded.saturating_add(1);
            }
            index = index.saturating_add(1);
        }
        WindowEnd::Molded
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::vec;
    use core::error::Error;

    use anodized::spec;
    use gandr_surface_grammar::CandidateCount;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::NodeDigest;
    use gandr_surface_syntax::SourceFragment;

    use super::CandidateLabel;
    use super::Molder;
    use super::SourceText;
    use super::TokenText;
    use super::candidate_labels;
    use crate::MeldState;
    use crate::SpaceText;
    use crate::label::Lexeme;
    use crate::label::label;
    use crate::testing::root_digest;

    /// Count of obligations generated by a deterministic mold run.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct MoldObligationCount(usize);

    /// Deterministic mold result used by the idempotence test.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct MoldHash
    {
        /// The committed root's content digest.
        root_digest: Option<NodeDigest>,
        /// How many obligations the run buffered.
        obligations: MoldObligationCount,
    }

    #[test]
    fn candidate_key_priorities_are_lexicographic()
    {
        let mut worse_delta = crate::Delta::empty();
        worse_delta.insert(crate::Oblig::UnmoldedTok);
        let low = super::CandidateRank::from(false);
        let high = super::CandidateRank::from(true);
        let keys = [
            super::CandidateKey {
                delta: crate::Delta::empty(),
                continuation: high,
                sort: high,
                operand_continuation: high,
            },
            super::CandidateKey {
                delta: worse_delta,
                continuation: low,
                sort: low,
                operand_continuation: low,
            },
        ];
        assert!(keys.first().unwrap() < keys.last().unwrap());
        let first = super::CandidateKey {
            delta: crate::Delta::empty(),
            continuation: low,
            sort: high,
            operand_continuation: high,
        };
        assert!(
            first
                < super::CandidateKey {
                    continuation: high,
                    sort: low,
                    operand_continuation: low,
                    ..first
                }
        );
        let second = super::CandidateKey { sort: low, ..first };
        assert!(
            second
                < super::CandidateKey {
                    operand_continuation: low,
                    ..first
                }
        );
        let third = super::CandidateKey {
            operand_continuation: low,
            ..second
        };
        assert!(third < second);
    }

    #[test]
    fn literal_and_shell_menus_are_exact()
    {
        let cases: &[(Lexeme, &str, &[&str])] = &[
            (Lexeme::Number, "1", &["number"]),
            (Lexeme::TypedNumber, "1u32", &["typed_number"]),
            (Lexeme::Character, "'a'", &["character"]),
            (Lexeme::Quote, "\"", &["\""]),
            (Lexeme::StringFragment, "x", &[
                "string_fragment",
                "double_string_fragment",
            ]),
            (Lexeme::EscapeSequence, "\\n", &["escape_sequence"]),
            (Lexeme::ShellWord, "word", &["shell_word"]),
            (Lexeme::EnvAssign, "A=b", &["environment_assignment"]),
            (Lexeme::SingleQuotedContent, "a", &["single_quoted_content"]),
            (Lexeme::VariableName, "A", &["variable_name"]),
            (Lexeme::SubshellOpen, "[", &["subshell_open"]),
            (Lexeme::SubshellClose, "]", &["subshell_close"]),
            (Lexeme::FileDescriptor, "2", &["file_descriptor"]),
            (Lexeme::Punct, "#!sh{", &["#!sh{", "#!{"]),
            (Lexeme::Punct, "$!py{", &[
                "$!py{",
                "command_substitution_start",
            ]),
            (Lexeme::Punct, "#!{", &["#!{", "#!{"]),
            (Lexeme::Space, " ", &[]),
            (Lexeme::Unknown, "~", &[]),
        ];
        for &(lexeme, text, expected) in cases {
            assert!(
                candidate_labels(lexeme, TokenText::from(text))
                    .iter()
                    .map(|label| <&str>::from(*label))
                    .eq(expected.iter().copied()),
                "{lexeme:?}: {text}"
            );
        }
    }

    #[test]
    fn lookahead_skips_only_space_and_never_the_current_token()
    {
        let tokens = label(SourceFragment::from("a  b ~  "));
        for (origin, expected) in [
            (0_usize, Some(2_usize)),
            (1, Some(2)),
            (2, Some(4)),
            (4, None),
            (5, None),
            (usize::MAX, None),
        ] {
            let next = super::next_significant(&tokens, super::TokenIndex::from(origin));
            assert_eq!(next.map(|(position, _)| usize::from(position)), expected);
            assert_eq!(
                next.map(|(_, token)| token),
                expected.and_then(|index| tokens.get(index).copied())
            );
        }
        assert_eq!(
            super::next_significant(&[], super::TokenIndex::from(0_usize)),
            None
        );
    }

    #[test]
    fn candidate_gathering_is_a_canonical_union() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        assert!(molder.candidates.is_empty());
        for (declared, _) in pbg.candidate_counts() {
            assert_eq!(
                molder.candidate_label(CandidateLabel::from(declared.0)),
                Some(declared)
            );
        }
        assert_eq!(
            molder.candidate_label(CandidateLabel::from("absent-label-for-witness")),
            None
        );
        let token = *label(SourceFragment::from("xyz")).first().unwrap();
        let expected: alloc::collections::BTreeSet<_> =
            ["xyz", "identifier", "type_variable", "hole_name"]
                .into_iter()
                .flat_map(|name| {
                    pbg.candidates(gandr_surface_grammar::TileLabel(name))
                        .iter()
                        .copied()
                })
                .collect();
        assert_eq!(
            molder.candidate_count(token, SourceText::from("xyz")),
            CandidateCount(expected.len())
        );
        assert!(
            molder
                .candidates
                .iter()
                .copied()
                .eq(expected.iter().copied())
        );
        molder.gather_labels(
            &[
                CandidateLabel::from("identifier"),
                CandidateLabel::from("identifier"),
                CandidateLabel::from("absent-label-for-witness"),
            ],
            None,
            super::CandidateMenu::Declared,
        );
        assert!(
            molder
                .candidates
                .iter()
                .copied()
                .eq(expected.iter().copied())
        );
        for source in [" ", "~"] {
            let token = *label(SourceFragment::from(source)).first().unwrap();
            assert_eq!(
                molder.candidate_count(token, SourceText::from(source)),
                CandidateCount(0)
            );
            assert_eq!(
                molder.choose(&mut MeldState::new(&pbg), TokenText::from(source)),
                None
            );
        }
        let &(open, successor) = pbg.adjacencies().first().unwrap();
        let label = pbg.mold(successor)?.label;
        molder.candidates = vec![open];
        molder.push_form_successors(&[CandidateLabel::from(label)], open);
        let expected: alloc::vec::Vec<_> = core::iter::once(open)
            .chain(pbg.adjacencies().iter().filter_map(|&(left, right)| {
                (left == open && pbg.mold(right).is_ok_and(|def| def.label == label))
                    .then_some(right)
            }))
            .collect();
        assert_eq!(molder.candidates, expected);
        let before = molder.candidates.clone();
        molder.push_form_successors(&[CandidateLabel::from("absent-label-for-witness")], open);
        assert_eq!(molder.candidates, before);
        Ok(())
    }

    #[test]
    fn dry_runs_restore_exact_state() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        let invalid = gandr_surface_syntax::MoldId::from(u32::MAX);
        state.push(&crate::MoldedTile::new(invalid, crate::TileText::from("~")));
        let before = state.checkpoint().to_bytes();
        let floor = molder.floor_key(&state, invalid, gandr_surface_grammar::Sort::Expression);
        assert!(bool::from(floor.delta.is_empty()));
        assert_eq!(state.checkpoint().to_bytes(), before);
        let delta = Molder::push_delta(&mut state, invalid, TokenText::from("!"));
        assert_eq!(usize::from(delta.inserted(crate::Oblig::UnmoldedTok)), 1);
        assert_eq!(state.checkpoint().to_bytes(), before);
        let _completion = Molder::completion(&mut state, invalid, TokenText::from("!"));
        assert_eq!(state.checkpoint().to_bytes(), before);
        let candidate = *pbg
            .candidates(gandr_surface_grammar::TileLabel("identifier"))
            .first()
            .unwrap();
        molder.candidates = vec![candidate];
        assert_eq!(
            molder.choose(&mut state, TokenText::from("x")),
            Some(candidate)
        );
        assert_eq!(state.checkpoint().to_bytes(), before);
        Ok(())
    }

    #[test]
    fn space_and_empty_stream_are_exact_noops() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        state.push(&crate::MoldedTile::new(
            gandr_surface_syntax::MoldId::from(u32::MAX),
            crate::TileText::from("~"),
        ));
        let before = state.checkpoint().to_bytes();
        let space = *label(SourceFragment::from(" ")).first().unwrap();
        molder.mold(&mut state, space, SourceText::from(" "));
        assert_eq!(state.checkpoint().to_bytes(), before);
        molder.mold_stream(&mut state, &[], SourceText::from(""));
        assert_eq!(state.checkpoint().to_bytes(), before);
        Ok(())
    }

    #[test]
    fn runs_mold_as_the_whole_stream() -> Result<(), Box<dyn Error>>
    {
        // Shared-prefix openers (`List` a type or an application, `Inl` an
        // atom or a constructor) need lookahead past the token, so a split
        // right after one only matches the whole stream when the first run's
        // window reads into the second run's tokens.
        let pbg = built()?;
        let src = "def a : Type = List(Integer);\ndef b = Inl(1);\ndef c = case b { Inl(x) => x, Inr(y) => y };\n";
        let source = SourceText::from(src);
        let tokens = label(SourceFragment::from(src));
        let mut molder = Molder::new(&pbg);
        let mut whole = MeldState::new(&pbg);
        molder.mold_stream(&mut whole, &tokens, source);
        let want = whole.checkpoint().to_bytes();
        for cut in 0 ..= tokens.len() {
            let mut state = MeldState::new(&pbg);
            for run in [
                super::TokenRun::new(
                    super::TokenIndex::from(0_usize),
                    super::TokenIndex::from(cut),
                ),
                super::TokenRun::new(
                    super::TokenIndex::from(cut),
                    super::TokenIndex::from(tokens.len()),
                ),
            ] {
                molder.mold_run(&mut state, &tokens, run, source);
            }
            assert_eq!(state.checkpoint().to_bytes(), want, "split at token {cut}");
        }
        Ok(())
    }

    #[test]
    fn lookahead_window_stops_after_eight_significant_tokens() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let source = SourceFragment::from("1 2 3 4 5 6 7 8 9");
        let tokens = label(source);
        let mut state = MeldState::new(&pbg);
        let mark = state.mark();
        let end = molder.mold_window(
            &mut state,
            &tokens,
            super::TokenIndex::from(0_usize),
            &source,
            &mark,
            super::WindowBound::Unbounded,
        );
        assert_eq!(end, super::WindowEnd::Molded);
        let tree = state.commit(SourceText::from("1 2 3 4 5 6 7 8"))?;
        assert_eq!(crate::testing::reconstruct(&tree), "1 2 3 4 5 6 7 8");
        let mut state = MeldState::new(&pbg);
        let mark = state.mark();
        molder.mold_window(
            &mut state,
            &tokens,
            super::TokenIndex::from(tokens.len()),
            &source,
            &mark,
            super::WindowBound::Unbounded,
        );
        assert_eq!(
            state.checkpoint().to_bytes(),
            MeldState::new(&pbg).checkpoint().to_bytes()
        );
        assert_eq!(
            molder.choose_stream(
                &mut state,
                &tokens,
                super::TokenIndex::from(tokens.len()),
                &source
            ),
            None
        );
        molder.candidates.clear();
        assert_eq!(
            molder.choose_stream(
                &mut state,
                &tokens,
                super::TokenIndex::from(0_usize),
                &source
            ),
            None
        );
        Ok(())
    }

    #[test]
    fn a_dominated_window_stops_before_its_next_token() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let source = SourceFragment::from("~ 1 2");
        let tokens = label(source);
        let unmolded_tokens = |count: usize| {
            let mut delta = crate::Delta::empty();
            for _ in 0 .. count {
                delta.insert(crate::Oblig::UnmoldedTok);
            }
            delta
        };
        // The unmolded `~` flags one obligation before the window's first
        // token, `1`: a bound it reaches stops the window there, one above it
        // lets the window mold to its end.
        let window = |molder: &mut Molder<'_>, bound| {
            let mut state = MeldState::new(&pbg);
            let mark = state.mark();
            state.push(&crate::MoldedTile::new(
                gandr_surface_syntax::MoldId::from(u32::MAX),
                crate::TileText::from("~"),
            ));
            let end = molder.mold_window(
                &mut state,
                &tokens,
                super::TokenIndex::from(2_usize),
                &source,
                &mark,
                bound,
            );
            (end, state.checkpoint().to_bytes())
        };
        let mut unmolded = MeldState::new(&pbg);
        unmolded.push(&crate::MoldedTile::new(
            gandr_surface_syntax::MoldId::from(u32::MAX),
            crate::TileText::from("~"),
        ));
        for reached in [crate::Delta::empty(), unmolded_tokens(1)] {
            assert_eq!(
                window(&mut molder, super::WindowBound::Below(reached)),
                (
                    super::WindowEnd::Dominated,
                    unmolded.checkpoint().to_bytes()
                )
            );
        }
        let (end, bytes) = window(&mut molder, super::WindowBound::Below(unmolded_tokens(2)));
        assert_eq!(end, super::WindowEnd::Molded);
        assert_eq!(bytes, window(&mut molder, super::WindowBound::Unbounded).1);
        assert_ne!(bytes, unmolded.checkpoint().to_bytes());
        Ok(())
    }

    #[test]
    fn identifier_menu_is_wide() -> Result<(), Box<dyn Error>>
    {
        // `identifier` has the widest declared candidate menu in the grammar;
        // a bare identifier's molder candidate set is correspondingly wide,
        // while a punctuation token has a narrow one.
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let ident = *label(SourceFragment::from("xyz"))
            .first()
            .expect("one token");
        let semi = *label(SourceFragment::from(";")).first().expect("one token");
        let ident_count = molder.candidate_count(ident, SourceText::from("xyz"));
        let semi_count = molder.candidate_count(semi, SourceText::from(";"));
        assert!(
            ident_count > CandidateCount(100),
            "identifier menu is wide, got {ident_count:?}"
        );
        assert!(
            semi_count > CandidateCount(0),
            "the `;` tile has candidates"
        );
        assert!(ident_count > semi_count);
        Ok(())
    }
    #[test]
    fn picks_the_obligation_minimum_mold() -> Result<(), Box<dyn Error>>
    {
        // A bare identifier at the start of input molds to an atom (zero
        // obligations), never to a form-continuing keyword mold that would
        // strand the slope. The committed parse has no obligations.
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        for token in label(SourceFragment::from("greeting")) {
            molder.mold(&mut state, token, SourceText::from("greeting"));
        }
        assert!(
            state.obligations().is_empty(),
            "a bare identifier atom molds without obligations"
        );
        Ok(())
    }
    #[test]
    fn unmoldable_token_takes_the_unmolded_path() -> Result<(), Box<dyn Error>>
    {
        // A stray byte the grammar has no tile for flows the UnmoldedTok path,
        // never a panic or a lexer error.
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        let src = "~";
        for token in label(SourceFragment::from(src)) {
            molder.mold(&mut state, token, SourceText::from(src));
        }
        assert!(
            state
                .obligations()
                .iter()
                .any(|obligation| obligation.class == crate::Oblig::UnmoldedTok),
            "a stray byte is an UnmoldedTok obligation"
        );
        Ok(())
    }
    #[test]
    fn molding_is_deterministic_across_runs() -> Result<(), Box<dyn Error>>
    {
        // Determinism is HARD: the molded + committed tree is
        // byte-identical across 100 runs. Nothing process-varying (hash order,
        // allocation address) reaches the decision.
        let pbg = built()?;
        let src = "def f() -> -F Integer { ret (x * x) } square(9) [1, 2, 3]";

        let reference = mold_and_hash(&pbg, SourceText::from(src))?;
        for _ in 0 .. 100_u32 {
            let observed = mold_and_hash(&pbg, SourceText::from(src))?;
            assert_eq!(observed, reference, "molding is deterministic");
        }
        Ok(())
    }
    /// Build the shared built-in grammar for the molder tests.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the checked grammar declares definitions, returns and
    ///   grouping.
    /// - fails: the grammar builder refuses the declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// The builder's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the checked built-in grammar accepts an identifier
    ///   without repair; a missing atom or invalid declaration changes the
    ///   result.
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |pbg| ["def", "ret", "(", ")"].into_iter().all(|label| !pbg.candidates(gandr_surface_grammar::TileLabel(label)).is_empty())))]
    fn built() -> Result<Pbg, Box<dyn Error>>
    {
        let pbg = built_in()?;
        Ok(pbg)
    }

    #[test]
    fn keyword_and_identifier_share_a_word_menu()
    {
        // A reserved keyword molds only to its own tile (no identifier menu).
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("def")),
            vec![CandidateLabel::from("def")]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("val")),
            vec![CandidateLabel::from("val")]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("let")),
            vec![
                CandidateLabel::from("let"),
                CandidateLabel::from("identifier"),
                CandidateLabel::from("type_variable"),
                CandidateLabel::from("hole_name")
            ]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("run")),
            vec![CandidateLabel::from("run")]
        );
        // An ordinary lowercase word gets the wide identifier menu, plus the
        // `hole_name` tile — admissible only after a `?` hole frontier, so it
        // never competes at an ordinary word slot.
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("greeting")),
            vec![
                CandidateLabel::from("greeting"),
                CandidateLabel::from("identifier"),
                CandidateLabel::from("type_variable"),
                CandidateLabel::from("hole_name")
            ]
        );
        // A reserved primitive/type keyword molds only to its own tile.
        assert_eq!(
            candidate_labels(Lexeme::UpperWord, TokenText::from("Integer")),
            vec![CandidateLabel::from("Integer")]
        );
        // An ordinary uppercase word gets the constructor / type-identifier menu.
        assert_eq!(
            candidate_labels(Lexeme::UpperWord, TokenText::from("Inl")),
            vec![
                CandidateLabel::from("Inl"),
                CandidateLabel::from("constructor"),
                CandidateLabel::from("type_identifier")
            ]
        );
        assert_eq!(
            candidate_labels(Lexeme::Punct, TokenText::from("->")),
            vec![CandidateLabel::from("->")]
        );
        assert!(candidate_labels(Lexeme::Space, TokenText::from(" ")).is_empty());
        assert!(candidate_labels(Lexeme::Unknown, TokenText::from("~")).is_empty());
    }

    /// Mold and commit `src`, returning the root digest and obligation count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: layout is recorded so the committed tree spans `src`, and
    ///   successful output contains its root digest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete forms, calls and list literals expose digest
    ///   and obligation pairs across repeated independent runs; unstable
    ///   candidate order or missing layout changes them.
    /// - witness: `mold::tests::molding_is_deterministic_across_runs`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |hash| hash.root_digest.is_some()))]
    fn mold_and_hash(
        pbg: &Pbg,
        src: SourceText<'_>,
    ) -> Result<MoldHash, Box<dyn Error>>
    {
        let mut molder = Molder::new(pbg);
        let mut state = MeldState::new(pbg);
        let source = SourceFragment::from(<&str>::from(src));
        for token in label(source) {
            if token.lexeme == Lexeme::Space {
                let text = token.text(&source);
                state.space(SpaceText::from(<&str>::from(text)));
            }
            else {
                molder.mold(&mut state, token, src);
            }
        }
        let obligations = MoldObligationCount(state.obligations().len());
        let tree = state.commit(src)?;
        Ok(MoldHash {
            root_digest: root_digest(&tree),
            obligations,
        })
    }
}
