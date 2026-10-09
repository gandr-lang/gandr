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
use crate::MoldedTile;
use crate::label::Lexeme;
use crate::label::Token;
use crate::meld::CandidateLabels;
use crate::meld::Mark;
use crate::meld::SpaceText;
use crate::meld::TileText;
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

/// Dense token-stream position used by bounded lookahead.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TokenIndex(usize);

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

/// Local candidate minimization key.
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

/// Candidate menu scope used by the gather step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CandidateMenu
{
    /// Fresh-slot candidates plus the open form's matching successors.
    Fresh,
    /// Full declared candidate menu.
    Declared,
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
#[anodized::spec(ensures: |ret| ret.is_empty() == matches!(lexeme, Lexeme::Space | Lexeme::Unknown) && ret.len() <= MAX_LABELS && (!matches!(lexeme, Lexeme::LowerWord | Lexeme::UpperWord | Lexeme::Punct) || ret.first().is_some_and(|label| label.0 == text.0)))]
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
#[anodized::spec(ensures: |ret| ret == tokens.iter().copied().enumerate().skip(index.0.saturating_add(1)).find(|&(_, token)| token.lexeme != Lexeme::Space).map(|(position, token)| (TokenIndex::from(position), token)))]
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
    /// Pooled dry-run marks, reused across candidates and tokens so the
    /// per-candidate `mark`/`rollback` transaction reaches a zero-allocation
    /// steady state ([`MeldState::mark_into`] fills a pooled mark with
    /// `clone_from`, reusing its buffers). A pool (not one scratch slot)
    /// because dry-runs nest: the lookahead window's outer mark must survive
    /// the inner per-token marks its greedy molding takes.
    marks: Vec<Mark>,
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
    #[anodized::spec(ensures: |ret| ret.candidates.is_empty() && ret.marks.is_empty() && ret.labels.iter().zip(ret.labels.iter().skip(1)).all(|(left, right)| left.as_ref() < right.as_ref()))]
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
            marks: Vec::new(),
        }
    }

    /// Take a pooled mark filled with `state`'s current snapshot.
    ///
    /// # Specification
    /// - ensures: returns a snapshot of the current melder, overwriting a
    ///   reused pool slot.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and reused mark pools surround an obligation-
    ///   bearing push; rolling back reproduces exact checkpoint bytes.
    ///   Returning a stale mark or leaking dry-run source, slope or obligations
    ///   changes them.
    /// - witness: `mold::tests::pooled_marks_and_dry_runs_restore_exact_state`
    #[anodized::spec(ensures: |ret| bool::from(state.delta_since(&ret).is_empty()))]
    fn take_mark(
        &mut self,
        state: &MeldState<'_>,
    ) -> Mark
    {
        let mut mark = self.marks.pop().unwrap_or_default();
        state.mark_into(&mut mark);
        mark
    }

    /// Return a used mark to the pool, keeping its buffers for reuse.
    ///
    /// # Specification
    /// trivial.
    fn put_mark(
        &mut self,
        mark: Mark,
    )
    {
        self.marks.push(mark);
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
    #[anodized::spec(ensures: |ret| ret == self.labels.iter().copied().find(|candidate| candidate.as_ref() == label.0))]
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
    #[anodized::spec(ensures: |ret| ret.0 == self.candidates.len() && self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
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
    #[anodized::spec(requires: <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
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
    #[anodized::spec(requires: tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()))]
    pub fn mold_stream(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        src: SourceText<'_>,
    )
    {
        let source = source_slice(src);
        let mut index = 0;
        while index < tokens.len() {
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
    #[anodized::spec(requires: source.as_ref().get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
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
    #[anodized::spec(ensures: |_| choice.is_some() || state.obligations().last().is_some_and(|obligation| obligation.class == crate::Oblig::UnmoldedTok))]
    fn push_choice(
        state: &mut MeldState<'_>,
        choice: Option<MoldId>,
        text: TokenText<'_>,
    )
    {
        match choice {
            | Some(mold) => state.push(&MoldedTile::new(mold, TileText::from(text))),
            // No candidate mold: the totally-defined unmolded path. An
            // out-of-range mold id routes `push` to `UnmoldedTok` (grammar-total
            // fallback) while preserving the token text.
            | None => state.push(&MoldedTile::new(
                MoldId::from(u32::MAX),
                TileText::from(text),
            )),
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
    #[anodized::spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
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
    #[anodized::spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
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
    #[anodized::spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
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
    #[anodized::spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
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
    #[anodized::spec(captures: before = self.candidates.len(), ensures: |_| self.candidates.get(before ..).is_some_and(|tail| tail.iter().all(|right| self.pbg.adjacencies().binary_search(&(open, *right)).is_ok() && self.pbg.mold(*right).is_ok_and(|def| labels.iter().any(|label| label.0 == def.label)))))]
    fn push_form_successors(
        &mut self,
        labels: &[CandidateLabel<'_>],
        open: MoldId,
    )
    {
        let pbg = self.pbg;
        let adjacencies = pbg.adjacencies();
        let start = adjacencies.partition_point(|&(left, _)| left < open);
        for &(left, right) in adjacencies.get(start ..).unwrap_or(&[]) {
            if left != open {
                break;
            }
            if pbg
                .mold(right)
                .is_ok_and(|def| labels.contains(&CandidateLabel::from(def.label)))
            {
                self.candidates.push(right);
            }
        }
    }

    /// The local minimization key of a candidate: `(Delta, continuation,
    /// sort)`.
    ///
    /// * `Delta` is the obligation change the push itself flags — the
    ///   **streaming** delta only. It deliberately excludes the `finalize`
    ///   completion penalty: a form-start (`Inl` opening a constructor pattern,
    ///   `def` opening an item) momentarily leaves the slope incomplete, and
    ///   penalizing that would make the bare atom always strictly cheaper, so
    ///   the two would never tie and the shared-prefix lookahead
    ///   ([`choose_stream`](Self::choose_stream)) would never fire to see the
    ///   discriminating tile. Completion is measured in the lookahead window,
    ///   where it belongs.
    /// * The **continuation** rank is `0` when the candidate `≐`-continues the
    ///   open form frontier and `1` otherwise, so a `def`'s name reads as the
    ///   form's name tile rather than a bare variable.
    /// * The **sort** rank is `0` when the candidate's grammar sort matches the
    ///   slot the head expects ([`MeldState::expected_operand_sort`]) and `1`
    ///   otherwise, so `"hi"` reads as the expression string at an expression
    ///   slot and the pattern string in a pattern slot.
    ///
    /// Candidates are visited in ascending [`MoldId`] order under a strict `<`,
    /// so an exact key tie keeps the smaller `MoldId` — the documented,
    /// process-invariant tie-break.
    ///
    /// # Specification
    /// - ensures: computes the streaming candidate key without completion
    ///   penalties and restores the melder exactly.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live state with prior obligations is dry-run
    ///   through a valid and invalid mold, using fresh and reused marks.
    ///   Checkpoint bytes before and after expose source, slope, cache or
    ///   obligation leakage; streaming and completion deltas distinguish their
    ///   scoring boundaries.
    /// - witness: `mold::tests::pooled_marks_and_dry_runs_restore_exact_state`
    #[anodized::spec(captures: before = (state.admissibility_frontier(), state.obligations().len()), ensures: |_| state.admissibility_frontier() == before.0 && state.obligations().len() == before.1)]
    fn key(
        &mut self,
        state: &mut MeldState<'_>,
        mold: MoldId,
        text: TokenText<'_>,
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
        let mark = self.take_mark(state);
        state.push(&MoldedTile::new(mold, TileText::from(text)));
        let delta = state.delta_since(&mark);
        state.rollback_to(&mark);
        self.put_mark(mark);
        CandidateKey {
            delta,
            continuation,
            sort: sort_rank,
            operand_continuation: continue_rank,
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
    /// [`key`](Self::key) tie-detection so a form-start (which momentarily
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
    ///   through a valid and invalid mold, using fresh and reused marks.
    ///   Checkpoint bytes before and after expose source, slope, cache or
    ///   obligation leakage; streaming and completion deltas distinguish their
    ///   scoring boundaries.
    /// - witness: `mold::tests::pooled_marks_and_dry_runs_restore_exact_state`
    #[anodized::spec(captures: before = (state.admissibility_frontier(), state.obligations().len()), ensures: |_| state.admissibility_frontier() == before.0 && state.obligations().len() == before.1)]
    fn completion(
        &mut self,
        state: &mut MeldState<'_>,
        mold: MoldId,
        text: TokenText<'_>,
    ) -> Delta
    {
        let mark = self.take_mark(state);
        state.push(&MoldedTile::new(mold, TileText::from(text)));
        let mut delta = Delta::empty();
        for obligation in state.finalize().obligations() {
            delta.insert(obligation.class);
        }
        state.rollback_to(&mark);
        self.put_mark(mark);
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
    /// [`key`](Self::key) then the [`completion`](Self::completion) penalty
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
    /// - witness: `mold::tests::pooled_marks_and_dry_runs_restore_exact_state`
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    #[anodized::spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), ensures: |ret| ret.map_or_else(|| self.candidates.is_empty(), |mold| self.candidates.contains(&mold)))]
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
        let mut sole: Option<MoldId> = None;
        let mut admissible = 0_usize;
        for &mold in &self.candidates {
            if bool::from(state.admits_at(mold, &frontier)) {
                admissible = admissible.saturating_add(1);
                sole = Some(mold);
            }
        }
        if admissible == 1 {
            return sole;
        }
        // Keep the pre-filter only when at least one candidate survives it; an
        // empty admissible set falls back to the full menu (push is total on any
        // mold, so a last resort always exists).
        let filter = admissible > 0;
        let expected = frontier.expected;
        // Pass one: the cheap local `(Delta, continuation, sort)` key, minimised
        // in ascending `MoldId` order (a strict `<` keeps the smaller `MoldId` on
        // a tie). The expensive `completion` finalize is deferred: it only breaks
        // a residual key-tie, and the overwhelming majority of tokens have a
        // unique key minimum, so the finalize never runs for them.
        let mut best_key: Option<CandidateKey> = None;
        let mut best_mold: Option<MoldId> = None;
        let mut key_tie = false;
        for index in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(index)
            else {
                break;
            };
            if filter && !bool::from(state.admits_at(mold, &frontier)) {
                continue;
            }
            let key = self.key(state, mold, text, expected);
            match best_key {
                | Some(prev) if key == prev => key_tie = true,
                | Some(prev) if key < prev => {
                    best_key = Some(key);
                    best_mold = Some(mold);
                    key_tie = false;
                },
                | Some(_) => {},
                | None => {
                    best_key = Some(key);
                    best_mold = Some(mold);
                },
            }
        }
        let (Some(min_key), true) = (best_key, key_tie)
        else {
            // Unique key minimum: no finalize needed.
            return best_mold;
        };
        // Pass two: break the key-tie by the single-token completion penalty,
        // keeping the smaller `MoldId` on a further tie (ascending visitation).
        let mut best: Option<(Delta, MoldId)> = None;
        for index in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(index)
            else {
                break;
            };
            if filter && !bool::from(state.admits_at(mold, &frontier)) {
                continue;
            }
            if self.key(state, mold, text, expected) != min_key {
                continue;
            }
            let completion = self.completion(state, mold, text);
            if best
                .as_ref()
                .is_none_or(|&(best_completion, _mold)| completion < best_completion)
            {
                best = Some((completion, mold));
            }
        }
        best.map(|(_, mold)| mold).or(best_mold)
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
    #[anodized::spec(ensures: |ret| !bool::from(ret) || bool::from(state.admits_at(mold, frontier)))]
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
    /// The admissibility-filtered local [`key`](Self::key) settles every
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
    #[anodized::spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = (self.candidates.len(), tokens.get(index.0).is_some()), ensures: |ret| ret.is_some() == (before.1 && before.0 > 0) && ret.is_none_or(|mold| self.pbg.mold(mold).is_ok()))]
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
        let mut sole: Option<MoldId> = None;
        let mut admissible = 0_usize;
        for &mold in &self.candidates {
            if bool::from(
                self.direct_rule_binder_admits(state, mold, &frontier, tokens, index, source),
            ) {
                admissible = admissible.saturating_add(1);
                sole = Some(mold);
            }
        }
        if admissible == 1 {
            return sole;
        }
        let filter = admissible > 0;
        let expected = frontier.expected;
        // Score each surviving candidate once by its local key, in ascending
        // MoldId order (the process-invariant tie-break).
        let mut scored: Vec<(CandidateKey, MoldId)> = Vec::new();
        for slot in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(slot)
            else {
                break;
            };
            if filter
                && !bool::from(
                    self.direct_rule_binder_admits(state, mold, &frontier, tokens, index, source),
                )
            {
                continue;
            }
            scored.push((self.key(state, mold, text, expected), mold));
        }
        let min_key = scored.iter().map(|&(key, _)| key).min()?;
        let tied: Vec<MoldId> = scored
            .iter()
            .filter(|&&(key, _)| key == min_key)
            .map(|&(_, mold)| mold)
            .collect();
        if tied.len() <= 1 {
            return tied.first().copied();
        }

        // A shared-prefix family: break the tie by a bounded greedy lookahead.
        let mut best: Option<(Delta, MoldId)> = None;
        for &mold in &tied {
            let mark = self.take_mark(state);
            state.push(&MoldedTile::new(mold, TileText::from(text)));
            self.mold_window(
                state,
                tokens,
                TokenIndex::from(usize::from(index).saturating_add(1)),
                source,
            );
            let mut delta = state.delta_since(&mark);
            for obligation in state.finalize().obligations() {
                delta.insert(obligation.class);
            }
            state.rollback_to(&mark);
            self.put_mark(mark);
            // Ascending MoldId visitation with a strict `<` keeps the smaller
            // MoldId on an exact window tie — the documented tie-break.
            if best
                .as_ref()
                .is_none_or(|&(best_delta, _mold)| delta < best_delta)
            {
                best = Some((delta, mold));
            }
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
    /// - requires: start is within the token stream or its end sentinel.
    /// - ensures: molds at most eight non-space tokens and records
    ///   preceding/intervening trivia, leaving the following token untouched.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty suffix and nine significant tokens separated
    ///   by spaces expose the exact committed prefix. Counting spaces against
    ///   the window, using seven or nine tokens, or consuming trailing trivia
    ///   after the eighth token changes the preserved source.
    /// - witness: `mold::tests::lookahead_window_stops_after_eight_significant_tokens`
    #[anodized::spec(requires: start.0 <= tokens.len())]
    fn mold_window<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        start: TokenIndex,
        source: &'src SourceFragment<'src>,
    )
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
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::vec;
    use core::error::Error;

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
        assert!(molder.marks.is_empty());
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
    fn pooled_marks_and_dry_runs_restore_exact_state() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let mut state = MeldState::new(&pbg);
        let invalid = gandr_surface_syntax::MoldId::from(u32::MAX);
        state.push(&crate::MoldedTile::new(invalid, crate::TileText::from("~")));
        for _ in 0_u8 .. 2_u8 {
            let before = state.checkpoint().to_bytes();
            let mark = molder.take_mark(&state);
            assert_eq!(mark, state.mark());
            state.push(&crate::MoldedTile::new(invalid, crate::TileText::from("!")));
            state.rollback_to(&mark);
            assert_eq!(state.checkpoint().to_bytes(), before);
            molder.put_mark(mark);
        }
        let before = state.checkpoint().to_bytes();
        let key = molder.key(
            &mut state,
            invalid,
            TokenText::from("!"),
            gandr_surface_grammar::Sort::Expression,
        );
        assert_eq!(
            usize::from(key.delta.inserted(crate::Oblig::UnmoldedTok)),
            1
        );
        assert_eq!(state.checkpoint().to_bytes(), before);
        let _completion = molder.completion(&mut state, invalid, TokenText::from("!"));
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
    fn lookahead_window_stops_after_eight_significant_tokens() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let source = SourceFragment::from("1 2 3 4 5 6 7 8 9");
        let tokens = label(source);
        let mut state = MeldState::new(&pbg);
        molder.mold_window(
            &mut state,
            &tokens,
            super::TokenIndex::from(0_usize),
            &source,
        );
        let tree = state.commit(SourceText::from("1 2 3 4 5 6 7 8"))?;
        assert_eq!(crate::testing::reconstruct(&tree), "1 2 3 4 5 6 7 8");
        let mut state = MeldState::new(&pbg);
        molder.mold_window(
            &mut state,
            &tokens,
            super::TokenIndex::from(tokens.len()),
            &source,
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
    #[anodized::spec(ensures: |ret| ret.as_ref().map_or(true, |pbg| ["def", "ret", "(", ")"].into_iter().all(|label| !pbg.candidates(gandr_surface_grammar::TileLabel(label)).is_empty())))]
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
    #[anodized::spec(ensures: |ret| ret.as_ref().map_or(true, |hash| hash.root_digest.is_some()))]
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
