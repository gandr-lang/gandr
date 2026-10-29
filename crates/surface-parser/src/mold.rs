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
//!
//! # The molder's search stops at its least key
//!
//! The work to reach the choice is bounded by the least key found. A
//! candidate's key is at least a floor read without a dry-run — its rank bits
//! and an empty delta — so candidates are visited floor by floor and the search
//! stops once the least key found lies below every floor left. Pass two stops
//! at the first empty completion, which nothing beats. Each window after the
//! first is bounded by the best window delta so far, and is abandoned the
//! moment its own delta reaches that bound, since a window's delta never
//! shrinks as it molds. A dry-run does not copy the slope: a `Mark` records
//! lengths, and the slope edits made under a live mark go to a trail that
//! `rollback_to` undoes newest first, restoring only the cells the dry-run
//! touched. The completion delta is counted without collecting the obligations,
//! a push never builds a `MoldedTile`, and the grammar answers adjacency and
//! membership from per-mold runs and flags.
//!
//! The tree and the obligations are identical, node by node, on every corpus
//! source and on each one cut short and with one significant token dropped at
//! eight positions.
//!
//! - Alternatives: dropping the whole-menu fallback inside windows removes most
//!   of the cost but changes 20 sources' trees, so it is not this crate's to
//!   make — the fallback is part of the molding the corpus checks. Memoizing
//!   completions across tied candidates by the slope they leave finds no two
//!   candidates leaving one slope on the corpus, and costs more than it saves.
//! - Reversal: a ranking key whose floor cannot be read without a dry-run, or a
//!   window delta that can shrink, voids the bound; the search then visits
//!   every survivor again.
//!
//! ### A tie the next token refutes runs no window
//!
//! Before the tied openers' windows run, the next significant token prunes
//! them. A tied mold whose right side faces no hole and that cannot end its
//! form is followed by one of its own form's next tiles, so a token that none
//! of those tiles is labelled with cannot follow it. A tied mold whose right
//! side faces a hole is followed by whatever fills the hole, which opens with
//! some form's first tile, so a token none of whose labels can begin a form
//! cannot follow it. The token's labels are its whole candidate menu, a
//! reserved uppercase word's generic fallback labels included, so the check
//! reads nothing of the state the opener would leave. A lone survivor wins
//! without a window; when the token refutes every opener, every one stays and
//! the windows decide as before. Over the corpus the trees are unchanged and
//! parsing takes half the time.
//!
//! A tied mold that can end its form is followed, past the form, by a tile a
//! hole of the form's sort faces on its left, since the whole form fills that
//! hole: a token none of whose molds faces such a hole cannot follow it. This
//! settles the receive `?(P). S` against the unknown type `?`, which tie at
//! `?`. No type form goes on with `(` after a whole type, so the parenthesis
//! refutes the unknown type, where a window of eight tokens ending inside a
//! payload such as `?(+{go : end})` read both readings as alike and kept the
//! unknown type, whose `.` then read as a path.
//!
//! The same pruning runs on every tie inside a window. A trailing separator
//! ties its list's two readings, the separator an element follows and the one
//! the closer follows, and a window has no window of its own to read past it.
//! Unpruned, the window would take the lower mold, read the closer as out of
//! place and charge the opener under test for it. No corpus tree depends on the
//! in-window pruning, but it decides ties the window would otherwise settle by
//! dry-running their completion.
//!
//! - Alternatives: one-token dry-run windows instead of the grammar check
//!   decide too few ties and disagree with the full windows on some; dropping
//!   the windows altogether loses the shared-prefix families the windows exist
//!   for. Inside a window, a one-token dry-run window per tie costs a dry-run
//!   per tied token for what the grammar check decides without one.
//! - Reversal: a grammar whose closed tile can be followed, within its form, by
//!   a tile that is not one of its same-form successors voids the check; the
//!   table's successor relation then has to carry that tile. A form whose hole
//!   can be filled by something that opens with a tile no form begins with
//!   voids the hole check. A form of one sort that stands in a hole of another,
//!   beyond the item sort every hole admits, voids the whole-form check.
//!
//! ### A window counts eight tokens
//!
//! A tied opener's window molds the eight significant tokens after it, whatever
//! they are. An attribute block is a form of its own before every declaration
//! it decorates, a decision of `gandr-surface-grammar`, so `@[` opens one
//! reading and its contents decide nothing between declarations. Two tied
//! openers on the corpus are brackets, and their trees are the same with a
//! window read past the closer.
//!
//! - Alternatives: a tied bracket opener whose contents and closer fill the
//!   count could mold through its closer and count its eight tokens from there;
//!   no tree on the corpus needs it, and it is a second window bound to keep
//!   right.
//! - Reversal: a family of readings that mold a bracket's contents alike and
//!   diverge only after its closer needs a window bounded by the closer, or by
//!   the grammar, instead of the token count.
//!
//! ### Interchangeable openers share one window
//!
//! A lowercase parameter name ties its `identifier` and `type_variable` molds:
//! both stand at one position of one form, with the same neighbours, context,
//! precedence and closing class, and only their labels differ. Everything the
//! melder reads of a pushed tile but its label agrees, so their windows mold
//! every later token alike and close with the same delta, and the window
//! comparison keeps the lesser mold. `Pbg::least_interchangeable` names each
//! mold's class, and of tied openers in one class only the least is kept before
//! any window runs; a class that was the whole tie then has a lone opener and
//! runs no window. Keeping one changes no corpus tree.
//!
//! - Alternatives: dropping the type-variable reading of a parameter name from
//!   the grammar removes the tie at its source, but it is a grammar change the
//!   lowering would have to follow; a window per class member molds every later
//!   token a second time for a known answer.
//! - Reversal: a melder that reads a pushed tile's label after the push — the
//!   label becomes a component of the class, and the classes split.
//!
//! ### An opener the next token continues beats a one-tile form
//!
//! A type name ties its two readings: the complete type `List`, a form of that
//! one tile, and the name that opens the application `List(T)`. When the next
//! significant token is `(`, the application's own next tile, the molder takes
//! the application without a window. A one-tile form is complete at its tile,
//! so the token after it would have to stand after the whole form, in whatever
//! encloses it, while the opener reads the token inside its own form: the
//! longer reading wins, as maximal munch. The rule applies only when exactly
//! one tied opener is continued that way and every other tied opener is a whole
//! one-tile form; any other tie keeps its window. It decides the
//! type-application family, the package type against a type variable, and
//! `pack` against an identifier.
//!
//! The opener may be one that could also end its form at its tile: a
//! constructor pattern's name opens `Some(x)`, whose arguments are optional,
//! and ties the bare constructor `Some`. Before `(` it is continued all the
//! same, and the corpus's windows chose it every time.
//!
//! A window can misread a long application. In `-F HomPlus(Integer, String, x,
//! x)` a window of eight tokens ends inside the argument list, so it scores the
//! unfinished application against the complete type `HomPlus` followed by a
//! complete parenthesized type, and takes the latter: the definition's return
//! type would be `-F HomPlus` with a stray tuple type beside it. The rule reads
//! the application whole.
//!
//! - Alternatives: a static table of the token sequences that tell each tied
//!   family apart, LL(k) over the same successor relation, which the corpus's
//!   ties need only for families this rule does not reach (the data
//!   declaration's two `:` readings); a longer window, which moves the
//!   misreading to longer argument lists and costs every tie more.
//! - Reversal: a grammar in which a one-tile form of some sort can itself be
//!   followed by the tile that continues its tied opener, so that both readings
//!   are well formed with different meanings — the rule then has to ask the
//!   enclosing form, or yield to the window, for that family.
//!
//! ### Readings that end alike before the next token keep the least
//!
//! A constructor pattern's name before `=>` ties its two rules, the opener of
//! `Some(x)` and the bare constructor; a parenthesized expression's `)` ties
//! the closers of its two shapes; a primitive type's name ties a type variable.
//! When every tied opener can end its form at its tile, none is continued by
//! the next significant token, and every opener's rule has one sort and one
//! precedence, the molder keeps the least opener without a window. Each reading
//! then ends a whole form before the token, and the forms stand alike as
//! operands to whatever follows, so every window closes with the same
//! obligations and the exact-tie rule keeps the least: the rule makes the
//! window's choice without molding it.
//!
//! - Alternatives: comparing the readings' whole outside view — closing class,
//!   context contents and rule as well as sort and precedence — which is
//!   stricter than any observed tie needs and would leave the primitive type
//!   and constructor families to the window; LL(k) tables over the successor
//!   relation, which these families do not need, since no reading goes on.
//! - Reversal: a grammar in which the rule of a complete form, not only its
//!   sort and precedence, changes how a later tile molds — a binder whose
//!   operand's rule decides what it binds, say. The rule then has to compare
//!   that too, or yield to the window.
//!
//! ### A shell string's text is its own lexeme
//!
//! A `"` opens an expression string in code and a double-quoted string in a
//! shell block, and both forms open with the same `"` label. The labeler
//! already scans the two interiors in different modes, so it gives a shell
//! string's text its own lexeme, `ShellStringFragment`, labelled
//! `double_string_fragment`, where an expression string's text stays a
//! `StringFragment` labelled `string_fragment`. The token after the `"` then
//! refutes the reading of the other context, and the tie runs no window.
//! Carrying both labels on both fragments would mold the two readings alike,
//! and the window would keep the lesser mold, the expression string, inside
//! shell blocks too.
//!
//! - Alternatives: a distinct label for the shell `"` itself, which is a
//!   grammar change for what the labeler already knows.
//! - Reversal: a string form that admits both interiors, which would take both
//!   labels again.
//!
//! ### A token's labels are derived once, held inline and read by number
//!
//! A token's candidate labels feed three steps: settling the holes it cannot
//! continue, gathering its menu, and, past a tie, refuting the openers it
//! cannot follow. `candidate_labels` returns them as `TokenLabels`, an array of
//! at most six held inline. The molder resolves them once per token to
//! `LabelIds`, the declared labels by number, and passes those to each step,
//! which reads menus and compares the labels of molds by number. Deriving the
//! labels again per step would cost two or three heap allocations per token,
//! and resolving them again a hash probe and a string comparison per label.
//!
//! - Alternatives: a `smallvec`, which is the same array behind a dependency;
//!   caching labels per token across windows, which re-reads a token's labels
//!   no cheaper than deriving them from its lexeme.
//! - Reversal: a lexeme whose menu outgrows the array; `candidate_labels`'s
//!   postcondition bounds each menu at four labels, so such a lexeme fails that
//!   check before it can lose a label.
//!
//! # References
//!
//! - `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: the
//!   directed-univalence design (§ The surface family) — `flow` is reserved as
//!   the lead of a flow between signatures, and `via` stays contextual.
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: the univalence
//!   design (§ The trust story) — `via` stands after an import's signature,
//!   naming the translation the importer reads through.
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation
//!   ruling (§ compilation-recipe-zero-cost) — a flow's renaming molds as any
//!   definition; what it costs is the lowering's to decide.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::CandidateCount;
use gandr_surface_grammar::LabelId;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::Observation;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::aliased;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;

use crate::Frontier;
use crate::MeldState;
use crate::closing::TileSpelling;
use crate::closing::tile_spelling;
use crate::label::Lexeme;
use crate::label::Token;
use crate::meld::CandidateLabels;
use crate::meld::DeclarationStart;
use crate::meld::FormUnit;
use crate::meld::Mark;
use crate::meld::MoldAdmissibility;
use crate::meld::SlopeHeight;
use crate::meld::SpaceText;
use crate::meld::TileText;
use crate::meld::UnitSeam;
use crate::meld::declaration_head;
use crate::meld::primitive_copy_wrapper;
use crate::oblig::Delta;
use crate::tables::Admission;
use crate::tables::PushKey;
use crate::tables::SettleChain;
use crate::tables::WindowClass;
use crate::tables::WindowClasses;

/// The most candidate labels a single lexeme can map to (a lowercase word: its
/// own keyword tile spelling, `identifier`, `type_variable`, and `hole_name`).
const MAX_LABELS: usize = 4;

/// The most labels a [`TokenLabels`] holds: a lexeme's own menu, and the
/// fallback labels the follow check adds for a reserved uppercase word.
const LABEL_CAPACITY: usize = MAX_LABELS + RESERVED_FALLBACK_LABELS.len();

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

/// The widest menu the tables admit candidate by candidate: composing an
/// [`Admission`] context reads one tile set per admitting context, which a
/// menu this narrow does not repay. Measured over the corpus, where most
/// menus hold a handful of molds.
pub const ADMISSION_MENU: usize = 4;

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

/// A token's candidate labels in their fixed order, held inline so that
/// deriving them allocates nothing.
///
/// # Specification
/// - ensures: reads as the slice of labels pushed, in push order, at most
///   [`LABEL_CAPACITY`] of them.
///
/// # Adequacy
/// - hypothesis: L3 — every lexeme's menu reads back as the exact label
///   sequence, and a reserved word's fallback labels follow its own.
/// - witness: `mold::tests::literal_and_shell_menus_are_exact`
/// - witness: `mold::tests::keyword_and_identifier_share_a_word_menu`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TokenLabels<'label>
{
    /// The labels, the first `count` of them live.
    labels: [CandidateLabel<'label>; LABEL_CAPACITY],
    /// How many labels are live.
    count: usize,
}

impl<'label> TokenLabels<'label>
{
    /// No labels.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new() -> Self
    {
        Self {
            labels: [CandidateLabel(""); LABEL_CAPACITY],
            count: 0,
        }
    }

    /// Append `label`.
    ///
    /// # Specification
    /// - requires: fewer than [`LABEL_CAPACITY`] labels are held; every caller
    ///   pushes a lexeme's menu and at most the fallback labels after it.
    /// - ensures: `label` is the last label, or nothing changes when the set is
    ///   full.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the menus of every lexeme and a reserved word's
    ///   fallback read back whole.
    /// - witness: `mold::tests::literal_and_shell_menus_are_exact`
    #[inline]
    #[spec(captures: before = self.count, ensures: |()| (before == LABEL_CAPACITY && self.count == before) || (self.count == before.saturating_add(1) && self.as_slice().last() == Some(&label)))]
    fn push(
        &mut self,
        label: CandidateLabel<'label>,
    )
    {
        if let Some(slot) = self.labels.get_mut(self.count) {
            *slot = label;
            self.count = self.count.saturating_add(1);
        }
    }

    /// The labels, in push order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[CandidateLabel<'label>]
    {
        self.labels.get(.. self.count).unwrap_or_default()
    }
}

impl<'label> core::ops::Deref for TokenLabels<'label>
{
    type Target = [CandidateLabel<'label>];

    /// The labels, in push order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &Self::Target
    {
        self.as_slice()
    }
}

impl<'set, 'label> IntoIterator for &'set TokenLabels<'label>
{
    type IntoIter = core::slice::Iter<'set, CandidateLabel<'label>>;
    type Item = &'set CandidateLabel<'label>;

    /// The labels, in push order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.as_slice().iter()
    }
}

impl<'label> IntoIterator for TokenLabels<'label>
{
    type IntoIter = core::iter::Take<core::array::IntoIter<CandidateLabel<'label>, LABEL_CAPACITY>>;
    type Item = CandidateLabel<'label>;

    /// The labels, in push order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.labels.into_iter().take(self.count)
    }
}

/// A token's declared labels by number, in the order of its labels, each
/// spelling the grammar does not declare left out: the token's spelling
/// resolved once, so each step reads the label's menus and compares the
/// labels of molds by number, with no further probe or string compare.
///
/// # Specification
/// - ensures: reads as the numbers resolved, in label order, at most
///   [`LABEL_CAPACITY`] of them; counts every label offered, declared or not.
///
/// # Adequacy
/// - hypothesis: L3 — duplicate, declared and absent labels resolve to the
///   numbers whose menus the gather reads; a dropped, reordered or misresolved
///   label changes the gathered menu.
/// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LabelIds
{
    /// The numbers, the first `count` of them live.
    ids: [LabelId; LABEL_CAPACITY],
    /// How many numbers are live.
    count: usize,
    /// How many labels the token offered, declared or not: none only when no
    /// token follows, or when the token has no label at all.
    offered: usize,
}

impl LabelIds
{
    /// No labels: no token follows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn new() -> Self
    {
        Self {
            ids: [LabelId::default(); LABEL_CAPACITY],
            count: 0,
            offered: 0,
        }
    }

    /// The numbers of the labels among `labels` that `pbg` declares, in
    /// their order.
    ///
    /// # Specification
    /// - requires: `labels` holds at most [`LABEL_CAPACITY`] labels.
    /// - ensures: holds the number of each declared label of `labels`, in
    ///   order, and counts every label of `labels` as offered.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type's.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[inline]
    #[spec(requires: labels.len() <= LABEL_CAPACITY, ensures: |ret| ret.offered == labels.len() && ret.as_slice().iter().copied().eq(labels.iter().filter_map(|label| pbg.label_id(LabelText(label.0)))))]
    fn resolve(
        pbg: &Pbg,
        labels: &[CandidateLabel<'_>],
    ) -> Self
    {
        let mut resolved = Self::new();
        resolved.offered = labels.len();
        for label in labels {
            if let Some(id) = pbg.label_id(LabelText(label.0))
                && let Some(slot) = resolved.ids.get_mut(resolved.count)
            {
                *slot = id;
                resolved.count = resolved.count.saturating_add(1);
            }
        }
        resolved
    }

    /// The numbers, in label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn as_slice(&self) -> &[LabelId]
    {
        self.ids.get(.. self.count).unwrap_or_default()
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
///   and the pattern string in a pattern slot. At the top level the slot is an
///   item's, which an expression fills only as an expression statement, so a
///   candidate opening an item-position declaration matches there too: `run`
///   opening a bind statement and `run` opening an expression tie, and the
///   lookahead reads which follows.
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

/// Whether a token can stand right after a mold.
///
/// # Specification
/// - ensures: `Refuted` when a hole faces the mold on its right and none of the
///   token's candidate labels can begin a form, or when no hole faces it, the
///   mold cannot end its form, and none of its same-form successors carries one
///   of the token's candidate labels; `Possible` otherwise.
/// - panics: none.
/// - executable: none — a plain value; [`Molder::follow`] carries the
///   executable clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Follow
{
    /// The token can follow: it can begin what fills the mold's hole, or the
    /// form's end or a successor admits it.
    Possible,
    /// The mold's next symbol is a hole the token cannot begin, or a tile of
    /// its own form the token is none of.
    Refuted,
}

/// What a choice may read past the token it molds.
///
/// # Specification
/// - ensures: `Stream` names the labeled stream, the molded token's index in it
///   and the text the stream spells; `Nothing` names no stream.
/// - panics: none.
/// - executable: none — a plain value.
#[derive(Clone, Copy, Debug)]
enum Ahead<'tokens, 'src>
{
    /// The single-token path: nothing past the token is known.
    Nothing,
    /// The token stands at `index` of `tokens`, which `source` spells.
    Stream
    {
        /// The labeled stream.
        tokens: &'tokens [Token],
        /// The molded token's index in `tokens`.
        index: TokenIndex,
        /// The text `tokens` index into.
        source: &'src SourceFragment<'src>,
    },
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
/// the `for … in` / `while` / `break` / `continue` control forms, the `case …
/// with …` view, the `import` declaration, and the `module` declaration. A
/// corpus + fixture sweep found no collision with any existing identifier, so
/// all reserve globally (the keyword table is provisional; a real collision
/// would move the offender to a contextual keyword). `loop` met that collision
/// first: the book's circle names its cell `loop` (`loop : Base <-> Base`),
/// so `loop` is contextual — its tile molds where `loop { … }` opens an
/// expression, the identifier everywhere else, and the window after the word
/// tells the two apart at an expression slot (`{` against anything else).
/// `codata`
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
/// leads, `theory` and `oper`: at a fresh top-level slot a lowercase word is
/// otherwise an expression statement, so an unreserved form-first lead would
/// tie its own tile against `identifier` at every declaration. Its four other
/// leads stay **contextual** — the member keyword `sort` (beside the already-
/// reserved `data` / `rule`) and the body statements `node` / `feed` are
/// `≐`-successors inside an open `theory` block or circuit body, so a user
/// program may still bind `sort`, `node`, or `feed` as an ordinary name;
/// `theory` and `oper` it may not. `sort` in particular could not be reserved
/// even if wanted: `list.sort` is a live projection in the corpus. Contextual
/// is not the same as inadmissible-elsewhere, and the circuit grammar module
/// records the one slot where `sort`'s mold does collide with a type variable.
///
/// The capability scope reserves its lead `handle`: it opens an expression,
/// where an unreserved lead would tie its own tile against `identifier` at
/// every expression slot. Temporary access reserves its leads `access`,
/// `resume` and `abort` for the same reason, and `unwind`, the tile after an
/// access's body, so a name there is never read as the next statement.
///
/// A world declaration reserves its lead `world`, an item-position lead as
/// `theory` is, and the mobility mark its lead `mobile`, which opens a module
/// signature's field where an unreserved word would tie against the value
/// field's `identifier`. A flow declaration reserves its lead `flow` for the
/// same reason as `world`; `via`, which names the flow an import reads its
/// source through, stays contextual, since no identifier stands after an
/// import's signature.
///
/// `inf`, the ASCII spelling of the grade `ω`, is reserved: a grade slot
/// admits a name as well as `ω`, and an unreserved `inf` would tie its glyph's
/// tile against `identifier` there.
pub const KEYWORDS: &[&str] = &[
    "def", "val", "run", "leta", "as", "extern", "from", "type", "fn", "pure", "return", "become",
    "thunk", "force", "case", "if", "else", "co", "hold", "dup", "drop", "send", "recv", "close",
    "select", "offer", "fork", "acquire", "release", "migrate", "at", "true", "false", "unit",
    "mu", "end", "data", "codata", "rec", "op", "rule", "for", "in", "while", "break", "continue",
    "with", "import", "module", "theory", "oper", "handle", "access", "unwind", "resume", "abort",
    "world", "mobile", "inf", "pub", "flow",
];

/// The keywords that open a block's statements: one that no open form
/// continues ends the statement it stands in, and starts the next.
const STATEMENT_LEADS: &[&str] = &[
    "val", "run", "unpack", "leta", "hold", "recv", "acquire", "release", "fork",
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
///   [`Lexeme::Space`] and [`Lexeme::Unknown`]. A word's menu leads with its
///   own text, save a lowercase word spelled as a lexical class's label
///   (`number`, `constructor`), whose menu is a name's alone.
/// - provides: the molder's per-token candidate-label source.
/// - fails: never.
/// - panics: none.
///
///
/// # Adequacy
/// - hypothesis: L3 — every lexeme menu, reserved and ordinary words, canonical
///   versus dialect shell openers and each ASCII token of the spelling table
///   (`<~>`, `~~>`, `::`, `inf`) expose exact label sequences. Dropping a
///   generic alternative, widening a keyword or losing the source spelling
///   changes the menu.
/// - witness: `mold::tests::keyword_and_identifier_share_a_word_menu`
/// - witness: `mold::tests::literal_and_shell_menus_are_exact`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.is_empty() == matches!(lexeme, Lexeme::Space | Lexeme::Unknown) && ret.len() <= MAX_LABELS && (!matches!(lexeme, Lexeme::LowerWord | Lexeme::UpperWord | Lexeme::Punct) || ret.first().is_some_and(|label| label.0 == text.0) || (matches!(lexeme, Lexeme::LowerWord) && tile_spelling(CandidateLabel::from(text.0)) != TileSpelling::Literal(text.0))))]
pub fn candidate_labels<'text>(
    lexeme: Lexeme,
    text: TokenText<'text>,
) -> TokenLabels<'text>
{
    let text = <&str>::from(text);
    let mut labels = TokenLabels::new();
    match lexeme {
        Lexeme::LowerWord => {
            // A word spelled as a lexical class's label (`number`,
            // `constructor`) is a name, never a token of that class.
            if tile_spelling(CandidateLabel::from(text)) == TileSpelling::Literal(text) {
                labels.push(CandidateLabel::from(text));
            }
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
            if let Some(tile) = aliased(LabelText(text)) {
                labels.push(CandidateLabel::from(tile.0));
            }
        },
        Lexeme::UpperWord => {
            labels.push(CandidateLabel::from(text));
            // A reserved primitive/type keyword is never a constructor or a
            // type identifier; only its own tile is a candidate.
            if !UPPER_KEYWORDS.contains(&text) {
                labels.push(CandidateLabel::from("constructor"));
                labels.push(CandidateLabel::from("type_identifier"));
            }
        },
        Lexeme::Number => labels.push(CandidateLabel::from("number")),
        Lexeme::TypedNumber => labels.push(CandidateLabel::from("typed_number")),
        Lexeme::Character => labels.push(CandidateLabel::from("character")),
        Lexeme::Quote => labels.push(CandidateLabel::from("\"")),
        Lexeme::StringFragment => labels.push(CandidateLabel::from("string_fragment")),
        Lexeme::ShellStringFragment => {
            labels.push(CandidateLabel::from("double_string_fragment"));
        },
        Lexeme::EscapeSequence => labels.push(CandidateLabel::from("escape_sequence")),
        // ONE label: the grammar's single shell-word atom class.
        // The former `command_name` / `argument` labels rode the
        // dead composite shell rules; with those folded away, a shell word has
        // exactly one mold and takes the molder's sole-admissible fast path —
        // no dry-run, no lookahead, per word.
        Lexeme::ShellWord => labels.push(CandidateLabel::from("shell_word")),
        // ONE label, like the shell word: the labeler has already decided the
        // `NAME=value` shape, so the assignment takes the sole-admissible fast
        // path too (no dry-run, no lookahead). The mold and its walk-index entry
        // already existed — only the tile was missing.
        Lexeme::EnvAssign => labels.push(CandidateLabel::from("environment_assignment")),
        Lexeme::SingleQuotedContent => {
            labels.push(CandidateLabel::from("single_quoted_content"));
        },
        Lexeme::VariableName => labels.push(CandidateLabel::from("variable_name")),
        Lexeme::SubshellOpen => labels.push(CandidateLabel::from("subshell_open")),
        Lexeme::SubshellClose => labels.push(CandidateLabel::from("subshell_close")),
        Lexeme::FileDescriptor => labels.push(CandidateLabel::from("file_descriptor")),
        Lexeme::Punct => {
            labels.push(CandidateLabel::from(text));
            // A dialect-bearing shell opener (`#!sh{`, `$!py{`) lexes as one
            // punctuation token; map it to the canonical opener label.
            if text.starts_with("#!") && text.ends_with('{') {
                labels.push(CandidateLabel::from("#!{"));
            }
            else if text.starts_with("$!") && text.ends_with('{') {
                labels.push(CandidateLabel::from("command_substitution_start"));
            }
            // An ASCII spelling the spelling table pairs with a glyph offers
            // the glyph's tile, so the alias molds the glyph's one form.
            else if let Some(tile) = aliased(LabelText(text)) {
                labels.push(CandidateLabel::from(tile.0));
            }
        },
        Lexeme::Space | Lexeme::Unknown => {},
    }
    labels
}

/// Return whether some fresh-slot reading of `token` opens an item-position
/// declaration under `pbg`.
///
/// The token's labels are resolved once, by number, and each label's fresh
/// menu is read for a mold [`declaration_head`] accepts.
///
/// # Specification
/// - requires: the token bounds identify its exact source fragment.
/// - ensures: true exactly when one of the token's candidate labels has a
///   fresh-slot mold that [`declaration_head`] accepts.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — declaration keywords, an attribute opener, an identifier
///   and a terminator distinguish heads from the rest; reading the declared
///   menu instead of the fresh one, or one label of several, moves a predicted
///   boundary.
/// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
#[spec(requires: source.as_ref().get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some())]
#[inline]
#[must_use]
pub fn heads_declaration(
    pbg: &Pbg,
    token: Token,
    source: &SourceFragment<'_>,
) -> DeclarationStart
{
    let slice = token.text(source);
    let text = TokenText::from(AsRef::<str>::as_ref(&slice));
    let labels = LabelIds::resolve(pbg, &candidate_labels(token.lexeme, text));
    DeclarationStart::from(labels.as_slice().iter().any(|&label| {
        pbg.label_fresh_candidates(label)
            .iter()
            .any(|&mold| bool::from(declaration_head(pbg, mold)))
    }))
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
/// word can still name the declaration (`theory Unknown`). `U` and `F` are not
/// reserved: the bridges are the compound tiles `+U` and `-F`, and the bare
/// letters are names like any other. `Cap` is reserved as `Path` is: the
/// capability former's own tile.
const UPPER_KEYWORDS: &[&str] = &[
    "Any", "Unknown", "Never", "Boolean", "Integer", "Char", "String", "Symbol", "Unit", "Void",
    "Path", "Type", "Cap",
];

/// The generic labels a reserved uppercase word falls back to where its own
/// tile cannot mold: [`Molder::gather_reserved_fallback`] re-admits them, and
/// [`next_labels`] counts them among the word's labels.
const RESERVED_FALLBACK_LABELS: [&str; 2] = ["constructor", "type_identifier"];

/// The rule whose `(` opens a parenthesized type, the domain list of a
/// value-function type among its readings.
const PARENTHESIZED_TYPE: RuleName = RuleName("parenthesized_type");

/// The rule whose `(` opens the unit, a parenthesized expression, a tuple or
/// an ascription.
const PARENTHESIZED_EXPRESSION: RuleName = RuleName("parenthesized_expression");

/// How the group a `(` opens closes on the stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GroupClose
{
    /// The group is empty: its `)` is the next significant token.
    Empty,
    /// The group closes, and `=>` is the next significant token past it.
    Arrow,
    /// The group closes before any other token, or before the stream's end.
    Other,
    /// The stream ends inside the group.
    Open,
}

/// Return how the group the `(` at `index` opens closes: a punctuation token
/// ending in `(` opens a nested group, as `type(` does, and `)` closes the
/// innermost.
///
/// # Specification
/// - requires: `tokens` is the labeler output for `source`; `index` names a
///   token whose text ends in `(`.
/// - ensures: [`GroupClose::Empty`] when the next significant token is `)`;
///   otherwise, past the `)` that balances the opener, [`GroupClose::Arrow`]
///   when the next significant token is `=>` and [`GroupClose::Other`]
///   otherwise; [`GroupClose::Open`] when no `)` balances it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an empty group, a nested call and quote inside the group,
///   a group closed before `=>`, before another token and at the stream's end,
///   and an unbalanced group expose each answer. Counting a string fragment's
///   `(`, or stopping at a nested `)`, reads the wrong token past the group.
/// - witness: `mold::tests::a_group_closes_past_its_nested_groups_2255`
#[spec(ensures: |ret| ret != GroupClose::Empty || next_significant(tokens, index).is_some_and(|(_, token)| AsRef::<str>::as_ref(&token.text(source)) == ")"))]
fn group_close(
    tokens: &[Token],
    index: TokenIndex,
    source: &SourceFragment<'_>,
) -> GroupClose
{
    let punct = |token: Token, text: &str| {
        token.lexeme == Lexeme::Punct && AsRef::<str>::as_ref(&token.text(source)) == text
    };
    if next_significant(tokens, index).is_some_and(|(_, token)| punct(token, ")")) {
        return GroupClose::Empty;
    }
    let mut depth = 0_usize;
    let mut cursor = index;
    while let Some(&token) = tokens.get(usize::from(cursor)) {
        if token.lexeme == Lexeme::Punct {
            let text = token.text(source);
            let text = AsRef::<str>::as_ref(&text);
            if text.ends_with('(') {
                depth = depth.saturating_add(1);
            }
            else if text == ")" {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return match next_significant(tokens, cursor) {
                        Some((_, next)) if punct(next, "=>") => GroupClose::Arrow,
                        Some(_) | None => GroupClose::Other,
                    };
                }
            }
        }
        cursor = TokenIndex::from(usize::from(cursor).saturating_add(1));
    }
    GroupClose::Open
}

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

/// The whole candidate menu of the next significant token after `index`: its
/// labels, and a reserved uppercase word's generic fallback labels.
///
/// The menu reads the token alone, so a decision taken on it never depends
/// on the state a mold would leave.
///
/// # Specification
/// - requires: `index` indexes `tokens`, which `source` spells.
/// - ensures: none at the stream's end; otherwise the [`candidate_labels`] of
///   [`next_significant`]'s token, followed by [`RESERVED_FALLBACK_LABELS`]
///   when that token is a reserved uppercase word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a name, a reserved uppercase word, a closer and the
///   stream's end read through the follow check: dropping the fallback refutes
///   the parameter comma before `Type`, and reading the current token instead
///   keeps the open comma before a closer.
/// - witness: `mold::tests::the_next_token_keeps_only_the_molds_it_can_follow`
#[spec(ensures: |ret| ret.as_ref().map(|labels| labels.len()) == next_significant(tokens, index).map(|(_, next)| { let text = TokenText::from(<&str>::from(next.text(source))); candidate_labels(next.lexeme, text).len().saturating_add(if matches!(next.lexeme, Lexeme::UpperWord) && UPPER_KEYWORDS.contains(&<&str>::from(text)) { RESERVED_FALLBACK_LABELS.len() } else { 0 }) }))]
fn next_labels<'src>(
    tokens: &[Token],
    index: TokenIndex,
    source: &'src SourceFragment<'src>,
) -> Option<TokenLabels<'src>>
{
    let (_, next) = next_significant(tokens, index)?;
    let text = TokenText::from(<&str>::from(next.text(source)));
    let mut labels = candidate_labels(next.lexeme, text);
    if matches!(next.lexeme, Lexeme::UpperWord) && UPPER_KEYWORDS.contains(&<&str>::from(text)) {
        for fallback in RESERVED_FALLBACK_LABELS {
            labels.push(CandidateLabel::from(fallback));
        }
    }
    Some(labels)
}

/// How a token takes part in bracket nesting.
///
/// # Specification
/// - ensures: `Open` for a punctuation or subshell token whose text ends in
///   `(`, `[` or `{`, `Close` for one that is `)`, `]` or `}`, `Neither`
///   otherwise.
/// - panics: none.
/// - executable: none — a plain value; [`bracket`] carries the executable
///   clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Bracket
{
    /// The token opens a bracket: `(`, `[`, `{`, or a compound opener such as
    /// `@[` or `#{`.
    Open,
    /// The token closes the innermost open bracket.
    Close,
    /// The token does not nest.
    Neither,
}

/// Classify `token`, whose text is `text`, for bracket nesting.
///
/// Every family nests alike: a closer closes the innermost open bracket
/// whatever opened it, so a mismatched closer still balances the count, the
/// convention [`Molder::form_runs`] splits by.
///
/// # Specification
/// - requires: `text` is `token`'s text.
/// - ensures: [`Bracket::Open`] exactly when `token` is punctuation or a
///   subshell bracket and `text` ends in `(`, `[` or `{`; [`Bracket::Close`]
///   exactly when it is one of those and `text` is `)`, `]` or `}`;
///   [`Bracket::Neither`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — plain and compound openers, the three closers, a word and
///   a string fragment spelling a bracket; reading the lexeme loosely counts a
///   bracket inside a string, and reading the closer by suffix counts `]]` or a
///   compound closer that does not exist.
/// - witness: `mold::tests::brackets_are_classified_by_lexeme_and_text`
#[spec(ensures: |ret| ret == if !matches!(token.lexeme, Lexeme::Punct | Lexeme::SubshellOpen | Lexeme::SubshellClose) {
    Bracket::Neither
} else if <&str>::from(text).ends_with(['(', '[', '{']) {
    Bracket::Open
} else if matches!(<&str>::from(text), ")" | "]" | "}") {
    Bracket::Close
} else {
    Bracket::Neither
})]
fn bracket(
    token: Token,
    text: TokenText<'_>,
) -> Bracket
{
    if !matches!(
        token.lexeme,
        Lexeme::Punct | Lexeme::SubshellOpen | Lexeme::SubshellClose
    ) {
        return Bracket::Neither;
    }
    let text = <&str>::from(text);
    if text.ends_with(['(', '[', '{']) {
        Bracket::Open
    }
    else if matches!(text, ")" | "]" | "}") {
        Bracket::Close
    }
    else {
        Bracket::Neither
    }
}

/// The position after the last token a run ending before `end` reads past
/// its end: the [`LOOKAHEAD`]-th significant token from `end` on, the spaces
/// before it included, or the stream's end when fewer remain.
///
/// A run's last token is the farthest-reaching: its tie-breaking window
/// ([`Molder::mold_window`]) begins at `end` and molds at most [`LOOKAHEAD`]
/// significant tokens, recording the spaces among them and none after the
/// last; the direct-binder check reads two significant tokens, inside that
/// window.
///
/// # Specification
/// - requires: nothing; an `end` past the stream reads as the stream's end.
/// - ensures: the least position at or after `end` whose prefix from `end`
///   holds [`LOOKAHEAD`] significant tokens, the last of them just before it;
///   the stream's length when fewer than [`LOOKAHEAD`] remain.
/// - provides: the extent of the tokens past its run a form unit depends on,
///   which [`FormSplit::identity`](crate::FormSplit::identity) covers.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — streams of spaced and adjacent significant tokens,
///   shorter and longer than the window, from every origin; counting spaces
///   against the window, stopping one short or swallowing the spaces after the
///   last token moves the reach.
/// - witness: `mold::tests::a_run_reads_eight_significant_tokens_past_its_end`
/// - witness: `parse::tests::an_equal_identity_molds_an_equal_unit`
#[spec(ensures: |ret| usize::from(ret) <= tokens.len()
    && usize::from(ret) >= usize::from(end).min(tokens.len())
    && tokens.get(usize::from(end).min(tokens.len()) .. usize::from(ret)).is_some_and(|window|
        window.iter().filter(|token| token.lexeme != Lexeme::Space).count() == LOOKAHEAD
            || usize::from(ret) == tokens.len()))]
pub fn lookahead_reach(
    tokens: &[Token],
    end: TokenIndex,
) -> TokenIndex
{
    let mut significant = 0_usize;
    let mut reach = usize::from(end).min(tokens.len());
    while significant < LOOKAHEAD {
        let Some(token) = tokens.get(reach)
        else {
            break;
        };
        if !matches!(token.lexeme, Lexeme::Space) {
            significant = significant.saturating_add(1);
        }
        reach = reach.saturating_add(1);
    }
    TokenIndex::from(reach)
}

/// How a [`Molder`] reaches its verdicts.
///
/// The verdicts are the dry runs' in every mode: the modes differ in how
/// many dry runs and windows reach them. [`Tables`](Self::Tables) is the
/// molder [`Molder::new`] builds; [`DryRuns`](Self::DryRuns) is the
/// procedure the tables are witnessed against, kept as their oracle;
/// [`Differential`](Self::Differential) runs both at every decision.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MoldVerdicts
{
    /// Admit through the grammar's tile sets, dry-run one candidate per push
    /// class, and mold one window per window class (`crate::tables`).
    #[default]
    Tables,
    /// Admit, dry-run and mold a window for every candidate and opener.
    DryRuns,
    /// Decide every token both ways, push the dry runs' verdict, and count
    /// each decision where the two disagree.
    Differential,
}

/// One way of reaching a decision: the procedure a [`MoldVerdicts`] mode
/// runs, or each of the two a differential molder runs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Procedure
{
    /// Through the tables.
    Tables,
    /// Through a dry run per candidate and a window per opener.
    DryRuns,
}

/// How many decisions a differential molder saw its two procedures settle
/// differently: the admitted menu or the chosen mold.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct DisagreementCount(pub usize);

/// What a window class's first window showed of its members' windows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum WindowRun
{
    /// The window read nothing of its opener beyond the class: every member
    /// molds it alike, so none molds its own.
    Shared,
    /// The window gathered a token's whole declared menu, where the members'
    /// own successors meet it: each member molds its own window.
    Exposed,
}

/// When a molding stops short of its run's end.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Halt
{
    /// Never: every token of the run is molded.
    Never,
    /// After the first push that leaves a repair.
    AtRepair,
}

/// How a molding that halts at its first repair ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Molding
{
    /// Every token was molded.
    Whole,
    /// A push left a repair, and the tokens after it were not molded.
    Halted,
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
    /// How the molder reaches its verdicts.
    verdicts: MoldVerdicts,
    /// Reused candidate-mold buffer, sorted and de-duplicated per token.
    candidates: Vec<MoldId>,
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
    /// The frontiers a push may consult, read once per decision.
    chain: SettleChain,
    /// Reused observation classes of the ranked candidates, sorted, to find
    /// a class two of them share.
    observed: Vec<Observation>,
    /// Reused streaming deltas of the push classes dry-run this decision.
    pushes: Vec<(PushKey, Delta)>,
    /// Reused completion deltas of the push classes this decision.
    completions: Vec<(PushKey, Delta)>,
    /// Reused window-signature buffers.
    windows: WindowClasses,
    /// Reused window classes of the openers, beside `openers`.
    opener_classes: Vec<WindowClass>,
    /// Reused push keys of the openers, beside `openers`.
    opener_keys: Vec<PushKey>,
    /// Reused sorted copy of `opener_keys`, to find a key two openers share.
    shared_keys: Vec<PushKey>,
    /// Reused classes whose first window this decision molded.
    windowed: Vec<(PushKey, WindowClass, WindowRun)>,
    /// Inside a window, the slope height the window's opener stands at: a
    /// frontier at or above it is the opener's form or the window's own.
    window_floor: Option<SlopeHeight>,
    /// Whether the window being molded gathered a token's whole declared
    /// menu where a push could reach a frontier at or above the window's
    /// floor below the nearest.
    exposed: bool,
    /// How many decisions the two procedures settled differently.
    disagreements: DisagreementCount,
}

impl<'pbg> Molder<'pbg>
{
    /// Create a molder over `pbg` that reaches its verdicts through the
    /// tables.
    ///
    /// # Specification
    /// - requires: `pbg` is a checked PBG.
    /// - ensures: returns a molder with an empty candidate buffer, in
    ///   [`MoldVerdicts::Tables`] mode.
    /// - provides: the molder constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh molder holds empty buffers before any token
    ///   is gathered; a buffer carried over from another molding changes the
    ///   first token's candidates.
    /// - witness: `mold::tests::candidate_gathering_is_a_canonical_union`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.verdicts == MoldVerdicts::Tables && ret.candidates.is_empty() && ret.eligible.is_empty() && ret.ranked.is_empty() && ret.tied.is_empty() && ret.openers.is_empty())]
    pub fn new(pbg: &'pbg Pbg) -> Self
    {
        Self::with_verdicts(pbg, MoldVerdicts::Tables)
    }

    /// Create a molder over `pbg` that reaches its verdicts as `verdicts`
    /// says.
    ///
    /// # Specification
    /// - requires: `pbg` is a checked PBG.
    /// - ensures: returns a molder with empty buffers and no disagreement, in
    ///   `verdicts` mode.
    /// - provides: the oracle and differential molders the tables are witnessed
    ///   with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the differential witness builds its molders here and
    ///   reads their verdicts against each other.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.verdicts == verdicts && ret.disagreements == DisagreementCount(0) && ret.candidates.is_empty())]
    pub fn with_verdicts(
        pbg: &'pbg Pbg,
        verdicts: MoldVerdicts,
    ) -> Self
    {
        Self {
            pbg,
            verdicts,
            candidates: Vec::new(),
            eligible: Vec::new(),
            ranked: Vec::new(),
            tied: Vec::new(),
            openers: Vec::new(),
            chain: SettleChain::default(),
            observed: Vec::new(),
            pushes: Vec::new(),
            completions: Vec::new(),
            windows: WindowClasses::default(),
            opener_classes: Vec::new(),
            opener_keys: Vec::new(),
            shared_keys: Vec::new(),
            windowed: Vec::new(),
            window_floor: None,
            exposed: false,
            disagreements: DisagreementCount(0),
        }
    }

    /// How many decisions this molder's two procedures settled differently:
    /// always none outside [`MoldVerdicts::Differential`] mode.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn disagreements(&self) -> DisagreementCount
    {
        self.disagreements
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body gathers and sorts the same candidate buffer"
        )
    )]
    #[spec(ensures: |ret| ret.0 == self.candidates.len() && self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    pub fn candidate_count(
        &mut self,
        token: Token,
        src: SourceText<'_>,
    ) -> CandidateCount
    {
        // The bench probe reports the full declared menu (no live frontier).
        let source = source_slice(src);
        let slice = token.text(&source);
        let labels = candidate_labels(token.lexeme, TokenText::from(AsRef::<str>::as_ref(&slice)));
        self.gather_menu(
            &LabelIds::resolve(self.pbg, &labels),
            None,
            CandidateMenu::Declared,
        );
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
        let labels = LabelIds::resolve(self.pbg, &candidate_labels(token.lexeme, text));
        state.settle_shadowing_frontiers(CandidateLabels::from(labels.as_slice()));
        self.gather(state, token.lexeme, text, &labels);
        self.settle_statement(state, token.lexeme, text, &labels, Ahead::Nothing);
        state.settle_declaration_boundary(&self.candidates);
        let best = self.choose(state, text, Ahead::Nothing);
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
        let _molding = self.mold_until(state, tokens, run, src, Halt::Never);
    }

    /// Mold and push a whole labeled token stream as
    /// [`mold_stream`](Self::mold_stream) does, stopping after the first push
    /// that leaves a repair.
    ///
    /// A repair, once pushed, stays: only a dry run's rollback drops one, and a
    /// dry run never reaches behind the tile it weighs. So the first push that
    /// leaves one settles whether the stream molds with none, and a caller
    /// that wants only that answer skips molding the rest.
    ///
    /// # Specification
    /// - requires: as [`mold_stream`](Self::mold_stream), and `state` holds no
    ///   obligation yet.
    /// - ensures: [`Molding::Whole`] exactly when `state`'s obligations are
    ///   empty, every token then molded as [`mold_stream`](Self::mold_stream)
    ///   molds it; [`Molding::Halted`] with the stream molded up to and
    ///   including the first tile whose push left an obligation.
    /// - provides: the cheap test the placement in `parse::place` runs over
    ///   each copy of a form it tries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over every prefix of sources that mold whole, with a
    ///   closer left out and with one too many, the answer is whether the whole
    ///   molding leaves no obligation; a check that stopped early on a repair a
    ///   later tile withdrew, or ran past one, changes it.
    /// - witness: `parse::place::tests::a_try_stopped_at_its_first_repair_answers_as_a_whole_parse`
    #[inline]
    #[spec(
        requires: state.obligations().is_empty() && tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()),
        ensures: |ret| (ret == Molding::Whole) == state.obligations().is_empty(),
    )]
    pub(crate) fn mold_stream_until_repair(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        src: SourceText<'_>,
    ) -> Molding
    {
        let whole = TokenRun::new(TokenIndex::from(0_usize), TokenIndex::from(tokens.len()));
        self.mold_until(state, tokens, whole, src, Halt::AtRepair)
    }

    /// Mold and push the tokens of `run` as [`mold_run`](Self::mold_run)
    /// does, stopping after the first push that leaves a repair.
    ///
    /// # Specification
    /// - requires: as [`mold_run`](Self::mold_run), and `state` holds no
    ///   obligation yet.
    /// - ensures: [`Molding::Whole`] exactly when `state`'s obligations are
    ///   empty, every token of `run` then molded as
    ///   [`mold_run`](Self::mold_run) molds it; [`Molding::Halted`] with `run`
    ///   molded up to and including the first tile whose push left an
    ///   obligation.
    /// - provides: the resumed test the placement in `parse::place` runs over
    ///   the part of a copy that parts from its form.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as
    ///   [`mold_stream_until_repair`](Self::mold_stream_until_repair) and
    ///   [`mold_run`](Self::mold_run).
    /// - witness: `parse::place::tests::a_resumed_copy_answers_as_a_fresh_one`
    #[inline]
    #[spec(
        requires: state.obligations().is_empty() && tokens.iter().all(|token| <&str>::from(src).get(usize::try_from(token.start).unwrap_or(usize::MAX) .. usize::try_from(token.end).unwrap_or(usize::MAX)).is_some()),
        ensures: |ret| (ret == Molding::Whole) == state.obligations().is_empty(),
    )]
    pub(crate) fn mold_run_until_repair(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        run: TokenRun,
        src: SourceText<'_>,
    ) -> Molding
    {
        self.mold_until(state, tokens, run, src, Halt::AtRepair)
    }

    /// Mold and push the tokens of `run` as [`mold_run`](Self::mold_run)
    /// does, until `halt` stops it.
    ///
    /// # Specification
    /// - requires: as [`mold_run`](Self::mold_run).
    /// - ensures: as [`mold_run`](Self::mold_run) under [`Halt::Never`], then
    ///   [`Molding::Whole`]; under [`Halt::AtRepair`], the same tokens molded
    ///   up to and including the first whose push left an obligation, then
    ///   [`Molding::Halted`], or every token with none, then
    ///   [`Molding::Whole`].
    /// - panics: none.
    /// - executable: none — the clause restates the loop's exit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`mold_run`](Self::mold_run) and
    ///   [`mold_stream_until_repair`](Self::mold_stream_until_repair).
    /// - witness: `mold::tests::runs_mold_as_the_whole_stream`
    /// - witness: `parse::place::tests::a_try_stopped_at_its_first_repair_answers_as_a_whole_parse`
    fn mold_until(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        run: TokenRun,
        src: SourceText<'_>,
        halt: Halt,
    ) -> Molding
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
                let labels = LabelIds::resolve(self.pbg, &candidate_labels(token.lexeme, text));
                state.settle_shadowing_frontiers(CandidateLabels::from(labels.as_slice()));
                self.gather(state, token.lexeme, text, &labels);
                let ahead = Ahead::Stream {
                    tokens,
                    index: TokenIndex::from(index),
                    source: &source,
                };
                self.settle_statement(state, token.lexeme, text, &labels, ahead);
                state.settle_declaration_boundary(&self.candidates);
                let best = self.choose_stream(state, tokens, TokenIndex::from(index), &source);
                Self::push_choice(state, best, text);
                if halt == Halt::AtRepair && !state.obligations().is_empty() {
                    return Molding::Halted;
                }
            }
            index = index.saturating_add(1);
        }
        Molding::Whole
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
            if depth == 0
                && after_terminator
                && bool::from(heads_declaration(self.pbg, token, &source))
            {
                runs.push(TokenRun::new(
                    TokenIndex::from(start),
                    TokenIndex::from(index),
                ));
                start = index;
            }
            let slice = token.text(&source);
            let text = AsRef::<str>::as_ref(&slice);
            match bracket(token, TokenText::from(text)) {
                Bracket::Open => depth = depth.saturating_add(1),
                Bracket::Close => depth = depth.saturating_sub(1),
                Bracket::Neither => {},
            }
            after_terminator = matches!(token.lexeme, Lexeme::Punct) && matches!(text, ";" | "}");
        }
        runs.push(TokenRun::new(
            TokenIndex::from(start),
            TokenIndex::from(tokens.len()),
        ));
        runs
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
            Some(mold) => state.push_text(mold, TileText::from(text)),
            // No candidate mold: the totally-defined unmolded path. An
            // out-of-range mold id routes `push` to `UnmoldedTok` (grammar-total
            // fallback) while preserving the token text.
            None => state.push_text(MoldId::from(u32::MAX), TileText::from(text)),
        }
    }

    /// Gather the sorted, de-duplicated candidate molds for a token's
    /// `labels`, restricted to the fresh-slot menu when no form is open.
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
    /// - requires: `labels` are the declared labels, by number, of a token of
    ///   `lexeme` spelled `text`.
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
    /// - witness: `tests::acceptance::a_theory_block_may_be_named_with_a_primitive_type_spelling`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body gathers and sorts the same candidate buffer"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather(
        &mut self,
        state: &MeldState<'_>,
        lexeme: Lexeme,
        text: TokenText<'_>,
        labels: &LabelIds,
    )
    {
        let open = state.open_form_mold();
        self.gather_menu(labels, open, CandidateMenu::Fresh);
        if self.candidates.is_empty() {
            // A stray form-continuation with no matching frontier: the full menu
            // supplies the tile the melder pushes to flag the exact obligation.
            self.gather_menu(labels, open, CandidateMenu::Declared);
            // Every open frontier's successors of the label are in the
            // declared menu: a window class's members meet their own here
            // when a push can reach their form below the nearest frontier.
            self.note_declared_menu(state);
        }
        self.gather_reserved_fallback(state, lexeme, text, open);
        self.drop_stray_keyword(state, lexeme, text);
    }

    /// Close the statement a statement keyword stands in, when the keyword
    /// continues no open form and fills no empty slot.
    ///
    /// The keyword's whole declared menu names the close
    /// ([`MeldState::statement_close`]). On the stream path the keyword's
    /// window is molded twice under a mark, read as it stands and after the
    /// close, and the close is applied unless the window read as it stands
    /// owes less; on the single-token path it is applied. The keyword's
    /// menu is then gathered again at the frontier the close leaves.
    ///
    /// # Specification
    /// - requires: `labels` are `text`'s candidate labels and the candidate
    ///   buffer holds their gathered menu at `state`'s frontier.
    /// - ensures: `state` is closed by [`MeldState::statement_close`]'s close
    ///   exactly when `text` is a statement lead that no candidate continues or
    ///   fills an empty slot with, a close is offered, and (on the stream path)
    ///   the window after the close owes no more than the window without it;
    ///   the candidate buffer, sorted, holds the menu gathered at the resulting
    ///   frontier; consumes no source.
    /// - provides: the statement close at a statement keyword.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a statement that lost its `<-` before the next `run`,
    ///   and a `fork` that lost its `as` before the next `recv`, expose both
    ///   sides of the window: closing the first keeps the next statement whole,
    ///   and closing the second would owe its `as`, name and `;` again where
    ///   the keyword read as it stands owes less.
    /// - witness: `tests::acceptance::a_statement_keyword_starts_the_next_statement_1090`
    /// - witness: `tests::sweeps::dropped_tokens_recover_no_worse_than_the_record`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body gathers the candidate menu the clause walks to check it sorted"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn settle_statement(
        &mut self,
        state: &mut MeldState<'_>,
        lexeme: Lexeme,
        text: TokenText<'_>,
        labels: &LabelIds,
        ahead: Ahead<'_, '_>,
    )
    {
        if !matches!(lexeme, Lexeme::LowerWord) || !STATEMENT_LEADS.contains(&<&str>::from(text)) {
            return;
        }
        let frontier = state.admissibility_frontier();
        if self
            .candidates
            .iter()
            .any(|&mold| bool::from(state.would_continue_form(mold)))
        {
            return;
        }
        // A keyword that heads an expression in an empty slot (an inline
        // `run`) stays that expression.
        if !bool::from(frontier.head_operand)
            && self
                .candidates
                .iter()
                .any(|&mold| bool::from(state.admits_at(mold, &frontier)))
        {
            return;
        }
        self.gather_menu(labels, frontier.open, CandidateMenu::Declared);
        let Some(close) = state.statement_close(&self.candidates)
        else {
            self.gather(state, lexeme, text, labels);
            return;
        };
        let closes = match ahead {
            Ahead::Stream {
                tokens,
                index,
                source,
            } => {
                let mark = state.mark();
                let end =
                    self.mold_window(state, tokens, index, source, &mark, WindowBound::Unbounded);
                let standing = (end == WindowEnd::Molded)
                    .then(|| state.completion_delta(state.delta_since(&mark)));
                state.rollback_to(&mark);
                let mark = state.mark();
                state.close_statement(close);
                let bound = standing.map_or(WindowBound::Unbounded, WindowBound::Below);
                let end = self.mold_window(state, tokens, index, source, &mark, bound);
                let closed = (end == WindowEnd::Molded)
                    .then(|| state.completion_delta(state.delta_since(&mark)));
                state.rollback_to(&mark);
                match (standing, closed) {
                    (Some(standing), Some(closed)) => closed <= standing,
                    (_, closed) => closed.is_some(),
                }
            },
            Ahead::Nothing => true,
        };
        if closes {
            state.close_statement(close);
        }
        self.gather(state, lexeme, text, labels);
    }

    /// Mark the window being molded exposed when this token's declared menu
    /// can meet its opener's form: when a push of a menu mold can reach,
    /// below the nearest frontier, a frontier at or above the window's floor.
    ///
    /// The nearest frontier continues no mold of the menu — its successors of
    /// the label would have filled the fresh menu — so the menu meets a
    /// window class's members alike unless a push passes the nearest to one
    /// of their own frontiers below it.
    ///
    /// # Specification
    /// - requires: the token's declared menu was just gathered over `state`.
    /// - ensures: inside a window, sets `self.exposed` when
    ///   [`MeldState::settles_into`] the window's floor; outside one, changes
    ///   nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the differential witness reads every windowed tie of
    ///   the corpus, the drop matrix and the editor scenario: a declared menu
    ///   that met a member's own frontier unmarked shares a window whose
    ///   verdict differs from the member's dry run.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[spec(captures: before = self.exposed, ensures: |()| self.window_floor.is_some() || self.exposed == before)]
    fn note_declared_menu(
        &mut self,
        state: &MeldState<'_>,
    )
    {
        if let Some(floor) = self.window_floor
            && bool::from(state.settles_into(floor))
        {
            self.exposed = true;
        }
    }

    /// Widen a **reserved uppercase word**'s menu to its lexical class's
    /// generic labels when its own tile cannot mold at this position.
    ///
    /// The `UPPER_KEYWORDS` reservation is a disambiguation preference, never
    /// a ban on declaration names: at a type slot the reserved tile (`Unknown`
    /// the primitive type) molds and the generic labels stay out, so the
    /// primitive/type-identifier tie the reservation exists to prevent never
    /// forms. But the reservation also fires at slots that admit ONLY
    /// `constructor` / `type_identifier` — a `theory` block's name, a `sort`
    /// member's colour, a `data` head — where the reserved tile is
    /// structurally inadmissible, and there it repaired the whole declaration
    /// (`theory Unknown` molded nothing). When no gathered
    /// candidate is admissible at the live frontier, the molder re-gathers
    /// with the class's generic labels appended; the reserved candidates stay
    /// in the menu so the last-resort path still flags the exact obligation
    /// when nothing admissible exists either way.
    ///
    /// # Specification
    /// - requires: the reserved menu of a token of `lexeme` spelled `text` was
    ///   already gathered into `self.candidates`.
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
    /// - witness: `tests::acceptance::a_theory_block_may_be_named_with_a_primitive_type_spelling`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "bounded: walks the token's candidate menu, which the gather that calls it has just built and sorted"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_reserved_fallback(
        &mut self,
        state: &MeldState<'_>,
        lexeme: Lexeme,
        text: TokenText<'_>,
        open: Option<MoldId>,
    )
    {
        if !matches!(lexeme, Lexeme::UpperWord) || !UPPER_KEYWORDS.contains(&<&str>::from(text)) {
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
        let generic = LabelIds::resolve(
            self.pbg,
            &RESERVED_FALLBACK_LABELS.map(CandidateLabel::from),
        );
        self.gather_labels(generic.as_slice(), open, CandidateMenu::Fresh);
        if self.candidates.is_empty() {
            self.gather_labels(generic.as_slice(), open, CandidateMenu::Declared);
            self.note_declared_menu(state);
        }
        self.candidates.extend_from_slice(&reserved);
        self.candidates.sort_unstable();
        self.candidates.dedup();
    }

    /// Empty a **reserved lowercase word**'s menu when it stands in a
    /// declaration's empty slot and no mold of it fits there: the word is a
    /// keyword out of place, and it stands in the slot as an unmolded token.
    ///
    /// Two shapes qualify. `sort M : type;` in a `theory` block writes the
    /// keyword `type` where the member's classifier belongs. `type` molds only
    /// as a module's type component, a member form that no open frontier
    /// continues and the classifier slot does not admit, so the full-menu
    /// fallback pushed it anyway: the push ghost-closed the `theory` block
    /// before the member's classifier and re-read the rest of the source as a
    /// stray form. `def mu : Integer ;` and `oper mu : … ;` write the keyword
    /// `mu` where the declaration's name belongs, in the slot the form's
    /// keyword tile has just opened; `mu` molds only as the recursive type's
    /// opener, which that slot does not admit, and the fallback pushed it
    /// there: the rest of the declaration was read inside `mu`'s form and the
    /// parse owed a missing closer at the end of the source (#722). `drop`,
    /// `dup` and `send` open session expressions, which the slot's sort does
    /// admit, and `oper drop : … ;` or `rule drop : … ;` read the rest of the
    /// declaration inside `drop(…)` the same way (#2460): the slot keeps only
    /// an item-position mold of the keyword, as `mobile type Report` writes
    /// one. With the menu empty the molder takes the unmolded path instead:
    /// the keyword becomes grout over its own bytes in its slot, and the
    /// parse's first obligation is the keyword's. In a member the declaration
    /// stays whole and the keyword is the one obligation; a top-level
    /// definition whose name is grout also owes its name tile, inside the same
    /// declaration. Either way the declarations after it keep their own
    /// tiles. This is the stray mid's recovery one keyword later: a stray mid
    /// flags its missing head in place rather than reading the source around
    /// it anew.
    ///
    /// The rule is held to those shapes, and each guard is measured: over
    /// the drop harness, widening it to any open slot, to a slot after an
    /// operand, to a non-declaration form's slot, to a declaration slot of
    /// another sort, to the empty slot after any tile of a declaration (a
    /// `:` or a module's name, not only a keyword tile) or to a keyword
    /// opening an expression form in any other slot each made some variant
    /// owe more obligations than the record, because there the keyword is
    /// usually written right and a delimiter before it is missing. An
    /// item-position declaration head is admitted at every slot (the
    /// [`MeldState::admits_at`] exemption that keeps top-level declarations
    /// reachable), so `def` after an unfinished declaration still opens the
    /// next one. _Reversal:_ a slot of another sort whose keyword recovery
    /// the harness measures as better joins the rule.
    ///
    /// # Specification
    /// - requires: the token's menu, `lexeme` spelled `text`, was gathered into
    ///   `self.candidates`.
    /// - ensures: empties `self.candidates` exactly when `text` is a reserved
    ///   lowercase keyword, the live frontier is an open slot holding no
    ///   operand, its nearest open form is of item position, and either the
    ///   slot is of [`Sort::Type`] and every candidate is a declaration head
    ///   that slot does not admit, or the form's frontier tile is a keyword and
    ///   the slope head ([`MeldState::head_is_frontier`]) and the slot admits
    ///   no candidate of item position; leaves it unchanged otherwise.
    /// - provides: the keyword-out-of-place half of the candidate menu.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the keyword `type` in a `theory` member's classifier
    ///   slot owes exactly one obligation, at the keyword, and keeps the member
    ///   and the block whole; the keywords `mu`, `drop`, `dup` and `send` in a
    ///   definition's, an operation's or a rule's name slot owe their first
    ///   obligation at the keyword and none in the declaration after it; `Type`
    ///   and a name that is no keyword owe none, and `mobile type` in a
    ///   signature keeps its member. The drop harness's records, a differential
    ///   measurement rather than a witness, hold every corpus variant to no
    ///   more obligations than before.
    /// - witness: `tests::acceptance::a_keyword_in_a_classifier_slot_stands_there_unmolded`
    /// - witness: `tests::acceptance::a_keyword_in_a_name_slot_stands_there_unmolded_722`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "bounded: walks the token's candidate menu, which the gather that calls it has just built and sorted"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn drop_stray_keyword(
        &mut self,
        state: &MeldState<'_>,
        lexeme: Lexeme,
        text: TokenText<'_>,
    )
    {
        if !matches!(lexeme, Lexeme::LowerWord) || !KEYWORDS.contains(&<&str>::from(text)) {
            return;
        }
        let frontier = state.admissibility_frontier();
        if bool::from(frontier.boundary)
            || bool::from(frontier.head_operand)
            || self.candidates.is_empty()
        {
            return;
        }
        let pbg = self.pbg;
        let classifier_slot = frontier.expected == Sort::Type
            && frontier.open.is_some_and(|open| {
                pbg.mold(open)
                    .is_ok_and(|def| matches!(def.sort, Sort::Item | Sort::ModuleMember))
            });
        // A declaration's name slot: the slot an item-position form's keyword
        // tile (`def`, `oper`) has just opened, empty. A keyword the slot
        // admits no item-position mold of is a name written as a keyword
        // (#722, #2460), where the full-menu fallback, or an expression form
        // such as `drop`'s that the slot's sort admits, would open the
        // keyword's own form and read the rest of the declaration inside it.
        // An admitted item-position mold stays: `mobile type Report` writes a
        // member's keyword there, rightly.
        let name_slot = frontier.open.is_some_and(|open| {
            pbg.mold(open).is_ok_and(|def| {
                matches!(def.sort, Sort::Item | Sort::ModuleMember) && KEYWORDS.contains(&def.label)
            })
        }) && bool::from(state.head_is_frontier());
        let stray = (classifier_slot
            && self.candidates.iter().all(|&mold| {
                !bool::from(state.admits_at(mold, &frontier))
                    && bool::from(declaration_head(pbg, mold))
            }))
            || (name_slot
                && self.candidates.iter().all(|&mold| {
                    !bool::from(state.admits_at(mold, &frontier))
                        || !pbg
                            .mold(mold)
                            .is_ok_and(|def| matches!(def.sort, Sort::Item | Sort::ModuleMember))
                }));
        if stray {
            self.candidates.clear();
        }
    }

    /// Gather the candidate molds for a token's `labels`, from the fresh-slot
    /// menu plus the open form's `≐`-successors ([`CandidateMenu::Fresh`]) or
    /// the full declared menu ([`CandidateMenu::Declared`]).
    ///
    /// # Specification
    /// - requires: `labels` are a token's declared labels, by number.
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
    /// - witness: `tests::acceptance::a_theory_block_may_be_named_with_a_primitive_type_spelling`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body gathers and sorts the same candidate buffer"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_menu(
        &mut self,
        labels: &LabelIds,
        open: Option<MoldId>,
        menu: CandidateMenu,
    )
    {
        self.candidates.clear();
        self.gather_labels(labels.as_slice(), open, menu);
    }

    /// Gather the candidate molds for `labels`, from the fresh-slot menu plus
    /// the open form's `≐`-successors ([`CandidateMenu::Fresh`]) or the full
    /// declared menu ([`CandidateMenu::Declared`]). The buffer is NOT cleared:
    /// callers stage menus (the reserved-word fallback unions its widened
    /// menu over the reserved one).
    ///
    /// # Specification
    /// - requires: `labels` are the numbers of the current token's labels.
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
    /// - witness: `tests::acceptance::a_theory_block_may_be_named_with_a_primitive_type_spelling`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body gathers and sorts the same candidate buffer"
        )
    )]
    #[spec(ensures: |_| self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right))]
    fn gather_labels(
        &mut self,
        labels: &[LabelId],
        open: Option<MoldId>,
        menu: CandidateMenu,
    )
    {
        for &label in labels {
            let candidates = match menu {
                CandidateMenu::Fresh => self.pbg.label_fresh_candidates(label),
                CandidateMenu::Declared => self.pbg.label_candidates(label),
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `labels` holds one token's candidate labels, at most `LABEL_CAPACITY`"
        )
    )]
    #[spec(captures: before = self.candidates.len(), ensures: |_| self.candidates.get(before ..).is_some_and(|tail| tail.iter().all(|right| self.pbg.adjacencies().binary_search(&(open, *right)).is_ok() && self.pbg.mold_label(*right).is_some_and(|label| labels.contains(&label)))))]
    fn push_form_successors(
        &mut self,
        labels: &[LabelId],
        open: MoldId,
    )
    {
        let pbg = self.pbg;
        for &(_open, right) in pbg.mold_successors(open) {
            if pbg
                .mold_label(right)
                .is_some_and(|label| labels.contains(&label))
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
    ///   key; the sort matches when it is the frontier's expected sort, or the
    ///   candidate opens a declaration at the top level; reads `state` without
    ///   changing it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ranks are the full key's; a floor above a found
    ///   key is what lets [`least_candidates`](Self::least_candidates) skip a
    ///   candidate's dry-run. A floor carrying a nonempty delta, or ranks that
    ///   differ from the key's, changes which candidates are kept; a top-level
    ///   bind statement read as the expression `run` leaves its `<-` stranded.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    /// - witness: `tests::acceptance::bind_statement_uses_run_keyword`
    #[spec(ensures: |ret| bool::from(ret.delta.is_empty()))]
    fn floor_key(
        &self,
        state: &MeldState<'_>,
        mold: MoldId,
        frontier: &Frontier,
    ) -> CandidateKey
    {
        let continuation = CandidateRank::from(!bool::from(state.would_continue_form(mold)));
        let mold_sort = self.pbg.mold(mold).map_or(Sort::Item, |def| def.sort);
        let sort_rank = CandidateRank::from(
            mold_sort != frontier.expected
                && !(bool::from(frontier.boundary) && bool::from(declaration_head(self.pbg, mold))),
        );
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
    ///   leakage, and the unmolded class exposes the delta. The clause reads
    ///   the frontier cache's top and the obligation count;
    ///   [`MeldState::rollback_to`]'s clause checks the rest of the restore.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    #[spec(captures: before = (state.open_form_mold(), state.obligations().len()), ensures: |_| state.open_form_mold() == before.0 && state.obligations().len() == before.1)]
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
    /// ties are exactly those of scoring every candidate. Through the tables
    /// a candidate whose push class an earlier candidate dry-ran takes that
    /// delta rather than its own dry run.
    ///
    /// # Specification
    /// - requires: `self.eligible` holds distinct molds in ascending order.
    /// - ensures: `self.tied` holds, in ascending order, exactly the eligible
    ///   candidates whose [`CandidateKey`] is the least among all eligible
    ///   candidates; it is empty exactly when none is eligible; the melder is
    ///   restored exactly; through the tables, `self.chain` is the state's
    ///   settle chain.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — menus whose least key has an empty delta, a nonempty
    ///   delta, and ties across one floor; the chosen molds and the corpus
    ///   moldings expose a skipped candidate that could have tied or won, and
    ///   the differential witness a push class whose members flag differently.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body ranks every eligible candidate and pushes each tie; the clause walks the ties, searching the eligible list"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `pushes` holds the push classes of one decision's candidates, a buffer reused across decisions"
        )
    )]
    #[spec(captures: before = state.obligations().len(), ensures: |_| state.obligations().len() == before && self.tied.iter().all(|mold| self.eligible.binary_search(mold).is_ok()) && self.tied.is_empty() == self.eligible.is_empty() && self.tied.iter().zip(self.tied.iter().skip(1)).all(|(left, right)| left < right))]
    fn least_candidates(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
        frontier: &Frontier,
        procedure: Procedure,
    )
    {
        self.ranked.clear();
        for slot in 0 .. self.eligible.len() {
            let Some(&mold) = self.eligible.get(slot)
            else {
                break;
            };
            let floor = self.floor_key(state, mold, frontier);
            self.ranked.push((floor, mold));
        }
        if procedure == Procedure::Tables {
            // Candidates share a push only when their observation classes
            // agree; with every class distinct, each is dry-run alone.
            self.observed.clear();
            for &(_, mold) in &self.ranked {
                if let Ok(observation) = self.pbg.observation(mold) {
                    self.observed.push(observation);
                }
            }
            self.observed.sort_unstable();
            if self
                .observed
                .windows(2)
                .any(|pair| matches!(pair, [left, right] if left == right))
            {
                self.chain.read(self.pbg, state);
            }
            else {
                self.chain.unkey();
            }
        }
        self.pushes.clear();
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
                let delta = match procedure {
                    Procedure::DryRuns => Self::push_delta(state, mold, text),
                    Procedure::Tables => {
                        let class = self.chain.key(self.pbg, mold);
                        if let Some(&(_, delta)) =
                            self.pushes.iter().find(|&&(held, _)| held == class)
                        {
                            delta
                        }
                        else {
                            let delta = Self::push_delta(state, mold, text);
                            self.pushes.push((class, delta));
                            delta
                        }
                    },
                };
                let key = CandidateKey { delta, ..floor };
                match least {
                    Some(found) if key > found => {},
                    Some(found) if key == found => self.tied.push(mold),
                    _ => {
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
    ///   completion deltas distinguish their scoring boundaries. The clause
    ///   reads the frontier cache's top and the obligation count;
    ///   [`MeldState::rollback_to`]'s clause checks the rest of the restore.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    #[spec(captures: before = (state.open_form_mold(), state.obligations().len()), ensures: |_| state.open_form_mold() == before.0 && state.obligations().len() == before.1)]
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
    /// stand-in for the lookahead the single-token path cannot run. Inside a
    /// window `ahead` names the stream, and a key tie first drops the
    /// candidates the next significant token cannot follow
    /// ([`drop_refuted`](Self::drop_refuted)): a list's separator before its
    /// closer is the trailing one, never the one that opens another element.
    /// The molder's [`MoldVerdicts`] mode says how the verdict is reached;
    /// a differential molder reaches it both ways and pushes the dry runs'.
    ///
    /// # Specification
    /// - requires: the candidate menu is canonical and belongs to this grammar.
    /// - ensures: selects a menu member, minimizing admissible key, then, when
    ///   `ahead` names a stream, keeping only what the next significant token
    ///   can follow unless it can follow none, then completion then identity;
    ///   an empty menu yields none. A differential molder counts the decision
    ///   as a disagreement when the two procedures admit different menus or
    ///   choose different molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, sole and ambiguous menus, including a
    ///   no-admissible fallback, expose the selected mold and final repairs.
    ///   Dropped candidates, choosing outside the menu or changing priority
    ///   changes those observations; dry-run state is compared byte-for-byte. A
    ///   call's separator before its closer takes the lesser comma read alone
    ///   and the trailing one when the window names the closer after it.
    /// - witness: `mold::tests::dry_runs_restore_exact_state`
    /// - witness: `mold::tests::picks_the_obligation_minimum_mold`
    /// - witness: `mold::tests::a_window_reads_the_token_after_a_tied_separator`
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the procedure the body dispatches to walks the same candidate menu to filter it by admissibility"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), ensures: |ret| ret.map_or_else(|| self.candidates.is_empty(), |mold| self.candidates.contains(&mold)))]
    fn choose(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
        ahead: Ahead<'_, '_>,
    ) -> Option<MoldId>
    {
        let procedure = match self.verdicts {
            MoldVerdicts::Tables => Procedure::Tables,
            MoldVerdicts::DryRuns => Procedure::DryRuns,
            MoldVerdicts::Differential => return self.choose_both(state, text, ahead),
        };
        self.choose_by(state, text, ahead, procedure)
    }

    /// Choose as [`choose`](Self::choose) does by both procedures, counting a
    /// disagreement, and keep the dry runs' verdict.
    ///
    /// # Specification
    /// - requires: as [`choose`](Self::choose).
    /// - ensures: the dry runs' choice; the disagreement count grows by one
    ///   when the two procedures admit different menus or choose different
    ///   molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the differential witness reads every decision of the
    ///   corpus, the drop matrix and the editor scenario through this
    ///   comparison; a comparison that missed the menus or the choice would let
    ///   a table verdict differ unseen.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cold]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same candidate menu to filter it by admissibility, once per procedure"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = self.disagreements, ensures: |ret| self.disagreements >= before && ret.map_or_else(|| self.candidates.is_empty(), |mold| self.candidates.contains(&mold)))]
    fn choose_both(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
        ahead: Ahead<'_, '_>,
    ) -> Option<MoldId>
    {
        let oracle = self.choose_by(state, text, ahead, Procedure::DryRuns);
        let admitted = self.eligible.clone();
        let table = self.choose_by(state, text, ahead, Procedure::Tables);
        if table != oracle || self.eligible != admitted {
            self.disagreements.0 = self.disagreements.0.saturating_add(1);
        }
        oracle
    }

    /// Choose as [`choose`](Self::choose) does, through `procedure`.
    ///
    /// # Specification
    /// - requires: as [`choose`](Self::choose).
    /// - ensures: as [`choose`](Self::choose), for either procedure; the
    ///   admitted menu is left in `self.eligible`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`choose`](Self::choose); the differential witness
    ///   reads the two procedures against each other.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same candidate menu to filter it by admissibility"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `completions` holds the push classes of one decision's ties, a buffer reused across decisions"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), ensures: |ret| ret.map_or_else(|| self.candidates.is_empty(), |mold| self.candidates.contains(&mold)))]
    fn choose_by(
        &mut self,
        state: &mut MeldState<'_>,
        text: TokenText<'_>,
        ahead: Ahead<'_, '_>,
        procedure: Procedure,
    ) -> Option<MoldId>
    {
        // Fast path: the pre-filter usually collapses the menu to
        // a lone admissible candidate, which needs no dry-run at all — the whole
        // point of the filter, and what keeps the batch cost inside budget. The
        // admissibility frontier is computed once and reused for every candidate.
        let frontier = state.admissibility_frontier();
        self.admit(state, &frontier, procedure, None);
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
        self.least_candidates(state, text, &frontier, procedure);
        if self.tied.len() <= 1 {
            return self.tied.first().copied();
        }
        // Inside a window the next token is known: a tied candidate it cannot
        // follow drops before any finalize runs.
        if let Ahead::Stream {
            tokens,
            index,
            source,
        } = ahead
        {
            let mut tied = core::mem::take(&mut self.tied);
            self.drop_refuted(&mut tied, tokens, index, source);
            self.tied = tied;
            if let [sole] = *self.tied.as_slice() {
                return Some(sole);
            }
        }
        // Pass two: break the key-tie by the single-token completion penalty,
        // keeping the smaller `MoldId` on a further tie (ascending visitation).
        // An empty completion is the least there is, so no later tie can beat
        // it. Through the tables a push class's completion is read once: the
        // chain the classes are keyed over is the one `least_candidates` read
        // from this unchanged state.
        self.completions.clear();
        let mut best: Option<(Delta, MoldId)> = None;
        for slot in 0 .. self.tied.len() {
            let Some(&mold) = self.tied.get(slot)
            else {
                break;
            };
            let completion = match procedure {
                Procedure::DryRuns => Self::completion(state, mold, text),
                Procedure::Tables => {
                    let class = self.chain.key(self.pbg, mold);
                    if let Some(&(_, completion)) =
                        self.completions.iter().find(|&&(held, _)| held == class)
                    {
                        completion
                    }
                    else {
                        let completion = Self::completion(state, mold, text);
                        self.completions.push((class, completion));
                        completion
                    }
                },
            };
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

    /// Admit the gathered menu into `self.eligible` through `procedure`: each
    /// candidate [`MeldState::admits_at`] admits, or the tables' [`Admission`]
    /// does, which answers alike; on the stream, only the direct rule binder
    /// the tokens after it bear out, and of a `(` read both as an expression
    /// and as a type only the reading the token past its group bears out
    /// ([`settle_telescope_arrow`](Self::settle_telescope_arrow)). The tables
    /// compose an admission context only for a menu wider than
    /// [`ADMISSION_MENU`]: a narrower one is admitted candidate by candidate,
    /// which costs less than composing it.
    ///
    /// # Specification
    /// - requires: `frontier` is `state`'s admissibility frontier; `binder`
    ///   names the stream and the token's index when the token is molded on the
    ///   stream.
    /// - ensures: `self.eligible` holds, in menu order, exactly the candidates
    ///   `admits_at` admits at `frontier` and, with `binder`, whose
    ///   direct-binder and parenthesized readings the stream bears out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the differential witness compares the two procedures'
    ///   admitted menus at every decision.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same candidate menu to filter it by admissibility"
        )
    )]
    #[spec(ensures: |()| self.eligible.iter().all(|mold| self.candidates.contains(mold)))]
    fn admit(
        &mut self,
        state: &MeldState<'_>,
        frontier: &Frontier,
        procedure: Procedure,
        binder: Option<(&[Token], TokenIndex, &SourceFragment<'_>)>,
    )
    {
        self.eligible.clear();
        let mut admission = (procedure == Procedure::Tables
            && self.candidates.len() > ADMISSION_MENU)
            .then(|| Admission::new(self.pbg, frontier));
        for slot in 0 .. self.candidates.len() {
            let Some(&mold) = self.candidates.get(slot)
            else {
                break;
            };
            let admitted = admission.as_mut().map_or_else(
                || state.admits_at(mold, frontier),
                |admission| admission.admits(mold),
            );
            let kept = match binder {
                Some((tokens, index, source)) => bool::from(
                    self.direct_rule_binder_admits(mold, frontier, admitted, tokens, index, source),
                ),
                None => bool::from(admitted),
            };
            if kept {
                self.eligible.push(mold);
            }
        }
        if let Some((tokens, index, source)) = binder {
            self.settle_telescope_arrow(state, frontier, tokens, index, source);
        }
    }

    /// Read a `(` a fresh expression slot admits as a parenthesized
    /// expression as a parenthesized type instead when `=>` is the next
    /// significant token past the group's `)`: the group is then the domain
    /// list of a value-function type, `(y : A, P) => B`, which stands where a
    /// value is read as `A => B` does. An ascription `(e : T)` never goes on
    /// with `=>`, and a handler's clause arrow reads only inside its `with`
    /// braces, so the token past the group decides. An empty group stays the
    /// unit: a domain list holds at least one type.
    ///
    /// # Specification
    /// - requires: `frontier` is `state`'s admissibility frontier; `tokens` is
    ///   the labeler output for `source`; `index` names the current token.
    /// - ensures: when the slot is a fresh expression slot, a parenthesized
    ///   expression's `(` is eligible and the group closes before `=>`, the
    ///   eligible parenthesized expression's molds give way to the
    ///   parenthesized type's molds a type slot there admits, in menu order;
    ///   otherwise, and when no such type mold is admitted, `self.eligible` is
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a telescope, a bare domain list, a tuple, an
    ///   ascription, the unit and a group left open on the stream expose the
    ///   decision. Keeping the expression before `=>` reads the domain list as
    ///   a tuple and refuses it as a type, and taking the type elsewhere reads
    ///   an ascription as a binder.
    /// - witness: `tests::grammar::every_type_operator_spelling_reads_cleanly`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the menu to classify its two parenthesized readings"
        )
    )]
    #[spec(ensures: |()| self.eligible.iter().all(|mold| self.candidates.contains(mold)))]
    fn settle_telescope_arrow(
        &mut self,
        state: &MeldState<'_>,
        frontier: &Frontier,
        tokens: &[Token],
        index: TokenIndex,
        source: &SourceFragment<'_>,
    )
    {
        if frontier.expected != Sort::Expression || bool::from(frontier.head_operand) {
            return;
        }
        let pbg = &self.pbg;
        let reading = |mold: MoldId| {
            let opens = pbg.mold(mold).is_ok_and(|def| def.label == "(");
            let rule = pbg
                .rule_of(mold)
                .ok()
                .map(gandr_surface_grammar::Rule::name);
            match rule {
                Some(name) if opens && name == PARENTHESIZED_TYPE => Some(Sort::Type),
                Some(name) if opens && name == PARENTHESIZED_EXPRESSION => Some(Sort::Expression),
                Some(_) | None => None,
            }
        };
        if !self
            .eligible
            .iter()
            .any(|&mold| reading(mold) == Some(Sort::Expression))
            || group_close(tokens, index, source) != GroupClose::Arrow
        {
            return;
        }
        let typed = Frontier {
            expected: Sort::Type,
            ..*frontier
        };
        let admitted = |mold: MoldId| {
            reading(mold) == Some(Sort::Type) && bool::from(state.admits_at(mold, &typed))
        };
        if !self.candidates.iter().any(|&mold| admitted(mold)) {
            return;
        }
        let mut kept = core::mem::take(&mut self.eligible);
        kept.retain(|&mold| reading(mold) != Some(Sort::Expression));
        kept.extend(
            self.candidates
                .iter()
                .copied()
                .filter(|&mold| admitted(mold)),
        );
        kept.sort_unstable();
        kept.dedup();
        self.eligible = kept;
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
    ///   the current `(` token; `admitted` is whether the frontier admits
    ///   `mold`.
    /// - ensures: returns `true` only for an admitted mold, and for the direct
    ///   circuit binder opener only when the next significant tokens have its
    ///   binder prefix.
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
    #[spec(ensures: |ret| !bool::from(ret) || bool::from(admitted))]
    fn direct_rule_binder_admits(
        &self,
        mold: MoldId,
        frontier: &Frontier,
        admitted: MoldAdmissibility,
        tokens: &[Token],
        index: TokenIndex,
        source: &SourceFragment<'_>,
    ) -> DirectRuleBinderAdmission
    {
        if !bool::from(admitted) {
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
    /// a bounded greedy lookahead instead. First the next significant token
    /// prunes the tie: a tied candidate whose hole the token cannot begin, or
    /// whose next symbol is a tile of its own form that the token cannot be,
    /// is dropped ([`drop_refuted`](Self::drop_refuted)), and of openers the
    /// grammar reads alike only the least remains
    /// ([`drop_interchangeable`](Self::drop_interchangeable)); a lone survivor
    /// wins without a window, and so does the one opener the token continues
    /// inside its own form when every other survivor is a one-tile form
    /// ([`continued_opener`](Self::continued_opener)), and the least of
    /// survivors that all end a form of one sort and precedence before the
    /// token ([`complete_alike`](Self::complete_alike)). Each remaining
    /// candidate is dry-run and its window molded greedily by
    /// [`choose`](Self::choose) (which IS completion aware and prunes its
    /// own ties by the token after each, so the window itself molds well),
    /// and the reading whose window closes with the fewest obligations wins
    /// — deterministically, keeping the smaller [`MoldId`] on an exact
    /// window tie. When the local minimum is unique the fast path returns
    /// it directly. Through the tables the openers of one window class share
    /// the least member's window (`crate::tables`). A differential molder
    /// decides both ways and pushes the dry runs' verdict.
    ///
    /// # Specification
    /// - requires: candidates are canonical for the current token.
    /// - ensures: returns no choice for an absent token or empty menu;
    ///   otherwise selects a grammar mold by bounded lookahead. A differential
    ///   molder counts the decision as a disagreement when the two procedures
    ///   admit different menus or choose different molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — complete shared-prefix families, exhausted input and
    ///   an empty menu expose selection and absence. Losing a tied opener or
    ///   looking beyond the bounded window changes the committed form; dry-run
    ///   mutations change the checkpoint bytes.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    /// - witness: `mold::tests::lookahead_window_stops_after_eight_significant_tokens`
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the procedure the body dispatches to walks the same candidate menu to filter it by admissibility"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = (self.candidates.len(), tokens.get(index.0).is_some()), ensures: |ret| ret.is_some() == (before.1 && before.0 > 0) && ret.is_none_or(|mold| self.pbg.mold(mold).is_ok()))]
    fn choose_stream<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        index: TokenIndex,
        source: &'src SourceFragment<'src>,
    ) -> Option<MoldId>
    {
        let procedure = match self.verdicts {
            MoldVerdicts::Tables => Procedure::Tables,
            MoldVerdicts::DryRuns => Procedure::DryRuns,
            MoldVerdicts::Differential => {
                return self.choose_stream_both(state, tokens, index, source);
            },
        };
        self.choose_stream_by(state, tokens, index, source, procedure)
    }

    /// Choose as [`choose_stream`](Self::choose_stream) does by both
    /// procedures, counting a disagreement, and keep the dry runs' verdict.
    ///
    /// # Specification
    /// - requires: as [`choose_stream`](Self::choose_stream).
    /// - ensures: the dry runs' choice, the menu as it was given; the
    ///   disagreement count grows by one when the two procedures admit
    ///   different menus or choose different molds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the differential witness reads every decision of the
    ///   corpus, the drop matrix and the editor scenario through this
    ///   comparison; a comparison that missed the menus, the choice, or a menu
    ///   one procedure's windows gathered over would let a table verdict differ
    ///   unseen.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cold]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body copies the candidate menu and walks it to filter it by admissibility, once per procedure"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = (self.candidates.len(), tokens.get(index.0).is_some(), self.disagreements), ensures: |ret| self.disagreements >= before.2 && ret.is_some() == (before.1 && before.0 > 0) && ret.is_none_or(|mold| self.pbg.mold(mold).is_ok()))]
    fn choose_stream_both<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        index: TokenIndex,
        source: &'src SourceFragment<'src>,
    ) -> Option<MoldId>
    {
        // The windows gather over the menu, so each procedure starts from a
        // copy of it; the admitted menus are compared before either runs.
        let menu = self.candidates.clone();
        let frontier = state.admissibility_frontier();
        let binder = Some((tokens, index, source));
        self.admit(state, &frontier, Procedure::DryRuns, binder);
        let admitted = self.eligible.clone();
        self.admit(state, &frontier, Procedure::Tables, binder);
        let admitted_alike = self.eligible == admitted;
        let oracle = self.choose_stream_by(state, tokens, index, source, Procedure::DryRuns);
        self.candidates.clone_from(&menu);
        let table = self.choose_stream_by(state, tokens, index, source, Procedure::Tables);
        self.candidates = menu;
        if table != oracle || !admitted_alike {
            self.disagreements.0 = self.disagreements.0.saturating_add(1);
        }
        oracle
    }

    /// Choose as [`choose_stream`](Self::choose_stream) does, through
    /// `procedure`.
    ///
    /// # Specification
    /// - requires: as [`choose_stream`](Self::choose_stream).
    /// - ensures: as [`choose_stream`](Self::choose_stream), for either
    ///   procedure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`choose_stream`](Self::choose_stream); the
    ///   differential witness reads the two procedures against each other.
    /// - witness: `tests::sweeps::table_verdicts_equal_dry_run_verdicts`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same candidate menu to filter it by admissibility"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `windowed` holds the opener classes of one decision, a buffer reused across decisions"
        )
    )]
    #[spec(requires: self.candidates.iter().zip(self.candidates.iter().skip(1)).all(|(left, right)| left < right), captures: before = (self.candidates.len(), tokens.get(index.0).is_some()), ensures: |ret| ret.is_some() == (before.1 && before.0 > 0) && ret.is_none_or(|mold| self.pbg.mold(mold).is_ok()))]
    fn choose_stream_by<'src>(
        &mut self,
        state: &mut MeldState<'_>,
        tokens: &[Token],
        index: TokenIndex,
        source: &'src SourceFragment<'src>,
        procedure: Procedure,
    ) -> Option<MoldId>
    {
        let token = *tokens.get(usize::from(index))?;
        let slice = token.text(source);
        let text = TokenText::from(AsRef::<str>::as_ref(&slice));
        // `self.candidates` is already gathered by the caller for this token.
        // Fast path: a lone admissible candidate needs no dry-run.
        // The admissibility frontier is computed once and reused per candidate.
        let frontier = state.admissibility_frontier();
        self.admit(state, &frontier, procedure, Some((tokens, index, source)));
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
        self.least_candidates(state, text, &frontier, procedure);
        if self.tied.len() <= 1 {
            return self.tied.first().copied();
        }
        core::mem::swap(&mut self.tied, &mut self.openers);
        // A tied opener the next significant token cannot follow is refuted
        // before any window runs; a lone survivor needs no window.
        let mut openers = core::mem::take(&mut self.openers);
        self.drop_refuted(&mut openers, tokens, index, source);
        self.openers = openers;
        // Interchangeable openers mold every later token alike, so their
        // windows tie exactly and the least would win: only it remains.
        self.drop_interchangeable();
        if let [sole] = *self.openers.as_slice() {
            return Some(sole);
        }
        // An opener the next token continues inside its own form beats the
        // one-tile forms the token could only follow from outside them, and of
        // readings that all end alike before the token the least wins.
        if let Some(labels) =
            next_labels(tokens, index, source).map(|labels| LabelIds::resolve(self.pbg, &labels))
            && let Some(mold) = self
                .continued_opener(labels.as_slice())
                .or_else(|| self.complete_alike(labels.as_slice()))
        {
            return Some(mold);
        }
        // Through the tables, each opener's window class: its push key over
        // the chain `least_candidates` read from this state, and its window
        // signature over the window's tokens and the one after them, which
        // the window's last tie reads. Openers share a window only when their
        // push keys agree, so a tie whose keys are all distinct molds every
        // window as the dry runs do and signs none.
        let mut classed = false;
        if procedure == Procedure::Tables {
            self.opener_keys.clear();
            for slot in 0 .. self.openers.len() {
                if let Some(&opener) = self.openers.get(slot) {
                    self.opener_keys.push(self.chain.key(self.pbg, opener));
                }
            }
            self.shared_keys.clone_from(&self.opener_keys);
            self.shared_keys.sort_unstable();
            classed = self
                .shared_keys
                .windows(2)
                .any(|pair| matches!(pair, [left, right] if left == right));
        }
        if classed {
            let mut window = [LabelIds::new(); LOOKAHEAD + 1];
            let mut positions = 0_usize;
            let mut cursor = index;
            while let Some((next, _token)) = next_significant(tokens, cursor)
                && let Some(labels) = next_labels(tokens, cursor, source)
                && let Some(slot) = window.get_mut(positions)
            {
                *slot = LabelIds::resolve(self.pbg, &labels);
                positions = positions.saturating_add(1);
                cursor = next;
            }
            self.windows.classify(
                self.pbg,
                &self.openers,
                window.get(.. positions).unwrap_or(&[]),
                &mut self.opener_classes,
            );
            self.windowed.clear();
        }
        // A shared-prefix family: break the tie by a bounded greedy lookahead.
        // Windows run in ascending MoldId order and a later opener wins only
        // with a strictly smaller delta, so each window after the first is
        // bounded by the best delta so far: a window delta never shrinks as
        // tokens are molded, and one that reaches the bound cannot win. A
        // class's least member molds first; a later member's window is the
        // same window unless the first gathered a whole declared menu, so it
        // ties or is dominated and cannot win.
        let start = TokenIndex::from(usize::from(index).saturating_add(1));
        let mut best: Option<(Delta, MoldId)> = None;
        for slot in 0 .. self.openers.len() {
            let Some(&mold) = self.openers.get(slot)
            else {
                break;
            };
            let class = if classed {
                self.opener_keys
                    .get(slot)
                    .copied()
                    .zip(self.opener_classes.get(slot).copied())
            }
            else {
                None
            };
            let first_of_class = match class {
                Some((key, signature)) => {
                    match self
                        .windowed
                        .iter()
                        .find(|&&(held, seen, _)| (held, seen) == (key, signature))
                    {
                        Some(&(_, _, WindowRun::Shared)) => continue,
                        Some(&(_, _, WindowRun::Exposed)) => false,
                        None => true,
                    }
                },
                None => false,
            };
            self.exposed = false;
            let mark = state.mark();
            state.push_text(mold, TileText::from(text));
            // The opener's cell is the slope's top: everything at or above
            // it is the opener's form or the window's. Only a class's first
            // window is recorded, so only it watches for exposure.
            self.window_floor = first_of_class
                .then(|| SlopeHeight::from(usize::from(state.slope_height()).saturating_sub(1)));
            let bound = best.map_or(WindowBound::Unbounded, |(delta, _mold)| {
                WindowBound::Below(delta)
            });
            let end = self.mold_window(state, tokens, start, source, &mark, bound);
            self.window_floor = None;
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
            if first_of_class && let Some((key, signature)) = class {
                let run = if self.exposed {
                    WindowRun::Exposed
                }
                else {
                    WindowRun::Shared
                };
                self.windowed.push((key, signature, run));
            }
        }
        best.map(|(_, mold)| mold)
    }

    /// Mold the tokens from `start` until [`LOOKAHEAD`] non-space tokens are
    /// molded, for a window.
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
    /// - requires: `start` is within the token stream or its end sentinel;
    ///   `mark` was taken from `state` before the tied opener was pushed.
    /// - ensures: molds at most eight non-space tokens from `start`, and
    ///   records preceding/intervening trivia, leaving the following token
    ///   untouched; returns [`WindowEnd::Dominated`] exactly when `bound` is
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
                let labels = LabelIds::resolve(self.pbg, &candidate_labels(token.lexeme, text));
                state.settle_shadowing_frontiers(CandidateLabels::from(labels.as_slice()));
                self.gather(state, token.lexeme, text, &labels);
                state.settle_declaration_boundary(&self.candidates);
                let ahead = Ahead::Stream {
                    tokens,
                    index: TokenIndex::from(index),
                    source,
                };
                let choice = self.choose(state, text, ahead);
                Self::push_choice(state, choice, text);
                molded = molded.saturating_add(1);
            }
            index = index.saturating_add(1);
        }
        WindowEnd::Molded
    }

    /// Whether a token carrying one of `labels` can stand right after `mold`.
    ///
    /// A mold a hole follows on its right is followed by what fills the hole,
    /// which begins with a form's first tile: a token none of whose labels
    /// can begin a form refutes it. A mold that no hole follows is followed
    /// by one of its same-form successors or, when it can end its form, by
    /// what follows the whole form: the form fills a hole, so the next tile is
    /// one a hole of the form's sort faces on its left, or nothing at all. A
    /// token carrying none of those refutes it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Follow::Refuted`] exactly when either `mold`'s right bound
    ///   is not the root and no label in `labels` names a tile that begins a
    ///   form, or its right bound is the root, none of its same-form successors
    ///   is labelled with one of `labels`, and either it is not form-last or
    ///   [`Molder::after_form`] refutes `labels`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter comma read before a name, before a closer
    ///   and before nothing, an argument comma before an argument and before a
    ///   closer, a call's form-last closer, and the unknown type before `(`
    ///   expose each branch: dropping the hole check keeps the argument comma
    ///   before a closer, reading the hole check as the successor check refutes
    ///   it before an argument, dropping the form-last check refutes the
    ///   closer, dropping the successor check refutes the parameter comma
    ///   before a name, and dropping the whole-form check keeps the unknown
    ///   type before `(`.
    /// - witness: `mold::tests::a_mold_is_refuted_only_by_a_token_that_cannot_stand_after_it`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same successor or candidate menus"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `labels` holds one token's candidate labels, at most `LABEL_CAPACITY`"
        )
    )]
    #[spec(ensures: |ret| (ret == Follow::Refuted) == if matches!(self.pbg.bounds(mold), Ok((_, Bound::Root))) {
        !self.pbg.mold_successors(mold).iter().any(|&(_, right)| self.pbg.mold_label(right).is_some_and(|label| labels.as_slice().contains(&label)))
            && (!bool::from(self.pbg.mold_is_form_last(mold)) || self.after_form(mold, labels) == Follow::Refuted)
    } else {
        !labels.as_slice().iter().any(|&label| !self.pbg.label_fresh_candidates(label).is_empty())
    })]
    fn follow(
        &self,
        mold: MoldId,
        labels: &LabelIds,
    ) -> Follow
    {
        let pbg = self.pbg;
        let ids = labels.as_slice();
        let continued = if matches!(pbg.bounds(mold), Ok((_, Bound::Root))) {
            pbg.mold_successors(mold).iter().any(|&(_, right)| {
                pbg.mold_label(right)
                    .is_some_and(|label| ids.contains(&label))
            }) || (bool::from(pbg.mold_is_form_last(mold))
                && self.after_form(mold, labels) == Follow::Possible)
        }
        else {
            ids.iter()
                .any(|&label| !pbg.label_fresh_candidates(label).is_empty())
        };
        if continued {
            Follow::Possible
        }
        else {
            Follow::Refuted
        }
    }

    /// Whether a token carrying one of `labels` can stand right after a whole
    /// form that `mold` ends: one of the token's molds faces on its left a
    /// hole that admits `mold`'s sort, or no token follows at all.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Follow::Possible`] exactly when the token offers no label
    ///   or some label in it names a tile with a mold whose left context
    ///   crosses a hole of `mold`'s sort, or of any sort when `mold`'s sort is
    ///   [`Sort::Item`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call's closer before nothing and before `(`, and
    ///   the unknown type before `(`, which no type form takes after a whole
    ///   type, and before `.` and `)`, which a type operand precedes: dropping
    ///   the sort check admits `(` after the unknown type through the call's
    ///   left hole, and dropping the empty case refutes the closer at the
    ///   stream's end.
    /// - witness: `mold::tests::a_mold_is_refuted_only_by_a_token_that_cannot_stand_after_it`
    #[spec(ensures: |ret| (ret == Follow::Possible) == (labels.offered == 0 || self.pbg.mold(mold).is_ok_and(|ended| labels.as_slice().iter().any(|&label| bool::from(self.pbg.label_follows_form(label, ended.sort))))))]
    fn after_form(
        &self,
        mold: MoldId,
        labels: &LabelIds,
    ) -> Follow
    {
        let pbg = self.pbg;
        let precedes = labels.offered == 0
            || pbg.mold(mold).is_ok_and(|ended| {
                labels
                    .as_slice()
                    .iter()
                    .any(|&label| bool::from(pbg.label_follows_form(label, ended.sort)))
            });
        if precedes {
            Follow::Possible
        }
        else {
            Follow::Refuted
        }
    }

    /// Drop from `molds` the ones the significant token after `index` cannot
    /// follow, keeping them all when it refutes every one.
    ///
    /// The token's labels are its whole candidate menu, the reserved
    /// uppercase words' generic fallback labels included, so a refutation
    /// never depends on the state a mold would leave.
    ///
    /// # Specification
    /// - requires: `index` indexes `tokens`, which `source` spells.
    /// - ensures: the molds that remain are the ones [`Molder::follow`] admits
    ///   for the next significant token, in their order, unless it admits none
    ///   or the stream ends, when every mold remains.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed commas tied before a name, a reserved
    ///   uppercase word, a closer and the stream's end, and a closed comma tied
    ///   with an open one before a closer and before an argument: the fallback
    ///   labels keep the parameter comma before `Type`, a closer drops the open
    ///   comma beside a closed one it can follow, an argument drops the closed
    ///   comma beside the open one, and a closer refuting both or the stream's
    ///   end keeps both.
    /// - witness: `mold::tests::the_next_token_keeps_only_the_molds_it_can_follow`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body tests every mold against the next token"
        )
    )]
    #[spec(captures: before = molds.clone(), ensures: |_| molds.iter().all(|mold| before.contains(mold)) && (before.is_empty() || !molds.is_empty()))]
    fn drop_refuted<'src>(
        &self,
        molds: &mut Vec<MoldId>,
        tokens: &[Token],
        index: TokenIndex,
        source: &'src SourceFragment<'src>,
    )
    {
        let Some(labels) =
            next_labels(tokens, index, source).map(|labels| LabelIds::resolve(self.pbg, &labels))
        else {
            return;
        };
        if molds
            .iter()
            .all(|&mold| self.follow(mold, &labels) == Follow::Refuted)
        {
            return;
        }
        molds.retain(|&mold| self.follow(mold, &labels) == Follow::Possible);
    }

    /// The one opener in `self.openers` that the token carrying `labels`
    /// continues inside its own form, when every other opener is a whole
    /// one-tile form.
    ///
    /// A one-tile form is complete at its tile, so the token after it stands
    /// outside it, after whatever form encloses it; an opener whose form goes
    /// on with a tile the token carries reads the token inside. The longer
    /// reading wins, as maximal munch: `List(` opens a type application
    /// rather than ending the type `List` before a parenthesis. A window would
    /// make the same choice on a well-formed source whose continuation it
    /// reads to the end; one that ends inside a long argument list scores the
    /// opener's unfinished form against the complete tile and can choose the
    /// tile.
    ///
    /// An opener that could also end its form at its tile, as a constructor
    /// pattern's name before its optional arguments, is continued all the
    /// same: `Some(` reads the parenthesis as its arguments.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a mold exactly when exactly one opener has a
    ///   same-form successor labelled with one of `labels`, and every other
    ///   opener is form-last with no same-form predecessor or successor; the
    ///   mold returned is that opener.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type application's name tied with the bare type
    ///   name before `(` and before `,`, beside a second opener `(` continues,
    ///   and beside a tile with a successor, and a constructor pattern's name,
    ///   which can end its form, before `(`: the first and the last return the
    ///   continued opener; dropping the uniqueness check, admitting a tile with
    ///   a successor as complete, or refusing a form-last opener each changes
    ///   one case. The corpus and a long application after `-F` observe the
    ///   choice through whole parses.
    /// - witness: `mold::tests::a_continued_opener_beats_a_one_tile_form`
    /// - witness: `mold::tests::a_long_type_application_is_read_whole`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same openers and their successor menus"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `labels` holds one token's candidate labels, at most `LABEL_CAPACITY`"
        )
    )]
    #[spec(ensures: |ret| {
        let pbg = self.pbg;
        let continued = |mold: MoldId| pbg.mold_successors(mold).iter().any(|&(_, right)| pbg.mold_label(right).is_some_and(|label| labels.contains(&label)));
        let whole = |mold: MoldId| bool::from(pbg.mold_is_form_last(mold)) && !bool::from(pbg.mold_has_successor(mold)) && !bool::from(pbg.mold_has_predecessor(mold));
        let mut found = self.openers.iter().copied().filter(|&mold| continued(mold));
        let only = found.next().filter(|_| found.next().is_none());
        ret == only.filter(|_| self.openers.iter().all(|&mold| continued(mold) || whole(mold)))
    })]
    fn continued_opener(
        &self,
        labels: &[LabelId],
    ) -> Option<MoldId>
    {
        let pbg = self.pbg;
        let mut continued = None;
        for &mold in &self.openers {
            if pbg.mold_successors(mold).iter().any(|&(_, right)| {
                pbg.mold_label(right)
                    .is_some_and(|label| labels.contains(&label))
            }) {
                if continued.replace(mold).is_some() {
                    return None;
                }
            }
            else if !bool::from(pbg.mold_is_form_last(mold))
                || bool::from(pbg.mold_has_successor(mold))
                || bool::from(pbg.mold_has_predecessor(mold))
            {
                return None;
            }
        }
        continued
    }

    /// The least opener in `self.openers` when every opener can end its form
    /// at its tile, none goes on with the token carrying `labels`, and every
    /// opener's rule has one sort and one precedence.
    ///
    /// Each reading then ends a whole form before the token, and the forms
    /// stand alike as operands to whatever follows: one sort, one precedence,
    /// nothing left open. Every window then closes with the same obligations,
    /// and the exact-tie rule keeps the least opener; this keeps it without
    /// molding the windows. A primitive type's spelling before `,` ties its
    /// primitive and type-variable readings this way, as a parenthesized
    /// expression's `)` ties its two closers.
    ///
    /// # Specification
    /// - requires: `self.openers` ascending.
    /// - ensures: the first opener exactly when every opener is form-last, has
    ///   no same-form successor labelled with one of `labels`, and has a rule
    ///   whose sort and precedence are the first opener's; otherwise none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a primitive type's two readings before `,`, a
    ///   constructor pattern's name before `=>` and before `(`, the name beside
    ///   a constructor expression, and a type application's name beside the
    ///   bare type name: only the alike readings and the lone name before `=>`
    ///   return the least; ignoring the next token, the sort, or the form-last
    ///   check each changes one case. The corpus molds to the same trees with
    ///   the windows the rule skips.
    /// - witness: `mold::tests::readings_that_end_alike_keep_the_least`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks the same openers and their successor menus"
        )
    )]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            linear_search_in_loop,
            reason = "bounded: `labels` holds one token's candidate labels, at most `LABEL_CAPACITY`"
        )
    )]
    #[spec(ensures: |ret| {
        let pbg = self.pbg;
        let continued = |mold: MoldId| pbg.mold_successors(mold).iter().any(|&(_, right)| pbg.mold_label(right).is_some_and(|label| labels.contains(&label)));
        let key = |mold: MoldId| pbg.rule_of(mold).ok().map(|rule| (rule.sort(), rule.prec()));
        ret == self.openers.first().copied().filter(|&least| key(least).is_some() && self.openers.iter().all(|&mold| bool::from(pbg.mold_is_form_last(mold)) && !continued(mold) && key(mold) == key(least)))
    })]
    fn complete_alike(
        &self,
        labels: &[LabelId],
    ) -> Option<MoldId>
    {
        let pbg = self.pbg;
        let &least = self.openers.first()?;
        let key = |mold: MoldId| {
            pbg.rule_of(mold)
                .ok()
                .map(|rule| (rule.sort(), rule.prec()))
        };
        let shared = key(least)?;
        self.openers
            .iter()
            .all(|&mold| {
                bool::from(pbg.mold_is_form_last(mold))
                    && key(mold) == Some(shared)
                    && !pbg.mold_successors(mold).iter().any(|&(_, right)| {
                        pbg.mold_label(right)
                            .is_some_and(|label| labels.contains(&label))
                    })
            })
            .then_some(least)
    }

    /// Keep, of each class of interchangeable openers in `self.openers`, only
    /// the least.
    ///
    /// Interchangeable molds ([`Pbg::least_interchangeable`]) leave the slope
    /// to evolve alike under every later tile, so their windows close with the
    /// same delta, and the strict comparison keeps the least of them. Dropping
    /// the others before any window runs makes the same choice.
    ///
    /// # Specification
    /// - requires: `self.openers` ascending.
    /// - ensures: the openers that remain are, in their order, each class's
    ///   least member among the openers.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition's two parameter-name molds beside a mold
    ///   of another class: the later name mold goes and the other class stays;
    ///   and the corpus molds to the same trees with the windows the drop
    ///   skips.
    /// - witness: `mold::tests::interchangeable_openers_keep_only_the_least`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares every opener against the classes kept before it"
        )
    )]
    #[spec(captures: before = self.openers.clone(), ensures: |()| self.openers.iter().all(|mold| before.contains(mold)) && before.iter().all(|&mold| self.openers.iter().any(|&kept| kept <= mold && self.pbg.least_interchangeable(kept) == self.pbg.least_interchangeable(mold))) && self.openers.iter().zip(self.openers.iter().skip(1)).all(|(left, right)| left < right && self.pbg.least_interchangeable(*left) != self.pbg.least_interchangeable(*right)))]
    fn drop_interchangeable(&mut self)
    {
        let pbg = self.pbg;
        let mut kept = 0_usize;
        for slot in 0 .. self.openers.len() {
            let Some(&mold) = self.openers.get(slot)
            else {
                break;
            };
            let class = pbg.least_interchangeable(mold);
            let seen = self.openers.get(.. kept).is_some_and(|earlier| {
                earlier
                    .iter()
                    .any(|&earlier| pbg.least_interchangeable(earlier) == class)
            });
            if !seen {
                if let Some(at) = self.openers.get_mut(kept) {
                    *at = mold;
                }
                kept = kept.saturating_add(1);
            }
        }
        self.openers.truncate(kept);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;

    use anodized::spec;
    use gandr_surface_grammar::CandidateCount;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::TileLabel;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeDigest;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_theory_graphs::Bound;

    use super::Ahead;
    use super::CandidateLabel;
    use super::Follow;
    use super::Molder;
    use super::SourceText;
    use super::TokenIndex;
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
            (Lexeme::StringFragment, "x", &["string_fragment"]),
            (Lexeme::ShellStringFragment, "x", &[
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
            (Lexeme::Punct, "<~>", &["<~>", "≃"]),
            (Lexeme::Punct, "~~>", &["~~>", "⇝"]),
            (Lexeme::Punct, "::", &["::", "∷"]),
            (Lexeme::Punct, "≃", &["≃"]),
            (Lexeme::LowerWord, "inf", &["inf", "ω"]),
            (Lexeme::Space, " ", &[]),
            (Lexeme::Unknown, "^", &[]),
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

    /// #2255: a group closes at the `)` that balances its opener, past a
    /// nested call, a nested group and a quote, and the token past it
    /// decides; a `(` inside a string opens nothing.
    #[test]
    fn a_group_closes_past_its_nested_groups_2255()
    {
        use super::GroupClose;
        for (text, expected) in [
            ("(y : A, z : P(y)) => B", GroupClose::Arrow),
            ("((A)) => B", GroupClose::Arrow),
            ("(type(T), \"(\") => B", GroupClose::Arrow),
            ("(x : A) , y", GroupClose::Other),
            ("(x, f(y)) => B", GroupClose::Arrow),
            ("(a, b)", GroupClose::Other),
            ("( ) => B", GroupClose::Empty),
            ("(a, f(b)", GroupClose::Open),
        ] {
            let source = SourceFragment::from(text);
            let tokens = label(source);
            assert_eq!(
                super::group_close(&tokens, super::TokenIndex::from(0_usize), &source),
                expected,
                "`{text}`"
            );
        }
    }

    #[test]
    fn a_run_reads_eight_significant_tokens_past_its_end()
    {
        // Positions: significant tokens at even positions 0..=20, one space
        // after each but the last.
        let tokens = label(SourceFragment::from("a b c d e f g h i j k"));
        assert_eq!(tokens.len(), 21);
        for (end, expected) in [
            // Eight significant tokens from position 0 end at position 14.
            (0_usize, 15_usize),
            // From a space, the window still counts only significant tokens.
            (1, 17),
            (2, 17),
            // Exactly eight remain, then fewer: the stream's end.
            (6, 21),
            (8, 21),
            (20, 21),
            (21, 21),
            (usize::MAX, 21),
        ] {
            assert_eq!(
                usize::from(super::lookahead_reach(
                    &tokens,
                    super::TokenIndex::from(end)
                )),
                expected,
                "from {end}"
            );
        }
        let adjacent = label(SourceFragment::from("((((((((((("));
        assert_eq!(
            usize::from(super::lookahead_reach(
                &adjacent,
                super::TokenIndex::from(1_usize)
            )),
            9
        );
        assert_eq!(
            usize::from(super::lookahead_reach(
                &[],
                super::TokenIndex::from(0_usize)
            )),
            0
        );
    }

    #[test]
    fn candidate_gathering_is_a_canonical_union() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        assert!(molder.candidates.is_empty());
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
        // Labels resolve once, in order, an undeclared spelling left out.
        let identifier = pbg
            .label_id(gandr_surface_grammar::LabelText("identifier"))
            .ok_or("no identifier label")?;
        let resolved = super::LabelIds::resolve(&pbg, &[
            CandidateLabel::from("identifier"),
            CandidateLabel::from("absent-label-for-witness"),
            CandidateLabel::from("identifier"),
        ]);
        assert_eq!(resolved.as_slice(), [identifier, identifier]);
        molder.gather_labels(resolved.as_slice(), None, super::CandidateMenu::Declared);
        assert!(
            molder
                .candidates
                .iter()
                .copied()
                .eq(expected.iter().copied())
        );
        for source in [" ", "^"] {
            let token = *label(SourceFragment::from(source)).first().unwrap();
            assert_eq!(
                molder.candidate_count(token, SourceText::from(source)),
                CandidateCount(0)
            );
            assert_eq!(
                molder.choose(
                    &mut MeldState::new(&pbg),
                    TokenText::from(source),
                    Ahead::Nothing
                ),
                None
            );
        }
        let &(open, successor) = pbg.adjacencies().first().unwrap();
        let label = pbg.mold(successor)?.label;
        molder.candidates = vec![open];
        let successor_label = pbg.mold_label(successor).ok_or("no label")?;
        molder.push_form_successors(&[successor_label], open);
        let expected: alloc::vec::Vec<_> = core::iter::once(open)
            .chain(pbg.adjacencies().iter().filter_map(|&(left, right)| {
                (left == open && pbg.mold(right).is_ok_and(|def| def.label == label))
                    .then_some(right)
            }))
            .collect();
        assert_eq!(molder.candidates, expected);
        let before = molder.candidates.clone();
        molder.push_form_successors(&[], open);
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
        state.push(&crate::MoldedTile::new(invalid, crate::TileText::from("^")));
        let before = state.checkpoint().to_bytes();
        let floor = molder.floor_key(&state, invalid, &state.admissibility_frontier());
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
            molder.choose(&mut state, TokenText::from("x"), Ahead::Nothing),
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
            crate::TileText::from("^"),
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
        let source = SourceFragment::from("1 2 3 4 5 6 7 8 9 10 11");
        let tokens = label(source);
        let at = |position: usize| super::TokenIndex::from(position);
        let mut state = MeldState::new(&pbg);
        let mark = state.mark();
        let end = molder.mold_window(
            &mut state,
            &tokens,
            at(0),
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
            at(tokens.len()),
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
        let source = SourceFragment::from("^ 1 2");
        let tokens = label(source);
        let unmolded_tokens = |count: usize| {
            let mut delta = crate::Delta::empty();
            for _ in 0 .. count {
                delta.insert(crate::Oblig::UnmoldedTok);
            }
            delta
        };
        // The unmolded `^` flags one obligation before the window's first
        // token, `1`: a bound it reaches stops the window there, one above it
        // lets the window mold to its end.
        let window = |molder: &mut Molder<'_>, bound| {
            let mut state = MeldState::new(&pbg);
            let mark = state.mark();
            state.push(&crate::MoldedTile::new(
                gandr_surface_syntax::MoldId::from(u32::MAX),
                crate::TileText::from("^"),
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
            crate::TileText::from("^"),
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
        let src = "^";
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
        let src = "def f() -> -F Integer { pure (x * x) } square(9) [1, 2, 3]";

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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |pbg| ["def", "pure", "(", ")"].into_iter().all(|label| !pbg.candidates(gandr_surface_grammar::TileLabel(label)).is_empty())))]
    fn built() -> Result<Pbg, Box<dyn Error>>
    {
        let pbg = built_in()?;
        Ok(pbg)
    }

    /// The rule of `def f(x, y) …`.
    const DEF: RuleName = RuleName("def_value");
    /// The rule of `f(x, y)`.
    const CALL: RuleName = RuleName("call_expression");
    /// The comma tile.
    const COMMA: TileLabel = TileLabel(",");
    /// The uppercase-name label a reserved word falls back to.
    const TYPE_IDENTIFIER: TileLabel = TileLabel("type_identifier");

    /// What a mold's right side faces.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum RightSide
    {
        /// No hole: the right bound is the root.
        Closed,
        /// A hole, so an operand may follow.
        Hole,
    }

    /// The first mold labelled `label` in rule `rule` whose right side is
    /// `side`, and which some same-form successor labelled with each of
    /// `after` follows.
    ///
    /// # Specification
    /// - ensures: a mold of `rule` labelled `label`, its right bound the root
    ///   exactly when `side` is closed.
    /// - fails: the grammar declares no such mold.
    /// - panics: none.
    ///
    /// # Errors
    /// No mold matches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the follow-check witnesses look up a closed and an
    ///   open comma and a closed form-last parenthesis; a wrong rule or side
    ///   changes which branch they exercise.
    /// - witness: `mold::tests::a_mold_is_refuted_only_by_a_token_that_cannot_stand_after_it`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&mold| pbg.rule_of(mold).is_ok_and(|found| found.name() == rule) && matches!(pbg.bounds(mold), Ok((_, Bound::Root))) == (side == RightSide::Closed)))]
    fn mold_in(
        pbg: &Pbg,
        rule: RuleName,
        label: TileLabel,
        side: RightSide,
        after: &[TileLabel],
    ) -> Result<MoldId, Box<dyn Error>>
    {
        pbg.candidates(label)
            .iter()
            .copied()
            .find(|&mold| {
                pbg.rule_of(mold).is_ok_and(|found| found.name() == rule)
                    && matches!(pbg.bounds(mold), Ok((_, Bound::Root)))
                        == (side == RightSide::Closed)
                    && after.iter().all(|next| {
                        pbg.mold_successors(mold)
                            .iter()
                            .any(|&(_, right)| pbg.mold(right).is_ok_and(|def| def.label == next.0))
                    })
            })
            .ok_or_else(|| alloc::format!("no `{}` mold in `{}`", label.0, rule.0).into())
    }

    #[test]
    fn a_mold_is_refuted_only_by_a_token_that_cannot_stand_after_it() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let molder = Molder::new(&pbg);
        let resolve = |label| super::LabelIds::resolve(&pbg, &[CandidateLabel::from(label)]);
        let nothing = super::LabelIds::new();
        let identifier = resolve("identifier");
        let close = resolve(")");
        // `def f(x, y)`: the parameter comma is followed by a parameter name.
        let parameter_comma = mold_in(&pbg, DEF, COMMA, RightSide::Closed, &[TYPE_IDENTIFIER])?;
        assert_eq!(
            molder.follow(parameter_comma, &identifier),
            Follow::Possible
        );
        assert_eq!(molder.follow(parameter_comma, &close), Follow::Refuted);
        assert_eq!(molder.follow(parameter_comma, &nothing), Follow::Refuted);
        // `f(x, y)`: an argument fills the hole after the comma, and an
        // argument begins with a form's first tile, which a closer never is.
        let argument_comma = mold_in(&pbg, CALL, COMMA, RightSide::Hole, &[])?;
        assert_eq!(molder.follow(argument_comma, &identifier), Follow::Possible);
        assert_eq!(molder.follow(argument_comma, &close), Follow::Refuted);
        // `f(x)`: the closer ends its form, so it may end the stream, and
        // whatever a hole of its sort precedes may follow it: a call of the
        // call.
        let call_close = mold_in(&pbg, CALL, TileLabel(")"), RightSide::Closed, &[])?;
        assert!(bool::from(pbg.mold_is_form_last(call_close)));
        assert_eq!(molder.follow(call_close, &nothing), Follow::Possible);
        // A token whose labels the grammar does not declare is a token all
        // the same: it follows no form, where no token at all may.
        assert_eq!(
            molder.follow(call_close, &resolve("absent-label-for-witness")),
            Follow::Refuted
        );
        let open = resolve("(");
        assert_eq!(molder.follow(call_close, &open), Follow::Possible);
        // `?(P). S` (#1229): the unknown type is a whole type, and no type
        // form goes on with `(` after one, while `.` and `)` stand after a
        // type operand.
        let unknown = mold_in(
            &pbg,
            RuleName("unknown_type"),
            TileLabel("?"),
            RightSide::Closed,
            &[],
        )?;
        assert_eq!(molder.follow(unknown, &open), Follow::Refuted);
        assert_eq!(molder.follow(unknown, &resolve(".")), Follow::Possible);
        assert_eq!(molder.follow(unknown, &close), Follow::Possible);
        Ok(())
    }

    #[test]
    fn the_next_token_keeps_only_the_molds_it_can_follow() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let molder = Molder::new(&pbg);
        // The parameter comma admits a type identifier after it; the comma
        // between a telescope update's fields admits only a field name.
        let parameter_comma = mold_in(&pbg, DEF, COMMA, RightSide::Closed, &[TYPE_IDENTIFIER])?;
        let field_comma = mold_in(
            &pbg,
            RuleName("telescope_expression"),
            COMMA,
            RightSide::Closed,
            &[TileLabel("identifier")],
        )?;
        // A call's argument comma opens another argument; its trailing comma
        // is followed by the closer.
        let argument_comma = mold_in(&pbg, CALL, COMMA, RightSide::Hole, &[])?;
        let trailing_comma = mold_in(&pbg, CALL, COMMA, RightSide::Closed, &[TileLabel(")")])?;
        let cases: [(&str, &[MoldId], &[MoldId]); 7] = [
            (", x", &[parameter_comma, field_comma], &[
                parameter_comma,
                field_comma,
            ]),
            // A reserved uppercase word follows wherever its generic fallback
            // labels do.
            (", Type", &[parameter_comma, field_comma], &[
                parameter_comma,
            ]),
            (", )", &[argument_comma, trailing_comma], &[trailing_comma]),
            (", x", &[argument_comma, trailing_comma], &[argument_comma]),
            // Refuting every mold refutes none.
            (", )", &[parameter_comma, field_comma], &[
                parameter_comma,
                field_comma,
            ]),
            (", )", &[parameter_comma, argument_comma], &[
                parameter_comma,
                argument_comma,
            ]),
            // At the stream's end nothing is read.
            (",  ", &[parameter_comma, field_comma], &[
                parameter_comma,
                field_comma,
            ]),
        ];
        for (source, molds, kept) in cases {
            let tokens = label(SourceFragment::from(source));
            let mut molds = molds.to_vec();
            molder.drop_refuted(
                &mut molds,
                &tokens,
                TokenIndex::from(0),
                &SourceFragment::from(source),
            );
            assert_eq!(molds, kept, "{source:?}");
        }
        Ok(())
    }

    #[test]
    fn interchangeable_openers_keep_only_the_least() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        // A definition's lowercase parameter name: `identifier` and
        // `type_variable` at one position read alike.
        let (variable, name) = pbg
            .iter_molds()
            .find_map(|(mold, def)| {
                let twin = pbg.least_interchangeable(mold);
                (twin != mold
                    && def.label == "type_variable"
                    && pbg.rule_of(mold).is_ok_and(|rule| rule.name() == DEF))
                .then_some((mold, twin))
            })
            .ok_or("a definition's parameter names share a class")?;
        let other = mold_in(&pbg, CALL, COMMA, RightSide::Hole, &[])?;
        assert_ne!(pbg.least_interchangeable(other), name);
        let mut ascending = [name, variable, other];
        ascending.sort_unstable();
        molder.openers = ascending.to_vec();
        molder.drop_interchangeable();
        let mut kept = vec![name, other];
        kept.sort_unstable();
        assert_eq!(molder.openers, kept);
        molder.openers = vec![variable];
        molder.drop_interchangeable();
        assert_eq!(molder.openers, vec![variable]);
        Ok(())
    }

    #[test]
    fn a_continued_opener_beats_a_one_tile_form() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let open = TileLabel("(");
        // `List(T)` against the complete type `List`.
        let application = mold_in(
            &pbg,
            RuleName("type_application"),
            TYPE_IDENTIFIER,
            RightSide::Closed,
            &[open],
        )?;
        let bare = mold_in(
            &pbg,
            RuleName("type_identifier"),
            TYPE_IDENTIFIER,
            RightSide::Closed,
            &[],
        )?;
        // A data declaration's name, which `(` also continues.
        let declared = mold_in(
            &pbg,
            RuleName("data_declaration"),
            TYPE_IDENTIFIER,
            RightSide::Closed,
            &[open],
        )?;
        // A parameter comma: neither continued by `(` nor a form of its own.
        let parameter_comma = mold_in(&pbg, DEF, COMMA, RightSide::Closed, &[TYPE_IDENTIFIER])?;
        // `Some(x)`: the pattern's name, which can also end its form.
        let pattern_name = constructor_pattern(&pbg)?;
        let label = |spelled| {
            pbg.label_id(gandr_surface_grammar::LabelText(spelled))
                .ok_or("undeclared label")
        };
        let parenthesis = [label("(")?];
        let comma = [label(",")?];
        let cases: [(&[MoldId], &[gandr_surface_grammar::LabelId], Option<MoldId>); 5] = [
            (&[application, bare], &parenthesis, Some(application)),
            (&[application, bare], &comma, None),
            (&[application, declared], &parenthesis, None),
            (&[application, parameter_comma], &parenthesis, None),
            (&[pattern_name], &parenthesis, Some(pattern_name)),
        ];
        for (openers, labels, expected) in cases {
            let mut ascending = openers.to_vec();
            ascending.sort_unstable();
            molder.openers = ascending;
            assert_eq!(
                molder.continued_opener(labels),
                expected,
                "{openers:?} before {labels:?}"
            );
        }
        Ok(())
    }

    /// The name opening `constructor_pattern`, whose arguments are optional.
    ///
    /// # Specification
    /// - ensures: the mold of the constructor tile `(` continues in
    ///   `constructor_pattern`.
    /// - fails: the grammar declares no such mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The mold is missing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tie witnesses read the mold's form membership; a
    ///   wrong rule changes which rule they exercise.
    /// - witness: `mold::tests::readings_that_end_alike_keep_the_least`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&opener| pbg.rule_of(opener).is_ok_and(|rule| rule.name() == RuleName("constructor_pattern"))))]
    fn constructor_pattern(pbg: &Pbg) -> Result<MoldId, Box<dyn Error>>
    {
        mold_in(
            pbg,
            RuleName("constructor_pattern"),
            TileLabel("constructor"),
            RightSide::Closed,
            &[TileLabel("(")],
        )
    }

    #[test]
    fn readings_that_end_alike_keep_the_least() -> Result<(), Box<dyn Error>>
    {
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let pattern_name = constructor_pattern(&pbg)?;
        // `u32` read as the primitive type and as a type variable.
        let primitive = mold_in(
            &pbg,
            RuleName("primitive_type"),
            TileLabel("u32"),
            RightSide::Closed,
            &[],
        )?;
        let variable = mold_in(
            &pbg,
            RuleName("type_variable"),
            TileLabel("type_variable"),
            RightSide::Closed,
            &[],
        )?;
        // The constructor in expression position: a form of another sort.
        let expression = mold_in(
            &pbg,
            RuleName("constructor.expression"),
            TileLabel("constructor"),
            RightSide::Closed,
            &[],
        )?;
        // `List(T)` against `List`: the application cannot end at its name.
        let application = mold_in(
            &pbg,
            RuleName("type_application"),
            TYPE_IDENTIFIER,
            RightSide::Closed,
            &[TileLabel("(")],
        )?;
        let bare = mold_in(
            &pbg,
            RuleName("type_identifier"),
            TYPE_IDENTIFIER,
            RightSide::Closed,
            &[],
        )?;
        let label = |spelled| {
            pbg.label_id(gandr_surface_grammar::LabelText(spelled))
                .ok_or("undeclared label")
        };
        let arrow = [label("=>")?];
        let parenthesis = [label("(")?];
        let comma = [label(",")?];
        let cases: [(&[MoldId], &[gandr_surface_grammar::LabelId], Option<MoldId>); 6] = [
            (
                &[primitive, variable],
                &comma,
                Some(primitive.min(variable)),
            ),
            (&[pattern_name], &arrow, Some(pattern_name)),
            (&[pattern_name], &parenthesis, None),
            (&[pattern_name, expression], &arrow, None),
            (&[application, bare], &comma, None),
            (&[primitive, application], &comma, None),
        ];
        for (openers, labels, expected) in cases {
            let mut ascending = openers.to_vec();
            ascending.sort_unstable();
            molder.openers = ascending;
            assert_eq!(
                molder.complete_alike(labels),
                expected,
                "{openers:?} before {labels:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn a_long_type_application_is_read_whole() -> Result<(), Box<dyn Error>>
    {
        // Nine tokens follow the name, so a window ends inside the argument
        // list, where the complete type `Pair` before a parenthesized type
        // scored better than the unfinished application.
        let pbg = built()?;
        let source = "def pair(x : Integer) -> -F Pair(Integer, String, x, x) { ret x }\n";
        let parsed = crate::parse(&pbg, SourceText::from(source))?;
        let tree = parsed.tree();
        let applied = source.find("Pair(").ok_or("the source applies `Pair`")?;
        let melds: Vec<(RuleName, usize, usize)> = tree
            .positions()
            .filter_map(|position| {
                let node = tree.node(position)?;
                let NodeLabel::Meld(mold) = node.label()
                else {
                    return None;
                };
                let rule = pbg.rule_of(mold).ok()?.name();
                Some((
                    rule,
                    usize::from(node.span().start()),
                    usize::from(node.span().end()),
                ))
            })
            .collect();
        assert!(
            melds.contains(&(
                RuleName("type_application"),
                applied,
                applied.saturating_add("Pair(Integer, String, x, x)".len())
            )),
            "the application spans its arguments: {melds:?}"
        );
        assert!(
            melds
                .iter()
                .all(|&(rule, ..)| rule != RuleName("parenthesized_type")),
            "no argument list stands alone: {melds:?}"
        );
        Ok(())
    }

    #[test]
    fn a_window_reads_the_token_after_a_tied_separator() -> Result<(), Box<dyn Error>>
    {
        // A call's separator ties the comma that opens another argument with
        // the trailing one its closer follows. Read alone, the lesser mold
        // wins and the closer after it becomes a repair; inside a window the
        // next token is known, and only the trailing comma can precede it.
        let pbg = built()?;
        let mut molder = Molder::new(&pbg);
        let source = SourceText::from("def x = f(a, ) ;");
        let tokens = label(SourceFragment::from("def x = f(a, ) ;"));
        let comma = tokens
            .iter()
            .position(|token| {
                AsRef::<str>::as_ref(&token.text(&SourceFragment::from("def x = f(a, ) ;"))) == ","
            })
            .ok_or("the source spells a comma")?;
        let mut state = MeldState::new(&pbg);
        for &token in tokens.get(.. comma).ok_or("the comma is in the stream")? {
            molder.mold(&mut state, token, source);
        }
        let argument_comma = mold_in(&pbg, CALL, COMMA, RightSide::Hole, &[])?;
        let trailing_comma = mold_in(&pbg, CALL, COMMA, RightSide::Closed, &[TileLabel(")")])?;
        let mut menu = vec![argument_comma, trailing_comma];
        menu.sort_unstable();
        molder.candidates.clone_from(&menu);
        let alone = molder.choose(&mut state, TokenText::from(","), Ahead::Nothing);
        molder.candidates = menu;
        let ahead = Ahead::Stream {
            tokens: &tokens,
            index: TokenIndex::from(comma),
            source: &SourceFragment::from("def x = f(a, ) ;"),
        };
        let windowed = molder.choose(&mut state, TokenText::from(","), ahead);
        assert_eq!(
            alone,
            Some(argument_comma),
            "read alone, the lesser mold wins"
        );
        assert_eq!(
            windowed,
            Some(trailing_comma),
            "the closer after it decides"
        );
        Ok(())
    }

    #[test]
    fn an_attribute_block_is_a_form_of_its_own() -> Result<(), Box<dyn Error>>
    {
        // Every block before a declaration is an `attribute_block` form of its
        // own, whatever its length and whatever declaration follows it, so a
        // definition's identity excludes the blocks decorating it.
        let pbg = built()?;
        let declarations = [
            ("def x = 1 ;", "def_value"),
            ("def x : Integer ;", "def_value"),
            ("def f(y : Integer) -> -F Integer { return y }", "def_value"),
            ("data Color : Type {\n  Red : Color;\n}", "data_declaration"),
        ];
        for count in 1_usize ..= 6 {
            let attributes = vec!["runs(\"1\")"; count].join(", ");
            for (declaration, expected) in declarations {
                let source = alloc::format!("@[ {attributes} ]\n@[ checks ]\n{declaration}\n");
                let parsed = crate::parse(&pbg, SourceText::from(source.as_str()))?;
                assert_eq!(parsed.obligations(), &[], "{source:?} parses clean");
                let tree = parsed.tree();
                let rules: Vec<RuleName> = tree
                    .children(tree.root())
                    .filter_map(|child| {
                        match tree.node(child).map(gandr_surface_syntax::Node::label) {
                            Some(NodeLabel::Meld(mold) | NodeLabel::Tile(mold)) => pbg
                                .rule_of(mold)
                                .ok()
                                .map(gandr_surface_grammar::Rule::name),
                            _ => None,
                        }
                    })
                    .collect();
                assert_eq!(
                    rules,
                    [
                        RuleName("attribute_block"),
                        RuleName("attribute_block"),
                        RuleName(expected)
                    ],
                    "{source:?}"
                );
            }
        }
        Ok(())
    }

    #[test]
    fn brackets_are_classified_by_lexeme_and_text()
    {
        let source = SourceFragment::from("@[ f([x], #{ y }) ] ( \"]\" z");
        let classes: Vec<(String, super::Bracket)> = label(source)
            .into_iter()
            .filter(|token| token.lexeme != Lexeme::Space)
            .map(|token| {
                let text = token.text(&source);
                let spelled = AsRef::<str>::as_ref(&text);
                (
                    String::from(spelled),
                    super::bracket(token, TokenText::from(spelled)),
                )
            })
            .collect();
        let open = super::Bracket::Open;
        let close = super::Bracket::Close;
        let neither = super::Bracket::Neither;
        let expected = [
            ("@[", open),
            ("f", neither),
            ("(", open),
            ("[", open),
            ("x", neither),
            ("]", close),
            (",", neither),
            ("#{", open),
            ("y", neither),
            ("}", close),
            (")", close),
            ("]", close),
            ("(", open),
            ("\"", neither),
            ("]", neither),
            ("\"", neither),
            ("z", neither),
        ];
        assert_eq!(
            classes,
            expected.map(|(text, class)| (String::from(text), class)),
            "a compound opener opens, a word and a bracket spelled inside a string do not"
        );
    }

    #[test]
    fn keyword_and_identifier_share_a_word_menu()
    {
        // A reserved keyword molds only to its own tile (no identifier menu).
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("def")).as_slice(),
            [CandidateLabel::from("def")]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("val")).as_slice(),
            [CandidateLabel::from("val")]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("let")).as_slice(),
            [
                CandidateLabel::from("let"),
                CandidateLabel::from("identifier"),
                CandidateLabel::from("type_variable"),
                CandidateLabel::from("hole_name")
            ]
        );
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("run")).as_slice(),
            [CandidateLabel::from("run")]
        );
        // An ordinary lowercase word gets the wide identifier menu, plus the
        // `hole_name` tile — admissible only after a `?` hole frontier, so it
        // never competes at an ordinary word slot.
        assert_eq!(
            candidate_labels(Lexeme::LowerWord, TokenText::from("greeting")).as_slice(),
            [
                CandidateLabel::from("greeting"),
                CandidateLabel::from("identifier"),
                CandidateLabel::from("type_variable"),
                CandidateLabel::from("hole_name")
            ]
        );
        // A word spelled as a lexical class's label is a name, never a token
        // of the class (#1863: `number` molded to the numeral tile).
        for class in ["number", "constructor", "typed_number"] {
            assert_eq!(
                candidate_labels(Lexeme::LowerWord, TokenText::from(class)).as_slice(),
                [
                    CandidateLabel::from("identifier"),
                    CandidateLabel::from("type_variable"),
                    CandidateLabel::from("hole_name")
                ]
            );
        }
        // A reserved primitive/type keyword molds only to its own tile.
        assert_eq!(
            candidate_labels(Lexeme::UpperWord, TokenText::from("Integer")).as_slice(),
            [CandidateLabel::from("Integer")]
        );
        // An ordinary uppercase word gets the constructor / type-identifier menu.
        assert_eq!(
            candidate_labels(Lexeme::UpperWord, TokenText::from("Inl")).as_slice(),
            [
                CandidateLabel::from("Inl"),
                CandidateLabel::from("constructor"),
                CandidateLabel::from("type_identifier")
            ]
        );
        assert_eq!(
            candidate_labels(Lexeme::Punct, TokenText::from("->")).as_slice(),
            [CandidateLabel::from("->")]
        );
        assert!(candidate_labels(Lexeme::Space, TokenText::from(" ")).is_empty());
        assert!(candidate_labels(Lexeme::Unknown, TokenText::from("^")).is_empty());
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
