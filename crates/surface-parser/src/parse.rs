//! The batch parser: `labeler ∘ molder ∘ fold(push) ∘ commit(finalize)`.
//!
//! [`parse`](fn@crate::parse) is the whole front-end composed:
//! it labels the source, molds each
//! token to its obligation-minimizing [`gandr_surface_syntax::MoldId`], folds
//! the molded stream through the melder's `push`, records trivia for
//! losslessness, and commits the molded [`SyntaxTree`]. The result carries the
//! buffered obligations beside the tree so the obligation surface is never
//! lost — a total function: any [`SourceText`] yields a well-formed
//! [`ParseResult`], never a panic.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::FormUnit;
use crate::MeldError;
use crate::MeldState;
use crate::Molder;
use crate::TokenIndex;
use crate::TokenRun;
use crate::UnitSeam;
use crate::label::Labeling;
use crate::label::Lexeme;
use crate::label::label;
use crate::mold::lookahead_reach;
use crate::oblig::ObligationInstance;

/// What a form run's molding depends on, spelled out.
///
/// The spelling is whether the run starts the source, its length in tokens,
/// and the run's tokens followed by the tokens past it its molding reads as
/// lookahead, each by its lexical class and its extent, then their bytes.
///
/// Two runs with one identity mold to equal [`FormUnit`]s, whichever
/// sources and positions they sit at, so a unit parked
/// ([`FormUnit::park`]) in one revision serves the run of a later revision
/// that carries its identity. Identity is equality of the spellings: exact,
/// with no digest to collide.
///
/// # Specification
/// - requires: nothing.
/// - ensures: holds the spelling [`FormSplit::identity`] computed.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the split's
///   identity carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — over edited corpus sources, every run whose identity a
///   run of the unedited source carries molds to an equal unit, and the run
///   whose lookahead the edit reaches does not keep its identity.
/// - witness: `parse::tests::an_equal_identity_molds_an_equal_unit`
/// - witness: `parse::tests::hostile_edits_reuse_only_equal_units`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormIdentity(Box<[u8]>);

/// Whether a batch parse produced no obligations.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ParseCleanStatus(bool);

impl From<bool> for ParseCleanStatus
{
    /// Wraps the flag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_clean: bool) -> Self
    {
        Self(is_clean)
    }
}

impl From<ParseCleanStatus> for bool
{
    /// Reads the flag back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_clean: ParseCleanStatus) -> Self
    {
        is_clean.0
    }
}

/// The result of a batch parse: the committed tree and its completion
/// obligations.
///
/// The obligations are the melder's buffer at commit — every convex, ghost or
/// incomparable repair the parse made — severity-ordered by
/// [`obligations`](ParseResult::obligations) so consumers render the most
/// serious first. A clean parse has an empty obligation slice.
///
/// # Specification
/// - requires: constructed by [`parse`](fn@crate::parse).
/// - ensures: preserves the committed [`SyntaxTree`] and the parse's
///   obligations exactly; [`obligations`](ParseResult::obligations) is
///   severity-ordered (highest first) then by span.
/// - provides: the batch parse's carrier so obligations are not lost.
/// - fails: never.
/// - panics: none.
/// - executable: none — this type has no call boundary; construction and
///   obligation observation carry its executable invariants.
///
/// # Adequacy
/// - hypothesis: L3 — a clean parse and an obligation-bearing parse distinguish
///   the empty and non-empty obligation slice.
/// - witness: `tests::acceptance::core_forms_are_clean`
/// - witness: `tests::acceptance::malformed_programs_repair_predictably`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseResult<'source>
{
    /// The committed concrete syntax tree.
    tree: SyntaxTree<'source>,
    /// The parse's obligations, severity-ordered (highest first) then by span.
    obligations: Vec<ObligationInstance>,
}

impl<'source> ParseResult<'source>
{
    /// Return the committed concrete syntax tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tree(&self) -> &SyntaxTree<'source>
    {
        &self.tree
    }

    /// Return the parse's obligations, severity-ordered (highest first).
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the buffered obligations sorted by descending
    ///   [`crate::Oblig`] severity, then ascending span.
    /// - provides: the batch obligation surface.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — clean input, distinct severities and repeated classes
    ///   at different source spans are observed through adjacent obligation
    ///   keys; reversed severity and span ties change those ordered keys.
    /// - witness: `parse::tests::obligations_are_reported_in_severity_then_source_order`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| (core::cmp::Reverse(left.class), left.span.start(), left.span.end()) <= (core::cmp::Reverse(right.class), right.span.start(), right.span.end())))]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// Return whether the parse produced no obligations (a clean parse).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_clean(&self) -> ParseCleanStatus
    {
        ParseCleanStatus::from(self.obligations.is_empty())
    }

    /// Return the class of every minted close in the whole tree, in tree
    /// order.
    ///
    /// A ghost's class is **carried**, never reconstructed: the melder records
    /// it when it mints the ghost, from the form-level closing class the
    /// grammar derives, and a ghost whose form has no single such class carries
    /// none. Reading the sequence back is what distinguishes *no ghost was
    /// minted* from *a ghost was minted and carried no class* — which a repair
    /// witness must tell apart, because only the second says the grammar could
    /// not name the closer.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns one entry per [`NodeLabel::GhostClose`] leaf, in tree
    ///   order; unclassed ghosts contribute nothing.
    /// - provides: the minted-close surface a witness reads directly.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested ghosts of distinct families and an unclassed
    ///   repair distinguish depth-first order from arena order, skipped ghosts
    ///   and invented families; a clean tree has no projected closes.
    /// - witness: `parse::tests::minted_closes_follow_depth_first_tree_order`
    /// - witness: `tests::acceptance::an_unclosed_delimiter_yields_to_every_declaration_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| [ClosingClass::Paren, ClosingClass::Bracket, ClosingClass::Brace].into_iter().all(|family| {
        ret.iter().filter(|&&class| class == family).count() == self.tree.positions().filter(|&position| self.tree.node(position).is_some_and(|node| matches!(node.label(), NodeLabel::GhostClose { class, .. } if class == family))).count()
    }))]
    pub fn minted_close_classes(&self) -> Vec<ClosingClass>
    {
        let mut classes = Vec::new();
        let mut pending: Vec<NodeIndex> = Vec::from([self.tree.root()]);
        let mut children: Vec<NodeIndex> = Vec::new();
        while let Some(next) = pending.pop() {
            let Some(node) = self.tree.node(next)
            else {
                continue;
            };
            if let NodeLabel::GhostClose { class, .. } = node.label() {
                classes.push(class);
            }
            children.clear();
            children.extend(self.tree.children(next));
            pending.extend(children.iter().rev().copied());
        }
        classes
    }

    /// Consume the result and return the committed tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_tree(self) -> SyntaxTree<'source>
    {
        self.tree
    }
}

/// Batch-parse `source` over the checked grammar `pbg`.
///
/// The whole front-end, composed: label → mold → fold(push) → commit. Trivia
/// are recorded for losslessness (the committed tree reconstructs the source),
/// and the obligations ride the result.
///
/// ```
/// use gandr_surface_grammar::built_in;
/// use gandr_surface_parser::Oblig;
/// use gandr_surface_parser::parse;
/// use gandr_surface_syntax::SourceText;
///
/// let pbg = built_in()?;
///
/// let whole = parse(&pbg, SourceText::from("def answer = 42;"))?;
/// assert!(bool::from(whole.is_clean()));
///
/// // An unclosed group still yields a tree; the missing `)` is an obligation.
/// let partial = parse(&pbg, SourceText::from("def answer = ( 42 ;"))?;
/// assert!(
///     partial
///         .obligations()
///         .iter()
///         .any(|obligation| obligation.class == Oblig::MissingTile)
/// );
/// # Ok::<(), Box<dyn core::error::Error>>(())
/// ```
///
/// # Specification
/// - requires: `pbg` is a checked grammar; `source` is any UTF-8 text.
/// - ensures: returns a well-formed [`SyntaxTree`] over `source` recording
///   `pbg`'s fingerprint plus the parse's severity-ordered obligations; the
///   committed tree's leaf spans, ordered by offset, reconstruct `source`
///   (losslessness — trivia are recorded as [`NodeLabel::Space`] leaves,
///   digest-skipped but byte-preserving); total over every input.
/// - provides: the batch parse entry point.
/// - fails: returns [`MeldError`] only for an arena-construction failure at
///   commit (arena size or coordinate overflow), never for ungrammatical input.
/// - panics: none.
/// - intension: labels are folded in source order; each non-space token is
///   molded by the obligation-minimizing [`Molder`]; space tokens are recorded
///   verbatim.
///
/// # Errors
/// Returns [`MeldError::Build`] when the flat arena cannot be assembled.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus sources (zero obligations), arbitrary byte
///   soup (totality), incomplete input (statement-local obligations), and
///   losslessness each exercise a distinct property.
/// - witness: `parse::tests::corpus_parses_totally`
/// - witness: `parse::tests::parse_is_lossless_and_hash_stable`
/// - witness: `parse::tests::arbitrary_source_parses_totally`
#[inline]
#[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|parsed| {
    parsed.tree.source() == source && parsed.tree.grammar() == pbg.fingerprint()
        && parsed.tree.node(parsed.tree.root()).is_some_and(|node| node.label() == NodeLabel::Wald)
        && parsed.obligations.iter().zip(parsed.obligations.iter().skip(1)).all(|(left, right)| (core::cmp::Reverse(left.class), left.span.start(), left.span.end()) <= (core::cmp::Reverse(right.class), right.span.start(), right.span.end()))
}))]
pub fn parse<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> Result<ParseResult<'source>, MeldError>
{
    let mut molder = Molder::new(pbg);
    let mut state = MeldState::new(pbg);
    let tokens = label(SourceFragment::from(<&str>::from(source)));
    molder.mold_stream(&mut state, &tokens, source);
    commit(state, source)
}

/// Commit a molded state over `source` as a parse result.
///
/// # Specification
/// - requires: `state` holds exactly `source`'s tokens, molded.
/// - ensures: the committed tree beside the completion's obligations,
///   severity-ordered (highest first) then by span.
/// - fails: [`MeldError`] when the state's source is not `source` or the arena
///   cannot be built.
/// - panics: none.
///
/// # Errors
/// The commit's [`MeldError`].
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
///   four fragments commit through the whole parse and the joined form split
///   alike; an unsorted or truncated obligation list changes both results.
/// - witness: `parse::tests::obligations_are_reported_in_severity_then_source_order`
/// - witness: `parse::tests::form_split_parses_as_the_whole_source`
/// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|parsed| parsed.tree.source() == source && parsed.obligations.iter().zip(parsed.obligations.iter().skip(1)).all(|(left, right)| (core::cmp::Reverse(left.class), left.span.start(), left.span.end()) <= (core::cmp::Reverse(right.class), right.span.start(), right.span.end()))))]
fn commit<'source>(
    state: MeldState<'_>,
    source: SourceText<'source>,
) -> Result<ParseResult<'source>, MeldError>
{
    // `commit_with_obligations` captures the completion's repairs (force-close
    // and missing-operand obligations flagged while closing the input), which a
    // bare `commit` would drop.
    let (tree, mut obligations) = state.commit_with_obligations(source)?;
    // Severity-ordered (highest first) then by span, so consumers render the
    // most serious repair first.
    obligations.sort_by(|left, right| {
        right
            .class
            .cmp(&left.class)
            .then_with(|| left.span.start().cmp(&right.span.start()))
            .then_with(|| left.span.end().cmp(&right.span.end()))
    });
    Ok(ParseResult { tree, obligations })
}

/// One source split at its predicted top-level form boundaries, so its forms
/// mold apart and join into the source's parse.
///
/// [`new`](Self::new) labels the source once, or
/// [`labeled`](Self::labeled) takes a labeling already made — an edited
/// revision's ([`Labeling::relabel`]) — and predicts the boundaries
/// ([`Molder::form_runs`]). [`mold`](Self::mold) molds one run into a
/// [`FormUnit`] that depends on no other, so the runs of every source can
/// mold in parallel, longest first. [`join`](Self::join) joins the units in
/// run order and commits.
///
/// The form boundary is the parser's contract: the joined result equals
/// [`parse`](fn@crate::parse) of the same source. A unit whose seam holds
/// keeps its own molding; a unit whose seam breaks — the boundary was not a
/// real one, or the unit's fold reached past it — is molded onto the state
/// before it, which is the whole parse's own step.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `labeling` is the labeling of `source`; `runs` is the molder's
///   form runs of its tokens.
/// - panics: none.
/// - executable: none — this data type has no call boundary; its constructor
///   and the join carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
///   four fragments parse by form as they parse whole; a dropped seam check or
///   a run molded without its lookahead changes a tree or an obligation.
/// - witness: `parse::tests::form_split_parses_as_the_whole_source`
/// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
#[derive(Clone, Debug)]
pub struct FormSplit<'source>
{
    /// The source text.
    source: SourceText<'source>,
    /// Its labeling.
    labeling: Labeling,
    /// Its form runs, in source order.
    runs: Vec<TokenRun>,
}

impl<'source> FormSplit<'source>
{
    /// Label `source` and predict its form runs with `molder`'s grammar.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the labeling of `source` and the molder's form runs of it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source of several declarations splits before each
    ///   head; a stale or partial labeling moves a run.
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.source == source && ret.labeling.tokens() == label(SourceFragment::from(<&str>::from(source))) && ret.runs == molder.form_runs(ret.labeling.tokens(), source))]
    pub fn new(
        molder: &Molder<'_>,
        source: SourceText<'source>,
    ) -> Self
    {
        Self::labeled(
            molder,
            source,
            Labeling::new(SourceFragment::from(<&str>::from(source))),
        )
    }

    /// Predict the form runs of `source`, whose labeling `labeling` is, with
    /// `molder`'s grammar.
    ///
    /// # Specification
    /// - requires: `labeling` is the labeling of `source`.
    /// - ensures: the split [`new`](Self::new) makes of `source`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — generated edits of every class submit through a
    ///   session that relabels each revision as the batch composition of the
    ///   revision submits.
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    #[inline]
    #[must_use]
    #[spec(requires: labeling == Labeling::new(SourceFragment::from(<&str>::from(source))),
        ensures: |ret| ret.source == source && ret.runs == molder.form_runs(ret.labeling.tokens(), source))]
    pub fn labeled(
        molder: &Molder<'_>,
        source: SourceText<'source>,
        labeling: Labeling,
    ) -> Self
    {
        let runs = molder.form_runs(labeling.tokens(), source);
        Self {
            source,
            labeling,
            runs,
        }
    }

    /// Give the split's labeling back, for the next revision to relabel.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_labeling(self) -> Labeling
    {
        self.labeling
    }

    /// The predicted form runs, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn runs(&self) -> &[TokenRun]
    {
        &self.runs
    }

    /// The identity of `run`: what its molding depends on, spelled out.
    ///
    /// A unit molds the run's tokens and reads, as lookahead, the tokens
    /// past the run up to the eighth significant one; it begins from the
    /// empty slope when the run starts the source and from the form-boundary
    /// stand-in otherwise. The spelling covers exactly those: the base, the
    /// run's length in tokens, each token's lexical class and end relative to
    /// the run's first byte, and the bytes from the run's first token to the
    /// last token read.
    ///
    /// # Specification
    /// - requires: `run` is one of [`runs`](Self::runs); a run past the tokens
    ///   covers what of it lies inside them.
    /// - ensures: one byte for the base (one past the source's start), the
    ///   run's token count as eight little-endian bytes, then per window token
    ///   one byte for its class and its relative end as four little-endian
    ///   bytes, then the window's bytes.
    /// - provides: the key a parked unit is reused under across revisions.
    /// - panics: none.
    /// - executable: none — the spelling restates the window; its contract,
    ///   that equal spellings mold equal units, only molding both runs
    ///   observes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over edited corpus sources, every run whose identity
    ///   a run of the unedited source carries molds to an equal unit, and the
    ///   run whose lookahead the edit reaches does not keep its identity; a
    ///   window short of the lookahead, or a spelling blind to the base or the
    ///   token classes, reuses a unit the run would not mold.
    /// - witness: `parse::tests::an_equal_identity_molds_an_equal_unit`
    /// - witness: `parse::tests::hostile_edits_reuse_only_equal_units`
    /// - witness: `mold::tests::a_run_reads_eight_significant_tokens_past_its_end`
    #[inline]
    #[must_use]
    pub fn identity(
        &self,
        run: TokenRun,
    ) -> FormIdentity
    {
        let tokens = self.labeling.tokens();
        let start = usize::from(run.start()).min(tokens.len());
        let end = usize::from(run.end()).clamp(start, tokens.len());
        let reach = usize::from(lookahead_reach(tokens, TokenIndex::from(end)));
        let window = tokens.get(start .. reach).unwrap_or_default();
        let origin = window.first().map_or(0, |token| token.start);
        let bytes_end = window.last().map_or(origin, |token| token.end);
        let bytes = <&str>::from(self.source)
            .as_bytes()
            .get(
                usize::try_from(origin).unwrap_or(usize::MAX)
                    .. usize::try_from(bytes_end).unwrap_or(usize::MAX),
            )
            .unwrap_or_default();
        let length = u64::try_from(end.saturating_sub(start)).unwrap_or(u64::MAX);
        let mut spelling = Vec::with_capacity(
            9_usize
                .saturating_add(window.len().saturating_mul(5))
                .saturating_add(bytes.len()),
        );
        spelling.push(u8::from(start != 0));
        spelling.extend_from_slice(&length.to_le_bytes());
        for token in window {
            spelling.push(match token.lexeme {
                | Lexeme::LowerWord => 0_u8,
                | Lexeme::UpperWord => 1,
                | Lexeme::Number => 2,
                | Lexeme::TypedNumber => 3,
                | Lexeme::Character => 4,
                | Lexeme::Quote => 5,
                | Lexeme::StringFragment => 6,
                | Lexeme::EscapeSequence => 7,
                | Lexeme::Punct => 8,
                | Lexeme::ShellWord => 9,
                | Lexeme::EnvAssign => 10,
                | Lexeme::SingleQuotedContent => 11,
                | Lexeme::VariableName => 12,
                | Lexeme::SubshellOpen => 13,
                | Lexeme::SubshellClose => 14,
                | Lexeme::FileDescriptor => 15,
                | Lexeme::Space => 16,
                | Lexeme::Unknown => 17,
                | Lexeme::ShellStringFragment => 18,
            });
            spelling.extend_from_slice(&token.end.saturating_sub(origin).to_le_bytes());
        }
        spelling.extend_from_slice(bytes);
        FormIdentity(spelling.into_boxed_slice())
    }

    /// Mold `run` into its form unit.
    ///
    /// # Specification
    /// - requires: `run` is one of [`runs`](Self::runs).
    /// - ensures: [`Molder::mold_unit`] of `run` over this split's tokens.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
    ///   four fragments parse by form as they parse whole; a unit molded over
    ///   another source's tokens changes the joined tree.
    /// - witness: `parse::tests::form_split_parses_as_the_whole_source`
    /// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.run() == run)]
    pub fn mold<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        run: TokenRun,
    ) -> FormUnit<'pbg>
    {
        molder.mold_unit(self.labeling.tokens(), run, self.source)
    }

    /// Join `units`, one per run in run order, and commit the source's parse.
    ///
    /// # Specification
    /// - requires: `units` are this split's units, one per run, in run order,
    ///   molded over `molder`'s grammar.
    /// - ensures: the parse equals [`parse`](fn@crate::parse) of the source;
    ///   the seams are how each unit met the state before it, in run order.
    /// - fails: [`MeldError`] when the commit's arena cannot be built.
    /// - panics: none.
    ///
    /// # Errors
    /// The commit's [`MeldError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every corpus source and 400 hostile sources of one to
    ///   four fragments parse by form as they parse whole, and a source with a
    ///   broken seam still does; a join that skipped a broken run or committed
    ///   a unit alone changes the result.
    /// - witness: `parse::tests::form_split_parses_as_the_whole_source`
    /// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
    /// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
    #[inline]
    #[spec(captures: before = units.len(), ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|joined| joined.result.tree.source() == self.source && joined.seams.len() == before))]
    pub fn join<'pbg>(
        &self,
        molder: &mut Molder<'pbg>,
        units: Vec<FormUnit<'pbg>>,
    ) -> Result<FormJoin<'source>, MeldError>
    {
        let mut whole = MeldState::new(molder.pbg());
        let mut seams = Vec::with_capacity(units.len());
        for unit in units {
            seams.push(molder.join_unit(&mut whole, unit, self.labeling.tokens(), self.source));
        }
        let result = commit(whole, self.source)?;
        Ok(FormJoin { result, seams })
    }
}

/// A source's parse joined from its form units, and how each seam stood.
///
/// # Specification
/// - requires: constructed by [`FormSplit::join`].
/// - ensures: the parse equals the whole parse; one seam per unit, in run
///   order.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the join carries
///   the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a split source reports a held seam per real boundary and
///   a broken one per false boundary; a miscounted seam changes the report.
/// - witness: `parse::tests::a_source_splits_before_each_declaration_head`
#[derive(Clone, Debug)]
pub struct FormJoin<'source>
{
    /// The joined parse.
    result: ParseResult<'source>,
    /// How each unit met the state before it, in run order.
    seams: Vec<UnitSeam>,
}

impl<'source> FormJoin<'source>
{
    /// The joined parse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn result(&self) -> &ParseResult<'source>
    {
        &self.result
    }

    /// How each unit met the state before it, in run order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn seams(&self) -> &[UnitSeam]
    {
        &self.seams
    }

    /// Consume the join and return its parse.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_result(self) -> ParseResult<'source>
    {
        self.result
    }
}

/// Batch-parse `source` by its top-level forms: split, mold each form run
/// apart, join.
///
/// The serial reference of [`FormSplit`]: a caller with a pool molds the
/// runs of [`FormSplit::runs`] on it instead.
///
/// # Specification
/// - requires: `pbg` is a checked grammar; `source` is any UTF-8 text.
/// - ensures: the result [`parse`](fn@crate::parse) returns for the same
///   source.
/// - fails: [`MeldError`] exactly when [`parse`](fn@crate::parse) fails.
/// - panics: none.
///
/// # Errors
/// The commit's [`MeldError`].
///
/// # Adequacy
/// - hypothesis: L2 — 400 hostile sources of one to four fragments, one per
///   line, mixing byte soup with whole and truncated declarations, parse by
///   form as they parse whole; any seam held where the whole parse would have
///   reached across it changes a tree. The corpus witness drives the same steps
///   through [`FormSplit`].
/// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
#[inline]
#[spec(ensures: |ret| match (ret.as_ref(), parse(pbg, source)) { (Ok(by_form), Ok(whole)) => *by_form == whole, (Err(_), Err(_)) => true, (Ok(_), Err(_)) | (Err(_), Ok(_)) => false })]
pub fn parse_by_form<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> Result<ParseResult<'source>, MeldError>
{
    let mut molder = Molder::new(pbg);
    let split = FormSplit::new(&molder, source);
    let units: Vec<FormUnit<'_>> = split
        .runs()
        .iter()
        .map(|&run| split.mold(&mut molder, run))
        .collect();
    Ok(split.join(&mut molder, units)?.into_result())
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;
    use core::fmt;
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use proptest::prelude::*;

    use super::FormIdentity;
    use super::FormSplit;
    use super::ParseResult;
    use super::parse;
    use super::parse_by_form;
    use crate::FormUnit;
    use crate::Molder;
    use crate::ParkedUnit;
    use crate::SeamBreak;
    use crate::UnitSeam;
    use crate::label::label;
    use crate::testing::reconstruct;
    use crate::testing::root_digest;

    /// File-read failure with the example path preserved.
    #[derive(Debug)]
    struct ReadSourceError
    {
        /// The file that failed to read.
        path: PathBuf,
        /// The underlying failure.
        source: std::io::Error,
    }

    impl fmt::Display for ReadSourceError
    {
        /// # Specification
        /// - ensures: the message names the requested path and original cause.
        /// - fails: propagates the formatter's write failure.
        /// - panics: none.
        /// - executable: none — the formatter's sink is write-only; observing
        ///   the emitted bytes would require replaying its side effects.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a directory read failure retains its path and
        ///   cause in the message; a rejecting sink detects swallowed errors.
        /// - witness: `parse::tests::source_reads_preserve_text_and_failure_context`
        fn fmt(
            &self,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result
        {
            write!(f, "failed to read {}: {}", self.path.display(), self.source)
        }
    }

    impl Error for ReadSourceError
    {
        /// # Specification
        /// trivial.
        fn source(&self) -> Option<&(dyn Error + 'static)>
        {
            Some(&self.source)
        }
    }

    #[test]
    fn obligations_are_reported_in_severity_then_source_order()
    {
        let pbg = built_in().unwrap();
        let mut distinct_severity = false;
        let mut distinct_span = false;
        for source in ["", "def x = 1;", "def a = ( ; # def b = [ ;", "def = ; ? ?"] {
            let parsed = parse(&pbg, SourceText::from(source)).unwrap();
            let obligations = parsed.obligations();
            for (left, right) in obligations.iter().zip(obligations.iter().skip(1)) {
                assert!(left.class >= right.class);
                if left.class == right.class {
                    assert!(left.span <= right.span);
                    distinct_span |= left.span != right.span;
                }
                else {
                    distinct_severity = true;
                }
            }
        }
        assert!(distinct_severity, "the fixtures separate severity order");
        assert!(distinct_span, "the fixtures separate source-order ties");
    }

    #[test]
    fn minted_closes_follow_depth_first_tree_order()
    {
        use gandr_surface_syntax::ByteOffset;
        use gandr_surface_syntax::ByteSpan;
        use gandr_surface_syntax::ClosingClass;
        use gandr_surface_syntax::GrammarFingerprint;
        use gandr_surface_syntax::GroutShape;
        use gandr_surface_syntax::GroutSort;
        use gandr_surface_syntax::MoldId;
        use gandr_surface_syntax::NodeLabel;
        use gandr_surface_syntax::TreeBuilder;
        let empty = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(0_usize)).unwrap();
        let mut builder =
            TreeBuilder::new(SourceText::from(""), GrammarFingerprint::from(0_u64)).unwrap();
        let inner = builder
            .node(
                NodeLabel::GhostClose {
                    sort: GroutSort::from(0_u16),
                    class: ClosingClass::Brace,
                },
                empty,
                &[],
            )
            .unwrap();
        let form = builder
            .node(NodeLabel::Meld(MoldId::from(0_u32)), empty, &[inner])
            .unwrap();
        let unclassed = builder
            .node(
                NodeLabel::Grout {
                    sort: GroutSort::from(0_u16),
                    shape: GroutShape::Postfix,
                },
                empty,
                &[],
            )
            .unwrap();
        let outer = builder
            .node(
                NodeLabel::GhostClose {
                    sort: GroutSort::from(0_u16),
                    class: ClosingClass::Paren,
                },
                empty,
                &[],
            )
            .unwrap();
        let root = builder
            .node(NodeLabel::Wald, empty, &[form, unclassed, outer])
            .unwrap();
        let parsed = super::ParseResult {
            tree: builder.finish(root).unwrap(),
            obligations: Vec::new(),
        };
        assert_eq!(parsed.minted_close_classes(), [
            ClosingClass::Brace,
            ClosingClass::Paren
        ]);
        let pbg = built_in().unwrap();
        assert!(
            parse(&pbg, SourceText::from("def x = 1;"))
                .unwrap()
                .minted_close_classes()
                .is_empty()
        );
    }

    #[test]
    fn source_inventory_is_sorted_and_excludes_non_sources()
    {
        let root = corpus_root();
        let paths = gandr_files(&root);
        assert!(paths.contains(&root.join("strict/values.gandr")));
        assert!(paths.contains(&root.join("fixture/surface/typed-holes.gandr")));
        assert!(
            paths
                .iter()
                .all(|path| path.extension().is_some_and(|ext| ext == "gandr"))
        );
        assert!(
            paths
                .iter()
                .zip(paths.iter().skip(1))
                .all(|(left, right)| left <= right)
        );
        assert!(gandr_files(&root.join("strict/values.gandr/child")).is_empty());
    }

    #[test]
    fn source_reads_preserve_text_and_failure_context()
    {
        use core::fmt::Write as _;
        let root = corpus_root();
        assert_eq!(
            read_source(&root.join("strict/values.gandr")).unwrap(),
            include_str!("../../surface-corpus/strict/values.gandr")
        );
        let error = read_source(&root).unwrap_err();
        assert_eq!(error.path, root);
        let rendered = alloc::format!("{error}");
        assert!(rendered.contains(&alloc::format!("{}", root.display())));
        assert!(rendered.contains(&alloc::format!("{}", error.source)));
        assert!(
            crate::testing::RefusingSink
                .write_fmt(format_args!("{error}"))
                .is_err()
        );
    }

    #[test]
    fn corpus_parses_totally() -> Result<(), Box<dyn Error>>
    {
        // Every corpus source parses totally — no panic, a well-formed tree
        // recording the grammar fingerprint, and its leaves reconstruct the
        // source. The stronger zero-obligation gate is
        // `acceptance::corpus_molds_to_zero_obligations`; this is the floor.
        let pbg = built_in()?;
        let files = gandr_files(&corpus_root());
        assert!(!files.is_empty(), "the corpus sources are present");

        for path in &files {
            let src = read_source(path)?;
            let result = parse(&pbg, SourceText::from(src.as_str()))?;
            assert_eq!(result.tree().grammar(), pbg.fingerprint());
            assert_eq!(
                reconstruct(result.tree()),
                src,
                "{:?} reconstructs losslessly",
                path.file_name()
            );
        }
        Ok(())
    }

    /// Every `.gandr` file under `dir`, sorted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a walk of `dir` and its subdirectories, unreadable entries
    ///   skipped, the paths sorted so a run is deterministic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested checked-in source tree and a path below a
    ///   regular file separate traversal from unreadable-directory refusal.
    ///   Exact nested members, suffixes and sorted paths detect shallow-only
    ///   walks, wrong extensions and nondeterministic ordering.
    /// - witness: `parse::tests::source_inventory_is_sorted_and_excludes_non_sources`
    #[spec(ensures: |ret| ret.iter().all(|path| path.starts_with(dir) && path.extension().is_some_and(|ext| ext == "gandr"))
        && ret.iter().zip(ret.iter().skip(1)).all(|(left, right)| left <= right))]
    fn gandr_files(dir: &Path) -> Vec<PathBuf>
    {
        let mut out = Vec::new();
        let mut pending = vec![dir.to_path_buf()];
        while let Some(next_dir) = pending.pop() {
            if let Ok(entries) = std::fs::read_dir(next_dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.is_dir() {
                        pending.push(path);
                    }
                    else if path.extension().is_some_and(|ext| ext == "gandr") {
                        out.push(path);
                    }
                }
            }
        }
        out.sort();
        out
    }

    /// The language's source corpus, which the corpus crate owns.
    ///
    /// # Specification
    /// trivial.
    fn corpus_root() -> PathBuf
    {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus")
    }

    /// Read a source file while retaining path context in the error.
    ///
    /// # Specification
    /// - ensures: success returns the file's UTF-8 text; failure retains the
    ///   exact requested path and original I/O error.
    /// - fails: propagates unreadable files and invalid UTF-8 with path
    ///   context.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a checked-in source and a directory path distinguish
    ///   byte-preserving success from a contextualized refusal. Exact source
    ///   text and the path/cause observers detect truncation and lost context.
    /// - witness: `parse::tests::source_reads_preserve_text_and_failure_context`
    ///
    /// # Errors
    /// The read failure, carrying `path`.
    #[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| error.path == path))]
    fn read_source(path: &Path) -> Result<String, ReadSourceError>
    {
        std::fs::read_to_string(path).map_err(|source| ReadSourceError {
            path: path.to_path_buf(),
            source,
        })
    }

    #[test]
    fn parse_is_lossless_and_hash_stable() -> Result<(), Box<dyn Error>>
    {
        // Losslessness: the committed tree's tile and layout leaves
        // reconstruct the exact source, including interleaved comments.
        let pbg = built_in()?;
        let src = r#"// a comment
def greeting = "hi";

ret greeting
"#;
        let result = parse(&pbg, SourceText::from(src))?;
        assert_eq!(
            reconstruct(result.tree()),
            src,
            "the committed tree reconstructs the source"
        );

        // Determinism: a second parse digests identically.
        let again = parse(&pbg, SourceText::from(src))?;
        assert_eq!(root_digest(result.tree()), root_digest(again.tree()));
        Ok(())
    }

    #[test]
    fn form_split_parses_as_the_whole_source() -> Result<(), Box<dyn Error>>
    {
        // Every corpus source, molded form by form and joined, parses exactly
        // as it parses whole: the same tree and the same obligations, whether
        // its seams hold or break.
        let pbg = built_in()?;
        let files = gandr_files(&corpus_root());
        assert!(!files.is_empty(), "the corpus sources are present");
        let mut molder = Molder::new(&pbg);
        for path in &files {
            let src = read_source(path)?;
            let source = SourceText::from(src.as_str());
            let whole = parse(&pbg, source)?;
            let split = FormSplit::new(&molder, source);
            let units: Vec<_> = split
                .runs()
                .iter()
                .map(|&run| split.mold(&mut molder, run))
                .collect();
            let joined = split.join(&mut molder, units)?;
            assert_eq!(
                *joined.result(),
                whole,
                "{} parses by form as whole",
                path.display()
            );
        }
        Ok(())
    }

    #[test]
    fn a_source_splits_before_each_declaration_head() -> Result<(), Box<dyn Error>>
    {
        // Five declarations: a plain one, an attributed one, a module whose
        // members sit inside its braces, a data declaration followed by an
        // expression statement, and one after that statement. The split cuts
        // before each top-level head and nowhere else; every seam holds but
        // the last, which follows a statement rather than a declaration.
        let pbg = built_in()?;
        let src = "def a = 1;\n@[doc(\"b\")] def b = 2;\nmodule M {\n  def c = 3;\n  def d = 4;\n}\ndata Bit : Type {\n  Off : Bit;\n}\n1;\ndef e = 5;\n";
        let source = SourceText::from(src);
        let mut molder = Molder::new(&pbg);
        let split = FormSplit::new(&molder, source);
        let tokens = label(SourceFragment::from(src));
        let heads: Vec<&str> = split
            .runs()
            .iter()
            .filter_map(|run| tokens.get(usize::from(run.start())))
            .filter_map(|token| {
                src.get(usize::try_from(token.start).ok()? .. usize::try_from(token.end).ok()?)
            })
            .collect();
        assert_eq!(heads, ["def", "@[", "module", "data", "def"]);
        let units: Vec<_> = split
            .runs()
            .iter()
            .map(|&run| split.mold(&mut molder, run))
            .collect();
        let joined = split.join(&mut molder, units)?;
        assert_eq!(joined.seams(), [
            UnitSeam::Joined,
            UnitSeam::Joined,
            UnitSeam::Joined,
            UnitSeam::Joined,
            UnitSeam::Broken(SeamBreak::SortMismatch),
        ]);
        assert_eq!(*joined.result(), parse(&pbg, source)?);
        Ok(())
    }

    #[test]
    fn a_parked_unit_joins_as_the_unit_it_parked() -> Result<(), Box<dyn Error>>
    {
        // Every corpus source's units, parked and taken up again, meet the
        // seams the fresh units met and join into the whole parse.
        let pbg = built_in()?;
        let files = gandr_files(&corpus_root());
        assert!(!files.is_empty(), "the corpus sources are present");
        let mut molder = Molder::new(&pbg);
        for path in &files {
            let src = read_source(path)?;
            let source = SourceText::from(src.as_str());
            let split = FormSplit::new(&molder, source);
            let fresh: Vec<_> = split
                .runs()
                .iter()
                .map(|&run| split.mold(&mut molder, run))
                .collect();
            let parked: Vec<ParkedUnit> = fresh.iter().map(FormUnit::park).collect();
            let resumed: Vec<_> = split
                .runs()
                .iter()
                .zip(&parked)
                .map(|(&run, parked)| FormUnit::resume(&pbg, run, parked))
                .collect();
            let fresh = split.join(&mut molder, fresh)?;
            let resumed = split.join(&mut molder, resumed)?;
            assert_eq!(resumed.seams(), fresh.seams(), "{}", path.display());
            assert_eq!(
                *resumed.result(),
                parse(&pbg, source)?,
                "{}",
                path.display()
            );
        }
        Ok(())
    }

    /// How many units a rejoin took up rather than molded.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Reused(usize);

    /// Mold every run of `after`, take up the unit `parked` holds under a
    /// run's identity in place of the fresh one, and join.
    ///
    /// # Specification
    /// - requires: `parked` holds units molded over `molder`'s grammar.
    /// - ensures: each run whose identity `parked` holds molds to the parked
    ///   unit; the answer is the join of the taken-up and fresh units and how
    ///   many were taken up.
    /// - fails: the join's [`MeldError`], or a description of the first run
    ///   whose fresh unit differs from the parked unit under its identity.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus and hostile edit witnesses call it on
    ///   every edited source they build.
    /// - witness: `parse::tests::an_equal_identity_molds_an_equal_unit`
    /// - witness: `parse::tests::hostile_edits_reuse_only_equal_units`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(_, Reused(reused))| reused <= after.runs().len()))]
    fn rejoin<'source>(
        molder: &mut Molder<'_>,
        after: &FormSplit<'source>,
        parked: &BTreeMap<FormIdentity, ParkedUnit>,
    ) -> Result<(ParseResult<'source>, Reused), Box<dyn Error>>
    {
        let pbg = molder.pbg();
        let mut units = Vec::with_capacity(after.runs().len());
        let mut reused = 0_usize;
        for &run in after.runs() {
            let fresh = after.mold(molder, run);
            match parked.get(&after.identity(run)) {
                | Some(unit) => {
                    if fresh.park() != *unit {
                        return Err(
                            format!("{run:?} molds otherwise than its identity's unit").into()
                        );
                    }
                    units.push(FormUnit::resume(pbg, run, unit));
                    reused = reused.saturating_add(1);
                },
                | None => units.push(fresh),
            }
        }
        Ok((after.join(molder, units)?.into_result(), Reused(reused)))
    }

    /// Every unit of `split`, parked under its run's identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per distinct identity among the runs.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus and hostile edit witnesses park every
    ///   unedited source through it.
    /// - witness: `parse::tests::an_equal_identity_molds_an_equal_unit`
    /// - witness: `parse::tests::hostile_edits_reuse_only_equal_units`
    #[spec(ensures: |ret| ret.len() <= split.runs().len())]
    fn parked_by_identity(
        molder: &mut Molder<'_>,
        split: &FormSplit<'_>,
    ) -> BTreeMap<FormIdentity, ParkedUnit>
    {
        split
            .runs()
            .iter()
            .map(|&run| (split.identity(run), split.mold(molder, run).park()))
            .collect()
    }

    #[test]
    fn an_equal_identity_molds_an_equal_unit() -> Result<(), Box<dyn Error>>
    {
        // Each corpus source of three forms or more, a declaration inserted
        // at its middle boundary: every run of the edited source whose
        // identity a run of the original carries molds to that run's unit,
        // the run before the insertion — whose lookahead now reads the new
        // declaration — takes a new identity, and the edited source joined
        // from reused and fresh units parses whole.
        let pbg = built_in()?;
        let mut molder = Molder::new(&pbg);
        let mut edited_sources = 0_usize;
        let mut reused_units = 0_usize;
        for path in gandr_files(&corpus_root()) {
            let src = read_source(&path)?;
            let before = FormSplit::new(&molder, SourceText::from(src.as_str()));
            if before.runs().len() < 3 {
                continue;
            }
            let middle = before.runs().len().div_euclid(2);
            let (Some(&previous), Some(&run)) = (
                before.runs().get(middle.saturating_sub(1)),
                before.runs().get(middle),
            )
            else {
                continue;
            };
            let tokens = label(SourceFragment::from(src.as_str()));
            let at = tokens
                .get(usize::from(run.start()))
                .and_then(|token| usize::try_from(token.start).ok())
                .ok_or("the middle run starts at a token")?;
            let (head, tail) = src
                .split_at_checked(at)
                .ok_or("a token starts at a character")?;
            let edited = format!("{head}def inserted = 1;\n{tail}");
            let parked = parked_by_identity(&mut molder, &before);
            let after = FormSplit::new(&molder, SourceText::from(edited.as_str()));
            assert_eq!(after.runs().get(middle.saturating_sub(1)), Some(&previous));
            assert!(
                !parked.contains_key(&after.identity(previous)),
                "{}: the run before the insertion reads it as lookahead",
                path.display()
            );
            let (joined, Reused(reused)) = rejoin(&mut molder, &after, &parked)?;
            assert_eq!(
                joined,
                parse(&pbg, SourceText::from(edited.as_str()))?,
                "{}",
                path.display()
            );
            edited_sources = edited_sources.saturating_add(1);
            reused_units = reused_units.saturating_add(reused);
        }
        assert!(
            edited_sources > 0,
            "the corpus holds sources of three forms"
        );
        assert!(
            reused_units >= edited_sources,
            "every edited source reuses a unit"
        );
        Ok(())
    }

    #[test]
    fn declaration_prefix_round_trips_and_snapshots_model_state() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let src = r#"def nth @[A : Type, i : Fin(length(xs))] (xs : List(A)) -> A {
  ret xs
}
"#;
        let result = parse(&pbg, SourceText::from(src))?;
        assert!(
            result.obligations().is_empty(),
            "the declaration prefix needs no completion: {:?}",
            result.obligations()
        );
        assert_eq!(
            result.tree().grammar(),
            pbg.fingerprint(),
            "the tree records the grammar that produced it"
        );
        assert_eq!(
            reconstruct(result.tree()),
            src,
            "the tree round-trips the raw multiline source"
        );

        let again = parse(&pbg, SourceText::from(src))?;
        assert_eq!(
            root_digest(result.tree()),
            root_digest(again.tree()),
            "the declaration-prefix parse is deterministic"
        );
        Ok(())
    }

    /// A biased strategy: byte soup, fragment mutations, and truncations.
    ///
    /// # Specification
    /// - ensures: samples UTF-8 byte-soup renderings and full or truncated
    ///   source fragments, including empty input.
    /// - executable: none — the opaque Strategy exposes a generated value only
    ///   through a random value tree; a separate sample cannot inspect the
    ///   returned strategy.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — 400 generated sources observe grammar identity and
    ///   exact source reconstruction after real parsing. Invalid bytes become
    ///   replacement characters before parsing; sampling does not exhaust
    ///   malformed programs or imply a distribution guarantee.
    /// - witness: `parse::tests::arbitrary_source_parses_totally`
    /// - witness: `parse::tests::arbitrary_source_parses_by_form_as_whole`
    fn hostile_source() -> impl Strategy<Value = String>
    {
        // A pool of gandr fragments to mutate and truncate.
        let fragments = vec![
            "def x = 1;",
            "fn(a) { ret a }",
            "case v { Inl(x) => x, Inr(y) => y }",
            "if c { ret 1 } else { ret 2 }",
            "#{ a = 1, b = \"s\" }",
            "[1, 2, 3] ++ [4]",
            "#!{ echo hi; }",
            "@[doc(\"d\")] def y = 2;",
        ];
        prop_oneof![
            // Byte soup.
            prop::collection::vec(any::<u8>(), 0 .. 64)
                .prop_map(|bytes| String::from_utf8_lossy(&bytes).into_owned()),
            // A fragment, possibly truncated.
            (prop::sample::select(fragments), 0_usize .. 40).prop_map(|(frag, cut)| {
                let end = cut.min(frag.len());
                frag.get(.. end).unwrap_or(frag).to_owned()
            }),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(400))]

        #[test]
        fn arbitrary_source_parses_totally(src in hostile_source()) {
            use std::sync::OnceLock;
            static PBG: OnceLock<Pbg> = OnceLock::new();
            let pbg = PBG.get_or_init(|| built_in().expect("built-in grammar"));

            // Parse never panics and always yields a well-formed tree.
            let parse_result = parse(pbg, SourceText::from(src.as_str())).expect("commit is total");
            prop_assert_eq!(parse_result.tree().grammar(), pbg.fingerprint());

            // Losslessness holds over arbitrary input.
            prop_assert_eq!(reconstruct(parse_result.tree()), src);
        }

        #[test]
        fn arbitrary_source_parses_by_form_as_whole(
            parts in prop::collection::vec(hostile_source(), 1 .. 5),
        ) {
            use std::sync::OnceLock;
            static PBG: OnceLock<Pbg> = OnceLock::new();
            let pbg = PBG.get_or_init(|| built_in().expect("built-in grammar"));

            // Several hostile fragments, one per line, so the split has
            // boundaries to predict, hold and break.
            let src = parts.join("\n");
            let whole = parse(pbg, SourceText::from(src.as_str())).expect("commit is total");
            let by_form = parse_by_form(pbg, SourceText::from(src.as_str())).expect("commit is total");
            prop_assert_eq!(by_form, whole);
        }
    }

    proptest! {
        // Each case molds, parks, splits and joins twice, so the enforcing
        // lane, whose checked clauses multiply that cost, draws fewer.
        #![proptest_config(ProptestConfig::with_cases(if cfg!(anodized_panic) { 64 } else { 400 }))]

        #[test]
        fn hostile_edits_reuse_only_equal_units(
            parts in prop::collection::vec(hostile_source(), 2 .. 6),
            replacement in hostile_source(),
            slot in any::<prop::sample::Index>(),
        ) {
            use std::sync::OnceLock;
            static PBG: OnceLock<Pbg> = OnceLock::new();
            let pbg = PBG.get_or_init(|| built_in().expect("built-in grammar"));

            // One hostile fragment of several replaced by another: every run
            // of the edited source that keeps an identity of the original
            // molds to the original's unit, and the edited source joined
            // from reused and fresh units parses whole.
            let before = parts.join("\n");
            let mut edited_parts = parts;
            let at = slot.index(edited_parts.len());
            if let Some(part) = edited_parts.get_mut(at) {
                *part = replacement;
            }
            let edited = edited_parts.join("\n");
            let mut molder = Molder::new(pbg);
            let unedited = FormSplit::new(&molder, SourceText::from(before.as_str()));
            let parked = parked_by_identity(&mut molder, &unedited);
            let after = FormSplit::new(&molder, SourceText::from(edited.as_str()));
            let (joined, _reused) = rejoin(&mut molder, &after, &parked).expect("equal identities mold equal units");
            prop_assert_eq!(joined, parse(pbg, SourceText::from(edited.as_str())).expect("commit is total"));
        }
    }
}
