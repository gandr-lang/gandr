//! The two readings of a description's rules made one.
//!
//! # Two readings, one meaning
//!
//! A `data` family's rules are read twice. The operation route compiles an
//! operation's rules, in the order written, to a decision tree whose first
//! matching rule fires (`operation`); the cell layer reads every rule as an
//! equation between commands and rewrites with whichever cell matches. The two
//! agree on every call when the rules terminate and every critical pair — two
//! rules matching one term — joins: the rewriting is then confluent, every
//! strategy reaches the one normal form, and first match is one strategy
//! (Newman's lemma with the critical-pair lemma). [`decide`] decides both
//! halves for every `data` and `sign` block with rules, at `checks`:
//!
//! 1. Termination, by the lexicographic path order over the block's faces
//!    (`orient_rules`; the order and why it is not the cell layer's own are in
//!    that function's crate). The first rule it does not orient is refused as
//!    [`LoweringRefusal::RulesUnoriented`] at that rule.
//! 2. Joinability of every critical pair over the block's own cells
//!    (`join_critical_pairs`). A pair whose normal forms differ is refused as
//!    [`LoweringRefusal::RulesDiverge`] at the later rule, naming the earlier
//!    one, the peak and both normal forms kept in the cell diagnostic
//!    ([`CoherenceFault::Diverges`]). A pair a reduct of which reaches no
//!    normal form within [`JOIN_STEPS`] steps is refused as
//!    [`LoweringRefusal::RulesUndecided`], which reports the budget and no
//!    verdict.
//!
//! A block that passes is orthogonal — no two of its rules overlap — or
//! joined, with one replaying certificate per critical pair
//! ([`Coincidence`]). Witnesses:
//! `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`,
//! `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`,
//! `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`.
//!
//! A circuit rule is a congruence over the rewrite it binds — `add(x, y) ==>
//! add(x′, y)` reads "a rewrite of `x` rewrites the sum" — not a rewrite of
//! its own: its right-hand side names a hole its left does not bind, so it is
//! left out of the rewriting the check reads ([`DeclarationCells::rewriting`]).
//! A block the cell gate declined an operation or a member of is not examined
//! ([`Coincidence::Unexamined`]): the decline is already its refusal, and a
//! verdict over the members left would be over rules the author did not write
//! alone.
//!
//! **Choice: refuse.** A block whose two readings part is refused whole, as a
//! family: the equational reading is what the rules mean — what a model of
//! the family satisfies, and what a `sign` block's models state as paths — and
//! the decision tree is how they run, so a tree computing what the equations
//! do not is a miscompilation, not a dialect. **Alternatives.** Warning and
//! running first match, the written order read as a disambiguation the author
//! opted into: rule order then means something, reordering two rules changes
//! what a program computes while every equation the family states stays the
//! same, and a model checked against the equations disagrees with the program
//! it models. Completing the rules — adding the derived cell that joins a
//! divergent pair, as completion does — was declined too: a derived cell is
//! an equation the author did not write, and a divergence between two
//! constructor terms would identify them. **Reversal.** A written opt-in to
//! ordered rules — an attribute on the block — makes first match the declared
//! semantics; the equational reading is then the one that changes, to the
//! rules with each one's earlier overlaps subtracted, and this check reads
//! that.
//!
//! # The normal form a call reaches
//!
//! [`normal_form`] reads a call written in the inspection notation —
//! `divmod(Succ(Succ(Zero)), Succ(Zero))` — elaborates it to the command its
//! operation's faces match, normalizes it under the block's rewriting, replays
//! the path it took to certify the normal form, and reads the normal form back
//! as a first-order term (`read_command`): a constructor term for one output,
//! the results tuple for several. It is the engine's reading of a call, the one
//! the corpus's `normalizes` attribute states and the differential test holds
//! the machine's run of the same call to. Only a block the check admitted is
//! read; a call into any other is [`NormalFormFault::Incoherent`].
//!
//! # What the kernel would need
//!
//! The verdict is the lowering's. The kernel admits the function an operation
//! lowers to and the paths a model carries, and never sees the rules as
//! rewrites, so it trusts the verdict rather than replaying it. Replaying it
//! needs the rewriting store as data; the critical-pair enumeration as a
//! certificate — every overlapping cell pair with its unifier, and the check
//! that no other pair's left-hand sides unify, which for the root-only
//! overlaps of linear left-hand sides the cell gate admits is first-order
//! unification over the pairs left out; one join certificate per pair, which
//! exists and replays by ground rewriting (`Tracelet::replay`); and the path
//! order's precedence with a checker for it. The certificates are kept on
//! [`Coincidence::Joined`]; the enumeration's completeness, the order and the
//! link from the confluent normal form to the lowered function are what the
//! kernel still owes (#322).

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Joinability;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::join_critical_pairs;
use gandr_theory_coherent_resolutions::normalize;
use gandr_theory_coherent_resolutions::replay_path;
use gandr_theory_computads::AdmittedFaceIndex;
use gandr_theory_computads::ElaborateError;
use gandr_theory_computads::command_reading;
use gandr_theory_computads::elaborate_call;
use gandr_theory_computads::read_command;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::Termination;
use gandr_theory_levitation::orient_rules;
use quenchant_shape::shape::Maybe;

use crate::LoweringRefusal;
use crate::desc_cells::CellDiagnosticIndex;
use crate::desc_cells::CircuitCell;
use crate::desc_cells::DeclarationCells;
use crate::desc_cells::located;

/// The most steps one reduct of a critical pair may take before the pair is
/// left undecided.
pub const JOIN_STEPS: usize = 4_096;

/// The most steps a call's normalization may take before it reports no normal
/// form.
pub const NORMAL_FORM_STEPS: usize = 1 << 16;

/// How a description's rules stand as one rewriting system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Coincidence
{
    /// The rules were not examined as one system: the cell gate declined an
    /// operation or a member, and that decline is the declaration's refusal.
    Unexamined,
    /// The rules terminate and no two of them overlap.
    Orthogonal,
    /// The rules terminate and every critical pair joins: one certificate per
    /// pair, each replaying over [`DeclarationCells::rewriting`].
    Joined(Vec<Tracelet>),
    /// The rules' two readings part, or the check could not tell: the report's
    /// diagnostic at this index says why.
    Refused(CellDiagnosticIndex),
}

/// Why a block's rules are refused as one rewriting system.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoherenceFault
{
    /// The path order does not put the rule's right-hand side below its left,
    /// so the rules are not known to terminate.
    Unoriented,
    /// The rule and an earlier one overlap at `peak` and rewrite it to two
    /// normal forms.
    Diverges
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<CmdPat>,
        /// The earlier rule's normal form of it.
        left: Box<CmdPat>,
        /// This rule's normal form of it.
        right: Box<CmdPat>,
    },
    /// The rule and an earlier one overlap at `peak`, and a reduct reaches no
    /// normal form within [`JOIN_STEPS`] steps.
    Undecided
    {
        /// The earlier rule's written interval.
        first: ByteSpan,
        /// The term both rules match.
        peak: Box<CmdPat>,
    },
}

impl CoherenceFault
{
    /// The refusal a held declaration carries for this fault at `span`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lowering_refusal(
        &self,
        span: ByteSpan,
    ) -> LoweringRefusal<'static>
    {
        match *self {
            | Self::Unoriented => LoweringRefusal::RulesUnoriented { span },
            | Self::Diverges { first, .. } => LoweringRefusal::RulesDiverge { span, first },
            | Self::Undecided { first, .. } => LoweringRefusal::RulesUndecided { span, first },
        }
    }
}

impl fmt::Display for CoherenceFault
{
    /// Writes the fault with the terms it names in the inspection notation: the
    /// peak and both normal forms of a divergence, the peak of an undecided
    /// pair.
    ///
    /// # Specification
    /// - ensures: one sentence per fault; a command the term reading cannot
    ///   write is spelled as the terminal it ends in.
    /// - fails: the formatting sink's error when it refuses the text.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readback of the written
    ///   text.
    ///
    /// # Errors
    /// Propagates a refusal from the formatting sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a divergent pair is written with its peak and both
    ///   normal forms in order; swapping them or dropping the peak changes the
    ///   witnessed text.
    /// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Unoriented => f.write_str(
                "the right-hand side is not below the left in the path order, so the rules may not \
                 end",
            ),
            | Self::Diverges {
                ref peak,
                ref left,
                ref right,
                ..
            } => write!(
                f,
                "both rules rewrite `{}`, one to `{}` and the other to `{}`",
                Spelled(peak),
                Spelled(left),
                Spelled(right)
            ),
            | Self::Undecided { ref peak, .. } => write!(
                f,
                "both rules rewrite `{}`, and its rewrites reach no normal form within \
                 {JOIN_STEPS} steps",
                Spelled(peak)
            ),
        }
    }
}

/// A command spelled as the term it denotes.
#[repr(transparent)]
struct Spelled<'command>(&'command CmdPat);

impl fmt::Display for Spelled<'_>
{
    /// Writes the term the command reads as, or the reason it reads as none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match read_command(self.0) {
            | Maybe::Present(term) => f.write_str(&spell(&term)),
            | Maybe::Absent(command_reading::Absent::Terminal) => f.write_str("★"),
            | Maybe::Absent(command_reading::Absent::SplitResults) => f.write_str("…"),
        }
    }
}

/// Decide whether a description's rules are one rewriting system: termination
/// by the path order, then joinability of every critical pair over its
/// rewriting store.
///
/// # Specification
/// - requires: `store`, `faces` and `circuits` are the cell gate's elaboration
///   of `description`, which declined none of its operations, faces or circuit
///   rules; `at` is the declaration's interval.
/// - ensures: the first unoriented rule as [`CoherenceFault::Unoriented`] at
///   its span; else the first critical pair that does not join, at the later
///   rule's span naming the earlier one's; else [`Coincidence::Orthogonal`]
///   when no two cells overlap and [`Coincidence::Joined`] with every pair's
///   certificate otherwise.
/// - panics: none.
///
/// # Errors
/// The fault and the span it stands at, as the ensures clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the addition family is orthogonal, the family adding a
///   right unit is joined with one certificate per overlap, a right unit
///   returning a successor diverges at the later rule, and a rule rebuilding
///   its own call is unoriented before any pair is read; reporting the earlier
///   rule's span, or deciding joinability first, changes one of them.
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
/// - witness: `coincide::tests::two_rules_rewriting_one_term_apart_refuse_the_block`
/// - witness: `coincide::tests::a_rule_that_rebuilds_its_own_call_refuses_the_block`
#[spec(ensures: |ret| match ret {
    Ok(Coincidence::Joined(ref certificates)) => !certificates.is_empty(),
    Ok(Coincidence::Orthogonal) => true,
    Ok(Coincidence::Unexamined | Coincidence::Refused(_)) => false,
    Err((span, CoherenceFault::Unoriented)) => matches!(orient_rules(description), Termination::Unoriented(_))
        && span.start() >= at.start() && span.end() <= at.end(),
    Err((_, CoherenceFault::Diverges { .. } | CoherenceFault::Undecided { .. })) => orient_rules(description) == Termination::Oriented,
})]
pub(crate) fn decide<G>(
    description: &SignDesc<G>,
    at: ByteSpan,
    store: &CellStore,
    faces: &[(AdmittedFaceIndex, CellId)],
    circuits: &[CircuitCell],
) -> Result<Coincidence, (ByteSpan, CoherenceFault)>
{
    let rule_span = |index: usize| {
        description
            .rules
            .get(index)
            .map_or(at, |face| located(face.provenance, at))
    };
    if let Termination::Unoriented(index) = orient_rules(description) {
        return Err((rule_span(usize::from(index)), CoherenceFault::Unoriented));
    }
    let cell_span = |cell: CellId| {
        faces
            .iter()
            .find(|&&(_, admitted)| admitted == cell)
            .map_or(at, |&(index, _)| rule_span(usize::from(index)))
    };
    let rewriting = rewriting_store(store, faces, circuits);
    match join_critical_pairs(&rewriting, NormalizationBudget::from(JOIN_STEPS)) {
        | Joinability::Joined(certificates) if certificates.is_empty() => {
            Ok(Coincidence::Orthogonal)
        },
        | Joinability::Joined(certificates) => Ok(Coincidence::Joined(certificates)),
        | Joinability::Diverges {
            overlap,
            left,
            right,
        } => Err((cell_span(overlap.right), CoherenceFault::Diverges {
            first: cell_span(overlap.left),
            peak: Box::new(overlap.peak),
            left: Box::new(left),
            right: Box::new(right),
        })),
        | Joinability::Undecided(overlap) => {
            Err((cell_span(overlap.right), CoherenceFault::Undecided {
                first: cell_span(overlap.left),
                peak: Box::new(overlap.peak),
            }))
        },
    }
}

/// The cells of `store` a rewrite reads: every cell but the admitted circuit
/// cells no face shares, in store order.
///
/// # Specification
/// - ensures: `store` itself when no circuit cell is left out; otherwise a
///   store holding the rest in order, so a cell inserted before the first left
///   out keeps its identifier.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `sign` block's congruence is left out while its faces
///   keep their identifiers, and a family with no circuit is read in place.
/// - witness: `coincide::tests::a_congruence_is_no_rewrite_of_its_own`
#[spec(ensures: |ret| usize::from(ret.len()) <= usize::from(store.len()))]
pub(crate) fn rewriting_store<'store>(
    store: &'store CellStore,
    faces: &[(AdmittedFaceIndex, CellId)],
    circuits: &[CircuitCell],
) -> Cow<'store, CellStore>
{
    let left_out: Vec<CellId> = circuits
        .iter()
        .filter_map(|circuit| match *circuit {
            | CircuitCell::Admitted { cell, .. } => Some(cell),
            | CircuitCell::Refused(_) => None,
        })
        .filter(|&cell| !faces.iter().any(|&(_, face)| face == cell))
        .collect();
    if left_out.is_empty() {
        return Cow::Borrowed(store);
    }
    let mut kept = CellStore::new();
    for (id, cell) in store.iter() {
        if !left_out.contains(&id) {
            let _kept = kept.insert(cell.clone());
        }
    }
    Cow::Owned(kept)
}

/// The text of one call in the inspection notation, as a `normalizes` row
/// writes it: `add(Succ(Zero), Zero)`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallText<'text>(&'text str);

impl<'text> From<&'text str> for CallText<'text>
{
    /// The call spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for CallText<'_>
{
    /// The call's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// The normal form a call reaches under a block's rules, with the path that
/// certifies it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NormalForm
{
    /// The call, as read.
    pub call: FreeTerm,
    /// The steps from the call's command to its normal form, replayed before
    /// the normal form is returned.
    pub path: Vec<CellApp>,
    /// The normal form, read back as a term: a constructor term for one
    /// output, the results tuple for several, or the call that no rule
    /// covers.
    pub normal: FreeTerm,
}

impl NormalForm
{
    /// The normal form spelled as `gandr run` spells the value: the
    /// inspection notation, a results tuple as `#{…}`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spelling(&self) -> String
    {
        spell(&self.normal)
    }
}

/// Why a call has no normal form to report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NormalFormFault
{
    /// The declaration is no family or `sign` block the description route
    /// read, so it has no rules to read the call under.
    Undescribed,
    /// The block's rules were not admitted as one rewriting system, so no
    /// reading of them is the block's.
    Incoherent,
    /// The text is not a term of the inspection notation.
    Unread,
    /// The text names a symbol the block declares neither as a constructor
    /// nor as an operation.
    UnknownSymbol,
    /// The term is no call the block's operations elaborate.
    NotACall(ElaborateError),
    /// The normalization took every step it was allowed.
    Exhausted,
    /// The recorded path does not replay to the normal form.
    Uncertified,
    /// The normal form writes no term.
    Unwritable(command_reading::Absent),
}

impl fmt::Display for NormalFormFault
{
    /// Writes why the call has no normal form.
    ///
    /// # Specification
    /// - ensures: one phrase per fault, naming the step budget when it ran out.
    /// - fails: the formatting sink's error when it refuses the text.
    /// - panics: none.
    /// - executable: none — a formatter exposes no readback of the written
    ///   text.
    ///
    /// # Errors
    /// Propagates a refusal from the formatting sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unread call and a call into a refused block read
    ///   apart.
    /// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Undescribed => f.write_str("no normal form: the declaration has no rules"),
            | Self::Incoherent => f.write_str("no normal form: the block's rules are refused"),
            | Self::Unread => f.write_str("no normal form: the call does not read as a term"),
            | Self::UnknownSymbol => {
                f.write_str("no normal form: the call names a symbol the block does not declare")
            },
            | Self::NotACall(_) => {
                f.write_str("no normal form: the term is no call the block's operations read")
            },
            | Self::Exhausted => write!(f, "no normal form within {NORMAL_FORM_STEPS} steps"),
            | Self::Uncertified => f.write_str("no normal form: the path does not replay"),
            | Self::Unwritable(_) => f.write_str("no normal form: it writes no term"),
        }
    }
}

/// The normal form `call` reaches under the rules of the block `cells` holds,
/// `description` being its description.
///
/// # Specification
/// - requires: `cells` is the cell gate's elaboration of `description`.
/// - ensures: the call read in the inspection notation against the block's
///   constructors and operations, elaborated to the command its faces match,
///   normalized under [`DeclarationCells::rewriting`] within
///   [`NORMAL_FORM_STEPS`] steps, its path replayed to the normal form, and the
///   normal form read back as a term.
/// - fails: [`NormalFormFault::Incoherent`] for a block the coincidence check
///   did not admit; otherwise the first step that fails, in that order.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a one-output and a two-output call read back their
///   values, a call into a refused block is incoherent before it is read, and
///   an unknown symbol and an unreadable text are told apart; reading the
///   normal form before the replay, or normalizing under the store with its
///   congruences, changes one of them.
/// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
/// - witness: `coincide::tests::an_overlap_that_joins_is_certified_and_runs_either_way`
#[spec(ensures: |ret| {
    let admitted = matches!(cells.coincidence, Coincidence::Orthogonal | Coincidence::Joined(_));
    match ret.as_ref() {
        Ok(normal) => admitted && read_call(description, call).as_ref() == Ok(&normal.call),
        Err(&NormalFormFault::Incoherent) => !admitted,
        Err(&NormalFormFault::Undescribed) => false,
        Err(_) => admitted,
    }
})]
#[inline]
pub fn normal_form<G>(
    description: &SignDesc<G>,
    cells: &DeclarationCells,
    call: CallText<'_>,
) -> Result<NormalForm, NormalFormFault>
{
    if !matches!(
        cells.coincidence,
        Coincidence::Orthogonal | Coincidence::Joined(_)
    ) {
        return Err(NormalFormFault::Incoherent);
    }
    let call = read_call(description, call)?;
    let command = elaborate_call(&call, description.polarity, &cells.operations)
        .map_err(NormalFormFault::NotACall)?;
    let rewriting = cells.rewriting();
    let normalized = normalize(
        &rewriting,
        &command,
        NormalizationBudget::from(NORMAL_FORM_STEPS),
    );
    if bool::from(normalized.exhausted) {
        return Err(NormalFormFault::Exhausted);
    }
    if !bool::from(replay_path(
        &rewriting,
        &command,
        &normalized.normal,
        &normalized.path,
    )) {
        return Err(NormalFormFault::Uncertified);
    }
    match read_command(&normalized.normal) {
        | Maybe::Present(normal) => Ok(NormalForm {
            call,
            path: normalized.path,
            normal,
        }),
        | Maybe::Absent(reason) => Err(NormalFormFault::Unwritable(reason)),
    }
}

/// Read `text` as a term of the inspection notation over `description`'s
/// symbols: a name, or a name applied to terms in parentheses separated by
/// commas, each name a constructor or an operation the description declares.
///
/// # Specification
/// - ensures: the term whose every application is the declared symbol of its
///   name, constructors and operations told apart by the declaration.
/// - fails: [`NormalFormFault::Unread`] when the text is not a whole term of
///   the notation; [`NormalFormFault::UnknownSymbol`] when a name is declared
///   as neither.
/// - panics: none.
/// - intension: one pass over the text with an explicit stack of open
///   applications, so nesting costs no call stack.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — nested and many-argument calls read to the terms whose
///   display they are, and a missing parenthesis, trailing text and an
///   undeclared name are refused apart.
/// - witness: `coincide::tests::a_call_reads_its_normal_form_or_says_why_not`
#[spec(ensures: |ret| ret.as_ref().is_err() || text.0.split_whitespace().collect::<String>()
    == ret.as_ref().map(|term| term.to_string().split_whitespace().collect::<String>()).unwrap_or_default())]
fn read_call<G>(
    description: &SignDesc<G>,
    text: CallText<'_>,
) -> Result<FreeTerm, NormalFormFault>
{
    let mut open: Vec<(Symbol<'_>, Vec<FreeTerm>)> = Vec::new();
    let mut rest = text.0.trim_start();
    loop {
        let length = rest
            .find(|character: char| !(character.is_alphanumeric() || "_'′".contains(character)))
            .unwrap_or(rest.len());
        let (name, after) = rest.split_at(length);
        if name.is_empty() {
            return Err(NormalFormFault::Unread);
        }
        let symbol = Symbol::of(description, CallText(name))?;
        rest = after.trim_start();
        if let Some(after) = rest.strip_prefix('(') {
            open.push((symbol, Vec::new()));
            rest = after.trim_start();
            continue;
        }
        let mut done = symbol.apply(Vec::new());
        loop {
            let Some(&mut (_, ref mut arguments)) = open.last_mut()
            else {
                return if rest.is_empty() {
                    Ok(done)
                }
                else {
                    Err(NormalFormFault::Unread)
                };
            };
            arguments.push(done);
            if let Some(after) = rest.strip_prefix(',') {
                rest = after.trim_start();
                break;
            }
            let Some(after) = rest.strip_prefix(')')
            else {
                return Err(NormalFormFault::Unread);
            };
            rest = after.trim_start();
            let Some((symbol, arguments)) = open.pop()
            else {
                return Err(NormalFormFault::Unread);
            };
            done = symbol.apply(arguments);
        }
    }
}

/// A declared symbol a call names.
#[derive(Clone, Copy, Debug)]
enum Symbol<'desc>
{
    /// A constructor.
    Ctor(&'desc Name),
    /// An operation.
    Op(&'desc Name),
}

impl<'desc> Symbol<'desc>
{
    /// The symbol `description` declares under `name`, its constructors before
    /// its operations.
    ///
    /// # Specification
    /// trivial.
    fn of<G>(
        description: &'desc SignDesc<G>,
        name: CallText<'_>,
    ) -> Result<Self, NormalFormFault>
    {
        description
            .ctors
            .iter()
            .find(|ctor| ctor.name.as_ref() == name.0)
            .map(|ctor| Self::Ctor(&ctor.name))
            .or_else(|| {
                description
                    .opers
                    .iter()
                    .find(|operation| operation.name.as_ref() == name.0)
                    .map(|operation| Self::Op(&operation.name))
            })
            .ok_or(NormalFormFault::UnknownSymbol)
    }

    /// The symbol applied to `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        self,
        arguments: Vec<FreeTerm>,
    ) -> FreeTerm
    {
        match self {
            | Self::Ctor(name) => FreeTerm::ctor(name.clone(), arguments),
            | Self::Op(name) => FreeTerm::op(name.clone(), arguments),
        }
    }
}

/// `term` in the inspection notation, a results tuple at its root as `#{…}`:
/// the spelling `gandr run` gives the value.
///
/// # Specification
/// trivial.
fn spell(term: &FreeTerm) -> String
{
    match term.view() {
        | TermView::Results { args } => {
            let mut spelled = String::from("#{");
            for (position, component) in args.enumerate() {
                if position > 0 {
                    spelled.push_str(", ");
                }
                spelled.push_str(&component.to_term().to_string());
            }
            spelled.push('}');
            spelled
        },
        | TermView::Var(_) | TermView::Ctor { .. } | TermView::Op { .. } => term.to_string(),
    }
}

#[cfg(test)]
mod tests;
