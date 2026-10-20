//! Suspension on owed holes, and the term-producing path that resumes it.
//!
//! # A judgement blocked on an owed hole waits; it is not refused
//!
//! A declaration whose body is a hole under a formed signature is owed, and
//! crosses to the kernel as an axiom: a rigid constant. A later value
//! declaration that needs `El(h) ≡ Integer` against an owed code `h` cannot be
//! decided today — filling `h` with `⌜Integer⌝` settles it, filling it with
//! `⌜String⌝` refutes it — so the checker gives it neither acceptance nor
//! refusal but the third verdict, [`Verdict::Suspended`]: the declaration
//! waits on `h`, its blockers. This is the suspension case of Slattery and
//! Sterling's elaboration calculus (*Bidirectional Elaborators à la Carte*,
//! arXiv:2607.09564v2, Exegesis 6.6): the problem's sieve is inhabited but
//! does not contain the identity, so it resumes under a more specific
//! context — here, after a fill.
//!
//! The checker realizes the calculus natively, with the calculus as its
//! specification and the kernel as its certifier; kernel readmission certifies
//! only that an output is well typed, so the calculus's other guarantees —
//! invariance under judgemental equality, stability under substitution,
//! independence of order — are tested as relational witnesses, below.
//!
//! # The fragment: bare flex–rigid equations on owed code constants
//!
//! Only a decode of a bare owed code constant opposite a constructor-headed
//! type becomes a residual [`Equation`], in either orientation, at the root
//! of a comparison or beneath matching type constructors. A hole applied to a
//! spine (`El(h(x))`) and two decodes of holes (`El(h) ≡ El(k)`) keep the
//! ordinary checker's answer: telling a clash from a postponement there is
//! unification — certified emptiness of the sieve — and belongs to the
//! unifier (Abel and Pientka's pattern fragment), not to this collector. A
//! residual records what a fill must settle; it neither solves a hole nor
//! certifies a clash.
//!
//! A value declaration's judgement collects; a nominal declaration's
//! formation (data, abstract, world) decides every comparison rigidly. A
//! context that has judged no owed hole has nothing to collect, so ordinary
//! checking of a module without holes is unchanged, and the collector costs a
//! set lookup per comparison only where holes exist.
//!
//! # One rule machine
//!
//! The judgement is [`check_declaration`]'s, not a second elaborator: the
//! value bridge and the computation bridge are the calculus's `conv`
//! awaiting type equality, and the collector sits inside the conversion they
//! share. A declaration whose accepted judgement left a residual, or read the
//! type of a declaration that waits, is suspended: its type enters the
//! signature table, so later declarations judge against it, but nothing is
//! defined for it, so no conditional body unfolds or crosses to the kernel. A
//! refusal wins over every residual, so a declaration with a deferred
//! comparison and a refused premise is refused (multistrictness, Corollary
//! 5.2), and a waiting read propagates (Theorem 5.1: a composite's support is
//! the conjunction of its parts'). [`check_module`] reports each suspension
//! with its blockers — the holes still owed among its equations' heads, its
//! waiting prerequisites' included — and the declarations it waits on.
//!
//! Recorded design: a private residual collector beside an unchanged ordinary
//! checker, with a separate elaboration judge. Change: the collector is the
//! checker's own, so the report every face reads says what waits and on
//! which holes, and the one declaration judgement [`check_declaration`]
//! carries every former the checker admits. Reason: the separate judge
//! re-implemented the declaration rule and fell behind it, and a suspension
//! the faces cannot see is a refusal to them.
//!
//! A refused prerequisite does not refuse its readers: a signed declaration
//! refused at its body still supplies its type, as the checker has always
//! held, and the kernel bridge withholds a reader of a constant it was not
//! offered. A waiting prerequisite does propagate, because its reader's
//! output would name a body that does not yet exist.
//!
//! # Output, fill and resume
//!
//! [`Session`] is the term-producing run over the same judgement:
//!
//! | Outcome | Payload and meaning |
//! | ------- | ------------------- |
//! | [`Outcome::Checked`] | the formed type and the emitted core body; universe transport is explicit quoted lifted syntax, recorded per occurrence, so a shared code inhabits different universes at different uses; unchanged subterms keep their ids |
//! | [`Outcome::Formed`] | a nominal declaration that formed |
//! | [`Outcome::Owed`] | the declaration lacks its body; its signature crosses as an axiom |
//! | [`Outcome::Suspended`] | sorted unique residual equations, the blockers still owed when it was judged, and its waiting prerequisites; nothing is exported or defined |
//! | [`Outcome::Refused`] | the checker's refusal, never a certificate that a sieve is empty |
//!
//! The output walk rebuilds the route's formers — variables, application,
//! lambda, thunk, force, return, the non-dependent bind, ascription, tuples,
//! injections, case, lifts, static application and lambda — and reads every
//! other former as a leaf; a lift recorded beneath a leaf stays in the
//! report's side table at its node, as ordinary checking keeps every lift.
//!
//! [`Session::fill`] checks a proposed body against the owed declaration's
//! signature in its admission prefix; only a checked fill is installed, and a
//! failed one changes nothing. [`Session::resume`] judges a suspended target
//! and its waiting prerequisites in admission order. Both rebuild the prefix
//! by adoption — [`CheckingContext::adopt`], the seat an incremental caller
//! places a reused answer in — so a checked declaration is never judged
//! again, and [`Entry::judgements`] counts the judgements that ran. A fill
//! that reads a declaration still waiting is refused as
//! [`ResumeError::Suspended`] with no blockers and that prerequisite named:
//! resuming it comes first.
//!
//! The continuation is one declaration: a resumption discards the partial
//! work within a declaration and judges it again. The alternative, saved
//! machine frames, holds partial derivations across a fill; it reverses when
//! a measured resumption workload is dominated by re-judging the declaration
//! prefix that saved frames would keep. Two other alternatives were set aside:
//! interpreting the calculus's shallow embedding directly, which needs an
//! extensional metalanguage with equality reflection, and reading every stuck
//! comparison as a failure, which is the conflation this module removes. The
//! bare-flex boundary gives way to the unifier once it supplies solutions,
//! postponement reasons and replayable clash evidence.
//!
//! # The route's guarantees, as witnesses
//!
//! | Property | Calculus law | Witness in `elaboration::tests` |
//! | -------- | ------------ | ------------------------------- |
//! | Every checked output is readmitted | typed combinators, Construction 4.3 | `every_fixture_the_checker_accepts_is_readmitted` |
//! | Equal expected types give equal output | `conv`, Construction 4.3; judgemental invariance, §4.5 | `judgemental_equality_leaves_output_unchanged` |
//! | An owed conversion suspends, never refuses | Exegesis 6.6 | `owed_conversion_suspends` |
//! | Resume after a fill agrees with a batch check of the filled module | Theorem 5.1, substitution naturality | `incremental_equals_from_scratch` |
//! | Resumption order is irrelevant | Lemma 3.19, commutative partiality | `resumptions_commute` |
//! | A checked success survives a fill without judging it again | Exegesis 6.6, success closed under substitution | `checked_success_is_stable_without_rejudgement` |
//! | A refused subterm refuses its declaration | Corollary 5.2, multistrictness | `refused_subterms_refuse_the_declaration` |
//!
//! The readmission witness elaborates the checker's generated fixture
//! families and matches every published output with independent kernel
//! admission. Directed witnesses cover both bridges, the bind under a binder,
//! dependent scheduling, nested and shared universe transports, a lift under
//! every position of the fragment that checks a subterm
//! (`every_fragment_former_carries_a_nested_lift`) and unchanged paths beside
//! one keeping their ids (`unchanged_paths_keep_their_ids_beside_a_lift`),
//! transports that stay their own declaration's
//! (`a_refused_declaration_leaves_no_transport_behind`), invalid fills, the
//! bare-flex boundary in both families
//! (`only_bare_flex_rigid_equations_suspend`,
//! `computation_code_decodes_suspend_as_value_ones_do`,
//! `spined_holes_do_not_enter_the_residual_fragment`), a collector that is off
//! (`an_off_collector_never_defers`) and a rigid failure after a deferred
//! comparison (`residual_conjunction_does_not_hide_refusal`).
//! These are executable witnesses over the named fragment, not a formal
//! construction of the dominance or a universal proof; output identity,
//! artifact equality and judgement counts observe the relational laws apart
//! from kernel typing. Gundry, `McBride` and `McKinna`'s order-independent
//! metacontext (*Type Inference in Context*) is the discipline the
//! commutation witness holds the resumption to.
//!
//! [`Verdict::Suspended`]: crate::Verdict::Suspended
//! [`check_declaration`]: crate::check_declaration
//! [`check_module`]: crate::check_module
//! [`CheckingContext::adopt`]: crate::CheckingContext::adopt

mod constraints;
mod output;
#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

pub(crate) use self::constraints::Collecting;
pub(crate) use self::constraints::Deferrals;
pub(crate) use self::constraints::Deferred;
pub use self::constraints::Equation;
pub(crate) use self::constraints::Residue;
pub(crate) use self::output::CodeUse;
pub(crate) use self::output::Emission;
use self::output::Transports;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::Declaration;
use crate::FormedValueType;
use crate::Lift;
use crate::ModuleReport;
use crate::ObligationEntry;
use crate::OriginToken;
use crate::Verdict;
use crate::bridge;
use crate::signature_table;
use crate::unfolding;

/// A checked, emitted core term and its original judgement evidence.
///
/// # Specification
/// - requires: constructed only after all declaration premises succeed.
/// - ensures: the body contains explicit conversion lifts and has `declared`;
///   no residual equation is represented by an `Output`.
/// - provides: a term for independent kernel readmission.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the kernel independently checks emitted definitions;
///   exact nested-lift observations distinguish emission from input copying.
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Output
{
    /// The formed result type.
    declared: FormedValueType,
    /// The core output, with lifts materialized.
    body: ValueId,
    /// The verdict over the emitted body, for the kernel bridge.
    verdict: Verdict,
}

impl Output
{
    /// The emitted core body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> ValueId
    {
        self.body
    }

    /// The output's formed type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> FormedValueType
    {
        self.declared
    }
}

/// What a suspended declaration waits on.
///
/// # Specification
/// - requires: created only from a suspended judgement's residue.
/// - ensures: equations are sorted and unique, the declaration's own and its
///   waiting prerequisites'; blockers are their distinct flex heads still owed
///   when this record is created; dependencies are the waiting declarations it
///   read. A record over a prerequisite can retain an equation whose hole was
///   filled since.
/// - provides: declaration-granular continuation, without a unification claim.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact blockers and equations detect refusal-as-suspension
///   and lost obligations; two residuals witness conjunction.
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
/// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Suspension
{
    /// The type the waiting declaration supplies.
    declared: FormedValueType,
    /// Canonical residual equations, including waiting prerequisites'.
    equations: Vec<Equation>,
    /// Canonical owed-hole identities at creation.
    blockers: BTreeSet<ConstantIndex>,
    /// Earlier waiting declarations whose types this declaration read.
    dependencies: BTreeSet<ConstantIndex>,
}

impl Suspension
{
    /// The record of a judgement that left `residue`, supplying `declared`,
    /// with `owed` the holes owed and `prior` the suspensions kept when it was
    /// judged.
    ///
    /// # Specification
    /// - requires: `residue` is pending.
    /// - ensures: the equations are `residue`'s with each dependency's own
    ///   appended, sorted and deduplicated; the blockers are their holes that
    ///   `owed` holds; the dependencies are `residue`'s.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill of the hole before a dependent's record is
    ///   made leaves its blockers empty with the prerequisite still named.
    /// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
    /// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
    #[spec(
        captures: residue_dependencies = residue.dependencies.clone(),
        ensures: |ret| ret.dependencies == residue_dependencies
            && ret.equations.windows(2).all(|pair| pair.first() < pair.get(1))
            && ret.blockers.iter().all(|hole| owed.contains(hole)),
    )]
    pub(crate) fn new(
        declared: FormedValueType,
        residue: Residue,
        owed: &BTreeSet<ConstantIndex>,
        prior: &BTreeMap<ConstantIndex, Self>,
    ) -> Self
    {
        let Residue {
            mut equations,
            dependencies,
        } = residue;
        for dependency in &dependencies {
            if let Some(waiting) = prior.get(dependency) {
                equations.extend_from_slice(&waiting.equations);
            }
        }
        equations.sort_unstable();
        equations.dedup();
        let blockers = equations
            .iter()
            .map(Equation::hole)
            .filter(|hole| owed.contains(hole))
            .collect();
        Self {
            declared,
            equations,
            blockers,
            dependencies,
        }
    }

    /// The type the waiting declaration supplies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> FormedValueType
    {
        self.declared
    }

    /// The pending conversion equations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn equations(&self) -> &[Equation]
    {
        &self.equations
    }

    /// The holes owed when this suspension was recorded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn blockers(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.blockers
    }

    /// Waiting declarations to resume before this one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dependencies(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.dependencies
    }
}

/// A term-producing run's answer for one declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// Every premise is settled and a core term is available.
    Checked(Output),
    /// A nominal declaration formed.
    Formed,
    /// The declaration itself lacks its body.
    Owed(ObligationEntry),
    /// The declaration waits on owed code constants.
    Suspended(Suspension),
    /// A premise was refused; this is not certified sieve emptiness.
    Refused(CheckRefusal),
}

/// Number of declaration judgements actually executed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Judgements(usize);

impl From<Judgements> for usize
{
    /// Expose the declared work count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Judgements) -> Self
    {
        count.0
    }
}

/// One declaration's current answer and cumulative judgement count.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// The current declaration, changed only by filling an owed body.
    source: Declaration,
    /// Its settled or residual answer.
    outcome: Outcome,
    /// The type it supplies, retained even when a signed body refuses.
    supplied: Maybe<FormedValueType, signature_table::Absent>,
    /// The body its constant unfolds to, as the judging run defined it.
    unfolds: Maybe<ValueId, unfolding::Absent>,
    /// The lifts its output left beneath a former read as a leaf, by node.
    lifts: BTreeMap<ValueId, Lift>,
    /// Actual judgement invocations, excluding adoption and kernel replay.
    judgements: Judgements,
}

impl Entry
{
    /// The declaration's admission identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.source.constant()
    }

    /// The declaration's origin.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.source.origin()
    }

    /// The declaration as currently filled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &Declaration
    {
        &self.source
    }

    /// The current answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> &Outcome
    {
        &self.outcome
    }

    /// Declaration judgements executed for this entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn judgements(&self) -> Judgements
    {
        self.judgements
    }

    /// The lifts the output left in a side table, by node.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// The verdict the checker's report carries for this entry: an accepted
    /// one over the emitted body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Outcome::Checked`] gives its output's verdict,
    ///   [`Outcome::Formed`] [`Verdict::Data`], [`Outcome::Owed`] and
    ///   [`Outcome::Refused`] their payloads, and [`Outcome::Suspended`]
    ///   [`Verdict::Suspended`] at the type it supplies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — readmission matches each outcome with its kernel
    ///   answer.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    #[spec(ensures: |ret| match self.outcome {
        Outcome::Checked(output) => ret == output.verdict,
        Outcome::Formed => ret == Verdict::Data,
        Outcome::Owed(owed) => ret == Verdict::Owed(owed),
        Outcome::Suspended(ref suspension) => ret == Verdict::Suspended(suspension.declared),
        Outcome::Refused(refusal) => ret == Verdict::Refused(refusal),
    })]
    pub(crate) fn verdict(&self) -> Verdict
    {
        match self.outcome {
            Outcome::Checked(output) => output.verdict,
            Outcome::Formed => Verdict::Data,
            Outcome::Owed(owed) => Verdict::Owed(owed),
            Outcome::Suspended(ref suspension) => Verdict::Suspended(suspension.declared),
            Outcome::Refused(refusal) => Verdict::Refused(refusal),
        }
    }
}

/// An invalid request to fill or resume a module declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResumeError
{
    /// The module has no declaration at this position.
    Unknown(ConstantIndex),
    /// Only a genuinely owed body may be filled.
    NotOwed(ConstantIndex),
    /// The proposed filling did not check; the session remains unchanged.
    Refused(CheckRefusal),
    /// The proposed filling itself waits; it is not installed.
    Suspended(Suspension),
}

impl fmt::Display for ResumeError
{
    /// Render the precise rejected transition.
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
            Self::Unknown(constant) => write!(f, "unknown declaration {}", usize::from(constant)),
            Self::NotOwed(constant) => {
                write!(f, "declaration {} has no owed body", usize::from(constant))
            },
            Self::Refused(_) => f.write_str("the filling is refused"),
            Self::Suspended(_) => f.write_str("the filling waits on owed holes"),
        }
    }
}

impl core::error::Error for ResumeError
{
}

/// A module elaboration, admitting only checked hole fillings as mutations.
///
/// # Specification
/// - requires: input ids belong to the borrowed arena.
/// - ensures: checked outputs are retained under every admitted filling; only
///   explicitly resumed suspensions and proposed fillings are judged.
/// - provides: the fill-only substitution boundary behind stable success.
/// - panics: none.
/// - intension: each entry reports actual declaration judgements; rebuilding an
///   admission prefix adopts results and never increments those counts.
///
/// # Adequacy
/// - hypothesis: L2/L3 — filled batch equality, opposite resumption orders, and
///   unchanged checked work counts distinguish the three substitution laws.
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
/// - witness: `elaboration::tests::resumptions_commute`
/// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
pub struct Session<'arena>
{
    /// Exclusive ownership of the arena borrow prevents external truncation.
    arena: &'arena mut CoreArena,
    /// The declarations, as currently filled, in admission order.
    declarations: Vec<Declaration>,
    /// One entry per declaration, in admission order.
    entries: Vec<Entry>,
    /// The batch run's report, whose tables the elaborated report keeps.
    base: ModuleReport,
    /// The per-judgement and output-pass allowance.
    budget: CheckBudget,
}

impl<'arena> Session<'arena>
{
    /// Elaborate a module in admission order.
    ///
    /// # Specification
    /// - requires: ids resolve in `arena`; malformed inputs are refused.
    /// - ensures: one entry per declaration, each answering the verdict
    ///   [`check_module`] gives it; checked outputs have explicit lifts, and
    ///   only bare owed flex–rigid comparisons become residuals.
    /// - fails: never; each refusal is an entry's outcome.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — kernel replay checks output typing; exact residual
    ///   and refused-subterm observations separate the outcomes.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    /// - witness: `elaboration::tests::refused_subterms_refuse_the_declaration`
    ///
    /// [`check_module`]: crate::check_module
    #[must_use]
    #[spec(ensures: |ret| ret.entries.len() == declarations.len())]
    #[inline]
    pub fn new(
        arena: &'arena mut CoreArena,
        declarations: &[Declaration],
        budget: CheckBudget,
    ) -> Self
    {
        let mut context = CheckingContext::new(&mut *arena, budget);
        context.deferrals_mut().emission = Emission::Recording(Transports::default());
        let mut emitted = BTreeMap::new();
        let base = crate::module::run(
            &mut context,
            declarations,
            |context, declaration, verdict| {
                if let Verdict::Checked { body, .. } | Verdict::Synthesised { body, .. } = verdict {
                    emitted.insert(declaration.constant(), emit_recorded(context, body, budget));
                }
            },
        );
        let entries = declarations
            .iter()
            .zip(base.judged())
            .map(|(declaration, judged)| {
                let constant = declaration.constant();
                let (outcome, lifts) = match judged.verdict() {
                    verdict @ (Verdict::Checked { .. } | Verdict::Synthesised { .. }) => accepted(
                        verdict,
                        emitted
                            .remove(&constant)
                            .unwrap_or(Err(CheckRefusal::MachineInvariant)),
                    ),
                    Verdict::Suspended(_) => (
                        base.suspensions().get(&constant).cloned().map_or(
                            Outcome::Refused(CheckRefusal::MachineInvariant),
                            Outcome::Suspended,
                        ),
                        BTreeMap::new(),
                    ),
                    Verdict::Data => (Outcome::Formed, BTreeMap::new()),
                    Verdict::Owed(owed) => (Outcome::Owed(owed), BTreeMap::new()),
                    Verdict::Refused(refusal) => (Outcome::Refused(refusal), BTreeMap::new()),
                };
                Entry {
                    source: declaration.clone(),
                    supplied: context.signature(constant),
                    unfolds: unfolds(&context, constant, &outcome),
                    outcome,
                    lifts,
                    judgements: Judgements(1),
                }
            })
            .collect();
        drop(context);
        Self {
            arena,
            declarations: declarations.to_vec(),
            entries,
            base,
            budget,
        }
    }

    /// Current answers in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[Entry]
    {
        &self.entries
    }

    /// Read the emitted terms while the session owns the arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arena(&self) -> &CoreArena
    {
        self.arena
    }

    /// Fill one owed body, without judging any dependent declaration.
    ///
    /// # Specification
    /// - requires: `body` belongs to the session's arena.
    /// - ensures: a successful fill checks against the original signature in
    ///   its original admission prefix, then replaces only that owed entry,
    ///   whose judgements advance by one. A failed fill changes no entry.
    ///   Checked dependents are never judged.
    /// - fails: unknown position, a non-owed target, a refused or suspended
    ///   fill.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the corresponding `ResumeError` without installing the filling.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — batch equality and work counts witness
    ///   substitution; invalid fills distinguish substitution from arbitrary
    ///   body editing.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    /// - witness: `elaboration::tests::invalid_fills_leave_entries_unchanged`
    /// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body copies every declaration and adopts every entry before the target once; the check compares each entry once"
        )
    )]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: |ret| match ret {
            Err(_) => self.entries == before,
            Ok(()) => self.entries.len() == before.len()
                && self.entries.iter().zip(&before).all(|(after, earlier)| {
                    if earlier.constant() == constant {
                        matches!(earlier.outcome, Outcome::Owed(_))
                            && matches!(after.outcome, Outcome::Checked(_))
                            && usize::from(after.judgements) == usize::from(earlier.judgements).saturating_add(1)
                    } else {
                        after == earlier
                    }
                }),
        },
    )]
    #[inline]
    pub fn fill(
        &mut self,
        constant: ConstantIndex,
        body: ValueId,
    ) -> Result<(), ResumeError>
    {
        let entry = self.entry(constant)?;
        let crate::DeclarationContent::Value { signature, .. } = *entry.source.content()
        else {
            return Err(ResumeError::NotOwed(constant));
        };
        if !matches!(entry.outcome, Outcome::Owed(_)) {
            return Err(ResumeError::NotOwed(constant));
        }
        let mut filled = Declaration::new(
            constant,
            signature,
            Maybe::Present(body),
            entry.source.origin(),
        )
        .lawful(entry.source.laws().to_vec())
        .ruled(entry.source.operation_rules().clone())
        .staged(entry.source.stages().to_vec());
        if let Maybe::Present(stated) = entry.source.entry() {
            filled = filled.entered(stated.clone());
        }
        let count = entry.judgements;
        let mut declarations = self.declarations.clone();
        if let Some(slot) = declarations
            .iter_mut()
            .find(|declaration| declaration.constant() == constant)
        {
            *slot = filled;
        }
        let mut replacement = self.rejudge(&declarations, constant)?;
        match replacement.outcome {
            Outcome::Checked(_) => {},
            Outcome::Refused(refusal) => return Err(ResumeError::Refused(refusal)),
            Outcome::Suspended(suspension) => return Err(ResumeError::Suspended(suspension)),
            Outcome::Formed | Outcome::Owed(_) => {
                return Err(ResumeError::Refused(CheckRefusal::MachineInvariant));
            },
        }
        replacement.judgements = Judgements(count.0.saturating_add(1));
        self.declarations = declarations;
        *self.entry_mut(constant)? = replacement;
        Ok(())
    }

    /// Resume a suspended declaration, or preserve a settled answer unchanged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: judges only the suspended target and its waiting
    ///   prerequisites, in admission order. Every checked entry remains
    ///   unchanged; cached prefix bodies are adopted rather than judged again.
    /// - fails: unknown target or inconsistent admission order in the prefix.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ResumeError::Unknown` or the refused prefix admission.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — batch comparison and opposite orders observe the
    ///   calculus laws independently of typing; work counts detect judging
    ///   again.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    /// - witness: `elaboration::tests::resumptions_commute`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    /// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body adopts every entry before each resumed target once; the check compares each entry once"
        )
    )]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: self.entries.len() == before.len()
            && self.entries.iter().zip(&before).all(|(after, earlier)| {
                after.source == earlier.source
                    && (matches!(earlier.outcome, Outcome::Suspended(_)) || after == earlier)
            }),
    )]
    #[inline]
    pub fn resume(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<(), ResumeError>
    {
        let mut pending = Vec::from([constant]);
        let mut scheduled = BTreeSet::new();
        while let Some(target) = pending.pop() {
            if let Outcome::Suspended(ref suspension) = self.entry(target)?.outcome
                && scheduled.insert(target)
            {
                pending.extend(suspension.dependencies.iter().copied());
            }
        }
        // Constants ascend in admission order, so the set runs prerequisites
        // first.
        for target in scheduled {
            let count = self.entry(target)?.judgements;
            let declarations = core::mem::take(&mut self.declarations);
            let replacement = self.rejudge(&declarations, target);
            self.declarations = declarations;
            let mut replacement = replacement?;
            replacement.judgements = Judgements(count.0.saturating_add(1));
            *self.entry_mut(target)? = replacement;
        }
        Ok(())
    }

    /// The checker's report over the current answers: each verdict over its
    /// emitted body, no conditional body defined, and every suspension with
    /// its blockers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`elaborated_report`] over the batch report and the current
    ///   entries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — readmission of this report observes every outcome.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    ///
    /// [`elaborated_report`]: crate::elaborated_report
    #[must_use]
    #[spec(ensures: |ret| ret.judged().len() == self.entries.len())]
    #[inline]
    pub fn report(&self) -> ModuleReport
    {
        crate::module::elaborated_report(&self.base, &self.entries)
    }

    /// Independently readmit all settled outputs and owed holes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel sees emitted bodies, owed axioms and refusal
    ///   marks, and is offered nothing for a suspended declaration.
    /// - fails: never; kernel and bridge failures are readmission outcomes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the existing kernel independently checks every
    ///   output; no conditional success is smuggled into its environment as an
    ///   axiom.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    #[must_use]
    #[spec(ensures: |ret| ret.readmitted().len() == self.entries.len())]
    #[inline]
    pub fn readmit(&mut self) -> bridge::Readmission
    {
        let report = self.report();
        bridge::readmit(self.arena, &report)
    }

    /// The entry at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry whose constant is `constant`.
    /// - fails: [`ResumeError::Unknown`] when no entry is at `constant`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unknown constant is refused before any work.
    /// - witness: `elaboration::tests::invalid_fills_leave_entries_unchanged`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entry| entry.constant() == constant))]
    fn entry(
        &self,
        constant: ConstantIndex,
    ) -> Result<&Entry, ResumeError>
    {
        self.entries
            .binary_search_by_key(&constant, Entry::constant)
            .ok()
            .and_then(|at| self.entries.get(at))
            .ok_or(ResumeError::Unknown(constant))
    }

    /// The entry at `constant`, to be replaced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry whose constant is `constant`.
    /// - fails: [`ResumeError::Unknown`] when no entry is at `constant`.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill and a resumption replace the entry they judged
    ///   and no other.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entry| entry.constant() == constant))]
    fn entry_mut(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<&mut Entry, ResumeError>
    {
        self.entries
            .binary_search_by_key(&constant, Entry::constant)
            .ok()
            .and_then(|at| self.entries.get_mut(at))
            .ok_or(ResumeError::Unknown(constant))
    }

    /// Judge the declaration at `constant` of `declarations` once, its prefix
    /// adopted from the current entries, and answer its entry.
    ///
    /// # Specification
    /// - requires: `declarations` is the session's module, with at most the
    ///   declaration at `constant` changed.
    /// - ensures: only the declaration at `constant` is judged; the prefix
    ///   supplies cached types, accepted definitions, and owed and waiting
    ///   marks in admission order; the answer is the entry that judgement
    ///   gives, with one judgement counted. The batch report's tables gain what
    ///   the judgement decided.
    /// - fails: a refused admission order in the prefix.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the prefix's `ResumeError::Refused`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — batch equality checks prefix reconstruction, and
    ///   per-entry counts distinguish adoption from judging again.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entry| entry.judgements == Judgements(1)))]
    fn rejudge(
        &mut self,
        declarations: &[Declaration],
        constant: ConstantIndex,
    ) -> Result<Entry, ResumeError>
    {
        let budget = self.budget;
        let entries = &self.entries;
        let mut context = CheckingContext::new(&mut *self.arena, budget);
        context.deferrals_mut().emission = Emission::Recording(Transports::default());
        let (verdict, residue) = crate::module::rejudge(
            &mut context,
            declarations,
            constant,
            |context, declaration| {
                let at = entries
                    .binary_search_by_key(&declaration.constant(), Entry::constant)
                    .map_err(|_insertion| CheckRefusal::MachineInvariant)?;
                let adopted = entries.get(at).ok_or(CheckRefusal::MachineInvariant)?;
                context.adopt(adopted.constant(), adopted.supplied, adopted.unfolds)
            },
        )
        .map_err(ResumeError::Refused)?;
        let target = declarations
            .iter()
            .find(|declaration| declaration.constant() == constant)
            .ok_or(ResumeError::Refused(CheckRefusal::MachineInvariant))?;
        let (outcome, lifts) = match verdict {
            Verdict::Checked { body, .. } | Verdict::Synthesised { body, .. } => {
                let emitted = emit_recorded(&mut context, body, budget);
                accepted(verdict, emitted)
            },
            Verdict::Suspended(declared) => {
                let prior = entries
                    .iter()
                    .filter_map(|entry| match entry.outcome {
                        Outcome::Suspended(ref waiting) => {
                            Some((entry.constant(), waiting.clone()))
                        },
                        Outcome::Checked(_)
                        | Outcome::Formed
                        | Outcome::Owed(_)
                        | Outcome::Refused(_) => None,
                    })
                    .collect();
                let suspension =
                    Suspension::new(declared, residue, &context.deferrals().owed, &prior);
                (Outcome::Suspended(suspension), BTreeMap::new())
            },
            Verdict::Data => (Outcome::Formed, BTreeMap::new()),
            Verdict::Owed(owed) => (Outcome::Owed(owed), BTreeMap::new()),
            Verdict::Refused(refusal) => (Outcome::Refused(refusal), BTreeMap::new()),
        };
        let entry = Entry {
            source: target.clone(),
            supplied: context.signature(constant),
            unfolds: unfolds(&context, constant, &outcome),
            outcome,
            lifts,
            judgements: Judgements(1),
        };
        crate::module::absorb(&mut self.base, &context);
        Ok(entry)
    }
}

/// The body the run in `context` defined `constant` as, or why it has none:
/// owed for a hole, waiting for a suspended declaration.
///
/// # Specification
/// - requires: `outcome` is the run's answer for `constant`.
/// - ensures: [`unfolding::Absent::Owed`] for an owed outcome,
///   [`unfolding::Absent::Waiting`] for a suspended one, and otherwise the body
///   the context defines `constant` as, or [`unfolding::Absent::Rigid`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — a resumed dependent of a filled hole unfolds it, and a
///   fill reading a waiting declaration waits on it.
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
/// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
#[spec(ensures: |ret| match *outcome {
    Outcome::Owed(_) => ret == Maybe::Absent(unfolding::Absent::Owed),
    Outcome::Suspended(_) => ret == Maybe::Absent(unfolding::Absent::Waiting),
    Outcome::Checked(_) | Outcome::Formed | Outcome::Refused(_) => ret != Maybe::Absent(unfolding::Absent::Owed)
        && ret != Maybe::Absent(unfolding::Absent::Waiting),
})]
fn unfolds(
    context: &CheckingContext<'_>,
    constant: ConstantIndex,
    outcome: &Outcome,
) -> Maybe<ValueId, unfolding::Absent>
{
    match *outcome {
        Outcome::Owed(_) => Maybe::Absent(unfolding::Absent::Owed),
        Outcome::Suspended(_) => Maybe::Absent(unfolding::Absent::Waiting),
        Outcome::Checked(_) | Outcome::Formed | Outcome::Refused(_) => {
            match context.definitions().body(constant) {
                Maybe::Present(body) => Maybe::Present(body),
                Maybe::Absent(_) => Maybe::Absent(unfolding::Absent::Rigid),
            }
        },
    }
}

/// Emit `body` with the transports the judgement just recorded, restarting
/// the recording for the next.
///
/// # Specification
/// - requires: `context` records transports.
/// - ensures: [`output::emit`]'s answer over the recorded transports; the
///   context records afresh.
/// - fails: [`CheckRefusal::MachineInvariant`] when the context records none;
///   the output pass's refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L1/L3 — a lifted argument is emitted explicitly, and two
///   declarations' transports stay their own, a refused one's included.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
/// - witness: `elaboration::tests::shared_code_occurrences_keep_distinct_transports`
/// - witness: `elaboration::tests::a_refused_declaration_leaves_no_transport_behind`
#[spec(ensures: |ret| matches!(context.deferrals().emission, Emission::Recording(_)) || ret.is_err())]
fn emit_recorded(
    context: &mut CheckingContext<'_>,
    body: ValueId,
    budget: CheckBudget,
) -> Result<output::Emitted, CheckRefusal>
{
    let recorded = core::mem::replace(
        &mut context.deferrals_mut().emission,
        Emission::Recording(Transports::default()),
    );
    let Emission::Recording(transports) = recorded
    else {
        context.deferrals_mut().emission = recorded;
        return Err(CheckRefusal::MachineInvariant);
    };
    output::emit(context.arena_mut(), body, transports, budget)
}

/// The outcome of the accepted `verdict` whose body emitted as `emitted`.
///
/// # Specification
/// - requires: `emitted` is the emission of `verdict`'s body.
/// - ensures: an accepted verdict whose emission succeeded is
///   [`Outcome::Checked`] over the emitted body, with the lifts the emission
///   left in a side table; one whose emission refused is [`Outcome::Refused`]
///   with that refusal, with no lifts.
/// - fails: never; a verdict that is not accepted is
///   [`CheckRefusal::MachineInvariant`] as the outcome.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — readmission observes the emitted body under the verdict's
///   own evidence.
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(
    captures: emitted_before = emitted.as_ref().map(|emitted| emitted.body).map_err(|refusal| *refusal),
    ensures: |ret| match (&emitted_before, &ret.0) {
        (&Ok(body), &Outcome::Checked(output)) => output.body == body,
        (&Err(refusal), &Outcome::Refused(answer)) => refusal == answer,
        (_, &Outcome::Refused(CheckRefusal::MachineInvariant)) => true,
        _ => false,
    },
)]
fn accepted(
    verdict: Verdict,
    emitted: Result<output::Emitted, CheckRefusal>,
) -> (Outcome, BTreeMap<ValueId, Lift>)
{
    let emitted = match emitted {
        Ok(emitted) => emitted,
        Err(refusal) => return (Outcome::Refused(refusal), BTreeMap::new()),
    };
    let (declared, verdict) = match verdict {
        Verdict::Checked {
            declared, evidence, ..
        } => (declared, Verdict::Checked {
            declared,
            body: emitted.body,
            evidence,
        }),
        Verdict::Synthesised { synthesised, .. } => {
            (synthesised.produced(), Verdict::Synthesised {
                body: emitted.body,
                synthesised,
            })
        },
        Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {
            return (
                Outcome::Refused(CheckRefusal::MachineInvariant),
                BTreeMap::new(),
            );
        },
    };
    (
        Outcome::Checked(Output {
            declared,
            body: emitted.body,
            verdict,
        }),
        emitted.lifts,
    )
}
