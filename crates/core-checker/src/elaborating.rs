//! The term-producing session over a module: it elaborates each declaration,
//! fills an owed hole, and resumes what waited on it.
//!
//! The session drives the module run and the kernel bridge, so it lives above
//! both. The suspension it reads, and the entry it answers, live below them in
//! [`crate::elaboration`].
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
//! [`CheckingContext::adopt`]: crate::CheckingContext::adopt

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::Declaration;
use crate::ModuleReport;
use crate::Verdict;
use crate::bridge;
use crate::elaboration::Entry;
use crate::elaboration::Outcome;
use crate::elaboration::Suspension;
use crate::elaboration::accepted;
use crate::elaboration::emit_recorded;
use crate::elaboration::record_transports;

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
        record_transports(&mut context);
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
                Entry::judged(&context, declaration.clone(), (outcome, lifts))
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
            reason = "parity: the body copies every declaration and adopts every entry before the target once; the check compares each entry once; #104 owns the cost of the clause"
        )
    )]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: |ret| match ret {
            Err(_) => self.entries == before,
            Ok(()) => self.entries.len() == before.len()
                && self.entries.iter().zip(&before).all(|(after, earlier)| {
                    if earlier.constant() == constant {
                        matches!(*earlier.outcome(), Outcome::Owed(_))
                            && matches!(*after.outcome(), Outcome::Checked(_))
                            && usize::from(after.judgements()) == usize::from(earlier.judgements()).saturating_add(1)
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
        let crate::DeclarationContent::Value { signature, .. } = *entry.source().content()
        else {
            return Err(ResumeError::NotOwed(constant));
        };
        if !matches!(*entry.outcome(), Outcome::Owed(_)) {
            return Err(ResumeError::NotOwed(constant));
        }
        let mut filled = Declaration::new(
            constant,
            signature,
            Maybe::Present(body),
            entry.source().origin(),
        )
        .lawful(entry.source().laws().to_vec())
        .ruled(entry.source().operation_rules().clone())
        .staged(entry.source().stages().to_vec())
        .supplied(entry.source().supplies().to_vec())
        .resolving(entry.source().models().to_vec())
        .obliged(entry.source().handler_laws().to_vec());
        if let Maybe::Present(stated) = entry.source().entry() {
            filled = filled.entered(stated.clone());
        }
        if let Maybe::Present(role) = entry.source().builtin() {
            filled = filled.built_in(role);
        }
        let count = entry.judgements();
        let mut declarations = self.declarations.clone();
        if let Some(slot) = declarations
            .iter_mut()
            .find(|declaration| declaration.constant() == constant)
        {
            *slot = filled;
        }
        let replacement = self.rejudge(&declarations, constant)?;
        match *replacement.outcome() {
            Outcome::Checked(_) => {},
            Outcome::Refused(refusal) => return Err(ResumeError::Refused(refusal)),
            Outcome::Suspended(ref suspension) => {
                return Err(ResumeError::Suspended(suspension.clone()));
            },
            Outcome::Formed | Outcome::Owed(_) => {
                return Err(ResumeError::Refused(CheckRefusal::MachineInvariant));
            },
        }
        self.declarations = declarations;
        *self.entry_mut(constant)? = replacement.after(count);
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
            reason = "parity: the body adopts every entry before each resumed target once; the check compares each entry once; #104 owns the cost of the clause"
        )
    )]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: self.entries.len() == before.len()
            && self.entries.iter().zip(&before).all(|(after, earlier)| {
                after.source() == earlier.source()
                    && (matches!(*earlier.outcome(), Outcome::Suspended(_)) || after == earlier)
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
            if let Outcome::Suspended(ref suspension) = *self.entry(target)?.outcome()
                && scheduled.insert(target)
            {
                pending.extend(suspension.dependencies().iter().copied());
            }
        }
        // Constants ascend in admission order, so the set runs prerequisites
        // first.
        for target in scheduled {
            let count = self.entry(target)?.judgements();
            let declarations = core::mem::take(&mut self.declarations);
            let replacement = self.rejudge(&declarations, target);
            self.declarations = declarations;
            *self.entry_mut(target)? = replacement?.after(count);
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
        crate::report::elaborated_report(&self.base, &self.entries)
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |entry| usize::from(entry.judgements()) == 1))]
    fn rejudge(
        &mut self,
        declarations: &[Declaration],
        constant: ConstantIndex,
    ) -> Result<Entry, ResumeError>
    {
        let budget = self.budget;
        let entries = &self.entries;
        let mut context = CheckingContext::new(&mut *self.arena, budget);
        record_transports(&mut context);
        let (verdict, residue) = crate::module::rejudge(
            &mut context,
            declarations,
            constant,
            |context, declaration| {
                let at = entries
                    .binary_search_by_key(&declaration.constant(), Entry::constant)
                    .map_err(|_insertion| CheckRefusal::MachineInvariant)?;
                let adopted = entries.get(at).ok_or(CheckRefusal::MachineInvariant)?;
                context.adopt(adopted.constant(), adopted.supplied(), adopted.unfolds())
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
                    .filter_map(|entry| match *entry.outcome() {
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
        let entry = Entry::judged(&context, target.clone(), (outcome, lifts));
        crate::report::absorb(&mut self.base, &context);
        Ok(entry)
    }
}
