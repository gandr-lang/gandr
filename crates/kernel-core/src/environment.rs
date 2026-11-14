//! The append-only **environment** and its single admission choke point.
//!
//! [`Environment::add_decl`] is the only way a declaration enters checked,
//! [`Environment::add_decl_unchecked`] is the one warned bypass, and
//! [`Environment::audit`] reports what a declaration transitively rests on.
//!
//! A [`CheckedId`] is unforgeable outside this crate — its constructor is
//! private — so "this declaration was admitted" is a type-level fact in
//! consuming code rather than a runtime claim. There is a single
//! checked-or-bypassed bit, never a trust lattice.
//!
//! # The arena and the admission watermark
//!
//! The environment owns the one arena every declaration's content lives in.
//! Content is built through [`Environment::stage`], which records the
//! **content-start** watermark; admission enforces the invariant:
//!
//! > After `add_decl` returns — success **or** rejection — the arena holds
//! > exactly the nodes admitted by prior declarations plus, on success, this
//! > declaration's content. Checker intermediates never persist.
//!
//! The mechanism is a two-mark scheme. Staging records content-start;
//! `add_decl` reads content-end on entry. The checker runs on a clone of the
//! frozen arena, so its synthesized intermediates allocate in the clone, past
//! content-end, and leave with it. On success the arena keeps the content up
//! to **content-end**; on rejection it is truncated to **content-start**,
//! which drops the content too.
//!
//! # Staging order, and the two ways it can diverge from admission order
//!
//! A staged declaration outlives its builder's borrow, so a producer may stage
//! one declaration and offer another before it. That divergence has **two**
//! shapes, and only one of them a contiguous watermark can absorb.
//!
//! **Content-start below already-admitted content — absorbed.** A producer
//! stages one declaration, admits a second, and only then offers the first; the
//! first's content-start mark now lies below content the environment already
//! committed, and a rejection truncating to it would delete an admitted
//! declaration's nodes, leaving the entries intact with their roots dangling.
//! The environment carries a third mark, the **admission floor** — the
//! watermark at the most recent admission, checked or bypassed — and a
//! rejection truncates to this declaration's content-start clamped into
//! `[admission floor, content-end]`. It therefore never reaches below committed
//! content and never leaves an intermediate behind. For the ordinary
//! stage-then-admit producer the clamp changes nothing; for this producer the
//! rejected declaration's nodes are retained as unreachable orphans, which no
//! admitted entry or audit walk can observe. **Retaining garbage is the failure
//! this trades for deleting evidence.**
//!
//! **Content-start below *outstanding* content — refused.** A producer stages
//! one declaration, stages a second, and then offers the first. The second's
//! nodes now sit above the first's content-start while its
//! [`StagedDeclaration`] is still live, and no clamp can save them: the floor
//! lies below both, so a rejection would truncate through the second's content
//! and leave the producer holding roots that dangle — or, worse, roots that a
//! later staging re-mints, so a subsequent admission would check *other*
//! content and admit a different declaration under that name. A contiguous
//! watermark cannot retain a disjoint region, so this is refused rather than
//! absorbed: the environment tracks the content-start mark of every staged and
//! unresolved declaration, and [`Environment::add_decl`] answers
//! [`KernelError::OutstandingStagedContent`] for any declaration with an
//! outstanding mark above its own. A silent index retarget is the one outcome
//! the floor's evidence-preservation rule exists to rule out, so the refusal is
//! the fail-closed posture the rest of the kernel takes toward a fault it
//! excludes.
//!
//! A mark is resolved by admitting the declaration, by bypassing it, or by
//! [`Environment::abandon`]; abandoning a staging session before it finishes
//! resolves its mark too. A producer that drops a [`StagedDeclaration`] without
//! doing any of those keeps its content in the arena, and the mark keeps saying
//! so, which is why the refusal is a producer-visible fact rather than a leak.
//!
//! Before a borrowing session finishes, both explicit discard and ordinary
//! scope exit roll back its builder and release its final registration. The
//! claim guard holds only the exclusive tracker borrow: no intervening
//! registration is possible, so release pops that final entry without an
//! allocation, state flag or duplicate watermark. All four finishers disarm
//! the guard when responsibility passes to the [`StagedDeclaration`].
//! [`Environment::abandon`] truncates when nothing outstanding sits above the
//! mark and otherwise retains the region as an orphan, the same clamp a
//! rejection takes. "Above" is componentwise rather than lexicographic,
//! because truncation is per family. Removing the outstanding-content guard
//! from `add_decl` is caught by the witness that the later staging's root
//! still resolves after the refusal.
//!
//! # Releases, their commits and the cursor
//!
//! [`Environment::release`] reserves the next position and the declaration's
//! rank. It gives the check, which runs on any thread.
//! [`Environment::settle`] commits the outcome at the reserved position.
//! Commits come in any order that the dependences allow. A cursor folds the
//! states that read the order of every commit, in position order: the order
//! flag, the rows of the dependents and the records of the verdicts. A
//! release can read an earlier commit before that commit comes. Then the
//! release holds, and [`Released::Held`] gives the declaration back. The
//! caller settles the outstanding releases and releases it again. A refusal
//! below the content of a later staging keeps its content as an orphan, as
//! the clamp of a rejection does. The bypass, a block and the move of a seed
//! read every commit. Each refuses with [`KernelError::UnsettledReleases`]
//! while a release is outstanding. A keep in place and a retirement go ahead
//! beside the outstanding releases. Each refuses the same way while a release
//! reads into what it writes.
//!
//! # Receipts and the audit
//!
//! A [`CheckedId`] names a position, not an environment identity; it is
//! meaningful only with the admission history it came from, which the
//! position alone cannot establish. [`Environment::add_decl_unchecked`]
//! performs no checking: the caller vouches for the declaration, a wrong one
//! can make the kernel prove anything, and the audit reports every
//! declaration that rests on it.
//!
//! **The audit follows types and terms.** A declaration can depend on a
//! sealed atom, a nominal declaration and its schema, or constants reached
//! through code and nominal arguments. A quote crosses back from a value to
//! its type. The dependency walk therefore follows both languages and every
//! variadic native child. Sealing provenance remains a separate question —
//! which sealed atoms did a projection rebind? — and does not become more
//! permissive by following ordinary code dependencies.
//!
//! The record itself, its entries and its admitted declarations, is
//! [`crate::env`]'s, which names no judgement.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ArenaWatermark;
use gandr_kernel_term::ChunkedMap;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::SourceRank;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::census::ExpansionCensus;
use crate::check;
use crate::encoding::ConstantName;
use crate::env::Admission;
use crate::env::AdmittedDeclaration;
use crate::env::AdmittedParts;
use crate::env::CheckedId;
use crate::env::CodeEdges;
use crate::env::Entries;
use crate::env::Membership;
use crate::env::Order;
use crate::env::OutstandingContent;
use crate::env::Slot;
use crate::env::StagedDeclaration;
use crate::env::StagedMarks;
use crate::env::Staging;
use crate::env::Unit;
use crate::env::UnitShape;
use crate::env::UnsettledCount;
use crate::env::collect_reachable;
use crate::env::references;
use crate::error::KernelError;
use crate::levels::LevelContext;

/// The check of one lone declaration, released from the environment.
///
/// It is a recorded verdict, or a check that owns everything that it reads.
/// So it runs on any thread while the committer writes the environment.
///
/// # Specification
/// - requires: made by [`Environment::release`].
/// - ensures: [`Self::run`] answers what the check of [`Environment::add_decl`]
///   answers for the declaration.
/// - panics: none.
/// - executable: none — the fields are private and set only by
///   [`Environment::release`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Environment::release`].
/// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
#[derive(Debug)]
pub struct Check
{
    /// The declaration that the check reads.
    declaration: Declaration,
    /// A recorded verdict, or what the check reads.
    way: Way,
}

quenchant_shape::reason_enum! {
    /// Why a staged declaration carries no rank.
    pub mod unranked {
        /// The reason no rank is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Its source gives it none, so it takes the rank past every
            /// live one.
            Unranked,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an environment ranks its next admission past every live entry.
    pub mod next_rank {
        /// The reason no next rank is set.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No readmission set a next rank, or the last one cleared it.
            Unset,
        }
    }
}

/// What a release answers: the check, released at its reserved position, or
/// the declaration handed back with the reason it holds.
///
/// # Specification
/// - requires: made by [`Environment::release`].
/// - ensures: a running check settles through [`Environment::settle`] at its
///   reserved position. A held declaration is unchanged, and its staged mark
///   stays outstanding: settle each outstanding check, then release it again.
/// - panics: none.
/// - executable: none — a data declaration.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Environment::release`].
/// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per release, moved once to its thread or back to its caller; boxing the check would allocate at every release"
)]
pub enum Released
{
    /// The check runs apart from the environment, and what its commit needs
    /// beside it.
    Running(Pending, Check),
    /// The declaration, handed back: its release reads a commit that has not
    /// come.
    Held(StagedDeclaration, Hold),
}

/// Why a release hands its declaration back: what it reads of an earlier
/// release whose commit has not come.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Hold
{
    /// An atom is manifest. Its seal advances at each admission, and the
    /// check reads the manifest atoms.
    Manifest,
    /// The declaration, or an outstanding one, is an abstract type, a
    /// presented type or a role holder. Each check after it reads it.
    Ordering,
    /// An outstanding release reserves the declaration's rank, or the rank
    /// past every rank that an unranked declaration takes; or a predicted
    /// rank is not folded yet, and the declaration carries a rank, or
    /// `speculation.rank` is off.
    Rank,
    /// An outstanding release ranked below carries the same generative
    /// content or the same plain definition, which the declaration's key or
    /// name counts.
    Content,
}

impl Check
{
    /// Run the check on the thread that calls: answer a recorded verdict,
    /// or check the declaration against the check's own scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a recall, its reading with an empty census; otherwise the
    ///   answer of the kernel's check of the declaration against the check's
    ///   view, arena and session, with the census it charged and the admitted
    ///   results it took.
    /// - panics: none.
    /// - executable: none — the answer is the check's, which no predicate
    ///   restates.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Environment::release`].
    /// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
    #[inline]
    #[must_use]
    pub fn run(self) -> Ran
    {
        let Self { declaration, way } = self;
        match way {
            Way::Recalled(accessibility) => Ran {
                declaration,
                outcome: Ok(accessibility),
                admission: Admission::Recalled,
                census: ExpansionCensus::new(),
                took: crate::admitted::AdmittedCount::NONE,
                scope: Maybe::Absent(ran::Absent::Recalled),
            },
            Way::Checking(mut scope, judged) => {
                let taken = crate::admitted::Tally::new();
                let mut census = ExpansionCensus::new();
                let outcome = {
                    let Scope {
                        ref view,
                        ref mut arena,
                        ref mut session,
                    } = scope;
                    check::check_declaration(
                        arena,
                        check::Judgement::new(view, &judged.levels)
                            .unsealing(&judged.manifest)
                            .taking(crate::admitted::Taking::under(judged.admitting, &taken))
                            .forking(judged.forking.forking()),
                        &declaration,
                        session,
                        &mut census,
                    )
                };
                Ran {
                    declaration,
                    outcome,
                    admission: Admission::Checked,
                    census,
                    took: taken.get(),
                    scope: Maybe::Present(scope),
                }
            },
        }
    }
}

/// The append-only kernel environment: one arena, and the admitted
/// declarations in admission order.
///
/// # Examples
///
/// Stage a declaration, admit it, watch an ill-typed one refused, and audit
/// what the admitted one rests on:
///
/// ```rust
/// use gandr_kernel_core::Environment;
/// use gandr_kernel_core::KernelError;
/// use gandr_kernel_term::BaseType;
/// use gandr_kernel_term::LevelSignature;
///
/// fn example() -> Result<(), KernelError>
/// {
///     let mut environment = Environment::new();
///
///     let unit = {
///         let mut staging = environment.stage();
///         let declared = staging.arena().value_type_unit();
///         let body = staging.arena().value_unit();
///         staging.def(LevelSignature::monomorphic(), declared, body)
///     };
///     let admitted = environment.add_decl(unit)?;
///
///     let ill_typed = {
///         let mut staging = environment.stage();
///         let declared = staging.arena().value_type_base(BaseType::Integer);
///         let body = staging.arena().value_unit();
///         staging.def(LevelSignature::monomorphic(), declared, body)
///     };
///     assert!(environment.add_decl(ill_typed).is_err());
///
///     let report = environment.audit(admitted);
///     assert!(report.axioms().is_empty());
///     assert!(report.unchecked_admissions().is_empty());
///     Ok(())
/// }
/// ```
#[derive(Clone, Debug, Default)]
pub struct Environment
{
    /// The one arena every declaration's content lives in.
    arena: TermArena,
    /// The admitted declarations, in admission order: those a freeze froze
    /// shared with every clone made after.
    entries: Entries,
    /// The committer's own part of the log: the rank index, the order, the
    /// reverse index and the generative index. No view holds it, so a check
    /// reads none of it. A clone of the environment shares it, and a commit
    /// copies it while another environment shares it.
    commits: alloc::sync::Arc<CommitLog>,
    /// The admission floor: the watermark at the most recent admission,
    /// checked or bypassed. No rejection truncates below it.
    admission_floor: ArenaWatermark,
    /// The content-start marks of declarations staged into the arena and not
    /// yet resolved. What a rejection may not truncate through.
    outstanding: StagedMarks,
    /// The atoms whose minting admission is open, ascending: what a
    /// declaration admitted now reads as its representation.
    manifest: Vec<ConstantIndex>,
    /// The position of each abstract type admitted, ascending, open or
    /// closed: the atoms whose scopes a key reads.
    atoms: Vec<ConstantIndex>,
    /// The verdict state: the policy, the receipts verified and the verdicts
    /// checked here.
    verdicts: crate::verdict::Verdicts,
    /// The session every admission's check is lent, whose names outlive the
    /// admission.
    names: Names,
    /// Whether a check takes a closed pair's admitted result or derives it.
    admitting: crate::admitted::AdmissionPolicy,
    /// How many admitted results this environment's checks took.
    admitted: crate::admitted::AdmittedCount,
    /// The fork that the last drain of each check runs its obligations
    /// through, if any.
    forking: crate::fork::SharedFork,
    /// The releases whose commits the cursor has not folded, and what each
    /// outstanding release holds. Only the committer reads it.
    releases: crate::releases::Releases,
    /// What a release behind the cursor predicts of the earlier commits.
    speculation: crate::speculation::Speculation,
    /// How many predictions the fold found wrong and set right, and how many
    /// outstanding releases a drop took back.
    rollbacks: crate::speculation::Rollbacks,
}

impl Environment
{
    /// An empty environment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// An empty environment that keys its admissions and recalls the verdicts
    /// `policy` trusts from `source`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn recalling(
        policy: crate::verdict::TrustPolicy,
        source: alloc::sync::Arc<dyn crate::verdict::VerdictSource>,
    ) -> Self
    {
        Self::recalling_under(policy, source, crate::build_identity())
    }

    /// An empty environment that keys its admissions under the build
    /// identity `build`, and recalls the verdicts `policy` trusts from
    /// `source`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn recalling_under(
        policy: crate::verdict::TrustPolicy,
        source: alloc::sync::Arc<dyn crate::verdict::VerdictSource>,
        build: crate::verdict::BuildIdentity,
    ) -> Self
    {
        Self {
            verdicts: crate::verdict::Verdicts::under(policy, source, build),
            ..Self::default()
        }
    }

    /// The same environment, its checks standing on admitted results as
    /// `policy` states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn admitting(
        self,
        policy: crate::admitted::AdmissionPolicy,
    ) -> Self
    {
        Self {
            admitting: policy,
            ..self
        }
    }

    /// The same environment, the last drain of each of its checks running its
    /// obligations as `fork` states. The fork changes no verdict: a part that
    /// refuses sends the check back to its serial drain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn forking(
        self,
        fork: crate::fork::SharedFork,
    ) -> Self
    {
        Self {
            forking: fork,
            ..self
        }
    }

    /// The same environment, each release behind the cursor predicting what
    /// `speculation` states. A prediction changes no outcome, entry or
    /// record: the fold checks each one, and sets a wrong one right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn speculating(
        self,
        speculation: crate::speculation::Speculation,
    ) -> Self
    {
        Self {
            speculation,
            ..self
        }
    }

    /// What a release behind the cursor predicts of the earlier commits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn speculation(&self) -> crate::speculation::Speculation
    {
        self.speculation
    }

    /// How many predictions the fold found wrong and set right, and how many
    /// outstanding releases a drop took back, since the environment began or
    /// since [`Self::handed_on`] made it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rollbacks(&self) -> crate::speculation::Rollbacks
    {
        self.rollbacks
    }

    /// This environment for a later run that resumes it: the same arena and
    /// declarations, and the names and kept outcomes of its session, without
    /// the verdicts this run checked or recalled, which its
    /// own receipt and [`Self::recalls`] answer for. After a [`Self::freeze`]
    /// the copy shares the session until its first check; before one, it
    /// copies the session at once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every read of the declarations answers as `self` answers it,
    ///   and a declaration admitted next is keyed and answered from kept
    ///   outcomes as it would be in `self`; [`Self::receipt`] answers absent
    ///   and [`Self::recalls`] zero until the copy admits a declaration.
    /// - provides: the environment a readmission records for another to resume,
    ///   so each receipt signs only what its own run checked.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses compare the copy's answers to every
    ///   later admission with `self`'s, which no predicate over one call reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a copy handed on after a recorded run recalls a later
    ///   declaration under the key the run would have given it, stands on the
    ///   outcomes the run kept, and neither signs nor counts what the run
    ///   admitted.
    /// - witness: `tests::verdicts::a_handed_on_environment_keys_on_and_signs_only_its_own`
    /// - witness: `environment::tests::a_handed_on_environment_stands_on_the_kept_outcomes_of_its_run_6468`
    #[inline]
    #[must_use]
    pub fn handed_on(&self) -> Self
    {
        Self {
            arena: self.arena.clone(),
            entries: self.entries.clone(),
            commits: alloc::sync::Arc::clone(&self.commits),
            admission_floor: self.admission_floor,
            outstanding: self.outstanding.clone(),
            manifest: self.manifest.clone(),
            atoms: self.atoms.clone(),
            verdicts: self.verdicts.handed_on(),
            names: self.names.carried(),
            admitting: crate::admitted::AdmissionPolicy::Derive,
            admitted: crate::admitted::AdmittedCount::NONE,
            forking: crate::fork::SharedFork::serial(),
            // A copy taken while a check is released holds its reservation,
            // which no settle of the copy fills, so the copy refuses what
            // reads the order of every commit.
            releases: self.releases.clone(),
            speculation: crate::speculation::Speculation::OFF,
            rollbacks: crate::speculation::Rollbacks::NONE,
        }
    }

    /// Share the arena's nodes, the admitted declarations and the reverse
    /// index of their references with every clone of the environment made
    /// after: such a clone copies, and its drop releases, only what was minted
    /// and admitted after the freeze ([`TermArena::freeze`],
    /// [`Family::freeze`](gandr_kernel_term::Family::freeze)). Share the
    /// session's names and kept outcomes with every environment
    /// [`Self::handed_on`] makes after: the first check of an environment
    /// that shares them with another copies them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arena's watermark and the entries are unchanged, and
    ///   admission, rejection and every read answer as they would have
    ///   unfrozen.
    /// - provides: the environment a readmission records, which each
    ///   readmission resuming it copies at the cost of what it admits, and of
    ///   the session when it checks a declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an environment frozen after one admission and cloned
    ///   admits a definition reading the frozen one and refuses a bad one as an
    ///   environment built alike and never frozen does, and the environment it
    ///   was cloned from sees neither.
    /// - witness: `environment::tests::a_frozen_environment_admits_as_one_never_frozen`
    #[spec(
        captures: [entry_mark = self.arena.watermark(), entry_len = self.entries.len()],
        ensures: self.arena.watermark() == entry_mark && self.entries.len() == entry_len,
    )]
    #[inline]
    pub fn freeze(&mut self)
    {
        self.arena.freeze();
        self.entries.freeze();
        // A log that another environment shares stays as it is: a freeze of
        // it here would copy the whole log first.
        if let Some(commits) = alloc::sync::Arc::get_mut(&mut self.commits) {
            commits.dependents.freeze();
        }
        self.names.share();
    }

    /// The arena, for a consumer reading admitted content.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &TermArena
    {
        &self.arena
    }

    /// The admitted declarations, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn entries(&self) -> &Entries
    {
        &self.entries
    }

    /// Whether the environment keys its admissions, as its policy states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn keying(&self) -> crate::verdict::Keying
    {
        self.verdicts.keying()
    }

    /// The positions of the live entries, in rank order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn in_rank_order(&self) -> impl Iterator<Item = ConstantIndex> + '_
    {
        self.commits.in_rank_order()
    }

    /// The place of each live position in rank order, which the export of a
    /// kept environment writes for that position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: absent as [`places::Absent::InOrder`] while no entry is
    ///   retired, no slot is a vacancy, and each entry is admitted at a rank
    ///   above each earlier entry's rank; then each live position is its own
    ///   place, and the answer reads no entry. Otherwise each live position's
    ///   place is its index in [`Self::in_rank_order`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — each clause walks the live positions in rank order,
    ///   and a capture runs in every build.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a kept environment over the kernel's generated
    ///   sources exports the bytes of a fresh admission for each class of edit;
    ///   an environment with nothing retired builds no places.
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    /// - witness: `environment::tests::an_export_by_position_after_a_retire_differs_6845`
    #[inline]
    pub fn places(&self) -> Maybe<gandr_kernel_term::Places, places::Absent>
    {
        self.commits.places(self.entries.len())
    }

    /// The reach of an edit to the entries at `edited`: each of them, with
    /// each entry whose support holds an entry of the reach, ascending; a
    /// retired entry stands in no reach.
    ///
    /// An entry outside the reach keeps its whole verdict input: the entries
    /// that its support holds are outside the reach too. So a readmission
    /// offers the kernel the reach of an edit, and nothing else.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ascending, each once, each below [`Entries::len`] and each
    ///   live; each live edited position below it, and each live entry whose
    ///   support holds an entry of the result through its direct references,
    ///   its mutual block or a type of words admitted before it over a sort
    ///   that it holds.
    /// - provides: the entries whose verdict an edit can change.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the reach of each edit of a generated environment
    ///   equals the entries whose support holds an edited entry, after refused
    ///   blocks roll back, and a type of words reaches an entry after it
    ///   through its sort and no entry before it.
    /// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
    /// - witness: `environment::presented_tests::a_type_of_words_reaches_the_entries_after_it_through_its_sort_6621`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(*pair, [earlier, later] if earlier < later)) && ret.iter().all(|&position| usize::from(position) < usize::from(self.entries.len())))]
    #[inline]
    #[must_use]
    pub fn reach<Edited>(
        &self,
        edited: Edited,
    ) -> Box<[ConstantIndex]>
    where
        Edited: IntoIterator<Item = ConstantIndex>,
    {
        self.commits.reach(&self.entries, edited)
    }

    /// Admit `entry` after every entry: the entries and the committer's own
    /// tables each take its rows.
    ///
    /// # Specification
    /// trivial.
    fn enter(
        &mut self,
        entry: AdmittedDeclaration,
    )
    {
        let position = ConstantIndex::from(usize::from(self.entries.len()));
        alloc::sync::Arc::make_mut(&mut self.commits)
            .admit((position, entry.rank()), entry.references());
        self.entries.push(&self.arena, entry);
    }

    /// Leave a vacancy at the next position, in the entries and in the
    /// committer's own tables.
    ///
    /// # Specification
    /// trivial.
    fn vacate(&mut self)
    {
        let position = ConstantIndex::from(usize::from(self.entries.len()));
        alloc::sync::Arc::make_mut(&mut self.commits).vacate(position);
        self.entries.vacate();
    }

    /// Begin building one declaration's content into this environment's arena.
    ///
    /// # Specification
    /// - requires: the returned session builds at most one declaration's
    ///   content and is then finalized or abandoned, with no other allocation
    ///   into the arena interleaved.
    /// - ensures: a [`Staging`] borrowing the arena and the session's table,
    ///   which names every constant admitted so far, with its content-start
    ///   watermark registered as outstanding. Abandoning the session truncates
    ///   each family to the lesser of its current and entry lengths and
    ///   resolves the mark, so no partially minted content survives and no
    ///   probe-before-stage discipline is owed. Finishing the session keeps the
    ///   mark outstanding until the resulting declaration is admitted,
    ///   bypassed, or abandoned.
    /// - provides: the construction surface every arena-resident declaration is
    ///   built through. Registration is checked at return; the later
    ///   finish/drop transitions outlive this call and are witnessed
    ///   separately.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the registration and its release,
    ///   separated by an abandoned session (which leaves nothing outstanding,
    ///   so an earlier declaration still admits) and a finished one (which
    ///   does, so an earlier declaration is refused).
    /// - witness: `environment::tests::an_abandoned_staging_leaves_the_arena_unchanged`
    /// - witness: `environment::tests::an_abandoned_staging_releases_its_claim`
    /// - witness: `environment::tests::implicit_staging_drop_releases_its_claim`
    /// - witness: `environment::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        captures: [entry_mark = self.arena.watermark(), entry_len = self.outstanding.marks.len()],
        ensures: |ret| ret.builder().content_start() == entry_mark
            && ret.claim().outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
            && ret.claim().outstanding.marks.last() == Some(&entry_mark)
    )]
    #[inline]
    pub fn stage(&mut self) -> Staging<'_>
    {
        let Self {
            ref mut arena,
            ref mut outstanding,
            ref mut names,
            ref entries,
            ..
        } = *self;
        let session = names.session_mut();
        session.name_constants(entries);
        Staging::new(arena, outstanding, session.table_mut())
    }

    /// Release a staged declaration without admitting it.
    ///
    /// The named counterpart of dropping a [`StagedDeclaration`] on the floor,
    /// and the only way to say so: a staged declaration holds no reference to
    /// the environment, so nothing else can observe that the producer is done
    /// with it. Until it is released, every declaration staged before it is
    /// refused, because a rollback to their marks would truncate through this
    /// one's content.
    ///
    /// # Specification
    /// - requires: `staged` was produced by this environment's [`Self::stage`].
    /// - ensures: the mark is resolved. The content is truncated away when
    ///   nothing outstanding sits above it and the admission floor permits —
    ///   the same clamp a rejection takes — and retained as an unreachable
    ///   orphan otherwise, since a contiguous watermark cannot release a
    ///   disjoint region. No admitted entry, audit, or later admission is
    ///   affected either way.
    /// - provides: the release that keeps the outstanding set honest.
    ///   Environment provenance and preservation of every audit and later
    ///   admission remain prose-only: staging carries no environment identity,
    ///   and a full comparison would require owning snapshots and future
    ///   executions.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the resolution and the
    ///   truncate-or-retain branch, separated by an abandonment with nothing
    ///   above it (the arena shrinks and an earlier declaration then admits)
    ///   and one with content above it (the arena is unchanged and the content
    ///   above still resolves).
    /// - witness: `environment::tests::abandoning_a_staged_declaration_releases_its_claim`
    /// - witness: `environment::tests::abandoning_beneath_outstanding_content_retains_it`
    /// - witness: `environment::tests::abandonment_preserves_the_admission_floor`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body resolves the mark and asks whether anything sits above it, each a walk of the outstanding marks; the check counts and clamps them the same way"
        )
    )]
    #[spec(
        captures: [
            entry_mark = staged.content_start(),
            entry_len = self.outstanding.marks.len(),
            entry_count = self.outstanding.marks.iter().filter(|&&held| held == staged.content_start()).count(),
            entry_entries = self.entries.len(),
            entry_floor = self.admission_floor,
            expected_mark = if self.outstanding.marks.iter().any(|&held| held.clamped_into(ArenaWatermark::default(), staged.content_start()) != held) {
                self.arena.watermark()
            } else {
                staged.content_start().clamped_into(self.admission_floor, self.arena.watermark())
            }
        ],
        ensures: self.arena.watermark() == expected_mark
            && self.admission_floor == entry_floor && self.entries.len() == entry_entries
            && self.outstanding.marks.len() == entry_len.saturating_sub(usize::from(entry_count != 0_usize))
            && self.outstanding.marks.iter().filter(|&&held| held == entry_mark).count() == entry_count.saturating_sub(1_usize)
    )]
    #[inline]
    #[expect(
        clippy::needless_pass_by_value,
        reason = "release consumes the staged declaration: taking it by value is what makes a \
                  released staging unofferable, and a reference would leave the producer holding \
                  a token the environment has already resolved"
    )]
    pub fn abandon(
        &mut self,
        staged: StagedDeclaration,
    )
    {
        let content_start = staged.content_start();
        self.outstanding.resolve(content_start);
        if matches!(
            self.outstanding_above(content_start),
            OutstandingContent::Absent
        ) {
            let current = self.arena.watermark();
            self.arena
                .truncate_to(content_start.clamped_into(self.admission_floor, current));
        }
    }

    /// Whether staged, unresolved content sits above `mark`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `OutstandingContent::Present` exactly when at least one
    ///   unresolved mark sits strictly above `mark` componentwise, and `Absent`
    ///   otherwise.
    /// - provides: the nominal answer a rejection's truncation is gated on, so
    ///   the two cases stay unmistakable for any other yes-or-no in this
    ///   module.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — later outstanding content refuses an earlier
    ///   admission; abandoning that later content removes the obstruction.
    ///   Equal and lower marks are separated by the componentwise count `above`
    ///   in `gandr-kernel-core-base`, which carries its own witness.
    /// - witness: `environment::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `environment::tests::abandoning_a_staged_declaration_releases_its_claim`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body counts the marks above through one walk; the check searches the same marks once"
        )
    )]
    #[spec(ensures: |ret| matches!(ret, OutstandingContent::Present)
        == self.outstanding.marks.iter().any(|&held| held.clamped_into(ArenaWatermark::default(), mark) != held))]
    #[inline]
    fn outstanding_above(
        &self,
        mark: ArenaWatermark,
    ) -> OutstandingContent
    {
        if usize::from(self.outstanding.above(mark)) == 0 {
            OutstandingContent::Absent
        }
        else {
            OutstandingContent::Present
        }
    }

    /// Admit a declaration through the checked choke point, or on a verdict
    /// recorded for the same input under a receipt this environment's policy
    /// trusts, by its entry key.
    ///
    /// # Specification
    /// - requires: `staged` was built into this environment's arena through
    ///   [`Self::stage`]; every well-formedness and typing obligation is
    ///   re-derived here, granting the producer no credence.
    /// - ensures: `Ok(id)` with an unforgeable [`CheckedId`] exactly when the
    ///   declaration's level signature admits, its declared type forms, its
    ///   sealing provenance re-derives, and a definition's body checks against
    ///   that type. The declaration is appended, its audit precomputed, the
    ///   arena holds prior content plus this declaration's, the checker's
    ///   intermediates left with the clone it ran on, and the admission floor
    ///   rises to that mark. The entry keeps the [`ExpansionCensus`] its check
    ///   charged, empty when a recorded verdict admitted it. On any failure the
    ///   arena is truncated to this declaration's content-start clamped into
    ///   `[admission floor, checker-entry mark]`, so every caller-observable
    ///   face of the environment is exactly what it was before the call. When
    ///   the environment keys its admissions ([`Self::recalling`] under a
    ///   trusting policy) and the declaration has a content key, its entry key
    ///   binds that content key to the build. A key a verified receipt from a
    ///   trusted signer attests admits the declaration as
    ///   [`Admission::Recalled`] with the recorded reading and without the
    ///   check; any other key is checked and, on success, recorded for
    ///   [`Self::receipt`] unless its check took an admitted result
    ///   ([`crate::admitted`]), since a receipt attests only what the kernel
    ///   checked itself. A refusal is never recorded.
    /// - provides: the one checked entry into the kernel. It takes **no memo**,
    ///   which is the structural form of the memo's one-call lifetime: nothing
    ///   an earlier check recorded can reach a later one through this entry. A
    ///   recall happens only here, where the kernel computed the key itself.
    /// - fails: [`KernelError::OutstandingStagedContent`] when a declaration
    ///   staged after this one is still unresolved, since no clamp can preserve
    ///   a disjoint region and a rejection would otherwise truncate through
    ///   content the producer still holds; otherwise any [`KernelError`] the
    ///   level admission or the checker surfaces.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::OutstandingStagedContent`], or any [`KernelError`].
    ///
    /// # Adequacy
    /// - hypothesis: L0/L2 — a [`CheckedId`] is unforgeable outside this crate,
    ///   and the corpus pins acceptance of well-typed declarations against
    ///   rejection of ill-typed ones; the L3 residues are the constant
    ///   resolution boundary, the arena-restored-on-rejection property asserted
    ///   through the arena's own watermark, and the outstanding-content guard,
    ///   separated in both directions — the refusal fires with a later staging
    ///   live, and an in-order producer sees the guard and the clamp change
    ///   nothing. A declaration recorded by a trusted signer is recalled under
    ///   its own key, refused after one name changes, refused under an unlisted
    ///   signer or a tampered record, and never recalled under
    ///   [`TrustPolicy::Recheck`](crate::verdict::TrustPolicy::Recheck). A
    ///   rejection between two declarations changes no later key. A declaration
    ///   that names the vacancy of a rejection has no entry key, so it is
    ///   checked and refused.
    /// - witness: `environment::tests::a_definition_referencing_a_prior_one_checks`
    /// - witness: `environment::tests::a_forward_constant_reference_is_unbound`
    /// - witness: `environment::tests::a_rejected_declaration_leaves_a_vacancy_at_its_position`
    /// - witness: `environment::tests::a_rejection_keeps_a_prior_admission_resolvable`
    /// - witness: `environment::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `environment::tests::an_in_order_producer_is_never_refused`
    /// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
    /// - witness: `tests::verdicts::an_unlisted_signer_recalls_nothing`
    /// - witness: `tests::verdicts::a_tampered_record_recalls_nothing`
    /// - witness: `tests::verdicts::a_rechecking_environment_recalls_nothing`
    /// - witness: `tests::verdicts::a_rejected_declaration_leaves_the_keys_as_if_never_offered_6566`
    /// - witness: `tests::verdicts::a_declaration_that_names_the_vacancy_of_a_rejection_is_checked_7426`
    /// - witness: `element_identity::tests::a_declaration_that_took_an_admitted_result_keeps_no_verdict_3558`
    // The predicate covers the two structural halves of the success
    // postcondition: exactly one entry is appended, and the admission floor
    // ends at the arena's own watermark — that is, the checker's intermediates
    // left with its clone rather than entering the arena. Whether the
    // declaration is *well-typed* is what the body decides and is not restated
    // here.
    #[inline]
    #[spec(captures: [entry_len = self.entries.len()], ensures: |ret| ret.is_err()
        || (arith::Int::from(usize::from(self.entries.len())) == arith::add(arith::Int::from(usize::from(entry_len)), arith::Int::from(1_usize))
            && self.admission_floor == self.arena.watermark()))]
    pub fn add_decl(
        &mut self,
        staged: StagedDeclaration,
    ) -> Result<CheckedId, KernelError>
    {
        match self.release(staged)? {
            Released::Running(pending, check) => {
                let ran = check.run();
                self.settle(pending, ran)
            },
            // A hold reads a commit that only the caller can settle, so the
            // declaration waits for it outside this call.
            Released::Held(..) => Err(KernelError::UnsettledReleases {
                unsettled: self.releases.outstanding(),
            }),
        }
    }

    /// How many released checks of this environment are not settled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unsettled(&self) -> UnsettledCount
    {
        self.releases.outstanding()
    }

    /// Release the check of a lone declaration at the next position: the
    /// guards, the keys and the recall run here, and the check runs apart from
    /// the environment, on any thread, until [`Self::settle`] commits what it
    /// found. Earlier releases may be outstanding, and their commits come in
    /// any order that the dependences allow.
    ///
    /// # Specification
    /// - requires: `staged` was built into this environment's arena through
    ///   [`Self::stage`], and the content that each declaration it names holds
    ///   is committed.
    /// - ensures: a running check holds the declaration's place, keys,
    ///   references, marks and name, and its check: the reading of a verdict
    ///   that a trusted record holds under its key, or a check that owns a view
    ///   of the entries below its rank through its support, a clone of the
    ///   frozen arena and a fork of the session. Its position is reserved, and
    ///   no read sees it until the settle. A held declaration comes back
    ///   unchanged, with its staged mark outstanding, when its release reads an
    ///   earlier commit that has not come ([`Hold`]); nothing else changes
    ///   then.
    /// - fails: as [`Self::add_decl`] fails before its check.
    /// - panics: none.
    /// - executable: none — the clauses state what the check owns, which no
    ///   predicate over one call reads.
    ///
    /// # Errors
    /// [`KernelError::OutstandingStagedContent`] when a declaration staged
    /// after this one is still unresolved, [`KernelError::RankTaken`] when a
    /// live entry holds its rank, and the refusal of its levels, which leaves
    /// a vacancy at its position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a check released from the environment crosses threads
    ///   and settles as [`Self::add_decl`] admits; each witness of
    ///   [`Self::add_decl`] runs through it. Releases settled in each order
    ///   that their dependences allow give the entries, ranks, keys, names,
    ///   refusals, records, order and reach of the serial run; a hold that does
    ///   not fire for one read of order changes one of them.
    /// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
    /// - witness: `environment::tests::a_rejected_declaration_leaves_a_vacancy_at_its_position`
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[inline]
    pub fn release(
        &mut self,
        staged: StagedDeclaration,
    ) -> Result<Released, KernelError>
    {
        let (content_start, staged_rank, declaration) = staged.into_parts();
        // The guard, before anything is truncated: a declaration staged after
        // this one owns arena nodes above this one's content-start, and the
        // rollback below is a contiguous truncation that cannot spare them.
        // Refusing is the fail-closed answer; the alternative is deleting a
        // live producer's content, or worse, letting a later staging
        // re-mint those indices so a subsequent admission checks other
        // content under that declaration's name.
        self.outstanding.resolve(content_start);
        let above = self.outstanding.above(content_start);
        if usize::from(above) != 0 {
            self.outstanding.register(content_start);
            return Err(KernelError::OutstandingStagedContent { above });
        }
        let position = ConstantIndex::from(usize::from(self.entries.len()));
        // A readmission that keeps entries in place sets the next rank: a
        // declaration staged with no rank takes it there, where a fresh
        // admission of the edited source ranks it ([`Self::ranking_from`]).
        let staged_rank = staged_rank.or_else(|| {
            match CommitLog::placed(
                &mut self.commits,
                position .. ConstantIndex::from(usize::from(position).saturating_add(1)),
            ) {
                Maybe::Present(rank) => Some(rank),
                Maybe::Absent(_) => None,
            }
        });
        // The cursor stands at this release when no earlier release is
        // outstanding. Then every read of order reads the serial state.
        let alone = usize::from(self.releases.outstanding()) == 0;
        // A declaration staged with no rank ranks past every live entry, so a
        // vacancy before it moves its position and not its rank. Behind the
        // cursor, with `speculation.rank` on, it takes the rank past each
        // reservation, as if each outstanding release admits; the fold
        // checks the rank at the cursor ([`Self::settle_rank`]).
        let committed = self.commits.past_ranks();
        let ranked = if alone {
            crate::releases::Ranked::Serial
        }
        else {
            match self.releases.rank(
                staged_rank.map_or(Maybe::Absent(unranked::Absent::Unranked), Maybe::Present),
                committed,
                self.speculation.rank,
            ) {
                Maybe::Present(hold) => {
                    return Ok(self.hand_back(
                        StagedDeclaration::new(content_start, staged_rank, declaration),
                        hold,
                    ));
                },
                Maybe::Absent(crate::releases::free::Absent::Unread) => {
                    crate::releases::Ranked::Serial
                },
                Maybe::Absent(crate::releases::free::Absent::Predicted) => {
                    crate::releases::Ranked::Predicted
                },
            }
        };
        let rank = staged_rank.unwrap_or_else(|| self.releases.past(committed));
        let content_end = self.arena.watermark();
        // The rejection mark: this declaration's content-start, clamped into
        // `[admission floor, content-end]`, so a rollback can neither delete an
        // admitted declaration's content nor retain a checker intermediate.
        let rejected = content_start.clamped_into(self.admission_floor, content_end);
        if let Some(by) = self.commits.ranked(rank) {
            self.arena.truncate_to(rejected);
            return Err(KernelError::RankTaken { rank, by });
        }
        let levels = match LevelContext::admit(
            declaration.levels().params(),
            declaration.levels().constraints().to_vec(),
        ) {
            Ok(levels) => levels,
            Err(error) => {
                // Its position stays as a vacancy.
                self.arena.truncate_to(rejected);
                if alone {
                    self.vacate();
                }
                else {
                    self.entries.vacate();
                    self.releases.vacate();
                }
                return Err(error);
            },
        };
        let content = self.content_key(
            core::slice::from_ref(&declaration),
            (position, core::slice::from_ref(&rank)),
        );
        let generative = !matches!(
            *declaration.content(),
            DeclarationContent::Def { .. } | DeclarationContent::LiteralIdentity { .. }
        );
        let entry_content = match content {
            Maybe::Present(content) if generative => Maybe::Present(
                content.generative(self.commits.generative_count(&self.entries, content, rank)),
            ),
            Maybe::Present(_) | Maybe::Absent(_) => content,
        };
        let entry_key = self.entry_key(entry_content);
        let generative_content = match (generative, content) {
            (true, Maybe::Present(content)) => Maybe::Present(content),
            (true, Maybe::Absent(_)) => Maybe::Absent(crate::releases::generative::Absent::Unkeyed),
            (false, Maybe::Present(_) | Maybe::Absent(_)) => {
                Maybe::Absent(crate::releases::generative::Absent::Plain)
            },
        };
        // The name reads the definitions ranked below this one, which every
        // earlier commit holds unless an outstanding one is alike.
        let key_name = self.definition_name(&declaration, rank);
        let sway = sway(&declaration);
        if !alone
            && let Maybe::Present(hold) =
                self.reads_order((sway, rank), generative_content, key_name)
        {
            return Ok(self.hand_back(
                StagedDeclaration::new(content_start, staged_rank, declaration),
                hold,
            ));
        }
        // The entry key alone, which an edit that the declaration does not read
        // leaves alone, wherever the edit stands in the admission order.
        let recalled = match entry_key {
            Maybe::Present(entry_key) => self.verdicts.recall(entry_key),
            Maybe::Absent(_) => Maybe::Absent(crate::verdict::stored::Absent::Unrecorded),
        };
        let named = references(&self.arena, &declaration);
        // The slot first, so the view that the check takes shares the log
        // that the next write would otherwise copy.
        self.entries.reserve();
        self.releases.reserve(
            position,
            crate::releases::Reservation::new(rank, sway, generative_content, key_name),
            ranked,
        );
        // The session names the reservation as the commit will, before the
        // check: a data type's constructors read their type, and a later
        // release reads the position. Content staged before this read its own
        // position past the table's end, so its placements go.
        {
            let session = self.names.session_mut();
            session.name_constants(&self.entries);
            session.table_mut().name_ahead(
                position,
                [crate::encoding::ConstantName::table_name(
                    key_name,
                    entry_content,
                )],
                named
                    .binary_search(&position)
                    .is_ok()
                    .then_some(content_start),
            );
        }
        let way = match recalled {
            Maybe::Present(accessibility) => Way::Recalled(accessibility),
            // The check reads through the support its content names, and a
            // read outside it refuses the declaration whatever the check
            // decided.
            Maybe::Absent(crate::verdict::stored::Absent::Unrecorded) => Way::Checking(
                self.open_scope(
                    (&named, rank),
                    gandr_kernel_term::ArenaLength::from(usize::from(position)),
                ),
                Judged {
                    levels,
                    manifest: self.manifest.clone(),
                    admitting: self.admitting,
                    forking: self.forking.clone(),
                },
            ),
        };
        Ok(Released::Running(
            Pending {
                place: (position, rank),
                content: (content, generative),
                keys: (entry_content, entry_key),
                references: named,
                marks: (content_end, rejected),
                key_name,
            },
            Check { declaration, way },
        ))
    }

    /// Hand `staged` back for `hold`: its staged mark stays outstanding, so
    /// the release that follows the settles resolves it.
    ///
    /// # Specification
    /// trivial.
    fn hand_back(
        &mut self,
        staged: StagedDeclaration,
        hold: Hold,
    ) -> Released
    {
        self.outstanding.register(staged.content_start());
        Released::Held(staged, hold)
    }

    /// Why a release behind the cursor reads an earlier commit that has not
    /// come: the manifest, a declaration that each later check reads, or the
    /// same generative content or plain definition ranked below it. `sway` and
    /// `rank` state the declaration, `generative` its content key when it is
    /// generative, and `key_name` its name.
    ///
    /// # Specification
    /// - requires: an earlier release is outstanding, and `key_name` names the
    ///   declaration's content in this environment's arena.
    /// - ensures: absent only when no read of order that the release makes
    ///   reads an outstanding release.
    /// - provides: the first hold that applies, in the order of the variants of
    ///   [`Hold`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state what the outstanding releases
    ///   would change, which no predicate over one call reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::release`].
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    fn reads_order(
        &mut self,
        (sway, rank): (crate::releases::Sway, SourceRank),
        generative: Maybe<crate::verdict::EntryContentKey, crate::releases::generative::Absent>,
        key_name: ConstantName,
    ) -> Maybe<Hold, crate::releases::free::Absent>
    {
        if !self.manifest.is_empty() {
            return Maybe::Present(Hold::Manifest);
        }
        if let Maybe::Present(hold) = self.releases.ordering(sway) {
            return Maybe::Present(hold);
        }
        if let Maybe::Present(content) = generative
            && let Maybe::Present(hold) = self.releases.generative(content, rank)
        {
            return Maybe::Present(hold);
        }
        if let ConstantName::Definition { digest, .. } = key_name
            && crate::encoding::likeness(
                self.names.session_mut().table_mut(),
                &self.arena,
                key_name,
                self.releases.definitions(digest, rank),
            ) == crate::encoding::Likeness::Alike
        {
            return Maybe::Present(Hold::Content);
        }
        Maybe::Absent(crate::releases::free::Absent::Unread)
    }

    /// Settle a released check at its reserved position: take back the scope
    /// that it ran in, refuse a read outside its support, and commit what it
    /// found. The cursor then folds each slot whose commit came, in position
    /// order.
    ///
    /// # Specification
    /// - requires: `pending` and the check that `ran` answers come from one
    ///   [`Self::release`] of this environment.
    /// - ensures: as [`Self::add_decl`] ensures after its check: on an outcome
    ///   that admits, one entry at the reserved position; on a refusal, a
    ///   vacancy there. The length is unchanged. The session holds what the
    ///   check named, and the entries hold no horizon.
    /// - panics: none.
    ///
    /// # Errors
    /// The refusal of the check, or [`KernelError::OutsideSupport`] at the
    /// first position that it read outside its support.
    /// [`KernelError::KeptOutcomesDisagree`] refuses the environment when the
    /// check kept an outcome under a key that the environment kept with
    /// another outcome since the release. [`KernelError::UnboundConstant`]
    /// when no reservation of this environment stands at the position.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::release`].
    /// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
    /// - witness: `environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[inline]
    #[spec(captures: [entry_len = self.entries.len()], ensures: |ret| self.entries.len() == entry_len && self.entries.check_horizon().is_none())]
    pub fn settle(
        &mut self,
        pending: Pending,
        ran: Ran,
    ) -> Result<CheckedId, KernelError>
    {
        let Ran {
            declaration,
            outcome,
            admission,
            census,
            took,
            scope,
        } = ran;
        let outcome = match scope {
            Maybe::Present(scope) => self.close_scope(scope, outcome),
            Maybe::Absent(ran::Absent::Recalled) => outcome,
        };
        let Pending {
            place,
            content,
            keys,
            references,
            marks,
            key_name,
        } = pending;
        self.commit(Lone {
            declaration,
            place,
            content,
            keys,
            references,
            census,
            took,
            outcome,
            admission,
            marks,
            key_name,
        })
    }

    /// Drop each release after the release of `pending`: their reservations,
    /// their slots and their staged content leave the environment, as if
    /// none of them was made. The check of each dropped release comes back
    /// through [`Self::discard`], and the caller releases each dropped
    /// declaration again in module order.
    ///
    /// # Specification
    /// - requires: `pending` comes from a [`Self::release`] of this
    ///   environment, and no admission after its position is committed.
    /// - ensures: the entries end past the position of `pending`, the queue of
    ///   releases ends at its slot, the arena ends at the mark past its
    ///   content, and the count of rollbacks grows by one for each outstanding
    ///   release dropped. Nothing changes on an error.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::UnboundConstant`] at the position of `pending` when the
    /// cursor passed it, or when an admission after it is committed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a drop that keeps a later slot, an index or staged
    ///   content gives the releases again other positions, ranks or content
    ///   than the serial run.
    /// - witness: `environment::tests::a_drop_after_a_release_leaves_the_serial_run_3476`
    /// - witness: `environment::tests::a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281`
    #[spec(captures: [entry_len = self.entries.len(), place = pending.place.0], ensures: |ret| match ret.as_ref() {
        Ok(&()) => usize::from(self.entries.len()) == usize::from(place).saturating_add(1),
        Err(_) => self.entries.len() == entry_len,
    })]
    #[inline]
    pub fn drop_after(
        &mut self,
        pending: &Pending,
    ) -> Result<(), KernelError>
    {
        let (position, _) = pending.place;
        let cursor =
            usize::from(self.entries.len()).saturating_sub(usize::from(self.releases.unfolded()));
        let Some(offset) = usize::from(position)
            .checked_sub(cursor)
            .map(gandr_kernel_term::ArenaLength::from)
        else {
            return Err(KernelError::UnboundConstant { index: position });
        };
        let Maybe::Present(dropped) = self.releases.drop_after(offset)
        else {
            return Err(KernelError::UnboundConstant { index: position });
        };
        self.entries.truncate(gandr_kernel_term::ArenaLength::from(
            usize::from(position).saturating_add(1),
        ));
        // The content of each dropped release lies above the content of
        // `pending`, and no admission after it raised the floor.
        let (content_end, _) = pending.marks;
        self.arena
            .truncate_to(content_end.clamped_into(self.admission_floor, self.arena.watermark()));
        for _ in 0 .. usize::from(dropped) {
            self.rollbacks = self.rollbacks.and_one();
        }
        Ok(())
    }

    /// Discard the run of a dropped release: take back the scope that its
    /// check ran in, and forget what the check found.
    ///
    /// # Specification
    /// - requires: `ran` answers the check of a release that
    ///   [`Self::drop_after`] dropped from this environment.
    /// - ensures: the entries hold the buffer of the support of the check's
    ///   view again, the arena forgets the nodes of the check's clone, and no
    ///   outcome or record of the check reaches the environment.
    /// - panics: none.
    /// - executable: none — the scope is private to the run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a discard that folds the check's session keeps the
    ///   outcomes of a run that the serial run never makes.
    /// - witness: `environment::tests::a_drop_after_a_release_leaves_the_serial_run_3476`
    #[inline]
    pub fn discard(
        &mut self,
        ran: Ran,
    )
    {
        if let Maybe::Present(Scope {
            mut view,
            arena,
            session: _,
        }) = ran.scope
        {
            self.arena.dropped(&arena);
            let _outside = view.close();
            self.entries.restore(view);
        }
    }

    /// Open a check's scope below `rank` for the declaration placed at `end`:
    /// a view whose support `roots` start, a clone of the frozen arena and a
    /// fork of the session, which names the view's constants first.
    ///
    /// # Specification
    /// trivial.
    fn open_scope(
        &mut self,
        (roots, rank): (&[ConstantIndex], SourceRank),
        end: gandr_kernel_term::ArenaLength,
    ) -> Scope
    {
        let mut view = self.entries.view();
        view.open(roots.iter().copied(), (rank, end));
        // A freeze moves the nodes minted since the last one into a segment,
        // so the clone shares every node and copies none.
        self.arena.freeze();
        let arena = self.arena.clone();
        let Self {
            arena: ref frozen,
            ref mut names,
            ..
        } = *self;
        let session = names.session_mut();
        // The session names the view's constants before the fork, so the
        // job shares the names by reference and names none.
        session.name_constants(&view);
        // The checks of a readmission overlap without a break, so no join
        // settles the layers that they hold. A compaction keeps the layers to
        // the open checks and a logarithm of the session (#7335).
        session.compact(frozen);
        let session = session.fork(frozen);
        Scope {
            view,
            arena,
            session,
        }
    }

    /// Close a check's scope: fold its session back into the environment's,
    /// forget the clone's nodes and take back the view's support. Refuse the
    /// environment when the fold meets two outcomes under one key, and refuse
    /// `checked` when the check read outside its support.
    ///
    /// # Specification
    /// trivial.
    fn close_scope<T>(
        &mut self,
        scope: Scope,
        checked: Result<T, KernelError>,
    ) -> Result<T, KernelError>
    {
        let Scope {
            mut view,
            arena,
            session,
        } = scope;
        let glued = {
            let Self {
                arena: ref frozen,
                ref mut names,
                ..
            } = *self;
            names.session_mut().join(frozen, session)
        };
        // A reader that names nodes by their positions forgets the clone's.
        self.arena.dropped(&arena);
        let outside = view.close();
        self.entries.restore(view);
        // Two outcomes under one key refuse the environment, whatever the
        // check decided.
        glued?;
        supported(checked, outside)
    }

    /// Run `check` against a view of this environment: a clone of the frozen
    /// arena that it mints its intermediates into, a judgement over the
    /// entries below `rank` through the support that `roots` start, and a
    /// job's session, forked from the environment's at this release, that it
    /// names records in. The check reads and writes no other part of the
    /// environment, its intermediates leave with the clone, and the job's
    /// session folds back into the environment's.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the answer of `check`, unless the check read a position
    ///   outside its support: then [`KernelError::OutsideSupport`] at the first
    ///   such position. The entries keep no horizon after the call, and the
    ///   arena holds the nodes it held before, all of them frozen.
    /// - panics: none.
    ///
    /// # Errors
    /// The error of `check`, [`KernelError::OutsideSupport`], or
    /// [`KernelError::KeptOutcomesDisagree`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a read outside the support refuses the declaration,
    ///   and an entry ranked above the declaration is unbound to its check.
    /// - witness: `environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
    /// - witness: `environment::tests::a_reference_to_an_entry_ranked_above_the_declaration_is_unbound_6621`
    #[spec(ensures: self.entries.check_horizon().is_none())]
    fn within_view<T>(
        &mut self,
        (roots, rank): (&[ConstantIndex], SourceRank),
        (levels, taken): (&LevelContext, &crate::admitted::Tally),
        check: impl FnOnce(
            &mut TermArena,
            check::Judgement<'_>,
            &mut crate::support::SupportContext,
        ) -> Result<T, KernelError>,
    ) -> Result<T, KernelError>
    {
        let end = self.entries.len();
        let mut scope = self.open_scope((roots, rank), end);
        let checked = {
            let Scope {
                ref view,
                ref mut arena,
                ref mut session,
            } = scope;
            check(
                arena,
                check::Judgement::new(view, levels)
                    .unsealing(&self.manifest)
                    .taking(crate::admitted::Taking::under(self.admitting, taken))
                    .forking(self.forking.forking()),
                session,
            )
        };
        self.close_scope(scope, checked)
    }

    /// Commit what the check of a lone declaration found at its reserved
    /// position: keep its content and fill its slot, or leave a vacancy on a
    /// refusal. The cursor then folds each slot whose commit came.
    ///
    /// # Specification
    /// - requires: `lone` is the declaration released at `lone.place.0`, and
    ///   the arena holds its content below `lone.marks.0`.
    /// - ensures: on an outcome that admits, one entry at `lone.place.0` and
    ///   the admission floor at least at `lone.marks.0`; on a refusal, a
    ///   vacancy at `lone.place.0`, and the arena truncated to `lone.marks.1`
    ///   when no content sits above the declaration's. Otherwise its content
    ///   stays as an orphan below the later content. The length is unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// The refusal that `lone.outcome` carries, or
    /// [`KernelError::UnboundConstant`] when no reservation stands at
    /// `lone.place.0`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::add_decl`], and a refusal under a later
    ///   staging keeps that staging's content.
    /// - witness: `environment::tests::a_rejected_declaration_leaves_a_vacancy_at_its_position`
    /// - witness: `tests::verdicts::a_rejected_declaration_leaves_the_keys_as_if_never_offered_6566`
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(captures: [entry_len = self.entries.len(), admitted = self.entries.admitted(), place = lone.place.0], ensures: |ret| self.entries.len() == entry_len && match ret.as_ref() {
        Ok(id) => id.position() == place,
        Err(_) => self.entries.admitted() == admitted,
    })]
    fn commit(
        &mut self,
        lone: Lone,
    ) -> Result<CheckedId, KernelError>
    {
        let Lone {
            declaration,
            place: (position, rank),
            content: (content, generative),
            keys: (entry_content, entry_key),
            references: named,
            census,
            took,
            outcome,
            admission,
            marks: (content_end, rejected),
            key_name,
        } = lone;
        let cursor =
            usize::from(self.entries.len()).saturating_sub(usize::from(self.releases.unfolded()));
        let Some(offset) = usize::from(position)
            .checked_sub(cursor)
            .map(gandr_kernel_term::ArenaLength::from)
        else {
            return Err(KernelError::UnboundConstant { index: position });
        };
        match outcome {
            Ok(accessibility) => {
                // A receipt attests only what the kernel checked itself.
                let record = (admission, took)
                    .eq(&(Admission::Checked, crate::admitted::AdmittedCount::NONE))
                    .then(|| accessibility.clone());
                if let Maybe::Absent(_) = self
                    .releases
                    .commit(offset, crate::releases::Unfolded::Admitted(record))
                {
                    return Err(KernelError::UnboundConstant { index: position });
                }
                self.admitted = self.admitted.and(took);
                // The arena holds this declaration's content, and the check's
                // intermediates left with its clone. A later commit may have
                // raised the floor past it already.
                self.admission_floor =
                    content_end.clamped_into(self.admission_floor, self.arena.watermark());
                let rested_on = self.transitive_rest(
                    declaration.content(),
                    declaration.laws(),
                    position,
                    admission,
                );
                self.entries.fill(
                    &self.arena,
                    position,
                    AdmittedDeclaration::live(AdmittedParts {
                        declaration,
                        admission,
                        rested_on,
                        references: named,
                        block: check::occurrence::Block::lone(position),
                        accessibility,
                        key_name,
                        census,
                        key: entry_key,
                        content: entry_content,
                        rank,
                        unit: Unit::lone(position),
                    }),
                );
                alloc::sync::Arc::make_mut(&mut self.commits).hold((position, rank));
                if let (true, Maybe::Present(content)) = (generative, content) {
                    alloc::sync::Arc::make_mut(&mut self.commits).generative(content, position);
                }
                self.advance_seals(position);
                self.fold();
                Ok(CheckedId::new(position))
            },
            Err(error) => {
                if let Maybe::Absent(_) = self
                    .releases
                    .commit(offset, crate::releases::Unfolded::Vacated)
                {
                    return Err(KernelError::UnboundConstant { index: position });
                }
                // Drop this declaration's content, down to the admission floor
                // and no further, when no later staging sits above it. Its
                // position stays as a vacancy either way.
                if self.arena.watermark() == content_end {
                    self.arena
                        .truncate_to(rejected.clamped_into(self.admission_floor, content_end));
                }
                self.entries.vacate_at(position);
                // The release named the position by its content; a vacancy is
                // unadmitted, and content staged from this one on read it.
                self.names.session_mut().table_mut().name_ahead(
                    position,
                    [crate::encoding::ConstantName::Unadmitted],
                    Some(rejected),
                );
                self.fold();
                Err(error)
            },
        }
    }

    /// Fold each slot at the cursor whose commit came, in position order: the
    /// rank that a release predicted, the rows of the dependents, the order
    /// and the record of the verdict. A refused slot folds its vacancy.
    ///
    /// # Specification
    /// - requires: each committed slot from the cursor on holds its commit.
    /// - ensures: the cursor stands at the first reserved slot, or at the
    ///   length; the folded state is the state of the serial run over the slots
    ///   below the cursor.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the folded state is the serial run's, which no
    ///   predicate over one call reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold out of position order moves the order flag,
    ///   the reach or the record of a verdict off the serial run's.
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    /// - witness: `environment::tests::a_refusal_before_a_predicted_rank_moves_it_at_the_fold_3476`
    /// - witness: `environment::tests::a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281`
    fn fold(&mut self)
    {
        loop {
            let position = ConstantIndex::from(
                usize::from(self.entries.len())
                    .saturating_sub(usize::from(self.releases.unfolded())),
            );
            let Maybe::Present((ranked, unfolded)) = self.releases.next()
            else {
                return;
            };
            match unfolded {
                crate::releases::Unfolded::Admitted(record) => {
                    if ranked == crate::releases::Ranked::Predicted {
                        self.settle_rank(position);
                    }
                    let Self {
                        ref entries,
                        ref mut commits,
                        ref mut verdicts,
                        ..
                    } = *self;
                    if let Some(entry) = entries.live(position) {
                        alloc::sync::Arc::make_mut(commits)
                            .fold((position, entry.rank()), entry.references());
                        if let Some(accessibility) = record {
                            verdicts.checked(entry.key(), accessibility);
                        }
                    }
                },
                crate::releases::Unfolded::Vacated => {
                    alloc::sync::Arc::make_mut(&mut self.commits).vacate(position);
                },
                crate::releases::Unfolded::Reserved(_) => return,
            }
        }
    }

    /// Set the predicted rank of the entry at `position` right, at the
    /// cursor. The serial run ranks a declaration staged with no rank past
    /// every live entry below it. A refusal of an earlier release, which the
    /// prediction took to admit, moves that rank down, and the entry takes
    /// it.
    ///
    /// A check reads a rank only as an order among the live entries: the
    /// horizon below it, the holder of a role, the types of words and the
    /// twins of a definition below it, and the rank order of the operations
    /// that it names. No live entry ranks between the two ranks, so the
    /// check read what the serial check reads. Its key, its name and its
    /// outcome stand, and no job runs again. The entry, its rows and the rank
    /// index take the rank, and the order folds after it.
    ///
    /// # Specification
    /// - requires: each slot below `position` is folded, and the release of the
    ///   entry at `position` predicted its rank.
    /// - ensures: the entry at `position` holds the rank past every rank that a
    ///   live entry below it holds, and the count of rollbacks is one more when
    ///   the rank moved.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the serial rank reads the folded entries below
    ///   `position`, which a predicate over one call would restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal settled after a later release that
    ///   predicted its admission leaves the later entry one rank too high, and
    ///   its rank and the order differ from the serial run's.
    /// - witness: `environment::tests::a_refusal_before_a_predicted_rank_moves_it_at_the_fold_3476`
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    fn settle_rank(
        &mut self,
        position: ConstantIndex,
    )
    {
        let Some(predicted) = self.entries.rank_of(position)
        else {
            return;
        };
        let serial = self.commits.past_below(position);
        if serial == predicted {
            return;
        }
        alloc::sync::Arc::make_mut(&mut self.commits).reheld((position, predicted), serial);
        self.entries.rerank(&BTreeMap::from([(position, serial)]));
        self.rollbacks = self.rollbacks.and_one();
    }

    /// A receipt `signer` gives over the verdicts this environment checked
    /// itself under a key, and those verdicts: never one it recalled, so a
    /// receipt attests only its own signer's checks.
    ///
    /// # Specification
    /// - ensures: absent as
    ///   [`stored::Absent::Unrecorded`](crate::verdict::stored::Absent::Unrecorded)
    ///   when no keyed admission was checked here; otherwise the records of
    ///   exactly those admissions and `signer`'s signature over them.
    /// - provides: the one way a receipt is made, so a signature never covers a
    ///   record the kernel did not produce.
    /// - panics: none.
    /// - executable: none — which admissions this environment checked rather
    ///   than recalled is private to its verdicts, so no predicate reads it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a receipt an environment gave recalls its
    ///   declarations in a fresh environment over the same input.
    /// - witness: `tests::verdicts::a_verdict_is_recalled_only_under_its_own_key`
    #[inline]
    pub fn receipt(
        &self,
        signer: &crate::verdict::KernelSigner,
    ) -> Maybe<crate::verdict::StoredReceipt, crate::verdict::stored::Absent>
    {
        self.verdicts.receipt(signer)
    }

    /// Read recorded verdicts from `source` from now on: a run that resumes
    /// this environment reads the source of its own readmission, which holds
    /// what the runs after this environment's recorded.
    ///
    /// # Specification
    /// - ensures: each later admission reads `source` by its key; the policy
    ///   and the receipts verified so far are unchanged.
    /// - panics: none.
    /// - executable: none — the source is private to the verdicts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a resumed run reads the source of its readmission, so
    ///   it recalls what a run after the record recorded.
    /// - witness: `tests::verdicts::a_resumed_environment_recalls_from_the_source_it_reads_6566`
    #[inline]
    pub fn reading(
        &mut self,
        source: alloc::sync::Arc<dyn crate::verdict::VerdictSource>,
    )
    {
        self.verdicts.reading(source);
    }

    /// How many admissions a recorded verdict answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn recalls(&self) -> crate::verdict::RecallCount
    {
        self.verdicts.recalls()
    }

    /// How many admissions this environment checked itself and recorded, each
    /// once whether its receipt keeps it under one key or two.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn recorded(&self) -> crate::verdict::RecordCount
    {
        self.verdicts.recorded()
    }

    /// How many admitted results this environment's checks took.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admitted(&self) -> crate::admitted::AdmittedCount
    {
        self.admitted
    }

    /// Admit a declaration through the **single warned bypass**, unchecked.
    ///
    /// # Soundness warning
    ///
    /// This is the one escape hatch, so no second bypass is ever improvised. It
    /// performs no type checking and no level admission: the declaration is
    /// trusted verbatim, and a wrong one admitted here can make the kernel
    /// prove anything. Every admission through it is tracked, and surfaces
    /// in the [`Self::audit`] of everything that transitively rests on it.
    ///
    /// # Specification
    /// - requires: `staged` was built into this environment's arena; the caller
    ///   vouches for it, and nothing is verified.
    /// - ensures: the declaration is appended, marked [`Admission::Unchecked`],
    ///   and included in the audit of every dependent, and its staged mark is
    ///   resolved. It takes its staged rank, or its position when staged with
    ///   none; when a live entry holds that rank, it takes the rank past every
    ///   live one. The arena is unchanged, since the bypass mints no
    ///   intermediate and truncates nothing, and the admission floor rises to
    ///   its watermark so a later rejection cannot truncate through what the
    ///   bypass committed. The outstanding-content guard is therefore not owed
    ///   here: the bypass destroys nothing, so there is nothing to preserve.
    /// - provides: the tracked, warned bypass.
    /// - fails: [`KernelError::UnsettledReleases`] while a released check is
    ///   not settled, since the bypass takes the rank past every rank, which
    ///   each outstanding commit moves. Otherwise never: the bypass does not
    ///   check.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::UnsettledReleases`] while a released check is not
    /// settled.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the bypass's whole observable effect is that the
    ///   declaration is present and that dependents' audits name it, pinned by
    ///   a dependent's report; the L3 residue is the floor rise, pinned by a
    ///   later rejection leaving bypassed content resolvable.
    /// - witness: `environment::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `environment::tests::a_rejection_keeps_bypassed_content_resolvable`
    #[inline]
    #[spec(captures: [entry_len = self.entries.len(), entry_watermark = self.arena.watermark()], ensures: |ret| ret.is_err() || (arith::Int::from(usize::from(self.entries.len())) == arith::add(arith::Int::from(usize::from(entry_len)), arith::Int::from(1_usize))
        && self
            .entries
            .live(ConstantIndex::from(entry_len))
            .is_some_and(|entry| entry.admission() == Admission::Unchecked)
        && self.arena.watermark() == entry_watermark
        && self.admission_floor == self.arena.watermark()))]
    pub fn add_decl_unchecked(
        &mut self,
        staged: StagedDeclaration,
    ) -> Result<CheckedId, KernelError>
    {
        self.settled()?;
        let (content_start, rank, declaration) = staged.into_parts();
        self.outstanding.resolve(content_start);
        let position = ConstantIndex::from(usize::from(self.entries.len()));
        // The bypass refuses nothing, so a held rank gives way to the rank past
        // every live one: two entries never share a rank. A declaration staged
        // with no rank takes the next rank, when a readmission sets one.
        let rank = rank.unwrap_or_else(|| {
            CommitLog::unranked(
                &mut self.commits,
                position .. ConstantIndex::from(usize::from(position).saturating_add(1)),
            )
        });
        let rank = match self.commits.ranked(rank) {
            None => rank,
            Some(_) => self.commits.past_ranks(),
        };
        // The bypass commits whatever content the arena holds, so the floor
        // rises to the current watermark. Without this a later rejection could
        // truncate through bypassed content.
        self.admission_floor = self.arena.watermark();
        let rested_on = self.transitive_rest(
            declaration.content(),
            declaration.laws(),
            position,
            Admission::Unchecked,
        );
        let named = references(&self.arena, &declaration);
        self.enter(AdmittedDeclaration::live(AdmittedParts {
            declaration,
            admission: Admission::Unchecked,
            rested_on,
            references: named,
            block: check::occurrence::Block::lone(position),
            accessibility: check::Accessibility::unwalked(),
            key_name: ConstantName::Position,
            census: ExpansionCensus::new(),
            key: Maybe::Absent(crate::verdict::keyed::Absent::Bypassed),
            content: Maybe::Absent(crate::verdict::keyed::Absent::Bypassed),
            rank,
            unit: Unit::lone(position),
        }));
        self.advance_seals(position);
        Ok(CheckedId::new(position))
    }

    /// Refuse a call that reads the order of every commit while a released
    /// check is not settled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when no release is outstanding.
    /// - fails: [`KernelError::UnsettledReleases`] with the count of the
    ///   outstanding releases.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block offered while a release is outstanding is
    ///   refused, and the same block after the settle is admitted.
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(self.releases.outstanding()) == 0))]
    fn settled(&self) -> Result<(), KernelError>
    {
        let unsettled = self.releases.outstanding();
        if usize::from(unsettled) == 0 {
            return Ok(());
        }
        Err(KernelError::UnsettledReleases { unsettled })
    }

    /// Refuse a keep in place of the unit whose first member stands at
    /// `first`, at `ranks`, while an outstanding release reads into its key
    /// or its name: a manifest atom, a release that each later check reads, a
    /// reservation at or above the lowest rank or a predicted rank, a
    /// generative release of the unit's content below it, or a plain
    /// definition below a lone one that its name counts.
    ///
    /// # Specification
    /// - requires: `ranks` names each member of the unit, ascending.
    /// - ensures: `Ok` exactly when no release is outstanding, or none reads
    ///   into the key or the name that the unit's check in place computes.
    /// - fails: [`KernelError::UnsettledReleases`] otherwise.
    /// - panics: none.
    /// - executable: none — the reads are those of [`Self::check_in_place`],
    ///   which no predicate over one call restates.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a keep beside a release that reads into its key reads
    ///   a key or a name that the serial run, which commits the release first,
    ///   does not read.
    /// - witness: `environment::tests::a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281`
    fn keeps_beside(
        &mut self,
        (first, ranks): (ConstantIndex, &[SourceRank]),
    ) -> Result<(), KernelError>
    {
        let unsettled = self.releases.outstanding();
        if usize::from(unsettled) == 0 {
            return Ok(());
        }
        let held = KernelError::UnsettledReleases { unsettled };
        let below = ranks.first().copied().unwrap_or(SourceRank::ABOVE);
        if !self.manifest.is_empty()
            || matches!(
                self.releases.ordering(crate::releases::Sway::Free),
                Maybe::Present(_)
            )
            || matches!(self.releases.reaches(below), Maybe::Present(_))
        {
            return Err(held);
        }
        let Some(entry) = self.entries.live(first)
        else {
            return Ok(());
        };
        // The unit key counts the generative entries of its own content
        // below it; its content is computed only while such a release waits.
        if let Maybe::Present(_) = self.releases.generative_below(below)
            && let Maybe::Present(UnitKey {
                generative: Some(content),
                ..
            }) = self.unit_key(entry, (first, ranks))
            && let Maybe::Present(_) = self.releases.generative(content, below)
        {
            return Err(held);
        }
        let name = match entry.unit().shape {
            UnitShape::Lone => entry.key_name(),
            UnitShape::Block => ConstantName::Position,
        };
        if let ConstantName::Definition { digest, .. } = name
            && crate::encoding::likeness(
                self.names.session_mut().table_mut(),
                &self.arena,
                name,
                self.releases.definitions(digest, below),
            ) == crate::encoding::Likeness::Alike
        {
            return Err(held);
        }
        Ok(())
    }

    /// Admit a mutual block through the checked choke point: its families, a
    /// run of data declarations, then its definitions, in order, as one
    /// admission.
    ///
    /// The block is admitted on the one schedule both checkers keep: each
    /// definition's declared type forms with the families in scope; each
    /// family's fields form with the block's families at their signatures and
    /// its definitions at their declared types; then each definition's body is
    /// checked with every family admitted, as a lone definition's is. Each step
    /// is the judgement a lone declaration takes — no node or rule is new — so
    /// the block is what lets a family name a definition that cases on it.
    ///
    /// # Specification
    /// - requires: `staged` was built into this environment's arena through
    ///   [`Self::stage`], in admission order; nothing is taken on credit.
    /// - ensures: `Ok(ids)` with one [`CheckedId`] per member, at consecutive
    ///   positions from the current length, exactly when every definition's
    ///   declared type forms with the families in scope, every family passes
    ///   the occurrence walk over the block and forms, and every definition's
    ///   body checks; each member's audit is the union of the block's. On a
    ///   failure of a member's check, a vacancy at each member's position, and
    ///   the arena and the manifest as they were before the call. On a refusal
    ///   before any position is taken, the entries as they were too.
    /// - provides: the one checked entry for declarations that name each other,
    ///   by the same choke point [`Self::add_decl`] is.
    /// - fails: [`KernelError::OutstandingStagedContent`] when a declaration
    ///   staged after the block is unresolved;
    ///   [`KernelError::UnsettledReleases`] while a released check is not
    ///   settled; otherwise any [`KernelError`] a member's admission surfaces.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::OutstandingStagedContent`],
    /// [`KernelError::UnsettledReleases`], or any [`KernelError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe and its decoder are admitted together; a
    ///   decoder that names itself at a place that does not descend, and a
    ///   field naming its family under a function domain, are each refused with
    ///   a vacancy at each member's position.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
    /// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole`
    #[spec(captures: [entry_len = self.entries.len(), entry_watermark = self.arena.watermark(), members = staged.len()],
        ensures: |ret| match ret.as_ref() {
            Ok(ids) => ids.len() == members
                && usize::from(self.entries.len()).checked_sub(usize::from(entry_len)) == Some(members)
                && self.admission_floor == self.arena.watermark(),
            Err(_) => (usize::from(self.entries.len()) == usize::from(entry_len)
                    || usize::from(self.entries.len()) == usize::from(entry_len).saturating_add(members))
                && self.arena.watermark().clamped_into(gandr_kernel_term::ArenaWatermark::default(), entry_watermark) == self.arena.watermark(),
        })]
    #[inline]
    pub fn add_block(
        &mut self,
        staged: Vec<StagedDeclaration>,
    ) -> Result<Vec<CheckedId>, KernelError>
    {
        self.settled()?;
        let Some(content_start) = staged.iter().map(StagedDeclaration::content_start).min()
        else {
            return Ok(Vec::new());
        };
        // The guard of `add_decl`, over the whole block: every member's claim
        // resolves, and a claim left above the block's start is a producer
        // the rollback would truncate through.
        for member in &staged {
            self.outstanding.resolve(member.content_start());
        }
        let above = self.outstanding.above(content_start);
        if usize::from(above) != 0 {
            for member in &staged {
                self.outstanding.register(member.content_start());
            }
            return Err(KernelError::OutstandingStagedContent { above });
        }
        let base = self.entries.len();
        let content_end = self.arena.watermark();
        let rejected = content_start.clamped_into(self.admission_floor, content_end);
        // A member staged with no rank ranks past every live entry, or from
        // the next rank a readmission set on, after the members before it.
        let past = CommitLog::unranked(
            &mut self.commits,
            ConstantIndex::from(usize::from(base))
                .. ConstantIndex::from(usize::from(base).saturating_add(staged.len())),
        );
        let mut ranks = Vec::with_capacity(staged.len());
        for (offset, member) in staged.iter().enumerate() {
            let position = ConstantIndex::from(usize::from(base).saturating_add(offset));
            let rank = member
                .rank()
                .unwrap_or_else(|| SourceRank::from(usize::from(past).saturating_add(offset)));
            // A member ranks above the member before it, at a rank no live
            // entry holds.
            let taken = match ranks.last() {
                Some(&earlier) if earlier >= rank => {
                    Some(ConstantIndex::from(usize::from(position).saturating_sub(1)))
                },
                Some(_) | None => self.commits.ranked(rank),
            };
            if let Some(by) = taken {
                self.arena.truncate_to(rejected);
                return Err(KernelError::RankTaken { rank, by });
            }
            ranks.push(rank);
        }
        let members = staged
            .into_iter()
            .map(StagedDeclaration::into_declaration)
            .collect::<Vec<_>>();
        let manifest = self.manifest.clone();
        match self.admit_block(&members, &ranks, rejected) {
            Ok(ids) => {
                self.admission_floor = content_end;
                Ok(ids)
            },
            Err(error) => {
                // The members admitted before the refusal leave the
                // environment, and each member's position stays as a vacancy.
                // No later admission takes those positions, so the kept
                // outcomes that read a member stay unread.
                alloc::sync::Arc::make_mut(&mut self.commits).truncate(&self.entries, base);
                self.entries.truncate(base);
                for _member in &members {
                    self.vacate();
                }
                // The block named its members by their content; a vacancy is
                // unadmitted, and the content staged from the block on read it.
                self.names.session_mut().table_mut().name_ahead(
                    ConstantIndex::from(usize::from(base)),
                    members.iter().map(|_member| ConstantName::Unadmitted),
                    Some(rejected),
                );
                if self.manifest != manifest {
                    alloc::sync::Arc::make_mut(&mut self.commits).stale_all();
                }
                self.manifest = manifest;
                self.atoms.retain(|&atom| atom < ConstantIndex::from(base));
                self.arena.truncate_to(rejected);
                Err(error)
            },
        }
    }

    /// The schedule of [`Self::add_block`], appending each member as it
    /// checks; the caller rolls back on failure.
    ///
    /// # Specification
    /// - requires: `members` were staged into this arena at its watermark, in
    ///   admission order, from `staged` on, and `ranks` holds one free rank per
    ///   member, ascending.
    /// - ensures: on success one entry per member is appended, each audited
    ///   with the union of the block's audits; on failure some prefix of them
    ///   may be, for the caller to truncate.
    /// - provides: the schedule, apart from the rollback.
    /// - fails: any [`KernelError`] a member's admission surfaces.
    /// - panics: none.
    ///
    /// # Errors
    /// Any [`KernelError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::add_block`].
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
    #[spec(captures: entry_len = self.entries.len(), ensures: |ret| ret.as_ref().map_or(true,
        |ids| usize::from(self.entries.len()).checked_sub(usize::from(entry_len)) == Some(ids.len())))]
    fn admit_block(
        &mut self,
        members: &[Declaration],
        ranks: &[SourceRank],
        staged: gandr_kernel_term::ArenaWatermark,
    ) -> Result<Vec<CheckedId>, KernelError>
    {
        let base = usize::from(self.entries.len());
        let first = ConstantIndex::from(base);
        let first_rank = ranks
            .first()
            .copied()
            .unwrap_or_else(|| SourceRank::from(first));
        // The block is keyed whole, before its first member enters, and each
        // member by its place in it.
        let content = self.content_key(members, (first, ranks));
        let generative = members.iter().any(|member| {
            !matches!(
                *member.content(),
                DeclarationContent::Def { .. } | DeclarationContent::LiteralIdentity { .. }
            )
        });
        let block_content = match content {
            Maybe::Present(content) if generative => {
                Maybe::Present(content.generative(self.commits.generative_count(
                    &self.entries,
                    content,
                    first_rank,
                )))
            },
            Maybe::Present(_) | Maybe::Absent(_) => content,
        };
        let families = members
            .iter()
            .take_while(|member| matches!(*member.content(), DeclarationContent::Data { .. }))
            .count();
        let past_families = ConstantIndex::from(base.saturating_add(families));
        let end = ConstantIndex::from(base.saturating_add(members.len()));
        // Each member's check reads through the references of the whole block.
        let named = block_references(&self.arena, members, first);
        let content_of = |offset: usize| match block_content {
            Maybe::Present(block_content) => {
                Maybe::Present(block_content.member(crate::verdict::KeyedCount::from(offset)))
            },
            Maybe::Absent(absent) => Maybe::Absent(absent),
        };
        // The session names each member as its admission will, before the
        // first check: the members read one another, and their staged content
        // read them past the table's end, so its placements go.
        {
            let session = self.names.session_mut();
            session.name_constants(&self.entries);
            session.table_mut().name_ahead(
                first,
                (0 .. members.len()).map(|offset| {
                    ConstantName::table_name(ConstantName::Position, content_of(offset))
                }),
                Some(staged),
            );
        }
        let mut admitted = Vec::with_capacity(members.len());
        // A block records no verdict, so what its checks take is only counted.
        let taken = crate::admitted::Tally::new();
        // Each member's tally: its declared type's formation here, then its
        // own check.
        let mut censuses = alloc::vec![ExpansionCensus::new(); members.len()];
        // The definitions' declared types form with the families in scope and
        // no definition: a declared type names the block's families, never
        // its definitions.
        for (member, census) in members.iter().zip(censuses.iter_mut()).skip(families) {
            let levels = LevelContext::admit(
                member.levels().params(),
                member.levels().constraints().to_vec(),
            )?;
            self.within_view(
                (&named, first_rank),
                (&levels, &taken),
                |arena, judgement, session| {
                    check::form_declared(
                        arena,
                        judgement.within_mutual(
                            check::occurrence::Block::new(first, past_families, past_families),
                            members,
                        ),
                        member.declared_id(),
                        session,
                        census,
                    )
                },
            )?;
        }
        for (((offset, member), census), &rank) in members
            .iter()
            .enumerate()
            .zip(censuses.iter_mut())
            .zip(ranks)
        {
            let position = ConstantIndex::from(base.saturating_add(offset));
            let levels = LevelContext::admit(
                member.levels().params(),
                member.levels().constraints().to_vec(),
            )?;
            // A family forms with the block in scope; a definition is checked
            // as a lone one is, every family and definition before it
            // admitted, inside the block only so its own fixpoint reads its
            // constant as the self binder.
            let accessibility = self.within_view(
                (&named, rank),
                (&levels, &taken),
                |arena, judgement, session| {
                    let judgement = judgement.within_mutual(
                        check::occurrence::Block::new(
                            first,
                            past_families,
                            if offset < families { end } else { position },
                        ),
                        members,
                    );
                    check::check_declaration(arena, judgement, member, session, census)
                },
            )?;
            let rested_on = self.transitive_rest(
                member.content(),
                member.laws(),
                position,
                Admission::Checked,
            );
            let member_content = content_of(offset);
            let member_key = self.entry_key(member_content);
            // The block's families share one stage; a definition stands alone.
            self.enter(AdmittedDeclaration::live(AdmittedParts {
                declaration: member.clone(),
                admission: Admission::Checked,
                rested_on,
                references: named.clone(),
                block: if offset < families {
                    check::occurrence::Block::new(first, past_families, end)
                }
                else {
                    check::occurrence::Block::lone(position)
                },
                accessibility,
                // A block's members name one another, and a definition its own
                // constant, so a key names each by its position.
                key_name: ConstantName::Position,
                census: *census,
                key: member_key,
                content: member_content,
                rank,
                unit: Unit {
                    first,
                    end,
                    shape: UnitShape::Block,
                },
            }));
            self.advance_seals(position);
            admitted.push(CheckedId::new(position));
        }
        // The members name each other, so each rests on what any rests on.
        let mut rested = BTreeSet::new();
        for entry in (base .. usize::from(self.entries.len()))
            .filter_map(|position| self.entries.live(ConstantIndex::from(position)))
        {
            rested.extend(entry.rested_on().iter().copied());
        }
        for offset in base .. usize::from(self.entries.len()) {
            if let Some(entry) = self.entries.get_mut(offset) {
                entry.rest_on(&rested);
            }
        }
        self.admitted = self.admitted.and(taken.get());
        if let (true, Maybe::Present(content)) = (generative, content) {
            alloc::sync::Arc::make_mut(&mut self.commits).generative(content, first);
        }
        Ok(admitted)
    }

    /// Retire the entries at `positions`, each with every member of the unit
    /// that admitted it.
    ///
    /// A readmission retires the reach of an edit, and each entry whose keep
    /// in place ([`Self::keep_in_place`]) is refused. A retired entry keeps
    /// its position as a name, so no other entry moves, and its slot frees its
    /// declaration. No read sees it, and its rank is free. When the entries
    /// retired since the last sweep reach half the live ones, the reverse
    /// index and the generative index drop the rows of the retired entries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, each entry at `positions` is retired, with each
    ///   member of its unit, and every other entry is as it was. On refusal,
    ///   the environment is unchanged. Either way the entries keep their
    ///   number, and the arena mints nothing.
    /// - provides: the retire of a readmission that keeps each entry outside
    ///   the reach of an edit live, beside the checks it released.
    /// - fails: [`KernelError::UnboundConstant`] at a position that holds no
    ///   entry, [`KernelError::Retired`] at an entry retired already, and
    ///   [`KernelError::UnsettledReleases`] while an outstanding release
    ///   reaches the rank of an entry that the call retires.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a readmission that retires the reach of an edit reads
    ///   as a fresh admission, and the reach of a later edit reads each live
    ///   support; a retired entry holds no declaration and does not retire
    ///   again.
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    /// - witness: `environment::tests::a_retired_entry_keeps_its_position_and_frees_its_declaration_7194`
    /// - witness: `environment::tests::an_admission_after_a_retirement_recalls_by_its_entry_key_alone_6846`
    /// - witness: `environment::tests::a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281`
    #[spec(captures: [length = self.entries.len(), watermark = self.arena.watermark()],
        ensures: |ret| self.entries.len() == length && self.arena.watermark() == watermark
            && (ret.is_err() || positions.iter().all(|&position| self.entries.live(position).is_none())))]
    #[inline]
    pub fn retire(
        &mut self,
        positions: &[ConstantIndex],
    ) -> Result<(), KernelError>
    {
        for &position in positions {
            match self.entries.family().get(usize::from(position)) {
                Some(&Slot::Admitted(_)) => {},
                Some(&Slot::Retired) => return Err(KernelError::Retired { position }),
                Some(&(Slot::Vacant | Slot::Reserved)) | None => {
                    return Err(KernelError::UnboundConstant { index: position });
                },
            }
        }
        if positions.is_empty() {
            return Ok(());
        }
        // An outstanding release ranked at or above a retired entry may read
        // it, and the serial run retires the entry after that release's
        // commit.
        let unsettled = self.releases.outstanding();
        if usize::from(unsettled) != 0
            && positions
                .iter()
                .filter_map(|&position| self.entries.live(position).map(AdmittedDeclaration::unit))
                .flat_map(|unit| usize::from(unit.first) .. usize::from(unit.end))
                .filter_map(|member| self.entries.rank_of(ConstantIndex::from(member)))
                .any(|rank| matches!(self.releases.reaches(rank), Maybe::Present(_)))
        {
            return Err(KernelError::UnsettledReleases { unsettled });
        }
        for &position in positions {
            let Some(unit) = self.entries.live(position).map(AdmittedDeclaration::unit)
            else {
                continue;
            };
            for member in usize::from(unit.first) .. usize::from(unit.end) {
                let member = ConstantIndex::from(member);
                if let Some(rank) = self.entries.rank_of(member) {
                    alloc::sync::Arc::make_mut(&mut self.commits).retire((member, rank));
                    self.entries.retire(&self.arena, member);
                }
            }
        }
        alloc::sync::Arc::make_mut(&mut self.commits).sweep(&self.entries);
        Ok(())
    }

    /// Whether the check of `entry`, the first member of its unit at `first`,
    /// reads what it read at its admission with its members at `ranks`: each
    /// position the unit names stands live and ranked below it, and the
    /// unit's narrowed key, computed again in place over its stored content
    /// and the entries live now, is the key each member holds.
    ///
    /// # Specification
    /// - requires: `ranks` names each member of the unit, ascending.
    /// - ensures: `Ok` exactly when every reference outside the unit is live
    ///   below the first rank of `ranks` and each member's held key is the key
    ///   its check reads at `ranks` now.
    /// - fails: [`KernelError::UnboundConstant`] at a reference that is not
    ///   live or not ranked below the unit, and [`KernelError::Unkept`] when
    ///   the unit or its check now has no key or the key changed.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::keep_in_place`].
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    #[spec(requires: ranks.windows(2).all(|pair| matches!(*pair, [lower, higher] if lower < higher)),
        ensures: |ret| matches!(ret, Ok(()) | Err(KernelError::UnboundConstant { .. } | KernelError::Unkept { .. })))]
    fn holds_its_key(
        &self,
        entry: &AdmittedDeclaration,
        (first, ranks): (ConstantIndex, &[SourceRank]),
    ) -> Result<(), KernelError>
    {
        use crate::error::KeepRefusal;
        let unkept = |refusal| KernelError::Unkept {
            position: first,
            refusal,
        };
        let unit = entry.unit();
        let Some(&below) = ranks.first()
        else {
            return Err(unkept(KeepRefusal::Unit));
        };
        // Each position the unit names stands live and ranked below it, as a
        // fresh admission's check reads it. The members of a block share the
        // references of the whole block.
        for &reference in entry.references() {
            if unit.holds(reference) == Membership::Member {
                continue;
            }
            match self.entries.rank_of(reference) {
                Some(rank) if rank < below => {},
                Some(_) | None => return Err(KernelError::UnboundConstant { index: reference }),
            }
        }
        let Maybe::Present(key) = self.unit_key(entry, (first, ranks))
        else {
            return Err(unkept(KeepRefusal::Unkeyed));
        };
        for (offset, member) in (usize::from(unit.first) .. usize::from(unit.end)).enumerate() {
            match self
                .entries
                .live(ConstantIndex::from(member))
                .map(AdmittedDeclaration::content_key)
            {
                Some(Maybe::Present(held))
                    if held == key.member(crate::verdict::KeyedCount::from(offset)) => {},
                Some(Maybe::Present(_)) => return Err(unkept(KeepRefusal::KeyChanged)),
                Some(Maybe::Absent(_)) | None => return Err(unkept(KeepRefusal::Unkeyed)),
            }
        }
        Ok(())
    }

    /// The key of the unit whose first member `entry` stands at `first`, at
    /// the ranks `ranks`, as a fresh admission at those ranks computes it:
    /// its content key over its stored content and the entries live now,
    /// counted among the generative contents ranked below it when a member
    /// is generative.
    ///
    /// # Specification
    /// trivial.
    fn unit_key(
        &self,
        entry: &AdmittedDeclaration,
        (first, ranks): (ConstantIndex, &[SourceRank]),
    ) -> Maybe<UnitKey, crate::verdict::keyed::Absent>
    {
        let unit = entry.unit();
        let below = ranks.first().copied().unwrap_or(SourceRank::ABOVE);
        let content = match unit.shape {
            UnitShape::Lone => {
                self.content_key(core::slice::from_ref(entry.declaration()), (first, ranks))
            },
            UnitShape::Block => {
                let declarations: Vec<Declaration> = (usize::from(unit.first)
                    .. usize::from(unit.end))
                    .filter_map(|member| self.entries.live(ConstantIndex::from(member)))
                    .map(|member| member.declaration().clone())
                    .collect();
                self.content_key(&declarations, (first, ranks))
            },
        };
        let content = match content {
            Maybe::Present(content) => content,
            Maybe::Absent(absent) => return Maybe::Absent(absent),
        };
        let generative = (usize::from(unit.first) .. usize::from(unit.end))
            .filter_map(|member| self.entries.live(ConstantIndex::from(member)))
            .any(|member| {
                !matches!(
                    *member.content(),
                    DeclarationContent::Def { .. } | DeclarationContent::LiteralIdentity { .. }
                )
            });
        Maybe::Present(if generative {
            UnitKey {
                key: content.generative(self.commits.generative_count(
                    &self.entries,
                    content,
                    below,
                )),
                shape: unit.shape,
                generative: Some(content),
            }
        }
        else {
            UnitKey {
                key: content,
                shape: unit.shape,
                generative: None,
            }
        })
    }

    /// The content key of the constant at `constant`, computed on demand
    /// from its stored content as an admission under a policy that keys
    /// computes it, in an environment under any policy. `demanded` keeps each
    /// key computed on the way, so a later demand reads it.
    ///
    /// A key reads the keys of the positions that its unit names, of the
    /// atoms manifest at it, of the role holders it reads and of the types of
    /// words it reaches, and each of them stands below it. A generative
    /// unit's key counts the generative units ranked below it that hold its
    /// content. So a demand keys what the unit reads first and, of the units
    /// ranked below it, only those whose segments match its own.
    ///
    /// # Specification
    /// - requires: the environment's ranks ascend with its positions, as in a
    ///   readmission that walks whole or from a leading run, and `demanded`
    ///   holds only keys computed in this environment.
    /// - ensures: absent when `constant` is no live entry. Otherwise the
    ///   content key that an admission at its position and rank under a policy
    ///   that keys gives it, absent where that key is absent; then `demanded`
    ///   holds it and each key computed on the way.
    /// - provides: the names of a formation under a policy that rechecks, which
    ///   read the keys of the constants that the formation reads and no other.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the key is a digest, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a program of twin axioms, a reader of one of them,
    ///   twin sorts, words over a sort, an atom manifest at a unit and twin
    ///   blocks, admitted under a policy that keys and under one that rechecks:
    ///   each key on demand, from the last constant down, is the key of its
    ///   admission.
    /// - witness: `tests::verdicts::a_key_on_demand_is_the_key_of_its_admission_7456`
    #[inline]
    pub fn demanded_key(
        &self,
        constant: ConstantIndex,
        demanded: &mut DemandedKeys,
    ) -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>
    {
        let unkeyed = Maybe::Absent(crate::verdict::keyed::Absent::Unkeyed);
        let Some(entry) = self.entries.live(constant)
        else {
            return unkeyed;
        };
        self.demand(entry.unit().first, demanded);
        demanded.keys.get(&constant).copied().unwrap_or(unkeyed)
    }

    /// Whether another constant shares the content key of the constant at
    /// `constant`, when a table names it by that key and counts no twins: a
    /// constant of a unit with no generative member, which its admission named
    /// by its position, such as a definition under an open atom.
    ///
    /// # Specification
    /// - requires: as [`Self::demanded_key`].
    /// - ensures: [`Twin::Twinned`] when the unit of `constant` has no
    ///   generative member, its admission named `constant` by its position, and
    ///   another live unit of that kind holds the unit's content key, each key
    ///   as [`Self::demanded_key`] computes it. [`Twin::Alone`] otherwise.
    /// - provides: the test that the twins of a definition that reads
    ///   `constant` are the same under keys as under positions.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer reads digests, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two unit definitions under one open atom hold one
    ///   key, so the first is twinned; with the atom's scope over the first
    ///   alone, the second is a plain definition, and the first is alone.
    /// - witness: `tests::verdicts::two_definitions_under_one_atom_are_twins_on_demand_7456`
    #[must_use]
    #[inline]
    pub fn demanded_twin(
        &self,
        constant: ConstantIndex,
        demanded: &mut DemandedKeys,
    ) -> Twin
    {
        let Some(entry) = self.entries.live(constant)
        else {
            return Twin::Alone;
        };
        let unit = entry.unit();
        if self.twinning(unit) != Twinning::Shared {
            return Twin::Alone;
        }
        self.demand(unit.first, demanded);
        let Some(&Maybe::Present(raw)) = demanded.raw.get(&unit.first)
        else {
            return Twin::Alone;
        };
        let mut missing = Vec::new();
        loop {
            missing.clear();
            let twins = self.twins((unit, raw, SourceRank::ABOVE), demanded, &mut missing);
            if missing.is_empty() {
                return if twins == crate::verdict::KeyedCount::default() {
                    Twin::Alone
                }
                else {
                    Twin::Twinned
                };
            }
            // Each demand keeps a key for its unit, so the next search finds
            // each of these keyed.
            for &first in &missing {
                self.demand(first, demanded);
            }
        }
    }

    /// How a table that names by key counts the twins of `unit`.
    ///
    /// # Specification
    /// trivial.
    fn twinning(
        &self,
        unit: Unit,
    ) -> Twinning
    {
        let mut members = (usize::from(unit.first) .. usize::from(unit.end))
            .filter_map(|member| self.entries.live(ConstantIndex::from(member)));
        if members.clone().any(|member| {
            !matches!(
                *member.content(),
                DeclarationContent::Def { .. } | DeclarationContent::LiteralIdentity { .. }
            )
        }) {
            Twinning::Counted
        }
        else if members
            .next()
            .is_some_and(|member| member.key_name() == ConstantName::Position)
        {
            Twinning::Shared
        }
        else {
            Twinning::Named
        }
    }

    /// Key on demand the unit whose first member stands at `first`, and each
    /// unit that its key reads first.
    ///
    /// The units wait on a stack: a unit whose key reads one that `demanded`
    /// lacks waits under the units it reads. A unit tried and waiting stands
    /// under all that it and its readers pushed, so a read of it is circular.
    ///
    /// # Specification
    /// - requires: as [`Self::demanded_key`].
    /// - ensures: `demanded` holds a key, present or absent, for the unit at
    ///   `first`, for each of its members and for each unit keyed on the way,
    ///   each as [`Self::demanded_key`] states. A unit whose key reads, through
    ///   other keys, a unit that waits for it takes no key.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the keys are digests, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::demanded_key`], whose program holds an
    ///   axiom that reads a sort and the type of words over it, the type of
    ///   words reading the sort too.
    /// - witness: `tests::verdicts::a_key_on_demand_is_the_key_of_its_admission_7456`
    fn demand(
        &self,
        first: ConstantIndex,
        demanded: &mut DemandedKeys,
    )
    {
        let mut waiting = Vec::from([first]);
        let mut tried = BTreeSet::new();
        let mut missing = Vec::new();
        while let Some(&unit) = waiting.last() {
            if demanded.keys.contains_key(&unit) {
                let _keyed = waiting.pop();
                let _done = tried.remove(&unit);
                continue;
            }
            missing.clear();
            self.demand_unit(unit, demanded, &mut missing);
            if missing.is_empty() {
                let _keyed = waiting.pop();
                let _done = tried.remove(&unit);
                continue;
            }
            let _waits = tried.insert(unit);
            // What a key reads stands below it, so no unit reads one that
            // waits for it. One that did would wait forever, as would one whose
            // reads are all keyed, so either takes no key.
            let wanted = waiting.len();
            let mut circular = false;
            for &read in &missing {
                let read = self
                    .entries
                    .live(read)
                    .map_or(read, |entry| entry.unit().first);
                if demanded.keys.contains_key(&read) {
                    continue;
                }
                if tried.contains(&read) {
                    circular = true;
                }
                else {
                    waiting.push(read);
                }
            }
            if circular || waiting.len() == wanted {
                waiting.truncate(wanted);
                let end = self.entries.live(unit).map_or_else(
                    || ConstantIndex::from(usize::from(unit).saturating_add(1)),
                    |entry| entry.unit().end,
                );
                let unkeyed = Maybe::Absent(crate::verdict::keyed::Absent::Unkeyed);
                demanded.hold((unit, end, UnitShape::Lone), (unkeyed, unkeyed));
                let _unkeyed = waiting.pop();
                let _done = tried.remove(&unit);
            }
        }
    }

    /// Key the unit whose first member stands at `first` from the keys that
    /// `demanded` holds, or put into `missing` each key it reads that
    /// `demanded` lacks.
    ///
    /// One pass reads every key the unit's key reads: a key that `demanded`
    /// lacks reads as a stand-in, so the pass names each one, and its digest
    /// is dropped.
    ///
    /// # Specification
    /// - requires: as [`Self::demanded_key`], and `missing` is empty.
    /// - ensures: when `missing` stays empty, `demanded` holds the unit's key
    ///   before its count, its key and each member's, as [`Self::demanded_key`]
    ///   states; otherwise `missing` holds positions that the key reads and
    ///   `demanded` keys none of, and units ranked below whose keys the count
    ///   needs.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the keys are digests, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::demanded_key`].
    /// - witness: `tests::verdicts::a_key_on_demand_is_the_key_of_its_admission_7456`
    fn demand_unit(
        &self,
        first: ConstantIndex,
        demanded: &mut DemandedKeys,
        missing: &mut Vec<ConstantIndex>,
    )
    {
        let unkeyed = Maybe::Absent(crate::verdict::keyed::Absent::Unkeyed);
        let Some(entry) = self.entries.live(first)
        else {
            let end = ConstantIndex::from(usize::from(first).saturating_add(1));
            demanded.hold((first, end, UnitShape::Lone), (unkeyed, unkeyed));
            return;
        };
        let unit = entry.unit();
        let span = (unit.first, unit.end, unit.shape);
        let ranks = self.unit_ranks(unit);
        let members = usize::from(unit.end).saturating_sub(usize::from(unit.first));
        if ranks.len() != members {
            demanded.hold(span, (unkeyed, unkeyed));
            return;
        }
        let raw = if let Some(&raw) = demanded.raw.get(&unit.first) {
            raw
        }
        else {
            let stand_in =
                crate::verdict::EntryContentKeyer::tagged(crate::verdict::EntryTag::Content)
                    .finish();
            let keys = &demanded.keys;
            let mut read = |position: ConstantIndex| {
                if let Some(&key) = keys.get(&position) {
                    key
                }
                else {
                    missing.push(position);
                    Maybe::Present(stand_in)
                }
            };
            let raw = match unit.shape {
                UnitShape::Lone => self.content_key_from(
                    core::slice::from_ref(entry.declaration()),
                    (unit.first, &ranks),
                    &mut read,
                ),
                UnitShape::Block => {
                    let declarations: Vec<Declaration> = (usize::from(unit.first)
                        .. usize::from(unit.end))
                        .filter_map(|member| self.entries.live(ConstantIndex::from(member)))
                        .map(|member| member.declaration().clone())
                        .collect();
                    if declarations.len() != members {
                        demanded.hold(span, (unkeyed, unkeyed));
                        return;
                    }
                    self.content_key_from(&declarations, (unit.first, &ranks), &mut read)
                },
            };
            if !missing.is_empty() {
                return;
            }
            raw
        };
        let key = match raw {
            Maybe::Present(content) if self.twinning(unit) == Twinning::Counted => {
                let below = ranks.first().copied().unwrap_or(SourceRank::ABOVE);
                let earlier = self.twins((unit, content, below), demanded, missing);
                if !missing.is_empty() {
                    // Kept, so the unit's key is not computed again.
                    let _previous = demanded.raw.insert(unit.first, raw);
                    return;
                }
                Maybe::Present(content.generative(earlier))
            },
            Maybe::Present(_) | Maybe::Absent(_) => raw,
        };
        demanded.hold(span, (raw, key));
    }

    /// How many units ranked below `below`, other than `unit`, hold the
    /// content key `content` before their count and count twins as `unit`
    /// does, each key as [`Self::demanded_key`] computes it. Each candidate
    /// whose key `demanded` lacks goes into `missing`, and the count then
    /// stands short.
    ///
    /// A twin has the shape of `unit`, members of its kinds that name as
    /// many positions, and its segments. So only a unit that passes those
    /// tests is keyed.
    ///
    /// # Specification
    /// - requires: as [`Self::demanded_key`], and `content` is the key of
    ///   `unit` before its count.
    /// - ensures: when `missing` takes no position, the count of the live units
    ///   ranked below `below`, other than `unit`, that count twins as `unit`
    ///   does and whose key before their count is `content`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the keys are digests, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::demanded_key`], whose program holds twin
    ///   axioms, twin sorts and twin blocks.
    /// - witness: `tests::verdicts::a_key_on_demand_is_the_key_of_its_admission_7456`
    fn twins(
        &self,
        (unit, content, below): (Unit, crate::verdict::EntryContentKey, SourceRank),
        demanded: &mut DemandedKeys,
        missing: &mut Vec<ConstantIndex>,
    ) -> crate::verdict::KeyedCount
    {
        let twinning = self.twinning(unit);
        let Maybe::Present(own) = self.fingerprint(unit, demanded)
        else {
            return crate::verdict::KeyedCount::default();
        };
        let members = |unit: Unit| {
            (usize::from(unit.first) .. usize::from(unit.end))
                .map(|member| self.entries.live(ConstantIndex::from(member)))
        };
        let mut count = 0_usize;
        for position in 0 .. usize::from(self.entries.len()) {
            let first = ConstantIndex::from(position);
            let Some(entry) = self.entries.live(first)
            else {
                continue;
            };
            let candidate = entry.unit();
            if first == unit.first
                || candidate.first != first
                || candidate.shape != unit.shape
                || self.entries.rank_of(first).is_none_or(|rank| rank >= below)
                || self.twinning(candidate) != twinning
                || members(candidate).len() != members(unit).len()
                || !members(candidate)
                    .zip(members(unit))
                    .all(|pair| match pair {
                        (Some(theirs), Some(ours)) => {
                            core::mem::discriminant(theirs.content())
                                == core::mem::discriminant(ours.content())
                                && theirs.references().len() == ours.references().len()
                        },
                        (Some(_) | None, Some(_) | None) => false,
                    })
            {
                continue;
            }
            if !matches!(self.fingerprint(candidate, demanded), Maybe::Present(theirs) if theirs == own)
            {
                continue;
            }
            match demanded.raw.get(&first) {
                Some(&Maybe::Present(theirs)) if theirs == content => {
                    count = count.saturating_add(1);
                },
                Some(&(Maybe::Present(_) | Maybe::Absent(_))) => {},
                None => missing.push(first),
            }
        }
        crate::verdict::KeyedCount::from(count)
    }

    /// The digest of the keyed segments of `unit`'s members, which two units
    /// of one content key share, kept in `demanded`.
    ///
    /// # Specification
    /// trivial.
    fn fingerprint(
        &self,
        unit: Unit,
        demanded: &mut DemandedKeys,
    ) -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>
    {
        use crate::verdict::KeyedCount;
        if let Some(&held) = demanded.images.get(&unit.first) {
            return held;
        }
        let mut keyer =
            crate::verdict::EntryContentKeyer::tagged(crate::verdict::EntryTag::Content);
        let members = usize::from(unit.first) .. usize::from(unit.end);
        keyer.count(KeyedCount::from(members.len()));
        let mut held = Maybe::Present(());
        for member in members {
            let Some(entry) = self.entries.live(ConstantIndex::from(member))
            else {
                held = Maybe::Absent(crate::verdict::keyed::Absent::Unkeyed);
                break;
            };
            let marked =
                MarkedDeclaration::new(AdmissionMark::Checked, entry.declaration().clone());
            let Maybe::Present(segment) =
                gandr_kernel_term::keyed_segment(&self.arena, &marked, unit.first .. unit.end)
            else {
                held = Maybe::Absent(crate::verdict::keyed::Absent::OpenSeal);
                break;
            };
            keyer.segment(segment.image());
            keyer.count(KeyedCount::from(segment.named().len()));
        }
        let held = match held {
            Maybe::Present(()) => Maybe::Present(keyer.finish()),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        };
        let _previous = demanded.images.insert(unit.first, held);
        held
    }

    /// The entry key of an entry whose content key is `content`: the content
    /// key bound to the build identity this environment keys under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entry_key(
        &self,
        content: Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    ) -> Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>
    {
        match (content, self.verdicts.build()) {
            (Maybe::Present(content), Maybe::Present(build)) => {
                Maybe::Present(crate::verdict::VerdictKey::entry(build, content))
            },
            (Maybe::Absent(absent), _) | (Maybe::Present(_), Maybe::Absent(absent)) => {
                Maybe::Absent(absent)
            },
        }
    }

    /// Key the atom at `atom`, closed at `extent`, and each unit in its scope
    /// that holds no key, in the order of their positions: the keys that a
    /// fresh admission of the closed module gives. A member admitted while
    /// the seal was open read the atom open, so it took no key.
    ///
    /// # Specification
    /// trivial.
    fn key_scope(
        &mut self,
        atom: ConstantIndex,
        extent: SealExtent,
    )
    {
        let end = usize::from(atom)
            .saturating_add(usize::from(extent))
            .saturating_add(1);
        let mut at = usize::from(atom);
        while at < end {
            let position = ConstantIndex::from(at);
            let Some(entry) = self.entries.live(position)
            else {
                at = at.saturating_add(1);
                continue;
            };
            let unit = entry.unit();
            at = usize::from(unit.end).max(at.saturating_add(1));
            if unit.first != position || matches!(entry.key(), Maybe::Present(_)) {
                continue;
            }
            let ranks = self.unit_ranks(unit);
            let Maybe::Present(key) = self.unit_key(entry, (position, &ranks))
            else {
                continue;
            };
            for (offset, member) in (usize::from(unit.first) .. usize::from(unit.end)).enumerate() {
                let content = key.member(crate::verdict::KeyedCount::from(offset));
                let Maybe::Present(entry) = self.entry_key(Maybe::Present(content))
                else {
                    continue;
                };
                self.entries
                    .rekey(ConstantIndex::from(member), (content, entry));
            }
            if let Some(content) = key.generative {
                alloc::sync::Arc::make_mut(&mut self.commits).generative(content, position);
            }
        }
    }

    /// Give each live entry ranked at or above `floor` the rank `ranks` names
    /// for it: the rank of its place in the edited source, one word for each
    /// entry. Each entry ranked below `floor` keeps its rank.
    ///
    /// A readmission rewrites the rank of every live entry past the run it
    /// shares with its record before it checks any, so each check reads the
    /// final environment below its rank. The rewrite moves no position, checks
    /// nothing and mints nothing, and it reads and writes nothing below
    /// `floor`. A rewrite that changes no rank writes nothing. A key holds the
    /// order of the ranks it reads and no rank's value, so an entry whose
    /// inputs keep their order keeps its key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, each live entry ranked at or above `floor` holds
    ///   the rank `ranks` names for it, each other entry holds its rank, and
    ///   every reader of ranks reads them: the rank table, the presented types,
    ///   the types of words over each sort and the order of the twins. When no
    ///   rank changes, the environment is unchanged. On refusal, the
    ///   environment is unchanged. Either way the entries keep their number,
    ///   and the arena mints nothing.
    /// - provides: the rank rewrite of a readmission that keeps each entry
    ///   outside the reach of an edit live.
    /// - fails: [`KernelError::UnboundConstant`] at a position that is not
    ///   live; [`KernelError::RankTaken`] when two positions take one rank;
    ///   [`KernelError::Unkept`] for [`crate::error::KeepRefusal::Ranks`] when
    ///   a live entry ranked at or above `floor` is named twice or not at all,
    ///   or when an entry ranked below `floor` is named or a rank below `floor`
    ///   is given; and [`KernelError::UnsettledReleases`] while a released
    ///   check is not settled.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an environment whose entries take new ranks in their
    ///   order, and whose entries are each kept in place, reads as a fresh
    ///   admission at those ranks, entry by entry, and exports its bytes; a
    ///   rewrite that misses a live entry is refused and changes nothing; a
    ///   rewrite above a floor keeps each rank below it, and refuses a rank
    ///   that crosses it.
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    /// - witness: `environment::tests::a_rank_rewrite_that_misses_a_live_entry_is_refused_6846`
    /// - witness: `environment::tests::a_rank_rewrite_above_a_floor_keeps_each_rank_below_it_7235`
    #[spec(captures: [length = self.entries.len(), watermark = self.arena.watermark()],
        ensures: |ret| self.entries.len() == length && self.arena.watermark() == watermark
            && (ret.is_err() || ranks.iter().all(|&(position, rank)| self.entries.rank_of(position) == Some(rank))))]
    #[inline]
    pub fn rerank(
        &mut self,
        (floor, ranks): (SourceRank, &[(ConstantIndex, SourceRank)]),
    ) -> Result<(), KernelError>
    {
        self.settled()?;
        let unkept = |position| KernelError::Unkept {
            position,
            refusal: crate::error::KeepRefusal::Ranks,
        };
        let mut by_position: BTreeMap<ConstantIndex, SourceRank> = BTreeMap::new();
        let mut taken: BTreeMap<SourceRank, ConstantIndex> = BTreeMap::new();
        let mut moved = false;
        for &(position, rank) in ranks {
            let Some(held) = self.entries.rank_of(position)
            else {
                return Err(KernelError::UnboundConstant { index: position });
            };
            if let Some(&by) = taken.get(&rank) {
                return Err(KernelError::RankTaken { rank, by });
            }
            // An entry below the floor keeps its rank, and no entry moves
            // below the floor.
            if held < floor || rank < floor || by_position.insert(position, rank).is_some() {
                return Err(unkept(position));
            }
            let _fresh = taken.insert(rank, position);
            moved |= held != rank;
        }
        if let Some(missing) = self
            .commits
            .ranked_from(floor)
            .find(|position| !by_position.contains_key(position))
        {
            return Err(unkept(missing));
        }
        if !moved {
            return Ok(());
        }
        let length = self.entries.len();
        alloc::sync::Arc::make_mut(&mut self.commits).rerank((floor, &by_position), length);
        self.entries.rerank(&by_position);
        Ok(())
    }

    /// Rank each later admission staged with no rank from `from` on, one rank
    /// for each entry, until [`Self::ranking_past`].
    ///
    /// A readmission that keeps the entries outside the reach of an edit
    /// crosses each other declaration at its place in the edited source: it
    /// sets the next rank at that place before the crossing, so a seed the
    /// crossing admits ranks just below its first reader, as a fresh
    /// admission ranks it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next admission staged with no rank takes `from`, and each
    ///   after it the rank past the one before. Nothing else changes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a readmission that crosses each edited declaration at
    ///   its place reads as a fresh admission of the edited source.
    /// - witness: `environment::tests::a_crossing_at_the_next_rank_ranks_at_its_place_6846`
    #[spec(ensures: self.commits.next == Some(from))]
    #[inline]
    pub fn ranking_from(
        &mut self,
        from: SourceRank,
    )
    {
        if self.commits.next != Some(from) {
            alloc::sync::Arc::make_mut(&mut self.commits).next = Some(from);
        }
    }

    /// Rank each later admission staged with no rank past every live entry,
    /// as an environment with no next rank ranks it ([`Self::ranking_from`]).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no next rank is set. Nothing else changes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::ranking_from`].
    /// - witness: `environment::tests::a_crossing_at_the_next_rank_ranks_at_its_place_6846`
    #[spec(ensures: self.commits.next.is_none())]
    #[inline]
    pub fn ranking_past(&mut self)
    {
        if self.commits.next.is_some() {
            alloc::sync::Arc::make_mut(&mut self.commits).next = None;
        }
    }

    /// The rank that the next admission staged with no rank takes, while a
    /// readmission sets one ([`Self::ranking_from`]).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn next_rank(&self) -> Maybe<SourceRank, next_rank::Absent>
    {
        self.commits
            .next
            .map_or(Maybe::Absent(next_rank::Absent::Unset), Maybe::Present)
    }

    /// Move the live entry at `position` to the next rank, and the next rank
    /// one past it.
    ///
    /// A readmission that keeps the entries outside the reach of an edit keeps
    /// a seed just below its first kept reader. A crossing at an earlier place
    /// that reads the seed takes it to the next rank, just below itself, where
    /// a fresh admission of the edited source seeds it. Each input of the
    /// entry's check stays below it in the same order, so the entry keeps its
    /// key; a reader that ranks past it may now read its inputs in another
    /// order, and its own key check in place says so.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the entry holds the rank that was next, every
    ///   reader of ranks reads it, the next rank is one past it, and the key
    ///   chain ends. On refusal, the environment is unchanged. Either way the
    ///   entries keep their number, and the arena mints nothing.
    /// - provides: the move of a kept seed that a crossing reads first.
    /// - fails: [`KernelError::UnboundConstant`] at a position that is not
    ///   live; [`KernelError::RankTaken`] when a live entry holds the next
    ///   rank; [`KernelError::Unkept`] for
    ///   [`crate::error::KeepRefusal::NextRank`] when no next rank is set, when
    ///   the entry ranks below it, or when an input of its check ranks at or
    ///   past it; and [`KernelError::UnsettledReleases`] while a released check
    ///   is not settled.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a kept seed that a crossing reads first moves below
    ///   the crossing, and the readmission answers as a whole one and keeps
    ///   each other entry.
    /// - witness: `environment::tests::a_seed_takes_the_next_rank_below_its_first_reader_7196`
    #[spec(captures: [length = self.entries.len(), watermark = self.arena.watermark()],
        ensures: |ret| self.entries.len() == length && self.arena.watermark() == watermark
            && (ret.is_err() || self.entries.rank_of(position).is_some_and(|rank| matches!(self.next_rank(), Maybe::Present(next) if usize::from(next) == usize::from(rank).saturating_add(1)))))]
    #[inline]
    pub fn take_next_rank(
        &mut self,
        position: ConstantIndex,
    ) -> Result<(), KernelError>
    {
        self.settled()?;
        let unkept = KernelError::Unkept {
            position,
            refusal: crate::error::KeepRefusal::NextRank,
        };
        let Some(from) = self.entries.rank_of(position)
        else {
            return Err(KernelError::UnboundConstant { index: position });
        };
        let Some(to) = self.commits.next
        else {
            return Err(unkept);
        };
        if from < to
            || self
                .entries
                .waits_on(position)
                .any(|input| self.entries.rank_of(input).is_none_or(|rank| rank >= to))
        {
            return Err(unkept);
        }
        if let Some(by) = self.commits.ranked(to) {
            return Err(KernelError::RankTaken { rank: to, by });
        }
        let length = self.entries.len();
        alloc::sync::Arc::make_mut(&mut self.commits).moved((position, from), to, length);
        self.entries.rerank(&BTreeMap::from([(position, to)]));
        Ok(())
    }

    /// Keep the live unit whose first member stands at `first` at the ranks
    /// it holds, when its own key says that its check reads what it read.
    ///
    /// After [`Self::rerank`], a readmission walks the edited source in rank
    /// order and checks each entry outside the reach in place: its key,
    /// computed again over the final environment below its rank, against the
    /// key it was admitted under. The check translates and encodes nothing,
    /// and it mints nothing. A plain definition kept alone takes the name a
    /// fresh admission at its rank gives, since a twin of its content may have
    /// left or joined below it.
    ///
    /// The kernel computes no key again for a unit that its own watermark
    /// covers. Each entry ranked at or below the watermark reads what it read
    /// when the kernel last checked its key, so the held key answers by
    /// lookup. Each commit, retire, rank rewrite, move and change of the
    /// manifest lowers the watermark. A check of the next key above it raises
    /// it, after the kernel checks each unit in the gap that the walk does not
    /// keep, as a seed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the unit stays live at its ranks with its keys,
    ///   and a plain definition kept alone holds the name a fresh admission at
    ///   its rank gives; on refusal, the environment is unchanged, and the
    ///   caller retires the unit and offers its declaration. Either way the
    ///   entries keep their number, and the arena mints nothing.
    /// - provides: the key check in place of a readmission that keeps each
    ///   entry outside the reach of an edit live, and a lookup in place of the
    ///   check while nothing the check reads changed.
    /// - fails: [`KernelError::UnboundConstant`] at `first` when it holds no
    ///   entry, or at a position the unit names that is not live or not ranked
    ///   below the unit; [`KernelError::Retired`] when the entry at `first` is
    ///   retired; [`KernelError::Unkept`] when `first` is not the first member
    ///   of its unit, or when the unit or its check now has no key, or when the
    ///   key its check reads now is another key; and
    ///   [`KernelError::UnsettledReleases`] while an outstanding release reads
    ///   into the unit's key or its name ([`Self::keeps_beside`]).
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::rerank`]; an entry that reads a retired
    ///   one is refused in place, and so is one whose precedence changed; a
    ///   twin kept after an appended one reads as after it; a lookup after a
    ///   second rank rewrite answers as the check does.
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    /// - witness: `environment::tests::a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281`
    /// - witness: `environment::tests::an_entry_that_reads_a_retired_one_is_refused_in_place_6846`
    /// - witness: `environment::tests::an_entry_kept_in_place_after_an_appended_twin_reads_as_after_it_6846`
    /// - witness: `environment::tests::a_held_key_answers_until_an_admission_below_it_7197`
    /// - witness: `ruled::tests::a_keep_whose_precedence_changed_is_refused_6621`
    /// - witness: `ruled::tests::an_appended_reach_orients_a_law_as_a_fresh_admission_does_6621`
    #[spec(captures: [length = self.entries.len(), watermark = self.arena.watermark()],
        ensures: |ret| self.entries.len() == length && self.arena.watermark() == watermark
            && ret.as_ref().map_or(true, |kept| self.entries.live(kept.position()).is_some()))]
    #[inline]
    pub fn keep_in_place(
        &mut self,
        first: ConstantIndex,
    ) -> Result<CheckedId, KernelError>
    {
        let Some(entry) = self.entries.live(first)
        else {
            return Err(match self.entries.family().get(usize::from(first)) {
                Some(&Slot::Retired) => KernelError::Retired { position: first },
                Some(&(Slot::Admitted(_) | Slot::Vacant | Slot::Reserved)) | None => {
                    KernelError::UnboundConstant { index: first }
                },
            });
        };
        let unit = entry.unit();
        if unit.first != first {
            return Err(KernelError::Unkept {
                position: first,
                refusal: crate::error::KeepRefusal::Unit,
            });
        }
        // A held key answers by lookup only while no outstanding release
        // reads into it, as the check in place does.
        let beside = if usize::from(self.releases.outstanding()) == 0 {
            None
        }
        else {
            let ranks = self.unit_ranks(unit);
            self.keeps_beside((first, &ranks))?;
            Some(ranks)
        };
        if self.lookup(unit) == Lookup::Answers {
            return Ok(CheckedId::new(first));
        }
        let ranks = beside.unwrap_or_else(|| self.unit_ranks(unit));
        self.check_in_place(first, &ranks)?;
        self.key_through(unit, &ranks);
        Ok(CheckedId::new(first))
    }

    /// Whether the held keys of `unit` answer for its check by lookup: the
    /// watermark covers each member, and each member holds a key under a
    /// policy that keys.
    ///
    /// # Specification
    /// trivial.
    fn lookup(
        &self,
        unit: crate::env::Unit,
    ) -> Lookup
    {
        let members = usize::from(unit.first) .. usize::from(unit.end);
        let covered = members
            .clone()
            .filter_map(|member| self.entries.rank_of(ConstantIndex::from(member)))
            .max()
            .is_some_and(|top| self.commits.keyed_through.is_some_and(|held| top <= held));
        let keyed = members.into_iter().all(|member| {
            self.entries
                .live(ConstantIndex::from(member))
                .is_some_and(|member| matches!(member.key(), Maybe::Present(_)))
        });
        if covered && keyed && self.verdicts.keying() == crate::verdict::Keying::Keys {
            Lookup::Answers
        }
        else {
            Lookup::Checks
        }
    }

    /// The ranks of the members of `unit`, in the order of their positions.
    ///
    /// # Specification
    /// trivial.
    fn unit_ranks(
        &self,
        unit: crate::env::Unit,
    ) -> Vec<SourceRank>
    {
        (usize::from(unit.first) .. usize::from(unit.end))
            .filter_map(|member| self.entries.rank_of(ConstantIndex::from(member)))
            .collect()
    }

    /// Check the unit whose first member stands at `first` in place, at its
    /// `ranks`, and give a plain definition kept alone the name a fresh
    /// admission at its rank gives.
    ///
    /// # Specification
    /// - requires: `first` holds the first member of a live unit, and `ranks`
    ///   names each member, ascending.
    /// - ensures: as [`Self::keep_in_place`] with no lookup.
    /// - fails: as [`Self::holds_its_key`].
    /// - panics: none.
    /// - executable: none — the clauses state the environment before and after
    ///   the change, which a predicate may not capture whole.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::keep_in_place`].
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    fn check_in_place(
        &mut self,
        first: ConstantIndex,
        ranks: &[SourceRank],
    ) -> Result<(), KernelError>
    {
        let Some(entry) = self.entries.live(first)
        else {
            return Err(KernelError::UnboundConstant { index: first });
        };
        self.holds_its_key(entry, (first, ranks))?;
        // A twin's order among the plain definitions of its content is in its
        // name: the kept twin takes the order of its rank among those live now.
        if matches!(entry.unit().shape, UnitShape::Lone)
            && let ConstantName::Definition { declared, body, .. } = entry.key_name()
            && let Some(&rank) = ranks.first()
        {
            let held = entry.key_name();
            let named = crate::encoding::name_definition(
                self.names.session_mut().table_mut(),
                &self.arena,
                (&self.entries, first, rank),
                declared,
                body,
            );
            if named != held {
                self.entries.rename(first, named);
            }
        }
        Ok(())
    }

    /// Raise the watermark through `unit`, whose key holds at `ranks`. Each
    /// unit that stands in the gap below it is checked in place first: a
    /// walk in rank order passes such a unit and does not keep it, as a seed.
    /// The watermark stops below the first unit in the gap whose check fails.
    ///
    /// # Specification
    /// trivial.
    fn key_through(
        &mut self,
        unit: crate::env::Unit,
        ranks: &[SourceRank],
    )
    {
        let Some(&through) = ranks.last()
        else {
            return;
        };
        while let Some((rank, position)) = self.commits.next_stale()
            && rank <= through
        {
            if unit.holds(position) == Membership::Member {
                let commits = alloc::sync::Arc::make_mut(&mut self.commits);
                for &member in ranks {
                    commits.keyed(member);
                }
                return;
            }
            let Some(gap) = self.entries.live(position).map(AdmittedDeclaration::unit)
            else {
                return;
            };
            let gap_ranks = self.unit_ranks(gap);
            if gap.first != position
                || gap_ranks.last().is_none_or(|&last| last > through)
                || self.keeps_beside((position, &gap_ranks)).is_err()
                || self.check_in_place(position, &gap_ranks).is_err()
            {
                return;
            }
            let commits = alloc::sync::Arc::make_mut(&mut self.commits);
            for &member in &gap_ranks {
                commits.keyed(member);
            }
        }
    }

    /// Close the admission that minted `atom`: from the next admission on, the
    /// atom is opaque.
    ///
    /// The kernel draws the boundary itself, from its own admission count: the
    /// extent it records is how many declarations it admitted after the atom,
    /// so no later declaration can claim its way inside, and an artifact
    /// exported from this environment carries the boundary as drawn.
    ///
    /// # Specification
    /// - requires: nothing — a receipt for anything but an open abstract type
    ///   is refused.
    /// - ensures: on success the atom is not manifest, its held declaration's
    ///   scope is closed at the number of declarations admitted after it, and
    ///   that extent is returned. Each unit of the closed scope that holds no
    ///   key takes the key a fresh admission of the closed module gives it.
    ///   Every other face of the environment is unchanged, and on failure
    ///   nothing changes.
    /// - provides: the close a producer sealing a module issues once its
    ///   members are admitted.
    /// - fails: [`KernelError::SealNotOpen`] when `atom` names no abstract type
    ///   staged [`SealScope::Open`] whose admission is still open — a closed
    ///   atom, one whose own scope closes it, or any other declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::SealNotOpen`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member admitted before the close checks at the
    ///   representation, a value of the representation offered after it is
    ///   refused, and a second close of the same atom is refused.
    /// - witness: `environment::tests::a_value_of_the_representation_does_not_inhabit_the_atom`
    /// - witness: `environment::tests::an_atom_seals_once`
    /// - witness: `environment::tests::a_seal_keys_its_scope_as_an_admission_of_the_closed_module_7200`
    #[spec(
        captures: [entry_len = self.entries.len(), entry_manifest = self.manifest.len()],
        ensures: |ret| self.entries.len() == entry_len && ret.as_ref().map_or_else(
            |error| self.manifest.len() == entry_manifest
                && *error == KernelError::SealNotOpen { index: atom.position() },
            |extent| self.manifest.len().checked_add(1) == Some(entry_manifest)
                && self.manifest.binary_search(&atom.position()).is_err()
                && usize::from(atom.position()).checked_add(usize::from(*extent)).and_then(|end| end.checked_add(1)) == Some(usize::from(entry_len)),
        ),
    )]
    #[inline]
    pub fn seal(
        &mut self,
        atom: CheckedId,
    ) -> Result<SealExtent, KernelError>
    {
        let position = atom.position();
        let refused = KernelError::SealNotOpen { index: position };
        let Some(held) = self.manifest.iter().position(|&open| open == position)
        else {
            return Err(refused);
        };
        let extent = SealExtent::from(
            usize::from(self.entries.len())
                .saturating_sub(usize::from(position))
                .saturating_sub(1),
        );
        let Some(entry) = self.entries.get_mut(usize::from(position))
        else {
            return Err(refused);
        };
        let DeclarationContent::AbstractType {
            scope: SealScope::Open,
            ..
        } = *entry.declaration().content()
        else {
            return Err(refused);
        };
        entry.close(extent);
        let _closed = self.manifest.remove(held);
        // Each key reads the manifest whole.
        alloc::sync::Arc::make_mut(&mut self.commits).stale_all();
        self.key_scope(position, extent);
        Ok(extent)
    }

    /// Re-admit an artifact's declarations, in order, into a fresh environment
    /// over the arena their content lives in.
    ///
    /// Each declaration passes the same choke point it passed when it was
    /// produced — checked through [`Self::add_decl`], or through the warned
    /// bypass when the artifact marks it so — and each abstract type closes
    /// at the extent its record carries, so a sealed module's members are
    /// re-checked at the representation and every later declaration against
    /// the atom.
    ///
    /// # Specification
    /// - requires: every root of `declarations` resolves in `arena`, as a
    ///   decoded artifact's do.
    /// - ensures: `Ok` holding an environment with one entry per declaration,
    ///   in order, each admitted as its mark says, whose audit is the producing
    ///   environment's; or the first refusal with the position it met.
    /// - provides: the replay a reader runs over a decoded artifact, which is
    ///   what makes the artifact's opacity a kernel fact rather than a
    ///   producer's claim.
    /// - fails: [`ArtifactRefusal`] naming the first declaration the kernel
    ///   rejects and why.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactRefusal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sealed module's export replays; a copy whose client
    ///   reads the atom at its representation, a copy whose atom was downgraded
    ///   to an axiom, and a copy whose provenance was rewritten are each
    ///   refused at the declaration that broke.
    /// - witness: `tests::sealed_export::the_export_of_a_sealed_module_replays`
    /// - witness: `tests::sealed_export::an_atom_downgraded_to_an_axiom_fails_to_replay`
    /// - witness: `tests::sealed_export::sealing_provenance_round_trips_and_cannot_be_rewritten`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |refusal| usize::from(refusal.position()) < declarations.len(),
        |environment| environment.entries.len() == declarations.len(),
    ))]
    #[inline]
    pub fn replay(
        arena: TermArena,
        declarations: &[MarkedDeclaration],
    ) -> Result<Self, ArtifactRefusal>
    {
        let floor = arena.watermark();
        let mut environment = Self {
            arena,
            admission_floor: floor,
            ..Self::default()
        };
        let mut position = 0_usize;
        while let Some(marked) = declarations.get(position) {
            // A data declaration whose fields name later positions leads the
            // block they reach, measured as both checkers measure it, and the
            // block is admitted whole.
            let end = usize::from(block_end(
                &environment.arena,
                declarations,
                ConstantIndex::from(position),
            ));
            if end > position.saturating_add(1) {
                let members = declarations.get(position .. end).unwrap_or_default();
                if members
                    .iter()
                    .all(|member| member.mark() == AdmissionMark::Checked)
                {
                    let staged = members
                        .iter()
                        .map(|member| {
                            StagedDeclaration::new(floor, None, member.declaration().clone())
                        })
                        .collect();
                    let _admitted =
                        environment
                            .add_block(staged)
                            .map_err(|error| ArtifactRefusal {
                                position: ConstantIndex::from(position),
                                error,
                            })?;
                    position = end;
                    continue;
                }
            }
            let staged = StagedDeclaration::new(floor, None, marked.declaration().clone());
            match marked.mark() {
                AdmissionMark::Checked => {
                    let _admitted =
                        environment
                            .add_decl(staged)
                            .map_err(|error| ArtifactRefusal {
                                position: ConstantIndex::from(position),
                                error,
                            })?;
                },
                AdmissionMark::UncheckedBypass => {
                    let _admitted = environment.add_decl_unchecked(staged).map_err(|error| {
                        ArtifactRefusal {
                            position: ConstantIndex::from(position),
                            error,
                        }
                    })?;
                },
            }
            position = position.saturating_add(1);
        }
        Ok(environment)
    }

    /// Open an atom just admitted at `position`, and close every atom whose
    /// scope that admission exhausted.
    ///
    /// # Specification
    /// - requires: `position` is the last entry's.
    /// - ensures: the manifest holds, ascending, exactly the earlier atoms
    ///   staged open and not yet sealed, the earlier atoms whose closed scope
    ///   still reaches past `position`, and the entry at `position` when it is
    ///   an abstract type staged open or closed past nothing less than one
    ///   declaration.
    /// - provides: the one place the manifest moves on admission, shared by the
    ///   checked choke point and the bypass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a replayed atom closed after one member is manifest
    ///   for that member and opaque for the next declaration.
    /// - witness: `tests::sealed_export::the_export_of_a_sealed_module_replays`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every held atom once to retain it; the check reads each twice"
        )
    )]
    #[spec(ensures: self.manifest.windows(2).all(|pair| pair.first() < pair.last())
        && self.manifest.iter().all(|&atom| atom <= position))]
    fn advance_seals(
        &mut self,
        position: ConstantIndex,
    )
    {
        let reaches_past = |atom: ConstantIndex, extent: SealExtent| {
            usize::from(atom).saturating_add(usize::from(extent)) > usize::from(position)
        };
        let Self {
            ref entries,
            ref mut manifest,
            ref mut atoms,
            ref mut commits,
            ..
        } = *self;
        let before = manifest.len();
        manifest.retain(|&atom| {
            match entries
                .get(usize::from(atom))
                .map(AdmittedDeclaration::content)
            {
                Some(&DeclarationContent::AbstractType {
                    scope: SealScope::Closed(extent),
                    ..
                }) => reaches_past(atom, extent),
                Some(&DeclarationContent::AbstractType {
                    scope: SealScope::Open,
                    ..
                }) => true,
                Some(_) | None => false,
            }
        });
        let mut changed = manifest.len() != before;
        let content = entries
            .get(usize::from(position))
            .map(AdmittedDeclaration::content);
        if matches!(content, Some(&DeclarationContent::AbstractType { .. })) {
            atoms.push(position);
        }
        match content {
            Some(&DeclarationContent::AbstractType {
                scope: SealScope::Open,
                ..
            }) => {
                manifest.push(position);
                changed = true;
            },
            Some(&DeclarationContent::AbstractType {
                scope: SealScope::Closed(extent),
                ..
            }) if reaches_past(position, extent) => {
                manifest.push(position);
                changed = true;
            },
            Some(_) | None => {},
        }
        // Each key reads the manifest whole.
        if changed {
            alloc::sync::Arc::make_mut(commits).stale_all();
        }
    }

    /// The content key of `members`, admitted as one unit from `first` on at
    /// the ranks `ranks`: what their checks read, with each position they name
    /// written as its entry's key.
    ///
    /// # Specification
    /// - requires: `first` is the position of the unit's first member: the
    ///   environment's length at an admission, and the first position of the
    ///   retired unit at a keep. `members` are in the environment's arena, and
    ///   `ranks` holds one rank per member, ascending.
    /// - ensures: absent as
    ///   [`keyed::Absent::Rechecking`](crate::verdict::keyed::Absent::Rechecking)
    ///   under a policy that rechecks, as
    ///   [`keyed::Absent::OpenSeal`](crate::verdict::keyed::Absent::OpenSeal)
    ///   when a member is an abstract type sealed to the end of the sequence,
    ///   and as [`keyed::Absent::Unkeyed`](crate::verdict::keyed::Absent::Unkeyed)
    ///   when a position a member names, a type of words its references reach,
    ///   a role holder it reads or an atom manifest at the admission has no
    ///   entry key. Otherwise the key over this kernel's build; each member's
    ///   keyed segment, the keys of the positions it names in the order it
    ///   names them, and what [`Self::key_ranks`] writes of its ranks; each
    ///   manifest atom's key with how many members read it; and the keys of the
    ///   types of words ranked below the first member over each sort the
    ///   references reach, in rank order.
    /// - provides: one key for two units at two positions exactly when, up to a
    ///   BLAKE3 collision, their checks read the same content in the same
    ///   source order.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the key is a digest, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an edit re-keys the declarations that read the edited
    ///   one and no other; a key reads no admission order outside operation
    ///   rules; two axioms of one type take two keys; a type of words over a
    ///   reached sort re-keys a declaration, and one over another sort or
    ///   ranked above the declaration does not; a ruled definition whose
    ///   operations swap their ranks takes another key.
    /// - witness: `tests::verdicts::an_edit_re_keys_only_what_reads_it_6568`
    /// - witness: `tests::verdicts::a_key_reads_no_admission_order_6568`
    /// - witness: `tests::verdicts::two_axioms_of_one_type_take_two_keys_6568`
    /// - witness: `tests::verdicts::words_over_a_reached_sort_re_key_a_declaration_6568`
    /// - witness: `tests::verdicts::words_ranked_above_a_declaration_do_not_re_key_it_6621`
    /// - witness: `ruled::tests::a_ruled_definition_is_keyed_by_the_rank_order_of_what_it_names_6621`
    fn content_key(
        &self,
        members: &[Declaration],
        (first, ranks): (ConstantIndex, &[SourceRank]),
    ) -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>
    {
        if self.verdicts.keying() == crate::verdict::Keying::Rechecks {
            return Maybe::Absent(crate::verdict::keyed::Absent::Rechecking);
        }
        self.content_key_from(members, (first, ranks), &mut |position| {
            self.entries.content(position)
        })
    }

    /// The content key of `members`, admitted as one unit from `first` on at
    /// the ranks `ranks`, with the key of each position that their checks
    /// read taken from `keys`: [`Self::content_key`] reads the entries' keys,
    /// and [`Self::demanded_key`] the keys it computes on demand.
    ///
    /// # Specification
    /// - requires: as [`Self::content_key`], and `keys` answers for each
    ///   admitted position the key that its admission under a policy that keys
    ///   gives it.
    /// - ensures: as [`Self::content_key`] under a policy that keys, under any
    ///   policy, with each key read through `keys`.
    /// - provides: one digest of a unit's content, whichever source holds the
    ///   keys of what it reads.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the key is a digest, which a predicate would
    ///   restate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::content_key`], and a key computed on
    ///   demand in an environment that keys nothing is the key of the
    ///   admission.
    /// - witness: `tests::verdicts::an_edit_re_keys_only_what_reads_it_6568`
    /// - witness: `tests::verdicts::a_key_on_demand_is_the_key_of_its_admission_7456`
    fn content_key_from<Keys>(
        &self,
        members: &[Declaration],
        (first, ranks): (ConstantIndex, &[SourceRank]),
        keys: &mut Keys,
    ) -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>
    where
        Keys: FnMut(
            ConstantIndex,
        )
            -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    {
        use crate::verdict::KeyedCount;
        use crate::verdict::keyed::Absent;
        let end = ConstantIndex::from(usize::from(first).saturating_add(members.len()));
        let below = ranks.first().copied().unwrap_or(SourceRank::ABOVE);
        let presentations = self.entries.presentations();
        let words = presentations.sorts().next().is_some();
        let mut keyer =
            crate::verdict::EntryContentKeyer::tagged(crate::verdict::EntryTag::Content);
        keyer.count(KeyedCount::from(members.len()));
        let mut reached = Vec::new();
        let mut order = Vec::new();
        let mut operations = Vec::new();
        for (offset, (member, &rank)) in members.iter().zip(ranks).enumerate() {
            let marked = MarkedDeclaration::new(AdmissionMark::Checked, member.clone());
            let Maybe::Present(segment) =
                gandr_kernel_term::keyed_segment(&self.arena, &marked, first .. end)
            else {
                return Maybe::Absent(Absent::OpenSeal);
            };
            keyer.segment(segment.image());
            keyer.count(KeyedCount::from(segment.named().len()));
            for &named in segment.named() {
                let Maybe::Present(key) = keys(named)
                else {
                    return Maybe::Absent(Absent::Unkeyed);
                };
                keyer.key(key);
            }
            let own = ConstantIndex::from(usize::from(first).saturating_add(offset));
            if let Err(absent) = self.key_ranks(
                (&mut keyer, &mut *keys),
                (member, (own, rank)),
                (segment.named(), (first, ranks)),
                (&mut order, &mut operations),
            ) {
                return Maybe::Absent(absent);
            }
            if words {
                reached.extend_from_slice(segment.named());
            }
        }
        // Each atom whose scope holds the first member is manifest for each
        // member its scope reaches. The scopes give the atoms manifest at the
        // admission, so a key computed again after a seal closes reads them
        // as the admission read them.
        let mut manifest = Vec::new();
        let atoms = self.atoms.partition_point(|&atom| atom < first);
        for &atom in self.atoms.get(.. atoms).unwrap_or_default() {
            let reach = match self.entries.live(atom).map(AdmittedDeclaration::content) {
                Some(&DeclarationContent::AbstractType {
                    scope: SealScope::Closed(extent),
                    ..
                }) => usize::from(atom).saturating_add(usize::from(extent)),
                Some(&DeclarationContent::AbstractType {
                    scope: SealScope::Open,
                    ..
                }) => return Maybe::Absent(Absent::Unkeyed),
                Some(_) | None => continue,
            };
            if reach < usize::from(first) {
                continue;
            }
            let Maybe::Present(key) = keys(atom)
            else {
                return Maybe::Absent(Absent::Unkeyed);
            };
            let read_by = reach
                .saturating_add(1)
                .saturating_sub(usize::from(first))
                .min(members.len());
            manifest.push((key, KeyedCount::from(read_by)));
        }
        manifest.sort_unstable();
        keyer.count(KeyedCount::from(manifest.len()));
        for (key, read_by) in manifest {
            keyer.key(key);
            keyer.count(read_by);
        }
        // The types of words ranked below the first member over each sort
        // the references reach, which a case over the sort owes a loop arm
        // for, in rank order.
        let mut registry = Vec::new();
        let mut visited = BTreeSet::new();
        while let Some(position) = reached.pop() {
            if !visited.insert(position) {
                continue;
            }
            for word in presentations.over(position) {
                let Some(word_rank) = self.entries.rank_of(word)
                else {
                    return Maybe::Absent(Absent::Unkeyed);
                };
                if word_rank < below {
                    registry.push((word_rank, word));
                }
            }
            if let Some(entry) = self.entries.live(position) {
                reached.extend(
                    entry
                        .references()
                        .iter()
                        .copied()
                        .filter(|named| !visited.contains(named)),
                );
            }
        }
        registry.sort_unstable();
        registry.dedup();
        keyer.count(KeyedCount::from(registry.len()));
        for (_, word) in registry {
            let Maybe::Present(key) = keys(word)
            else {
                return Maybe::Absent(Absent::Unkeyed);
            };
            keyer.key(key);
        }
        Maybe::Present(keyer.finish())
    }

    /// Write into `keyer` what the check of `member`, admitted at `own` and
    /// ranked at `rank`, reads of source order beyond its content and the
    /// keys of the positions it names, `named`; `keys` answers each key it
    /// reads, `first` and `ranks` place and rank the members of its unit, and
    /// `order` is scratch.
    ///
    /// # Specification
    /// - requires: each of `named` is an admitted position, and the unit's
    ///   members stand from `first` on, one per rank of `ranks`.
    /// - ensures: [`keyed::Absent::Unkeyed`](crate::verdict::keyed::Absent::Unkeyed)
    ///   when an operation the rules name stands neither in `named` nor in
    ///   the unit, or when it or a role holder the member reads has no entry
    ///   key or no rank. Otherwise written: for a member that carries
    ///   operation rules, the rank order of the operations they name, its own
    ///   among them, each written as its place in `named` or past it in the
    ///   unit, which the path order compares; then, for a role holder, the key
    ///   of each role's holder ranked first below it, or none. Nothing for a
    ///   member that carries no rules and holds no role: its check reads no
    ///   order among the entries it names.
    /// - provides: the one place where a key reads ranks, so a ruling on what a
    ///   key holds of source order changes this function alone. A twin's order
    ///   among the definitions of its content is in its name, and no check
    ///   reads it; the types of words below a rank are in the registry
    ///   [`Self::content_key`] writes.
    /// - fails: as `- ensures:`.
    /// - panics: none.
    /// - executable: none — what is written is digest input, which a predicate
    ///   would restate.
    ///
    /// # Errors
    /// As `- ensures:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::content_key`].
    /// - witness: `tests::verdicts::a_key_reads_no_admission_order_6568`
    /// - witness: `ruled::tests::a_ruled_definition_is_keyed_by_the_rank_order_of_what_it_names_6621`
    fn key_ranks<Keys>(
        &self,
        (keyer, keys): (&mut crate::verdict::EntryContentKeyer, &mut Keys),
        (member, (own, rank)): (&Declaration, (ConstantIndex, SourceRank)),
        (named, (first, ranks)): (&[ConstantIndex], (ConstantIndex, &[SourceRank])),
        (order, operations): (
            &mut Vec<(SourceRank, crate::verdict::KeyedCount)>,
            &mut Vec<ConstantIndex>,
        ),
    ) -> Result<(), crate::verdict::keyed::Absent>
    where
        Keys: FnMut(
            ConstantIndex,
        )
            -> Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    {
        use crate::verdict::KeyedCount;
        use crate::verdict::keyed::Absent;
        let rules = member.operation_rules().rules();
        if !rules.is_empty() {
            operations.clear();
            operations.push(own);
            for rule in rules {
                for node in rule.left().iter().chain(rule.right()) {
                    if let gandr_kernel_term::OperationNode::Operation { constant, .. } = *node {
                        operations.push(constant);
                    }
                }
            }
            operations.sort_unstable();
            operations.dedup();
            // An operation the member names stands at its place in `named`; an
            // operation of the unit, the member's own among them, stands past
            // `named` at its place in the unit.
            order.clear();
            for (place, &position) in named.iter().enumerate() {
                if operations.binary_search(&position).is_ok() {
                    let ranked = self.entries.rank_of(position).ok_or(Absent::Unkeyed)?;
                    order.push((ranked, KeyedCount::from(place)));
                }
            }
            let unit = operations.partition_point(|&operation| operation < first);
            for &operation in operations.get(unit ..).unwrap_or_default() {
                let Some((offset, &ranked)) = usize::from(operation)
                    .checked_sub(usize::from(first))
                    .and_then(|offset| Some((offset, ranks.get(offset)?)))
                else {
                    break;
                };
                order.push((ranked, KeyedCount::from(named.len().saturating_add(offset))));
            }
            // An operation that stands neither in `named` nor in the unit has
            // no key to read.
            if order.len() != operations.len() {
                return Err(Absent::Unkeyed);
            }
            order.sort_unstable();
            keyer.count(KeyedCount::from(order.len()));
            for &(_, place) in order.iter() {
                keyer.count(place);
            }
        }
        if let Maybe::Present(_) = member.role() {
            for role in gandr_kernel_term::Builtin::ALL {
                match self.entries.holder_below(role, rank) {
                    Some(holder) => {
                        let Maybe::Present(key) = keys(holder)
                        else {
                            return Err(Absent::Unkeyed);
                        };
                        keyer.count(KeyedCount::from(1_usize));
                        keyer.key(key);
                    },
                    None => keyer.count(KeyedCount::from(0_usize)),
                }
            }
        }
        Ok(())
    }

    /// The transitive audit of an admitted declaration.
    ///
    /// # Specification
    /// - requires: `id` was returned by this environment.
    /// - ensures: the axioms and unchecked admissions in the stored transitive
    ///   dependency set, each ascending.
    /// - provides: a positional projection of the precomputed dependency set.
    ///   Origin is a caller obligation because ids carry no environment
    ///   identity; completeness of that set is witnessed through admission and
    ///   graph walks.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — finite chains report their transitive axiom or
    ///   unchecked admission, including a reference reached only through a
    ///   code. L3 distinguishes a closed definition's empty report. These
    ///   witnesses do not establish completeness for arbitrary dependency
    ///   graphs.
    /// - witness: `environment::tests::audit_reports_the_transitive_axiom`
    /// - witness: `environment::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `environment::tests::audit_reaches_an_axiom_named_only_inside_a_code`
    /// - witness: `environment::tests::a_closed_definition_rests_on_nothing`
    #[spec(ensures: |ret| self.entries.peek(usize::from(id.position())).map_or_else(
        || ret.axioms().is_empty() && ret.unchecked_admissions().is_empty() && ret.primitives().is_empty(),
        |entry| ret.axioms().iter().copied().eq(entry.rested_on().iter().copied().filter(|&position|
            self.entries.peek(usize::from(position)).is_some_and(|ancestor|
                matches!(*ancestor.declaration().content(), DeclarationContent::Axiom { .. }))))
            && ret.unchecked_admissions().iter().copied().eq(entry.rested_on().iter().copied().filter(|&position|
                self.entries.peek(usize::from(position)).is_some_and(|ancestor|
                    matches!(ancestor.admission(), Admission::Unchecked))))
            && ret.primitives().iter().copied().eq(entry.rested_on().iter().copied().filter(|&position|
                self.entries.peek(usize::from(position)).is_some_and(|ancestor|
                    matches!(*ancestor.declaration().content(), DeclarationContent::LiteralIdentity { .. })))),
    ))]
    #[inline]
    #[must_use]
    pub fn audit(
        &self,
        id: CheckedId,
    ) -> AxiomReport
    {
        let Some(entry) = self.entries.get(usize::from(id.position()))
        else {
            return AxiomReport::default();
        };
        let ancestor = |position: ConstantIndex| self.entries.get(usize::from(position));
        let rested = || entry.rested_on().iter().copied();
        let mut positions: Vec<ConstantIndex> = rested()
            .filter(|&position| {
                ancestor(position).is_some_and(|held| {
                    matches!(
                        *held.declaration().content(),
                        DeclarationContent::Axiom { .. }
                    )
                })
            })
            .collect();
        let unchecked_from = positions.len();
        positions.extend(rested().filter(|&position| {
            ancestor(position).is_some_and(|held| matches!(held.admission(), Admission::Unchecked))
        }));
        let primitives_from = positions.len();
        positions.extend(rested().filter(|&position| {
            ancestor(position).is_some_and(|held| {
                matches!(
                    *held.declaration().content(),
                    DeclarationContent::LiteralIdentity { .. }
                )
            })
        }));
        AxiomReport {
            positions,
            unchecked_from,
            primitives_from,
        }
    }

    /// Precompute the transitive set of axioms, unchecked admissions and
    /// kernel primitives a declaration rests on.
    ///
    /// **A declaration depends on what its declared type names as well as on
    /// what its body names**, and the two are separate graphs to walk.
    /// Formation resting on a reference is exactly as load-bearing as a
    /// body resting on an axiom, so every arm's declared root is scanned —
    /// an abstract type's own kind included, and its representation beside
    /// it, because the members sealed over the atom were checked against
    /// that representation and reach it through the atom.
    ///
    /// **The type plane has two reference forms, and both are followed here.**
    /// A sealed atom names a declaration directly; a code names one through
    /// the term language, because a type read off a code carries a value. A
    /// walk that stopped at the code would drop a declaration reachable
    /// *only* that way out of the graph, and the report's own contract —
    /// empty on both faces means resting on nothing outside the checked
    /// kernel — would then be a false negative rather than a fact.
    ///
    /// # Specification
    /// - requires: `position` is the next admission index, or the slot that the
    ///   declaration's release reserved, and `content` and `laws` are its
    ///   declaration's. Checked references name earlier admissions; a bypass is
    ///   itself an audit reason even if it names an unknown position.
    /// - ensures: the union of the audits of every position the declared type,
    ///   an abstract type's representation or a definition's body names, and of
    ///   every law the definition's folds rest on, with `position` itself
    ///   included exactly when the declaration is an axiom, a literal identity
    ///   test or is being bypassed. Both reference forms of the type plane are
    ///   followed — a sealed atom directly, and a code through the term
    ///   language — so a declaration reachable only through a code stays in the
    ///   graph.
    /// - provides: the precomputed audit an admission stores, which makes the
    ///   report a lookup rather than a walk, and which is what lets "empty on
    ///   both faces" be a fact rather than a false negative.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite axiom and unchecked chains preserve their
    ///   audit reasons through definitions and through type-level code edges.
    ///   The predicate checks self-inclusion and the classification of every
    ///   returned earlier position, not reachability of arbitrary graphs.
    /// - witness: `environment::tests::audit_reports_the_transitive_axiom`
    /// - witness: `environment::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `environment::tests::audit_reaches_an_axiom_named_only_inside_a_code`
    /// - witness: `tests::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
    #[spec(
        requires: usize::from(position) <= usize::from(self.entries.len()),
        ensures: |ret| ret.contains(&position)
            == (matches!(*content, DeclarationContent::Axiom { .. } | DeclarationContent::LiteralIdentity { .. }) || matches!(admission, Admission::Unchecked))
            && ret.iter().all(|&ancestor| ancestor == position ||
                (ancestor < position && self.entries.peek(usize::from(ancestor)).is_some_and(|entry|
                    matches!(entry.admission(), Admission::Unchecked)
                        || matches!(*entry.declaration().content(), DeclarationContent::Axiom { .. } | DeclarationContent::LiteralIdentity { .. }))))
    )]
    fn transitive_rest(
        &self,
        content: &DeclarationContent,
        laws: &[ConstantIndex],
        position: ConstantIndex,
        admission: Admission,
    ) -> BTreeSet<ConstantIndex>
    {
        let mut direct = audited_type_constants(&self.arena, content.declared_id());
        if let DeclarationContent::Data {
            ref parameters,
            ref constructors,
            ..
        } = *(content)
        {
            for root in parameters.iter().chain(constructors.iter().flatten()) {
                direct.append(&mut audited_type_constants(&self.arena, *root));
            }
        }
        if let DeclarationContent::AbstractType { representation, .. } = *content {
            direct.append(&mut audited_type_constants(&self.arena, representation));
        }
        if let DeclarationContent::Def { body, .. } = *content {
            direct.append(&mut collect_reachable(
                &self.arena,
                AnyNode::Value(body),
                CodeEdges::Follow,
            ));
        }
        // A fold rests on every law it names, as a body rests on every
        // constant it names.
        direct.extend(laws.iter().copied());
        let mut rested = BTreeSet::new();
        for referenced in direct {
            if let Some(entry) = self.entries.get(usize::from(referenced)) {
                for &ancestor in entry.rested_on() {
                    let _fresh = rested.insert(ancestor);
                }
            }
        }
        let audited = matches!(
            *content,
            DeclarationContent::Axiom { .. } | DeclarationContent::LiteralIdentity { .. }
        );
        if audited || matches!(admission, Admission::Unchecked) {
            let _fresh = rested.insert(position);
        }
        rested
    }

    /// How a memo key names a reference to `declaration`, about to be
    /// admitted alone at the rank `rank`.
    ///
    /// # Specification
    /// - requires: the content of `declaration` lives in its arena.
    /// - ensures: its declared type and body, ordered by how many entries
    ///   ranked below `rank` and named so carry the same type and body, when it
    ///   is a plain definition — monomorphic, carrying no laws, relations,
    ///   operation rules, stages, presentation or sealing provenance, and
    ///   admitted while no atom's minting admission is open; its position
    ///   otherwise.
    /// - provides: names injective on the environment's positions, so a key
    ///   built through them answers as one built through positions does. A
    ///   checked definition admitted alone names only constants ranked below
    ///   it, so reading references by content descends in rank order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain definition reads alike under either admission
    ///   order, an axiom keeps its position, and definitions of one type and
    ///   body keep a name each.
    /// - witness: `environment::encoding_tests::a_definition_reference_reads_alike_in_either_admission_order`
    /// - witness: `environment::encoding_tests::an_axiom_reference_keeps_its_position`
    /// - witness: `environment::encoding_tests::each_twin_of_one_content_ranks_past_the_latest_3686`
    #[spec(ensures: |ret| match ret {
        ConstantName::Definition { declared, body, .. } => self.manifest.is_empty()
            && *declaration.content() == DeclarationContent::Def { declared, body },
        ConstantName::Position => true,
        ConstantName::Admitted { .. } | ConstantName::Unadmitted => false,
    })]
    fn definition_name(
        &mut self,
        declaration: &Declaration,
        rank: SourceRank,
    ) -> ConstantName
    {
        let DeclarationContent::Def { declared, body } = *declaration.content()
        else {
            return ConstantName::Position;
        };
        let plain = self.manifest.is_empty()
            && *declaration.levels() == LevelSignature::monomorphic()
            && declaration.laws().is_empty()
            && declaration.related().is_empty()
            && declaration.provenance().is_empty()
            && declaration.operation_rules().rules().is_empty()
            && *declaration.stages() == gandr_kernel_term::StageSignature::UNQUANTIFIED
            && declaration.presentation().rules().is_empty()
            && declaration.presentation().cells().is_none();
        if plain {
            crate::encoding::name_definition(
                self.names.session_mut().table_mut(),
                &self.arena,
                (
                    &self.entries,
                    ConstantIndex::from(usize::from(self.entries.len())),
                    rank,
                ),
                declared,
                body,
            )
        }
        else {
            ConstantName::Position
        }
    }
}

/// How a released check answers.
///
/// # Specification
/// trivial.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per released check, moved once to its thread and back; boxing the scope would allocate at every release to shrink the rare recall"
)]
enum Way
{
    /// A verdict that a trusted record holds under the declaration's key.
    Recalled(check::Accessibility),
    /// The check's own scope, and what its judgement reads beside it.
    Checking(Scope, Judged),
}

/// The content key of one unit, computed in place, with the shape that gives
/// each member's content key from it.
#[derive(Clone, Copy, Debug)]
struct UnitKey
{
    /// The unit's content key, counted among the generative contents ranked
    /// below it when a member is generative.
    key: crate::verdict::EntryContentKey,
    /// Whether the unit is one declaration or a block.
    shape: UnitShape,
    /// The unit's content key before the count when a member is generative:
    /// the row the generative index holds for it.
    generative: Option<crate::verdict::EntryContentKey>,
}

impl UnitKey
{
    /// The content key of the member at `offset` in the unit.
    ///
    /// # Specification
    /// trivial.
    fn member(
        self,
        offset: crate::verdict::KeyedCount,
    ) -> crate::verdict::EntryContentKey
    {
        match self.shape {
            UnitShape::Lone => self.key,
            UnitShape::Block => self.key.member(offset),
        }
    }
}

/// The content keys that an environment computes on demand
/// ([`Environment::demanded_key`]), kept so that a later demand reads them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
pub struct DemandedKeys
{
    /// The content key of each constant computed so far.
    keys: BTreeMap<
        ConstantIndex,
        Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    >,
    /// The content key of each unit computed so far, before the count of its
    /// generative twins, by the position of its first member.
    raw: BTreeMap<
        ConstantIndex,
        Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    >,
    /// The digest of the segments of each unit that a search for twins read,
    /// by the position of its first member.
    images: BTreeMap<
        ConstantIndex,
        Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    >,
}

impl DemandedKeys
{
    /// Keep `raw` as the key of the unit from `first` to `end` before its
    /// count, and `key` as its own, each member's key from it as `shape`
    /// states.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        (first, end, shape): (ConstantIndex, ConstantIndex, UnitShape),
        (raw, key): (
            Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
            Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
        ),
    )
    {
        let _previous = self.raw.insert(first, raw);
        for (offset, member) in (usize::from(first) .. usize::from(end)).enumerate() {
            let held = match (key, shape) {
                (Maybe::Present(key), UnitShape::Block) => {
                    Maybe::Present(key.member(crate::verdict::KeyedCount::from(offset)))
                },
                (key, UnitShape::Lone | UnitShape::Block) => key,
            };
            let _previous = self.keys.insert(ConstantIndex::from(member), held);
        }
    }
}

/// Whether another constant shares the content key of a constant that a
/// table names by that key ([`Environment::demanded_twin`]).
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Twin
{
    /// No other constant of its kind holds its key.
    Alone,
    /// Another constant of its kind holds its key, so a table that names by
    /// key names the two alike.
    Twinned,
}

/// How a table that names by key counts the twins of a unit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Twinning
{
    /// A member is generative, so its key counts the generative twins ranked
    /// below it, and two twins take two keys.
    Counted,
    /// No member is generative, and its admission named it by its position,
    /// so twins take one key and one name.
    Shared,
    /// No member is generative, and its admission named it by its content.
    Named,
}

/// How a keep in place answers for a unit's check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Lookup
{
    /// The held keys answer: the watermark covers each member, and each
    /// member holds a key under a policy that keys.
    Answers,
    /// The kernel computes each key again.
    Checks,
}

/// What the committer alone reads and writes beside the entries: the
/// committer's own part of the log. An environment holds it outside the
/// `Arc` of [`EntryLog`](crate::env::EntryLog), and no view holds it, so a
/// check has no path to it. A commit while a view lives copies the view's part
/// alone.
#[derive(Clone, Debug, Default)]
struct CommitLog
{
    /// The entries that name each position: the reverse of each entry's
    /// direct references.
    dependents: crate::dependents::Dependents,
    /// The positions of the generative admissions, by their content key:
    /// the earlier ones with one content are what a new one's key counts.
    generative: ChunkedMap<crate::verdict::EntryContentKey, Vec<ConstantIndex>>,
    /// The position of the entry that holds each rank.
    ranked: ChunkedMap<SourceRank, ConstantIndex>,
    /// Whether each live entry's place in rank order is its position.
    order: Order,
    /// The rank the next admission staged with no rank takes, while a
    /// readmission ranks its crossings at their places in the edited source;
    /// none for the rank past every live entry.
    next: Option<SourceRank>,
    /// How many entries a readmission retired since the indexes last dropped
    /// the rows of the retired entries.
    retired: usize,
    /// The rank through which each live entry's held key answers for the
    /// environment as it stands: each live entry ranked at or below it reads
    /// what it read when the kernel last checked its key. Each commit, retire,
    /// rank rewrite, move and change of the manifest lowers it, and a check of
    /// the next key above it raises it. None while no entry is known to hold.
    keyed_through: Option<SourceRank>,
}

impl CommitLog
{
    /// The position of the live entry that holds `rank`, if one holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn ranked(
        &self,
        rank: SourceRank,
    ) -> Option<ConstantIndex>
    {
        self.ranked.get(&rank).copied()
    }

    /// The positions of the live entries, in rank order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn in_rank_order(&self) -> impl Iterator<Item = ConstantIndex> + '_
    {
        self.ranked.values().copied()
    }

    /// The positions of the live entries ranked at or above `floor`, in rank
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn ranked_from(
        &self,
        floor: SourceRank,
    ) -> impl Iterator<Item = ConstantIndex> + '_
    {
        self.ranked.range(floor ..).map(|(_, &position)| position)
    }

    /// The rank past every rank a live entry holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn past_ranks(&self) -> SourceRank
    {
        self.ranked.last_key_value().map_or_else(
            || SourceRank::from(0_usize),
            |(&rank, _)| SourceRank::from(usize::from(rank).saturating_add(1)),
        )
    }

    /// The rank past every rank that a live entry below `position` holds:
    /// the rank that the serial run gives a declaration staged with no rank
    /// at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn past_below(
        &self,
        position: ConstantIndex,
    ) -> SourceRank
    {
        // economy: the walk from the top passes only the entries at or past
        // `position`, which are the commits past the cursor, so it passes at
        // most the releases in flight (gandr #3476).
        self.ranked
            .iter()
            .rev()
            .find(|&(_, &held)| held < position)
            .map_or_else(
                || SourceRank::from(0_usize),
                |(&rank, _)| SourceRank::from(usize::from(rank).saturating_add(1)),
            )
    }

    /// The next rank, while a readmission sets one, for the admissions staged
    /// with no rank that take `positions`, each one rank past the one before:
    /// the next rank then moves past them all.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn placed(
        commits: &mut alloc::sync::Arc<Self>,
        positions: core::ops::Range<ConstantIndex>,
    ) -> Maybe<SourceRank, next_rank::Absent>
    {
        let Some(next) = commits.next
        else {
            return Maybe::Absent(next_rank::Absent::Unset);
        };
        let width = usize::from(positions.end).saturating_sub(usize::from(positions.start));
        alloc::sync::Arc::make_mut(commits).next =
            Some(SourceRank::from(usize::from(next).saturating_add(width)));
        Maybe::Present(next)
    }

    /// The rank of the first of the admissions staged with no rank that take
    /// `positions`: the next rank ([`Self::placed`]), or the rank past every
    /// live entry when no next rank is set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn unranked(
        commits: &mut alloc::sync::Arc<Self>,
        positions: core::ops::Range<ConstantIndex>,
    ) -> SourceRank
    {
        match Self::placed(commits, positions) {
            Maybe::Present(rank) => rank,
            Maybe::Absent(_) => commits.past_ranks(),
        }
    }

    /// The place of each live position in rank order, among `length` slots:
    /// absent while each live position is its own place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn places(
        &self,
        length: gandr_kernel_term::ArenaLength,
    ) -> Maybe<gandr_kernel_term::Places, places::Absent>
    {
        match self.order {
            Order::Ranked => Maybe::Present(gandr_kernel_term::Places::new(
                self.ranked.values().copied(),
                ConstantIndex::from(length),
            )),
            Order::Positional => Maybe::Absent(places::Absent::InOrder),
        }
    }

    /// How many generative admissions of `entries` ranked below `below` hold
    /// the content key `content`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generative_count(
        &self,
        entries: &Entries,
        content: crate::verdict::EntryContentKey,
        below: SourceRank,
    ) -> crate::verdict::KeyedCount
    {
        crate::verdict::KeyedCount::from(self.generative.get(&content).map_or(0, |positions| {
            positions
                .iter()
                .filter(|&&position| entries.rank_of(position).is_some_and(|rank| rank < below))
                .count()
        }))
    }

    /// Note the generative admission at `position`, whose content key is
    /// `content`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generative(
        &mut self,
        content: crate::verdict::EntryContentKey,
        position: ConstantIndex,
    )
    {
        self.generative
            .update_or_default(content, |positions| positions.push(position));
    }

    /// Take the rows of the entry admitted at `position` and `rank`, which
    /// names `references`: its rank, then its fold.
    ///
    /// # Specification
    /// - requires: `position` is the next position, and no live entry holds
    ///   `rank`.
    /// - ensures: as [`Self::hold`] and then [`Self::fold`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   change, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Environment::add_decl`].
    /// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
    fn admit(
        &mut self,
        (position, rank): (ConstantIndex, SourceRank),
        references: &[ConstantIndex],
    )
    {
        self.hold((position, rank));
        self.fold((position, rank), references);
    }

    /// Hold `rank` at `position`, for the entry committed there. Its key
    /// reads the environment as it stands, so it holds; each live entry
    /// ranked above it may read it, so their keys may not.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        (position, rank): (ConstantIndex, SourceRank),
    )
    {
        let _previous = self.ranked.insert(rank, position);
        if self
            .ranked
            .range((
                core::ops::Bound::Excluded(rank),
                core::ops::Bound::Unbounded,
            ))
            .next()
            .is_some()
        {
            self.stale_above(rank);
        }
        self.keyed(rank);
    }

    /// Hold `serial` at `position` in place of `predicted`, which the entry
    /// committed there held: as [`Self::hold`] holds the rank of a commit, so
    /// each live entry ranked above it may read it.
    ///
    /// # Specification
    /// trivial.
    fn reheld(
        &mut self,
        (position, predicted): (ConstantIndex, SourceRank),
        serial: SourceRank,
    )
    {
        if self.ranked.get(&predicted) == Some(&position) {
            let _freed = self.ranked.remove(&predicted);
        }
        self.hold((position, serial));
    }

    /// Mark the key of each live entry ranked above `rank` as one that may
    /// read otherwise.
    ///
    /// # Specification
    /// trivial.
    fn stale_above(
        &mut self,
        rank: SourceRank,
    )
    {
        if self.keyed_through.is_some_and(|held| held > rank) {
            self.keyed_through = Some(rank);
        }
    }

    /// Mark the key of each live entry ranked at or above `rank` as one that
    /// may read otherwise.
    ///
    /// # Specification
    /// trivial.
    fn stale_from(
        &mut self,
        rank: SourceRank,
    )
    {
        if self.keyed_through.is_some_and(|held| held >= rank) {
            self.keyed_through = self
                .ranked
                .range(.. rank)
                .next_back()
                .map(|(&below, _)| below);
        }
    }

    /// Mark the key of each live entry as one that may read otherwise: the
    /// manifest, which each key reads whole, changed.
    ///
    /// # Specification
    /// trivial.
    fn stale_all(&mut self)
    {
        self.keyed_through = None;
    }

    /// The live entry ranked next above the watermark: the next one whose key
    /// the kernel checks, with its rank.
    ///
    /// # Specification
    /// trivial.
    fn next_stale(&self) -> Option<(SourceRank, ConstantIndex)>
    {
        self.keyed_through
            .map_or_else(
                || self.ranked.iter().next(),
                |held| {
                    self.ranked
                        .range((
                            core::ops::Bound::Excluded(held),
                            core::ops::Bound::Unbounded,
                        ))
                        .next()
                },
            )
            .map(|(&rank, &position)| (rank, position))
    }

    /// Raise the watermark to `rank` when the entry there is the next one
    /// above it and its key holds.
    ///
    /// # Specification
    /// trivial.
    fn keyed(
        &mut self,
        rank: SourceRank,
    )
    {
        if self.next_stale().is_some_and(|(next, _)| next == rank) {
            self.keyed_through = Some(rank);
        }
    }

    /// Fold the entry at `position` and `rank`, which names `references`,
    /// once every slot before it is folded: its rows in the reverse index,
    /// and the order.
    ///
    /// # Specification
    /// - requires: every slot before `position` is folded, and the rank index
    ///   holds `rank` at `position`.
    /// - ensures: the reverse index holds a row for each of `references`; the
    ///   order is ranked once `rank` stands below the rank of a live entry
    ///   before `position`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   change, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold that reads a later commit's rank ranks an
    ///   order that the serial run keeps positional.
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    fn fold(
        &mut self,
        (position, rank): (ConstantIndex, SourceRank),
        references: &[ConstantIndex],
    )
    {
        // A commit past the cursor holds its rank before the fold reads this
        // entry, so the walk passes each later position. Those are the
        // commits in flight, and no other.
        if self.order == Order::Positional
            && self
                .ranked
                .iter()
                .rev()
                .find(|&(_, &held)| held < position)
                .is_some_and(|(&last, _)| last > rank)
        {
            self.order = Order::Ranked;
        }
        self.dependents.admit(position, references);
    }

    /// Take the vacancy at `position`: a row of no reference, and the order
    /// ranked from now on.
    ///
    /// # Specification
    /// trivial.
    fn vacate(
        &mut self,
        position: ConstantIndex,
    )
    {
        self.order = Order::Ranked;
        self.dependents.admit(position, &[]);
    }

    /// Free `rank`, which the entry retired at `position` held.
    ///
    /// # Specification
    /// trivial.
    fn retire(
        &mut self,
        (position, rank): (ConstantIndex, SourceRank),
    )
    {
        self.order = Order::Ranked;
        self.retired = self.retired.saturating_add(1);
        if self.ranked.get(&rank) == Some(&position) {
            let _freed = self.ranked.remove(&rank);
        }
        self.stale_above(rank);
    }

    /// Drop the rows of the retired entries from the reverse index and the
    /// generative index, once the entries retired since the last sweep reach
    /// half the live ones. A sweep reads every row, so the retired entries
    /// pay for it, and each retire costs a share that the live rows bound.
    ///
    /// A live entry that names a retired one is retired before the next
    /// reach: a readmission refuses its keep in place. So no reach passes
    /// through a dropped row.
    ///
    /// # Specification
    /// trivial.
    fn sweep(
        &mut self,
        entries: &Entries,
    )
    {
        if self.retired == 0 || self.retired.saturating_mul(2) < usize::from(self.ranked.len()) {
            return;
        }
        self.retired = 0;
        let live = |position: ConstantIndex| entries.live(position).is_some();
        self.dependents.retain(live);
        self.generative.retain_items(|&position| live(position));
    }

    /// Hold each rank of `ranks` at its position, in place of every rank held
    /// at or above `floor` before, among `length` slots: the rank table after
    /// a readmission rewrites the rank of each live entry past the run it
    /// shares. Each rank below `floor` stays.
    ///
    /// # Specification
    /// - requires: `ranks` names each live entry ranked at or above `floor`
    ///   once, each at a rank at or above `floor`, and no two take one rank.
    /// - ensures: the rank index holds each rank below `floor` as before and
    ///   exactly `ranks` from `floor` on; the order is positional exactly when
    ///   the ranks ascend with the positions over every slot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Environment::rerank`].
    /// - witness: `environment::tests::a_reranked_environment_reads_as_a_fresh_admission_6846`
    /// - witness: `environment::tests::a_rank_rewrite_above_a_floor_keeps_each_rank_below_it_7235`
    #[spec(ensures: usize::from(self.ranked.len()) >= ranks.len()
        && ranks.iter().all(|(&position, &rank)| self.ranked.get(&rank) == Some(&position)))]
    fn rerank(
        &mut self,
        (floor, ranks): (SourceRank, &BTreeMap<ConstantIndex, SourceRank>),
        length: gandr_kernel_term::ArenaLength,
    )
    {
        let before = self.ranked.split_off(&floor);
        for (&position, &rank) in ranks {
            let _fresh = self.ranked.insert(rank, position);
        }
        // The keys below the watermark hold through the longest run of
        // entries that keeps its order, from the lowest rank on. The entries
        // below the floor keep theirs.
        if let Some(held) = self.keyed_through
            && held >= floor
        {
            let mut keyed_through = self
                .ranked
                .range(.. floor)
                .next_back()
                .map(|(&rank, _)| rank);
            for ((_, &was), (&rank, &now)) in
                before.range(..= held).zip(self.ranked.range(floor ..))
            {
                if was != now {
                    break;
                }
                keyed_through = Some(rank);
            }
            self.keyed_through = keyed_through;
        }
        self.order = self.order_over(length);
    }

    /// Hold `to` at `position` in place of `from`, and set the next rank one
    /// past `to`, among `length` slots: the rank table after a crossing takes
    /// a kept seed to the next rank, just below itself.
    ///
    /// # Specification
    /// - requires: `position` holds `from`, and no live entry holds `to`.
    /// - ensures: the rank index holds `to` at `position` and every other rank
    ///   as before; the next rank is one past `to`; the order is positional
    ///   exactly when the ranks ascend with the positions over every slot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Environment::take_next_rank`].
    /// - witness: `environment::tests::a_seed_takes_the_next_rank_below_its_first_reader_7196`
    #[spec(ensures: self.ranked.get(&to) == Some(&position)
        && self.next == Some(SourceRank::from(usize::from(to).saturating_add(1))))]
    fn moved(
        &mut self,
        (position, from): (ConstantIndex, SourceRank),
        to: SourceRank,
        length: gandr_kernel_term::ArenaLength,
    )
    {
        let _from = self.ranked.remove(&from);
        let _to = self.ranked.insert(to, position);
        self.next = Some(SourceRank::from(usize::from(to).saturating_add(1)));
        self.order = self.order_over(length);
        self.stale_from(from.min(to));
    }

    /// The order of the rank index among `length` slots: positional exactly
    /// when it ranks each slot, and the ranks ascend with the positions.
    ///
    /// # Specification
    /// trivial.
    fn order_over(
        &self,
        length: gandr_kernel_term::ArenaLength,
    ) -> Order
    {
        let positional = usize::from(self.ranked.len()) == usize::from(length)
            && self
                .ranked
                .values()
                .enumerate()
                .all(|(at, &position)| usize::from(position) == at);
        if positional {
            Order::Positional
        }
        else {
            Order::Ranked
        }
    }

    /// Keep the rows of the first `length` slots of `entries`, which still
    /// hold every slot.
    ///
    /// # Specification
    /// - requires: `entries` holds the slots whose rows these tables hold.
    /// - ensures: the tables as they were when the first `length` slots were
    ///   all.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   change, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block refused after one member is admitted leaves
    ///   the rows it found.
    /// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
    fn truncate(
        &mut self,
        entries: &Entries,
        length: gandr_kernel_term::ArenaLength,
    )
    {
        let first = ConstantIndex::from(length);
        // The reverse index drops the rows of the last entry first.
        for at in (usize::from(length) .. usize::from(entries.len())).rev() {
            if let Some(entry) = entries.live(ConstantIndex::from(at)) {
                self.dependents.forget(entry.references());
            }
        }
        self.dependents.truncate(first);
        self.generative.retain_items(|&position| position < first);
        let least = self
            .ranked
            .iter()
            .find(|&(_, &position)| position >= first)
            .map(|(&rank, _)| rank);
        self.ranked.retain(|_, &position| position < first);
        if let Some(least) = least {
            self.stale_from(least);
        }
    }

    /// The reach of an edit to the entries of `entries` at `edited`, as
    /// [`Environment::reach`] states it.
    ///
    /// # Specification
    /// trivial.
    fn reach<Edited>(
        &self,
        entries: &Entries,
        edited: Edited,
    ) -> Box<[ConstantIndex]>
    where
        Edited: IntoIterator<Item = ConstantIndex>,
    {
        let Some(log) = entries.log()
        else {
            return Box::default();
        };
        let words = |position: ConstantIndex| {
            let entry = log.family.get(usize::from(position))?.admitted()?;
            let sort = entry.declaration().presentation().cells()?.sort();
            let mut over = log.presentations.over(sort);
            over.any(|words| words == position).then_some(sort)
        };
        let reached = crate::dependents::reach(&self.dependents, words, log.family.len(), edited);
        // A retired entry keeps its rows in the reverse index until a sweep
        // drops them; the reach holds the live entries alone.
        if reached
            .iter()
            .all(|&position| entries.live(position).is_some())
        {
            return reached;
        }
        reached
            .iter()
            .copied()
            .filter(|&position| entries.live(position).is_some())
            .collect()
    }
}

/// What an environment names content through: the session it lends each
/// admission's check and each staging fold, whose content table names the
/// environment's nodes once for the environment's life, and names each plain
/// definition from the names of its two roots.
///
/// A clone starts empty and names the nodes it reads afresh;
/// [`Self::carried`] keeps the names and the kept outcomes.
#[derive(Debug, Default)]
struct Names
{
    /// The session every admission's check is lent, empty while `shared`
    /// holds it.
    session: crate::support::SupportContext,
    /// The session shared with the environments that
    /// [`Environment::handed_on`] made after a freeze, until a check of this
    /// environment takes it ([`Self::session_mut`]).
    shared: Option<alloc::sync::Arc<crate::support::SupportContext>>,
}

impl Clone for Names
{
    /// An empty session: the clone names its nodes afresh.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        Self::default()
    }
}

impl Names
{
    /// The names and the kept outcomes of this session, for an environment
    /// that continues this one's arena: shared when the session is shared,
    /// else copied as
    /// [`SupportContext::carried`](crate::support::SupportContext::carried)
    /// copies them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carried(&self) -> Self
    {
        self.shared.as_ref().map_or_else(
            || Self {
                session: self.session.carried(),
                ..Self::default()
            },
            |shared| Self {
                shared: Some(alloc::sync::Arc::clone(shared)),
                ..Self::default()
            },
        )
    }

    /// Share the session with the environments handed on after this call.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn share(&mut self)
    {
        if self.shared.is_none() {
            self.shared = Some(alloc::sync::Arc::new(core::mem::take(&mut self.session)));
        }
    }

    /// The session, read.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    fn session(&self) -> &crate::support::SupportContext
    {
        self.shared.as_deref().unwrap_or(&self.session)
    }

    /// The session, to lend a check: this environment's own, taken from the
    /// share when no other environment holds it, else copied as
    /// [`SupportContext::carried`](crate::support::SupportContext::carried)
    /// copies it. So only an environment that checks a declaration pays for
    /// the copy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn session_mut(&mut self) -> &mut crate::support::SupportContext
    {
        if let Some(shared) = self.shared.take() {
            // economy: the copy is linear in the table and the kept memo that
            // the share holds, and the first check of each resumed readmission
            // pays it; #4369 bounds the keystroke by the edit.
            self.session =
                alloc::sync::Arc::try_unwrap(shared).unwrap_or_else(|shared| shared.carried());
        }
        &mut self.session
    }
}

/// What a check under a support answers: `checked`, unless the check read the
/// entry at `outside` outside its support. Then the declaration is refused at
/// that position, whatever the check decided.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `checked` when `outside` is `None`, and
///   [`KernelError::OutsideSupport`] at `outside` otherwise.
/// - provides: the refusal that makes a missing edge in a support a refusal,
///   never another verdict.
/// - fails: as `- ensures:`.
/// - panics: none.
///
/// # Errors
/// As `- ensures:`.
///
/// # Adequacy
/// - hypothesis: L3 — a check that reads past its support and fails, and one
///   that reads past it and succeeds, are each refused at the position read.
/// - witness: `environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
#[spec(ensures: |ret| outside.is_none_or(|position| ret.as_ref().err() == Some(&KernelError::OutsideSupport { position })))]
fn supported<T>(
    checked: Result<T, KernelError>,
    outside: Option<ConstantIndex>,
) -> Result<T, KernelError>
{
    outside.map_or(checked, |position| {
        Err(KernelError::OutsideSupport { position })
    })
}

/// Whether `declaration` holds each release after it until its commit: an
/// abstract type, whose seal each later check reads through the manifest; a
/// presented type, whose words each later key over its sort reads; or a role
/// holder, which each later check that reads the role finds.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`crate::releases::Sway::Ordering`] exactly for an abstract type,
///   a declaration with presentation rules, or a declaration with a role.
/// - provides: the one classification of a release that holds its successors.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a released atom whose successors do not hold for its
///   commit reads another manifest than the serial run.
/// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
#[spec(ensures: |ret| (ret == crate::releases::Sway::Ordering)
    == (matches!(*declaration.content(), DeclarationContent::AbstractType { .. })
        || !declaration.presentation().rules().is_empty()
        || matches!(declaration.role(), Maybe::Present(_))))]
fn sway(declaration: &Declaration) -> crate::releases::Sway
{
    let abstract_type = matches!(
        *declaration.content(),
        DeclarationContent::AbstractType { .. }
    );
    if abstract_type
        || !declaration.presentation().rules().is_empty()
        || matches!(declaration.role(), Maybe::Present(_))
    {
        return crate::releases::Sway::Ordering;
    }
    crate::releases::Sway::Free
}

/// The position past the block the declaration at `first` leads: past the
/// furthest position its run of data declarations reaches, when every
/// position up to there is held — data declarations at the head, then
/// definitions — or past `first` alone otherwise.
///
/// # Specification
/// - requires: `declarations` resolve in `arena`.
/// - ensures: one past `first` unless `first` is a data declaration whose
///   fields reach later; then one past the furthest position the data
///   declarations from `first` reach, when `declarations` holds every position
///   before it and each after the leading data run is a definition, and one
///   past `first` when not.
/// - provides: the measurement replay groups a block by, the one the checker
///   groups its schedule by and the bridge admits a block by.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the walk advances one position per step and stops at the measured
///   end, which only rises to a reached position.
/// - measure: `end - position`, bounded by the furthest position named.
///
/// # Adequacy
/// - hypothesis: L3 — a lone family is no block, and a universe naming its
///   decoder leads a block of the two.
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
#[spec(ensures: |ret| ret > first)]
fn block_end(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
    first: ConstantIndex,
) -> ConstantIndex
{
    let start = usize::from(first);
    let lone = start.saturating_add(1);
    let mut end = lone;
    let mut position = start;
    while position < end {
        match declarations
            .get(position)
            .map(|marked| marked.declaration().content())
        {
            Some(&DeclarationContent::Data {
                ref parameters,
                ref constructors,
                ..
            }) => {
                let reached = check::occurrence::reach(
                    arena,
                    ConstantIndex::from(position),
                    parameters,
                    constructors,
                );
                end = end.max(usize::from(reached));
            },
            Some(&DeclarationContent::Def { .. }) => break,
            Some(
                &(DeclarationContent::Axiom { .. }
                | DeclarationContent::LiteralIdentity { .. }
                | DeclarationContent::AbstractType { .. }
                | DeclarationContent::Codata { .. }),
            )
            | None => return ConstantIndex::from(lone),
        }
        position = position.saturating_add(1);
    }
    let definitions = declarations.get(position .. end).unwrap_or_default();
    if end > declarations.len()
        || !definitions.iter().all(|marked| {
            matches!(
                *marked.declaration().content(),
                DeclarationContent::Def { .. }
            )
        })
    {
        return ConstantIndex::from(lone);
    }
    ConstantIndex::from(end)
}

/// The direct references of a mutual block's members: each position any of
/// them names, and each member's own position from `first` on.
///
/// # Specification
/// trivial.
fn block_references(
    arena: &TermArena,
    members: &[Declaration],
    first: ConstantIndex,
) -> Box<[ConstantIndex]>
{
    let mut found = BTreeSet::new();
    for member in members {
        found.extend(references(arena, member).iter().copied());
    }
    let start = usize::from(first);
    found.extend((start .. start.saturating_add(members.len())).map(ConstantIndex::from));
    found.into_iter().collect()
}

/// The constants a declaration's declared type names, **through its codes as
/// well as through its sealed atoms**: the type half of the audit graph.
///
/// # Specification
/// trivial.
#[inline]
fn audited_type_constants(
    arena: &TermArena,
    root: ValueTypeId,
) -> BTreeSet<ConstantIndex>
{
    collect_reachable(arena, AnyNode::ValueType(root), CodeEdges::Follow)
}

/// The transitive audit of a declaration: the axioms and unchecked admissions
/// it rests on, and the kernel primitives it computes by.
///
/// A declaration whose report is empty on its axioms and its unchecked
/// admissions rests on nothing outside the checked kernel. A kernel primitive
/// is inside it: the kernel computes the primitive by its own rule, and the
/// report names it so that a reader sees that trusted surface.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AxiomReport
{
    /// The positions it transitively rests on or computes by, in three runs:
    /// its axioms, then its unchecked admissions, then its literal identity
    /// tests, each run ascending. One list keeps the report small where an
    /// outcome holds it, and takes one allocation.
    positions: Vec<ConstantIndex>,
    /// Where the run of unchecked admissions starts in `positions`.
    unchecked_from: usize,
    /// Where the run of literal identity tests starts in `positions`.
    primitives_from: usize,
}

impl AxiomReport
{
    /// The axioms this declaration transitively rests on, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn axioms(&self) -> &[ConstantIndex]
    {
        self.positions
            .get(.. self.unchecked_from)
            .unwrap_or_default()
    }

    /// The unchecked admissions this declaration transitively rests on,
    /// ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unchecked_admissions(&self) -> &[ConstantIndex]
    {
        self.positions
            .get(self.unchecked_from .. self.primitives_from)
            .unwrap_or_default()
    }

    /// The kernel primitives this declaration transitively computes by,
    /// ascending: the literal identity tests it reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn primitives(&self) -> &[ConstantIndex]
    {
        self.positions
            .get(self.primitives_from ..)
            .unwrap_or_default()
    }
}

/// Why an artifact did not replay: the first declaration the kernel rejected,
/// and the rejection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRefusal
{
    /// The artifact position of the rejected declaration.
    position: ConstantIndex,
    /// What the choke point refused it for.
    error: KernelError,
}

impl ArtifactRefusal
{
    /// The artifact position of the rejected declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> ConstantIndex
    {
        self.position
    }

    /// What the choke point refused it for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn error(&self) -> &KernelError
    {
        &self.error
    }
}

/// An entry's content key and entry key, each absent with its reason.
type EntryKeys = (
    Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
    Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>,
);

/// What the check of one lone declaration hands its commit: the declaration,
/// its place, its keys, its name and its outcome. The check reads its view
/// alone, and the commit alone writes the environment.
struct Lone
{
    /// The declaration staged at its reserved position.
    declaration: Declaration,
    /// Its position and its rank.
    place: (ConstantIndex, SourceRank),
    /// Its unit's content key, and whether its admission is generative.
    content: (
        Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
        bool,
    ),
    /// Its own content key and entry key.
    keys: EntryKeys,
    /// The positions that its content names.
    references: Box<[ConstantIndex]>,
    /// What its check charged.
    census: ExpansionCensus,
    /// The admitted results that its check took.
    took: crate::admitted::AdmittedCount,
    /// Its reading, or the refusal of its check.
    outcome: Result<crate::occurrence::Accessibility, KernelError>,
    /// Whether its check ran, or a recorded verdict recalled it.
    admission: Admission,
    /// The arena's mark past its content, and the mark that a refusal
    /// truncates to.
    marks: (ArenaWatermark, ArenaWatermark),
    /// How a memo key names a reference to it once it is admitted.
    key_name: ConstantName,
}

/// What the commit of one lone declaration needs beside its check: its
/// place, its keys, the positions that its content names, the arena's marks
/// and its name. The committer keeps it while the check runs.
///
/// # Specification
/// - requires: made by [`Environment::release`].
/// - ensures: the place, the keys, the references, the marks and the name that
///   [`Environment::settle`] commits with the check's outcome.
/// - panics: none.
/// - executable: none — the fields are private and set only by
///   [`Environment::release`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Environment::release`].
/// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
#[derive(Debug)]
pub struct Pending
{
    /// Its position and its rank.
    place: (ConstantIndex, SourceRank),
    /// Its unit's content key, and whether its admission is generative.
    content: (
        Maybe<crate::verdict::EntryContentKey, crate::verdict::keyed::Absent>,
        bool,
    ),
    /// Its own content key and entry key.
    keys: EntryKeys,
    /// The positions that its content names.
    references: Box<[ConstantIndex]>,
    /// The arena's mark past its content, and the mark that a refusal
    /// truncates to.
    marks: (ArenaWatermark, ArenaWatermark),
    /// How a memo key names a reference to it once it is admitted.
    key_name: ConstantName,
}

/// What a check owns of the environment: a view of the entries below its
/// rank through its support, a clone of the frozen arena that it mints its
/// intermediates into, and a fork of the session that it names records in.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Scope
{
    /// The entries, read through the check's support below its rank.
    view: Entries,
    /// The clone of the frozen arena.
    arena: TermArena,
    /// The fork of the environment's session.
    session: crate::support::SupportContext,
}

/// What a released check's judgement reads beside its scope: the levels of
/// the declaration, the atoms open at its release, the policy of admitted
/// results and the fork of its last drain.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Judged
{
    /// The declaration's level context.
    levels: LevelContext,
    /// The atoms whose representation the declaration reads.
    manifest: Vec<ConstantIndex>,
    /// Whether the check takes a closed pair's admitted result.
    admitting: crate::admitted::AdmissionPolicy,
    /// The fork that the last drain of the check runs its obligations
    /// through, if any.
    forking: crate::fork::SharedFork,
}

/// What a released check found: its outcome and its tally, with the scope
/// that the committer takes back at the settle.
///
/// # Specification
/// - requires: made by [`Check::run`].
/// - ensures: the declaration, the outcome, the admission, the census and the
///   admitted results taken, as [`Environment::add_decl`] finds them.
/// - panics: none.
/// - executable: none — the fields are private and set only by [`Check::run`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Environment::release`].
/// - witness: `environment::tests::a_released_check_crosses_threads_and_settles_as_an_admission_3476`
#[derive(Debug)]
pub struct Ran
{
    /// The declaration that the check read.
    declaration: Declaration,
    /// Its reading, or the refusal of its check.
    outcome: Result<crate::occurrence::Accessibility, KernelError>,
    /// Whether its check ran, or a recorded verdict recalled it.
    admission: Admission,
    /// What its check charged.
    census: ExpansionCensus,
    /// The admitted results that its check took.
    took: crate::admitted::AdmittedCount,
    /// The scope that the check ran in, absent for a recall.
    scope: Maybe<Scope, ran::Absent>,
}

impl Ran
{
    /// The reading that the check found, or its refusal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The kernel's refusal of the check.
    #[inline]
    pub const fn outcome(&self) -> Result<&crate::check::Accessibility, &KernelError>
    {
        self.outcome.as_ref()
    }
}

quenchant_shape::reason_enum! {
    /// Why a check that ran holds no scope.
    pub mod ran {
        /// The reason the scope is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A recorded verdict answered, so no check ran.
            Recalled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an environment's export writes each position as itself.
    pub mod places {
        /// The reason no entry needs a place.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No entry is retired and the ranks ascend with the positions,
            /// so each live position is its own place.
            InOrder,
        }
    }
}

#[cfg(test)]
mod encoding_tests;
#[cfg(test)]
mod error_tests;
#[cfg(test)]
mod presented_tests;
#[cfg(test)]
mod seal_tests;
#[cfg(test)]
mod theory_rules_tests;
#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::SealExtent;
    use gandr_kernel_term::SealScope;
    use gandr_kernel_term::SourceRank;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;
    use quenchant_shape::shape::Maybe;

    use super::Environment;
    use super::Released;
    use crate::census::ExpansionCensus;
    use crate::env::Admission;
    use crate::env::AdmittedDeclaration;
    use crate::env::CheckedId;
    use crate::env::Entries;
    use crate::env::OutstandingCount;
    use crate::env::Slot;
    use crate::env::StagedDeclaration;
    use crate::error::KernelError;

    /// The constant level `value`.
    ///
    /// # Specification
    /// trivial.
    fn level(value: LevelConstant) -> Level
    {
        Level::constant(value)
    }

    #[test]
    fn a_definition_referencing_a_prior_one_checks()
    {
        let mut environment = Environment::new();
        let first = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let first = environment
            .add_decl(first)
            .expect("a unit definition admits");
        let second = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_constant(first.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            environment.add_decl(second).is_ok(),
            "a reference to an admitted declaration resolves to its declared type"
        );
    }

    #[test]
    fn a_released_check_crosses_threads_and_settles_as_an_admission_3476()
    {
        /// The body of a staged unit definition.
        #[derive(Clone, Copy)]
        enum Body
        {
            /// The unit value: admitted.
            Unit,
            /// A reference to the first entry: admitted.
            First,
            /// A text literal, which no unit inhabits: refused.
            Text,
        }
        /// A unit definition with `body`, staged into `environment`.
        ///
        /// # Specification
        /// trivial.
        fn staged(
            environment: &mut Environment,
            body: Body,
        ) -> StagedDeclaration
        {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = match body {
                Body::Unit => staging.arena().value_unit(),
                Body::First => staging.arena().value_constant(ConstantIndex::from(0_usize)),
                Body::Text => staging
                    .arena()
                    .value_literal(Literal::Text(StringLiteral::new(String::from("x")))),
            };
            staging.def(LevelSignature::monomorphic(), declared, body)
        }
        extern crate std;
        let mut serial = Environment::new();
        let mut released = Environment::new();
        for body in [Body::Unit, Body::First, Body::Text] {
            let serial_staged = staged(&mut serial, body);
            let admitted = serial.add_decl(serial_staged);
            let released_staged = staged(&mut released, body);
            let Released::Running(pending, check) = released
                .release(released_staged)
                .expect("a monomorphic definition releases its check")
            else {
                panic!("a release with no other release outstanding never holds");
            };
            // The check runs on a thread of its own while the environment
            // stays on this one.
            let ran = std::thread::scope(|scope| scope.spawn(move || check.run()).join())
                .expect("the released check runs to its end on its thread");
            assert_eq!(
                released.settle(pending, ran),
                admitted,
                "a released check settles as the check of add_decl answers"
            );
        }
        assert!(
            serial.entries().get(2_usize).is_none() && released.entries().get(2_usize).is_none(),
            "the third declaration is refused and leaves a vacancy"
        );
        assert_eq!(released.entries().len(), serial.entries().len());
        for position in 0_usize .. 2 {
            assert_eq!(
                released
                    .entries()
                    .get(position)
                    .map(super::AdmittedDeclaration::census),
                serial
                    .entries()
                    .get(position)
                    .map(super::AdmittedDeclaration::census),
                "each admitted entry charges the census of the serial check"
            );
        }
    }

    /// The census of a unit definition admitted into `environment`.
    ///
    /// # Specification
    /// trivial.
    fn admit_unit(environment: &mut Environment) -> ExpansionCensus
    {
        let staged = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let admitted = environment
            .add_decl(staged)
            .expect("a unit definition admits");
        let super::Maybe::Present(census) = environment
            .entries()
            .get(usize::from(admitted.position()))
            .expect("an admitted declaration has an entry")
            .census()
        else {
            panic!("a checked admission keeps its census");
        };
        census
    }

    #[test]
    fn a_repeated_declaration_is_answered_by_the_kept_outcomes_of_the_first()
    {
        let mut environment = Environment::new();
        let first = admit_unit(&mut environment);
        let second = admit_unit(&mut environment);
        assert_eq!(
            u64::from(first.kept()),
            0,
            "the first admission has no earlier outcome to stand on"
        );
        assert!(
            u64::from(first.expansions()) > 0,
            "the first admission runs its rules: {first:?}"
        );
        assert!(
            u64::from(second.kept()) > 0,
            "the second admission stands on the first's kept outcomes: {second:?}"
        );
        assert!(
            second.expansions() < first.expansions(),
            "and so runs fewer rules than the first: {first:?} against {second:?}"
        );
        let bypassed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let bypassed = environment
            .add_decl_unchecked(bypassed)
            .expect("no check is released, so the bypass admits");
        assert_eq!(
            environment
                .entries()
                .get(usize::from(bypassed.position()))
                .map(super::AdmittedDeclaration::census),
            Some(super::Maybe::Absent(crate::env::tallied::Absent::Unchecked)),
            "the bypass runs no check, so it answers no tally"
        );
    }

    /// An environment handed on before a freeze copies the session at once.
    /// One handed on after it shares the session: the first to check copies
    /// it, and the last holder takes it whole. Each path stands on the kept
    /// outcomes, and a copy that dropped them, or a share that one check
    /// changed for another, changes a census.
    #[test]
    fn a_handed_on_environment_stands_on_the_kept_outcomes_of_its_run_6468()
    {
        let mut environment = Environment::new();
        let _first = admit_unit(&mut environment);
        let mut copied = environment.handed_on();
        environment.freeze();
        let mut shared = environment.handed_on();
        let mut last = environment.handed_on();
        let continued = admit_unit(&mut environment);
        assert!(
            u64::from(continued.kept()) > 0,
            "the recorded run stands on its own kept outcomes: {continued:?}"
        );
        assert_eq!(
            [
                admit_unit(&mut copied),
                admit_unit(&mut shared),
                admit_unit(&mut last)
            ],
            [continued; 3],
            "each environment handed on charges the goals the recorded run charges"
        );
    }

    #[test]
    fn a_forward_constant_reference_is_unbound()
    {
        let mut environment = Environment::new();
        let forward = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_constant(ConstantIndex::from(3_usize));
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert_eq!(
            Err(KernelError::UnboundConstant {
                index: ConstantIndex::from(3_usize)
            }),
            environment.add_decl(forward).map(|_admitted| ()),
            "the environment is append-only, so a forward reference names nothing"
        );
    }

    /// #6621: a check reads only the entries its source states before the
    /// declaration. A definition ranked below the entry it names reads that
    /// entry as a forward reference, though the entry stands at an earlier
    /// position; ranked above it, the definition admits.
    #[test]
    fn a_reference_to_an_entry_ranked_above_the_declaration_is_unbound_6621()
    {
        let mut environment = Environment::new();
        let earlier = unit_definition(&mut environment, None).ranked(SourceRank::from(5_usize));
        let named = environment
            .add_decl(earlier)
            .expect("a unit definition admits")
            .position();
        let below =
            unit_definition(&mut environment, Some(named)).ranked(SourceRank::from(3_usize));
        assert_eq!(
            environment.add_decl(below).map(|_admitted| ()),
            Err(KernelError::UnboundConstant { index: named }),
            "an entry ranked above the declaration names nothing to it"
        );
        let above =
            unit_definition(&mut environment, Some(named)).ranked(SourceRank::from(7_usize));
        assert!(
            environment.add_decl(above).is_ok(),
            "an entry ranked below the declaration is read"
        );
    }

    /// #6621: two entries never share a rank. A declaration staged at a rank
    /// a live entry holds is refused naming that entry, and so is a block
    /// member ranked at or below the member before it.
    #[test]
    fn a_rank_another_entry_holds_is_refused_6621()
    {
        let rank = SourceRank::from;
        let mut environment = Environment::new();
        let held = unit_definition(&mut environment, None).ranked(rank(4_usize));
        let holder = environment
            .add_decl(held)
            .expect("a unit definition admits")
            .position();
        let again = unit_definition(&mut environment, None).ranked(rank(4_usize));
        assert_eq!(
            environment.add_decl(again).map(|_admitted| ()),
            Err(KernelError::RankTaken {
                rank: rank(4_usize),
                by: holder,
            }),
            "a live entry holds the rank"
        );
        let first = unit_definition(&mut environment, None).ranked(rank(6_usize));
        let second = unit_definition(&mut environment, None).ranked(rank(6_usize));
        assert_eq!(
            environment
                .add_block(vec![first, second])
                .map(|_admitted| ()),
            Err(KernelError::RankTaken {
                rank: rank(6_usize),
                by: ConstantIndex::from(1_usize),
            }),
            "the member before it ranks at the same rank"
        );
        assert_eq!(
            usize::from(environment.entries.len()),
            1,
            "neither refusal admits an entry"
        );
    }

    #[test]
    fn a_definition_after_a_refused_block_is_named_by_its_content()
    {
        let mut environment = Environment::new();
        let admitted = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let refused = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_variable(DeBruijnIndex::from(0_u32));
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            environment.add_block(vec![admitted, refused]).is_err(),
            "a block whose second member reads an unbound variable is refused"
        );
        let definition = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let definition = environment
            .add_decl(definition)
            .expect("a unit definition admits")
            .position();
        assert_eq!(
            ConstantIndex::from(2_usize),
            definition,
            "each member of the refused block leaves a vacancy, so the \
             definition takes the next position"
        );
        let reference = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_constant(definition);
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let _reference = environment
            .add_decl(reference)
            .expect("a reference to the definition admits");
        assert!(
            matches!(
                gandr_kernel_core_base::fixture::constant_name(
                    environment.names.session(),
                    definition
                ),
                Some(crate::encoding::ConstantName::Definition { .. })
            ),
            "the positions of the refused members stay vacant, so the \
             definition after them is named by its content"
        );
    }

    #[test]
    fn a_rejected_declaration_leaves_a_vacancy_at_its_position()
    {
        let mut environment = Environment::new();
        let before = environment.arena().watermark();
        let bad = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging
                .arena()
                .value_literal(Literal::Text(StringLiteral::new(String::from("x"))));
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            environment.add_decl(bad).is_err(),
            "a string literal does not inhabit the unit type"
        );
        assert_eq!(
            before,
            environment.arena().watermark(),
            "and the arena holds exactly what it held before the call"
        );
        assert_eq!(
            usize::from(environment.entries().len()),
            1_usize,
            "with a vacancy at the refused declaration's position"
        );
        assert!(
            environment.entries().get(0_usize).is_none()
                && environment.entries().iter().next().is_none(),
            "which no read sees and no walk of the entries yields"
        );
        let good = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert_eq!(
            Ok(ConstantIndex::from(1_usize)),
            environment.add_decl(good).map(CheckedId::position),
            "the next declaration takes the position after the vacancy"
        );
        assert_eq!(
            environment
                .entries()
                .vacancies()
                .collect::<alloc::vec::Vec<_>>(),
            [ConstantIndex::from(0_usize)],
            "and the vacancies name the refused declaration's position alone"
        );
    }

    #[test]
    fn a_rejection_keeps_a_prior_admission_resolvable()
    {
        let mut environment = Environment::new();
        let good = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let good = environment
            .add_decl(good)
            .expect("a unit definition admits");
        let after_admission = environment.arena().watermark();
        let bad = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(environment.add_decl(bad).is_err(), "unit is not an integer");
        assert_eq!(
            after_admission,
            environment.arena().watermark(),
            "the rollback stops at the admission floor"
        );
        let declared = environment
            .entries()
            .get(usize::from(good.position()))
            .expect("the admitted entry survives")
            .declared_id();
        assert!(
            environment.arena().value_type(declared).is_some(),
            "and the admitted declaration's content still resolves"
        );
    }

    #[test]
    fn a_frozen_environment_admits_as_one_never_frozen()
    {
        let first = |environment: &mut Environment| {
            let staged = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_unit();
                let body = staging.arena().value_unit();
                staging.def(LevelSignature::monomorphic(), declared, body)
            };
            environment
                .add_decl(staged)
                .expect("a unit definition admits")
        };
        let then = |environment: &mut Environment, first: ConstantIndex| {
            let reading = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_unit();
                let body = staging.arena().value_constant(first);
                staging.def(LevelSignature::monomorphic(), declared, body)
            };
            let reading = environment
                .add_decl(reading)
                .map(super::CheckedId::position);
            let bad = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_base(BaseType::Integer);
                let body = staging.arena().value_unit();
                staging.def(LevelSignature::monomorphic(), declared, body)
            };
            (reading, environment.add_decl(bad).map(|_admitted| ()))
        };
        let mut plain = Environment::new();
        let position = first(&mut plain).position();
        let mut frozen = Environment::new();
        assert_eq!(position, first(&mut frozen).position());
        let at_freeze = frozen.arena().watermark();
        frozen.freeze();
        assert_eq!(
            at_freeze,
            frozen.arena().watermark(),
            "a freeze keeps the watermark"
        );
        assert_eq!(plain.arena(), frozen.arena(), "and every node");

        let mut copy = frozen.clone();
        let answers = then(&mut plain, position);
        assert!(answers.0.is_ok(), "a definition reading the first admits");
        assert!(answers.1.is_err(), "unit is not an integer");
        assert_eq!(answers, then(&mut copy, position), "the copy answers alike");
        assert_eq!(plain.arena(), copy.arena(), "and holds the same nodes");
        assert_eq!(plain.entries().len(), copy.entries().len());
        assert_eq!(
            at_freeze,
            frozen.arena().watermark(),
            "the frozen environment never sees the copy's admission"
        );
        assert_eq!(1, frozen.entries().len());
    }

    #[test]
    fn a_rejection_keeps_bypassed_content_resolvable()
    {
        let mut environment = Environment::new();
        let bypassed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let bypassed = environment
            .add_decl_unchecked(bypassed)
            .expect("no check is released, so the bypass admits");
        let bad = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(environment.add_decl(bad).is_err(), "unit is not an integer");
        let declared = environment
            .entries()
            .get(usize::from(bypassed.position()))
            .expect("the bypassed entry survives")
            .declared_id();
        assert!(
            environment.arena().value_type(declared).is_some(),
            "the bypass raised the floor, so a later rejection cannot truncate through it"
        );
    }

    #[test]
    fn an_out_of_order_rejection_keeps_committed_content()
    {
        let mut environment = Environment::new();
        // Stage a declaration, then admit a different one before offering it,
        // so its content-start mark lies below committed content.
        let early = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let committed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let committed = environment
            .add_decl(committed)
            .expect("the second declaration admits");
        let floor = environment.arena().watermark();
        assert!(
            environment.add_decl(early).is_err(),
            "the out-of-order declaration is ill-typed and is refused"
        );
        assert_eq!(
            floor,
            environment.arena().watermark(),
            "the rollback clamps to the admission floor rather than deleting committed content"
        );
        let declared = environment
            .entries()
            .get(usize::from(committed.position()))
            .expect("the committed entry survives")
            .declared_id();
        assert!(
            environment.arena().value_type(declared).is_some(),
            "and the committed declaration's content still resolves"
        );
    }

    #[test]
    fn audit_reports_the_transitive_axiom()
    {
        let mut environment = Environment::new();
        let axiom = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let axiom = environment.add_decl(axiom).expect("an axiom admits");
        let middle = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_constant(axiom.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let middle = environment.add_decl(middle).expect("the middle admits");
        let top = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_constant(middle.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let top = environment.add_decl(top).expect("the top admits");
        assert_eq!(
            &[axiom.position()],
            environment.audit(top).axioms(),
            "a definition on a definition on an axiom rests on that axiom"
        );
    }

    /// A declaration reachable **only through a code** is in the audit graph.
    ///
    /// Both spellings the type plane admits are covered. The definition
    /// spelling names the axiom inside a code in its declared type and
    /// nowhere else; the axiom spelling has a declared type that *is* a
    /// type read off that code. Either one dropping out would make the
    /// report claim the declaration rests on nothing outside the checked
    /// kernel, which is the one thing an empty report is contracted to
    /// mean.
    #[test]
    fn audit_reaches_an_axiom_named_only_inside_a_code()
    {
        let mut environment = Environment::new();
        let zero = level(LevelConstant::from(0));
        let atom = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_universe(GroundSort::Value, zero.clone());
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let atom = environment.add_decl(atom).expect("the code axiom admits");

        // `def d : U (El 0 A -> F (El 0 A)) := thunk (lambda x. return x)`.
        let definition = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            let code = mint.value_constant(atom.position());
            let element = mint.value_type_element(code, zero.clone());
            let returner = mint.comp_type_returner(element);
            let arrow = mint.comp_type_arrow(element, returner);
            let declared = mint.value_type_thunk(arrow);
            let bound = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(bound);
            let lambda = mint.computation_lambda(body);
            let thunk = mint.value_thunk(lambda);
            staging.def(LevelSignature::monomorphic(), declared, thunk)
        };
        let definition = environment
            .add_decl(definition)
            .expect("the code-typed identity admits");
        assert_eq!(
            &[atom.position()],
            environment.audit(definition).axioms(),
            "a definition whose type names an axiom only inside a code rests on that axiom"
        );

        // `axiom b : El 0 A`, where the declared type *is* the code-read type.
        let dependent_axiom = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            let code = mint.value_constant(atom.position());
            let declared = mint.value_type_element(code, zero);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let dependent_axiom = environment
            .add_decl(dependent_axiom)
            .expect("the code-typed axiom admits");
        assert_eq!(
            &[atom.position(), dependent_axiom.position()],
            environment.audit(dependent_axiom).axioms(),
            "and an axiom whose type is read off a code rests on the code's axiom as well as on \
             itself"
        );
    }

    /// The provenance set stays sealed-atom-only, so following a code in the
    /// audit graph cannot loosen the sealing gate.
    ///
    /// A provenance entry naming the definition a code mentions is refused: the
    /// claim is about atoms a projection rebound, and no projection rebound a
    /// definition.
    #[test]
    fn sealing_provenance_does_not_follow_codes()
    {
        let mut environment = Environment::new();
        let zero = level(LevelConstant::from(0));
        let atom = {
            let mut staging = environment.stage();
            let declared = staging
                .arena()
                .value_type_universe(GroundSort::Value, zero.clone());
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let atom = environment.add_decl(atom).expect("the code axiom admits");
        let claiming = {
            let mut staging = environment.stage();
            let mint = staging.arena();
            let code = mint.value_constant(atom.position());
            let element = mint.value_type_element(code, zero);
            let returner = mint.comp_type_returner(element);
            let arrow = mint.comp_type_arrow(element, returner);
            let declared = mint.value_type_thunk(arrow);
            let bound = mint.value_variable(DeBruijnIndex::from(0_u32));
            let body = mint.computation_return(bound);
            let lambda = mint.computation_lambda(body);
            let thunk = mint.value_thunk(lambda);
            staging.sealed_def(LevelSignature::monomorphic(), declared, thunk, vec![
                atom.position(),
            ])
        };
        assert!(
            matches!(
                environment.add_decl(claiming),
                Err(KernelError::SealingProvenanceNotProjected { .. })
            ),
            "a provenance entry naming a declaration a code mentions is not a projected atom"
        );
    }

    #[test]
    fn audit_reports_a_transitive_unchecked_admission()
    {
        let mut environment = Environment::new();
        let bypassed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let bypassed = environment
            .add_decl_unchecked(bypassed)
            .expect("no check is released, so the bypass admits");
        let dependent = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_constant(bypassed.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let dependent = environment
            .add_decl(dependent)
            .expect("a reference to bypassed content still type-checks");
        assert_eq!(
            &[bypassed.position()],
            environment.audit(dependent).unchecked_admissions(),
            "the bypass surfaces in every dependent's audit"
        );
    }

    #[test]
    fn a_closed_definition_rests_on_nothing()
    {
        let mut environment = Environment::new();
        let closed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let closed = environment.add_decl(closed).expect("it admits");
        let report = environment.audit(closed);
        assert!(report.axioms().is_empty(), "no axiom");
        assert!(
            report.unchecked_admissions().is_empty(),
            "and no bypass: it rests on nothing outside the checked kernel"
        );
    }

    #[test]
    fn a_type_level_atom_reference_reaches_the_audit()
    {
        let mut environment = Environment::new();
        let atom_kind_axiom = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let axiom = environment.add_decl(atom_kind_axiom).expect("it admits");
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let integer = staging.arena().value_type_base(BaseType::Integer);
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                SealScope::Closed(SealExtent::from(0_usize)),
            )
        };
        let atom = environment.add_decl(atom).expect("an atom admits");
        // A declaration whose *type* names the atom, and whose body names the
        // axiom, rests on the axiom through the term plane.
        let dependent = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_constant(axiom.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let dependent = environment.add_decl(dependent).expect("it admits");
        assert_eq!(
            &[axiom.position()],
            environment.audit(dependent).axioms(),
            "the body's reference reaches the audit"
        );
        assert!(
            environment.audit(atom).axioms().is_empty(),
            "and an atom whose kind names nothing rests on nothing"
        );
    }

    #[test]
    fn an_abandoned_staging_leaves_the_arena_unchanged()
    {
        let mut environment = Environment::new();
        let before = environment.arena().watermark();
        let mut staging = environment.stage();
        let _staged = staging.arena().value_unit();
        staging.discard();
        assert_eq!(
            before,
            environment.arena().watermark(),
            "a discarded staging session rolls its content back"
        );
    }

    /// Stage a well-typed unit definition into `environment`.
    ///
    /// # Specification
    /// - requires: `environment` has no other staging session open.
    /// - ensures: a staged unit definition whose declared type and body are
    ///   both minted into that environment's arena, with its content-start mark
    ///   left outstanding.
    /// - provides: the fixture the staging and rollback cases are written over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fixture's distinct staged regions drive admission
    ///   refusal, abandonment and subsequent successful admission. Predicates
    ///   check its unit roots, starting mark and outstanding registration.
    /// - witness: `environment::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `environment::tests::abandoning_a_staged_declaration_releases_its_claim`
    #[spec(captures: [entry_mark = environment.arena().watermark(), entry_len = environment.outstanding.marks.len()],
    ensures: |ret| ret.content_start() == entry_mark
        && environment.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
        && environment.outstanding.marks.last() == Some(&entry_mark)
        && match *ret.declaration().content() {
            super::DeclarationContent::Def { declared, body } =>
                matches!(environment.arena().value_type(declared), Some(gandr_kernel_term::ValueType::Product(parts)) if parts.is_empty())
                && matches!(environment.arena().value(body).and_then(gandr_kernel_term::Value::components), Some(&[])),
            super::DeclarationContent::Data { .. } | super::DeclarationContent::Codata { .. } | super::DeclarationContent::Axiom { .. } | super::DeclarationContent::LiteralIdentity { .. } | super::DeclarationContent::AbstractType { .. } => false,
        })]
    fn stage_unit(environment: &mut Environment) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    }

    #[test]
    fn abandonment_preserves_the_admission_floor()
    {
        let mut environment = Environment::new();
        let earlier = stage_unit(&mut environment);
        let later = stage_unit(&mut environment);
        let admitted = environment
            .add_decl(later)
            .expect("the later declaration admits");
        let declared = environment
            .entries()
            .get(usize::from(admitted.position()))
            .expect("the admitted declaration exists")
            .declared_id();
        let before = environment.arena().watermark();
        environment.abandon(earlier);
        assert_eq!(before, environment.arena().watermark());
        assert!(matches!(
            environment.arena().value_type(declared),
            Some(gandr_kernel_term::ValueType::Product(parts)) if parts.is_empty()
        ));
        let report = environment.audit(admitted);
        assert!(report.axioms().is_empty(), "{:?}", report.axioms());
        assert!(
            report.unchecked_admissions().is_empty(),
            "{:?}",
            report.unchecked_admissions()
        );
    }

    /// The blocker's scenario: a rejection may not truncate through content a
    /// producer still holds, and the refusal is what stops it.
    #[test]
    fn outstanding_later_staged_content_refuses_admission()
    {
        let mut environment = Environment::new();
        // The first declaration is ill-typed, so admitting it would reject and
        // roll back — through the second's content, were it allowed to run.
        let first = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let second = stage_unit(&mut environment);
        let held = second.declaration().declared_id();
        let before = environment.arena().watermark();

        let refused = environment.add_decl(first).map(|_admitted| ());

        // The destruction check comes first, because it is what the guard
        // exists to prevent: without it the rollback truncates to the first
        // declaration's content-start and this root stops resolving.
        assert!(
            environment.arena().value_type(held).is_some(),
            "the later staging's content is untouched, which is the whole point of the refusal"
        );
        assert_eq!(
            before,
            environment.arena().watermark(),
            "and nothing at all was truncated"
        );
        assert_eq!(
            Err(KernelError::OutstandingStagedContent {
                above: OutstandingCount::from(1_usize)
            }),
            refused,
            "a declaration with a later staging outstanding above it is refused, naming how many"
        );
        assert_eq!(
            environment.entries().len(),
            0_usize,
            "with nothing appended"
        );

        // The producer's remedy: resolve the later staging, then retry. The
        // retry now runs the check, and refuses on the declaration's own
        // merits.
        let second = environment
            .add_decl(second)
            .expect("the later declaration admits on its own");
        let declared = environment
            .entries()
            .get(usize::from(second.position()))
            .expect("it was appended")
            .declared_id();
        assert!(
            environment.arena().value_type(declared).is_some(),
            "its content was never touched"
        );
    }

    #[test]
    fn an_in_order_producer_is_never_refused()
    {
        // The other direction: stage, admit, stage, admit. Nothing is ever
        // outstanding above the declaration being offered, so the guard never
        // fires and the clamp changes nothing.
        let mut environment = Environment::new();
        for _round in 0 .. 3_u32 {
            let staged = stage_unit(&mut environment);
            assert!(
                environment.add_decl(staged).is_ok(),
                "an in-order producer is admitted, round after round"
            );
        }
        assert_eq!(3, environment.entries().len(), "all three admitted");

        // And an in-order producer whose declaration is refused on its own
        // merits still sees the ordinary rollback rather than the guard.
        let before = environment.arena().watermark();
        let bad = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            matches!(
                environment.add_decl(bad),
                Err(KernelError::ValueShapeMismatch { .. })
            ),
            "the refusal is the type error, not the outstanding-content guard"
        );
        assert_eq!(
            before,
            environment.arena().watermark(),
            "and the arena is exactly what it was"
        );
    }

    #[test]
    fn an_abandoned_staging_releases_its_claim()
    {
        let mut environment = Environment::new();
        let first = stage_unit(&mut environment);
        let mut staging = environment.stage();
        let _staged = staging.arena().value_unit();
        staging.discard();
        assert!(
            environment.add_decl(first).is_ok(),
            "a discarded session holds no claim, so the earlier declaration admits"
        );
    }

    #[test]
    fn every_finisher_retains_its_claim_until_admission()
    {
        enum Finisher
        {
            Definition,
            SealedDefinition,
            Axiom,
            AbstractType,
        }

        for finisher in [
            Finisher::Definition,
            Finisher::SealedDefinition,
            Finisher::Axiom,
            Finisher::AbstractType,
        ] {
            let mut environment = Environment::new();
            let earlier = stage_unit(&mut environment);
            let later = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_unit();
                let body = staging.arena().value_unit();
                let kind = staging
                    .arena()
                    .value_type_universe(GroundSort::Value, Level::zero());
                match finisher {
                    Finisher::Definition => {
                        staging.def(LevelSignature::monomorphic(), declared, body)
                    },
                    Finisher::SealedDefinition => {
                        staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![])
                    },
                    Finisher::Axiom => staging.axiom(LevelSignature::monomorphic(), declared),
                    Finisher::AbstractType => staging.abstract_type(
                        LevelSignature::monomorphic(),
                        kind,
                        declared,
                        SealScope::Open,
                    ),
                }
            };
            let before = environment.arena().watermark();
            assert_eq!(
                Err(KernelError::OutstandingStagedContent {
                    above: OutstandingCount::from(1_usize)
                }),
                environment.add_decl(earlier),
            );
            assert_eq!(before, environment.arena().watermark());
            assert!(environment.add_decl(later).is_ok());
        }
    }

    #[test]
    fn implicit_staging_drop_releases_its_claim()
    {
        let mut environment = Environment::new();
        let first = stage_unit(&mut environment);
        let before = environment.arena().watermark();
        {
            let mut abandoned = environment.stage();
            let _discarded = abandoned.arena().value_unit();
        }
        assert_eq!(before, environment.arena().watermark());
        assert_eq!(vec![first.content_start()], environment.outstanding.marks);
        assert!(
            environment.add_decl(first).is_ok(),
            "implicit abandonment cannot block an earlier declaration"
        );
    }

    #[test]
    fn abandoning_a_staged_declaration_releases_its_claim()
    {
        let mut environment = Environment::new();
        let first = stage_unit(&mut environment);
        let second = stage_unit(&mut environment);
        let before_abandon = environment.arena().watermark();
        environment.abandon(second);
        assert_ne!(
            before_abandon,
            environment.arena().watermark(),
            "nothing outstanding sits above it, so its content is truncated away"
        );
        assert!(
            environment.add_decl(first).is_ok(),
            "and the earlier declaration is no longer blocked"
        );
    }

    #[test]
    fn abandoning_beneath_outstanding_content_retains_it()
    {
        let mut environment = Environment::new();
        let first = stage_unit(&mut environment);
        let second = stage_unit(&mut environment);
        let before = environment.arena().watermark();
        // Abandoning the *lower* one cannot release its region, because the
        // higher one's content sits above it and a contiguous truncation cannot
        // spare a disjoint region.
        environment.abandon(first);
        assert_eq!(
            before,
            environment.arena().watermark(),
            "the arena is unchanged: the lower region is retained as an orphan"
        );
        assert!(
            environment.add_decl(second).is_ok(),
            "and the outstanding declaration above it still admits"
        );
    }

    /// Stage an abstract type at the value universe of level zero over the
    /// integer, with `scope`.
    ///
    /// # Specification
    /// trivial.
    fn integer_atom(
        environment: &mut Environment,
        scope: SealScope,
    ) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
        let integer = staging.arena().value_type_base(BaseType::Integer);
        staging.abstract_type(LevelSignature::monomorphic(), kind, integer, scope)
    }

    /// Stage `def : declared = 7`, with `declared` the atom at `atom` when
    /// given and the integer otherwise.
    ///
    /// # Specification
    /// trivial.
    fn seven_at(
        environment: &mut Environment,
        atom: Option<ConstantIndex>,
    ) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        let declared = match atom {
            Some(atom) => staging.arena().value_type_abstract(atom),
            None => staging.arena().value_type_base(BaseType::Integer),
        };
        let seven = staging.arena().value_literal(Literal::Integer(
            gandr_kernel_term::IntegerLiteral::new(
                gandr_kernel_term::Sign::NonNegative,
                gandr_kernel_term::Magnitude::from_decimal_text(String::from("7"))
                    .expect("decimal digits"),
            ),
        ));
        staging.def(LevelSignature::monomorphic(), declared, seven)
    }

    #[test]
    fn a_value_of_the_representation_does_not_inhabit_the_atom()
    {
        let mut environment = Environment::new();
        let atom = integer_atom(&mut environment, SealScope::Open);
        let atom = environment.add_decl(atom).expect("an atom admits");
        let inside = seven_at(&mut environment, Some(atom.position()));
        let seed = environment
            .add_decl(inside)
            .expect("inside the minting admission the atom reads as the integer");
        assert_eq!(
            environment.seal(atom),
            Ok(SealExtent::from(1_usize)),
            "the admission closes after its one member"
        );
        let outside = seven_at(&mut environment, Some(atom.position()));
        assert!(
            matches!(
                environment.add_decl(outside),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "after the seal an integer does not inhabit the atom"
        );
        let leak = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_base(BaseType::Integer);
            let body = staging.arena().value_constant(seed.position());
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        assert!(
            matches!(
                environment.add_decl(leak),
                Err(KernelError::ValueTypeMismatch(_))
            ),
            "nor does the member sealed at it read as an integer"
        );
    }

    #[test]
    fn an_atom_seals_once()
    {
        let mut environment = Environment::new();
        let open = integer_atom(&mut environment, SealScope::Open);
        let open = environment.add_decl(open).expect("an open atom admits");
        let closed = integer_atom(
            &mut environment,
            SealScope::Closed(SealExtent::from(1_usize)),
        );
        let closed = environment.add_decl(closed).expect("a closed atom admits");
        let member = seven_at(&mut environment, None);
        let member = environment.add_decl(member).expect("an integer admits");
        assert_eq!(
            environment.seal(closed),
            Err(KernelError::SealNotOpen {
                index: closed.position()
            }),
            "an atom whose own scope closes it is not closed by hand"
        );
        assert_eq!(
            environment.seal(member),
            Err(KernelError::SealNotOpen {
                index: member.position()
            }),
            "a definition has no minting admission"
        );
        assert_eq!(
            environment.seal(open),
            Ok(SealExtent::from(2_usize)),
            "the open atom closes after the two declarations admitted since"
        );
        assert_eq!(
            environment.seal(open),
            Err(KernelError::SealNotOpen {
                index: open.position()
            }),
            "and closes once"
        );
    }

    #[test]
    fn a_seal_keys_its_scope_as_an_admission_of_the_closed_module_7200()
    {
        let mut open = keyed();
        let atom = integer_atom(&mut open, SealScope::Open);
        let atom = open.add_decl(atom).expect("an open atom admits");
        let member = seven_at(&mut open, Some(atom.position()));
        let member = open
            .add_decl(member)
            .expect("a member checks at the representation")
            .position();
        assert!(
            matches!(open.entries().key(member), Maybe::Absent(_)),
            "a member that reads an open atom holds no key"
        );
        let extent = open.seal(atom).expect("the open atom seals");
        let mut closed = keyed();
        let replayed = integer_atom(&mut closed, SealScope::Closed(extent));
        let replayed = closed
            .add_decl(replayed)
            .expect("a closed atom admits")
            .position();
        let inside = seven_at(&mut closed, Some(replayed));
        let inside = closed
            .add_decl(inside)
            .expect("a member inside the closed scope admits")
            .position();
        let sealed = [atom.position(), member].map(|position| open.entries().key(position));
        assert!(
            sealed.iter().all(|key| matches!(key, Maybe::Present(_))),
            "the seal keys its atom and its member: {sealed:?}"
        );
        assert_eq!(
            sealed,
            [replayed, inside].map(|position| closed.entries().key(position)),
            "each key is the one an admission of the closed module gives"
        );
    }

    #[test]
    fn a_sealed_atom_is_not_an_axiom_and_adds_no_obligation()
    {
        let mut environment = Environment::new();
        let atom = integer_atom(&mut environment, SealScope::Open);
        let atom = environment.add_decl(atom).expect("an atom admits");
        let member = seven_at(&mut environment, Some(atom.position()));
        let member = environment.add_decl(member).expect("the member admits");
        let _extent = environment.seal(atom).expect("the atom seals");
        for admitted in [atom, member] {
            let report = environment.audit(admitted);
            assert!(
                report.axioms().is_empty(),
                "neither the atom nor a member checked at its representation is an axiom"
            );
            assert!(
                report.unchecked_admissions().is_empty(),
                "and both crossed the checked choke point"
            );
        }
    }

    #[test]
    fn audit_follows_the_declared_type_to_an_unchecked_atom()
    {
        let mut environment = Environment::new();
        let sealed = integer_atom(
            &mut environment,
            SealScope::Closed(SealExtent::from(0_usize)),
        );
        let sealed = environment
            .add_decl_unchecked(sealed)
            .expect("no check is released, so the bypass admits");
        let axiom = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_abstract(sealed.position());
            staging.axiom(LevelSignature::monomorphic(), declared)
        };
        let axiom = environment
            .add_decl(axiom)
            .expect("an axiom at the atom admits");
        assert_eq!(
            environment.audit(axiom).unchecked_admissions(),
            &[sealed.position()],
            "formation rests on the unchecked atom, so the audit reports it"
        );
    }

    #[test]
    fn a_representation_above_its_kind_is_refused()
    {
        let mut environment = Environment::new();
        let atom = {
            let mut staging = environment.stage();
            let kind = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            let universe = staging
                .arena()
                .value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
            staging.abstract_type(
                LevelSignature::monomorphic(),
                kind,
                universe,
                SealScope::Open,
            )
        };
        assert!(
            matches!(
                environment.add_decl(atom),
                Err(KernelError::UniverseViolation(_))
            ),
            "a universe lives one level above the kind it would be sealed at"
        );
    }

    /// A field type a generated declaration carries.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Field
    {
        /// The value universe at a level.
        Universe(LevelConstant),
        /// The type of the declaration being admitted.
        Own,
        /// A data type in scope, chosen by the draw.
        Earlier(usize),
        /// The unit type.
        Unit,
    }

    /// One generated declaration, admitted alone or as a block's member.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Member
    {
        /// A monomorphic data declaration whose one constructor carries the
        /// fields, at the value universe at the level.
        Data(LevelConstant, Vec<Field>),
        /// A codata declaration whose one observation returns the field's
        /// type, at the computation universe at the level.
        Codata(LevelConstant, Field),
        /// An axiom of the field's type.
        Axiom(Field),
        /// A definition whose body reads an unbound variable. The kernel
        /// refuses it.
        Refused,
    }

    /// Mint `field` in `arena`. The declaration being admitted is at `own`.
    /// The data types in scope are at `data`.
    ///
    /// # Specification
    /// trivial.
    fn form(
        arena: &mut TermArena,
        field: Field,
        own: ConstantIndex,
        data: &[ConstantIndex],
    ) -> gandr_kernel_term::ValueTypeId
    {
        match field {
            Field::Universe(at) => arena.value_type_universe(GroundSort::Value, level(at)),
            Field::Own => arena.value_type_data(own, vec![]),
            Field::Earlier(draw) => {
                match draw.checked_rem(data.len()).and_then(|at| data.get(at)) {
                    Some(&position) => arena.value_type_data(position, vec![]),
                    None => arena.value_type_unit(),
                }
            },
            Field::Unit => arena.value_type_unit(),
        }
    }

    /// Stage `member` in `environment` for admission at `own`. Its fields come
    /// from the data types in scope at `data`.
    ///
    /// # Specification
    /// trivial.
    fn stage_member(
        environment: &mut Environment,
        member: &Member,
        own: ConstantIndex,
        data: &[ConstantIndex],
    ) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        match *member {
            Member::Data(kind, ref fields) => {
                let kind = form(staging.arena(), Field::Universe(kind), own, data);
                let fields = fields
                    .iter()
                    .map(|&field| form(staging.arena(), field, own, data))
                    .collect();
                staging.data(LevelSignature::monomorphic(), vec![], vec![fields], kind)
            },
            Member::Codata(kind, field) => {
                let arena = staging.arena();
                let result = form(arena, field, own, data);
                let returns = arena.comp_type_returner(result);
                let kind = arena.value_type_universe(GroundSort::Computation, level(kind));
                staging.codata(LevelSignature::monomorphic(), vec![], vec![returns], kind)
            },
            Member::Axiom(field) => {
                let declared = form(staging.arena(), field, own, data);
                staging.axiom(LevelSignature::monomorphic(), declared)
            },
            Member::Refused => {
                let declared = staging.arena().value_type_unit();
                let body = staging.arena().value_variable(DeBruijnIndex::from(0_u32));
                staging.def(LevelSignature::monomorphic(), declared, body)
            },
        }
    }

    #[test]
    fn a_refused_data_declaration_s_outcomes_do_not_answer_its_successor()
    {
        let mut environment = Environment::new();
        let position = ConstantIndex::from(0_usize);
        let zero = LevelConstant::from(0_u64);
        let one = LevelConstant::from(1_u64);
        let refused = stage_member(
            &mut environment,
            &Member::Data(zero, vec![Field::Own, Field::Universe(zero)]),
            position,
            &[],
        );
        assert!(
            matches!(
                environment.add_decl(refused),
                Err(KernelError::UniverseViolation(_))
            ),
            "a universe is no field of a type in that universe. The type's own \
             field formed at its level first"
        );
        let one_up = ConstantIndex::from(1_usize);
        let admitted = stage_member(
            &mut environment,
            &Member::Data(one, vec![Field::Own, Field::Universe(zero)]),
            one_up,
            &[],
        );
        assert_eq!(
            Ok(one_up),
            environment.add_decl(admitted).map(CheckedId::position),
            "one level up, the declaration admits past the vacancy of the \
             refused one"
        );
        let successor = stage_member(
            &mut environment,
            &Member::Data(zero, vec![Field::Earlier(0)]),
            ConstantIndex::from(2_usize),
            &[one_up],
        );
        let verdict = environment.add_decl(successor).map(CheckedId::position);
        assert!(
            matches!(verdict, Err(KernelError::UniverseViolation(_))),
            "the type at that position lives one level up. The refused \
             declaration formed it at the bottom, under its own block: \
             {verdict:?}"
        );
    }

    #[test]
    fn a_refused_block_s_outcomes_answer_no_later_family()
    {
        let mut environment = Environment::new();
        let family = ConstantIndex::from(0_usize);
        let bottom = LevelConstant::from(0_u64);
        let observer = Member::Codata(bottom, Field::Earlier(0));
        let block = vec![
            stage_member(&mut environment, &Member::Data(bottom, vec![]), family, &[]),
            stage_member(
                &mut environment,
                &observer,
                ConstantIndex::from(1_usize),
                &[family],
            ),
            stage_member(
                &mut environment,
                &Member::Refused,
                ConstantIndex::from(2_usize),
                &[],
            ),
        ];
        assert_eq!(
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(0_u32)
            }),
            environment.add_block(block).map(|ids| ids.len()),
            "the block refuses at its last member, after its codata member's \
             observation formed at the bottom over the family before it"
        );
        let later = ConstantIndex::from(3_usize);
        let second_family = stage_member(
            &mut environment,
            &Member::Data(LevelConstant::from(1_u64), vec![]),
            later,
            &[],
        );
        assert_eq!(
            Ok(later),
            environment.add_decl(second_family).map(CheckedId::position),
            "a family one level up admits after the vacancy of each member of \
             the refused block"
        );
        let staged = stage_member(
            &mut environment,
            &observer,
            ConstantIndex::from(4_usize),
            &[later],
        );
        let verdict = environment.add_decl(staged).map(CheckedId::position);
        assert!(
            matches!(verdict, Err(KernelError::UniverseViolation(_))),
            "the same observation over the later family returns a type one \
             level up. The refused block's codata member formed one at the \
             bottom over the refused family: {verdict:?}"
        );
    }

    /// One admission of a generated environment.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Generated
    {
        /// A declaration admitted alone.
        Lone(Member),
        /// Declarations admitted together, or refused whole.
        Block(Vec<Member>),
    }

    /// A generated field type. The alphabet is small, so declarations repeat.
    ///
    /// # Specification
    /// trivial.
    fn field() -> impl proptest::strategy::Strategy<Value = Field>
    {
        use proptest::prelude::Just;
        use proptest::strategy::Strategy as _;
        proptest::prop_oneof![
            (0_u64 .. 2).prop_map(|at| Field::Universe(LevelConstant::from(at))),
            Just(Field::Own),
            (0_usize .. 4).prop_map(Field::Earlier),
            Just(Field::Unit),
        ]
    }

    /// A generated declaration.
    ///
    /// # Specification
    /// trivial.
    fn member() -> impl proptest::strategy::Strategy<Value = Member>
    {
        use proptest::prelude::Just;
        use proptest::strategy::Strategy as _;
        proptest::prop_oneof![
            3 => ((0_u64 .. 2), proptest::collection::vec(field(), 0 .. 3))
                .prop_map(|(kind, fields)| Member::Data(LevelConstant::from(kind), fields)),
            1 => ((0_u64 .. 2), field())
                .prop_map(|(kind, field)| Member::Codata(LevelConstant::from(kind), field)),
            1 => field().prop_map(Member::Axiom),
            1 => Just(Member::Refused),
        ]
    }

    /// A generated admission.
    ///
    /// # Specification
    /// trivial.
    fn generated() -> impl proptest::strategy::Strategy<Value = Generated>
    {
        use proptest::strategy::Strategy as _;
        proptest::prop_oneof![
            3 => member().prop_map(Generated::Lone),
            1 => proptest::collection::vec(member(), 1 .. 4).prop_map(Generated::Block),
        ]
    }

    /// Admit `generated` in `environment`, its members ranked from `rank` on
    /// when a rank is given and at their positions otherwise. A member's
    /// fields come from the data types at `data` and from the block's data
    /// members before it.
    ///
    /// # Specification
    /// trivial.
    fn admit_generated(
        environment: &mut Environment,
        generated: &Generated,
        data: &[ConstantIndex],
        rank: Option<SourceRank>,
    ) -> Result<Vec<ConstantIndex>, KernelError>
    {
        let base = usize::from(environment.entries().len());
        let ranked = |staged: StagedDeclaration, offset: usize| match rank {
            Some(first) => {
                staged.ranked(SourceRank::from(usize::from(first).saturating_add(offset)))
            },
            None => staged,
        };
        match *generated {
            Generated::Lone(ref member) => {
                let staged = stage_member(environment, member, ConstantIndex::from(base), data);
                environment
                    .add_decl(ranked(staged, 0))
                    .map(|admitted| vec![admitted.position()])
            },
            Generated::Block(ref members) => {
                let mut scope = data.to_vec();
                let mut staged = Vec::with_capacity(members.len());
                for (offset, member) in members.iter().enumerate() {
                    let own = ConstantIndex::from(base.saturating_add(offset));
                    staged.push(ranked(
                        stage_member(environment, member, own, &scope),
                        offset,
                    ));
                    if matches!(*member, Member::Data(..)) {
                        scope.push(own);
                    }
                }
                environment
                    .add_block(staged)
                    .map(|ids| ids.into_iter().map(CheckedId::position).collect())
            },
        }
    }

    /// The members of `generated`, in the order it admits them.
    ///
    /// # Specification
    /// trivial.
    fn members(generated: &Generated) -> &[Member]
    {
        match *generated {
            Generated::Lone(ref member) => core::slice::from_ref(member),
            Generated::Block(ref members) => members.as_slice(),
        }
    }

    /// The place of a data member in a source.
    ///
    /// # Specification
    /// trivial.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Origin
    {
        /// The index of the member's admission in the source.
        admission: usize,
        /// The member's offset among the admission's members.
        member: usize,
    }

    /// What admitting a source gave: the positions of each admission, or
    /// none where the kernel refused it, and the places of the data types in
    /// scope at each admission.
    ///
    /// # Specification
    /// trivial.
    #[derive(Debug)]
    struct Admitted
    {
        /// The positions of each admission, or none where it was refused.
        positions: Vec<Option<Vec<ConstantIndex>>>,
        /// The places of the data types in scope at each admission.
        scopes: Vec<Vec<Origin>>,
    }

    /// Admit `source` in `environment`, in order, each admission at its
    /// positions.
    ///
    /// # Specification
    /// trivial.
    fn admit_source(
        environment: &mut Environment,
        source: &[Generated],
    ) -> Admitted
    {
        let mut data = Vec::new();
        let mut origins: Vec<Origin> = Vec::new();
        let mut positions = Vec::with_capacity(source.len());
        let mut scopes = Vec::with_capacity(source.len());
        for (index, admission) in source.iter().enumerate() {
            scopes.push(origins.clone());
            let verdict = admit_generated(environment, admission, &data, None).ok();
            let admitted = verdict.as_deref().unwrap_or_default();
            for (member, (generated, &position)) in
                members(admission).iter().zip(admitted).enumerate()
            {
                if matches!(*generated, Member::Data(..)) {
                    data.push(position);
                    origins.push(Origin {
                        admission: index,
                        member,
                    });
                }
            }
            positions.push(verdict);
        }
        Admitted { positions, scopes }
    }

    /// A fresh environment that keys each admission, so a readmission can
    /// keep an entry on its key.
    ///
    /// # Specification
    /// trivial.
    fn keyed() -> Environment
    {
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        Environment::recalling(
            crate::verdict::TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
            alloc::sync::Arc::new(crate::verdict::NoVerdicts),
        )
    }

    /// The live entries of `environment` in rank order, each read as its
    /// rank, its key and how it was admitted.
    ///
    /// # Specification
    /// trivial.
    fn read_by_rank(
        environment: &Environment
    ) -> Vec<(
        SourceRank,
        Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>,
        Admission,
    )>
    {
        let mut read: Vec<_> = environment
            .entries()
            .iter()
            .map(|entry| (entry.rank(), entry.key(), entry.admission()))
            .collect();
        read.sort_by_key(|&(rank, ..)| rank);
        read
    }

    /// #7295: an entry's content key reads no build identity, and its entry
    /// key binds that content key to the build. One source admitted under
    /// two builds gives each entry one content key and two entry keys. The
    /// source holds a family `a`, an axiom that names `a`, and a block of two
    /// families: the first names `a`, and the second names the first.
    #[test]
    fn two_builds_give_one_content_key_and_two_entry_keys_7295()
    {
        let zero = LevelConstant::from(0_u64);
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        let read = [[1_u8; 32], [2_u8; 32]].map(|build| {
            let build = crate::verdict::BuildIdentity::from(build);
            let mut environment = Environment::recalling_under(
                crate::verdict::TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
                alloc::sync::Arc::new(crate::verdict::NoVerdicts),
                build,
            );
            let a = admit_generated(
                &mut environment,
                &Generated::Lone(Member::Data(zero, vec![])),
                &[],
                None,
            )
            .expect("`a` admits");
            admit_generated(
                &mut environment,
                &Generated::Lone(Member::Axiom(Field::Earlier(0))),
                &a,
                None,
            )
            .expect("the axiom admits");
            admit_generated(
                &mut environment,
                &Generated::Block(vec![
                    Member::Data(zero, vec![Field::Earlier(0)]),
                    Member::Data(zero, vec![Field::Earlier(1)]),
                ]),
                &a,
                None,
            )
            .expect("the block admits");
            environment
                .entries()
                .iter()
                .map(|entry| {
                    let keys = (entry.content_key(), entry.key());
                    let (Maybe::Present(content), Maybe::Present(key)) = keys
                    else {
                        panic!("each entry is keyed, but read {keys:?}");
                    };
                    assert_eq!(
                        key,
                        crate::verdict::VerdictKey::entry(build, content),
                        "the entry key binds the content key to the build"
                    );
                    (content, key)
                })
                .collect::<Vec<_>>()
        });
        let [ref one, ref other] = read;
        assert_eq!(one.len(), 4, "four entries under the first build");
        assert_eq!(other.len(), 4, "four entries under the second build");
        for (&(one_content, one_key), &(other_content, other_key)) in one.iter().zip(other) {
            assert_eq!(
                one_content, other_content,
                "two builds give one content key"
            );
            assert_ne!(one_key, other_key, "two builds give two entry keys");
        }
    }

    /// #7194: a retired entry keeps its position as a name and frees its
    /// declaration. `b` names `a`, and a readmission retires both. Neither
    /// retires again, each slot holds no declaration, and no position moves.
    /// #7231: the entries count both as retired, and a truncation that drops
    /// both counts none.
    #[test]
    fn a_retired_entry_keeps_its_position_and_frees_its_declaration_7194()
    {
        let zero = LevelConstant::from(0_u64);
        let mut environment = keyed();
        let a = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Data(zero, vec![])),
            &[],
            None,
        )
        .expect("`a` admits");
        let b = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Axiom(Field::Earlier(0))),
            &a,
            None,
        )
        .expect("`b` admits");
        let (a, b) = (a[0], b[0]);
        let length = environment.entries().len();
        let admitted = environment.entries().admitted();
        let watermark = environment.arena().watermark();
        assert_eq!(
            usize::from(environment.entries().retired()),
            0,
            "nothing is retired yet"
        );
        assert_eq!(environment.retire(&[a, b]), Ok(()), "`a` and `b` retire");
        assert_eq!(
            (
                usize::from(environment.entries().retired()),
                environment.entries().admitted()
            ),
            (2, admitted),
            "two entries count as retired, and as admitted still"
        );
        assert_eq!(
            environment.retire(&[a]),
            Err(KernelError::Retired { position: a }),
            "a retired entry does not retire again"
        );
        for position in [a, b] {
            assert!(
                matches!(
                    environment.entries().family().get(usize::from(position)),
                    Some(&Slot::Retired)
                ),
                "the slot at {position:?} holds no declaration"
            );
        }
        assert_eq!(
            environment.entries().len(),
            length,
            "each retired position stays a name"
        );
        assert_eq!(
            environment.arena().watermark(),
            watermark,
            "the retire mints nothing"
        );
        environment
            .entries
            .truncate(gandr_kernel_term::ArenaLength::from(usize::from(a)));
        assert_eq!(
            usize::from(environment.entries().retired()),
            0,
            "a truncation that drops both retired slots counts none"
        );
    }

    /// An entry kept in place after an appended twin reads as after it. A
    /// plain definition is named by its content and by its order among its
    /// twins. The previous revision holds one unit definition, and the edit
    /// puts a twin before it. The readmission gives the old twin the rank 1,
    /// offers the new one at the rank 0, which takes position 1, and keeps
    /// the old one in place. The appended twin takes the first order and the
    /// kept one the second, as a fresh admission of the edited source orders
    /// them.
    #[test]
    fn an_entry_kept_in_place_after_an_appended_twin_reads_as_after_it_6846()
    {
        let order = |environment: &Environment, position: usize| match environment
            .entries()
            .get(position)
            .map(AdmittedDeclaration::key_name)
        {
            Some(crate::encoding::ConstantName::Definition { rank, .. }) => rank,
            Some(
                crate::encoding::ConstantName::Position
                | crate::encoding::ConstantName::Admitted { .. }
                | crate::encoding::ConstantName::Unadmitted,
            )
            | None => {
                panic!("a plain definition is named by its content")
            },
        };
        let mut fresh = keyed();
        for _twin in 0 .. 2_usize {
            let twin = stage_unit(&mut fresh);
            let _admitted = fresh.add_decl(twin).expect("a twin admits");
        }
        let mut readmitted = keyed();
        let old = stage_unit(&mut readmitted);
        let old = readmitted
            .add_decl(old)
            .expect("the old twin admits")
            .position();
        assert_eq!(
            readmitted.rerank((SourceRank::from(0_usize), &[(
                old,
                SourceRank::from(1_usize)
            )])),
            Ok(()),
            "the old twin takes the rank 1"
        );
        let new = stage_unit(&mut readmitted).ranked(SourceRank::from(0_usize));
        let new = readmitted
            .add_decl(new)
            .expect("the new twin admits")
            .position();
        assert_eq!(
            readmitted.keep_in_place(old).map(CheckedId::position),
            Ok(old),
            "the old twin is kept in place"
        );
        assert!(new > old, "the appended twin stands at the later position");
        assert!(
            order(&fresh, 0) < order(&fresh, 1),
            "the fresh twins take two orders"
        );
        assert_eq!(
            order(&readmitted, usize::from(new)),
            order(&fresh, 0),
            "the appended twin takes the first order"
        );
        assert_eq!(
            order(&readmitted, usize::from(old)),
            order(&fresh, 1),
            "the kept twin takes the second order, as after it"
        );
    }

    /// #7197: a held key answers for a keep in place until a commit below
    /// its entry changes what the check reads. `a` and `b` are equal data
    /// declarations, so the key of each counts the ones ranked below it. A
    /// rank rewrite that keeps their order keeps both on their held keys. An
    /// equal declaration `c` committed between them changes the count that
    /// the check of `b` reads, so the keep of `b` is refused, as the check
    /// refuses it. `a`, ranked below `c`, is kept.
    #[test]
    fn a_held_key_answers_until_an_admission_below_it_7197()
    {
        let data = Generated::Lone(Member::Data(LevelConstant::from(0_u64), vec![]));
        let mut environment = keyed();
        let [a, b] = [(); 2].map(|()| {
            match admit_generated(&mut environment, &data, &[], None)
                .expect("an equal declaration admits")
                .as_slice()
            {
                &[position] => position,
                _ => panic!("a lone declaration takes one position"),
            }
        });
        assert_eq!(
            environment.rerank((SourceRank::from(0_usize), &[
                (a, SourceRank::from(2_usize)),
                (b, SourceRank::from(4_usize))
            ])),
            Ok(()),
            "`a` takes the rank 2 and `b` the rank 4"
        );
        for position in [a, b] {
            assert_eq!(
                environment.keep_in_place(position).map(CheckedId::position),
                Ok(position),
                "the entry at {position:?} keeps its order, so it is kept"
            );
        }
        let _c = admit_generated(
            &mut environment,
            &data,
            &[],
            Some(SourceRank::from(3_usize)),
        )
        .expect("`c` admits between them");
        assert_eq!(
            environment.keep_in_place(a).map(CheckedId::position),
            Ok(a),
            "`a`, ranked below `c`, reads what it read"
        );
        assert!(
            matches!(
                environment.keep_in_place(b),
                Err(KernelError::Unkept { position, .. }) if position == b
            ),
            "`b` counts `c` now, so its held key is refused"
        );
    }

    /// #6845: an export that writes each position as itself after a retire
    /// is not the fresh artifact, so the byte witness can fail. The source
    /// holds `x`, then `a`, then `b` over `a`, and the edit deletes `x`. The
    /// readmission retires `x`, gives `a` the rank 0 and `b` the rank 1, and
    /// keeps both in place. `b` names `a` at the position 1, whose place is 0.
    #[test]
    fn an_export_by_position_after_a_retire_differs_6845()
    {
        let (zero, one) = (LevelConstant::from(0_u64), LevelConstant::from(1_u64));
        let x = Generated::Lone(Member::Data(one, vec![]));
        let a = Generated::Lone(Member::Data(zero, vec![]));
        let b = Generated::Lone(Member::Axiom(Field::Earlier(0)));
        let mut fresh = keyed();
        let fresh_a = admit_generated(&mut fresh, &a, &[], None).expect("`a` admits");
        let _fresh_b = admit_generated(&mut fresh, &b, &fresh_a, None).expect("`b` admits");
        let mut kept = keyed();
        let kept_x = admit_generated(&mut kept, &x, &[], None).expect("`x` admits");
        let kept_a = admit_generated(&mut kept, &a, &[], None).expect("`a` admits");
        let kept_b = admit_generated(&mut kept, &b, &kept_a, None).expect("`b` admits");
        assert_eq!(kept.retire(&kept_x), Ok(()), "`x` retires");
        let (a, b) = (kept_a[0], kept_b[0]);
        assert_eq!(
            kept.rerank((SourceRank::from(0_usize), &[
                (a, SourceRank::from(0_usize)),
                (b, SourceRank::from(1_usize))
            ])),
            Ok(()),
            "`a` takes the rank 0 and `b` the rank 1"
        );
        for position in [a, b] {
            assert_eq!(
                kept.keep_in_place(position).map(CheckedId::position),
                Ok(position),
                "the entry at {position:?} is kept in place"
            );
        }
        let expected = exported(&fresh);
        assert_eq!(
            exported(&kept),
            expected,
            "the export by place writes the fresh artifact"
        );
        assert_ne!(
            gandr_kernel_term::encode(kept.arena(), &in_rank_order(&kept)),
            expected,
            "the export by position writes `a` at the position 1"
        );
    }

    /// The live entries of `environment` in rank order, each marked as
    /// checked.
    ///
    /// # Specification
    /// trivial.
    fn in_rank_order(environment: &Environment) -> Vec<gandr_kernel_term::MarkedDeclaration>
    {
        let entries = environment.entries();
        environment
            .in_rank_order()
            .filter_map(|position| entries.get(usize::from(position)))
            .map(|entry| {
                gandr_kernel_term::MarkedDeclaration::new(
                    gandr_kernel_term::AdmissionMark::Checked,
                    entry.declaration().clone(),
                )
            })
            .collect()
    }

    /// The bytes that the export of `environment` writes: its live entries
    /// in rank order, each position written as its place.
    ///
    /// # Specification
    /// trivial.
    fn exported(environment: &Environment) -> gandr_kernel_term::EncodedArtifact
    {
        let marked = in_rank_order(environment);
        match environment.places() {
            Maybe::Present(places) => {
                gandr_kernel_term::encode_placed(environment.arena(), &marked, &places)
            },
            Maybe::Absent(super::places::Absent::InOrder) => {
                gandr_kernel_term::encode(environment.arena(), &marked)
            },
        }
    }

    /// One edit of a generated source.
    #[derive(Clone, Debug)]
    enum Edit
    {
        /// Another admission replaces the admission at the index.
        Replaced(usize, Generated),
        /// Another admission goes in at the index.
        Inserted(usize, Generated),
        /// The admission at the index goes out.
        Deleted(usize),
        /// The admission at the first index moves to the second index.
        Moved(usize, usize),
        /// No admission changes.
        Unedited,
    }

    /// A generated source after an edit, with the admission of the source
    /// before the edit that each of its admissions is unchanged from.
    ///
    /// # Specification
    /// trivial.
    #[derive(Debug)]
    struct EditedSource
    {
        /// The admissions after the edit.
        admissions: Vec<Generated>,
        /// For each of them, the index of the admission before the edit that
        /// it is unchanged from, or none for an admission the edit writes.
        origin: Vec<Option<usize>>,
    }

    /// `source` after `edit`. An index past the source wraps.
    ///
    /// # Specification
    /// trivial.
    fn edited_by(
        source: &[Generated],
        edit: &Edit,
    ) -> EditedSource
    {
        let length = source.len();
        let wrap = |at: usize| at.checked_rem(length).unwrap_or_default();
        let mut admissions = source.to_vec();
        let mut origin: Vec<Option<usize>> = (0 .. length).map(Some).collect();
        match *edit {
            Edit::Replaced(at, ref admission) => {
                if let (Some(slot), Some(from)) =
                    (admissions.get_mut(wrap(at)), origin.get_mut(wrap(at)))
                {
                    *slot = admission.clone();
                    *from = None;
                }
            },
            Edit::Inserted(at, ref admission) => {
                let at = at.checked_rem(length.saturating_add(1)).unwrap_or_default();
                admissions.insert(at, admission.clone());
                origin.insert(at, None);
            },
            Edit::Deleted(at) => {
                if wrap(at) < length {
                    let _deleted = admissions.remove(wrap(at));
                    let _origin = origin.remove(wrap(at));
                }
            },
            Edit::Moved(from, to) => {
                if wrap(from) < length {
                    let admission = admissions.remove(wrap(from));
                    admissions.insert(wrap(to), admission);
                    let moved = origin.remove(wrap(from));
                    origin.insert(wrap(to), moved);
                }
            },
            Edit::Unedited => {},
        }
        EditedSource { admissions, origin }
    }

    /// Whether an offer of the release differential ranks below the offer
    /// before it.
    #[derive(Clone, Copy, Debug)]
    enum Dip
    {
        /// It ranks past every earlier offer.
        Ascending,
        /// It ranks below the offer before it.
        Below,
    }

    /// One offer of a source that the release differential admits.
    #[derive(Clone, Debug)]
    enum Offer
    {
        /// A generated declaration, alone.
        Lone(Member, Dip),
        /// A block of generated declarations.
        Block(Vec<Member>),
        /// A unit definition: its body is the unit value, or the constant of
        /// the earlier unit definition that the draw picks.
        Unit(Option<usize>, Dip),
        /// An integer atom, sealed open, or closed after the extent.
        Atom(Option<usize>),
        /// The definition `7` of the latest atom, or of the integer.
        Seven,
    }

    /// What an offer gives the offers after it, and what it reads of the
    /// offers before it.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Kind
    {
        /// The data types.
        Data,
        /// The unit definitions.
        Unit,
        /// The atoms.
        Atom,
        /// Every earlier offer: a block settles each release before it.
        Every,
        /// No earlier offer.
        Nothing,
    }

    /// A generated dip.
    ///
    /// # Specification
    /// trivial.
    fn dip() -> impl proptest::strategy::Strategy<Value = Dip>
    {
        use proptest::prelude::Just;
        proptest::prop_oneof![3 => Just(Dip::Ascending), 1 => Just(Dip::Below)]
    }

    /// A generated offer. The alphabet is small, so declarations repeat.
    ///
    /// # Specification
    /// trivial.
    fn offer() -> impl proptest::strategy::Strategy<Value = Offer>
    {
        use proptest::prelude::Just;
        use proptest::strategy::Strategy as _;
        proptest::prop_oneof![
            4 => (member(), dip()).prop_map(|(member, dip)| Offer::Lone(member, dip)),
            1 => proptest::collection::vec(member(), 1 .. 3).prop_map(Offer::Block),
            4 => (proptest::option::of(0_usize .. 4), dip())
                .prop_map(|(drawn, dip)| Offer::Unit(drawn, dip)),
            1 => proptest::option::of(0_usize .. 3).prop_map(Offer::Atom),
            1 => Just(Offer::Seven),
        ]
    }

    /// What `offer` gives the offers after it.
    ///
    /// # Specification
    /// trivial.
    fn gives(offer: &Offer) -> Kind
    {
        match *offer {
            Offer::Lone(Member::Data(..), _) => Kind::Data,
            Offer::Unit(..) => Kind::Unit,
            Offer::Atom(_) => Kind::Atom,
            Offer::Block(_) => Kind::Every,
            Offer::Lone(Member::Codata(..) | Member::Axiom(_) | Member::Refused, _)
            | Offer::Seven => Kind::Nothing,
        }
    }

    /// What `offer` reads of the offers before it, which the driver settles
    /// before it stages the offer.
    ///
    /// # Specification
    /// trivial.
    fn reads(offer: &Offer) -> Kind
    {
        let earlier = |field: &Field| matches!(*field, Field::Earlier(_));
        match *offer {
            Offer::Lone(Member::Data(_, ref fields), _) if fields.iter().any(earlier) => Kind::Data,
            Offer::Lone(Member::Codata(_, ref field) | Member::Axiom(ref field), _)
                if earlier(field) =>
            {
                Kind::Data
            },
            Offer::Unit(Some(_), _) => Kind::Unit,
            Offer::Seven => Kind::Atom,
            Offer::Block(_) => Kind::Every,
            Offer::Lone(..) | Offer::Unit(None, _) | Offer::Atom(_) => Kind::Nothing,
        }
    }

    /// Whether the release differential ranks each offer.
    #[derive(Clone, Copy, Debug)]
    enum Ranking
    {
        /// Each offer ranks at twice its position, or three below that when it
        /// dips.
        Ranked,
        /// No offer carries a rank.
        Unranked,
    }

    /// The admitted positions that an offer reads: the data types, the unit
    /// definitions and the latest atom, each in position order.
    #[derive(Clone, Debug, Default)]
    struct InScope
    {
        /// The admitted data types.
        data: Vec<ConstantIndex>,
        /// The admitted unit definitions.
        units: Vec<ConstantIndex>,
        /// The latest admitted atom.
        atom: Option<ConstantIndex>,
    }

    impl InScope
    {
        /// Note what `offer` gives once `outcome` resolves it.
        ///
        /// # Specification
        /// trivial.
        fn note(
            &mut self,
            offer: &Offer,
            outcome: &Result<Vec<ConstantIndex>, KernelError>,
        )
        {
            let Ok(positions) = outcome.as_ref()
            else {
                return;
            };
            let insert = |held: &mut Vec<ConstantIndex>, position: ConstantIndex| {
                let at = held.partition_point(|&earlier| earlier < position);
                held.insert(at, position);
            };
            match *offer {
                Offer::Lone(Member::Data(..), _) => {
                    for &position in positions {
                        insert(&mut self.data, position);
                    }
                },
                Offer::Block(ref members) => {
                    for (member, &position) in members.iter().zip(positions) {
                        if matches!(*member, Member::Data(..)) {
                            insert(&mut self.data, position);
                        }
                    }
                },
                Offer::Unit(..) => {
                    for &position in positions {
                        insert(&mut self.units, position);
                    }
                },
                Offer::Atom(_) => self.atom = positions.last().copied().max(self.atom),
                Offer::Lone(Member::Codata(..) | Member::Axiom(_) | Member::Refused, _)
                | Offer::Seven => {},
            }
        }
    }

    /// The rank of an offer at `position`, as `dip` and `ranking` state.
    ///
    /// # Specification
    /// trivial.
    fn ranked(
        staged: StagedDeclaration,
        position: ConstantIndex,
        (dip, ranking): (Dip, Ranking),
    ) -> StagedDeclaration
    {
        let even = usize::from(position).saturating_mul(2);
        match (ranking, dip) {
            (Ranking::Unranked, Dip::Ascending | Dip::Below) => staged,
            (Ranking::Ranked, Dip::Below) if even >= 4 => {
                staged.ranked(SourceRank::from(even.saturating_sub(3)))
            },
            (Ranking::Ranked, Dip::Ascending | Dip::Below) => staged.ranked(SourceRank::from(even)),
        }
    }

    /// Stage `offer` in `environment` over what `scope` holds.
    ///
    /// # Specification
    /// trivial.
    fn stage_offer(
        environment: &mut Environment,
        offer: &Offer,
        scope: &InScope,
        ranking: Ranking,
    ) -> Vec<StagedDeclaration>
    {
        let base = environment.entries().len();
        let own = ConstantIndex::from(base);
        match *offer {
            Offer::Lone(ref member, dip) => {
                let staged = stage_member(environment, member, own, &scope.data);
                vec![ranked(staged, own, (dip, ranking))]
            },
            Offer::Block(ref members) => {
                let mut data = scope.data.clone();
                let mut staged = Vec::with_capacity(members.len());
                for (offset, member) in members.iter().enumerate() {
                    let own = ConstantIndex::from(usize::from(base).saturating_add(offset));
                    staged.push(ranked(
                        stage_member(environment, member, own, &data),
                        own,
                        (Dip::Ascending, ranking),
                    ));
                    if matches!(*member, Member::Data(..)) {
                        data.push(own);
                    }
                }
                staged
            },
            Offer::Unit(drawn, dip) => {
                let named = drawn.and_then(|drawn| {
                    let at = drawn.checked_rem(scope.units.len())?;
                    scope.units.get(at).copied()
                });
                vec![ranked(
                    unit_definition(environment, named),
                    own,
                    (dip, ranking),
                )]
            },
            Offer::Atom(extent) => {
                let scope = extent.map_or(SealScope::Open, |extent| {
                    SealScope::Closed(SealExtent::from(extent))
                });
                vec![ranked(
                    integer_atom(environment, scope),
                    own,
                    (Dip::Ascending, ranking),
                )]
            },
            Offer::Seven => vec![ranked(
                seven_at(environment, scope.atom),
                own,
                (Dip::Ascending, ranking),
            )],
        }
    }

    /// Admit `source` in `environment` in order, each offer settled before
    /// the next, and answer the outcome of each offer.
    ///
    /// # Specification
    /// trivial.
    fn admit_serially(
        environment: &mut Environment,
        source: &[Offer],
        ranking: Ranking,
    ) -> Vec<Result<Vec<ConstantIndex>, KernelError>>
    {
        let mut scope = InScope::default();
        let mut outcomes = Vec::with_capacity(source.len());
        for offer in source {
            let mut staged = stage_offer(environment, offer, &scope, ranking);
            let outcome = match *offer {
                Offer::Block(_) => environment
                    .add_block(staged)
                    .map(|ids| ids.into_iter().map(CheckedId::position).collect()),
                Offer::Lone(..) | Offer::Unit(..) | Offer::Atom(_) | Offer::Seven => environment
                    .add_decl(staged.pop().expect("a lone offer stages one declaration"))
                    .map(|id| vec![id.position()]),
            };
            scope.note(offer, &outcome);
            outcomes.push(outcome);
        }
        outcomes
    }

    /// How the driver picks the release that it settles next.
    #[derive(Clone, Copy, Debug)]
    enum Settling
    {
        /// The release made first.
        Oldest,
        /// The release made last.
        Newest,
        /// A release that a fixed sequence of draws picks.
        Drawn,
    }

    /// One release in flight: the offer that it answers, what the offer
    /// gives, and the check.
    struct Flight
    {
        /// The index of the offer in the source.
        offer: usize,
        /// What the offer gives the offers after it.
        gives: Kind,
        /// What the commit needs beside the check.
        pending: super::Pending,
        /// The check, released.
        check: super::Check,
    }

    /// The place of an offer in its source.
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    struct At(usize);

    /// The most releases that a driver keeps in flight.
    #[derive(Clone, Copy, Debug)]
    #[repr(transparent)]
    struct InFlight(usize);

    /// The serial driver of the release differential: it releases each offer
    /// in source order, and it settles the releases in flight in the order
    /// that its settling picks, as their dependences allow.
    struct Driver<'source>
    {
        /// The environment that the driver admits into.
        environment: Environment,
        /// The offers.
        source: &'source [Offer],
        /// The releases in flight, oldest first.
        flights: Vec<Flight>,
        /// What the offers settled so far give.
        scope: InScope,
        /// The outcome of each offer, once it resolves.
        outcomes: Vec<Option<Result<Vec<ConstantIndex>, KernelError>>>,
        /// How the driver picks the release that it settles next.
        settling: Settling,
        /// The state of the draws.
        draw: u64,
    }

    impl Driver<'_>
    {
        /// Settle one release in flight, as the settling picks it.
        ///
        /// # Specification
        /// trivial.
        fn settle_one(&mut self)
        {
            let last = self.flights.len().saturating_sub(1);
            let at = match self.settling {
                Settling::Oldest => 0,
                Settling::Newest => last,
                Settling::Drawn => {
                    // A xorshift step: deterministic, and enough to reach
                    // each order of a few releases.
                    let state = self.draw ^ self.draw.wrapping_shl(13);
                    let state = state ^ state.wrapping_shr(7);
                    let state = state ^ state.wrapping_shl(17);
                    self.draw = state;
                    let count = u64::try_from(self.flights.len()).expect("a small count");
                    usize::try_from(state.checked_rem(count).unwrap_or(0)).expect("a small index")
                },
            };
            let Flight {
                offer,
                pending,
                check,
                ..
            } = self.flights.remove(at);
            let ran = check.run();
            let outcome = self
                .environment
                .settle(pending, ran)
                .map(|id| vec![id.position()]);
            self.scope.note(&self.source[offer], &outcome);
            self.outcomes[offer] = Some(outcome);
        }

        /// Settle the releases in flight until none gives `kind`.
        ///
        /// # Specification
        /// trivial.
        fn settle_until_none_gives(
            &mut self,
            kind: Kind,
        )
        {
            while self
                .flights
                .iter()
                .any(|flight| kind == Kind::Every || flight.gives == kind)
            {
                self.settle_one();
            }
        }

        /// Release `offer`, at index `index`, settling every release in
        /// flight when it holds.
        ///
        /// # Specification
        /// trivial.
        fn release(
            &mut self,
            At(index): At,
            staged: StagedDeclaration,
        )
        {
            let released = match self.environment.release(staged) {
                Ok(super::Released::Held(staged, _)) => {
                    self.settle_until_none_gives(Kind::Every);
                    self.environment.release(staged)
                },
                other => other,
            };
            match released {
                Ok(super::Released::Running(pending, check)) => self.flights.push(Flight {
                    offer: index,
                    gives: gives(&self.source[index]),
                    pending,
                    check,
                }),
                Ok(super::Released::Held(_, hold)) => {
                    panic!("a release with no release outstanding never holds, yet {hold:?}")
                },
                Err(error) => self.outcomes[index] = Some(Err(error)),
            }
        }
    }

    /// Admit `source` through the driver under `settling`, with at most
    /// `width` releases in flight, and answer the outcome of each offer.
    ///
    /// # Specification
    /// trivial.
    fn admit_released(
        environment: Environment,
        source: &[Offer],
        (settling, InFlight(width), ranking): (Settling, InFlight, Ranking),
    ) -> (Environment, Vec<Result<Vec<ConstantIndex>, KernelError>>)
    {
        let mut driver = Driver {
            environment,
            source,
            flights: Vec::new(),
            scope: InScope::default(),
            outcomes: vec![None; source.len()],
            settling,
            draw: 0x9e37_79b9_7f4a_7c15,
        };
        for (index, offer) in source.iter().enumerate() {
            match reads(offer) {
                Kind::Nothing => {},
                kind @ (Kind::Data | Kind::Unit | Kind::Atom | Kind::Every) => {
                    driver.settle_until_none_gives(kind);
                },
            }
            let mut staged = stage_offer(&mut driver.environment, offer, &driver.scope, ranking);
            match *offer {
                Offer::Block(_) => {
                    let outcome = driver
                        .environment
                        .add_block(staged)
                        .map(|ids| ids.into_iter().map(CheckedId::position).collect());
                    driver.scope.note(offer, &outcome);
                    driver.outcomes[index] = Some(outcome);
                },
                Offer::Lone(..) | Offer::Unit(..) | Offer::Atom(_) | Offer::Seven => {
                    driver.release(
                        At(index),
                        staged.pop().expect("a lone offer stages one declaration"),
                    );
                },
            }
            while driver.flights.len() > width {
                driver.settle_one();
            }
        }
        driver.settle_until_none_gives(Kind::Every);
        let outcomes = driver
            .outcomes
            .into_iter()
            .map(|outcome| outcome.expect("every offer resolves"))
            .collect();
        (driver.environment, outcomes)
    }

    /// How an entry's admission named it, read without the arena's ids.
    #[derive(Debug, Eq, PartialEq)]
    enum Named
    {
        /// By its position.
        Position,
        /// By its content: its order among its twins and its digest.
        Definition(
            crate::encoding::DefinitionRank,
            gandr_kernel_check_memo::ContentDigest,
        ),
        /// By the content key a caller's table gives it.
        Admitted(crate::verdict::EntryContentKey),
        /// As no constant, which no admitted entry is.
        Unadmitted,
    }

    /// One entry as the release differential compares it: its rank, its key,
    /// its name, how it was admitted, what it names, what it rests on and its
    /// reading.
    type Compared = (
        SourceRank,
        Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>,
        Named,
        Admission,
        alloc::boxed::Box<[ConstantIndex]>,
        BTreeSet<ConstantIndex>,
        crate::check::Accessibility,
    );

    /// What the release differential compares of an environment: each slot,
    /// the places, the reach of each position, the records that a receipt
    /// signs, the manifest and the admitted count. The census is a tally of
    /// the memo that each check met, and the memo is the one part that the
    /// order of the commits moves; so it is left out.
    #[derive(Debug, PartialEq)]
    struct Folded
    {
        /// Each slot, as its live entry, or nothing for a vacancy or a
        /// retired entry.
        slots: Vec<Option<Compared>>,
        /// The place of each live position.
        places: Maybe<gandr_kernel_term::Places, super::places::Absent>,
        /// The reach of an edit at each position.
        reach: Vec<alloc::boxed::Box<[ConstantIndex]>>,
        /// The records that a receipt signs.
        records: Vec<crate::verdict::VerdictRecord>,
        /// The atoms manifest after the last admission.
        manifest: Vec<ConstantIndex>,
        /// How many admitted results the checks took.
        admitted: crate::admitted::AdmittedCount,
    }

    /// Read `environment` as the release differential compares it.
    ///
    /// # Specification
    /// trivial.
    fn folded(
        environment: &Environment,
        signer: &crate::verdict::KernelSigner,
    ) -> Folded
    {
        let length = usize::from(environment.entries().len());
        let slots = (0 .. length)
            .map(|position| {
                environment
                    .entries()
                    .live(ConstantIndex::from(position))
                    .map(|entry| {
                        (
                            entry.rank(),
                            entry.key(),
                            match entry.key_name() {
                                crate::encoding::ConstantName::Position => Named::Position,
                                crate::encoding::ConstantName::Definition {
                                    rank, digest, ..
                                } => Named::Definition(rank, digest),
                                crate::encoding::ConstantName::Admitted { key } => {
                                    Named::Admitted(key)
                                },
                                crate::encoding::ConstantName::Unadmitted => Named::Unadmitted,
                            },
                            entry.admission(),
                            alloc::boxed::Box::<[ConstantIndex]>::from(entry.references()),
                            entry.rested_on().clone(),
                            entry.accessibility().clone(),
                        )
                    })
            })
            .collect();
        let reach = (0 .. length)
            .map(|position| environment.reach([ConstantIndex::from(position)]))
            .collect();
        let records = match environment.receipt(signer) {
            Maybe::Present(stored) => stored.records().to_vec(),
            Maybe::Absent(_) => Vec::new(),
        };
        Folded {
            slots,
            places: environment.places(),
            reach,
            records,
            manifest: environment.manifest.clone(),
            admitted: environment.admitted(),
        }
    }

    /// A source of verdicts that answers the receipts of one earlier run for
    /// every key.
    #[derive(Debug)]
    #[repr(transparent)]
    struct Recorded(Vec<alloc::sync::Arc<crate::verdict::StoredReceipt>>);

    impl crate::verdict::VerdictSource for Recorded
    {
        /// The receipts of the earlier run, whatever `key` is.
        ///
        /// # Specification
        /// trivial.
        fn receipts(
            &self,
            _key: crate::verdict::VerdictKey,
        ) -> &[alloc::sync::Arc<crate::verdict::StoredReceipt>]
        {
            &self.0
        }
    }

    /// How the environments of the release differential treat verdicts.
    #[derive(Clone, Copy, Debug)]
    enum Verdicts
    {
        /// They recheck every admission and key none.
        Rechecked,
        /// They key each admission and recall nothing.
        Keyed,
        /// They recall from the receipt of a keyed serial run of the whole
        /// source, and they admit the source less its first offer.
        Recalled,
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

        /// #3476: releases settled in each order that their dependences
        /// allow give the outcomes, the entries, the ranks, the keys, the
        /// names, the order, the reach and the records of the serial run,
        /// with the speculation group off and on. The driver releases in
        /// source order. It settles the releases in flight that an offer
        /// reads before it stages the offer, every release when a release
        /// holds, and one more whenever more than the width are in flight.
        /// Atoms, presented and repeated declarations, refusals, dips in rank
        /// and unranked offers each meet a read of order, and a refusal
        /// before an unranked offer meets a predicted rank.
        #[test]
        fn each_commit_order_of_a_released_source_folds_as_the_serial_run_3476(
            source in proptest::collection::vec(offer(), 1 .. 12),
        ) {
            let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
            for ranking in [Ranking::Ranked, Ranking::Unranked] {
                let mut recording = keyed();
                let _recorded = admit_serially(&mut recording, &source, ranking);
                let store: Vec<_> = match recording.receipt(&signer) {
                    Maybe::Present(stored) => vec![alloc::sync::Arc::new(stored)],
                    Maybe::Absent(_) => Vec::new(),
                };
                let store: alloc::sync::Arc<dyn crate::verdict::VerdictSource> =
                    alloc::sync::Arc::new(Recorded(store));
                for verdicts in [Verdicts::Rechecked, Verdicts::Keyed, Verdicts::Recalled] {
                    let fresh = || match verdicts {
                        Verdicts::Rechecked => Environment::new(),
                        Verdicts::Keyed => keyed(),
                        Verdicts::Recalled => Environment::recalling(
                            crate::verdict::TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
                            alloc::sync::Arc::clone(&store),
                        ),
                    };
                    let offered = match verdicts {
                        Verdicts::Rechecked | Verdicts::Keyed => source.as_slice(),
                        Verdicts::Recalled => source.get(1 ..).unwrap_or_default(),
                    };
                    let mut serial = fresh();
                    let reference = admit_serially(&mut serial, offered, ranking);
                    let expected = folded(&serial, &signer);
                    for settling in [Settling::Oldest, Settling::Newest, Settling::Drawn] {
                        for width in [1_usize, 2, 3, 8] {
                            for speculation in [
                                crate::speculation::Speculation::OFF,
                                crate::speculation::Speculation::ON,
                            ] {
                                let (released, outcomes) = admit_released(
                                    fresh().speculating(speculation),
                                    offered,
                                    (settling, InFlight(width), ranking),
                                );
                                proptest::prop_assert_eq!(
                                    &outcomes,
                                    &reference,
                                    "each offer resolves as in the serial run: {:?} {:?} {:?} {} {}",
                                    verdicts, ranking, settling, width, speculation
                                );
                                proptest::prop_assert_eq!(
                                    &folded(&released, &signer),
                                    &expected,
                                    "the environment folds as the serial run's: {:?} {:?} {:?} {} {}",
                                    verdicts, ranking, settling, width, speculation
                                );
                                proptest::prop_assert_eq!(
                                    usize::from(released.releases.outstanding()),
                                    0_usize,
                                    "no release stays outstanding"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// #3476: a release behind a refused one takes the rank past the refused
    /// release's reservation, as if that release admits. Settled first, it
    /// commits at the predicted rank. The refusal folds, and the fold moves
    /// the entry to the serial rank: one rollback, and the environment folds
    /// as the serial run's.
    #[test]
    fn a_refusal_before_a_predicted_rank_moves_it_at_the_fold_3476()
    {
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        let source = [
            Offer::Lone(Member::Refused, Dip::Ascending),
            Offer::Unit(None, Dip::Ascending),
        ];
        let mut serial = Environment::new();
        let reference = admit_serially(&mut serial, &source, Ranking::Unranked);
        let (released, outcomes) = admit_released(
            Environment::new().speculating(crate::speculation::Speculation::ON),
            &source,
            (Settling::Newest, InFlight(2), Ranking::Unranked),
        );
        assert_eq!(
            outcomes, reference,
            "each offer resolves as in the serial run"
        );
        assert_eq!(
            usize::from(released.rollbacks()),
            1_usize,
            "the fold moves the predicted rank once"
        );
        assert_eq!(
            released.entries().rank_of(ConstantIndex::from(1_usize)),
            Some(SourceRank::from(0_usize)),
            "the unit definition takes the serial rank"
        );
        assert_eq!(
            folded(&released, &signer),
            folded(&serial, &signer),
            "the environment folds as the serial run's"
        );
    }

    /// Release each offer of `source` in `environment` in order, ranked, with
    /// none settled, and answer each release with the arena's mark after it.
    ///
    /// # Specification
    /// trivial.
    fn release_each(
        environment: &mut Environment,
        source: &[Offer],
    ) -> Vec<(
        super::Pending,
        super::Check,
        gandr_kernel_term::ArenaWatermark,
    )>
    {
        let scope = InScope::default();
        source
            .iter()
            .map(|offer| {
                let staged = stage_offer(environment, offer, &scope, Ranking::Ranked)
                    .pop()
                    .expect("a lone offer stages one declaration");
                let Ok(Released::Running(pending, check)) = environment.release(staged)
                else {
                    panic!("each offer releases");
                };
                (pending, check, environment.arena.watermark())
            })
            .collect()
    }

    /// #3476: a drop after a release leaves the environment as if no later
    /// release was made. The later releases leave the queue, the entries and
    /// the arena, each counts one rollback, and their runs are discarded. The
    /// same declarations admitted again fold as the serial run's. A drop past
    /// a committed admission is refused, and nothing changes.
    #[test]
    fn a_drop_after_a_release_leaves_the_serial_run_3476()
    {
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        let source = [
            Offer::Unit(None, Dip::Ascending),
            Offer::Lone(Member::Refused, Dip::Ascending),
            Offer::Lone(Member::Axiom(Field::Unit), Dip::Ascending),
        ];
        let mut serial = Environment::new();
        let reference = admit_serially(&mut serial, &source, Ranking::Ranked);

        let mut environment = Environment::new();
        let mut released = release_each(&mut environment, &source).into_iter();
        let (first, first_check, first_mark) = released.next().expect("three releases");
        let (_, second_check, _) = released.next().expect("three releases");
        let (_, third_check, _) = released.next().expect("three releases");
        let second_ran = second_check.run();
        assert_eq!(
            environment.drop_after(&first),
            Ok(()),
            "no admission after the first release is committed"
        );
        assert_eq!(
            usize::from(environment.entries().len()),
            1_usize,
            "the entries end past the first release"
        );
        assert_eq!(
            usize::from(environment.releases.outstanding()),
            1_usize,
            "the first release alone stays outstanding"
        );
        assert_eq!(
            usize::from(environment.rollbacks()),
            2_usize,
            "each dropped release counts one rollback"
        );
        assert_eq!(
            environment.arena.watermark(),
            first_mark,
            "the arena ends past the content of the first release"
        );
        environment.discard(second_ran);
        environment.discard(third_check.run());
        let mut outcomes = vec![
            environment
                .settle(first, first_check.run())
                .map(|id| vec![id.position()]),
        ];
        let scope = InScope::default();
        for offer in source.get(1 ..).unwrap_or_default() {
            let staged = stage_offer(&mut environment, offer, &scope, Ranking::Ranked)
                .pop()
                .expect("a lone offer stages one declaration");
            outcomes.push(environment.add_decl(staged).map(|id| vec![id.position()]));
        }
        assert_eq!(
            outcomes, reference,
            "each offer resolves as in the serial run"
        );
        assert_eq!(
            folded(&environment, &signer),
            folded(&serial, &signer),
            "the environment folds as the serial run's"
        );

        let mut committed = Environment::new();
        let mut released = release_each(&mut committed, &source).into_iter();
        let (first, ..) = released.next().expect("three releases");
        let _second = released.next().expect("three releases");
        let (third, third_check, _) = released.next().expect("three releases");
        assert!(
            committed.settle(third, third_check.run()).is_ok(),
            "the third declaration admits"
        );
        assert_eq!(
            committed.drop_after(&first),
            Err(KernelError::UnboundConstant {
                index: ConstantIndex::from(0_usize)
            }),
            "an admission after the first release refuses the drop"
        );
        assert_eq!(
            usize::from(committed.entries().len()),
            3_usize,
            "the refused drop keeps every entry"
        );
    }

    /// Stage `offer` alone in `environment`, at `rank`.
    ///
    /// # Specification
    /// trivial.
    fn staged_at(
        environment: &mut Environment,
        (offer, rank): (&Offer, SourceRank),
    ) -> StagedDeclaration
    {
        stage_offer(environment, offer, &InScope::default(), Ranking::Unranked)
            .pop()
            .expect("a lone offer stages one declaration")
            .ranked(rank)
    }

    /// Release `offer` alone in `environment` at `rank`, with its check.
    ///
    /// # Specification
    /// trivial.
    fn released_at(
        environment: &mut Environment,
        (offer, rank): (&Offer, SourceRank),
    ) -> (super::Pending, super::Check)
    {
        let staged = staged_at(environment, (offer, rank));
        let Ok(Released::Running(pending, check)) = environment.release(staged)
        else {
            panic!("the offer releases at its rank");
        };
        (pending, check)
    }

    /// #7281: a keep in place and a retirement go ahead beside two
    /// outstanding releases below them. The environment folds as the serial
    /// run's, which commits the releases first. A release ranked above, one
    /// that reads order, a generative release of the same content and a twin
    /// below each hold the keep.
    #[test]
    fn a_keep_and_a_retirement_beside_a_release_fold_as_the_serial_run_7281()
    {
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        let level = LevelConstant::from(0);
        let admitted = [
            (Offer::Unit(None, Dip::Ascending), 0_usize),
            (Offer::Lone(Member::Axiom(Field::Unit), Dip::Ascending), 10),
            (
                Offer::Lone(Member::Codata(level, Field::Unit), Dip::Ascending),
                12,
            ),
            (Offer::Unit(None, Dip::Ascending), 20),
        ];
        let beside = [
            (
                Offer::Lone(Member::Data(level, vec![Field::Unit]), Dip::Ascending),
                4_usize,
            ),
            (
                Offer::Lone(Member::Axiom(Field::Universe(level)), Dip::Ascending),
                6,
            ),
        ];
        let kept = ConstantIndex::from(1_usize);
        let retired = ConstantIndex::from(2_usize);
        let twin = ConstantIndex::from(3_usize);
        let admit = |environment: &mut Environment| {
            for &(ref offer, rank) in &admitted {
                let staged = staged_at(environment, (offer, SourceRank::from(rank)));
                assert!(
                    environment.add_decl(staged).is_ok(),
                    "each admitted offer admits"
                );
            }
        };

        let mut serial = keyed();
        admit(&mut serial);
        for &(ref offer, rank) in &beside {
            let staged = staged_at(&mut serial, (offer, SourceRank::from(rank)));
            assert!(serial.add_decl(staged).is_ok(), "each offer beside admits");
        }
        assert_eq!(
            serial.keep_in_place(kept).map(CheckedId::position),
            Ok(kept),
            "the serial run keeps the axiom"
        );
        assert_eq!(
            serial.retire(&[retired]),
            Ok(()),
            "the serial run retires the codata"
        );

        let mut environment = keyed();
        admit(&mut environment);
        let [first, second] = beside.each_ref().map(|&(ref offer, rank)| {
            released_at(&mut environment, (offer, SourceRank::from(rank)))
        });
        assert_eq!(
            environment.keep_in_place(kept).map(CheckedId::position),
            Ok(kept),
            "the axiom keeps beside the releases below it"
        );
        assert_eq!(
            environment.retire(&[retired]),
            Ok(()),
            "the codata retires beside the releases below it"
        );
        for (pending, check) in [first, second] {
            assert!(
                environment.settle(pending, check.run()).is_ok(),
                "each release admits"
            );
        }
        assert_eq!(
            folded(&environment, &signer),
            folded(&serial, &signer),
            "the environment folds as the serial run's"
        );

        let mut above = keyed();
        admit(&mut above);
        let _released = released_at(
            &mut above,
            (
                &Offer::Unit(None, Dip::Ascending),
                SourceRank::from(14_usize),
            ),
        );
        assert!(
            matches!(
                above.retire(&[retired]),
                Err(KernelError::UnsettledReleases { .. })
            ),
            "a release ranked above the codata holds its retirement"
        );
        for (reads, offer, rank, at) in [
            (
                "a release ranked above it",
                Offer::Unit(None, Dip::Ascending),
                14_usize,
                kept,
            ),
            ("a release that reads order", Offer::Atom(Some(0)), 8, kept),
            (
                "a generative release of its content",
                Offer::Lone(Member::Axiom(Field::Unit), Dip::Ascending),
                8,
                kept,
            ),
            (
                "a twin below it",
                Offer::Unit(None, Dip::Ascending),
                16,
                twin,
            ),
        ] {
            let mut holding = keyed();
            admit(&mut holding);
            let _released = released_at(&mut holding, (&offer, SourceRank::from(rank)));
            assert!(
                matches!(
                    holding.keep_in_place(at),
                    Err(KernelError::UnsettledReleases { .. })
                ),
                "{reads} holds the keep"
            );
        }
    }

    /// The ranks between the first members of two admissions: room for the
    /// members of a block.
    const STRIDE: usize = 8;

    /// Admit `source` in `environment`, in order, the members of each
    /// admission ranked from its index times [`STRIDE`] on.
    ///
    /// # Specification
    /// trivial.
    fn admit_spaced(
        environment: &mut Environment,
        source: &[Generated],
    ) -> Admitted
    {
        let mut data = Vec::new();
        let mut origins: Vec<Origin> = Vec::new();
        let mut positions = Vec::with_capacity(source.len());
        let mut scopes = Vec::with_capacity(source.len());
        for (index, admission) in source.iter().enumerate() {
            scopes.push(origins.clone());
            let rank = SourceRank::from(index.saturating_mul(STRIDE));
            let verdict = admit_generated(environment, admission, &data, Some(rank)).ok();
            let admitted = verdict.as_deref().unwrap_or_default();
            for (member, (generated, &position)) in
                members(admission).iter().zip(admitted).enumerate()
            {
                if matches!(*generated, Member::Data(..)) {
                    data.push(position);
                    origins.push(Origin {
                        admission: index,
                        member,
                    });
                }
            }
            positions.push(verdict);
        }
        Admitted { positions, scopes }
    }

    /// The admissions of a source that an edit keeps in order, each read as
    /// its index in the source.
    #[derive(Debug)]
    #[repr(transparent)]
    struct InOrder(BTreeSet<usize>);

    /// The admissions of the source that `edited` keeps in order: the
    /// longest run of edited admissions whose origins ascend. A moved
    /// admission leaves the run, since a readmission keeps the relative order
    /// of every two entries it keeps.
    ///
    /// # Specification
    /// trivial.
    fn kept_in_order(edited: &EditedSource) -> InOrder
    {
        let held: Vec<(usize, usize)> = edited
            .origin
            .iter()
            .enumerate()
            .filter_map(|(index, &from)| from.map(|from| (index, from)))
            .collect();
        // The longest run that ends at each held admission, and the one
        // before it in that run.
        let mut longest: Vec<(usize, Option<usize>)> = Vec::with_capacity(held.len());
        for (at, &(_, from)) in held.iter().enumerate() {
            let best = (0 .. at)
                .filter(|&before| held.get(before).is_some_and(|&(_, earlier)| earlier < from))
                .max_by_key(|&before| longest.get(before).map_or(0, |&(length, _)| length));
            let length = best
                .and_then(|before| longest.get(before))
                .map_or(0, |&(length, _)| length);
            longest.push((length.saturating_add(1), best));
        }
        let mut kept = BTreeSet::new();
        let mut at =
            (0 .. longest.len()).max_by_key(|&at| longest.get(at).map(|&(length, _)| length));
        while let Some(index) = at {
            if let Some(&(_, from)) = held.get(index) {
                let _fresh = kept.insert(from);
            }
            at = longest.get(index).and_then(|&(_, before)| before);
        }
        InOrder(kept)
    }

    /// Check that a readmission that retires the reach of an edit and
    /// nothing else reads as a fresh admission of `edited`, entry by entry,
    /// and exports its bytes. The edited admissions are those the edit
    /// writes, moves or deletes, and each whose data types in scope change.
    /// The readmission retires their reach. It rewrites the rank of each
    /// live entry to the rank of its admission in the edited source. Then it
    /// walks the edited source in order: it keeps each live admission in
    /// place, and it offers each other admission and each one whose keep is
    /// refused. A keep is refused only for what its check reads, and with no
    /// edit nothing is retired or offered.
    ///
    /// # Specification
    /// trivial.
    fn reranks_as_fresh(
        source: &[Generated],
        edited: &EditedSource,
    ) -> Result<(), proptest::test_runner::TestCaseError>
    {
        let EditedSource {
            ref admissions,
            ref origin,
        } = *edited;
        let mut fresh = keyed();
        let Admitted {
            positions: answers,
            scopes: edited_scopes,
        } = admit_spaced(&mut fresh, admissions);
        let mut kept = keyed();
        let Admitted {
            positions: admitted,
            scopes,
        } = admit_source(&mut kept, source);
        let unedited = admissions.len() == source.len()
            && origin
                .iter()
                .enumerate()
                .all(|(index, &from)| from == Some(index));
        let mut image: Vec<Option<usize>> = vec![None; source.len()];
        for (index, &from) in origin.iter().enumerate() {
            if let Some(slot) = from.and_then(|from| image.get_mut(from)) {
                *slot = Some(index);
            }
        }
        let in_order = kept_in_order(edited);
        // An admission of the source stays when the edit keeps it in order
        // and its data types in scope read as the edited source reads them.
        let stays = |from: usize| {
            let Some(index) = image.get(from).copied().flatten()
            else {
                return false;
            };
            let read = scopes.get(from).map(|scope| {
                scope.iter().map(|held| {
                    image
                        .get(held.admission)
                        .copied()
                        .flatten()
                        .map(|admission| Origin {
                            admission,
                            member: held.member,
                        })
                })
            });
            let expected = edited_scopes
                .get(index)
                .map(|scope| scope.iter().copied().map(Some));
            in_order.0.contains(&from)
                && read
                    .zip(expected)
                    .is_some_and(|(read, expected)| read.eq(expected))
        };
        let changed: Vec<ConstantIndex> = admitted
            .iter()
            .enumerate()
            .filter(|&(from, _)| !stays(from))
            .filter_map(|(_, positions)| positions.as_ref())
            .flatten()
            .copied()
            .collect();
        let reach = kept.reach(changed.iter().copied());
        let reached: BTreeSet<ConstantIndex> = reach.iter().copied().collect();
        proptest::prop_assert!(
            changed.iter().all(|position| reached.contains(position)),
            "the reach holds each edited entry"
        );
        let watermark = kept.arena().watermark();
        proptest::prop_assert_eq!(kept.retire(&reach), Ok(()));
        if unedited {
            proptest::prop_assert!(reach.is_empty(), "with no edit, nothing is retired");
        }
        // Each live entry takes the rank of its admission in the edited
        // source.
        let mut ranks: Vec<(ConstantIndex, SourceRank)> = Vec::new();
        for (from, positions) in admitted.iter().enumerate() {
            let (Some(positions), Some(index)) =
                (positions.as_ref(), image.get(from).copied().flatten())
            else {
                continue;
            };
            for (offset, &position) in positions.iter().enumerate() {
                if kept.entries().get(usize::from(position)).is_some() {
                    ranks.push((
                        position,
                        SourceRank::from(index.saturating_mul(STRIDE).saturating_add(offset)),
                    ));
                }
            }
        }
        proptest::prop_assert_eq!(kept.rerank((SourceRank::from(0_usize), &ranks)), Ok(()));
        let mut data: Vec<ConstantIndex> = Vec::new();
        let mut offered = 0_usize;
        for (index, admission) in admissions.iter().enumerate() {
            let from = origin.get(index).copied().flatten();
            let held = from
                .and_then(|from| admitted.get(from).cloned().flatten())
                .filter(|positions| {
                    positions
                        .first()
                        .is_some_and(|&first| kept.entries().get(usize::from(first)).is_some())
                });
            let mut kept_positions = None;
            if let Some(positions) = held {
                let first = positions
                    .first()
                    .copied()
                    .unwrap_or_else(|| ConstantIndex::from(0_usize));
                match kept.keep_in_place(first) {
                    Ok(_kept) => kept_positions = Some(positions),
                    Err(refusal) => {
                        proptest::prop_assert!(
                            !unedited,
                            "with no edit, every keep in place holds: {:?}",
                            refusal
                        );
                        proptest::prop_assert!(
                            matches!(
                                refusal,
                                KernelError::Unkept { .. } | KernelError::UnboundConstant { .. }
                            ),
                            "a keep in place is refused only for what its check reads: {:?}",
                            refusal
                        );
                        proptest::prop_assert_eq!(kept.retire(&[first]), Ok(()));
                    },
                }
            }
            // An admission the kernel refused holds no entry to keep, so it
            // is offered again, as a fresh admission offers it; it counts as
            // no offer of the readmission.
            let refused = from.is_some_and(|from| admitted.get(from).is_some_and(Option::is_none));
            let verdict = kept_positions.or_else(|| {
                if !refused {
                    offered = offered.saturating_add(1);
                }
                let rank = SourceRank::from(index.saturating_mul(STRIDE));
                admit_generated(&mut kept, admission, &data, Some(rank)).ok()
            });
            proptest::prop_assert_eq!(
                verdict.is_some(),
                answers.get(index).is_some_and(Option::is_some),
                "admission {} answers as the fresh admission answers",
                index
            );
            for (member, &position) in members(admission)
                .iter()
                .zip(verdict.as_deref().unwrap_or_default())
            {
                if matches!(*member, Member::Data(..)) {
                    data.push(position);
                }
            }
        }
        if unedited {
            proptest::prop_assert_eq!(offered, 0, "with no edit, nothing is offered");
            proptest::prop_assert_eq!(kept.arena().watermark(), watermark);
        }
        proptest::prop_assert_eq!(read_by_rank(&kept), read_by_rank(&fresh));
        proptest::prop_assert_eq!(
            exported(&kept),
            exported(&fresh),
            "the kept environment exports the bytes of the fresh one"
        );
        let vacant = fresh.entries().admitted() < fresh.entries().len();
        proptest::prop_assert_eq!(
            matches!(fresh.places(), Maybe::Present(_)),
            vacant,
            "a fresh admission builds places exactly when a refusal left a vacancy"
        );
        // The reach of a later edit reads the indexes that the retires swept.
        for position in kept.in_rank_order() {
            proptest::prop_assert_eq!(
                kept.reach([position]).into_vec(),
                forward_reach(kept.entries(), &[position]),
                "the reach of {:?} holds each live entry whose support holds it",
                position
            );
        }
        Ok(())
    }

    /// A generated edit of a source of up to ten admissions.
    ///
    /// # Specification
    /// trivial.
    fn edit() -> impl proptest::strategy::Strategy<Value = Edit>
    {
        use proptest::prelude::Just;
        use proptest::strategy::Strategy as _;
        proptest::prop_oneof![
            ((0_usize .. 10), generated())
                .prop_map(|(at, admission)| Edit::Replaced(at, admission)),
            ((0_usize .. 11), generated())
                .prop_map(|(at, admission)| Edit::Inserted(at, admission)),
            (0_usize .. 10).prop_map(Edit::Deleted),
            ((0_usize .. 10), (0_usize .. 10)).prop_map(|(from, to)| Edit::Moved(from, to)),
            Just(Edit::Unedited),
        ]
    }

    /// #6846: a rank rewrite names each live entry once. A rewrite that
    /// leaves one out, or names one twice, is refused, and the environment
    /// keeps its ranks.
    #[test]
    fn a_rank_rewrite_that_misses_a_live_entry_is_refused_6846()
    {
        let zero = LevelConstant::from(0_u64);
        let mut environment = keyed();
        let a = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Data(zero, vec![])),
            &[],
            None,
        )
        .expect("`a` admits");
        let b = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Axiom(Field::Earlier(0))),
            &a,
            None,
        )
        .expect("`b` admits");
        let (a, b) = (a.first().copied(), b.first().copied());
        let (Some(a), Some(b)) = (a, b)
        else {
            panic!("each admission takes a position");
        };
        let before = read_by_rank(&environment);
        assert_eq!(
            environment.rerank((SourceRank::from(0_usize), &[(b, SourceRank::from(9_usize))])),
            Err(KernelError::Unkept {
                position: a,
                refusal: crate::error::KeepRefusal::Ranks,
            }),
            "the rewrite leaves `a` out"
        );
        assert_eq!(
            environment.rerank((SourceRank::from(0_usize), &[
                (a, SourceRank::from(4_usize)),
                (b, SourceRank::from(9_usize)),
                (a, SourceRank::from(5_usize)),
            ])),
            Err(KernelError::Unkept {
                position: a,
                refusal: crate::error::KeepRefusal::Ranks,
            }),
            "the rewrite names `a` twice"
        );
        assert_eq!(
            environment.rerank((SourceRank::from(0_usize), &[
                (a, SourceRank::from(4_usize)),
                (b, SourceRank::from(4_usize))
            ])),
            Err(KernelError::RankTaken {
                rank: SourceRank::from(4_usize),
                by: a,
            }),
            "the rewrite gives two entries one rank"
        );
        assert_eq!(
            read_by_rank(&environment),
            before,
            "a refused rewrite changes nothing"
        );
        assert_eq!(
            environment.rerank((SourceRank::from(0_usize), &[
                (a, SourceRank::from(4_usize)),
                (b, SourceRank::from(9_usize))
            ])),
            Ok(())
        );
        assert_eq!(
            read_by_rank(&environment)
                .iter()
                .map(|&(rank, ..)| rank)
                .collect::<Vec<_>>(),
            vec![SourceRank::from(4_usize), SourceRank::from(9_usize)],
            "each entry holds its new rank"
        );
        assert_eq!(environment.keep_in_place(b).map(CheckedId::position), Ok(b));
    }

    /// #7235: a rank rewrite above a floor keeps the rank of each entry below
    /// it, as a readmission that shares its leading run keeps the run's ranks.
    /// `a`, `b` and `c` take the ranks 0, 1 and 2, and `b` names `a`. A
    /// rewrite that names an entry below the floor, or gives a rank below it,
    /// is refused. So is one that leaves out an entry at or above the floor,
    /// and a refused rewrite changes nothing.
    #[test]
    fn a_rank_rewrite_above_a_floor_keeps_each_rank_below_it_7235()
    {
        let data = |level: u64| Generated::Lone(Member::Data(LevelConstant::from(level), vec![]));
        let mut environment = keyed();
        let a = admit_generated(&mut environment, &data(0), &[], None).expect("`a` admits");
        let b = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Axiom(Field::Earlier(0))),
            &a,
            None,
        )
        .expect("`b` admits");
        let c = admit_generated(&mut environment, &data(1), &[], None).expect("`c` admits");
        let (Some(&b), Some(&c)) = (b.first(), c.first())
        else {
            panic!("each admission takes a position");
        };
        let rank = SourceRank::from;
        let before = read_by_rank(&environment);
        let unkept = |position| {
            Err(KernelError::Unkept {
                position,
                refusal: crate::error::KeepRefusal::Ranks,
            })
        };
        assert_eq!(
            environment.rerank((rank(2_usize), &[(b, rank(5_usize)), (c, rank(9_usize))])),
            unkept(b),
            "`b` ranks below the floor"
        );
        assert_eq!(
            environment.rerank((rank(2_usize), &[(c, rank(1_usize))])),
            unkept(c),
            "the rank 1 is below the floor"
        );
        assert_eq!(
            environment.rerank((rank(1_usize), &[(c, rank(9_usize))])),
            unkept(b),
            "`b` ranks at the floor, and the rewrite leaves it out"
        );
        assert_eq!(
            read_by_rank(&environment),
            before,
            "a refused rewrite changes nothing"
        );
        assert_eq!(
            environment.rerank((rank(2_usize), &[(c, rank(9_usize))])),
            Ok(())
        );
        assert_eq!(
            read_by_rank(&environment)
                .iter()
                .map(|&(rank, ..)| rank)
                .collect::<Vec<_>>(),
            vec![rank(0_usize), rank(1_usize), rank(9_usize)],
            "`a` and `b` keep their ranks below the floor, and `c` takes the rank 9"
        );
        assert_eq!(
            environment.keep_in_place(b).map(CheckedId::position),
            Ok(b),
            "`b` reads `a` in the same order, so it keeps its key"
        );
    }

    /// #6846: while a next rank is set, each admission staged with no rank
    /// takes the next rank, a block one rank for each member, so a crossing
    /// ranks at its place between kept entries. With no next rank, an
    /// admission ranks past every live entry, as before.
    #[test]
    fn a_crossing_at_the_next_rank_ranks_at_its_place_6846()
    {
        let zero = LevelConstant::from(0_u64);
        let mut environment = keyed();
        let lone = Generated::Lone(Member::Data(zero, vec![]));
        for rank in [0_usize, 16] {
            admit_generated(&mut environment, &lone, &[], Some(SourceRank::from(rank)))
                .expect("a kept entry admits at its rank");
        }
        environment.ranking_from(SourceRank::from(8_usize));
        admit_generated(&mut environment, &lone, &[], None).expect("a crossing admits");
        admit_generated(
            &mut environment,
            &Generated::Block(vec![Member::Data(zero, vec![]), Member::Data(zero, vec![])]),
            &[],
            None,
        )
        .expect("a block crosses");
        environment.ranking_past();
        admit_generated(&mut environment, &lone, &[], None).expect("a fresh admission admits");
        assert_eq!(
            read_by_rank(&environment)
                .iter()
                .map(|&(rank, ..)| usize::from(rank))
                .collect::<Vec<_>>(),
            vec![0, 8, 9, 10, 16, 17],
            "the crossings take the next ranks, the last admission the rank past them all"
        );
    }

    /// #6846: an entry outside the reach that reads a retired entry is
    /// refused in place, as a fresh admission refuses a reference to a
    /// declaration it does not hold. `b` names `a`, and the readmission
    /// retires `a` alone.
    #[test]
    fn an_entry_that_reads_a_retired_one_is_refused_in_place_6846()
    {
        let zero = LevelConstant::from(0_u64);
        let mut environment = keyed();
        let a = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Data(zero, vec![])),
            &[],
            None,
        )
        .expect("`a` admits");
        let b = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Axiom(Field::Earlier(0))),
            &a,
            None,
        )
        .expect("`b` admits");
        let (Some(&a), Some(&b)) = (a.first(), b.first())
        else {
            panic!("each admission takes a position");
        };
        assert_eq!(environment.retire(&[a]), Ok(()));
        assert_eq!(
            environment.keep_in_place(b),
            Err(KernelError::UnboundConstant { index: a }),
            "`b` reads the retired `a`"
        );
        assert_eq!(
            environment.keep_in_place(a),
            Err(KernelError::Retired { position: a }),
            "a retired entry is not kept in place"
        );
    }

    /// #7196: a seed `s` ranks past the next rank, and its reader `b` ranks
    /// above it. `s` takes the next rank, the next rank moves one past it,
    /// and `b` keeps its key in place. An entry below the next rank is
    /// refused, and so is each entry while no next rank is set.
    #[test]
    fn a_seed_takes_the_next_rank_below_its_first_reader_7196()
    {
        let zero = LevelConstant::from(0_u64);
        let mut environment = keyed();
        let data = Generated::Lone(Member::Data(zero, vec![]));
        let a = admit_generated(
            &mut environment,
            &data,
            &[],
            Some(SourceRank::from(0_usize)),
        )
        .expect("`a` admits");
        let s = admit_generated(
            &mut environment,
            &data,
            &[],
            Some(SourceRank::from(16_usize)),
        )
        .expect("`s` admits");
        let b = admit_generated(
            &mut environment,
            &Generated::Lone(Member::Axiom(Field::Earlier(0))),
            &s,
            Some(SourceRank::from(24_usize)),
        )
        .expect("`b` admits");
        let (Some(&a), Some(&s), Some(&b)) = (a.first(), s.first(), b.first())
        else {
            panic!("each admission takes a position");
        };
        assert_eq!(
            environment.take_next_rank(s),
            Err(KernelError::Unkept {
                position: s,
                refusal: crate::error::KeepRefusal::NextRank,
            }),
            "no next rank is set"
        );
        environment.ranking_from(SourceRank::from(8_usize));
        assert_eq!(
            environment.take_next_rank(a),
            Err(KernelError::Unkept {
                position: a,
                refusal: crate::error::KeepRefusal::NextRank,
            }),
            "`a` ranks below the next rank"
        );
        assert_eq!(environment.take_next_rank(s), Ok(()));
        assert_eq!(
            read_by_rank(&environment)
                .iter()
                .map(|&(rank, ..)| usize::from(rank))
                .collect::<Vec<_>>(),
            vec![0, 8, 24],
            "`s` holds the rank that was next"
        );
        assert_eq!(
            environment.next_rank(),
            Maybe::Present(SourceRank::from(9_usize))
        );
        assert_eq!(
            environment.keep_in_place(b).map(CheckedId::position),
            Ok(b),
            "`b` reads its input in the same order, so it keeps its key"
        );
    }

    /// A source that answers one receipt for each key its records hold.
    #[derive(Debug)]
    #[repr(transparent)]
    struct Held(alloc::sync::Arc<crate::verdict::StoredReceipt>);

    impl crate::verdict::VerdictSource for Held
    {
        /// The receipt, when one of its records holds `key`.
        ///
        /// # Specification
        /// trivial.
        fn receipts(
            &self,
            key: crate::verdict::VerdictKey,
        ) -> &[alloc::sync::Arc<crate::verdict::StoredReceipt>]
        {
            if self.0.records().iter().any(|record| record.key() == key) {
                core::slice::from_ref(&self.0)
            }
            else {
                &[]
            }
        }
    }

    /// #6846: an admission after a retirement is recalled by its entry key
    /// alone. `a`, `b` and `d` are equal data declarations, so the entry key
    /// of each counts the ones ranked below it. One environment admits `d`
    /// with `b` live and records it. One that retired `b` admits `d` at the
    /// same rank: its entry key counts one equal declaration less, and it
    /// recalls nothing. The environment that recorded `d` recalls it.
    #[test]
    fn an_admission_after_a_retirement_recalls_by_its_entry_key_alone_6846()
    {
        let signer = crate::verdict::KernelSigner::from([7_u8; 32]);
        let data = Generated::Lone(Member::Data(LevelConstant::from(0_u64), vec![]));
        let d = |environment: &mut Environment| {
            admit_generated(environment, &data, &[], Some(SourceRank::from(10_usize)))
                .expect("`d` admits")
        };
        let mut base = keyed();
        let _a = admit_generated(&mut base, &data, &[], None).expect("`a` admits");
        let b = admit_generated(&mut base, &data, &[], None).expect("`b` admits");
        let Some(&b) = b.first()
        else {
            panic!("`b` takes a position");
        };
        let mut recording = base.handed_on();
        let _d = d(&mut recording);
        let Maybe::Present(receipt) = recording.receipt(&signer)
        else {
            panic!("a keyed environment gives a receipt");
        };
        let held: alloc::sync::Arc<dyn crate::verdict::VerdictSource> =
            alloc::sync::Arc::new(Held(alloc::sync::Arc::new(receipt)));
        let mut again = base.handed_on();
        again.reading(alloc::sync::Arc::clone(&held));
        let _d = d(&mut again);
        assert_eq!(
            usize::from(again.recalls()),
            1,
            "the environment that recorded `d` recalls it"
        );
        let mut retired = base.handed_on();
        assert_eq!(retired.retire(&[b]), Ok(()));
        retired.reading(held);
        let _d = d(&mut retired);
        assert_eq!(
            usize::from(retired.recalls()),
            0,
            "after the retirement, the entry key of `d` is another and recalls nothing"
        );
    }

    proptest::proptest! {
        #![proptest_config(proptest::prelude::ProptestConfig::with_cases(512))]

        /// An environment that keeps its content outcomes gives every
        /// admission the verdict that a fresh session gives. A kept outcome
        /// answers only under its own parameters. The generated environments
        /// leave a vacancy at each position that a refused declaration or
        /// block takes.
        #[test]
        fn kept_outcomes_leave_every_verdict_as_fresh_sessions_give(
            admissions in proptest::collection::vec(generated(), 1 .. 12),
        ) {
            let mut kept = Environment::new();
            let mut fresh = Environment::new();
            let mut data: Vec<ConstantIndex> = Vec::new();
            for admission in &admissions {
                let verdict = admit_generated(&mut kept, admission, &data, None);
                // A clone keeps no session. So the reference checks each
                // admission on an empty one.
                fresh = fresh.clone();
                let reference = admit_generated(&mut fresh, admission, &data, None);
                proptest::prop_assert_eq!(&reference, &verdict);
                let members = match *admission {
                    Generated::Lone(ref member) => core::slice::from_ref(member),
                    Generated::Block(ref members) => members.as_slice(),
                };
                for (member, position) in members.iter().zip(verdict.unwrap_or_default()) {
                    if matches!(*member, Member::Data(..)) {
                        data.push(position);
                    }
                }
            }
        }

        /// #6621: the reach of an edit, read backward through the reverse
        /// index, equals the entries whose support holds an edited entry,
        /// found forward. The refused declarations and blocks roll back their
        /// rows before the later admissions take them.
        #[test]
        fn the_reach_holds_each_entry_whose_support_holds_an_edited_one(
            admissions in proptest::collection::vec(generated(), 1 .. 16),
            edited in proptest::collection::vec(0_usize .. 24, 0 .. 4),
        ) {
            let mut environment = Environment::new();
            let mut data: Vec<ConstantIndex> = Vec::new();
            for admission in &admissions {
                let verdict = admit_generated(&mut environment, admission, &data, None);
                let members = match *admission {
                    Generated::Lone(ref member) => core::slice::from_ref(member),
                    Generated::Block(ref members) => members.as_slice(),
                };
                for (member, position) in members.iter().zip(verdict.unwrap_or_default()) {
                    if matches!(*member, Member::Data(..)) {
                        data.push(position);
                    }
                }
            }
            let edited: Vec<ConstantIndex> = edited.into_iter().map(ConstantIndex::from).collect();
            let found = forward_reach(environment.entries(), &edited);
            proptest::prop_assert_eq!(&*environment.reach(edited.iter().copied()), found.as_slice());
        }

        /// #6846: a readmission that retires the reach of an edit and
        /// nothing else, rewrites the rank of each live entry and keeps it in
        /// place, reads as a fresh admission of the edited source, entry by
        /// entry, and exports its bytes, for each class of edit.
        #[test]
        fn a_reranked_environment_reads_as_a_fresh_admission_6846(
            source in proptest::collection::vec(generated(), 1 .. 10),
            edit in edit(),
        ) {
            reranks_as_fresh(&source, &edited_by(&source, &edit))?;
        }
    }

    /// The edited entries below the count of `entries`, with each entry whose
    /// support holds one of them, found forward and ascending. An entry's
    /// support is the closure of its direct references, with each type of
    /// words admitted before it over each position that the closure holds.
    ///
    /// # Specification
    /// trivial.
    fn forward_reach(
        entries: &Entries,
        edited: &[ConstantIndex],
    ) -> Vec<ConstantIndex>
    {
        let length = usize::from(entries.len());
        // A vacancy stands in no reach, as a retired entry does not.
        let mut reached: BTreeSet<ConstantIndex> = edited
            .iter()
            .copied()
            .filter(|&position| entries.get(usize::from(position)).is_some())
            .collect();
        let mut support = BTreeSet::new();
        let mut pending: Vec<ConstantIndex> = Vec::new();
        loop {
            let before = reached.len();
            for (at, entry) in (0 .. length).filter_map(|at| Some((at, entries.get(at)?))) {
                let consumer = ConstantIndex::from(at);
                if reached.contains(&consumer) {
                    continue;
                }
                support.clear();
                pending.clear();
                pending.extend_from_slice(entry.references());
                while let Some(position) = pending.pop() {
                    if !support.insert(position) {
                        continue;
                    }
                    if let Some(held) = entries.get(usize::from(position)) {
                        pending.extend(held.references().iter().copied());
                    }
                    let over = entries.presentations().over(position);
                    pending.extend(over.filter(|&words| words < consumer));
                }
                if !support.is_disjoint(&reached) {
                    let _fresh = reached.insert(consumer);
                }
            }
            if reached.len() == before {
                return reached.into_iter().collect();
            }
        }
    }

    /// Stage the unit definition `() : 1` in `environment`, or `c : 1` when
    /// `named` is the constant `c`.
    ///
    /// # Specification
    /// trivial.
    fn unit_definition(
        environment: &mut Environment,
        named: Option<ConstantIndex>,
    ) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = match named {
            Some(constant) => staging.arena().value_constant(constant),
            None => staging.arena().value_unit(),
        };
        staging.def(LevelSignature::monomorphic(), declared, body)
    }

    /// #2797: a definition naming an earlier one checks under the support its
    /// content names. The same check under a support that misses that edge
    /// reads the earlier entry outside its support, and the declaration is
    /// refused at that position.
    #[test]
    fn a_read_outside_the_support_refuses_the_declaration_2797()
    {
        let mut environment = Environment::new();
        let staged = unit_definition(&mut environment, None);
        let named = environment
            .add_decl(staged)
            .expect("a unit definition admits")
            .position();
        let reading = unit_definition(&mut environment, Some(named));
        let levels = crate::levels::LevelContext::admit(
            gandr_kernel_term::LevelParamCount::from(0_u32),
            Vec::new(),
        )
        .expect("no level parameter admits");
        let check = |environment: &mut Environment, roots: &[ConstantIndex]| {
            let taken = crate::admitted::Tally::new();
            // The check runs on copies of the arena and of the session, so the
            // environment stays as the admission below finds it.
            environment.within_view(
                (roots, gandr_kernel_term::SourceRank::ABOVE),
                (&levels, &taken),
                |arena, judgement, _session| {
                    crate::check::check_declaration(
                        &mut arena.clone(),
                        judgement,
                        reading.declaration(),
                        &mut crate::support::SupportContext::new(),
                        &mut ExpansionCensus::new(),
                    )
                },
            )
        };
        let roots = super::references(&environment.arena, reading.declaration());
        assert_eq!(&*roots, &[named], "the definition names the one before it");
        assert!(
            check(&mut environment, &roots).is_ok(),
            "the check reads only what the content names"
        );
        assert_eq!(
            check(&mut environment, &[]).err(),
            Some(KernelError::OutsideSupport { position: named }),
            "a support that misses the edge refuses the read at its position"
        );
        assert_eq!(
            environment
                .add_decl(reading)
                .map(super::CheckedId::position)
                .map(usize::from),
            Ok(1_usize),
            "the admission opens the support its content names"
        );
    }

    /// #2797: the admission of one definition reads the entries its content
    /// reaches and no other. So its count of entries read is the same after
    /// 10, 1,000 and 10,000 unrelated definitions.
    #[test]
    fn an_admission_reads_as_many_entries_after_many_unrelated_ones_2797()
    {
        let reads = |unrelated: usize| {
            let mut environment = Environment::new();
            let staged = unit_definition(&mut environment, None);
            let named = environment
                .add_decl(staged)
                .expect("a unit definition admits")
                .position();
            for _ in 0 .. unrelated {
                let staged = unit_definition(&mut environment, None);
                let _admitted = environment
                    .add_decl(staged)
                    .expect("an unrelated definition admits");
            }
            let reading = unit_definition(&mut environment, Some(named));
            let _admitted = environment
                .add_decl(reading)
                .expect("a definition naming the first admits");
            gandr_kernel_core_base::fixture::reads(&environment.entries)
        };
        let few = reads(10);
        assert_eq!(
            few,
            gandr_kernel_term::ArenaLength::from(1_usize),
            "the definition reads the one entry it names"
        );
        assert_eq!(few, reads(1_000));
        assert_eq!(few, reads(10_000));
    }

    /// #6961: a reflexivity at a held point presents as the empty word of a
    /// type of words only when the support of the check names that type. The
    /// guard that asks for such a type reads the types through the support,
    /// so a type outside it answers nothing, and the reflexivity stays.
    #[test]
    fn a_reflexivity_reads_no_type_of_words_outside_its_support_6961()
    {
        use gandr_kernel_conversion_trace::ConversionDecision;
        use gandr_kernel_term::ConstructorTag;
        use gandr_kernel_term::FreeCell;
        use gandr_kernel_term::FreeCells;
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::RuleNode;

        use crate::replay::EngineClaim;
        use crate::replay::KernelVerdict;
        use crate::replay::ReplayBudget;
        use crate::replay::ReplayNode;
        use crate::replay::ReplaySides;
        use crate::replay::Unfoldable;
        use crate::replay::Unfoldings;

        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let staged = staging.data(
            LevelSignature::monomorphic(),
            Vec::new(),
            vec![vec![]],
            kind,
        );
        let sort = environment
            .add_decl(staged)
            .expect("the one-point sort admits")
            .position();
        let point = || -> alloc::boxed::Box<[RuleNode]> {
            [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
        };
        let cells = FreeCells::new(sort, vec![FreeCell::new(point(), point())]);
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(1_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                vec![vec![], vec![own], vec![own]],
                kind,
            )
            .presented(Presentation::words(cells));
        let words = environment
            .add_decl(staged)
            .expect("the loop's words admit")
            .position();
        // `here(⟨ident(Base)⟩)` against the empty word, with `ident` the
        // identity on the sort at the position past the entries, read under
        // the support that `roots` start.
        let presents = |environment: &mut Environment, roots: &[ConstantIndex]| {
            let mut arena = environment.arena.clone();
            let occurrence = arena.value_variable(DeBruijnIndex::from(0_u32));
            let returned = arena.computation_return(occurrence);
            let lambda = arena.computation_lambda(returned);
            let ident = arena.value_thunk(lambda);
            let carrier = arena.value_type_data(sort, Vec::new());
            let base =
                arena.value_constructor(sort, carrier, ConstructorTag::from(0_usize), Vec::new());
            let head = arena.value_constant(ConstantIndex::from(2_usize));
            let forced = arena.computation_force(head);
            let applied = arena.computation_application(forced, base);
            let held = arena.value_returned(applied);
            let reflexivity = arena.value_here(held);
            let own = arena.value_type_data(words, Vec::new());
            let empty =
                arena.value_constructor(words, own, ConstructorTag::from(0_usize), Vec::new());
            let mut view = environment.entries.view();
            let end = view.len();
            view.open(roots.iter().copied(), (SourceRank::ABOVE, end));
            let unfoldings = Unfoldings::admitted(&view)
                .extended(vec![Unfoldable::Body(ident)])
                .presenting(view.presentations().clone());
            let verdict = crate::replay::replay(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(reflexivity, empty),
                EngineClaim::Convertible,
                core::iter::once(ConversionDecision::ComparedShared {
                    left: ReplayNode::Other,
                    right: ReplayNode::Other,
                }),
                ReplayBudget::default(),
            );
            drop(unfoldings);
            let outside = view.close();
            environment.entries.restore(view);
            super::supported(Ok(verdict), outside)
        };
        assert_eq!(
            presents(&mut environment, &[sort, words]),
            Ok(KernelVerdict::Convertible),
            "a type of words that the support names presents the reflexivity"
        );
        assert_ne!(
            presents(&mut environment, &[]),
            Ok(KernelVerdict::Convertible),
            "a type of words outside the support answers no guard"
        );
    }
}
