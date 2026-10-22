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
//! `add_decl` reads content-end on entry, so the checker's synthesized
//! intermediates allocate strictly after it. The checker runs, then the arena
//! is truncated: to **content-end** on success, dropping intermediates and
//! keeping content, or to **content-start** on rejection, dropping both.
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

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ArenaWatermark;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;

use crate::check;
use crate::error::KernelError;
use crate::levels::LevelContext;

/// An unforgeable receipt that a declaration was admitted, naming its position.
///
/// Minted only inside this crate, so a consumer holding one holds a fact rather
/// than a claim.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CheckedId(ConstantIndex);

impl CheckedId
{
    /// Mint a receipt for an admitted position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new(position: ConstantIndex) -> Self
    {
        Self(position)
    }

    /// The declaration's admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn position(self) -> ConstantIndex
    {
        self.0
    }
}

/// How a declaration was admitted: through the checked choke point, or through
/// the warned bypass. A single bit — never a trust lattice.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Admission
{
    /// Admitted through [`Environment::add_decl`], fully checked.
    Checked,
    /// Admitted through [`Environment::add_decl_unchecked`], trusted and
    /// tracked.
    Unchecked,
}

/// A declaration whose content has been minted, paired with the watermark its
/// content began at.
///
/// The pairing is what lets a rejection roll back exactly this declaration's
/// content and no more. It exists as its own type because the watermark is
/// meaningful only against the arena that produced it, and a bare declaration
/// would carry no way to say so.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StagedDeclaration
{
    /// Where this declaration's content begins in the environment's arena.
    content_start: ArenaWatermark,
    /// The declaration itself.
    declaration: Declaration,
}

impl StagedDeclaration
{
    /// The declaration, for a caller that inspects it before offering it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &Declaration
    {
        &self.declaration
    }

    /// This staged definition carrying `related` as the path endpoints its
    /// type conversions relate, its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: every pair's roots were minted into the arena this
    ///   declaration was staged into, no earlier than its content start.
    /// - ensures: the declaration as [`Declaration::relating`] leaves it, at
    ///   the same content start: a definition carries exactly `related`, any
    ///   other declaration is unchanged.
    /// - provides: how a producer attaches the dialogues its conversion kept
    ///   before offering the definition; the choke point replays them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a relating definition admits by its dialogue and the
    ///   same definition without it is refused.
    /// - witness: `element_identity::tests::a_definition_relating_compound_endpoints_admits_274`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. }), self.declaration.related().len(), related.len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.related().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn relating(
        self,
        related: Vec<RelatedEndpoints>,
    ) -> Self
    {
        Self {
            declaration: self.declaration.relating(related),
            ..self
        }
    }

    /// This staged definition carrying `laws` as the laws its folds rest on,
    /// its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the choke point instantiates each law where a fold
    ///   needs it.
    /// - ensures: the declaration as [`Declaration::lawful`] leaves it, at the
    ///   same content start: a definition carries exactly `laws`, any other
    ///   declaration is unchanged.
    /// - provides: how a producer attaches a fold's laws before offering the
    ///   definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold admits on its laws and is refused without
    ///   them.
    /// - witness: `tests::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. }), self.declaration.laws().len(), laws.len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.laws().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn lawful(
        self,
        laws: Vec<ConstantIndex>,
    ) -> Self
    {
        Self {
            declaration: self.declaration.lawful(laws),
            ..self
        }
    }

    /// This staged definition carrying `rules` as the rules of the operation
    /// it lowered from, its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the choke point decides that the rules converge.
    /// - ensures: the declaration as [`Declaration::ruled`] leaves it, at the
    ///   same content start: a definition carries exactly `rules`, any other
    ///   declaration is unchanged.
    /// - provides: how a producer attaches an operation's rules before offering
    ///   the definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — converging rules admit and a forged pair is refused.
    /// - witness: `ruled::tests::rules_over_the_environment_admit_and_a_forged_pair_is_refused`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. }), self.declaration.operation_rules().rules().len(), rules.rules().len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.operation_rules().rules().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn ruled(
        self,
        rules: gandr_kernel_term::OperationRules,
    ) -> Self
    {
        Self {
            declaration: self.declaration.ruled(rules),
            ..self
        }
    }

    /// This staged definition quantified over `stages`, its content start
    /// and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — admission refuses a mark the declared type does
    ///   not place.
    /// - ensures: the declaration as [`Declaration::staged`] leaves it, at the
    ///   same content start: a definition carries exactly `stages`, any other
    ///   declaration is unchanged.
    /// - provides: how a producer attaches a stage signature before offering
    ///   the definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a helper typed at a stage takes a recursion's claim
    ///   in the kernel as in the checker.
    /// - witness: `tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. }), self.declaration.stages().bounds().len(), stages.bounds().len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.stages().bounds().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn staged(
        self,
        stages: gandr_kernel_term::StageSignature,
    ) -> Self
    {
        Self {
            declaration: self.declaration.staged(stages),
            ..self
        }
    }

    /// This staged data declaration carrying `presentation` as the rules
    /// rewriting its constructor terms, its content start and content
    /// unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the choke point checks the rules against the
    ///   constructor table.
    /// - ensures: the declaration as [`Declaration::presented`] leaves it, at
    ///   the same content start: a data declaration carries exactly
    ///   `presentation`, any other declaration is unchanged.
    /// - provides: how a producer attaches a presented type's rules before
    ///   offering the declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle admits with its rules and normalizes its
    ///   words by them.
    /// - witness: `presented::tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Data { .. }), self.declaration.presentation().rules().len(), presentation.rules().len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.presentation().rules().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn presented(
        self,
        presentation: gandr_kernel_term::Presentation,
    ) -> Self
    {
        Self {
            declaration: self.declaration.presented(presentation),
            ..self
        }
    }

    /// This staged declaration with an abstract type's elements related by
    /// `interface`.
    ///
    /// # Specification
    /// - requires: nothing; the admission checks the interface.
    /// - ensures: the content region is unchanged; an abstract type carries
    ///   `interface`, any other declaration is unchanged.
    /// - provides: how a producer states an atom's element relation and its
    ///   reflexivity before offering the declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an interfaced atom admits where its interface checks
    ///   and its bridges read the relation.
    /// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
    #[spec(
        captures: entry = self.content_start,
        ensures: |ret| ret.content_start == entry,
    )]
    #[inline]
    #[must_use]
    pub fn interfaced(
        self,
        interface: gandr_kernel_term::AtomInterface,
    ) -> Self
    {
        Self {
            declaration: self.declaration.interfaced(interface),
            ..self
        }
    }
}

/// Whether an environment holds staged, unresolved content above some mark.
///
/// A nominal answer rather than a bare boolean because it is the input to a
/// refusal: the two cases are "a rollback to this mark would destroy content a
/// producer still holds" and "it would not", and those are not interchangeable
/// with any other yes-or-no in this module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OutstandingContent
{
    /// Some staged, unresolved declaration's content sits above the mark.
    Present,
    /// Nothing staged and unresolved sits above the mark.
    Absent,
}

/// How many staged, unresolved marks sit above the one a refusal is about.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OutstandingCount(usize);

impl From<usize> for OutstandingCount
{
    /// The count of `count` outstanding marks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<OutstandingCount> for usize
{
    /// How many outstanding marks `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: OutstandingCount) -> Self
    {
        count.0
    }
}

/// The content-start marks of declarations staged into the arena and not yet
/// resolved by an admission, a bypass, or an abandonment.
///
/// A multiset rather than a set: sessions that reuse already-minted roots can
/// finish without moving the watermark. Each retains an independent claim,
/// and resolving one occurrence must not resolve every equal occurrence.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct StagedMarks
{
    /// The outstanding marks, in registration order.
    marks: Vec<ArenaWatermark>,
}

impl StagedMarks
{
    /// Record a mark as outstanding.
    ///
    /// # Specification
    /// - requires: nothing; a mark already held is recorded a second time
    ///   rather than merged, since two sessions can legitimately share one
    ///   mark.
    /// - ensures: one more occurrence of `mark` is outstanding, in registration
    ///   order, and every other mark is untouched.
    /// - provides: the registration every staging session performs, whose
    ///   occurrence a later resolution removes exactly one of.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four registrations, including a repeated middle mark,
    ///   retain insertion order and are resolved one occurrence at a time. A
    ///   registration appends, so the predicate reads the length and the last
    ///   mark; the witness checks the whole order and every multiplicity.
    /// - witness: `env::tests::registration_resolution_preserves_multiplicity_and_order`
    #[spec(
        captures: [entry_len = self.marks.len()],
        ensures: self.marks.len().checked_sub(1_usize) == Some(entry_len)
            && self.marks.last() == Some(&mark)
    )]
    #[inline]
    fn register(
        &mut self,
        mark: ArenaWatermark,
    )
    {
        self.marks.push(mark);
    }

    /// Resolve one occurrence of `mark`, if it is held.
    ///
    /// # Specification
    /// - requires: nothing; an absent mark leaves the multiset unchanged.
    /// - ensures: the first occurrence of a held mark is removed and every
    ///   other occurrence retains its order. An equal occurrence belonging to
    ///   another session remains held until a separate resolution.
    /// - provides: the resolution every admission, bypass and abandonment
    ///   performs.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated and absent resolutions distinguish removal
    ///   of one occurrence from removal of all equal marks or another mark. The
    ///   predicate checks counts; the witness also checks the exact order.
    /// - witness: `env::tests::registration_resolution_preserves_multiplicity_and_order`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body searches the marks for the first occurrence and shifts the rest; the check counts occurrences before and after"
        )
    )]
    #[spec(
        captures: [entry_len = self.marks.len(), entry_count = self.marks.iter().filter(|&&held| held == mark).count()],
        ensures: self.marks.len() == entry_len.saturating_sub(usize::from(entry_count != 0_usize))
            && self.marks.iter().filter(|&&held| held == mark).count() == entry_count.saturating_sub(1_usize)
    )]
    fn resolve(
        &mut self,
        mark: ArenaWatermark,
    )
    {
        if let Some(position) = self.marks.iter().position(|held| *held == mark) {
            let _removed = self.marks.remove(position);
        }
    }

    /// How many outstanding marks sit strictly above `mark` in some family.
    ///
    /// "Above" is **componentwise**, not lexicographic, because truncation is
    /// per family: a mark whose computation count exceeds this one's has
    /// content a truncation would destroy however the two order as tuples. The
    /// test is expressed through the watermark's own clamp — the componentwise
    /// minimum of the candidate and the floor differs from the candidate
    /// exactly when some family of the candidate exceeds the floor — so this
    /// module reads no family length and the watermark keeps its fields.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| usize::from(ret) == self.marks.iter().filter(|&&held|
    ///   held.clamped_into(ArenaWatermark::default(), mark) != held).count()` —
    ///   the number of held marks strictly above `mark` componentwise; equal
    ///   and lower marks contribute zero.
    /// - provides: the quantity the outstanding-content refusal reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the componentwise comparison,
    ///   separated by a mark below (counted), a mark equal (not counted), and a
    ///   mark above (not counted), each asserted as an exact count.
    /// - witness: `env::tests::marks_above_are_counted_componentwise`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body clamps every held mark once, as the check does"
        )
    )]
    #[spec(ensures: |ret| usize::from(ret) == self.marks.iter().filter(|&&held| held.clamped_into(ArenaWatermark::default(), mark) != held).count())]
    fn above(
        &self,
        mark: ArenaWatermark,
    ) -> OutstandingCount
    {
        let mut found: usize = 0;
        for &held in &self.marks {
            if held.clamped_into(ArenaWatermark::default(), mark) != held {
                // At most marks.len() distinct entries contribute to this count.
                found = usize::from(arith::add(
                    arith::Int::from(found),
                    arith::Int::from(1_usize),
                ));
            }
        }
        OutstandingCount(found)
    }
}

/// The exclusively borrowed final registration of a live staging session.
///
/// While this borrow lives, no other registration can be appended or resolved.
/// Dropping it removes the final entry; a finisher suppresses that destructor
/// when ownership of the claim passes to a staged declaration.
#[repr(transparent)]
struct StagingClaim<'env>
{
    /// The nonempty multiset whose final entry belongs to this session.
    outstanding: &'env mut StagedMarks,
}

impl Drop for StagingClaim<'_>
{
    /// Release the session's final registration without disturbing its prefix.
    ///
    /// # Specification
    /// - requires: the exclusively borrowed multiset is nonempty; construction
    ///   registered this session last and the borrow prevents intervening
    ///   edits.
    /// - ensures: the final registration is removed and the preceding sequence
    ///   is unchanged. The predicate checks its length and final endpoint.
    /// - provides: automatic claim release on ordinary and unwinding scope
    ///   exit.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — explicit discard and implicit scope exit both
    ///   preserve an earlier staged declaration's claim and permit its later
    ///   admission. The witnesses cover ordinary scope exit, not every
    ///   unwinding context.
    /// - witness: `env::tests::implicit_staging_drop_releases_its_claim`
    /// - witness: `env::tests::an_abandoned_staging_releases_its_claim`
    #[spec(
        requires: !self.outstanding.marks.is_empty(),
        captures: [
            entry_len = self.outstanding.marks.len(),
            prefix_last = self.outstanding.marks.len().checked_sub(2_usize)
                .and_then(|index| self.outstanding.marks.get(index)).copied()
        ],
        ensures: self.outstanding.marks.len() == entry_len.saturating_sub(1_usize)
            && self.outstanding.marks.last().copied() == prefix_last
    )]
    fn drop(&mut self)
    {
        let _released = self.outstanding.marks.pop();
    }
}

/// A borrowing staging session for one declaration's content.
///
/// It wraps the term crate's builder so that finishing yields a
/// [`StagedDeclaration`] carrying the content-start watermark, and it registers
/// that watermark as outstanding while the session is live. Abandoning it — a
/// scope exit on a failure path, or an explicit [`Self::discard`] — rolls the
/// arena back and resolves the mark, so a lowering that fails partway leaves
/// neither an orphan nor a claim on the arena.
///
/// A finisher keeps the mark outstanding, because the content it produced is
/// still in the arena and the [`StagedDeclaration`] that names it is live. That
/// mark is resolved by [`Environment::add_decl`],
/// [`Environment::add_decl_unchecked`], or [`Environment::abandon`].
pub struct Staging<'env>
{
    /// The wrapped builder, which owns the rollback.
    builder: DeclarationBuilder<'env>,
    /// The final registration, dropped after the builder rolls back the arena.
    claim: StagingClaim<'env>,
}

impl<'env> Staging<'env>
{
    /// Finalize a nominal data signature while retaining its staging claim.
    ///
    /// # Specification
    /// - requires: this session owns the last outstanding staging mark.
    /// - ensures: the mark remains outstanding and the signature is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — data admission rejects a malformed signature without
    ///   retaining its nodes.
    /// - witness: `tests::native_formers::data_signature_formation_checks_fields_and_parameters`
    #[spec(requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()), captures: start = self.builder.content_start(), ensures: |ret| ret.content_start == start && matches!(ret.declaration.content(), DeclarationContent::Data { kind: actual, .. } if *actual == kind))]
    #[inline]
    #[must_use]
    pub fn data(
        self,
        levels: LevelSignature,
        parameters: Vec<ValueTypeId>,
        constructors: Vec<Vec<ValueTypeId>>,
        kind: ValueTypeId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.data(levels, parameters, constructors, kind),
        }
    }

    /// Finalize a codata signature while retaining its staging claim.
    ///
    /// # Specification
    /// - requires: this session owns the last outstanding staging mark.
    /// - ensures: the mark remains outstanding and the signature is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — codata admission refuses a malformed signature
    ///   without retaining its nodes.
    /// - witness: `tests::codata::a_value_universe_is_no_codata_kind`
    #[spec(requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()), captures: start = self.builder.content_start(), ensures: |ret| ret.content_start == start && matches!(ret.declaration.content(), DeclarationContent::Codata { kind: actual, .. } if *actual == kind))]
    #[inline]
    #[must_use]
    pub fn codata(
        self,
        levels: LevelSignature,
        parameters: Vec<ValueTypeId>,
        observations: Vec<CompTypeId>,
        kind: ValueTypeId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.codata(levels, parameters, observations, kind),
        }
    }

    /// Finalize a nominal data signature indexed by `indices`, each
    /// constructor's fields beside the index it states, while retaining its
    /// staging claim.
    ///
    /// # Specification
    /// - requires: this session owns the last outstanding staging mark.
    /// - ensures: the mark remains outstanding and the signature is preserved.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector admits at its stated lengths and refuses a
    ///   constructor stating an index of the wrong kind.
    /// - witness: `tests::native_formers::an_indexed_family_states_its_result_indices`
    #[spec(requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()), captures: start = self.builder.content_start(), ensures: |ret| ret.content_start == start && matches!(ret.declaration.content(), DeclarationContent::Data { kind: actual, .. } if *actual == kind))]
    #[inline]
    #[must_use]
    pub fn indexed(
        self,
        levels: LevelSignature,
        parameters: Vec<ValueTypeId>,
        table: (Vec<ValueTypeId>, Vec<Vec<ValueTypeId>>, Vec<Vec<ValueId>>),
        kind: ValueTypeId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.indexed(levels, parameters, table, kind),
        }
    }

    /// Begin staging into `arena`, registering the content-start mark.
    ///
    /// # Specification
    /// - requires: `arena` is the environment's own, and `outstanding` its own
    ///   mark multiset.
    /// - ensures: a session whose builder owns the rollback to the arena's
    ///   current watermark, with that watermark registered as outstanding.
    /// - provides: the only way a staging session comes into existence, so no
    ///   content is minted without a mark a rejection must respect.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finished definition retains its claim, while a
    ///   later implicit abandonment restores the prior arena and claim
    ///   sequence.
    /// - witness: `env::tests::implicit_staging_drop_releases_its_claim`
    #[spec(
        captures: [entry_mark = arena.watermark(), entry_len = outstanding.marks.len()],
        ensures: |ret| ret.builder.content_start() == entry_mark
            && ret.claim.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
            && ret.claim.outstanding.marks.last() == Some(&entry_mark)
    )]
    #[inline]
    fn new(
        arena: &'env mut TermArena,
        outstanding: &'env mut StagedMarks,
    ) -> Self
    {
        let builder = DeclarationBuilder::new(arena);
        outstanding.register(builder.content_start());
        Self {
            builder,
            claim: StagingClaim { outstanding },
        }
    }

    /// The borrowed arena, for minting this declaration's content.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn arena(&mut self) -> &mut TermArena
    {
        self.builder.arena()
    }

    /// Discard the staged content, restoring the arena and resolving the mark.
    ///
    /// # Specification
    /// - requires: the session owns its builder's start mark as the final
    ///   registration, as established by construction and its exclusive borrow.
    /// - ensures: each arena family is truncated to the lesser of its current
    ///   length and this session's content-start; the final claim is released.
    ///   No node minted by this session survives, and its claim cannot block a
    ///   later admission.
    /// - provides: the abandonment path a producer takes before offering
    ///   anything, which is what makes a probe-before-stage discipline
    ///   unnecessary.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — explicit abandonment rolls back one newly minted
    ///   value and releases a later claim so an earlier declaration admits.
    /// - witness: `env::tests::an_abandoned_staging_leaves_the_arena_unchanged`
    /// - witness: `env::tests::an_abandoned_staging_releases_its_claim`
    #[spec(requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()))]
    #[inline]
    pub fn discard(self)
    {
        // Fields drop in declaration order: the builder rolls back first, then
        // the exclusively borrowed registration is released.
    }

    /// Finalize a definition over an already-minted declared type and body.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned definition retains that start mark and the
    ///   supplied level signature and roots. Its arena content and registration
    ///   remain live until admission, bypass, or abandonment.
    /// - provides: ownership transfer from a borrowing session to a staged
    ///   declaration without triggering either rollback or claim release.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four finishers leaves a later claim that
    ///   blocks an earlier admission without truncating either region, and the
    ///   retained declaration subsequently admits on its own.
    /// - witness: `env::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()),
        captures: [entry_start = self.builder.content_start()],
        ensures: |ret| ret.content_start == entry_start
            && *ret.declaration.content() == DeclarationContent::Def { declared, body }
    )]
    #[inline]
    #[must_use]
    pub fn def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.def(levels, declared, body),
        }
    }

    /// Finalize a definition carrying sealing provenance.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned definition carrying the supplied sealing
    ///   provenance retains that start mark and the supplied level signature
    ///   and roots. Its arena content and registration remain live until
    ///   admission, bypass, or abandonment.
    /// - provides: ownership transfer from a borrowing session to a staged
    ///   declaration without triggering either rollback or claim release.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four finishers leaves a later claim that
    ///   blocks an earlier admission without truncating either region, and the
    ///   retained declaration subsequently admits on its own.
    /// - witness: `env::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()),
        captures: [entry_start = self.builder.content_start(), entry_provenance = provenance.len()],
        ensures: |ret| ret.content_start == entry_start
            && *ret.declaration.content() == DeclarationContent::Def { declared, body }
            && ret.declaration.provenance().len() == entry_provenance
    )]
    #[inline]
    #[must_use]
    pub fn sealed_def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
        provenance: Vec<ConstantIndex>,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.sealed_def(levels, declared, body, provenance),
        }
    }

    /// Finalize an axiom over an already-minted declared type.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned axiom retains that start mark and the supplied
    ///   level signature and roots. Its arena content and registration remain
    ///   live until admission, bypass, or abandonment.
    /// - provides: ownership transfer from a borrowing session to a staged
    ///   declaration without triggering either rollback or claim release.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four finishers leaves a later claim that
    ///   blocks an earlier admission without truncating either region, and the
    ///   retained declaration subsequently admits on its own.
    /// - witness: `env::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()),
        captures: [entry_start = self.builder.content_start()],
        ensures: |ret| ret.content_start == entry_start
            && *ret.declaration.content() == DeclarationContent::Axiom { declared }
    )]
    #[inline]
    #[must_use]
    pub fn axiom(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.axiom(levels, declared),
        }
    }

    /// Finalize a sealed abstract type at an already-minted universe kind, over
    /// an already-minted representation, with the scope of its minting
    /// admission.
    ///
    /// A producer sealing a module stages its atoms [`SealScope::Open`] and
    /// closes them with [`Environment::seal`] once the module's members are
    /// admitted; a replay stages them [`SealScope::Closed`] at the extent the
    /// artifact carries, and the environment closes them itself.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned abstract type retains that start mark and the
    ///   supplied level signature, roots and scope. Its arena content and
    ///   registration remain live until admission, bypass, or abandonment.
    /// - provides: ownership transfer from a borrowing session to a staged
    ///   declaration without triggering either rollback or claim release.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four finishers leaves a later claim that
    ///   blocks an earlier admission without truncating either region, and the
    ///   retained declaration subsequently admits on its own.
    /// - witness: `env::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()),
        captures: [entry_start = self.builder.content_start()],
        ensures: |ret| ret.content_start == entry_start
            && matches!(*ret.declaration.content(), DeclarationContent::AbstractType { kind: k, representation: r, scope: s, .. } if k == kind && r == representation && s == scope)
    )]
    #[inline]
    #[must_use]
    pub fn abstract_type(
        self,
        levels: LevelSignature,
        kind: ValueTypeId,
        representation: ValueTypeId,
        scope: SealScope,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self
                .builder
                .abstract_type(levels, kind, representation, scope),
        }
    }
}

/// One admitted declaration and its audit metadata.
#[derive(Clone, Debug)]
pub struct AdmittedDeclaration
{
    /// The declaration itself.
    declaration: Declaration,
    /// Whether it was checked or bypassed.
    admission: Admission,
    /// The transitive positions of axioms and unchecked admissions this
    /// declaration rests on, itself included when it is one. Precomputed at
    /// admission, so the audit is a lookup.
    rested_on: BTreeSet<ConstantIndex>,
    /// The block it was admitted in: its own position alone unless a mutual
    /// block admitted it, whose families share one stage.
    block: check::occurrence::Block,
    /// What the occurrence walk decided of it: a family's stratification and
    /// its parameters' variance; the reading that admits least for anything
    /// no walk read.
    accessibility: check::Accessibility,
}

impl AdmittedDeclaration
{
    /// The declared value-type root: what a constant reference resolves to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declared_id(&self) -> ValueTypeId
    {
        self.declaration.declared_id()
    }

    /// How this declaration was admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admission(&self) -> Admission
    {
        self.admission
    }

    /// The declaration's content, which a sealed-atom reference is resolved
    /// against so an atom's claim to be one is checked rather than believed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn content(&self) -> &DeclarationContent
    {
        self.declaration.content()
    }

    /// The declaration as the environment holds it: as staged, with an
    /// abstract type's scope closed where the environment closed it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &Declaration
    {
        &self.declaration
    }

    /// The block the declaration was admitted in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn block(&self) -> check::occurrence::Block
    {
        self.block
    }

    /// What the occurrence walk decided of the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn accessibility(&self) -> &check::Accessibility
    {
        &self.accessibility
    }
}

/// The transitive audit of a declaration: the axioms and unchecked admissions
/// it rests on.
///
/// A declaration whose report is empty on both faces rests on nothing outside
/// the checked kernel.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct AxiomReport
{
    /// The positions of axioms it transitively rests on, ascending.
    axioms: Vec<ConstantIndex>,
    /// The positions of unchecked admissions it transitively rests on,
    /// ascending.
    unchecked: Vec<ConstantIndex>,
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
        self.axioms.as_slice()
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
        self.unchecked.as_slice()
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

/// The append-only kernel environment: one arena, and the admitted
/// declarations in admission order.
#[derive(Clone, Debug, Default)]
pub struct Environment
{
    /// The one arena every declaration's content lives in.
    arena: TermArena,
    /// The admitted declarations, in admission order.
    entries: Vec<AdmittedDeclaration>,
    /// The admission floor: the watermark at the most recent admission,
    /// checked or bypassed. No rejection truncates below it.
    admission_floor: ArenaWatermark,
    /// The content-start marks of declarations staged into the arena and not
    /// yet resolved. What a rejection may not truncate through.
    outstanding: StagedMarks,
    /// The atoms whose minting admission is open, ascending: what a
    /// declaration admitted now reads as its representation.
    manifest: Vec<ConstantIndex>,
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
    pub fn entries(&self) -> &[AdmittedDeclaration]
    {
        self.entries.as_slice()
    }

    /// Begin building one declaration's content into this environment's arena.
    ///
    /// # Specification
    /// - requires: the returned session builds at most one declaration's
    ///   content and is then finalized or abandoned, with no other allocation
    ///   into the arena interleaved.
    /// - ensures: a [`Staging`] borrowing the arena, with its content-start
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
    /// - witness: `env::tests::an_abandoned_staging_leaves_the_arena_unchanged`
    /// - witness: `env::tests::an_abandoned_staging_releases_its_claim`
    /// - witness: `env::tests::implicit_staging_drop_releases_its_claim`
    /// - witness: `env::tests::every_finisher_retains_its_claim_until_admission`
    #[spec(
        captures: [entry_mark = self.arena.watermark(), entry_len = self.outstanding.marks.len()],
        ensures: |ret| ret.builder.content_start() == entry_mark
            && ret.claim.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
            && ret.claim.outstanding.marks.last() == Some(&entry_mark)
    )]
    #[inline]
    pub fn stage(&mut self) -> Staging<'_>
    {
        let Self {
            ref mut arena,
            ref mut outstanding,
            ..
        } = *self;
        Staging::new(arena, outstanding)
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
    /// - witness: `env::tests::abandoning_a_staged_declaration_releases_its_claim`
    /// - witness: `env::tests::abandoning_beneath_outstanding_content_retains_it`
    /// - witness: `env::tests::abandonment_preserves_the_admission_floor`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body resolves the mark and asks whether anything sits above it, each a walk of the outstanding marks; the check counts and clamps them the same way"
        )
    )]
    #[spec(
        captures: [
            entry_mark = staged.content_start,
            entry_len = self.outstanding.marks.len(),
            entry_count = self.outstanding.marks.iter().filter(|&&held| held == staged.content_start).count(),
            entry_entries = self.entries.len(),
            entry_floor = self.admission_floor,
            expected_mark = if self.outstanding.marks.iter().any(|&held| held.clamped_into(ArenaWatermark::default(), staged.content_start) != held) {
                self.arena.watermark()
            } else {
                staged.content_start.clamped_into(self.admission_floor, self.arena.watermark())
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
        let StagedDeclaration {
            content_start,
            declaration: _,
        } = staged;
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
    ///   Equal and lower marks are separated by the componentwise-count
    ///   witness.
    /// - witness: `env::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `env::tests::abandoning_a_staged_declaration_releases_its_claim`
    /// - witness: `env::tests::marks_above_are_counted_componentwise`
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

    /// Admit a declaration through the checked choke point.
    ///
    /// # Specification
    /// - requires: `staged` was built into this environment's arena through
    ///   [`Self::stage`]; every well-formedness and typing obligation is
    ///   re-derived here, granting the producer no credence.
    /// - ensures: `Ok(id)` with an unforgeable [`CheckedId`] exactly when the
    ///   declaration's level signature admits, its declared type forms, its
    ///   sealing provenance re-derives, and a definition's body checks against
    ///   that type. The declaration is appended, its audit precomputed, the
    ///   arena holds prior content plus this declaration's with the checker's
    ///   intermediates truncated, and the admission floor rises to that mark.
    ///   On any failure the arena is truncated to this declaration's
    ///   content-start clamped into `[admission floor, checker-entry mark]`, so
    ///   every caller-observable face of the environment is exactly what it was
    ///   before the call.
    /// - provides: the one checked entry into the kernel. It takes **no memo**,
    ///   which is the structural form of the memo's one-call lifetime: nothing
    ///   an earlier check recorded can reach a later one through this entry.
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
    ///   nothing.
    /// - witness: `env::tests::a_definition_referencing_a_prior_one_checks`
    /// - witness: `env::tests::a_forward_constant_reference_is_unbound`
    /// - witness: `env::tests::a_rejected_declaration_leaves_the_environment_unchanged`
    /// - witness: `env::tests::a_rejection_keeps_a_prior_admission_resolvable`
    /// - witness: `env::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `env::tests::an_in_order_producer_is_never_refused`
    // The predicate covers the two structural halves of the success
    // postcondition: exactly one entry is appended, and the admission floor
    // ends at the arena's own watermark — that is, the checker's intermediates
    // were truncated away rather than committed. Whether the declaration is
    // *well-typed* is what the body decides and is not restated here.
    #[inline]
    #[spec(captures: [entry_len = self.entries.len()], ensures: |ret| ret.is_err()
        || (arith::Int::from(self.entries.len()) == arith::add(arith::Int::from(entry_len), arith::Int::from(1_usize))
            && self.admission_floor == self.arena.watermark()))]
    pub fn add_decl(
        &mut self,
        staged: StagedDeclaration,
    ) -> Result<CheckedId, KernelError>
    {
        let StagedDeclaration {
            content_start,
            declaration,
        } = staged;
        // The guard, before anything is truncated: a declaration staged after
        // this one owns arena nodes above this one's content-start, and the
        // rollback below is a contiguous truncation that cannot spare them.
        // Refusing is the fail-closed answer; the alternative is deleting a live
        // producer's content, or worse, letting a later staging re-mint those
        // indices so a subsequent admission checks other content under that
        // declaration's name.
        self.outstanding.resolve(content_start);
        let above = self.outstanding.above(content_start);
        if usize::from(above) != 0 {
            self.outstanding.register(content_start);
            return Err(KernelError::OutstandingStagedContent { above });
        }
        let position = ConstantIndex::from(self.entries.len());
        let content_end = self.arena.watermark();
        // The rejection mark: this declaration's content-start, clamped into
        // `[admission floor, content-end]`, so a rollback can neither delete an
        // admitted declaration's content nor retain a checker intermediate.
        let rejected = content_start.clamped_into(self.admission_floor, content_end);
        let levels = match LevelContext::admit(
            declaration.levels().params(),
            declaration.levels().constraints().to_vec(),
        ) {
            Ok(levels) => levels,
            Err(error) => {
                self.arena.truncate_to(rejected);
                return Err(error);
            },
        };
        let outcome = {
            let Self {
                ref mut arena,
                ref entries,
                ref manifest,
                ..
            } = *self;
            check::check_declaration(
                arena,
                check::Judgement::new(entries, &levels).unsealing(manifest),
                &declaration,
            )
        };
        match outcome {
            Ok(accessibility) => {
                // Keep this declaration's content; drop the intermediates that
                // allocated past it.
                self.arena.truncate_to(content_end);
                self.admission_floor = content_end;
                let rested_on = self.transitive_rest(
                    declaration.content(),
                    declaration.laws(),
                    position,
                    Admission::Checked,
                );
                self.entries.push(AdmittedDeclaration {
                    declaration,
                    admission: Admission::Checked,
                    rested_on,
                    block: check::occurrence::Block::lone(position),
                    accessibility,
                });
                self.advance_seals(position);
                Ok(CheckedId::new(position))
            },
            Err(error) => {
                // Drop the intermediates and this declaration's content, down
                // to the admission floor and no further.
                self.arena.truncate_to(rejected);
                Err(error)
            },
        }
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
    ///   resolved. The arena is unchanged, since the bypass mints no
    ///   intermediate and truncates nothing, and the admission floor rises to
    ///   its watermark so a later rejection cannot truncate through what the
    ///   bypass committed. The outstanding-content guard is therefore not owed
    ///   here: the bypass destroys nothing, so there is nothing to preserve.
    /// - provides: the tracked, warned bypass.
    /// - fails: never — the bypass does not check.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the bypass's whole observable effect is that the
    ///   declaration is present and that dependents' audits name it, pinned by
    ///   a dependent's report; the L3 residue is the floor rise, pinned by a
    ///   later rejection leaving bypassed content resolvable.
    /// - witness: `env::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `env::tests::a_rejection_keeps_bypassed_content_resolvable`
    #[inline]
    #[spec(captures: [entry_len = self.entries.len(), entry_watermark = self.arena.watermark()], ensures: arith::Int::from(self.entries.len()) == arith::add(arith::Int::from(entry_len), arith::Int::from(1_usize))
        && self
            .entries
            .last()
            .is_some_and(|entry| entry.admission == Admission::Unchecked)
        && self.arena.watermark() == entry_watermark
        && self.admission_floor == self.arena.watermark())]
    pub fn add_decl_unchecked(
        &mut self,
        staged: StagedDeclaration,
    ) -> CheckedId
    {
        let StagedDeclaration {
            content_start,
            declaration,
        } = staged;
        self.outstanding.resolve(content_start);
        let position = ConstantIndex::from(self.entries.len());
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
        self.entries.push(AdmittedDeclaration {
            declaration,
            admission: Admission::Unchecked,
            rested_on,
            block: check::occurrence::Block::lone(position),
            accessibility: check::Accessibility::unwalked(),
        });
        self.advance_seals(position);
        CheckedId::new(position)
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
    ///   body checks; each member's audit is the union of the block's. On any
    ///   failure the arena, the entries and the manifest are as they were
    ///   before the call.
    /// - provides: the one checked entry for declarations that name each other,
    ///   by the same choke point [`Self::add_decl`] is.
    /// - fails: [`KernelError::OutstandingStagedContent`] when a declaration
    ///   staged after the block is unresolved; otherwise any [`KernelError`] a
    ///   member's admission surfaces.
    /// - panics: none.
    ///
    /// # Errors
    /// [`KernelError::OutstandingStagedContent`], or any [`KernelError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe and its decoder are admitted together; a
    ///   decoder that names itself at a place that does not descend, and a
    ///   field naming its family under a function domain, are each refused with
    ///   the environment unchanged.
    /// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
    /// - witness: `tests::recursive_data::a_mutual_block_is_refused_whole`
    #[spec(captures: [entry_len = self.entries.len(), entry_watermark = self.arena.watermark(), members = staged.len()],
        ensures: |ret| match ret.as_ref() {
            Ok(ids) => ids.len() == members
                && self.entries.len().checked_sub(entry_len) == Some(members)
                && self.admission_floor == self.arena.watermark(),
            Err(_) => self.entries.len() == entry_len
                && self.arena.watermark().clamped_into(gandr_kernel_term::ArenaWatermark::default(), entry_watermark) == self.arena.watermark(),
        })]
    #[inline]
    pub fn add_block(
        &mut self,
        staged: Vec<StagedDeclaration>,
    ) -> Result<Vec<CheckedId>, KernelError>
    {
        let Some(content_start) = staged.iter().map(|member| member.content_start).min()
        else {
            return Ok(Vec::new());
        };
        // The guard of `add_decl`, over the whole block: every member's claim
        // resolves, and a claim left above the block's start is a producer
        // the rollback would truncate through.
        for member in &staged {
            self.outstanding.resolve(member.content_start);
        }
        let above = self.outstanding.above(content_start);
        if usize::from(above) != 0 {
            for member in &staged {
                self.outstanding.register(member.content_start);
            }
            return Err(KernelError::OutstandingStagedContent { above });
        }
        let members = staged
            .into_iter()
            .map(|member| member.declaration)
            .collect::<Vec<_>>();
        let base = self.entries.len();
        let content_end = self.arena.watermark();
        let rejected = content_start.clamped_into(self.admission_floor, content_end);
        let manifest = self.manifest.clone();
        match self.admit_block(&members, content_end) {
            Ok(ids) => {
                self.arena.truncate_to(content_end);
                self.admission_floor = content_end;
                Ok(ids)
            },
            Err(error) => {
                self.entries.truncate(base);
                self.manifest = manifest;
                self.arena.truncate_to(rejected);
                Err(error)
            },
        }
    }

    /// The schedule of [`Self::add_block`], appending each member as it
    /// checks; the caller rolls back on failure.
    ///
    /// # Specification
    /// - requires: `members` were staged into this arena below `content_end`,
    ///   in admission order.
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
        |ids| self.entries.len().checked_sub(entry_len) == Some(ids.len())))]
    fn admit_block(
        &mut self,
        members: &[Declaration],
        content_end: ArenaWatermark,
    ) -> Result<Vec<CheckedId>, KernelError>
    {
        let base = self.entries.len();
        let first = ConstantIndex::from(base);
        let families = members
            .iter()
            .take_while(|member| matches!(*member.content(), DeclarationContent::Data { .. }))
            .count();
        let past_families = ConstantIndex::from(base.saturating_add(families));
        let end = ConstantIndex::from(base.saturating_add(members.len()));
        let mut admitted = Vec::with_capacity(members.len());
        // The definitions' declared types form with the families in scope and
        // no definition: a declared type names the block's families, never
        // its definitions.
        for member in members.iter().skip(families) {
            let levels = LevelContext::admit(
                member.levels().params(),
                member.levels().constraints().to_vec(),
            )?;
            let Self {
                ref mut arena,
                ref entries,
                ref manifest,
                ..
            } = *self;
            check::form_declared(
                arena,
                check::Judgement::new(entries, &levels)
                    .unsealing(manifest)
                    .within_mutual(
                        check::occurrence::Block::new(first, past_families, past_families),
                        members,
                    ),
                member.declared_id(),
            )?;
            self.arena.truncate_to(content_end);
        }
        for (offset, member) in members.iter().enumerate() {
            let position = ConstantIndex::from(base.saturating_add(offset));
            let levels = LevelContext::admit(
                member.levels().params(),
                member.levels().constraints().to_vec(),
            )?;
            // A family forms with the block in scope; a definition is checked
            // as a lone one is, every family and definition before it
            // admitted, inside the block only so its own fixpoint reads its
            // constant as the self binder.
            let accessibility = {
                let Self {
                    ref mut arena,
                    ref entries,
                    ref manifest,
                    ..
                } = *self;
                let judgement = check::Judgement::new(entries, &levels)
                    .unsealing(manifest)
                    .within_mutual(
                        check::occurrence::Block::new(
                            first,
                            past_families,
                            if offset < families { end } else { position },
                        ),
                        members,
                    );
                check::check_declaration(arena, judgement, member)?
            };
            self.arena.truncate_to(content_end);
            let rested_on = self.transitive_rest(
                member.content(),
                member.laws(),
                position,
                Admission::Checked,
            );
            // The block's families share one stage; a definition stands alone.
            self.entries.push(AdmittedDeclaration {
                declaration: member.clone(),
                admission: Admission::Checked,
                rested_on,
                block: if offset < families {
                    check::occurrence::Block::new(first, past_families, end)
                }
                else {
                    check::occurrence::Block::lone(position)
                },
                accessibility,
            });
            self.advance_seals(position);
            admitted.push(CheckedId::new(position));
        }
        // The members name each other, so each rests on what any rests on.
        let mut rested = BTreeSet::new();
        for entry in self.entries.iter().skip(base) {
            rested.extend(entry.rested_on.iter().copied());
        }
        for entry in self.entries.iter_mut().skip(base) {
            entry.rested_on.clone_from(&rested);
        }
        Ok(admitted)
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
    ///   that extent is returned. Every other face of the environment is
    ///   unchanged, and on failure nothing changes.
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
    /// - witness: `env::tests::a_value_of_the_representation_does_not_inhabit_the_atom`
    /// - witness: `env::tests::an_atom_seals_once`
    #[spec(
        captures: [entry_len = self.entries.len(), entry_manifest = self.manifest.len()],
        ensures: |ret| self.entries.len() == entry_len && ret.as_ref().map_or_else(
            |error| self.manifest.len() == entry_manifest
                && *error == KernelError::SealNotOpen { index: atom.position() },
            |extent| self.manifest.len().checked_add(1) == Some(entry_manifest)
                && self.manifest.binary_search(&atom.position()).is_err()
                && usize::from(atom.position()).checked_add(usize::from(*extent)).and_then(|end| end.checked_add(1)) == Some(entry_len),
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
            self.entries
                .len()
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
        } = *entry.declaration.content()
        else {
            return Err(refused);
        };
        entry.declaration = entry.declaration.clone().closed(extent);
        let _closed = self.manifest.remove(held);
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
                        .map(|member| StagedDeclaration {
                            content_start: floor,
                            declaration: member.declaration().clone(),
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
            let staged = StagedDeclaration {
                content_start: floor,
                declaration: marked.declaration().clone(),
            };
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
                    let _admitted = environment.add_decl_unchecked(staged);
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
            ..
        } = *self;
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
        match entries
            .get(usize::from(position))
            .map(AdmittedDeclaration::content)
        {
            Some(&DeclarationContent::AbstractType {
                scope: SealScope::Open,
                ..
            }) => manifest.push(position),
            Some(&DeclarationContent::AbstractType {
                scope: SealScope::Closed(extent),
                ..
            }) if reaches_past(position, extent) => manifest.push(position),
            Some(_) | None => {},
        }
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
    /// - witness: `env::tests::audit_reports_the_transitive_axiom`
    /// - witness: `env::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `env::tests::audit_reaches_an_axiom_named_only_inside_a_code`
    /// - witness: `env::tests::a_closed_definition_rests_on_nothing`
    #[spec(ensures: |ret| match self.entries.get(usize::from(id.position())) {
        None => ret.axioms.is_empty() && ret.unchecked.is_empty(),
        Some(entry) => ret.axioms.iter().copied().eq(entry.rested_on.iter().copied().filter(|&position|
            self.entries.get(usize::from(position)).is_some_and(|ancestor|
                matches!(*ancestor.declaration.content(), DeclarationContent::Axiom { .. }))))
            && ret.unchecked.iter().copied().eq(entry.rested_on.iter().copied().filter(|&position|
                self.entries.get(usize::from(position)).is_some_and(|ancestor|
                    matches!(ancestor.admission, Admission::Unchecked))))
    })]
    #[inline]
    #[must_use]
    pub fn audit(
        &self,
        id: CheckedId,
    ) -> AxiomReport
    {
        let mut axioms = Vec::new();
        let mut unchecked = Vec::new();
        if let Some(entry) = self.entries.get(usize::from(id.position())) {
            for &position in &entry.rested_on {
                if let Some(ancestor) = self.entries.get(usize::from(position)) {
                    if matches!(ancestor.admission, Admission::Unchecked) {
                        unchecked.push(position);
                    }
                    if matches!(
                        *ancestor.declaration.content(),
                        DeclarationContent::Axiom { .. }
                    ) {
                        axioms.push(position);
                    }
                }
            }
        }
        AxiomReport { axioms, unchecked }
    }

    /// Precompute the transitive set of axioms and unchecked admissions a
    /// declaration rests on.
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
    /// - requires: `position` is the next admission index and `content` and
    ///   `laws` are its declaration's. Checked references name earlier
    ///   admissions; a bypass is itself an audit reason even if it names an
    ///   unknown position.
    /// - ensures: the union of the audits of every position the declared type,
    ///   an abstract type's representation or a definition's body names, and of
    ///   every law the definition's folds rest on, with `position` itself
    ///   included exactly when the declaration is an axiom or is being
    ///   bypassed. Both reference forms of the type plane are followed — a
    ///   sealed atom directly, and a code through the term language — so a
    ///   declaration reachable only through a code stays in the graph.
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
    /// - witness: `env::tests::audit_reports_the_transitive_axiom`
    /// - witness: `env::tests::audit_reports_a_transitive_unchecked_admission`
    /// - witness: `env::tests::audit_reaches_an_axiom_named_only_inside_a_code`
    /// - witness: `tests::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
    #[spec(
        requires: usize::from(position) == self.entries.len(),
        ensures: |ret| ret.contains(&position)
            == (matches!(*content, DeclarationContent::Axiom { .. }) || matches!(admission, Admission::Unchecked))
            && ret.iter().all(|&ancestor| ancestor == position ||
                (ancestor < position && self.entries.get(usize::from(ancestor)).is_some_and(|entry|
                    matches!(entry.admission, Admission::Unchecked)
                        || matches!(*entry.declaration.content(), DeclarationContent::Axiom { .. }))))
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
                for &ancestor in &entry.rested_on {
                    let _fresh = rested.insert(ancestor);
                }
            }
        }
        let is_axiom = matches!(*content, DeclarationContent::Axiom { .. });
        if is_axiom || matches!(admission, Admission::Unchecked) {
            let _fresh = rested.insert(position);
        }
        rested
    }
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

/// Whether a walk follows the codes the types it meets are read off.
///
/// **The two consumers of this walk want two different sets, and conflating
/// them is wrong in both directions.** The audit graph asks what a declaration
/// *rests on*, and a constant named inside a code is as load-bearing as one
/// named by a sealed atom, so it follows the code. The sealing-provenance gate
/// asks which sealed atoms a projection could have rebound, and following a
/// code there would admit provenance entries naming declarations no projection
/// touched — a strictly more permissive gate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CodeEdges
{
    /// Follow a code into the term language and union the constants it names.
    Follow,
    /// Stop at the decoding formers of both type families.
    Stop,
}

/// The constant references reachable from one node: the constants its values
/// name and the sealed atoms its types name.
///
/// The graph crosses families both ways. A type reaches a value through a
/// decoding former, which carries a code, and a value reaches a type through a
/// quote, which carries one. `codes` chooses whether the first crossing is
/// taken; see [`CodeEdges`] for why that is a choice rather than a setting. The
/// second is always taken, because a quote is reached only from a value and so
/// only once a code edge has been followed or the walk began at a value.
///
/// # Specification
/// - requires: nothing — an unreadable id contributes nothing, fail-closed.
/// - ensures: exactly the set of positions reachable from `root`: every
///   constant and every sealed atom, where under [`CodeEdges::Stop`] the walk
///   does not cross from a decoding former into its code.
/// - provides: both halves of the audit graph's direct edges and the projection
///   set used by the sealing-provenance gate. Predicates check leaf,
///   unreadable, direct-reference and root code-edge cases without repeating
///   the traversal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pair containing a constant and a quoted atom separates
///   the two reference forms. Value and computation decoding formers separate
///   follow from stop, and unreadable roots are empty in all four families.
///   Existing admission witnesses cover finite transitive chains through codes.
/// - witness: `env::tests::reachability_separates_references_and_code_edges`
/// - witness: `env::tests::unreadable_roots_contribute_no_references`
/// - witness: `env::tests::audit_reaches_an_axiom_named_only_inside_a_code`
///
/// - witness: `env::tests::sealing_provenance_does_not_follow_codes`
/// - witness: `env::tests::a_type_level_atom_reference_reaches_the_audit`
#[spec(ensures: |ret| match root {
    AnyNode::Value(id) => match arena.value(id) {
        Some(&Value::Constant(index)) => ret.len() == 1_usize && ret.contains(&index),
        Some(&Value::Variable(_) | &Value::Literal(_)) | None => ret.is_empty(),
        Some(held) if held.components() == Some(&[]) => ret.is_empty(),
        _ => true,
    },
    AnyNode::Computation(id) => arena.computation(id).is_some() || ret.is_empty(),
    AnyNode::ValueType(id) => match arena.value_type(id) {
        Some(&ValueType::Abstract(index)) => ret.len() == 1_usize && ret.contains(&index),
        Some(&ValueType::Base(_) | &ValueType::Universe { .. }) | None => ret.is_empty(),
        Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)) if parts.is_empty() => ret.is_empty(),
        Some(&ValueType::Element { .. } | &ValueType::PathUniverse(..)) if matches!(codes, CodeEdges::Stop) => ret.is_empty(),
        _ => true,
    },
    AnyNode::CompType(id) => match arena.comp_type(id) {
        None => ret.is_empty(),
        Some(&CompType::Element { .. }) if matches!(codes, CodeEdges::Stop) => ret.is_empty(),
        _ => true,
    },
})]
fn collect_reachable(
    arena: &TermArena,
    root: AnyNode,
    codes: CodeEdges,
) -> BTreeSet<ConstantIndex>
{
    let mut found = BTreeSet::new();
    let _gathered = reach(
        arena,
        root,
        codes,
        &mut Walk::default(),
        &mut Sink::Gather(&mut found),
    );
    found
}

/// Whether a walk met the constant it sought.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mention
{
    /// The constant is reachable from the root.
    Named,
    /// Nothing reachable from the root names the constant.
    Unnamed,
}

/// What a reachability walk does with each constant it meets.
#[derive(Debug)]
enum Sink<'found>
{
    /// Gather every constant met; the walk runs to its end.
    Gather(&'found mut BTreeSet<ConstantIndex>),
    /// Stop at the first meeting of the one constant sought.
    Seek(ConstantIndex),
}

impl Sink<'_>
{
    /// Meet `index`: gather it, or say whether it is the constant sought.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a gathering sink holds `index` and answers `Unnamed`; a
    ///   seeking sink answers `Named` exactly when `index` is the constant it
    ///   seeks.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a gathering walk collects both reference forms, and a
    ///   seeking one answers for its own constant and not for another reachable
    ///   one.
    /// - witness: `env::tests::reachability_separates_references_and_code_edges`
    /// - witness: `env::tests::a_search_stops_at_its_constant_across_roots`
    #[spec(ensures: |ret| match *self {
        Self::Gather(ref found) => ret == Mention::Unnamed && found.contains(&index),
        Self::Seek(sought) => (ret == Mention::Named) == (sought == index),
    })]
    fn meet(
        &mut self,
        index: ConstantIndex,
    ) -> Mention
    {
        match *self {
            Self::Gather(ref mut found) => {
                let _fresh = found.insert(index);
                Mention::Unnamed
            },
            Self::Seek(sought) => {
                if sought == index {
                    Mention::Named
                }
                else {
                    Mention::Unnamed
                }
            },
        }
    }
}

/// A reachability walk's worklist and the nodes it has expanded.
#[derive(Debug, Default)]
struct Walk
{
    /// Every node expanded so far, each once.
    seen: BTreeSet<AnyNode>,
    /// The nodes met and not yet expanded.
    pending: Vec<AnyNode>,
}

/// Expand every node reachable from `root` that `walk` has not expanded,
/// handing each constant reference one of them makes to `sink`, and stop at
/// the first the sink answers `Named` for.
///
/// # Specification
/// - requires: every node `walk` has expanded had its children expanded by it,
///   under the same `codes`, and its worklist is empty.
/// - ensures: `Named` exactly when `sink` answers `Named` for a constant
///   reachable from `root` through nodes `walk` had not expanded; on `Unnamed`,
///   every such node is expanded, every constant it names has met `sink`, and
///   the worklist is empty again.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`collect_reachable`] for a gathering sink; a seeking
///   walk answers a later root through the nodes an earlier one expanded.
/// - witness: `env::tests::reachability_separates_references_and_code_edges`
/// - witness: `env::tests::a_search_stops_at_its_constant_across_roots`
///
/// # Termination
/// - reason: the walk is a loop over one explicit worklist, not recursion.
/// - measure: lexicographically, reachable node identities not yet seen and
///   pending worklist length. First visits reduce the former; revisits enqueue
///   nothing and reduce the latter.
/// - boundedness: the finite arena and its finite child-reference fields bound
///   the reachable identities, including unreadable ones.
/// - input recursion: none.
#[spec(ensures: |ret| ret == Mention::Named || walk.pending.is_empty())]
fn reach(
    arena: &TermArena,
    root: AnyNode,
    codes: CodeEdges,
    walk: &mut Walk,
    sink: &mut Sink<'_>,
) -> Mention
{
    let Walk {
        ref mut seen,
        ref mut pending,
    } = *walk;
    // Each arena node is expanded once: re-walking a shared subtree meets
    // only constants already met, and without the seen set the walk
    // tree-expands the graph, which is exponential in sharing depth.
    pending.push(root);
    let follow = matches!(codes, CodeEdges::Follow);
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        match node {
            AnyNode::Value(id) => match arena.value(id) {
                Some(&Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                }) => pending.extend(
                    core::iter::once(AnyNode::ValueType(datatype))
                        .chain(fields.iter().copied().map(AnyNode::Value)),
                ),
                Some(&Value::Record(ref fields)) => {
                    pending.extend(fields.values().copied().map(AnyNode::Value));
                },
                Some(&Value::Constant(index)) => {
                    if sink.meet(index) == Mention::Named {
                        return Mention::Named;
                    }
                },
                Some(&Value::ListNil | &Value::Variable(_) | &Value::Literal(_)) | None => {},
                Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    pending.push(AnyNode::ValueType(path_type));
                    pending.push(AnyNode::Value(forward));
                    pending.push(AnyNode::Value(backward));
                },
                Some(&Value::Univalence(equivalence)) => {
                    pending.push(AnyNode::Value(equivalence));
                },
                Some(
                    &Value::SessionPath {
                        path_type,
                        payload_paths,
                        ..
                    }
                    | &Value::SessionFlow {
                        flow_type: path_type,
                        payload_paths,
                        ..
                    },
                ) => {
                    pending.push(AnyNode::ValueType(path_type));
                    pending.push(AnyNode::Value(payload_paths));
                },
                Some(
                    &Value::PathRefl(code)
                    | &Value::Here { point: code, .. }
                    | &Value::Stay { point: code, .. },
                ) => {
                    pending.push(AnyNode::Value(code));
                },
                Some(
                    &Value::Higher {
                        evidence: ref values,
                        ..
                    }
                    | &Value::QuantifiedEvaluation {
                        children: ref values,
                        ..
                    },
                ) => {
                    pending.extend(values.iter().copied().map(AnyNode::Value));
                },
                Some(&Value::HigherEvaluation { ref components, .. }) => pending.extend(
                    components
                        .iter()
                        .flat_map(|component| [component.left, component.right, component.evidence])
                        .map(AnyNode::Value),
                ),
                Some(&Value::ForwardFlow {
                    flow_type,
                    translator,
                    ref outputs,
                    ..
                }) => {
                    pending.push(AnyNode::ValueType(flow_type));
                    pending.push(AnyNode::Value(translator));
                    pending.extend(outputs.iter().copied().map(AnyNode::Value));
                },
                Some(&Value::FunctionFlow {
                    flow_type,
                    domain,
                    codomain,
                }) => {
                    pending.push(AnyNode::ValueType(flow_type));
                    pending.push(AnyNode::Value(domain));
                    pending.push(AnyNode::Value(codomain));
                },
                Some(
                    &Value::PathProduct(first, second)
                    | &Value::FlowProduct(first, second)
                    | &Value::ListCons(first, second)
                    | &Value::StaticApplication(first, second)
                    | &Value::Then { first, second, .. },
                ) => {
                    pending.push(AnyNode::Value(first));
                    pending.push(AnyNode::Value(second));
                },
                Some(&Value::Tuple(ref components)) => {
                    pending.extend(components.iter().copied().map(AnyNode::Value));
                },
                Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                    pending.push(AnyNode::Value(body));
                },
                Some(&(Value::Thunk(body) | Value::Returned(body))) => {
                    pending.push(AnyNode::Computation(body));
                },
                Some(&Value::Quote(quoted)) => pending.push(AnyNode::ValueType(quoted)),
                Some(&Value::QuoteComputation(quoted)) => pending.push(AnyNode::CompType(quoted)),
            },
            AnyNode::Computation(id) => match arena.computation(id) {
                Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                }) => pending.extend(
                    [AnyNode::Value(scrutinee), AnyNode::CompType(motive)]
                        .into_iter()
                        .chain(branches.iter().copied().map(AnyNode::Computation)),
                ),
                Some(&Computation::SigmaSplit {
                    scrutinee,
                    motive,
                    body,
                }) => pending.extend([
                    AnyNode::Value(scrutinee),
                    AnyNode::CompType(motive),
                    AnyNode::Computation(body),
                ]),
                Some(
                    &(Computation::RecordProjection(record, _)
                    | Computation::TupleProjection(record, _)),
                ) => {
                    pending.extend(core::iter::once(AnyNode::Value(record)));
                },
                Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.extend([
                        AnyNode::ValueType(element),
                        AnyNode::ValueType(result),
                        AnyNode::Value(list),
                        AnyNode::Computation(on_nil),
                        AnyNode::Computation(on_cons),
                    ]);
                },
                Some(&Computation::ListCase {
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.extend([
                        AnyNode::Value(list),
                        AnyNode::Computation(on_nil),
                        AnyNode::Computation(on_cons),
                    ]);
                },
                Some(&Computation::Transport(path, value)) => {
                    pending.push(AnyNode::Value(path));
                    pending.push(AnyNode::Value(value));
                },
                Some(
                    &Computation::PathTransport {
                        motive,
                        path,
                        value,
                    }
                    | &Computation::Ride {
                        motive,
                        flow: path,
                        value,
                    },
                ) => {
                    pending.push(AnyNode::ValueType(motive));
                    pending.push(AnyNode::Value(path));
                    pending.push(AnyNode::Value(value));
                },
                Some(
                    &Computation::TelescopeTransport {
                        motive,
                        path,
                        start,
                        over,
                        value,
                    }
                    | &Computation::TelescopeRide {
                        motive,
                        flow: path,
                        start,
                        over,
                        value,
                    },
                ) => {
                    pending.extend([
                        AnyNode::CompType(motive),
                        AnyNode::Value(path),
                        AnyNode::Value(start),
                        AnyNode::Value(over),
                        AnyNode::Value(value),
                    ]);
                },
                Some(&Computation::RelatedApplication {
                    path,
                    left,
                    right,
                    evidence,
                    body,
                }) => {
                    pending.extend([
                        AnyNode::Value(path),
                        AnyNode::Value(left),
                        AnyNode::Value(right),
                        AnyNode::Value(evidence),
                        AnyNode::Computation(body),
                    ]);
                },
                Some(&Computation::Lambda(body) | &Computation::Fixpoint { body, .. }) => {
                    pending.push(AnyNode::Computation(body));
                },
                Some(&Computation::Application(head, argument)) => {
                    pending.push(AnyNode::Computation(head));
                    pending.push(AnyNode::Value(argument));
                },
                Some(&Computation::Return(value) | &Computation::Force(value)) => {
                    pending.push(AnyNode::Value(value));
                },
                Some(&Computation::Bind(bound, body)) => {
                    pending.push(AnyNode::Computation(bound));
                    pending.push(AnyNode::Computation(body));
                },
                Some(&Computation::With(ref components)) => {
                    pending.extend(components.iter().copied().map(AnyNode::Computation));
                },
                Some(&Computation::Project(_, pair)) => pending.push(AnyNode::Computation(pair)),
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push(AnyNode::Value(scrutinee));
                    pending.extend(branches.iter().copied().map(AnyNode::Computation));
                },
                None => {},
            },
            AnyNode::ValueType(id) => match arena.value_type(id) {
                Some(&ValueType::Data {
                    declaration,
                    ref arguments,
                }) => {
                    if follow {
                        if sink.meet(declaration) == Mention::Named {
                            return Mention::Named;
                        }
                        pending.extend(arguments.iter().copied().map(AnyNode::Value));
                    }
                },
                Some(&ValueType::Record(ref fields)) => {
                    pending.extend(fields.values().copied().map(AnyNode::ValueType));
                },
                Some(&ValueType::Abstract(index)) => {
                    if sink.meet(index) == Mention::Named {
                        return Mention::Named;
                    }
                },
                Some(
                    &ValueType::PathUniverse(source, target)
                    | &ValueType::FlowUniverse(source, target),
                ) => {
                    if follow {
                        pending.push(AnyNode::Value(source));
                        pending.push(AnyNode::Value(target));
                    }
                },
                // The domain is a type; the endpoints cross into the term
                // language and follow only where codes do.
                Some(
                    &ValueType::Path {
                        domain,
                        left,
                        right,
                    }
                    | &ValueType::Flow {
                        domain,
                        source: left,
                        target: right,
                    }
                    | &ValueType::Bridge {
                        domain,
                        left,
                        right,
                    },
                ) => {
                    pending.push(AnyNode::ValueType(domain));
                    if follow {
                        pending.push(AnyNode::Value(left));
                        pending.push(AnyNode::Value(right));
                    }
                },
                Some(&ValueType::Element { code, .. }) => {
                    if follow {
                        pending.push(AnyNode::Value(code));
                    }
                },
                Some(&ValueType::Base(_) | &ValueType::Universe { .. }) | None => {},
                Some(&ValueType::Product(ref parts) | &ValueType::Sum(ref parts)) => {
                    pending.extend(parts.iter().copied().map(AnyNode::ValueType));
                },
                Some(
                    &ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    }
                    | &ValueType::Sigma { first, second },
                ) => {
                    pending.push(AnyNode::ValueType(first));
                    pending.push(AnyNode::ValueType(second));
                },
                Some(
                    &ValueType::Session {
                        payloads: inner, ..
                    }
                    | &ValueType::Lift { inner, .. }
                    | &ValueType::List(inner)
                    | &ValueType::Staged { base: inner, .. },
                ) => {
                    pending.push(AnyNode::ValueType(inner));
                },
                Some(&ValueType::Thunk(body)) => pending.push(AnyNode::CompType(body)),
            },
            AnyNode::CompType(id) => match arena.comp_type(id) {
                Some(&CompType::Returner(result)) => pending.push(AnyNode::ValueType(result)),
                Some(
                    &CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain },
                ) => {
                    pending.push(AnyNode::ValueType(domain));
                    pending.push(AnyNode::CompType(codomain));
                },
                Some(&CompType::Element { code, .. }) => {
                    if follow {
                        pending.push(AnyNode::Value(code));
                    }
                },
                Some(&CompType::With(ref components)) => {
                    pending.extend(components.iter().copied().map(AnyNode::CompType));
                },
                Some(&CompType::Codata {
                    declaration,
                    ref arguments,
                }) if follow => {
                    if sink.meet(declaration) == Mention::Named {
                        return Mention::Named;
                    }
                    pending.extend(arguments.iter().copied().map(AnyNode::Value));
                },
                Some(&CompType::Codata { .. }) | None => {},
            },
        }
    }
    Mention::Unnamed
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

/// A search for one constant through codes and sealed atoms alike, over as
/// many roots as it is asked about.
///
/// The search keeps the nodes it expanded for every root it answered
/// `Unnamed` for, so asking about the parts of one type walks the nodes they
/// share once, and it stops at the first node naming the constant.
#[derive(Debug)]
pub(crate) struct ConstantSearch
{
    /// The constant sought.
    sought: ConstantIndex,
    /// The walk, closed under children over every node it has expanded.
    walk: Walk,
}

impl ConstantSearch
{
    /// A search for `sought` that has expanded nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn new(sought: ConstantIndex) -> Self
    {
        Self {
            sought,
            walk: Walk::default(),
        }
    }

    /// Whether `root` names the constant sought, through codes and sealed
    /// atoms alike.
    ///
    /// # Specification
    /// - requires: nothing — an unreadable id names nothing.
    /// - ensures: `Named` exactly when the constant sought is among the
    ///   constants [`collect_reachable`] reaches from `root` under
    ///   [`CodeEdges::Follow`], whatever roots the search answered before.
    /// - provides: an occurrence test that stops at the first occurrence and
    ///   keeps no set of the constants it passes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant reached through a code and one reached
    ///   through a sealed atom are each found; a root sharing a node with one
    ///   answered `Unnamed` before is still answered `Unnamed`, and one
    ///   reaching the constant after a root that named it is still answered
    ///   `Named`.
    /// - witness: `env::tests::a_search_stops_at_its_constant_across_roots`
    #[spec(ensures: |ret| (ret == Mention::Named) == collect_reachable(arena, root, CodeEdges::Follow).contains(&self.sought))]
    pub(crate) fn names(
        &mut self,
        arena: &TermArena,
        root: AnyNode,
    ) -> Mention
    {
        let mention = reach(
            arena,
            root,
            CodeEdges::Follow,
            &mut self.walk,
            &mut Sink::Seek(self.sought),
        );
        if mention == Mention::Named {
            // A walk that stopped is not closed under children: the next
            // root starts afresh.
            self.walk.seen.clear();
            self.walk.pending.clear();
        }
        mention
    }
}

/// The atoms a value type projects onto: every sealed atom reachable from it.
///
/// **Sealed atoms only, and the exclusion is the gate rather than an
/// omission.** The provenance slot claims which atoms a sealing projection
/// rebound, and the gate checks that claim by requiring every claimed atom to
/// occur here. Unioning the constants a code names would let a provenance entry
/// naming an ordinary definition pass, which is a strictly more permissive gate
/// on the one surface whose whole job is to be falsifiable.
///
/// # Specification
/// - requires: `root` is a declared value-type root of this arena.
/// - ensures: every sealed atom reachable from `root`, and no constant a code
///   names, since the walk stops at code edges.
/// - provides: the falsifiable set a sealing-provenance claim is checked
///   against. Unioning the constants a code names would admit a provenance
///   entry naming an ordinary definition, which is a strictly more permissive
///   gate on the one surface whose whole job is to be falsifiable.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a direct sealed atom is retained, while a value decoded
///   from a constant contributes no projected atom. The existing sealing test
///   verifies that a constant reachable only through a code cannot justify a
///   provenance entry.
/// - witness: `env::tests::reachability_separates_references_and_code_edges`
/// - witness: `env::tests::sealing_provenance_does_not_follow_codes`
#[spec(ensures: |ret| match arena.value_type(root) {
    Some(&ValueType::Abstract(index)) => ret.len() == 1_usize && ret.contains(&index),
    Some(&ValueType::Data { .. } | &ValueType::Base(_) | &ValueType::Universe { .. } | &ValueType::Element { .. }) | None => ret.is_empty(),
    Some(held) if held.product_parts() == Some(&[]) => ret.is_empty(),
    _ => true,
})]
#[inline]
pub(crate) fn projected_atoms(
    arena: &TermArena,
    root: ValueTypeId,
) -> BTreeSet<ConstantIndex>
{
    collect_reachable(arena, AnyNode::ValueType(root), CodeEdges::Stop)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec;

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
    use gandr_kernel_term::Seam;
    use gandr_kernel_term::StringLiteral;
    use gandr_kernel_term::TermArena;

    use super::Environment;
    use super::OutstandingCount;
    use super::StagedDeclaration;
    use super::StagedMarks;
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

    #[test]
    fn a_rejected_declaration_leaves_the_environment_unchanged()
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
        assert!(environment.entries().is_empty(), "with nothing appended");
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
    fn a_rejection_keeps_bypassed_content_resolvable()
    {
        let mut environment = Environment::new();
        let bypassed = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let bypassed = environment.add_decl_unchecked(bypassed);
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
        let bypassed = environment.add_decl_unchecked(bypassed);
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
    /// - witness: `env::tests::outstanding_later_staged_content_refuses_admission`
    /// - witness: `env::tests::abandoning_a_staged_declaration_releases_its_claim`
    #[spec(captures: [entry_mark = environment.arena().watermark(), entry_len = environment.outstanding.marks.len()],
    ensures: |ret| ret.content_start == entry_mark
        && environment.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
        && environment.outstanding.marks.last() == Some(&entry_mark)
        && match *ret.declaration.content() {
            super::DeclarationContent::Def { declared, body } =>
                matches!(environment.arena().value_type(declared), Some(super::ValueType::Product(parts)) if parts.is_empty())
                && matches!(environment.arena().value(body).and_then(super::Value::components), Some(&[])),
            super::DeclarationContent::Data { .. } | super::DeclarationContent::Codata { .. } | super::DeclarationContent::Axiom { .. } | super::DeclarationContent::AbstractType { .. } => false,
        })]
    fn stage_unit(environment: &mut Environment) -> StagedDeclaration
    {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    }

    #[test]
    fn registration_resolution_preserves_multiplicity_and_order()
    {
        let mut arena = TermArena::new();
        let low = arena.watermark();
        let _value = arena.value_unit();
        let middle = arena.watermark();
        let unit = arena.value_type_unit();
        let _returner = arena.comp_type_returner(unit);
        let high = arena.watermark();
        let mut marks = StagedMarks::default();
        for mark in [middle, low, middle, high] {
            marks.register(mark);
        }
        assert_eq!([middle, low, middle, high], marks.marks.as_slice());
        marks.resolve(middle);
        assert_eq!([low, middle, high], marks.marks.as_slice());
        marks.resolve(middle);
        assert_eq!([low, high], marks.marks.as_slice());
        marks.resolve(middle);
        assert_eq!([low, high], marks.marks.as_slice());
        marks.resolve(low);
        marks.resolve(high);
        assert!(marks.marks.is_empty());
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
            Some(super::ValueType::Product(parts)) if parts.is_empty()
        ));
        let report = environment.audit(admitted);
        assert!(report.axioms().is_empty());
        assert!(report.unchecked_admissions().is_empty());
    }

    #[test]
    fn reachability_separates_references_and_code_edges()
    {
        let mut arena = TermArena::new();
        let constant = ConstantIndex::from(7_usize);
        let atom = ConstantIndex::from(9_usize);
        let code = arena.value_constant(constant);
        let abstract_type = arena.value_type_abstract(atom);
        let quote = arena.value_quote(abstract_type);
        let pair = arena.value_tuple(&[code, quote]);
        assert_eq!(
            super::BTreeSet::from([constant, atom]),
            super::collect_reachable(
                &arena,
                super::AnyNode::Value(pair),
                super::CodeEdges::Follow
            ),
        );
        assert_eq!(
            super::BTreeSet::from([atom]),
            super::projected_atoms(&arena, abstract_type)
        );
        let value_decode = arena.value_type_element(code, Level::zero());
        let computation_decode = arena.comp_type_element(code, Level::zero());
        for root in [
            super::AnyNode::ValueType(value_decode),
            super::AnyNode::CompType(computation_decode),
        ] {
            assert_eq!(
                super::BTreeSet::from([constant]),
                super::collect_reachable(&arena, root, super::CodeEdges::Follow),
            );
            assert!(super::collect_reachable(&arena, root, super::CodeEdges::Stop).is_empty());
        }
        assert!(super::projected_atoms(&arena, value_decode).is_empty());
    }

    #[test]
    fn unreadable_roots_contribute_no_references()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let value = arena.value_constant(ConstantIndex::from(7_usize));
        let computation = arena.computation_return(value);
        let value_type = arena.value_type_abstract(ConstantIndex::from(9_usize));
        let comp_type = arena.comp_type_returner(value_type);
        arena.truncate_to(before);
        for root in [
            super::AnyNode::Value(value),
            super::AnyNode::Computation(computation),
            super::AnyNode::ValueType(value_type),
            super::AnyNode::CompType(comp_type),
        ] {
            assert!(super::collect_reachable(&arena, root, super::CodeEdges::Follow).is_empty());
        }
    }

    #[test]
    fn a_search_stops_at_its_constant_across_roots()
    {
        let mut arena = TermArena::new();
        let (constant, atom, other) = (
            ConstantIndex::from(7_usize),
            ConstantIndex::from(9_usize),
            ConstantIndex::from(11_usize),
        );
        let code = arena.value_constant(constant);
        let decoded = arena.value_type_element(code, Level::zero());
        let sealed = arena.value_type_abstract(atom);
        let elsewhere = arena.value_type_abstract(other);
        // Every root reaches `shared`, which names only `other`.
        let shared = arena.value_type_list(elsewhere);
        let through_code = arena.value_type_product(&[shared, decoded]);
        let through_atom = arena.value_type_product(&[shared, sealed]);
        let alone = arena.value_type_product(&[shared]);
        let root = super::AnyNode::ValueType;

        let mut search = super::ConstantSearch::new(atom);
        assert_eq!(search.names(&arena, root(alone)), super::Mention::Unnamed);
        assert_eq!(
            search.names(&arena, root(through_atom)),
            super::Mention::Named,
            "a root past the nodes an earlier one expanded"
        );
        assert_eq!(search.names(&arena, root(alone)), super::Mention::Unnamed);

        let mut search = super::ConstantSearch::new(constant);
        assert_eq!(
            search.names(&arena, root(through_code)),
            super::Mention::Named,
            "a constant inside a code"
        );
        assert_eq!(
            search.names(&arena, root(through_atom)),
            super::Mention::Unnamed
        );

        let mut search = super::ConstantSearch::new(other);
        assert_eq!(
            search.names(&arena, root(through_code)),
            super::Mention::Named
        );
        assert_eq!(
            search.names(&arena, root(through_atom)),
            super::Mention::Named,
            "a stopped walk keeps nothing it did not finish"
        );
    }

    /// The walk reaches a constant through every child slot of the formers
    /// that hold one beside other children: each root names the constant
    /// once, and nothing else.
    #[test]
    fn reachability_descends_into_every_former()
    {
        let mut arena = TermArena::new();
        let constant = ConstantIndex::from(7_usize);
        let code = arena.value_constant(constant);
        let unit = arena.value_unit();
        let done = arena.computation_return(unit);
        let one = arena.value_type_unit();
        let decoded = arena.value_type_element(code, Level::zero());
        let returns = arena.comp_type_returner(decoded);
        let static_pi = arena.value_type_static_pi(decoded, one);
        let sigma = arena.value_type_sigma(one, decoded);
        let fold = arena.computation_list_fold(one, one, code, done, done);
        let related = arena.computation_related_application(code, (unit, unit), unit, done);
        let roots = [
            ("c ()", arena.value_static_application(code, unit)),
            ("⌜F (El c)⌝", arena.value_quote_computation(returns)),
            ("⌜El c ⇒ 1⌝", arena.value_quote(static_pi)),
            ("⌜Σ 1. El c⌝", arena.value_quote(sigma)),
            ("c then ()", arena.value_then(code, unit, Seam::Sequence)),
            ("thunk (fold c)", arena.value_thunk(fold)),
            ("thunk (apply c)", arena.value_thunk(related)),
        ];
        for (what, root) in roots {
            assert_eq!(
                super::BTreeSet::from([constant]),
                super::collect_reachable(
                    &arena,
                    super::AnyNode::Value(root),
                    super::CodeEdges::Follow
                ),
                "{what}"
            );
        }
    }

    #[test]
    fn marks_above_are_counted_componentwise()
    {
        let mut arena = TermArena::new();
        let low = arena.watermark();
        let _value = arena.value_unit();
        let middle = arena.watermark();
        // A family the middle mark did not move, so the two marks are ordered
        // in a family the lexicographic tuple order would not have led with.
        let unit_type = arena.value_type_unit();
        let _comp_type = arena.comp_type_returner(unit_type);
        let high = arena.watermark();

        let mut marks = StagedMarks::default();
        marks.register(middle);
        marks.register(high);
        assert_eq!(
            OutstandingCount::from(2_usize),
            marks.above(low),
            "both marks sit above the floor"
        );
        assert_eq!(
            OutstandingCount::from(1_usize),
            marks.above(middle),
            "an equal mark is not above itself, so only the higher one counts"
        );
        assert_eq!(
            OutstandingCount::from(0_usize),
            marks.above(high),
            "and nothing sits above the top"
        );
        marks.resolve(middle);
        assert_eq!(
            OutstandingCount::from(1_usize),
            marks.above(low),
            "resolving one mark removes exactly one"
        );
        marks.resolve(middle);
        assert_eq!(
            OutstandingCount::from(1_usize),
            marks.above(low),
            "and resolving a mark that is not held removes nothing"
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
        assert!(environment.entries().is_empty(), "with nothing appended");

        // The producer's remedy: resolve the later staging, then retry. The
        // retry now runs the check, and refuses on the declaration's own merits.
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
        assert_eq!(vec![first.content_start], environment.outstanding.marks);
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
        let sealed = environment.add_decl_unchecked(sealed);
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
}
