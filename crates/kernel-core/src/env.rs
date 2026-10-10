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
//! watermark as of the most recent admission, checked or bypassed — and a
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

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ArenaWatermark;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::LevelSignature;
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
    ///   retain insertion order and are resolved one occurrence at a time.
    /// - witness: `env::tests::registration_resolution_preserves_multiplicity_and_order`
    #[spec(
        captures: [entry_len = self.marks.len(), entry_count = self.marks.iter().filter(|&&held| held == mark).count()],
        ensures: self.marks.len().checked_sub(1_usize) == Some(entry_len)
            && self.marks.last() == Some(&mark)
            && self.marks.iter().filter(|&&held| held == mark).count().checked_sub(1_usize) == Some(entry_count)
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

    /// Finalize a sealed abstract type at an already-minted universe kind.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned abstract type retains that start mark and the
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
            && *ret.declaration.content() == DeclarationContent::AbstractType { kind }
    )]
    #[inline]
    #[must_use]
    pub fn abstract_type(
        self,
        levels: LevelSignature,
        kind: ValueTypeId,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            declaration: self.builder.abstract_type(levels, kind),
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

/// The append-only kernel environment: one arena, and the admitted
/// declarations in admission order.
#[derive(Clone, Debug, Default)]
pub struct Environment
{
    /// The one arena every declaration's content lives in.
    arena: TermArena,
    /// The admitted declarations, in admission order.
    entries: Vec<AdmittedDeclaration>,
    /// The admission floor: the watermark as of the most recent admission,
    /// checked or bypassed. No rejection truncates below it.
    admission_floor: ArenaWatermark,
    /// The content-start marks of declarations staged into the arena and not
    /// yet resolved. What a rejection may not truncate through.
    outstanding: StagedMarks,
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
            | Ok(levels) => levels,
            | Err(error) => {
                self.arena.truncate_to(rejected);
                return Err(error);
            },
        };
        let outcome = {
            let Self {
                ref mut arena,
                ref entries,
                ..
            } = *self;
            check::check_declaration(arena, entries, &levels, &declaration)
        };
        match outcome {
            | Ok(()) => {
                // Keep this declaration's content; drop the intermediates that
                // allocated past it.
                self.arena.truncate_to(content_end);
                self.admission_floor = content_end;
                let rested_on =
                    self.transitive_rest(declaration.content(), position, Admission::Checked);
                self.entries.push(AdmittedDeclaration {
                    declaration,
                    admission: Admission::Checked,
                    rested_on,
                });
                Ok(CheckedId::new(position))
            },
            | Err(error) => {
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
        let rested_on = self.transitive_rest(declaration.content(), position, Admission::Unchecked);
        self.entries.push(AdmittedDeclaration {
            declaration,
            admission: Admission::Unchecked,
            rested_on,
        });
        CheckedId::new(position)
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
    /// an abstract type's own kind included.
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
    /// - requires: `position` is the next admission index and `content` is its
    ///   declaration. Checked references name earlier admissions; a bypass is
    ///   itself an audit reason even if it names an unknown position.
    /// - ensures: the union of the audits of every position the declared type
    ///   or a definition's body names, with `position` itself included exactly
    ///   when the declaration is an axiom or is being bypassed. Both reference
    ///   forms of the type plane are followed — a sealed atom directly, and a
    ///   code through the term language — so a declaration reachable only
    ///   through a code stays in the graph.
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
        position: ConstantIndex,
        admission: Admission,
    ) -> BTreeSet<ConstantIndex>
    {
        let mut direct = audited_type_constants(&self.arena, content.declared_id());
        if let DeclarationContent::Def { body, .. } = *content {
            direct.append(&mut collect_reachable(
                &self.arena,
                AnyNode::Value(body),
                CodeEdges::Follow,
            ));
        }
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
/// # Termination
/// - reason: the walk is a loop over one explicit worklist, not recursion.
/// - measure: lexicographically, reachable node identities not yet seen and
///   pending worklist length. First visits reduce the former; revisits enqueue
///   nothing and reduce the latter.
/// - boundedness: the finite arena and its finite child-reference fields bound
///   the reachable identities, including unreadable ones.
/// - input recursion: none.
#[spec(ensures: |ret| match root {
    AnyNode::Value(id) => match arena.value(id) {
        Some(&Value::Constant(index)) => ret.len() == 1_usize && ret.contains(&index),
        Some(&Value::Variable(_) | &Value::Unit | &Value::Literal(_)) | None => ret.is_empty(),
        _ => true,
    },
    AnyNode::Computation(id) => arena.computation(id).is_some() || ret.is_empty(),
    AnyNode::ValueType(id) => match arena.value_type(id) {
        Some(&ValueType::Abstract(index)) => ret.len() == 1_usize && ret.contains(&index),
        Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Universe { .. }) | None => ret.is_empty(),
        Some(&ValueType::Element { .. }) if matches!(codes, CodeEdges::Stop) => ret.is_empty(),
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
    // Each arena node is expanded once. The walk computes the *set* of
    // reachable constants, so re-walking a shared subtree can only re-derive
    // what is already recorded — and without the seen set the walk
    // tree-expands the graph, which is exponential in sharing depth.
    let mut seen: BTreeSet<AnyNode> = BTreeSet::new();
    let mut pending: Vec<AnyNode> = Vec::new();
    pending.push(root);
    let follow = matches!(codes, CodeEdges::Follow);
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        match node {
            | AnyNode::Value(id) => match arena.value(id) {
                | Some(&Value::Constant(index)) => {
                    let _fresh = found.insert(index);
                },
                | Some(&Value::Variable(_) | &Value::Unit | &Value::Literal(_)) | None => {},
                | Some(&Value::Pair(first, second) | &Value::StaticApplication(first, second)) => {
                    pending.push(AnyNode::Value(first));
                    pending.push(AnyNode::Value(second));
                },
                | Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                    pending.push(AnyNode::Value(body));
                },
                | Some(&Value::Thunk(body)) => pending.push(AnyNode::Computation(body)),
                | Some(&Value::Quote(quoted)) => pending.push(AnyNode::ValueType(quoted)),
                | Some(&Value::QuoteComputation(quoted)) => pending.push(AnyNode::CompType(quoted)),
            },
            | AnyNode::Computation(id) => match arena.computation(id) {
                | Some(&Computation::Lambda(body)) => pending.push(AnyNode::Computation(body)),
                | Some(&Computation::Application(head, argument)) => {
                    pending.push(AnyNode::Computation(head));
                    pending.push(AnyNode::Value(argument));
                },
                | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                    pending.push(AnyNode::Value(value));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    pending.push(AnyNode::Computation(bound));
                    pending.push(AnyNode::Computation(body));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    pending.push(AnyNode::Value(scrutinee));
                    pending.push(AnyNode::Computation(on_left));
                    pending.push(AnyNode::Computation(on_right));
                },
                | None => {},
            },
            | AnyNode::ValueType(id) => match arena.value_type(id) {
                | Some(&ValueType::Abstract(index)) => {
                    let _fresh = found.insert(index);
                },
                | Some(&ValueType::Element { code, .. }) => {
                    if follow {
                        pending.push(AnyNode::Value(code));
                    }
                },
                | Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Universe { .. })
                | None => {},
                | Some(
                    &ValueType::Product(first, second)
                    | &ValueType::Sum(first, second)
                    | &ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    },
                ) => {
                    pending.push(AnyNode::ValueType(first));
                    pending.push(AnyNode::ValueType(second));
                },
                | Some(&ValueType::Lift { inner, .. }) => pending.push(AnyNode::ValueType(inner)),
                | Some(&ValueType::Thunk(body)) => pending.push(AnyNode::CompType(body)),
            },
            | AnyNode::CompType(id) => match arena.comp_type(id) {
                | Some(&CompType::Returner(result)) => pending.push(AnyNode::ValueType(result)),
                | Some(
                    &CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain },
                ) => {
                    pending.push(AnyNode::ValueType(domain));
                    pending.push(AnyNode::CompType(codomain));
                },
                | Some(&CompType::Element { code, .. }) => {
                    if follow {
                        pending.push(AnyNode::Value(code));
                    }
                },
                | None => {},
            },
        }
    }
    found
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
    Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Universe { .. } | &ValueType::Element { .. }) | None => ret.is_empty(),
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

    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Literal;
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
            staging.abstract_type(LevelSignature::monomorphic(), kind)
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
    #[anodized::spec(
        captures: [entry_mark = environment.arena().watermark(), entry_len = environment.outstanding.marks.len()],
        ensures: |ret| ret.content_start == entry_mark
            && environment.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
            && environment.outstanding.marks.last() == Some(&entry_mark)
            && match *ret.declaration.content() {
                super::DeclarationContent::Def { declared, body } =>
                    matches!(environment.arena().value_type(declared), Some(&super::ValueType::Unit))
                    && matches!(environment.arena().value(body), Some(&super::Value::Unit)),
                _ => false,
            }
    )]
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
            Some(&super::ValueType::Unit)
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
        let pair = arena.value_pair(code, quote);
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
                Err(KernelError::ValueTypeMismatch(_))
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
                    | Finisher::Definition => {
                        staging.def(LevelSignature::monomorphic(), declared, body)
                    },
                    | Finisher::SealedDefinition => {
                        staging.sealed_def(LevelSignature::monomorphic(), declared, body, vec![])
                    },
                    | Finisher::Axiom => staging.axiom(LevelSignature::monomorphic(), declared),
                    | Finisher::AbstractType => {
                        staging.abstract_type(LevelSignature::monomorphic(), kind)
                    },
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
}
