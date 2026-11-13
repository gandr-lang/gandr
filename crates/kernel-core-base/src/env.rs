//! The record of admitted declarations.
//!
//! The record holds its entries, each admitted declaration with its block
//! and its unit, and the staging of the content of a declaration. It names
//! no part of the judgement. `Environment` admits each declaration into the
//! record.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ArenaWatermark;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Declaration;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Family;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::SourceRank;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::census::ExpansionCensus;
use crate::encoding::ConstantName;

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
    #[must_use]
    pub const fn new(position: ConstantIndex) -> Self
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

/// How a declaration was admitted: checked here, recalled, or through the
/// warned bypass.
///
/// A recalled declaration stands on a verdict a trusted kernel recorded for
/// the same input: what the declaration reads, or the whole admitted prefix.
/// A provenance, never a trust lattice: a recalled admission was checked, by
/// the kernel that signed its receipt.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Admission
{
    /// Admitted through `Environment::add_decl`, fully checked.
    Checked,
    /// Admitted through `Environment::add_decl` on a recorded verdict whose
    /// receipt a trusted signer gave.
    Recalled,
    /// Admitted through `Environment::add_decl_unchecked`, trusted and
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
    /// The rank its source gives it; none for the rank of a fresh
    /// admission, which is its position.
    rank: Option<SourceRank>,
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

    /// Where this declaration's content begins in the environment's arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content_start(&self) -> ArenaWatermark
    {
        self.content_start
    }

    /// The rank its source gives it; none for the rank of a fresh
    /// admission, which is its position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rank(&self) -> Option<SourceRank>
    {
        self.rank
    }

    /// The declaration the stage holds, with the stage spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_declaration(self) -> Declaration
    {
        self.declaration
    }

    /// The declaration `declaration`, staged at `content_start` and ranked at
    /// `rank` when a source states one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        content_start: ArenaWatermark,
        rank: Option<SourceRank>,
        declaration: Declaration,
    ) -> Self
    {
        Self {
            content_start,
            declaration,
            rank,
        }
    }

    /// The parts of the stage, with the stage spent: where its content starts,
    /// its rank and its declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (ArenaWatermark, Option<SourceRank>, Declaration)
    {
        (self.content_start, self.rank, self.declaration)
    }

    /// This staged declaration ranked at `rank` in its source, its content
    /// start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — admission refuses a rank a live entry holds.
    /// - ensures: the same declaration at the same content start, ranked at
    ///   `rank`.
    /// - provides: how a readmission places an appended declaration where its
    ///   source states it, so each reader of ranks answers as over a fresh
    ///   admission of that source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition ranked below an earlier admission
    ///   orients its rules as though admitted before it.
    /// - witness: `gandr-kernel-core::ruled::tests::a_rank_below_an_earlier_admission_orients_as_admitted_before_it_6621`
    #[spec(ensures: |ret| ret.rank == Some(rank))]
    #[inline]
    #[must_use]
    pub fn ranked(
        self,
        rank: SourceRank,
    ) -> Self
    {
        Self {
            rank: Some(rank),
            ..self
        }
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
    /// - witness: `gandr-kernel-core::element_identity::tests::a_definition_relating_compound_endpoints_admits_274`
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
    /// - witness: `gandr-kernel-core::tests::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
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
    /// - witness: `gandr-kernel-core::ruled::tests::rules_over_the_environment_admit_and_a_forged_pair_is_refused`
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
    /// - witness: `gandr-kernel-core::tests::quantified::a_helper_at_a_stage_takes_a_recursion_s_claim`
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

    /// This staged definition carrying `covers` as its matches' derivations,
    /// its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — admission replays each derivation against the tree
    ///   its root names.
    /// - ensures: the declaration as [`Declaration::covered`] leaves it, at the
    ///   same content start: a definition carries exactly `covers`, any other
    ///   declaration is unchanged.
    /// - provides: how a producer attaches its matches' derivations before
    ///   offering the definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a match's derivation crosses and the kernel replays
    ///   it.
    /// - witness: `gandr-kernel-core::tests::cover::every_broken_derivation_is_refused_by_its_rule_5104`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. }), self.declaration.covers().len(), covers.len()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.covers().len() == if entry.1 { entry.3 } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn covered(
        self,
        covers: Vec<gandr_kernel_term::cover::Covered>,
    ) -> Self
    {
        Self {
            declaration: self.declaration.covered(covers),
            ..self
        }
    }

    /// This staged data declaration or definition holding the built-in
    /// `role`, its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the choke point validates the holder against the
    ///   role's canonical form.
    /// - ensures: the declaration as [`Declaration::held`] leaves it, at the
    ///   same content start: a data declaration or a definition holds exactly
    ///   `role`, any other declaration is unchanged.
    /// - provides: how a producer attaches a role before offering the
    ///   declaration.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a canonical holder admits with its role, and a
    ///   departing one is refused at its departure.
    /// - witness: `gandr-kernel-core::builtin::tests::a_role_s_holder_is_admitted_in_its_canonical_form_5304`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Def { .. } | DeclarationContent::Data { .. }), self.declaration.role()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.role() == if entry.1 { Maybe::Present(role) } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn held(
        self,
        role: gandr_kernel_term::Builtin,
    ) -> Self
    {
        Self {
            declaration: self.declaration.held(role),
            ..self
        }
    }

    /// This staged data declaration read as the greatest fixpoint of its
    /// constructors, its content start and content unchanged.
    ///
    /// # Specification
    /// - requires: nothing — the choke point refuses a coinductive datatype
    ///   with indices, rules, cells or a role, or inside a mutual block.
    /// - ensures: the declaration as [`Declaration::coinductive`] leaves it, at
    ///   the same content start: a data declaration is
    ///   [`gandr_kernel_term::DataFixpoint::Greatest`], any other declaration
    ///   is unchanged.
    /// - provides: how a producer stages a coinductive datatype at the value
    ///   universe before offering it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the delay type admits as a coinductive datatype, and
    ///   a guarded fixpoint into it admits where the same fixpoint into the
    ///   inductive datatype is refused.
    /// - witness: `gandr-kernel-core::tests::guard::a_guarded_fixpoint_stands_only_at_a_coinductive_type`
    #[spec(
        captures: entry = (self.content_start, matches!(self.declaration.content(), DeclarationContent::Data { .. }), self.declaration.fixpoint()),
        ensures: |ret| ret.content_start == entry.0
            && ret.declaration.fixpoint() == if entry.1 { gandr_kernel_term::DataFixpoint::Greatest } else { entry.2 },
    )]
    #[inline]
    #[must_use]
    pub fn coinductive(self) -> Self
    {
        Self {
            declaration: self.declaration.coinductive(),
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
    /// - witness: `gandr-kernel-core::environment::presented_tests::a_circle_word_normalizes_keeping_what_it_did_not_touch`
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
    /// - witness: `gandr-kernel-core::element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
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

/// How many released checks of an environment are not settled.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnsettledCount(usize);

impl From<usize> for UnsettledCount
{
    /// The count of `count` released checks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<UnsettledCount> for usize
{
    /// How many released checks `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: UnsettledCount) -> Self
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
pub struct StagedMarks
{
    /// The outstanding marks, in registration order.
    pub marks: Vec<ArenaWatermark>,
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
    pub fn register(
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
    pub fn resolve(
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
    #[must_use]
    pub fn above(
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
pub struct StagingClaim<'env>
{
    /// The nonempty multiset whose final entry belongs to this session.
    pub outstanding: &'env mut StagedMarks,
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
    /// - witness: `gandr-kernel-core::environment::tests::implicit_staging_drop_releases_its_claim`
    /// - witness: `gandr-kernel-core::environment::tests::an_abandoned_staging_releases_its_claim`
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
    #[inline]
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
/// mark is resolved by `Environment::add_decl`,
/// `Environment::add_decl_unchecked`, or `Environment::abandon`.
pub struct Staging<'env>
{
    /// The wrapped builder, which owns the rollback.
    builder: DeclarationBuilder<'env>,
    /// The final registration, dropped after the builder rolls back the arena.
    claim: StagingClaim<'env>,
    /// The session's table, which a fold that mints the content borrows to
    /// name each image at mint ([`Self::minting`]).
    table: &'env mut crate::encoding::ContentTable,
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
    /// - witness: `gandr-kernel-core::tests::native_formers::data_signature_formation_checks_fields_and_parameters`
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
            rank: None,
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
    /// - witness: `gandr-kernel-core::tests::codata::a_value_universe_is_no_codata_kind`
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
            rank: None,
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
    /// - witness: `gandr-kernel-core::tests::native_formers::an_indexed_family_states_its_result_indices`
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
            rank: None,
            declaration: self.builder.indexed(levels, parameters, table, kind),
        }
    }

    /// Begin staging into `arena`, registering the content-start mark, with
    /// the session's `table` to lend a fold that names each image at mint.
    ///
    /// # Specification
    /// - requires: `arena` is the environment's own, `outstanding` its own mark
    ///   multiset, and `table` its session's table, which names the constants
    ///   `arena` holds content for.
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
    /// - witness: `gandr-kernel-core::environment::tests::implicit_staging_drop_releases_its_claim`
    #[spec(
        captures: [entry_mark = arena.watermark(), entry_len = outstanding.marks.len()],
        ensures: |ret| ret.builder.content_start() == entry_mark
            && ret.claim.outstanding.marks.len().checked_sub(1_usize) == Some(entry_len)
            && ret.claim.outstanding.marks.last() == Some(&entry_mark)
    )]
    #[inline]
    pub fn new(
        arena: &'env mut TermArena,
        outstanding: &'env mut StagedMarks,
        table: &'env mut crate::encoding::ContentTable,
    ) -> Self
    {
        let builder = DeclarationBuilder::new(arena);
        outstanding.register(builder.content_start());
        Self {
            builder,
            claim: StagingClaim { outstanding },
            table,
        }
    }

    /// The wrapped builder, which owns the rollback.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn builder(&self) -> &DeclarationBuilder<'env>
    {
        &self.builder
    }

    /// The final registration, dropped after the builder rolls back the arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn claim(&self) -> &StagingClaim<'env>
    {
        &self.claim
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

    /// The borrowed arena, and the session's table lent as the names a fold
    /// gives each image it mints there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn minting(&mut self) -> (&mut TermArena, crate::encoding::MintNames<'_>)
    {
        (
            self.builder.arena(),
            crate::encoding::MintNames::new(self.table),
        )
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
    /// - witness: `gandr-kernel-core::environment::tests::an_abandoned_staging_leaves_the_arena_unchanged`
    /// - witness: `gandr-kernel-core::environment::tests::an_abandoned_staging_releases_its_claim`
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
    /// - witness: `gandr-kernel-core::environment::tests::every_finisher_retains_its_claim_until_admission`
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
            rank: None,
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
    /// - witness: `gandr-kernel-core::environment::tests::every_finisher_retains_its_claim_until_admission`
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
            rank: None,
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
    /// - witness: `gandr-kernel-core::environment::tests::every_finisher_retains_its_claim_until_admission`
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
            rank: None,
            declaration: self.builder.axiom(levels, declared),
        }
    }

    /// Finalize a literal identity test over an already-minted declared type.
    ///
    /// # Specification
    /// - requires: this session owns the final registration for its builder's
    ///   start mark, as established by construction and its exclusive borrow.
    /// - ensures: the returned test retains that start mark, the supplied level
    ///   signature, its root and its test. Its arena content and registration
    ///   remain live until admission, bypass, or abandonment.
    /// - provides: ownership transfer from a borrowing session to a staged
    ///   declaration without triggering either rollback or claim release.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a test staged at its base's type admits and one at
    ///   another type is refused.
    /// - witness: `gandr-kernel-core::check::tests::a_literal_identity_test_admits_only_at_its_base_s_type`
    #[spec(
        requires: self.claim.outstanding.marks.last() == Some(&self.builder.content_start()),
        captures: [entry_start = self.builder.content_start()],
        ensures: |ret| ret.content_start == entry_start
            && *ret.declaration.content() == DeclarationContent::LiteralIdentity { declared, test }
    )]
    #[inline]
    #[must_use]
    pub fn literal_identity(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        test: gandr_kernel_term::LiteralIdentity,
    ) -> StagedDeclaration
    {
        let content_start = self.builder.content_start();
        let _kept = core::mem::ManuallyDrop::new(self.claim);
        StagedDeclaration {
            content_start,
            rank: None,
            declaration: self.builder.literal_identity(levels, declared, test),
        }
    }

    /// Finalize a sealed abstract type at an already-minted universe kind, over
    /// an already-minted representation, with the scope of its minting
    /// admission.
    ///
    /// A producer sealing a module stages its atoms [`SealScope::Open`] and
    /// closes them with `Environment::seal` once the module's members are
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
    /// - witness: `gandr-kernel-core::environment::tests::every_finisher_retains_its_claim_until_admission`
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
            rank: None,
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
    /// The transitive positions of axioms, unchecked admissions and literal
    /// identity tests this declaration rests on, itself included when it is
    /// one. Precomputed at admission, so the audit is a lookup.
    rested_on: BTreeSet<ConstantIndex>,
    /// The positions its content names, ascending: what joins a check's
    /// support when the check reads it. A mutual block's members each keep the
    /// references of the whole block.
    references: Box<[ConstantIndex]>,
    /// The block it was admitted in: its own position alone unless a mutual
    /// block admitted it, whose families share one stage.
    block: crate::occurrence::Block,
    /// What the occurrence walk decided of it: a family's stratification and
    /// its parameters' variance; the reading that admits least for anything
    /// no walk read.
    accessibility: crate::occurrence::Accessibility,
    /// How a memo key names a reference to it, decided at admission.
    key_name: ConstantName,
    /// What its check charged: each goal expanded, recalled from the check's
    /// memo or answered by an earlier admission's kept outcome, per plane.
    /// Empty when a recorded verdict or the bypass admitted it, since neither
    /// runs a check. [`AdmittedDeclaration::census`] answers it only for a
    /// checked admission.
    census: ExpansionCensus,
    /// Its entry key: what its admission read, each position named by its
    /// entry's key. Absent when the policy rechecks, the bypass admitted it or
    /// an input of it has no entry key.
    key: Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>,
    /// Its rank in the source of the revision that holds it: what every
    /// reader of "admitted before" compares.
    rank: SourceRank,
    /// Its kind: live, or retired by a readmission.
    kind: EntryKind,
    /// The positions of the unit that admitted it: its own position alone,
    /// or the members of its mutual block.
    unit: Unit,
}

/// The parts of an admitted declaration that an admission hands the record:
/// each part but its kind, since an admitted declaration enters live.
pub struct AdmittedParts
{
    /// The declaration itself.
    pub declaration: Declaration,
    /// Whether it was checked or bypassed.
    pub admission: Admission,
    /// The transitive positions of axioms, unchecked admissions and literal
    /// identity tests this declaration rests on, itself included when it is
    /// one. Precomputed at admission, so the audit is a lookup.
    pub rested_on: BTreeSet<ConstantIndex>,
    /// The positions its content names, ascending: what joins a check's
    /// support when the check reads it. A mutual block's members each keep the
    /// references of the whole block.
    pub references: Box<[ConstantIndex]>,
    /// The block it was admitted in: its own position alone unless a mutual
    /// block admitted it, whose families share one stage.
    pub block: crate::occurrence::Block,
    /// What the occurrence walk decided of it: a family's stratification and
    /// its parameters' variance; the reading that admits least for anything
    /// no walk read.
    pub accessibility: crate::occurrence::Accessibility,
    /// How a memo key names a reference to it, decided at admission.
    pub key_name: ConstantName,
    /// What its check charged: each goal expanded, recalled from the check's
    /// memo or answered by an earlier admission's kept outcome, per plane.
    /// Empty when a recorded verdict or the bypass admitted it, since neither
    /// runs a check. [`AdmittedDeclaration::census`] answers it only for a
    /// checked admission.
    pub census: ExpansionCensus,
    /// Its entry key: what its admission read, each position named by its
    /// entry's key. Absent when the policy rechecks, the bypass admitted it or
    /// an input of it has no entry key.
    pub key: Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>,
    /// Its rank in the source of the revision that holds it: what every
    /// reader of "admitted before" compares.
    pub rank: SourceRank,
    /// The positions of the unit that admitted it: its own position alone,
    /// or the members of its mutual block.
    pub unit: Unit,
}

/// The kind of an entry: live, or retired by a readmission.
///
/// A retired entry keeps its position and its content, so no other entry
/// moves. No read sees it, no rank table holds it, and its rank is free.
/// `Environment::keep` makes it live again, at a new rank, when its own
/// key says that its check reads what it read.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EntryKind
{
    /// The entry stands live: a read sees it, and the tables hold it.
    Live,
    /// A readmission retired the entry: no read sees it.
    Retired,
}

/// The positions of the unit that admitted an entry, `first .. end`, and
/// how it was admitted.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unit
{
    /// The position of the unit's first member.
    pub first: ConstantIndex,
    /// The position past the unit's last member.
    pub end: ConstantIndex,
    /// Whether one declaration was admitted alone, or a block.
    pub shape: UnitShape,
}

/// How a unit was admitted: one declaration alone, keyed by its own key, or
/// a block, each member keyed by its place in the block's key.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnitShape
{
    /// One declaration, admitted alone.
    Lone,
    /// The members of one block, admitted together.
    Block,
}

impl Unit
{
    /// The unit of one declaration admitted alone at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lone(position: ConstantIndex) -> Self
    {
        Self {
            first: position,
            end: ConstantIndex::from(usize::from(position).saturating_add(1)),
            shape: UnitShape::Lone,
        }
    }

    /// Whether `position` is a member of the unit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holds(
        self,
        position: ConstantIndex,
    ) -> Membership
    {
        if self.first <= position && position < self.end {
            Membership::Member
        }
        else {
            Membership::Outside
        }
    }
}

/// Whether a position is a member of a unit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// The position is a member of the unit.
    Member,
    /// The position stands outside the unit.
    Outside,
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
    #[must_use]
    pub const fn content(&self) -> &DeclarationContent
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
    #[must_use]
    pub const fn block(&self) -> crate::occurrence::Block
    {
        self.block
    }

    /// What the occurrence walk decided of the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn accessibility(&self) -> &crate::occurrence::Accessibility
    {
        &self.accessibility
    }

    /// How a memo key names a reference to the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key_name(&self) -> ConstantName
    {
        self.key_name
    }

    /// The transitive positions of axioms, unchecked admissions and literal
    /// identity tests this declaration rests on, itself included when it is
    /// one. Precomputed at admission, so the audit is a lookup.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rested_on(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.rested_on
    }

    /// The positions its content names, ascending: what joins a check's
    /// support when the check reads it. A mutual block's members each keep the
    /// references of the whole block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn references(&self) -> &[ConstantIndex]
    {
        &self.references
    }

    /// The positions of the unit that admitted it: its own position alone,
    /// or the members of its mutual block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unit(&self) -> Unit
    {
        self.unit
    }

    /// Rest the declaration on `rested`: each member of a block rests on
    /// what any member rests on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn rest_on(
        &mut self,
        rested: &BTreeSet<ConstantIndex>,
    )
    {
        self.rested_on.clone_from(rested);
    }

    /// Close the open seal of the declaration at `extent`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn close(
        &mut self,
        extent: SealExtent,
    )
    {
        self.declaration = self.declaration.clone().closed(extent);
    }

    /// The live entry of an admission's `parts`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn live(parts: AdmittedParts) -> Self
    {
        let AdmittedParts {
            declaration,
            admission,
            rested_on,
            references,
            block,
            accessibility,
            key_name,
            census,
            key,
            rank,
            unit,
        } = parts;
        Self {
            declaration,
            admission,
            rested_on,
            references,
            block,
            accessibility,
            key_name,
            census,
            key,
            rank,
            kind: EntryKind::Live,
            unit,
        }
    }

    /// The declaration's entry key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn key(&self) -> Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>
    {
        self.key
    }

    /// The declaration's rank in its source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rank(&self) -> SourceRank
    {
        self.rank
    }

    /// The entry's kind: live, or retired by a readmission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> EntryKind
    {
        self.kind
    }

    /// What the declaration's check charged, goal by goal: its admission's
    /// tally, when this kernel checked it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the census its check charged when the declaration was
    ///   [`Admission::Checked`]. A recorded verdict's admission answers
    ///   [`tallied::Absent::Recalled`] and the bypass's
    ///   [`tallied::Absent::Unchecked`], since neither ran a check.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a recalled or bypassed declaration whose census read
    ///   as the empty tally of a check that charged nothing.
    /// - witness: `gandr-kernel-core::environment::tests::a_repeated_declaration_is_answered_by_the_kept_outcomes_of_the_first`
    #[inline]
    #[spec(ensures: |ret| matches!(
        (self.admission, ret),
        (Admission::Checked, Maybe::Present(_))
            | (Admission::Recalled, Maybe::Absent(tallied::Absent::Recalled))
            | (Admission::Unchecked, Maybe::Absent(tallied::Absent::Unchecked))
    ))]
    pub const fn census(&self) -> Maybe<ExpansionCensus, tallied::Absent>
    {
        match self.admission {
            Admission::Checked => Maybe::Present(self.census),
            Admission::Recalled => Maybe::Absent(tallied::Absent::Recalled),
            Admission::Unchecked => Maybe::Absent(tallied::Absent::Unchecked),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an admitted declaration carries no census of its check.
    pub mod tallied {
        /// The reason no check of it was tallied here.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A recorded verdict admitted it, so this kernel ran no check.
            Recalled,
            /// The bypass admitted it, which runs no check.
            Unchecked,
        }
    }
}

/// An environment's admitted declarations, in admission order, indexed by
/// admission position, and the tables a check reads beside them.
///
/// Those `Environment::freeze` froze are shared with every clone of the
/// environment made after. A clone shares the entries and takes no support. A
/// check reads an entry only through [`Self::get`], which answers through the
/// check's support ([`crate::weakening`]); [`Self::iter`] is for a reader
/// outside a check.
///
/// # Specification
/// - executable: none — a data declaration; [`Self::get`] states what a read
///   during a check sees.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration whose check reads an entry its content does
///   not name is refused at that position, and a check after many unrelated
///   entries reads as many entries as after few.
/// - witness: `gandr-kernel-core::environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
/// - witness: `gandr-kernel-core::environment::tests::an_admission_reads_as_many_entries_after_many_unrelated_ones_2797`
#[derive(Debug, Default)]
pub struct Entries
{
    /// The entries and the tables kept beside them, shared with every clone
    /// and with every reading a check makes, until one of them admits more.
    log: Option<alloc::sync::Arc<EntryLog>>,
    /// The support of the check that runs over the entries: none until a
    /// check opens one, and never shared with a clone.
    support: Option<alloc::sync::Arc<crate::weakening::Support>>,
    /// The rank the check that runs reads below: none until a check opens
    /// one, and never shared with a clone.
    horizon: Option<Horizon>,
}

/// The rank a check reads below, the rank of the declaration it admits, and
/// the position of that declaration. The check reads only the entries its
/// source states before that declaration.
#[derive(Clone, Debug)]
pub struct Horizon
{
    /// The rank of the declaration the check admits.
    rank: SourceRank,
    /// The position of the declaration the check admits: the length the
    /// check reads, whatever the releases after it reserve.
    end: gandr_kernel_term::ArenaLength,
    /// The presentations, as a reading below the rank sees them.
    presentations: crate::presented::Presentations,
}

/// Whether each live entry's place in rank order is its position.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Order
{
    /// No entry is retired, and each entry is admitted at a rank above the
    /// rank of each earlier entry: each position is its own place.
    #[default]
    Positional,
    /// An entry is retired, or admitted below the rank of an earlier entry:
    /// a place can differ from its position.
    Ranked,
}

/// The admitted declarations and what a check reads beside them: the view's
/// part of the log, which every view shares under one `Arc`.
#[derive(Clone, Debug, Default)]
pub struct EntryLog
{
    /// The slot at each position, in admission order.
    pub family: Family<Slot>,
    /// The presented types, and the types of words over each sort.
    pub presentations: crate::presented::Presentations,
    /// The position of each ruled definition, by the fixpoint its body thunks.
    ruled: BTreeMap<ComputationId, ConstantIndex>,
    /// The positions of each built-in role's holders, ascending.
    roles: BTreeMap<gandr_kernel_term::Builtin, Vec<ConstantIndex>>,
    /// The positions of the plain definitions named by their content, by the
    /// digest of their declared type and body, by rank ascending.
    definitions: BTreeMap<ContentDigest, Vec<ConstantIndex>>,
    /// How many slots are vacancies.
    vacancies: usize,
    /// How many slots are reserved for a release whose commit has not come.
    reservations: usize,
}

/// The slot at one position of the entries: an admitted declaration, the
/// vacancy that a refused declaration leaves, or the reservation of a
/// released declaration whose commit has not come.
///
/// A refused declaration keeps its position, so no later position moves when
/// a refusal comes after it. Its content leaves the arena, or stays as an
/// orphan below later content, so its slot holds no declaration. No read sees
/// a vacancy, no rank table holds it, no reach holds it, and the chain passes
/// it. No read sees a reservation either, until its commit fills it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per position, read by every check; boxing the declaration would allocate per \
              admission and add an indirection to every read to shrink the rare vacant slot"
)]
pub enum Slot
{
    /// An admitted declaration, live or retired.
    Admitted(AdmittedDeclaration),
    /// The position of a refused declaration.
    Vacant,
    /// The position of a released declaration whose commit has not come.
    Reserved,
}

impl Slot
{
    /// The admitted declaration in this slot: none for a vacancy or a
    /// reservation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn admitted(&self) -> Option<&AdmittedDeclaration>
    {
        match *self {
            Self::Admitted(ref entry) => Some(entry),
            Self::Vacant | Self::Reserved => None,
        }
    }

    /// The admitted declaration in this slot, to change in place: none for a
    /// vacancy or a reservation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn admitted_mut(&mut self) -> Option<&mut AdmittedDeclaration>
    {
        match *self {
            Self::Admitted(ref mut entry) => Some(entry),
            Self::Vacant | Self::Reserved => None,
        }
    }
}

/// No slot.
static NO_FAMILY: Family<Slot> = Family::new();

/// No admitted declaration: what a judgement over an empty environment reads.
pub static NO_ENTRIES: Entries = Entries::new();

impl Clone for Entries
{
    /// The same entries, with no support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        Self {
            log: self.log.clone(),
            support: None,
            horizon: None,
        }
    }
}

impl PartialEq for Entries
{
    /// Two readings of one log: the same entries, shared, at the same length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        match (self.log.as_ref(), other.log.as_ref()) {
            (Some(mine), Some(theirs)) => alloc::sync::Arc::ptr_eq(mine, theirs),
            (None, None) => true,
            (Some(_), None) | (None, Some(_)) => false,
        }
    }
}

impl Eq for Entries
{
}

impl Entries
{
    /// No entry, for a constant or a static.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            log: None,
            support: None,
            horizon: None,
        }
    }

    /// The slots, read outside any support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn family(&self) -> &Family<Slot>
    {
        self.log.as_deref().map_or(&NO_FAMILY, |log| &log.family)
    }

    /// The admitted declaration at `offset`, live or retired, read outside
    /// any support: none for a vacancy, and none past the entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn at<Offset>(
        &self,
        offset: Offset,
    ) -> Option<&AdmittedDeclaration>
    where
        Offset: Into<gandr_kernel_term::ArenaLength>,
    {
        self.family().get(offset).and_then(Slot::admitted)
    }

    /// How many slots there are, each vacancy and each reservation included:
    /// the position that the next admission takes. A running check reads the
    /// position of the declaration that it admits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> gandr_kernel_term::ArenaLength
    {
        self.horizon
            .as_ref()
            .map_or_else(|| self.family().len(), |horizon| horizon.end)
    }

    /// How many admitted entries there are, live or retired: the slots less
    /// each vacancy and each reservation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count of [`Self::iter`], read in constant time.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the count of [`Self::iter`] walks every slot, and a
    ///   clause may not walk the entries.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a count that misses a vacancy or an entry that a
    ///   refused block drops differs from the count of [`Self::iter`].
    /// - witness: `gandr-kernel-core::tests::recursive_data::a_mutual_block_is_refused_whole`
    #[inline]
    #[must_use]
    pub fn admitted(&self) -> gandr_kernel_term::ArenaLength
    {
        gandr_kernel_term::ArenaLength::from(
            usize::from(self.len()).saturating_sub(
                self.log
                    .as_deref()
                    .map_or(0, |log| log.vacancies.saturating_add(log.reservations)),
            ),
        )
    }

    /// The entry at `offset`, read through the support of the check that
    /// runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry at `offset` while no check runs, or when it is in
    ///   the running check's support; then, at the check's first read of it,
    ///   its direct references join the support, with each type of words over
    ///   each of them. `None` past the entries, for an entry the check's
    ///   horizon does not hold, as for an entry not admitted, and for an entry
    ///   outside the support, whose position the support keeps.
    /// - provides: the one read of an entry a check makes, so the kernel checks
    ///   the weakening rather than assumes it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the support before and after the
    ///   read, which a predicate may not capture.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a check reading an entry its content does not name is
    ///   refused at that position, and a case over a sort keeps the loop arm of
    ///   a type of words the case does not name. A reference to an entry ranked
    ///   above the declaration is unbound.
    /// - witness: `gandr-kernel-core::environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
    /// - witness: `gandr-kernel-core::tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
    /// - witness: `gandr-kernel-core::environment::tests::a_reference_to_an_entry_ranked_above_the_declaration_is_unbound_6621`
    #[inline]
    #[must_use]
    pub fn get<Offset>(
        &self,
        offset: Offset,
    ) -> Option<&AdmittedDeclaration>
    where
        Offset: Into<gandr_kernel_term::ArenaLength>,
    {
        let position = usize::from(offset.into());
        let log = self.log.as_deref()?;
        let entry = log.family.get(position)?.admitted()?;
        if entry.kind == EntryKind::Retired || entry.rank >= self.horizon() {
            return None;
        }
        let Some(support) = self.support.as_deref()
        else {
            return Some(entry);
        };
        match support.read(ConstantIndex::from(position)) {
            crate::weakening::Read::Open | crate::weakening::Read::Again => Some(entry),
            crate::weakening::Read::First => {
                for &reference in &entry.references {
                    log.join(support, reference);
                }
                Some(entry)
            },
            crate::weakening::Read::Outside => None,
        }
    }

    /// The entry at `offset`, read through the support of the check that runs
    /// without moving it: for a specification clause, which may not change
    /// what the check reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn peek<Offset>(
        &self,
        offset: Offset,
    ) -> Option<&AdmittedDeclaration>
    where
        Offset: Into<gandr_kernel_term::ArenaLength>,
    {
        let position = usize::from(offset.into());
        let entry = self.at(position)?;
        if entry.kind == EntryKind::Retired || entry.rank >= self.horizon() {
            return None;
        }
        let read = self
            .support
            .as_deref()
            .map_or(crate::weakening::Read::Open, |support| {
                support.peek(ConstantIndex::from(position))
            });
        match read {
            crate::weakening::Read::Outside => None,
            crate::weakening::Read::Open
            | crate::weakening::Read::First
            | crate::weakening::Read::Again => Some(entry),
        }
    }

    /// The entry admitted last, read outside any support: a vacancy after it
    /// is passed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn last(&self) -> Option<&AdmittedDeclaration>
    {
        self.family().iter().rev().find_map(Slot::admitted)
    }

    /// Every admitted entry, live or retired, in admission order, read outside
    /// any support: for a reader outside a check. A vacancy gives nothing, so
    /// a reader that needs each position counts it from [`Self::len`], and a
    /// reader that needs the count of entries reads [`Self::admitted`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &AdmittedDeclaration>
    {
        self.family().iter().filter_map(Slot::admitted)
    }

    /// How a memo key names a reference to each position, in admission
    /// order: as the admission of its entry named it, and a vacancy by its
    /// position, which no read reaches.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn key_names(&self) -> impl Iterator<Item = ConstantName> + '_
    {
        self.family().iter().map(|slot| {
            slot.admitted()
                .map_or(ConstantName::Position, |entry| entry.key_name)
        })
    }

    /// The presented types among the entries, and the types of words over
    /// each sort, as the running check reads them: below its horizon.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn presentations(&self) -> &crate::presented::Presentations
    {
        self.horizon.as_ref().map_or_else(
            || {
                self.log
                    .as_deref()
                    .map_or(&crate::presented::FREE, |log| &log.presentations)
            },
            |horizon| &horizon.presentations,
        )
    }

    /// The rank the running check reads below: the rank of the declaration
    /// it admits, and above every rank while no check runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn horizon(&self) -> SourceRank
    {
        self.horizon
            .as_ref()
            .map_or(SourceRank::ABOVE, |horizon| horizon.rank)
    }

    /// The entries and the tables kept beside them, shared with every clone
    /// and with every reading a check makes, until one of them admits more.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn log(&self) -> Option<&EntryLog>
    {
        self.log.as_deref()
    }

    /// The rank the check that runs reads below, with its presentations:
    /// none until a check opens one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn check_horizon(&self) -> Option<&Horizon>
    {
        self.horizon.as_ref()
    }

    /// The live entry at `position`, read outside any support: none for a
    /// retired entry, and none past the entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn live(
        &self,
        position: ConstantIndex,
    ) -> Option<&AdmittedDeclaration>
    {
        self.at(usize::from(position))
            .filter(|entry| entry.kind == EntryKind::Live)
    }

    /// The rank of the live entry at `position`, read outside any support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn rank_of(
        &self,
        position: ConstantIndex,
    ) -> Option<SourceRank>
    {
        self.live(position).map(AdmittedDeclaration::rank)
    }

    /// The entries that the check of the live entry at `position` reads
    /// first, as its support joins them: each position that its content
    /// names, each followed by the types of words over it that rank below the
    /// entry. Nothing for a retired entry, and nothing past the entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn waits_on(
        &self,
        position: ConstantIndex,
    ) -> impl Iterator<Item = ConstantIndex> + '_
    {
        let presentations = self
            .log
            .as_deref()
            .map_or(&crate::presented::FREE, |log| &log.presentations);
        self.live(position).into_iter().flat_map(move |entry| {
            entry.references.iter().flat_map(move |&root| {
                core::iter::once(root).chain(presentations.over(root).filter(move |&words| {
                    self.rank_of(words).is_some_and(|rank| rank < entry.rank)
                }))
            })
        })
    }

    /// The entry key of the live declaration at `position`, read outside any
    /// support; absent as unkeyed for a retired entry and past the last
    /// entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn key(
        &self,
        position: ConstantIndex,
    ) -> Maybe<crate::verdict::VerdictKey, crate::verdict::keyed::Absent>
    {
        self.live(position).map_or(
            Maybe::Absent(crate::verdict::keyed::Absent::Unkeyed),
            AdmittedDeclaration::key,
        )
    }

    /// The position of the ruled definition whose body thunks the fixpoint
    /// `root`, read through the support of the check that runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ruled(
        &self,
        root: ComputationId,
    ) -> Option<ConstantIndex>
    {
        let position = *self.log.as_deref()?.ruled.get(&root)?;
        self.get(usize::from(position)).map(|_| position)
    }

    /// The position of the entry that holds `role` and that the running
    /// check reads, if one holds it: the holder ranked first below the
    /// check's horizon.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holder(
        &self,
        role: gandr_kernel_term::Builtin,
    ) -> Option<ConstantIndex>
    {
        self.holder_below(role, self.horizon())
    }

    /// The position of the holder of `role` ranked first below `below`, if
    /// one holds it there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holder_below(
        &self,
        role: gandr_kernel_term::Builtin,
        below: SourceRank,
    ) -> Option<ConstantIndex>
    {
        self.log
            .as_deref()?
            .roles
            .get(&role)?
            .iter()
            .filter_map(|&position| Some((self.rank_of(position)?, position)))
            .filter(|&(rank, _)| rank < below)
            .min()
            .map(|(_, position)| position)
    }

    /// The positions of the plain definitions ranked below `below` whose
    /// declared type and body digest to `digest`, by rank ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn digested(
        &self,
        digest: ContentDigest,
        below: SourceRank,
    ) -> &[ConstantIndex]
    {
        let positions = self
            .log
            .as_deref()
            .and_then(|log| log.definitions.get(&digest))
            .map_or(&[][..], Vec::as_slice);
        let held = positions
            .partition_point(|&position| self.rank_of(position).is_some_and(|rank| rank < below));
        positions.get(.. held).unwrap_or_default()
    }

    /// These entries and the support of the check that runs, for a reading
    /// the check makes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn reading(&self) -> Self
    {
        Self {
            log: self.log.clone(),
            support: self.support.clone(),
            horizon: self.horizon.clone(),
        }
    }

    /// These entries for one check: the log shared, and the buffer of the
    /// support taken from the entries, so the check opens a horizon and a
    /// support of its own while the entries keep none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&mut self) -> Self
    {
        Self {
            log: self.log.clone(),
            support: self.support.take(),
            horizon: None,
        }
    }

    /// Take back the buffer of the support that `view` held, once its check
    /// closed it. The view's share of the log ends here, so the next
    /// admission changes the log in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn restore(
        &mut self,
        view: Self,
    )
    {
        self.support = view.support;
    }

    /// The log, to change: shared with no clone or reading after.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn log_mut(&mut self) -> &mut EntryLog
    {
        alloc::sync::Arc::make_mut(self.log.get_or_insert_with(alloc::sync::Arc::default))
    }

    /// Admit `entry` after every entry, its content in `arena`.
    ///
    /// # Specification
    /// - requires: `entry` is the declaration admitted at the next position,
    ///   its content in `arena`, at a rank no entry holds.
    /// - ensures: one more entry; the presentations hold its presented type and
    ///   the type of words it is over its sort, the ruled index its fixpoint,
    ///   the role index its role, and the digest index its content name.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::get`].
    /// - witness: `gandr-kernel-core::tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
    #[spec(captures: entry_len = self.len(), ensures: usize::from(self.len()) == usize::from(entry_len).saturating_add(1))]
    #[inline]
    pub fn push(
        &mut self,
        arena: &TermArena,
        entry: AdmittedDeclaration,
    )
    {
        let log = self.log_mut();
        let position = ConstantIndex::from(usize::from(log.family.len()));
        log.index(arena, position, &entry);
        log.family.push(Slot::Admitted(entry));
    }

    /// Reserve the next position for a released declaration: a slot that no
    /// read sees until its commit fills it.
    ///
    /// # Specification
    /// trivial.
    #[spec(captures: [entry_len = self.len(), admitted = self.admitted()], ensures: usize::from(self.len()) == usize::from(entry_len).saturating_add(1) && self.admitted() == admitted)]
    #[inline]
    pub fn reserve(&mut self)
    {
        let log = self.log_mut();
        log.reservations = log.reservations.saturating_add(1);
        log.family.push(Slot::Reserved);
    }

    /// Admit `entry` at its reserved `position`, its content in `arena`.
    ///
    /// # Specification
    /// - requires: the slot at `position` is reserved, and `entry` is the
    ///   declaration released there, its content in `arena`, at a rank no entry
    ///   holds.
    /// - ensures: the slot holds `entry`, and the indexes hold its rows as
    ///   [`Self::push`] states. The length is unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a commit in another order than the positions fills
    ///   each slot as the serial run admits it.
    /// - witness: `gandr-kernel-core::environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(captures: [entry_len = self.len(), admitted = self.admitted()], ensures: self.len() == entry_len && usize::from(self.admitted()) == usize::from(admitted).saturating_add(1))]
    #[inline]
    pub fn fill(
        &mut self,
        arena: &TermArena,
        position: ConstantIndex,
        entry: AdmittedDeclaration,
    )
    {
        let log = self.log_mut();
        log.index(arena, position, &entry);
        if let Some(slot) = log.family.get_mut(usize::from(position)) {
            *slot = Slot::Admitted(entry);
            log.reservations = log.reservations.saturating_sub(1);
        }
    }

    /// Leave a vacancy at the next position: the slot of a refused
    /// declaration, which holds no declaration and no content.
    ///
    /// # Specification
    /// - requires: the declaration staged at the next position is refused, and
    ///   the arena holds none of its content.
    /// - ensures: one more slot, which no read sees and no table holds.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as `Environment::add_decl`.
    /// - witness: `gandr-kernel-core::environment::tests::a_rejected_declaration_leaves_a_vacancy_at_its_position`
    #[spec(captures: [entry_len = self.len(), admitted = self.admitted()], ensures: usize::from(self.len()) == usize::from(entry_len).saturating_add(1) && self.admitted() == admitted)]
    #[inline]
    pub fn vacate(&mut self)
    {
        let log = self.log_mut();
        log.vacancies = log.vacancies.saturating_add(1);
        log.family.push(Slot::Vacant);
    }

    /// Leave a vacancy at the reserved `position`: the slot of a released
    /// declaration that its check refused.
    ///
    /// # Specification
    /// trivial.
    #[spec(captures: [entry_len = self.len(), admitted = self.admitted()], ensures: self.len() == entry_len && self.admitted() == admitted)]
    #[inline]
    pub fn vacate_at(
        &mut self,
        position: ConstantIndex,
    )
    {
        let log = self.log_mut();
        if let Some(slot) = log.family.get_mut(usize::from(position)) {
            *slot = Slot::Vacant;
            log.reservations = log.reservations.saturating_sub(1);
            log.vacancies = log.vacancies.saturating_add(1);
        }
    }

    /// Retire the live entry at `position`: no read sees it after, and its
    /// rank is free.
    ///
    /// The entry keeps its position, its content and its row in the role
    /// index. A reader of that index reads the live entries alone, through
    /// their ranks.
    ///
    /// # Specification
    /// - requires: the entry at `position` stands live.
    /// - ensures: the entry is retired; the digest index and the presentations
    ///   hold no row of it; every other entry and row is unchanged.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   change, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as `Environment::retire`.
    /// - witness: `gandr-kernel-core::environment::tests::a_kept_environment_reads_as_a_fresh_admission_6621`
    #[inline]
    pub fn retire(
        &mut self,
        position: ConstantIndex,
    )
    {
        let log = self.log_mut();
        let Some(entry) = log
            .family
            .get_mut(usize::from(position))
            .and_then(Slot::admitted_mut)
        else {
            return;
        };
        entry.kind = EntryKind::Retired;
        let key_name = entry.key_name;
        if let ConstantName::Definition { digest, .. } = key_name
            && let Some(positions) = log.definitions.get_mut(&digest)
        {
            positions.retain(|&held| held != position);
        }
        log.presentations.retire(position);
    }

    /// Stand the retired entry at `position` live again at the rank `rank`,
    /// named `key_name`, its content in `arena`.
    ///
    /// # Specification
    /// - requires: the entry at `position` is retired, and no live entry holds
    ///   `rank`.
    /// - ensures: the entry stands live at `rank` under `key_name`; the digest
    ///   index, the ruled index and the presentations hold its rows at `rank`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state the tables before and after the
    ///   change, which a predicate may not capture whole.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as `Environment::keep`.
    /// - witness: `gandr-kernel-core::environment::tests::a_kept_environment_reads_as_a_fresh_admission_6621`
    #[inline]
    pub fn reinstate(
        &mut self,
        arena: &TermArena,
        (position, rank): (ConstantIndex, SourceRank),
        key_name: ConstantName,
    )
    {
        let log = self.log_mut();
        let Some(entry) = log
            .family
            .get_mut(usize::from(position))
            .and_then(Slot::admitted_mut)
        else {
            return;
        };
        entry.kind = EntryKind::Live;
        entry.rank = rank;
        entry.key_name = key_name;
        let EntryLog {
            ref family,
            ref mut presentations,
            ref mut ruled,
            ref mut definitions,
            ..
        } = *log;
        let Some(entry) = family.get(usize::from(position)).and_then(Slot::admitted)
        else {
            return;
        };
        let declaration = &entry.declaration;
        presentations.admit(
            (position, rank),
            declaration,
            sort_constructors(family, declaration),
        );
        if let DeclarationContent::Def { body, .. } = *declaration.content()
            && !declaration.operation_rules().rules().is_empty()
            && let Some(&Value::Thunk(root)) = arena.value(body)
        {
            let _previous = ruled.insert(root, position);
        }
        if let ConstantName::Definition { digest, .. } = key_name {
            place_definition(family, definitions, digest, (position, rank));
        }
    }

    /// Keep the first `length` entries, dropping later ones and their rows in
    /// the tables kept beside them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entries and tables as they were when the first `length`
    ///   entries were all.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a block refused after one member is admitted leaves
    ///   the entries it found.
    /// - witness: `gandr-kernel-core::tests::recursive_data::a_mutual_block_is_refused_whole`
    #[spec(captures: entry_len = self.len(), ensures: self.len() == length.min(entry_len))]
    #[inline]
    pub fn truncate(
        &mut self,
        length: gandr_kernel_term::ArenaLength,
    )
    {
        if self.len() <= length {
            return;
        }
        let first = ConstantIndex::from(length);
        let log = self.log_mut();
        let dropped = usize::from(log.family.len()).saturating_sub(usize::from(length));
        let (vacant, reserved) = log.family.iter().rev().take(dropped).fold(
            (0_usize, 0_usize),
            |(vacant, reserved), slot| match *slot {
                Slot::Admitted(_) => (vacant, reserved),
                Slot::Vacant => (vacant.saturating_add(1), reserved),
                Slot::Reserved => (vacant, reserved.saturating_add(1)),
            },
        );
        log.vacancies = log.vacancies.saturating_sub(vacant);
        log.reservations = log.reservations.saturating_sub(reserved);
        log.family.truncate(length);
        log.presentations.forget_from(first);
        log.ruled.retain(|_, &mut position| position < first);
        log.roles.retain(|_, positions| {
            positions.retain(|&position| position < first);
            !positions.is_empty()
        });
        log.definitions.retain(|_, positions| {
            positions.retain(|&position| position < first);
            !positions.is_empty()
        });
    }

    /// Share every entry with every clone made after.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn freeze(&mut self)
    {
        if self.log.is_some() {
            self.log_mut().family.freeze();
        }
    }

    /// The entry at `offset`, to change in place, outside any support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn get_mut<Offset>(
        &mut self,
        offset: Offset,
    ) -> Option<&mut AdmittedDeclaration>
    where
        Offset: Into<gandr_kernel_term::ArenaLength>,
    {
        self.log.as_ref()?;
        self.log_mut()
            .family
            .get_mut(offset)
            .and_then(Slot::admitted_mut)
    }

    /// Open a check of the declaration ranked at `rank` and placed at `end`,
    /// whose support starts at `roots`: each joins, with each type of words
    /// over it.
    ///
    /// # Specification
    /// - requires: no check runs over these entries, and `end` is at most their
    ///   length.
    /// - ensures: until [`Self::close`], [`Self::get`] answers only the entries
    ///   in the support, which grows as the check reads, and only those ranked
    ///   below `rank`; [`Self::presentations`] and [`Self::holder`] answer only
    ///   the rows ranked below it; [`Self::len`] answers `end`.
    /// - provides: the start of a support by weakening, and the horizon that
    ///   makes a check read only what its source states before it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state what later reads answer, which
    ///   opening does not run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::get`].
    /// - witness: `gandr-kernel-core::environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
    /// - witness: `gandr-kernel-core::environment::tests::a_reference_to_an_entry_ranked_above_the_declaration_is_unbound_6621`
    #[inline]
    pub fn open<Roots>(
        &mut self,
        roots: Roots,
        (rank, end): (SourceRank, gandr_kernel_term::ArenaLength),
    ) where
        Roots: IntoIterator<Item = ConstantIndex>,
    {
        self.horizon = Some(Horizon {
            rank,
            end,
            presentations: self
                .log
                .as_deref()
                .map_or(&crate::presented::FREE, |log| &log.presentations)
                .below(rank),
        });
        let length = self.len();
        let fresh = alloc::sync::Arc::default;
        let support = self.support.get_or_insert_with(fresh);
        if alloc::sync::Arc::get_mut(support).is_none() {
            *support = fresh();
        }
        let Some(support) = alloc::sync::Arc::get_mut(support)
        else {
            return;
        };
        support.open(length);
        if let Some(log) = self.log.as_deref() {
            for root in roots {
                log.join(support, root);
            }
        }
    }

    /// Close the running check: the first position it read outside its
    /// support, if it read one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn close(&mut self) -> Option<ConstantIndex>
    {
        self.horizon = None;
        alloc::sync::Arc::get_mut(self.support.as_mut()?)?.close()
    }

    /// How many entries the last check read.
    ///
    /// # Specification
    /// trivial.
    #[cfg(any(test, feature = "fixture"))]
    pub(crate) fn reads(&self) -> gandr_kernel_term::ArenaLength
    {
        self.support.as_deref().map_or_else(
            || gandr_kernel_term::ArenaLength::from(0_usize),
            crate::weakening::Support::reads,
        )
    }
}

/// The constructor table of the sort that the cells of `declaration` loop
/// in, read from `family`, for a type of words.
///
/// # Specification
/// trivial.
fn sort_constructors<'family>(
    family: &'family Family<Slot>,
    declaration: &Declaration,
) -> Option<&'family [Vec<ValueTypeId>]>
{
    let cells = declaration.presentation().cells()?;
    match *family.get(usize::from(cells.sort()))?.admitted()?.content() {
        DeclarationContent::Data {
            ref constructors, ..
        } => Some(constructors.as_slice()),
        DeclarationContent::Codata { .. }
        | DeclarationContent::Def { .. }
        | DeclarationContent::Axiom { .. }
        | DeclarationContent::LiteralIdentity { .. }
        | DeclarationContent::AbstractType { .. } => None,
    }
}

/// Place `position`, ranked at `rank`, among the plain definitions that
/// `definitions` holds under `digest`, by rank ascending; `family` ranks the
/// definitions it holds already.
///
/// # Specification
/// trivial.
fn place_definition(
    family: &Family<Slot>,
    definitions: &mut BTreeMap<ContentDigest, Vec<ConstantIndex>>,
    digest: ContentDigest,
    (position, rank): (ConstantIndex, SourceRank),
)
{
    let positions = definitions.entry(digest).or_default();
    let at = positions.partition_point(|&held| {
        family
            .get(usize::from(held))
            .and_then(Slot::admitted)
            .is_some_and(|earlier| earlier.rank < rank)
    });
    positions.insert(at, position);
}

impl EntryLog
{
    /// Take the rows of `entry`, admitted at `position` with its content in
    /// `arena`: its presented type and the type of words it is over its
    /// sort, its fixpoint, its role and its content name.
    ///
    /// # Specification
    /// trivial.
    fn index(
        &mut self,
        arena: &TermArena,
        position: ConstantIndex,
        entry: &AdmittedDeclaration,
    )
    {
        let declaration = &entry.declaration;
        let rank = entry.rank;
        self.presentations.admit(
            (position, rank),
            declaration,
            sort_constructors(&self.family, declaration),
        );
        if let DeclarationContent::Def { body, .. } = *declaration.content()
            && !declaration.operation_rules().rules().is_empty()
            && let Some(&Value::Thunk(root)) = arena.value(body)
        {
            let _previous = self.ruled.insert(root, position);
        }
        // Each holder is kept: a reader takes the one ranked first below
        // it. Admission refuses a second holder, and only the bypass admits
        // one.
        if let Maybe::Present(role) = declaration.role() {
            self.roles.entry(role).or_default().push(position);
        }
        if let ConstantName::Definition { digest, .. } = entry.key_name {
            place_definition(
                &self.family,
                &mut self.definitions,
                digest,
                (position, rank),
            );
        }
    }

    /// Join `position` to `support`, with each type of words over it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn join(
        &self,
        support: &crate::weakening::Support,
        position: ConstantIndex,
    )
    {
        support.join(position);
        for words in self.presentations.over(position) {
            support.join(words);
        }
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
pub enum CodeEdges
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
/// - witness: `gandr-kernel-core::environment::tests::audit_reaches_an_axiom_named_only_inside_a_code`
///
/// - witness: `gandr-kernel-core::environment::tests::sealing_provenance_does_not_follow_codes`
/// - witness: `gandr-kernel-core::environment::tests::a_type_level_atom_reference_reaches_the_audit`
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
#[inline]
#[must_use]
pub fn collect_reachable(
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

/// The positions `declaration`'s content names, ascending, each once.
///
/// These are the positions its roots reach through codes — its types, its
/// body, its constructors and their results, an abstract type's
/// representation and interface, and its related endpoints — with its laws,
/// its sealing provenance, the positions its operation rules name and the
/// sort of its presentation's cells.
///
/// # Specification
/// - requires: nothing — an unreadable id names nothing, so a missing edge
///   refuses the check that reads past it.
/// - ensures: exactly the positions [`collect_reachable`] gathers from each
///   root under [`CodeEdges::Follow`], with each law, each provenance atom,
///   each operation and family an operation rule names and the cells' sort,
///   ascending and each once.
/// - provides: where a check's support starts, and what joins the support of a
///   later check when it reads the entry.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a check that reads only what its content names admits,
///   and one that reads past it is refused.
/// - witness: `gandr-kernel-core::environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(*pair, [earlier, later] if earlier < later)))]
#[inline]
#[must_use]
pub fn references(
    arena: &TermArena,
    declaration: &Declaration,
) -> Box<[ConstantIndex]>
{
    let mut found = BTreeSet::new();
    {
        let mut walk = Walk::default();
        let mut sink = Sink::Gather(&mut found);
        let mut from = |root: AnyNode| {
            let _gathered = reach(arena, root, CodeEdges::Follow, &mut walk, &mut sink);
        };
        match *declaration.content() {
            DeclarationContent::Data {
                ref parameters,
                ref indices,
                ref constructors,
                ref results,
                kind,
            } => {
                for &root in parameters
                    .iter()
                    .chain(indices)
                    .chain(constructors.iter().flatten())
                    .chain(core::iter::once(&kind))
                {
                    from(AnyNode::ValueType(root));
                }
                for &result in results.iter().flatten() {
                    from(AnyNode::Value(result));
                }
            },
            DeclarationContent::Def { declared, body } => {
                from(AnyNode::ValueType(declared));
                from(AnyNode::Value(body));
            },
            DeclarationContent::Axiom { declared }
            | DeclarationContent::LiteralIdentity { declared, .. } => {
                from(AnyNode::ValueType(declared));
            },
            DeclarationContent::AbstractType {
                kind,
                representation,
                interface,
                ..
            } => {
                from(AnyNode::ValueType(kind));
                from(AnyNode::ValueType(representation));
                if let Maybe::Present(interface) = interface {
                    from(AnyNode::Value(interface.relation()));
                    from(AnyNode::Value(interface.reflexivity()));
                    if let Maybe::Present(law) = interface.law() {
                        from(AnyNode::Value(law));
                    }
                }
            },
            DeclarationContent::Codata {
                ref parameters,
                ref observations,
                kind,
            } => {
                for &root in parameters.iter().chain(core::iter::once(&kind)) {
                    from(AnyNode::ValueType(root));
                }
                for &observation in observations {
                    from(AnyNode::CompType(observation));
                }
            },
        }
        for related in declaration.related() {
            from(AnyNode::Value(related.left));
            from(AnyNode::Value(related.right));
        }
    }
    found.extend(declaration.laws().iter().copied());
    found.extend(declaration.provenance().iter().copied());
    for rule in declaration.operation_rules().rules() {
        found.extend(
            rule.left()
                .iter()
                .chain(rule.right())
                .filter_map(|node| match *node {
                    gandr_kernel_term::OperationNode::Operation { constant, .. } => Some(constant),
                    gandr_kernel_term::OperationNode::Constructor { family, .. } => Some(family),
                    gandr_kernel_term::OperationNode::Results(_)
                    | gandr_kernel_term::OperationNode::Variable(_) => None,
                }),
        );
    }
    if let Some(cells) = declaration.presentation().cells() {
        let _fresh = found.insert(cells.sort());
    }
    found.into_iter().collect()
}

/// Whether a walk met the constant it sought.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mention
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
                Some(&Value::Restrict { value, ref fixed }) => pending.extend(
                    core::iter::once(AnyNode::Value(value))
                        .chain(fixed.values().copied().map(AnyNode::Value)),
                ),
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
                    ..
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
                Some(
                    &(Computation::Bind(bound, body) | Computation::BindAll { bound, body, .. }),
                ) => {
                    pending.push(AnyNode::Computation(bound));
                    pending.push(AnyNode::Computation(body));
                },
                Some(&Computation::ReturnAll(ref values)) => {
                    pending.extend(values.iter().copied().map(AnyNode::Value));
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
                Some(&CompType::Returns(ref results)) => {
                    pending.extend(results.iter().copied().map(AnyNode::ValueType));
                },
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

/// A search for one constant through codes and sealed atoms alike, over as
/// many roots as it is asked about.
///
/// The search keeps the nodes it expanded for every root it answered
/// `Unnamed` for, so asking about the parts of one type walks the nodes they
/// share once, and it stops at the first node naming the constant.
#[derive(Debug)]
pub struct ConstantSearch
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
    #[must_use]
    pub fn new(sought: ConstantIndex) -> Self
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
    #[inline]
    pub fn names(
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
/// - witness: `gandr-kernel-core::environment::tests::sealing_provenance_does_not_follow_codes`
#[spec(ensures: |ret| match arena.value_type(root) {
    Some(&ValueType::Abstract(index)) => ret.len() == 1_usize && ret.contains(&index),
    Some(&ValueType::Data { .. } | &ValueType::Base(_) | &ValueType::Universe { .. } | &ValueType::Element { .. }) | None => ret.is_empty(),
    Some(held) if held.product_parts() == Some(&[]) => ret.is_empty(),
    _ => true,
})]
#[inline]
#[must_use]
pub fn projected_atoms(
    arena: &TermArena,
    root: ValueTypeId,
) -> BTreeSet<ConstantIndex>
{
    collect_reachable(arena, AnyNode::ValueType(root), CodeEdges::Stop)
}

#[cfg(test)]
mod tests
{

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::Seam;
    use gandr_kernel_term::TermArena;

    use super::OutstandingCount;
    use super::StagedMarks;

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
}
