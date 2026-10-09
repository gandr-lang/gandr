//! The multi-sum overlap enumerator and the overlap support relation, generic
//! over the [`CellAlphabet`].
//!
//! For each ordered pair of cells the enumerator returns every unification at
//! a seam, never one chosen among them: the family is a multi-sum, one entry
//! per unifier. Two kinds of entry, both rooted at the seam:
//!
//! - [`OverlapKind::Confluence`], the Knuth–Bendix critical pair: the two
//!   left-hand sides unify at the root, so the peak reduces two ways.
//!   Completion normalizes both reducts and either joins them under a
//!   certificate or orients them into a new cell.
//! - [`OverlapKind::Composition`], the sequential composition of the two cells:
//!   the left cell's right-hand side unifies, at one of its command positions,
//!   with the right cell's left-hand side, so firing the left cell and then the
//!   right one is a two-step derivation whose composite is a fused cell.
//!
//! An entry carries its seam data — the unifier, the seam position, the peak
//! and the right cell renamed apart from the left — rather than a verdict, so
//! a consumer reads the span the overlap is, not only that one exists.
//!
//! [`OverlapSupport`] memoizes which cells and which certificates overlap, so
//! scheduling asks constant-time independence questions and batches a family
//! into groups no two members of which interact.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CommandSpliceRefusal;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::CertificateIndex;
use crate::boundary::StepIndependence;
use crate::tracelet::Tracelet;

/// The unordered identity of two cells.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct CellPair(CellId, CellId);

impl CellPair
{
    /// The unordered identity of two cells, ascending, so both argument orders
    /// build one key.
    ///
    /// # Specification
    /// - ensures: the smaller identifier first and larger second; exchanging
    ///   arguments preserves the key.
    /// - panics: none.    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, unequal, equal and maximum identifiers give
    ///   exact canonical pairs. Reversed sorting or losing an endpoint changes
    ///   identity.
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[spec(ensures: |output| output.0 == core::cmp::min(left, right) && output.1 == core::cmp::max(left, right))]
    fn new(
        left: CellId,
        right: CellId,
    ) -> Self
    {
        if left <= right {
            return Self(left, right);
        }
        Self(right, left)
    }
}

/// The unordered identity of two certificate keys, ascending.
///
/// # Specification
/// - ensures: the smaller certificate key first and larger second; exchanging
///   arguments preserves the pair.
/// - panics: none.///
/// # Adequacy
/// - hypothesis: L3 — zero, unequal, equal and maximum keys give exact
///   canonical pairs. Reversed sorting or losing an endpoint changes
///   memoization identity.
/// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
#[spec(ensures: |output| output.0 == core::cmp::min(left, right) && output.1 == core::cmp::max(left, right))]
fn certificate_pair(
    left: CertificateIndex,
    right: CertificateIndex,
) -> (CertificateIndex, CertificateIndex)
{
    if left <= right {
        return (left, right);
    }
    (right, left)
}

/// The memoized overlap relation on the cells of one store and on the
/// certificates added to it.
///
/// Every set is ordered, so iteration and equality are deterministic and
/// independent of insertion history.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OverlapSupport
{
    /// The unordered cell pairs the enumerator finds an overlap for.
    cell_overlaps: BTreeSet<CellPair>,
    /// The unordered certificate-key pairs whose supports meet, ascending.
    certificate_overlaps: BTreeSet<(CertificateIndex, CertificateIndex)>,
    /// The cells each added certificate's paths fire, by key.
    certificate_cells: Vec<BTreeSet<CellId>>,
}

impl OverlapSupport
{
    /// The support of every cell pair in `store`.
    ///
    /// # Specification
    /// - ensures: a cell pair is related exactly when [`overlaps_between`]
    ///   returns a nonempty family for it in either order.
    /// - provides: logarithmic independence queries afterwards.
    /// - panics: none.
    /// - intension: one pair query per ordered cell pair.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the frame-defining and successor cells, which
    ///   compose, are related in both argument orders. Empty stores and
    ///   unissued identifiers bound the empty relation; missing or spurious
    ///   edges change independence.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.certificate_cells.is_empty() && output.certificate_overlaps.is_empty()
        && store.iter().all(|left| store.iter().all(|right| output.cell_overlaps.contains(&CellPair::new(left.0, right.0))
            == (!overlaps_between(left, right).is_empty() || !overlaps_between(right, left).is_empty()))))]
    pub fn from_store<A>(store: &CellStore<A>) -> Self
    where
        A: CellAlphabet,
    {
        let mut support = Self::default();
        for (left_id, left) in store.iter() {
            for (right_id, right) in store.iter() {
                if !overlaps_between((left_id, left), (right_id, right)).is_empty() {
                    support
                        .cell_overlaps
                        .insert(CellPair::new(left_id, right_id));
                }
            }
        }
        support
    }

    /// Add `certificates` to the relation and return their keys.
    ///
    /// The keys are the half-open pair `(first, past_the_end)` rather than a
    /// [`core::ops::Range`], because a range over a wrapper does not iterate.
    ///
    /// # Specification
    /// - ensures: the certificates take the next keys in order, starting at the
    ///   number of certificates already added; each is related to itself, and
    ///   to every certificate added before or with it whose support meets its
    ///   own.
    /// - ensures: adding a sequence in one call or split across several leaves
    ///   the same support.
    /// - provides: logarithmic certificate-independence queries afterwards.
    /// - panics: none.
    /// - intension: each new certificate's support is compared once with every
    ///   support already held and every later one in the same call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two one-step certificates over related cells are
    ///   dependent, a certificate and its separately added copy share keys with
    ///   nothing and support with each other, and one call over two
    ///   certificates equals two calls over one each. Empty input preserves the
    ///   relation; empty certificates are self-dependent but mutually
    ///   independent. Wrong ranges or lost reflexivity change those
    ///   observations.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[inline]
    #[spec(captures: base = self.certificate_cells.len(), ensures: |output| usize::from(output.0) == base
        && usize::from(output.1) == base.saturating_add(certificates.len())
        && self.certificate_cells.len() == usize::from(output.1)
        && certificates.iter().zip(self.certificate_cells.iter().skip(base)).all(|(certificate, held)|
            certificate.path_a.iter().chain(&certificate.path_b).all(|step| held.contains(&step.cell))
            && held.iter().all(|id| certificate.path_a.iter().chain(&certificate.path_b).any(|step| step.cell == *id)))
        && (base..self.certificate_cells.len()).all(|index| self.certificate_overlaps.contains(&(CertificateIndex::from(index), CertificateIndex::from(index)))))]
    pub fn add_certificates<A>(
        &mut self,
        certificates: &[Tracelet<A>],
    ) -> (CertificateIndex, CertificateIndex)
    where
        A: CellAlphabet,
    {
        // Both lengths count values held in memory, so their sum is far below
        // the saturation bound and every key below is exact.
        let base = self.certificate_cells.len();
        let end = base.saturating_add(certificates.len());
        for certificate in certificates {
            let support: BTreeSet<CellId> = certificate
                .path_a
                .iter()
                .chain(&certificate.path_b)
                .map(|step| step.cell)
                .collect();
            let index = CertificateIndex::from(self.certificate_cells.len());
            self.certificate_overlaps.insert((index, index));
            let mut related = Vec::new();
            for (prior, prior_support) in self.certificate_cells.iter().enumerate() {
                if !bool::from(self.supports_independent(&support, prior_support)) {
                    related.push(certificate_pair(index, CertificateIndex::from(prior)));
                }
            }
            self.certificate_overlaps.extend(related);
            self.certificate_cells.push(support);
        }
        (CertificateIndex::from(base), CertificateIndex::from(end))
    }

    /// Whether two certificate supports are independent: no shared cell and
    /// no related pair of cells.
    ///
    /// # Specification
    /// - ensures: positive exactly for disjoint supports with no related cross
    ///   pair.
    /// - panics: none.    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, shared and disjoint supports separate aliasing
    ///   from the overlap relation. Missing the alias guard or reversing
    ///   dependence changes the answer.
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[spec(ensures: |output| bool::from(output) == (left.is_disjoint(right)
        && left.iter().all(|one| right.iter().all(|other| bool::from(self.independent(*one, *other))))))]
    fn supports_independent(
        &self,
        left: &BTreeSet<CellId>,
        right: &BTreeSet<CellId>,
    ) -> StepIndependence
    {
        StepIndependence::from(!left.iter().any(|&left_cell| {
            right.iter().any(|&right_cell| {
                left_cell == right_cell || !bool::from(self.independent(left_cell, right_cell))
            })
        }))
    }

    /// Whether two certificate keys are independent.
    ///
    /// # Specification
    /// - ensures: negative exactly when the two certificates' supports meet, a
    ///   certificate with itself included; symmetric in its arguments.
    /// - ensures: positive for a key no [`OverlapSupport::add_certificates`]
    ///   call handed out, which relates to nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a certificate is dependent on itself and on a
    ///   separately added copy, and two certificates over related cells are
    ///   dependent. Unissued keys, including the first unused key, are
    ///   independent even of themselves. A widened self-dependence guard
    ///   changes that boundary.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == match (self.certificate_cells.get(usize::from(left)), self.certificate_cells.get(usize::from(right))) {
        (Some(one), Some(other)) => left != right && bool::from(self.supports_independent(one, other)),
        _ => true,
    })]
    pub fn certificates_independent(
        &self,
        left: CertificateIndex,
        right: CertificateIndex,
    ) -> StepIndependence
    {
        StepIndependence::from(
            !self
                .certificate_overlaps
                .contains(&certificate_pair(left, right)),
        )
    }

    /// Whether two cells are independent under this support.
    ///
    /// The support answers in this one polarity; an overlap question is this
    /// answer negated where it is asked, so no second query can drift from it.
    ///
    /// # Specification
    /// - ensures: negative exactly when the enumerator found an overlap for the
    ///   pair in either order; symmetric in its arguments.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composing frame and successor cells are dependent
    ///   in both argument orders. Empty support leaves unissued cells
    ///   unrelated, including an equal identifier pair. Spurious or asymmetric
    ///   edges change the decision.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) != self.cell_overlaps.contains(&CellPair::new(left, right)))]
    pub fn independent(
        &self,
        left: CellId,
        right: CellId,
    ) -> StepIndependence
    {
        StepIndependence::from(!self.cell_overlaps.contains(&CellPair::new(left, right)))
    }

    /// Partition `overlaps` into batches whose members are pairwise
    /// independent.
    ///
    /// # Specification
    /// - ensures: flattening the batches returns `overlaps` with multiplicity;
    ///   each batch is a subsequence of `overlaps` in input order, each member
    ///   placed in the first batch it is independent of every member of, so
    ///   batch order follows first appearance.
    /// - ensures: every two members of one batch are independent under
    ///   [`OverlapSupport::overlaps_are_independent`].
    /// - panics: none.
    /// - intension: first-fit, quadratic in the family.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three independent two-rule clusters, enumerated so
    ///   the family alternates between them, batch into exactly two batches of
    ///   three at the exact input positions first-fit predicts. Empty and
    ///   repeated input preserve exact multiplicities. Deduplication, reordered
    ///   first-fit choices and an admitted dependent pair change the batches.
    /// - witness: `tests::overlap::overlap_support_batches_are_pairwise_independent`
    /// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output.iter().map(Vec::len).sum::<usize>() == overlaps.len()
        && overlaps.iter().all(|item| output.iter().flatten().filter(|held| *held == item).count() == overlaps.iter().filter(|held| *held == item).count())
        && output.iter().all(|batch| !batch.is_empty() && batch.iter().enumerate().all(|(index, left)| batch.iter().skip(index.saturating_add(1)).all(|right| bool::from(self.overlaps_are_independent(left, right))))))]
    pub fn batches<A>(
        &self,
        overlaps: &[Overlap<A>],
    ) -> Vec<Vec<Overlap<A>>>
    where
        A: CellAlphabet,
    {
        let mut batches: Vec<Vec<Overlap<A>>> = Vec::new();
        for overlap in overlaps {
            let open = batches.iter_mut().find(|batch| {
                batch
                    .iter()
                    .all(|held| bool::from(self.overlaps_are_independent(held, overlap)))
            });
            match open {
                | Some(batch) => batch.push(overlap.clone()),
                | None => batches.push(alloc::vec![overlap.clone()]),
            }
        }
        batches
    }

    /// Whether two overlaps are independent: every endpoint of one is
    /// independent of every endpoint of the other.
    ///
    /// # Specification
    /// - ensures: the conjunction of [`OverlapSupport::independent`] over the
    ///   four endpoint pairs; symmetric in its arguments.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every batch the clustered family schedules into is
    ///   pairwise independent by this test, and overlaps from one cluster are
    ///   never batched together. Each of the four cross-endpoint positions can
    ///   hold the only connecting edge. Omitting any conjunction term admits a
    ///   dependent pair.
    /// - witness: `tests::overlap::overlap_support_batches_are_pairwise_independent`
    /// - witness: `overlap::tests::every_cross_endpoint_can_block_an_overlap_batch`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == [left.left, left.right].iter().all(|one| [right.left, right.right].iter().all(|other| bool::from(self.independent(*one, *other)))))]
    pub fn overlaps_are_independent<A>(
        &self,
        left: &Overlap<A>,
        right: &Overlap<A>,
    ) -> StepIndependence
    where
        A: CellAlphabet,
    {
        StepIndependence::from(
            [
                (left.left, right.left),
                (left.left, right.right),
                (left.right, right.left),
                (left.right, right.right),
            ]
            .into_iter()
            .all(|(one, other)| bool::from(self.independent(one, other))),
        )
    }
}

/// The kind of an overlap.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlapKind
{
    /// The two left-hand sides unify at the root: a confluence critical pair.
    Confluence,
    /// The left cell's right-hand side unifies with the right cell's left-hand
    /// side at a command position: a sequential composition.
    Composition,
}

/// A refused operation on an overlap.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlapRefusal
{
    /// The operation reads a composition, and the overlap is a confluence.
    NotAComposition,
    /// The operation reads a confluence, and the overlap is a composition.
    NotAConfluence,
    /// The store holds no cell under an identifier the overlap names.
    UnissuedCell(CellId),
    /// The alphabet refused to splice the right cell's contractum in at the
    /// seam.
    SeamSplice(CommandSpliceRefusal),
}

impl core::fmt::Display for OverlapRefusal
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::NotAComposition => f.write_str("the overlap is not a composition"),
            | Self::NotAConfluence => f.write_str("the overlap is not a confluence"),
            | Self::UnissuedCell(cell) => {
                write!(f, "the store holds no cell {}", usize::from(cell))
            },
            | Self::SeamSplice(refusal) => write!(f, "the seam splice is refused: {refusal}"),
        }
    }
}

impl core::error::Error for OverlapRefusal
{
    /// The splice refusal behind a seam refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)>
    {
        match *self {
            | Self::SeamSplice(ref refusal) => Some(refusal),
            | Self::NotAComposition | Self::NotAConfluence | Self::UnissuedCell(_) => None,
        }
    }
}

/// One overlap between two cells at a seam, with its seam data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Overlap<A: CellAlphabet = SequentAlphabet>
{
    /// The left cell.
    pub left: CellId,
    /// The right cell.
    pub right: CellId,
    /// The overlap kind.
    pub kind: OverlapKind,
    /// The most general unifier at the seam.
    pub unifier: A::Subst,
    /// The seam: the root for a confluence, a command position of the left
    /// right-hand side for a composition.
    pub seam: A::Pos,
    /// The superposition `σ(l_left)` the overlap is rooted at.
    pub peak: A::Cmd,
    /// The right cell renamed apart from the left, which the unifier's
    /// bindings on the right read against.
    right_renamed: Cell<A>,
}

impl<A: CellAlphabet> Overlap<A>
{
    /// A confluence overlap from evidence a caller's own matcher supplies.
    ///
    /// A domain matcher may know a unifier the alphabet's generic
    /// [`CellAlphabet::unify_cmd`] does not find. This constructor records the
    /// supplied evidence without re-running the generic unifier; completion
    /// validates it before it reaches the worklist.
    ///
    /// # Specification
    /// - requires: `left` and `right` are `(id, cell)` pairs one store handed
    ///   out, and `unifier` and `seam` are the supplied evidence for them.
    /// - ensures: a confluence overlap carrying the two ids, `unifier` and
    ///   `seam`; its peak is `unifier` applied to the left cell's left-hand
    ///   side, and its right leg is the right cell renamed apart from the left
    ///   exactly as [`overlaps_between`] renames it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an overlap rebuilt from the enumerator's own unifier
    ///   through this constructor is accepted by completion, and one whose
    ///   unifier makes the legs miss the peak is declined with its position.
    ///   Changed evidence, peak construction or apartness alters validation
    ///   rather than silently admitting a malformed pair.
    /// - witness: `tests::completion::supplied_overlap_validation_returns_typed_declines`
    /// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
    #[inline]
    #[must_use]
    #[spec(captures: supplied = (unifier.clone(), seam.clone()), ensures: |output| output.left == left.0 && output.right == right.0
        && output.kind == OverlapKind::Confluence && output.unifier == supplied.0 && output.seam == supplied.1
        && output.peak == A::apply_subst(&output.unifier, left.1.lhs()) && output.right_renamed == renamed_apart(left.1, right.1))]
    pub fn from_supplied_confluence(
        left: (CellId, &Cell<A>),
        right: (CellId, &Cell<A>),
        unifier: A::Subst,
        seam: A::Pos,
    ) -> Self
    {
        let (left_id, left_cell) = left;
        let (right_id, right_cell) = right;
        let right_renamed = renamed_apart(left_cell, right_cell);
        let peak = A::apply_subst(&unifier, left_cell.lhs());
        Self {
            left: left_id,
            right: right_id,
            kind: OverlapKind::Confluence,
            unifier,
            seam,
            peak,
            right_renamed,
        }
    }

    /// The left reduct: the peak contracted at the root by the left cell.
    ///
    /// # Specification
    /// - ensures: the unifier applied to the left cell's right-hand side.
    /// - fails: [`OverlapRefusal::UnissuedCell`] when `store` holds no cell
    ///   under [`Overlap::left`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the composite of the frame and successor overlap is
    ///   built from this reduct, and a critical pair's legs compare it with the
    ///   right reduct. An unissued left identifier refuses by identity; a wrong
    ///   image or discarded lookup refusal changes the reduct.
    /// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
    /// - witness: `tests::completion::completion_processes_within_budget`
    /// - witness: `overlap::tests::overlap_reducts_preserve_refusal_precedence`
    #[inline]
    #[spec(ensures: |output| match store.get(self.left) {
        Maybe::Present(left) => output == Ok(A::apply_subst(&self.unifier, left.rhs())),
        Maybe::Absent(_) => output == Err(OverlapRefusal::UnissuedCell(self.left)),
    })]
    pub fn left_reduct(
        &self,
        store: &CellStore<A>,
    ) -> Result<A::Cmd, OverlapRefusal>
    {
        match store.get(self.left) {
            | Maybe::Present(left) => Ok(A::apply_subst(&self.unifier, left.rhs())),
            | Maybe::Absent(_) => Err(OverlapRefusal::UnissuedCell(self.left)),
        }
    }

    /// The right reduct of a confluence: the peak contracted at the root by
    /// the right cell.
    ///
    /// # Specification
    /// - requires: [`Overlap::kind`] is [`OverlapKind::Confluence`]; for a
    ///   composition the term is the right cell's contractum at the seam, not a
    ///   reduct of the peak.
    /// - ensures: the unifier applied to the renamed right cell's right-hand
    ///   side; the critical pair is `(left_reduct, right_reduct)`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completion normalizes this reduct against the left
    ///   one and either certifies the join or orients the divergence. Equal and
    ///   differing reducts separate joining from orientation; changing the
    ///   image changes that outcome.
    /// - witness: `tests::completion::completion_processes_within_budget`
    /// - witness: `tests::second_inhabitant::completion_orients_and_certifies_over_the_toy_alphabet`
    #[inline]
    #[must_use]
    #[spec(requires: self.kind == OverlapKind::Confluence, ensures: |output| output == A::apply_subst(&self.unifier, self.right_renamed.rhs()))]
    pub fn right_reduct(&self) -> A::Cmd
    {
        A::apply_subst(&self.unifier, self.right_renamed.rhs())
    }

    /// The right cell renamed apart from the left: the span's right leg.
    ///
    /// The enumerator renames the right cell's metavariables apart from the
    /// left cell's before unifying, so the unifier's bindings on the right
    /// read against this cell, never the stored one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right_renamed(&self) -> &Cell<A>
    {
        &self.right_renamed
    }

    /// The composite of a composition: the left cell fired at the root, then
    /// the right cell at the seam — the fused cell's right-hand side.
    ///
    /// # Specification
    /// - ensures: the left reduct with the seam's command replaced by the
    ///   unifier applied to the renamed right cell's right-hand side; the fused
    ///   cell is `peak ~> composite`.
    /// - fails: [`OverlapRefusal::NotAComposition`] for a confluence;
    ///   [`OverlapRefusal::UnissuedCell`] when `store` holds no cell under
    ///   [`Overlap::left`]; [`OverlapRefusal::SeamSplice`] when the alphabet
    ///   refuses the splice at the seam.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the frame and successor cells compose to the exact
    ///   commutation cell over the sequent alphabet, and the toy alphabet's two
    ///   addition cells compose below the root. Wrong kind precedes an unissued
    ///   left identifier, and an off-term seam refuses after the left reduct.
    ///   Changed precedence or context changes the result.
    /// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
    /// - witness: `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`
    /// - witness: `overlap::tests::overlap_reducts_preserve_refusal_precedence`
    #[inline]
    #[spec(ensures: |output| if self.kind == OverlapKind::Composition {
        match self.left_reduct(store) {
            Ok(left) => output == A::splice_cmd_at(&left, &self.seam, A::apply_subst(&self.unifier, self.right_renamed.rhs())).map_err(OverlapRefusal::SeamSplice),
            Err(reason) => output == Err(reason),
        }
    } else { output == Err(OverlapRefusal::NotAComposition) })]
    pub fn composite(
        &self,
        store: &CellStore<A>,
    ) -> Result<A::Cmd, OverlapRefusal>
    {
        if self.kind != OverlapKind::Composition {
            return Err(OverlapRefusal::NotAComposition);
        }
        let after_left = self.left_reduct(store)?;
        let right_contractum = A::apply_subst(&self.unifier, self.right_renamed.rhs());
        A::splice_cmd_at(&after_left, &self.seam, right_contractum)
            .map_err(OverlapRefusal::SeamSplice)
    }
}

/// The right cell renamed apart from the left, with the right cell's tags.
///
/// # Specification
/// trivial.
fn renamed_apart<A>(
    left: &Cell<A>,
    right: &Cell<A>,
) -> Cell<A>
where
    A: CellAlphabet,
{
    let (lhs, rhs) = A::rename_apart((left.lhs(), left.rhs()), (right.lhs(), right.rhs()));
    Cell::new(lhs, rhs, right.orient(), right.provenance())
}

/// Whether a peak's two one-step contractions are the same term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PeakLegs
{
    /// Both contractions give the same term, so the peak joins in no steps.
    Coincide,
    /// The contractions differ, so the peak is a critical pair worth carrying.
    Differ,
}

/// Decide whether a root confluence peak's two legs coincide.
///
/// This states the exception in [`enumerate_overlaps`]'s completeness claim:
/// the enumeration omits each cell's overlap with itself at the root, and is
/// entitled to, because the root unifier of a pattern with its own renaming
/// apart is that renaming, so both contractions land on one term.
///
/// It is not the enumerator's suppression test. Suppressing every peak whose
/// legs coincide would delete real work: a ground rule and a schematic rule
/// over one operation are distinct cells whose legs coincide once unification
/// instantiates the schematic one, and completion certifies that joinable pair.
/// Coinciding legs mean trivially joinable, not absent.
///
/// # Specification
/// - requires: `unifier` unifies the two left-hand sides, and the two
///   right-hand sides are the left cell's own and the renamed right cell's.
/// - ensures: [`PeakLegs::Coincide`] exactly when the unifier sends the two
///   right-hand sides to one term.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a cell's diagonal peak, computed and contracted both
///   ways, coincides, and a genuine critical pair between a ground and a
///   schematic rule differs. Swapping coincidence and divergence changes the
///   exact decision at those two boundaries.
/// - witness: `tests::overlap::the_suppressed_diagonal_peak_has_coinciding_legs`
/// - witness: `tests::overlap::a_real_critical_pair_has_differing_legs`
#[inline]
#[must_use]
#[spec(ensures: |output| (output == PeakLegs::Coincide) == (A::apply_subst(unifier, left_rhs) == A::apply_subst(unifier, right_rhs)))]
pub fn peak_legs<A>(
    unifier: &A::Subst,
    left_rhs: &A::Cmd,
    right_rhs: &A::Cmd,
) -> PeakLegs
where
    A: CellAlphabet,
{
    if A::apply_subst(unifier, left_rhs) == A::apply_subst(unifier, right_rhs) {
        return PeakLegs::Coincide;
    }
    PeakLegs::Differ
}

/// Enumerate the overlap family of every ordered cell pair in `store`.
///
/// The family is complete up to the root diagonal: a cell is not overlapped
/// with itself at the root, where the two contractions coincide by
/// construction ([`peak_legs`]). This is not the Knuth–Bendix exclusion of
/// self-overlaps: completion over first-order terms needs a rule's overlaps
/// with itself at interior positions of its left-hand side, and the confluence
/// branch here unifies whole left-hand sides at the root for every pair, so
/// its family is the root-shared peaks. A consumer needing interior
/// self-overlaps needs a different enumerator, not this one with the guard
/// removed.
///
/// # Specification
/// - ensures: the concatenation of [`overlaps_between`] over every ordered pair
///   of the store's cells, left cell outer and in store order; one entry per
///   unifier, never collapsed.
/// - ensures: the family depends on the store's identifiers as well as its
///   cells: two structurally equal cells share one identifier and take the
///   excluded diagonal, two renamings of one rule take two and do not.
/// - panics: none.
/// - intension: one pair query per ordered cell pair.
///
/// # Adequacy
/// - hypothesis: L3 — the sequent alphabet's frame and successor cells give the
///   same family twice and include their commutation composite, and the toy
///   alphabet's addition cells give a composition below the root. Empty stores
///   yield no overlaps; reordered pairs, omitted compositions or forged
///   endpoints change the family.
/// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
/// - witness: `tests::overlap::overlaps_are_a_deterministic_family`
/// - witness: `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`
/// - witness: `overlap::tests::support_identity_and_empty_certificates_have_distinct_boundaries`
#[inline]
#[must_use]
#[spec(ensures: |output| output.iter().all(|overlap| matches!(store.get(overlap.left), Maybe::Present(_)) && matches!(store.get(overlap.right), Maybe::Present(_)))
    && output.iter().map(|overlap| (overlap.left, overlap.right)).is_sorted()
    && (!bool::from(store.is_empty()) || output.is_empty()))]
pub fn enumerate_overlaps<A>(store: &CellStore<A>) -> Vec<Overlap<A>>
where
    A: CellAlphabet,
{
    let mut out = Vec::new();
    for (left_id, left) in store.iter() {
        for (right_id, right) in store.iter() {
            out.extend(overlaps_between((left_id, left), (right_id, right)));
        }
    }
    out
}

/// The overlap family of one ordered cell pair, the query
/// [`enumerate_overlaps`] iterates.
///
/// Independence is keyed by cell pair, so a consumer asking about two cells
/// pays for those two, not for the store-wide sweep.
///
/// # Specification
/// - requires: `left` and `right` are `(id, cell)` pairs one store handed out,
///   so the emitted identifiers address the cells they name.
/// - ensures: the confluence overlap of the two left-hand sides when they unify
///   — omitted when the two identifiers are equal — then one composition
///   overlap per command position of the left right-hand side that unifies with
///   the right left-hand side, in the alphabet's position order.
/// - ensures: every confluence entry's seam is the root position.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — reassembling the pair queries over every ordered pair
///   reproduces the store-wide family exactly, and every confluence entry
///   carries the root seam over an alphabet whose terms have interior command
///   positions. A matching diagonal omits root confluence while preserving
///   composition candidates; wrong suppression or seam construction changes the
///   family.
/// - witness: `tests::overlap::the_pair_query_agrees_with_the_store_wide_family`
/// - witness: `tests::overlap::every_confluence_entry_carries_the_root_seam`
/// - witness: `tests::second_inhabitant::every_toy_confluence_entry_carries_the_root_seam`
/// - witness: `overlap::tests::overlap_reducts_preserve_refusal_precedence`
#[inline]
#[must_use]
#[spec(ensures: |output| output.iter().all(|overlap| overlap.left == left.0 && overlap.right == right.0
        && overlap.peak == A::apply_subst(&overlap.unifier, left.1.lhs())
        && match overlap.kind {
            OverlapKind::Confluence => left.0 != right.0 && overlap.seam == A::root_position(),
            OverlapKind::Composition => A::command_positions(left.1.rhs()).contains(&overlap.seam),
        })
    && output.iter().filter(|overlap| overlap.kind == OverlapKind::Confluence).count() <= 1
    && output.iter().skip_while(|overlap| overlap.kind == OverlapKind::Confluence).all(|overlap| overlap.kind == OverlapKind::Composition))]
pub fn overlaps_between<A>(
    left: (CellId, &Cell<A>),
    right: (CellId, &Cell<A>),
) -> Vec<Overlap<A>>
where
    A: CellAlphabet,
{
    let (left_id, left_cell) = left;
    let (right_id, right_cell) = right;
    let mut out = Vec::new();
    let renamed = renamed_apart(left_cell, right_cell);
    // The guard is on the identifiers, not on whether the legs coincide: a
    // ground rule and a schematic rule over one operation are distinct cells
    // whose legs coincide once unified, and that joinable pair is real work
    // completion certifies. See `peak_legs`.
    if left_id != right_id {
        let mut unifier = A::Subst::default();
        if bool::from(A::unify_cmd(left_cell.lhs(), renamed.lhs(), &mut unifier)) {
            let peak = A::apply_subst(&unifier, left_cell.lhs());
            out.push(Overlap {
                left: left_id,
                right: right_id,
                kind: OverlapKind::Confluence,
                unifier,
                seam: A::root_position(),
                peak,
                right_renamed: renamed.clone(),
            });
        }
    }
    for seam in A::command_positions(left_cell.rhs()) {
        let Maybe::Present(sub) = A::subterm_cmd_at(left_cell.rhs(), &seam)
        else {
            continue;
        };
        let mut unifier = A::Subst::default();
        if bool::from(A::unify_cmd(&sub, renamed.lhs(), &mut unifier)) {
            let peak = A::apply_subst(&unifier, left_cell.lhs());
            out.push(Overlap {
                left: left_id,
                right: right_id,
                kind: OverlapKind::Composition,
                unifier,
                seam,
                peak,
                right_renamed: renamed.clone(),
            });
        }
    }
    out
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;

    use super::*;
    use crate::rewrite::CellApp;

    #[test]
    fn support_identity_and_empty_certificates_have_distinct_boundaries()
    {
        for (left, right, low, high) in [
            (0_usize, 0_usize, 0_usize, 0_usize),
            (0, 7, 0, 7),
            (7, 0, 0, 7),
            (usize::MAX, 0, 0, usize::MAX),
            (0, usize::MAX, 0, usize::MAX),
        ] {
            assert_eq!(
                CellPair(CellId::from(low), CellId::from(high)),
                CellPair::new(CellId::from(left), CellId::from(right))
            );
            assert_eq!(
                (CertificateIndex::from(low), CertificateIndex::from(high)),
                certificate_pair(CertificateIndex::from(left), CertificateIndex::from(right))
            );
        }
        let empty_store = CellStore::<ToyAlphabet>::new();
        let empty_support = OverlapSupport::from_store(&empty_store);
        assert!(enumerate_overlaps(&empty_store).is_empty());
        assert!(empty_support.batches::<ToyAlphabet>(&[]).is_empty());
        let a = BTreeSet::from([CellId::from(0_usize)]);
        let b = BTreeSet::from([CellId::from(1_usize)]);
        assert!(bool::from(
            empty_support.independent(CellId::from(0_usize), CellId::from(0_usize))
        ));
        assert!(bool::from(
            empty_support.supports_independent(&BTreeSet::new(), &a)
        ));
        assert!(bool::from(empty_support.supports_independent(&a, &b)));
        assert!(!bool::from(empty_support.supports_independent(&a, &a)));
        let cell = toy_cell(Toy::zero(), Toy::zero());
        let mut store = CellStore::new();
        let id = store.insert(cell.clone());
        let overlap = Overlap::from_supplied_confluence(
            (id, &cell),
            (id, &cell),
            gandr_theory_cell_complexes_tools::ToySubst::default(),
            ToyAlphabet::root_position(),
        );
        let empty = Tracelet {
            overlap: overlap.clone(),
            path_a: Vec::new(),
            path_b: Vec::new(),
            joins_at: Toy::zero(),
        };
        let mut support = OverlapSupport::from_store(&store);
        let before = support.clone();
        assert_eq!(
            (
                CertificateIndex::from(0_usize),
                CertificateIndex::from(0_usize)
            ),
            support.add_certificates::<ToyAlphabet>(&[])
        );
        assert_eq!(before, support);
        assert_eq!(
            (
                CertificateIndex::from(0_usize),
                CertificateIndex::from(2_usize)
            ),
            support.add_certificates(&[empty.clone(), empty.clone()])
        );
        assert!(!bool::from(support.certificates_independent(
            CertificateIndex::from(0_usize),
            CertificateIndex::from(0_usize)
        )));
        assert!(bool::from(support.certificates_independent(
            CertificateIndex::from(0_usize),
            CertificateIndex::from(1_usize)
        )));
        for unknown in [2_usize, usize::MAX] {
            assert!(bool::from(support.certificates_independent(
                CertificateIndex::from(unknown),
                CertificateIndex::from(0_usize)
            )));
            assert!(bool::from(support.certificates_independent(
                CertificateIndex::from(unknown),
                CertificateIndex::from(unknown)
            )));
        }
        let mut traced = empty;
        traced.path_a.push(CellApp {
            cell: id,
            at: ToyAlphabet::root_position(),
        });
        assert_eq!(
            (
                CertificateIndex::from(2_usize),
                CertificateIndex::from(4_usize)
            ),
            support.add_certificates(&[traced.clone(), traced])
        );
        assert!(bool::from(support.certificates_independent(
            CertificateIndex::from(1_usize),
            CertificateIndex::from(2_usize)
        )));
        assert!(!bool::from(support.certificates_independent(
            CertificateIndex::from(2_usize),
            CertificateIndex::from(3_usize)
        )));
        assert_eq!(
            alloc::vec![alloc::vec![overlap.clone()], alloc::vec![overlap.clone()]],
            support.batches(&[overlap.clone(), overlap])
        );
    }

    #[test]
    fn every_cross_endpoint_can_block_an_overlap_batch()
    {
        let one = || Toy::succ(Toy::zero());
        let triple = |x, y, z| Toy::add(x, Toy::add(y, z));
        let output = ToyAlphabet::skolemize(&Toy::var("out"));
        let cells = [
            toy_cell(
                triple(Toy::zero(), Toy::var("a"), Toy::zero()),
                output.clone(),
            ),
            toy_cell(
                triple(Toy::var("b"), Toy::zero(), Toy::zero()),
                output.clone(),
            ),
            toy_cell(triple(one(), Toy::zero(), Toy::var("c")), output.clone()),
            toy_cell(triple(one(), Toy::var("d"), one()), output),
        ];
        let mut store = CellStore::new();
        let ids = cells.clone().map(|cell| store.insert(cell));
        let support = OverlapSupport::from_store(&store);
        assert!(!bool::from(support.independent(ids[1], ids[2])));
        for (a, b) in [(0_usize, 2_usize), (0, 3), (1, 3)] {
            assert!(bool::from(support.independent(ids[a], ids[b])));
        }
        for (a, b) in [(0_usize, 1_usize), (1, 0)] {
            let left = overlaps_between((ids[a], &cells[a]), (ids[b], &cells[b]))
                .into_iter()
                .find(|overlap| overlap.kind == OverlapKind::Confluence)
                .expect("the left adjacent patterns unify");
            for (c, d) in [(2_usize, 3_usize), (3, 2)] {
                let right = overlaps_between((ids[c], &cells[c]), (ids[d], &cells[d]))
                    .into_iter()
                    .find(|overlap| overlap.kind == OverlapKind::Confluence)
                    .expect("the right adjacent patterns unify");
                assert!(!bool::from(support.overlaps_are_independent(&left, &right)));
                assert_eq!(
                    alloc::vec![alloc::vec![left.clone()], alloc::vec![right.clone()]],
                    support.batches(&[left.clone(), right])
                );
            }
        }
    }

    #[test]
    fn overlap_reducts_preserve_refusal_precedence()
    {
        let left = toy_cell(Toy::succ(Toy::zero()), Toy::zero());
        let right = toy_cell(Toy::zero(), Toy::succ(Toy::zero()));
        let mut store = CellStore::new();
        let left_id = store.insert(left.clone());
        let right_id = store.insert(right.clone());
        let composition = overlaps_between((left_id, &left), (right_id, &right))
            .into_iter()
            .find(|overlap| overlap.kind == OverlapKind::Composition)
            .expect("the first reduct matches the second cell");
        assert_eq!(Ok(Toy::zero()), composition.left_reduct(&store));
        assert_eq!(Ok(Toy::succ(Toy::zero())), composition.composite(&store));
        let empty = CellStore::new();
        assert_eq!(
            Err(OverlapRefusal::UnissuedCell(left_id)),
            composition.left_reduct(&empty)
        );
        assert_eq!(
            Err(OverlapRefusal::UnissuedCell(left_id)),
            composition.composite(&empty)
        );
        let mut confluence = composition.clone();
        confluence.kind = OverlapKind::Confluence;
        assert_eq!(
            Err(OverlapRefusal::NotAComposition),
            confluence.composite(&empty)
        );
        let mut off_term = composition;
        off_term.seam = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
        assert_eq!(
            Err(OverlapRefusal::SeamSplice(CommandSpliceRefusal::OffTerm)),
            off_term.composite(&store)
        );
        let identity = toy_cell(Toy::zero(), Toy::zero());
        let identity_id = store.insert(identity.clone());
        let diagonal = overlaps_between((identity_id, &identity), (identity_id, &identity));
        assert_eq!(1, diagonal.len());
        assert_eq!(OverlapKind::Composition, diagonal[0].kind);
        assert_eq!(ToyAlphabet::root_position(), diagonal[0].seam);
    }
}
