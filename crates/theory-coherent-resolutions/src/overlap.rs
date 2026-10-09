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
    /// trivial.
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
/// trivial.
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
    ///   compose, are related in both argument orders.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    #[inline]
    #[must_use]
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
    ///   certificates equals two calls over one each.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    #[inline]
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
    /// trivial.
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
    ///   dependent.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    #[inline]
    #[must_use]
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
    ///   in both argument orders.
    /// - witness: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`
    #[inline]
    #[must_use]
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
    ///   three at the exact input positions first-fit predicts.
    /// - witness: `tests::overlap::overlap_support_batches_are_pairwise_independent`
    #[inline]
    #[must_use]
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
    ///   never batched together.
    /// - witness: `tests::overlap::overlap_support_batches_are_pairwise_independent`
    #[inline]
    #[must_use]
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
    /// - witness: `tests::completion::supplied_overlap_validation_returns_typed_declines`
    /// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
    #[inline]
    #[must_use]
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
    ///   right reduct.
    /// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
    /// - witness: `tests::completion::completion_processes_within_budget`
    #[inline]
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
    ///   one and either certifies the join or orients the divergence.
    /// - witness: `tests::completion::completion_processes_within_budget`
    /// - witness: `tests::second_inhabitant::completion_orients_and_certifies_over_the_toy_alphabet`
    #[inline]
    #[must_use]
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
    ///   addition cells compose below the root.
    /// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
    /// - witness: `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`
    #[inline]
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
///   schematic rule differs.
/// - witness: `tests::overlap::the_suppressed_diagonal_peak_has_coinciding_legs`
/// - witness: `tests::overlap::a_real_critical_pair_has_differing_legs`
#[inline]
#[must_use]
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
///   alphabet's addition cells give a composition below the root.
/// - witness: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`
/// - witness: `tests::overlap::overlaps_are_a_deterministic_family`
/// - witness: `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`
#[inline]
#[must_use]
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
///   positions.
/// - witness: `tests::overlap::the_pair_query_agrees_with_the_store_wide_family`
/// - witness: `tests::overlap::every_confluence_entry_carries_the_root_seam`
/// - witness: `tests::second_inhabitant::every_toy_confluence_entry_carries_the_root_seam`
#[inline]
#[must_use]
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
