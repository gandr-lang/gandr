//! Directed and invertible certificate composition.

use anodized::spec;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_decomposition_spaces::CompositionObstruction;
use gandr_theory_decomposition_spaces::compose_directed;
use gandr_theory_decomposition_spaces::compose_invertible;
use quenchant_shape::shape::Maybe;

use crate::boundary::CertificateInvertibility;
use crate::boundary::CutCoherence;
use crate::boundary::CutDeclination;

/// The outcome of a [`directed_cut`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CutOutcome
{
    /// Admitted **unconditionally** — every participating cell is invertible,
    /// so the cut uses the ungated `compose_invertible`.
    Coherent(Tracelet),
    /// Admitted through the **acyclicity gate** — the directed lane's
    /// variable-flow graph was acyclic and `compose_directed` composed.
    Directed(Tracelet),
    /// **Declined** by the acyclicity gate — a variable-flow cycle obstructs
    /// the directed composition (canonically a shared mixed-variance seam
    /// hole).
    Declined(CompositionObstruction),
}

impl CutOutcome
{
    /// The composite certificate, when the cut was admitted (either lane).
    ///
    /// # Specification
    /// - ensures: `Ok` borrows the admitted certificate; `Err` borrows the
    ///   recorded composition obstruction.
    /// - panics: none.
    #[inline]
    /// # Errors
    /// Returns the recorded composition obstruction for a declined cut.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the admitted and declined cut witnesses preserve
    ///   actual certificates and obstruction evidence, not just success flags.
    /// - witness: `tests::directed::tests::a_mixed_variance_cycle_is_declined`
    #[spec(ensures: |ret| match *self { Self::Coherent(ref expected) | Self::Directed(ref expected) => ret == Ok(expected), Self::Declined(ref expected) => ret == Err(expected) })]
    pub fn tracelet(&self) -> Result<&Tracelet, &CompositionObstruction>
    {
        match *self {
            | Self::Coherent(ref t) | Self::Directed(ref t) => Ok(t),
            | Self::Declined(ref reason) => Err(reason),
        }
    }

    /// Whether the cut was admitted unconditionally (the invertible / coherence
    /// lane).
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_coherent(&self) -> CutCoherence
    {
        CutCoherence::from(matches!(*self, Self::Coherent(_)))
    }

    /// Whether the cut was declined by the acyclicity gate.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn is_declined(&self) -> CutDeclination
    {
        CutDeclination::from(matches!(*self, Self::Declined(_)))
    }
}

/// **The directed cut** — compose two directed certificates, routing off the
/// invertible boundary.
///
/// When every participating cell of both certificates is invertible
/// ([`all_participating_invertible`]), the cut is admissible unconditionally
/// (the boundary theorem): it uses the ungated
/// [`gandr_theory_decomposition_spaces::compose_invertible`] and yields
/// [`CutOutcome::Coherent`]. Otherwise it consults the acyclicity gate
/// ([`gandr_theory_decomposition_spaces::compose_directed`]):
/// [`CutOutcome::Directed`] when the seam variable-flow graph is acyclic,
/// [`CutOutcome::Declined`] when a cycle obstructs it.
///
/// The gate this routes to recomputes its flow graph on every consultation
/// rather than maintaining one; why that is a property of the call shape, and
/// what would change it, is stated at
/// [`gandr_theory_decomposition_spaces::compose_directed`].
///
/// Composing a family means folding this function, and that fold's verdict does
/// **not** factor through the pairwise verdicts of the certificates in it — a
/// chain whose every adjacent pair is admitted may still be declined. The same
/// statement carries what the verdict does factor through; the measurement and
/// its witnesses are `overlap_factoring` in this crate's test suite.
///
/// # Specification
/// - requires: `a.joins_at == b.overlap.peak` (the sequential seam) for the
///   admitted composite to **replay**; admissibility itself (which lane, and
///   whether the gate declines) is decided from the cells' invertibility and
///   variance alone.
/// - ensures: [`CutOutcome::Coherent`] iff both certificates are wholly
///   invertible (never [`CutOutcome::Declined`] on that lane — the boundary
///   theorem); otherwise the gate's verdict — [`CutOutcome::Directed`] on an
///   acyclic seam, [`CutOutcome::Declined`] carrying the
///   [`CompositionObstruction`] cycle otherwise. Never diverges or panics.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 evidence + property — an all-invertible ground chain always
///   yields [`CutOutcome::Coherent`] whose composite replays (the boundary
///   theorem's operational content, over generated chain lengths); a
///   mixed-variance (non-invertible) cycle yields [`CutOutcome::Declined`]
///   carrying the flow cycle. Boundary: the same seam is `Coherent` when its
///   cells are invertible and `Declined` when they are directed and cyclic.
/// - witness: `tests::directed::tests::an_invertible_chain_cuts_unconditionally`
/// - witness: `tests::directed::tests::a_mixed_variance_cycle_is_declined`
/// - witness: `tests::directed::tests::the_invertible_lane_is_never_declined`
#[inline]
#[must_use]
#[spec(ensures: |out| match out { CutOutcome::Coherent(ref cert) => bool::from(all_participating_invertible(a, store)) && bool::from(all_participating_invertible(b, store)) && cert.overlap.peak == a.overlap.peak && cert.joins_at == b.joins_at, CutOutcome::Directed(ref cert) => (!bool::from(all_participating_invertible(a, store)) || !bool::from(all_participating_invertible(b, store))) && cert.overlap.peak == a.overlap.peak && cert.joins_at == b.joins_at, CutOutcome::Declined(_) => !bool::from(all_participating_invertible(a, store)) || !bool::from(all_participating_invertible(b, store)) })]
pub fn directed_cut(
    a: &Tracelet,
    b: &Tracelet,
    store: &CellStore,
) -> CutOutcome
{
    if bool::from(all_participating_invertible(a, store))
        && bool::from(all_participating_invertible(b, store))
    {
        return CutOutcome::Coherent(compose_invertible(a, b));
    }
    match compose_directed(a, b, store) {
        | Ok(composite) => CutOutcome::Directed(composite),
        | Err(obstruction) => CutOutcome::Declined(obstruction),
    }
}

/// Whether **every** cell a certificate fires is an invertible joinability
/// certificate.
///
/// Reads the live [`gandr_theory_cell_complexes::CellMeta::invertible`] of each
/// cell in `path_a` then `path_b`. A stale cell id (absent from the store) is
/// **conservatively** not invertible — invertibility cannot be certified for a
/// cell that is not there.
///
/// # Specification
/// - ensures: `true` iff every [`gandr_theory_cell_complexes::CellId`] the
///   certificate fires resolves in `store` and carries `meta.invertible`;
///   vacuously `true` for a certificate with empty paths (a groupoid identity).
/// - panics: none.
#[inline]
#[must_use]
/// # Adequacy
/// - hypothesis: L3 — both certificate paths consult current engine metadata;
///   an unissued identifier refuses the unconditional lane.
/// - witness: `tests::directed::tests::an_invertible_chain_cuts_unconditionally`
#[spec(ensures: |out| bool::from(out) == cert.path_a.iter().chain(&cert.path_b).all(|step| matches!(store.get(step.cell), Maybe::Present(cell) if bool::from(cell.meta().invertible()))))]
pub fn all_participating_invertible(
    cert: &Tracelet,
    store: &CellStore,
) -> CertificateInvertibility
{
    CertificateInvertibility::from(cert.path_a.iter().chain(&cert.path_b).all(|step| {
        matches!(store.get(step.cell), Maybe::Present(cell) if bool::from(cell.meta().invertible()))
    }))
}
