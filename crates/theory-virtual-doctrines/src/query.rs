//! Constructor-menu queries over the cell store.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::normalize;
use quenchant_shape::shape::Maybe;

use crate::boundary::RewriteCompletion;
use crate::boundary::RewriteReachability;
use crate::boundary::RewriteStepBudget;
use crate::vdc::RelationRef;

/// A **rewrite path** — a reduction trace and its endpoint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RewritePath
{
    /// The endpoint reached (a normal form when `complete`).
    pub target: CmdPat,
    /// The reduction steps taken, in order.
    pub steps: Vec<CellApp>,
    /// Whether a normal form was reached within budget.
    pub complete: RewriteCompletion,
}

/// A **seam composite** — one overlap-indexed member of the ⊙ family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SeamComposite
{
    /// The left generating cell.
    pub left: CellId,
    /// The right generating cell.
    pub right: CellId,
    /// The fused right-hand side the composition produces.
    pub composite: CmdPat,
}

/// A **right/left extension candidate** — a seam a completing consumer
/// resolves.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtensionCandidate
{
    /// The left generating cell of the critical pair.
    pub left: CellId,
    /// The right generating cell of the critical pair.
    pub right: CellId,
    /// The superposition peak the completion would join.
    pub peak: CmdPat,
}

/// One **instance** of a relation — a generating cell with its two projections.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstanceRow
{
    /// The generating cell this instance comes from.
    pub cell: CellId,
    /// The source-side projection (the cell's left-hand face).
    pub left: CmdPat,
    /// The target-side projection (the cell's right-hand face).
    pub right: CmdPat,
}

/// The **instantiation table** of a relation — its instances with two
/// projections.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InstanceTable
{
    /// The instance rows, one per resolvable generating cell.
    pub rows: Vec<InstanceRow>,
}

/// The **query view** over a cell store — the constructor menu's realization.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Query<'store>
{
    /// The cell store the queries read.
    pub cells: &'store CellStore,
}

impl<'store> Query<'store>
{
    /// A query view over `cells`.
    #[inline]
    #[must_use]
    /// # Specification
    /// trivial.
    pub fn new(cells: &'store CellStore) -> Self
    {
        Self { cells }
    }

    /// The **path** query (`⤳` unit) — normalize `from` under the store, taking
    /// at most `budget` steps, and return the reduction trace.
    ///
    /// # Specification
    /// - ensures: the [`RewritePath`] whose `target` is the term reached,
    ///   `steps` the fired reductions in order, and `complete` true iff a
    ///   normal form was reached within `budget` (never diverges — the budget
    ///   is the guard).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — the trace is replayed against the store by
    ///   re-running `steps` from `from` and asserting it reproduces `target`
    ///   (external oracle: the engine's own rewriting).
    /// - witness: `tests::laws::tests::a_path_query_trace_reproduces_its_target`
    #[inline]
    #[must_use]
    #[spec(ensures: |out| out.steps.len() <= usize::from(budget) && bool::from(gandr_theory_coherent_resolutions::replay_from_peak(self.cells, from, &out.target, &out.steps, &out.steps)) && bool::from(out.complete) == matches!(gandr_theory_coherent_resolutions::apply_once(self.cells, &out.target), Maybe::Absent(_)))]
    pub fn path(
        &self,
        from: &CmdPat,
        budget: RewriteStepBudget,
    ) -> RewritePath
    {
        let normalization = normalize(self.cells, from, usize::from(budget).into());
        RewritePath {
            target: normalization.normal,
            steps: normalization.path,
            complete: RewriteCompletion::from(!bool::from(normalization.exhausted)),
        }
    }

    /// Whether `from` **reaches** `to` within `budget` — the path-existence
    /// query.
    ///
    /// # Specification
    /// - ensures: `true` iff normalizing `from` within `budget` reaches a
    ///   normal form structurally equal to `to`.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L3 — the law witnesses the reached endpoint. The predicate
    ///   observes only that a claimed target has no remaining redex, not
    ///   reachability by itself.
    /// - witness: `tests::laws::tests::a_path_query_trace_reproduces_its_target`
    #[spec(ensures: |out| !bool::from(out) || matches!(gandr_theory_coherent_resolutions::apply_once(self.cells, to), Maybe::Absent(_)))]
    pub fn reaches(
        &self,
        from: &CmdPat,
        to: &CmdPat,
        budget: RewriteStepBudget,
    ) -> RewriteReachability
    {
        let path = self.path(from, budget);
        RewriteReachability::from(bool::from(path.complete) && path.target == *to)
    }

    /// **Path induction** — fold a value over a rewrite trace (induction on
    /// traces: `base` is the value on `refl`, `step` extends by one reduction).
    ///
    /// # Specification
    /// - ensures: `base` when the path is empty (the `refl` case); otherwise
    ///   `step` folded left-to-right over the path's steps — the reflected
    ///   `PathInd` (a cell out of the path relation is determined by its value
    ///   on `refl` and its action on each reduction).
    /// - panics: none.
    #[inline]
    #[must_use]
    /// - executable: none — Acc has no equality constraint, and invoking Step
    ///   again can change its caller-visible effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a noncommutative trace fold observes the base and
    ///   step order. No executable predicate re-invokes the caller-supplied
    ///   step: it may have effects and Acc need not support equality.
    /// - witness: `tests::laws::tests::path_induction_folds_the_reduction_trace`
    pub fn induct<Acc, Step>(
        path: &RewritePath,
        base: Acc,
        step: Step,
    ) -> Acc
    where
        Step: Fn(Acc, &CellApp) -> Acc,
    {
        let mut acc = base;
        for cell_app in &path.steps {
            acc = step(acc, cell_app);
        }
        acc
    }

    /// The **⊙ seam family** — the overlap-indexed composites of `left`'s
    /// generators against `right`'s.
    ///
    /// # Specification
    /// - ensures: one [`SeamComposite`] per composition overlap between a
    ///   generator of `left` and a generator of `right`, in the deterministic
    ///   enumeration order; the **family** (multi-sum), never collapsed to a
    ///   single rule — a non-linear seam yields several composites (the
    ///   *virtual* weakening's honest fan-out).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence — each returned composite is re-derived from
    ///   the overlap and asserted equal (the engine's `composite` is the
    ///   oracle); boundary: a non-linear seam returns a multi-member family.
    /// - witness: `tests::laws::tests::the_seam_family_is_the_overlap_indexed_multi_sum`
    #[inline]
    #[must_use]
    #[spec(ensures: |out| out.iter().all(|member| left.generators.contains(&member.left) && right.generators.contains(&member.right)))]
    pub fn seam_family(
        &self,
        left: &RelationRef,
        right: &RelationRef,
    ) -> Vec<SeamComposite>
    {
        let mut out = Vec::new();
        for overlap in enumerate_overlaps(self.cells) {
            if overlap.kind != OverlapKind::Composition
                || !left.generators.contains(&overlap.left)
                || !right.generators.contains(&overlap.right)
            {
                continue;
            }
            if let Ok(composite) = overlap.composite(self.cells) {
                out.push(SeamComposite {
                    left: overlap.left,
                    right: overlap.right,
                    composite,
                });
            }
        }
        out
    }

    /// The **⊲/⊳ extension candidates** — the confluence critical pairs among a
    /// relation's generators.
    ///
    /// This is the query *surface* for the Kan-shaped extension; the
    /// best-consumer **synthesis** (running budgeted completion to derive
    /// the frame) is the completion engine's job and is not run here.
    ///
    /// # Specification
    /// - ensures: one [`ExtensionCandidate`] per confluence overlap between two
    ///   generators of `rel`, in enumeration order — the critical-pair seams
    ///   the completion loop would resolve into a derived frame.
    /// - panics: none.
    #[inline]
    #[must_use]
    /// # Adequacy
    /// - hypothesis: L1 — the predicate observes both generator filters.
    ///   Confluence classification and exhaustiveness follow the engine
    ///   enumeration, not membership alone.
    /// - witness: `tests::laws::tests::the_seam_family_is_the_overlap_indexed_multi_sum`
    #[spec(ensures: |out| out.iter().all(|candidate| rel.generators.contains(&candidate.left) && rel.generators.contains(&candidate.right)))]
    pub fn extension_candidates(
        &self,
        rel: &RelationRef,
    ) -> Vec<ExtensionCandidate>
    {
        let mut out = Vec::new();
        for overlap in enumerate_overlaps(self.cells) {
            if overlap.kind != OverlapKind::Confluence
                || !rel.generators.contains(&overlap.left)
                || !rel.generators.contains(&overlap.right)
            {
                continue;
            }
            out.push(ExtensionCandidate {
                left: overlap.left,
                right: overlap.right,
                peak: overlap.peak,
            });
        }
        out
    }

    /// The **tabulator** `{|R|}` — the instantiation table of a relation, each
    /// generating cell an instance with its two projections.
    ///
    /// # Specification
    /// - ensures: one [`InstanceRow`] per generating cell of `rel` present in
    ///   the store, in the relation's generator order, whose `left`/`right` are
    ///   the cell's two faces (the two-sided category-of-elements the
    ///   inspection protocol renders); a stale generator id contributes no row.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — the row count and the exact projected faces
    ///   are asserted against a small hand-built relation, with a stale id as
    ///   the boundary that contributes no row.
    /// - witness: `tests::laws::tests::the_tabulator_projects_each_instance_to_its_two_faces`
    #[inline]
    #[must_use]
    #[spec(ensures: |out| out.rows.iter().map(|row| (&row.cell, &row.left, &row.right)).eq(rel.generators.iter().filter_map(|id| match self.cells.get(*id) { Maybe::Present(cell) => Some((id, cell.lhs(), cell.rhs())), Maybe::Absent(_) => None })))]
    pub fn tabulate(
        &self,
        rel: &RelationRef,
    ) -> InstanceTable
    {
        let mut rows = Vec::new();
        for &id in &rel.generators {
            if let Maybe::Present(cell) = self.cells.get(id) {
                rows.push(InstanceRow {
                    cell: id,
                    left: cell.lhs().clone(),
                    right: cell.rhs().clone(),
                });
            }
        }
        InstanceTable { rows }
    }
}
