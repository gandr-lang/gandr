//! The fusion rows of a census: each composition overlap of a block fused,
//! its certificate replayed, and its distance grade composed through the two
//! steps of its derivation in the Lawvere quantale.
//!
//! # A cell's distance grade
//!
//! A cell's grade has two parts. The first is the distance of its step: one
//! tick for a written rule, and none for a cell that the elaboration adds.
//! The second is each hole's count, which is the hole's Lipschitz constant.
//! Two steps compose in the Lawvere quantale: their distances add, and each
//! hole's count scales by the count of each hole that it passes through. The
//! census compares the composed bound with the fused cell's own reading; the
//! fused cells are the census's alone, and the lowering's cells stay as they
//! are.
//!
//! # Verdicts
//!
//! |verdict|meaning|
//! |---|---|
//! |exact|the composed bound equals the reading at every hole|
//! |looser|the composed bound lies above the reading at a hole|
//! |unsound|the composed bound lies below the reading at a hole|
//! |unread|a cell of the derivation has no reading for a hole that it matches|
//! |unfused|a match of the derivation fails|
//! |refused|the fusion refuses the overlap|
//! |outside|a composed distance lies past the distances that the quantale holds|
//! |unreplayed|the certificate of the fusion does not replay, with the cell and the wire that it writes unbound when one does|
//!
//! A block fuses at most [`FUSIONS`] composition overlaps; the census names
//! each block that has more ([`OverBudget`]).
//!
//! # References
//!
//! - `Gavazzo-2022-quantitative_metric_rewriting_abstract_nonexpansive_graded_systems`
//!   — exemplar: § 8's graded system, where a context scales a step's distance
//!   by its Lipschitz grade: the composition a row reports.
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: a step's
//!   distance, and a hole's count as its Lipschitz constant (§ quant-fusion).
//! - `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems`
//!   — newest: a reduction weighs the product of its steps' weights in a
//!   semiring. A row's composed bound is that product in the Lawvere quantale.
//! - `Hadzihasanovic-2023-higherdimensional_subdiagram_matching` — newest: a
//!   match is a convex subdiagram, and a firing pastes a new interior in its
//!   place. So each internal wire of a fused cell takes a fresh name.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;

use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::OverlapRefusal;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::Distance;
use gandr_theory_ordered_algebras::Lawvere;
use gandr_theory_ordered_algebras::OrderedSemiring as _;
use quenchant_shape::shape::Maybe;

use crate::format::LineColumn;

/// The most composition overlaps that a census fuses in one block.
pub const FUSIONS: usize = 1 << 10;

/// Whether a census fuses the composition overlaps of each block.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fusions
{
    /// The census reads each cell, and fuses nothing.
    Omitted,
    /// The census also fuses each composition overlap and composes its
    /// bound.
    Composed,
}

/// A count of occurrences: the Lipschitz constant of a hole, or how many
/// times a term holds a metavariable.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct HoleCount(u64);

impl HoleCount
{
    /// This count plus `other` times `scale`, saturating.
    ///
    /// # Specification
    /// trivial.
    const fn add_scaled(
        self,
        other: Self,
        scale: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0.saturating_mul(scale.0)))
    }

    /// This count less `other`, saturating at zero.
    ///
    /// # Specification
    /// trivial.
    const fn less(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_sub(other.0))
    }
}

impl From<u64> for HoleCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl From<HoleCount> for u64
{
    /// The number the count holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: HoleCount) -> Self
    {
        count.0
    }
}

/// A count for each metavariable: the census reading of a cell, or the
/// occurrences in a term.
type Reading = BTreeMap<MetaVar, HoleCount>;

/// How the census reads one fusion cell.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FusionVerdict
{
    /// The composed bound equals the fused cell's reading at every hole.
    Exact,
    /// The composed bound lies above the reading at the hole.
    Looser(MetaVar),
    /// The composed bound lies below the reading at the hole.
    Unsound(MetaVar),
    /// The cell has no reading for a hole that the derivation matches.
    Unread(CellId, MetaVar),
    /// A match of the derivation fails.
    Unfused,
    /// The fusion refuses the overlap.
    Refused(OverlapRefusal),
    /// A composed distance lies past the distances that the quantale holds.
    Outside,
    /// The fusion's certificate does not replay, and neither cell writes a
    /// wire that its left side does not bind.
    Unreplayed,
    /// The fusion's certificate does not replay, and the cell writes the wire
    /// with its right side and does not bind it with its left side.
    Unbound(CellId, MetaVar),
}

impl core::fmt::Display for FusionVerdict
{
    /// Names the verdict, and the cell and the hole that it reads.
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
            Self::Exact => f.write_str("exact"),
            Self::Looser(ref hole) => write!(f, "looser at {}", hole.hole()),
            Self::Unsound(ref hole) => write!(f, "unsound at {}", hole.hole()),
            Self::Unread(cell, ref hole) => {
                write!(
                    f,
                    "unread: cell {} has no count for {}",
                    usize::from(cell),
                    hole.hole()
                )
            },
            Self::Unfused => f.write_str("unfused"),
            Self::Refused(refusal) => write!(f, "refused: {refusal}"),
            Self::Outside => f.write_str("outside the distances"),
            Self::Unreplayed => f.write_str("unreplayed"),
            Self::Unbound(cell, ref hole) => write!(
                f,
                "unreplayed: cell {} writes {} unbound",
                usize::from(cell),
                hole.hole()
            ),
        }
    }
}

/// One fusion cell of a block that a source writes: the two cells that it
/// fuses, its composed bound and its verdict.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FusionRow
{
    /// The one-based line of the block's start.
    pub line: usize,
    /// The one-based column, in characters, of the same place.
    pub column: usize,
    /// The cell of the first step.
    pub left: CellId,
    /// The cell of the second step.
    pub right: CellId,
    /// The distance of the derivation's two steps, before the holes scale
    /// it: `∞` when the sum lies past the distances that the quantale holds.
    pub ticks: Distance,
    /// Each metavariable of the overlap's peak with its composed count, in
    /// metavariable order: empty when the derivation does not compose.
    pub holes: Vec<(MetaVar, HoleCount)>,
    /// The verdict.
    pub verdict: FusionVerdict,
}

impl core::fmt::Display for FusionRow
{
    /// The line and column, the two cells, the ticks, the verdict, then each
    /// hole and its composed count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes ``<line>:<column>: fusion of cell <left> then cell
    ///   <right>, distance <ticks>, <verdict>:`` and then each hole as ` <hole>
    ///   <count>`, separated by commas, or ` no holes` for a row without one,
    ///   and no line terminator. The distance is a whole number of ticks,
    ///   `m·2^e` for a distance that is not whole, or `∞`.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not the text
    ///   written, so the rendering is read off the census's witness rows.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fusions of a rule with itself and with another
    ///   rule, at one and two ticks, and holes counted one to nine times render
    ///   exactly; the verdicts other than `exact` are read in the corpus suite.
    /// - witness: `cells::tests::a_census_reads_each_hole_s_count_in_the_source_s_own_declarations`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}:{}: fusion of cell {} then cell {}, distance {}, {}:",
            self.line,
            self.column,
            usize::from(self.left),
            usize::from(self.right),
            Written(&self.ticks),
            self.verdict
        )?;
        if self.holes.is_empty() {
            return f.write_str(" no holes");
        }
        let mut separator = " ";
        for &(ref hole, count) in &self.holes {
            write!(f, "{separator}{} {}", hole.hole(), count.0)?;
            separator = ", ";
        }
        Ok(())
    }
}

/// A block whose composition overlaps pass the census's budget.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OverBudget
{
    /// The one-based line of the block's start.
    pub line: usize,
    /// The one-based column, in characters, of the same place.
    pub column: usize,
    /// How many composition overlaps the block has.
    pub overlaps: usize,
}

impl core::fmt::Display for OverBudget
{
    /// The line and column, the block's composition overlaps and the budget.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}:{}: {} composition overlaps, past the budget: the first {FUSIONS} fused",
            self.line, self.column, self.overlaps
        )
    }
}

/// A distance as the census writes it: a whole number, `m·2^e` for a
/// distance that is not whole, or `∞`.
#[repr(transparent)]
struct Written<'distance>(&'distance Distance);

impl core::fmt::Display for Written<'_>
{
    /// Writes the distance.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let Some(value) = self.0.value()
        else {
            return f.write_str("∞");
        };
        let mantissa = value.mantissa();
        let exponent = i32::from(value.exponent());
        let whole = u32::try_from(exponent).ok().and_then(|shift| {
            u64::try_from(&mantissa)
                .ok()?
                .checked_mul(1_u64.checked_shl(shift)?)
        });
        match whole {
            Some(whole) => write!(f, "{whole}"),
            None => write!(f, "{mantissa}·2^{exponent}"),
        }
    }
}

/// Fuse each composition overlap of the block `store`, which starts at `at`
/// in `own`, into `fused`, and push one row for each to `rows`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row for each of the block's first [`FUSIONS`] composition
///   overlaps, in [`enumerate_overlaps`]'s order, and one entry in `over` when
///   the block has more. `fused` holds the block's cells and the cells that the
///   fusions derive.
/// - fails: never; a fusion that does not compose, fuse or replay is a verdict.
/// - panics: none.
/// - intension: refills `fused` once for each block that has a composition
///   overlap, so its storage serves every block, and places a block in `own`
///   only when it has one.
/// - executable: none — the rows are the verdicts of each fusion and replay,
///   and a predicate would have to fuse and replay each overlap again.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus's fusions read 1,778 `exact` and three fusions
///   of a cell with itself that do not replay.
/// - witness: `tests::distances::each_fusion_cell_s_composed_bound_is_its_census_reading`
pub(super) fn fuse(
    store: &CellStore,
    (own, at): (SourceText<'_>, ByteOffset),
    fused: &mut CellStore,
    rows: &mut Vec<FusionRow>,
    over: &mut Vec<OverBudget>,
)
{
    let overlaps = enumerate_overlaps(store);
    let composition = |overlap: &&Overlap| overlap.kind == OverlapKind::Composition;
    let count = overlaps.iter().filter(composition).count();
    if count == 0 {
        return;
    }
    let LineColumn { line, column } = LineColumn::of(own, at);
    if count > FUSIONS {
        over.push(OverBudget {
            line,
            column,
            overlaps: count,
        });
    }
    fused.clone_from(store);
    let quantale = Lawvere::default();
    for overlap in overlaps.iter().filter(composition).take(FUSIONS) {
        let (Maybe::Present(left), Maybe::Present(right)) =
            (store.get(overlap.left), store.get(overlap.right))
        else {
            continue;
        };
        let ticks = derivation(&quantale, left, right);
        let (composed, verdict) = match compose(store, overlap) {
            Err(verdict) => (Reading::new(), verdict),
            Ok(composed) => {
                let verdict = match derive_fused(overlap, fused) {
                    Ok((id, certificate)) if bool::from(certificate.replay(fused)) => {
                        match fused.get(id) {
                            Maybe::Present(cell) => judge(&composed, (id, cell)),
                            Maybe::Absent(_) => FusionVerdict::Unreplayed,
                        }
                    },
                    Ok(_) => [(overlap.left, left), (overlap.right, right)]
                        .into_iter()
                        .find_map(|(id, cell)| cell.wires().first().map(|wire| (id, wire.clone())))
                        .map_or(FusionVerdict::Unreplayed, |(cell, wire)| {
                            FusionVerdict::Unbound(cell, wire)
                        }),
                    Err(refusal) => FusionVerdict::Refused(refusal),
                };
                (composed, verdict)
            },
        };
        let (ticks, verdict) = match ticks {
            Ok(ticks) => (ticks, verdict),
            Err(outside) => (Distance::INFINITY, outside),
        };
        rows.push(FusionRow {
            line,
            column,
            left: overlap.left,
            right: overlap.right,
            ticks,
            holes: composed.into_iter().collect(),
            verdict,
        });
    }
}

/// The census reading of `cell`: each hole with how many times the
/// contractum writes it.
///
/// # Specification
/// trivial.
fn reading(cell: &Cell) -> Reading
{
    cell.meta()
        .vars()
        .iter()
        .map(|hole| {
            (
                hole.var().clone(),
                HoleCount(u64::from(hole.contractum().occurrences())),
            )
        })
        .collect()
}

/// How many times `term` holds each metavariable.
///
/// # Specification
/// trivial.
fn occurrences(term: &CmdPat) -> Reading
{
    let mut counted = Reading::new();
    for var in SequentAlphabet::metavariables(term) {
        let entry = counted.entry(var).or_default();
        *entry = entry.add_scaled(HoleCount(1), HoleCount(1));
    }
    counted
}

/// The distance of one step of `cell`: one tick for a written rule, and none
/// for a cell that the elaboration adds.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`FusionVerdict::Outside`]: the quantale refuses the tick.
fn tick(cell: &Cell) -> Result<Distance, FusionVerdict>
{
    let ticks: i64 = match cell.provenance() {
        CellProvenance::SurfaceRule => 1,
        CellProvenance::MuMuTilde
        | CellProvenance::FrameDefining
        | CellProvenance::Eta(_)
        | CellProvenance::DerivedByCompletion => 0,
    };
    Distance::finite(Dyadic::from(ticks)).map_err(|_negative| FusionVerdict::Outside)
}

/// The distance of the two steps of `left` and then `right`: their ticks
/// added in the Lawvere quantale.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`FusionVerdict::Outside`]: the quantale refuses a tick or their sum.
fn derivation(
    quantale: &Lawvere,
    left: &Cell,
    right: &Cell,
) -> Result<Distance, FusionVerdict>
{
    quantale
        .multiply(&tick(left)?, &tick(right)?)
        .map_err(|_outside| FusionVerdict::Outside)
}

/// One tick scaled by `count`: the `count`-fold tensor in the Lawvere
/// quantale, and its unit for a count of zero.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`FusionVerdict::Outside`]: the scaled distance lies past the distances
/// that the quantale holds.
fn scaled(count: HoleCount) -> Result<Distance, FusionVerdict>
{
    let quantale = Lawvere::default();
    let unit = Distance::finite(Dyadic::from(1_i64)).map_err(|_negative| FusionVerdict::Outside)?;
    (0 .. count.0).try_fold(quantale.one(), |product, _| {
        quantale
            .multiply(&product, &unit)
            .map_err(|_outside| FusionVerdict::Outside)
    })
}

/// One step of the cell `id` at the subterm `redex`: each metavariable `x`
/// of a hole's image changes its composed count by the count of `x` in the
/// image times the hole's reading, less the count of `x` in the image.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`FusionVerdict::Unfused`] when the cell does not match `redex`, and
/// [`FusionVerdict::Unread`] when it has no reading for a hole it matches.
fn step(
    (id, cell): (CellId, &Cell),
    redex: &CmdPat,
    composed: &mut Reading,
) -> Result<(), FusionVerdict>
{
    let pattern = cell.lhs();
    let mut matched = Subst::default();
    if !bool::from(SequentAlphabet::match_cmd(pattern, redex, &mut matched)) {
        return Err(FusionVerdict::Unfused);
    }
    let read = reading(cell);
    let own = occurrences(pattern);
    for hole in own.keys() {
        let Some(&scale) = read.get(hole)
        else {
            return Err(FusionVerdict::Unread(id, hole.clone()));
        };
        // The pattern with this hole alone replaced by its image: each
        // metavariable's count there, less its count in the pattern, plus one
        // for the hole that the image replaces.
        let image = SequentAlphabet::apply_subst(
            &SequentAlphabet::restrict_subst(&matched, core::slice::from_ref(hole)),
            pattern,
        );
        for (var, within) in occurrences(&image) {
            let replaced = HoleCount(u64::from(var == *hole));
            let count = within
                .add_scaled(replaced, HoleCount(1))
                .less(own.get(&var).copied().unwrap_or_default());
            let entry = composed.entry(var).or_default();
            *entry = entry.add_scaled(count, scale).less(count);
        }
    }
    Ok(())
}

/// The composed count of each hole of the peak of `overlap`, through the
/// derivation's two steps over `store`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The verdict of the step that does not compose.
fn compose(
    store: &CellStore,
    overlap: &Overlap,
) -> Result<Reading, FusionVerdict>
{
    let (Maybe::Present(left), Maybe::Present(right)) =
        (store.get(overlap.left), store.get(overlap.right))
    else {
        return Err(FusionVerdict::Unfused);
    };
    let mut composed = occurrences(&overlap.peak);
    step((overlap.left, left), &overlap.peak, &mut composed)?;
    let middle = overlap.left_reduct(store).map_err(FusionVerdict::Refused)?;
    let Maybe::Present(redex) = SequentAlphabet::subterm_cmd_at(&middle, &overlap.seam)
    else {
        return Err(FusionVerdict::Unfused);
    };
    step((overlap.right, right), &redex, &mut composed)?;
    Ok(composed)
}

/// The verdict on the composed counts against the reading of the fused cell
/// `id`, each count scaling one tick in the Lawvere quantale. A wire of the
/// fused cell ([`Cell::wires`]) matches no subterm of the peak, so it bounds
/// nothing and the verdict does not read it.
///
/// # Specification
/// trivial.
fn judge(
    composed: &Reading,
    (id, fused): (CellId, &Cell),
) -> FusionVerdict
{
    let quantale = Lawvere::default();
    let read = reading(fused);
    for (var, &count) in composed {
        if count > HoleCount(0) && !read.contains_key(var) {
            return FusionVerdict::Unread(id, var.clone());
        }
    }
    let wires: BTreeSet<&MetaVar> = fused.wires().iter().collect();
    for (var, &reported) in read.iter().filter(|&(var, _)| !wires.contains(var)) {
        let (bound, report) = match (
            scaled(composed.get(var).copied().unwrap_or_default()),
            scaled(reported),
        ) {
            (Ok(bound), Ok(report)) => (bound, report),
            (Err(outside), _) | (_, Err(outside)) => return outside,
        };
        // The quantale's order reverses the numbers': the bound lies below
        // the report exactly when it is no smaller.
        if quantale.compare(&bound, &report) == Comparison::NotBelow {
            return FusionVerdict::Unsound(var.clone());
        }
        if quantale.compare(&report, &bound) == Comparison::NotBelow {
            return FusionVerdict::Looser(var.clone());
        }
    }
    FusionVerdict::Exact
}
