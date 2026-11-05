//! Probe 14 of the presented-spaces frame: distances in the Lawvere quantale,
//! composed along the two-step derivation that each fusion cell replaces.
//!
//! A composition overlap fires one cell, and then a second cell at a command
//! position of the first cell's contractum. `derive_fused` makes the fused
//! cell of the two steps, with a certificate whose replay runs the two-step
//! derivation. The census reads, for each hole of a cell, how many times the
//! contractum writes it: its Lipschitz constant under the step. Over
//! non-expansive symbols, a step that writes a hole `n` times stretches a
//! distance `δ` between two instances of the hole to at most `n · δ`.
//!
//! In the Lawvere quantale the tensor is the sum. So the distance of a
//! derivation is the tensor of the distances of its steps, and a scale `n` is
//! the `n`-fold tensor. A written rule carries the distance of one tick, and
//! a cell that the elaboration adds carries none. For each hole of the fused
//! cell, the probe composes the counts of the two steps through the matches
//! of the derivation. That gives the bound of the derivation. The probe then
//! compares the bound with the census reading of the fused cell:
//!
//! |verdict|meaning|
//! |---|---|
//! |exact|the composed bound equals the reading at every hole|
//! |looser|the composed bound lies above the reading at a hole|
//! |unsound|the composed bound lies below the reading at a hole|
//! |unread|a cell of the derivation has no reading for a hole that it matches|
//! |unfused|a match of the derivation fails|
//! |refused|the fusion refuses the overlap|
//! |unreplayed|the certificate of the fusion does not replay|
//!
//! A cell whose right side writes a wire that its left side does not bind,
//! fused with itself, does not replay. The renaming of the second copy gives
//! the wire a new name, so the two paths reach two terms.
//!
//! The probe fuses at most [`FUSIONS`] composition overlaps in one block.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::HoleName;
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
use gandr_theory_ordered_algebras::check;
use quenchant_shape::shape::Maybe;

/// The most composition overlaps the probe fuses in one block.
const FUSIONS: usize = 1 << 10;

/// A count of occurrences: the Lipschitz constant of a hole, or how many
/// times a term holds a metavariable.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Count(u64);

impl Count
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

/// A count for each metavariable: the census reading of a cell, or the
/// occurrences in a term.
type Reading = BTreeMap<MetaVar, Count>;

/// How the probe reads one fusion cell.
#[derive(Debug, Eq, PartialEq)]
enum Verdict
{
    /// The composed bound equals the reading at every hole.
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
    /// The fusion's certificate does not replay: the cell and the hole its
    /// right side writes and its left side does not bind, if one does.
    Unreplayed(Option<(CellId, MetaVar)>),
}

/// One fusion cell: the block, its two steps, its bound and its verdict.
#[derive(Debug)]
struct Row
{
    /// The source that writes the block.
    path: PathBuf,
    /// The first line of the block.
    header: String,
    /// The cell of the first step.
    left: CellId,
    /// The cell of the second step.
    right: CellId,
    /// The distance of the derivation's steps, before the holes scale it.
    ticks: Distance,
    /// The composed count of each hole of the fused cell.
    composed: Reading,
    /// The verdict.
    verdict: Verdict,
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
                Count(u64::from(hole.contractum().occurrences())),
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
        *entry = entry.add_scaled(Count(1), Count(1));
    }
    counted
}

/// The distance of one step of `cell`: one tick for a written rule, and none
/// for a cell that the elaboration adds.
///
/// # Specification
/// trivial.
fn tick(cell: &Cell) -> Distance
{
    let ticks = match cell.provenance() {
        CellProvenance::SurfaceRule => 1,
        CellProvenance::MuMuTilde
        | CellProvenance::FrameDefining
        | CellProvenance::Eta(_)
        | CellProvenance::DerivedByCompletion => 0,
    };
    Distance::finite(Dyadic::from(ticks)).expect("a tick is not negative")
}

/// `distance` scaled by `count`: the `count`-fold tensor in the Lawvere
/// quantale, and its unit for a count of zero.
///
/// # Specification
/// trivial.
fn scaled(
    distance: &Distance,
    count: Count,
) -> Distance
{
    let quantale = Lawvere::default();
    (0 .. count.0).fold(quantale.one(), |product, _| {
        quantale
            .multiply(&product, distance)
            .expect("a scaled distance stays exact")
    })
}

/// One step of the cell `id` at the subterm `redex`: each metavariable `x`
/// of a hole's image changes its composed count by the count of `x` in the
/// image times the hole's reading, less the count of `x` in the image.
///
/// # Specification
/// trivial.
fn step(
    (id, cell): (CellId, &Cell),
    redex: &CmdPat,
    composed: &mut Reading,
) -> Result<(), Verdict>
{
    let pattern = cell.lhs();
    let mut matched = Subst::default();
    if !bool::from(SequentAlphabet::match_cmd(pattern, redex, &mut matched)) {
        return Err(Verdict::Unfused);
    }
    let read = reading(cell);
    let own = occurrences(pattern);
    for hole in own.keys() {
        let Some(&scale) = read.get(hole)
        else {
            return Err(Verdict::Unread(id, hole.clone()));
        };
        // The pattern with this hole alone replaced by its image: each
        // metavariable's count there, less its count in the pattern, plus one
        // for the hole that the image replaces.
        let image = SequentAlphabet::apply_subst(
            &SequentAlphabet::restrict_subst(&matched, core::slice::from_ref(hole)),
            pattern,
        );
        for (var, within) in occurrences(&image) {
            let replaced = Count(u64::from(var == *hole));
            let count = within
                .add_scaled(replaced, Count(1))
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
fn compose(
    store: &CellStore,
    overlap: &Overlap,
) -> Result<Reading, Verdict>
{
    let (Maybe::Present(left), Maybe::Present(right)) =
        (store.get(overlap.left), store.get(overlap.right))
    else {
        return Err(Verdict::Unfused);
    };
    let mut composed = occurrences(&overlap.peak);
    step((overlap.left, left), &overlap.peak, &mut composed)?;
    let middle = overlap.left_reduct(store).map_err(Verdict::Refused)?;
    let Maybe::Present(redex) = SequentAlphabet::subterm_cmd_at(&middle, &overlap.seam)
    else {
        return Err(Verdict::Unfused);
    };
    step((overlap.right, right), &redex, &mut composed)?;
    Ok(composed)
}

/// The verdict on the composed counts against the reading of the fused cell
/// `id`, each count scaling the distance `unit` in the Lawvere quantale.
///
/// # Specification
/// trivial.
fn judge(
    composed: &Reading,
    (id, fused): (CellId, &Cell),
    unit: &Distance,
) -> Verdict
{
    let quantale = Lawvere::default();
    let read = reading(fused);
    for (var, &count) in composed {
        if count > Count(0) && !read.contains_key(var) {
            return Verdict::Unread(id, var.clone());
        }
    }
    for (var, &reported) in &read {
        let bound = scaled(unit, composed.get(var).copied().unwrap_or_default());
        let report = scaled(unit, reported);
        // The quantale's order reverses the numbers': the bound lies below
        // the report exactly when it is no smaller.
        if quantale.compare(&bound, &report) == Comparison::NotBelow {
            return Verdict::Unsound(var.clone());
        }
        if quantale.compare(&report, &bound) == Comparison::NotBelow {
            return Verdict::Looser(var.clone());
        }
    }
    Verdict::Exact
}

/// The fusion cells of every corpus block, in path order and then in written
/// order, each read through its derivation, its certificate replayed.
///
/// # Specification
/// trivial.
fn probe() -> Vec<Row>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let unit = Distance::finite(Dyadic::from(1)).expect("one is not negative");
    let quantale = Lawvere::default();
    let mut lowerings = LoweringCount::default();
    let mut rows = Vec::new();
    // One store, refilled for each block, takes the fused cells.
    let mut fused = CellStore::new();
    for path in super::coincide::sources() {
        let text = std::fs::read_to_string(&path).expect("the source reads");
        let Lowered::Module { module, .. } =
            lower_source(&grammar, SourceText::from(text.as_str()), &mut lowerings)
                .unwrap_or_else(|fault| panic!("{}: {fault}", path.display()))
                .into_lowered()
        else {
            continue;
        };
        for declaration in &module.cells().declarations {
            let store = &declaration.store;
            let span = declaration.at.span;
            let header: String = text
                .get(usize::from(span.start()) .. usize::from(span.end()))
                .and_then(|written| written.lines().next())
                .unwrap_or_default()
                .into();
            fused.clone_from(store);
            let compositions = enumerate_overlaps(store)
                .into_iter()
                .filter(|overlap| overlap.kind == OverlapKind::Composition)
                .take(FUSIONS);
            for overlap in compositions {
                let (Maybe::Present(left), Maybe::Present(right)) =
                    (store.get(overlap.left), store.get(overlap.right))
                else {
                    continue;
                };
                let ticks = quantale
                    .multiply(&tick(left), &tick(right))
                    .expect("two ticks stay exact");
                let (composed, verdict) = match compose(store, &overlap) {
                    Err(verdict) => (Reading::new(), verdict),
                    Ok(composed) => {
                        let verdict = match derive_fused(&overlap, &mut fused) {
                            Ok((id, certificate)) if bool::from(certificate.replay(&fused)) => {
                                match fused.get(id) {
                                    Maybe::Present(cell) => judge(&composed, (id, cell), &unit),
                                    Maybe::Absent(_) => Verdict::Unreplayed(None),
                                }
                            },
                            Ok(_) => Verdict::Unreplayed(
                                fresh(left)
                                    .map(|var| (overlap.left, var))
                                    .or_else(|| fresh(right).map(|var| (overlap.right, var))),
                            ),
                            Err(refusal) => Verdict::Refused(refusal),
                        };
                        (composed, verdict)
                    },
                };
                rows.push(Row {
                    path: path.clone(),
                    header: header.clone(),
                    left: overlap.left,
                    right: overlap.right,
                    ticks,
                    composed,
                    verdict,
                });
            }
        }
    }
    rows
}

/// A metavariable that the right side of `cell` holds and its left side does
/// not bind.
///
/// # Specification
/// trivial.
fn fresh(cell: &Cell) -> Option<MetaVar>
{
    let bound = occurrences(cell.lhs());
    occurrences(cell.rhs())
        .into_keys()
        .find(|var| !bound.contains_key(var))
}

/// The composed count of the hole named `hole` in `row`.
///
/// # Specification
/// trivial.
fn hole_count(
    row: &Row,
    hole: &HoleName,
) -> Count
{
    row.composed
        .iter()
        .find(|&(var, _)| var.hole() == hole)
        .map(|(_, &count)| count)
        .unwrap_or_default()
}

#[test]
fn each_fusion_cell_s_composed_bound_is_its_census_reading()
{
    let rows = probe();
    let quantale = Lawvere::default();
    let unit = Distance::finite(Dyadic::from(1)).expect("one is not negative");
    // Each fusion whose certificate replays has a composed bound equal to
    // the census reading of its cell. Each other fusion fuses a cell with
    // itself, and that cell writes a wire that its left side does not bind.
    for row in &rows {
        match row.verdict {
            Verdict::Exact => {},
            Verdict::Unreplayed(Some((cell, _))) if row.left == cell && row.right == cell => {},
            ref other @ (Verdict::Looser(_)
            | Verdict::Unsound(_)
            | Verdict::Unread(..)
            | Verdict::Unfused
            | Verdict::Refused(_)
            | Verdict::Unreplayed(_)) => panic!(
                "{}: {}: the fusion of {:?} into {:?} reads {other:?}",
                row.path.display(),
                row.header,
                row.left,
                row.right
            ),
        }
    }
    // The circuit rule `cong1` wires `x′` between its two nodes, and its left
    // side does not bind `x′`. Fused with itself, it does not replay.
    let wire = HoleName::from("x′");
    assert!(
        rows.iter().any(|row| {
            row.path
                .ends_with(Path::new("model/circuit/circuit-rule-block.gandr"))
                && row.left == row.right
                && matches!(
                    row.verdict,
                    Verdict::Unreplayed(Some((_, ref fresh))) if *fresh.hole() == wire
                )
        }),
        "`cong1` fused with itself does not replay"
    );
    // `thrice` writes `t` three times. Fused with itself, it writes `t` nine
    // times in two ticks. Fused with `twice`, it writes `t` six times.
    let shrub = |left: usize, right: usize| {
        rows.iter()
            .find(|row| {
                row.path
                    .ends_with(Path::new("model/desc/occurrence-count.gandr"))
                    && row.left == CellId::from(left)
                    && row.right == CellId::from(right)
            })
            .unwrap_or_else(|| panic!("the shrubs fuse cell {left} into cell {right}"))
    };
    let two = Distance::finite(Dyadic::from(2)).expect("two is not negative");
    let t = HoleName::from("t");
    for (right, copies) in [(7_usize, Count(9)), (6, Count(6))] {
        let row = shrub(7, right);
        assert_eq!(row.verdict, Verdict::Exact, "{row:?}");
        assert_eq!(hole_count(row, &t), copies, "{row:?}");
        assert!(
            quantale.compare(&row.ticks, &two) == Comparison::Below
                && quantale.compare(&two, &row.ticks) == Comparison::Below,
            "two written rules make two ticks: {row:?}"
        );
    }
    // The quantale's laws hold on every distance a bound takes.
    let distances: std::collections::HashSet<Distance> = rows
        .iter()
        .flat_map(|row| {
            let scales = row.composed.values().map(|&count| scaled(&unit, count));
            core::iter::once(row.ticks.clone()).chain(scales)
        })
        .collect();
    assert!(
        check(&Lawvere::generated(distances.into_iter().collect())).is_ok(),
        "the Lawvere laws hold on the bounds' distances"
    );
}
