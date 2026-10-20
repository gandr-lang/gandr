use alloc::collections::BTreeSet;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt::Write as _;
use core::iter;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Agreement;
use super::Coding;
use super::Cover;
use super::CoverError;
use super::Crossing;
use super::PlacementError;
use super::Scope;
use super::SelectionError;
use super::Thinning;
use super::ThinningRef;
use super::Union;
use super::WordArena;
use super::check_cover;
use super::unselected;
use super::unstored;
use crate::context::BinderDepth;
use crate::syntax::Zone;

/// Both zones, in the order the carrier walks them.
const ZONES: [Zone; 2] = [Zone::Intuitionistic, Zone::Linear];

/// Every strictly ascending selection from `0 .. width`.
///
/// # Specification
/// - requires: `width` below 16, so the enumeration stays small.
/// - ensures: the `2^width` subsets of `0 .. width`, each ascending.
/// - provides: the exhaustive domain the cover rows range over.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the generator is the rows' domain; its count is checked
///   by the rank row, which walks every subset of a width.
/// - witness: `support::tests::rank_and_select_are_inverse`
#[spec(ensures: |ret| ret.len() == 1_usize << usize::from(width))]
fn subsets(width: BinderDepth) -> Vec<Vec<DeBruijnIndex>>
{
    let width = u32::try_from(usize::from(width)).expect("a small width");
    (0_u32 .. 1_u32 << width)
        .map(|mask| {
            (0_u32 .. width)
                .filter(|bit| mask & (1_u32 << bit) != 0)
                .map(DeBruijnIndex::from)
                .collect()
        })
        .collect()
}

/// The thinning of `intuitionistic` and `linear`, which ascend.
///
/// # Specification
/// - requires: each list strictly ascends.
/// - ensures: the thinning selecting them.
/// - panics: when a list does not strictly ascend.
///
/// # Adequacy
/// - hypothesis: L2 — a fixture constructor over the checked entry point.
/// - witness: `support::tests::selections_refuse_unordered_indices`
#[spec(ensures: |ret| ret.indices(Zone::Intuitionistic).eq(intuitionistic.iter().copied())
    && ret.indices(Zone::Linear).eq(linear.iter().copied()))]
fn thinning(
    intuitionistic: &[DeBruijnIndex],
    linear: &[DeBruijnIndex],
) -> Thinning
{
    Thinning::from_ascending(intuitionistic, linear).expect("fixture selections ascend")
}

/// The support a node naming `own` with one child `child` under `crossing`
/// has, computed independently of the carrier: the set union of `own` and
/// every child index past the crossing, lowered by it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: per zone, the ascending union described.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle restates the cover's union as set arithmetic,
///   sharing no code with [`Cover::of`].
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
#[spec(ensures: |ret| ZONES.into_iter().all(|zone| ret.contains_key(&zone)))]
fn reference_union(
    own: &[(Zone, DeBruijnIndex)],
    children: &[(&Thinning, Crossing)],
) -> alloc::collections::BTreeMap<Zone, BTreeSet<DeBruijnIndex>>
{
    let mut union = alloc::collections::BTreeMap::new();
    for zone in ZONES {
        let mut selected = BTreeSet::new();
        for &(own_zone, index) in own {
            if own_zone == zone {
                let _fresh = selected.insert(index);
            }
        }
        for &(child, crossing) in children {
            let crossed = u32::try_from(usize::from(crossing.depth(zone))).expect("small crossing");
            for index in child.indices(zone) {
                if let Some(outer) = u32::from(index).checked_sub(crossed) {
                    let _fresh = selected.insert(DeBruijnIndex::from(outer));
                }
            }
        }
        let _absent = union.insert(zone, selected);
    }
    union
}

/// The compact positions a node's own occurrences take in its support.
///
/// # Specification
/// - requires: every occurrence is selected by `support`.
/// - ensures: each occurrence's rank, in order.
/// - panics: when an occurrence is unselected.
///
/// # Adequacy
/// - hypothesis: L2 — a fixture adapter over [`Thinning::rank`].
/// - witness: `support::tests::placing_each_edge_recovers_its_child`
#[spec(ensures: |ret| ret.len() == own.len())]
fn ranks(
    support: &Thinning,
    own: &[(Zone, DeBruijnIndex)],
) -> Vec<(Zone, DeBruijnIndex)>
{
    own.iter()
        .map(|&(zone, index)| match support.rank(zone, index) {
            Maybe::Present(rank) => (zone, rank),
            Maybe::Absent(unselected::Absent::Unselected) => {
                panic!("an own occurrence is selected")
            },
        })
        .collect()
}

#[test]
fn placing_each_edge_recovers_its_child()
{
    // An ambient placement of the node that is not the identity: slot `k` of
    // the support stands at `2k + 1`, so an edge read by position rather than
    // by rank lands on the wrong index.
    let spread = |index: DeBruijnIndex| DeBruijnIndex::from(2 * u32::from(index) + 1);
    // One buffer per selection the passes below build, refilled per pass.
    let mut own: Vec<(Zone, DeBruijnIndex)> = Vec::new();
    let (mut ambient_intuitionistic, mut ambient_linear) = (Vec::new(), Vec::new());
    let (mut expected_intuitionistic, mut expected_linear) = (Vec::new(), Vec::new());
    for crossed_intuitionistic in 0_usize ..= 2 {
        for crossed_linear in 0_usize ..= 1 {
            let crossing = Crossing::new(
                BinderDepth::from(crossed_intuitionistic),
                BinderDepth::from(crossed_linear),
            );
            for child_intuitionistic in subsets(BinderDepth::from(3 + crossed_intuitionistic)) {
                for child_linear in subsets(BinderDepth::from(2 + crossed_linear)) {
                    let child = thinning(&child_intuitionistic, &child_linear);
                    for own_intuitionistic in subsets(BinderDepth::from(3_usize)) {
                        for own_linear in subsets(BinderDepth::from(2_usize)) {
                            own.clear();
                            own.extend(
                                own_intuitionistic
                                    .iter()
                                    .map(|&index| (Zone::Intuitionistic, index))
                                    .chain(own_linear.iter().map(|&index| (Zone::Linear, index))),
                            );
                            let cover =
                                Cover::of(own.iter().copied(), &iter::once((&child, crossing)));
                            let union = reference_union(&own, &[(&child, crossing)]);
                            for zone in ZONES {
                                assert!(union.get(&zone).is_some_and(|carried| {
                                    carried.iter().copied().eq(cover.support().indices(zone))
                                }));
                            }
                            let [ref edge] = *cover.edges()
                            else {
                                panic!("one edge per child");
                            };
                            assert_eq!(edge.scope(), child.scope());
                            assert_eq!(cover.support().place(edge, crossing), Ok(child.clone()));
                            assert_eq!(
                                check_cover(
                                    cover.support().scope(),
                                    ranks(cover.support(), &own),
                                    cover.edges(),
                                    iter::once((child.scope(), crossing)),
                                ),
                                Ok(())
                            );
                            ambient_intuitionistic.clear();
                            ambient_intuitionistic
                                .extend(cover.support().indices(Zone::Intuitionistic).map(spread));
                            ambient_linear.clear();
                            ambient_linear
                                .extend(cover.support().indices(Zone::Linear).map(spread));
                            let ambient = thinning(&ambient_intuitionistic, &ambient_linear);
                            let lift = |zone: Zone, index: DeBruijnIndex| {
                                let crossed = u32::try_from(usize::from(crossing.depth(zone)))
                                    .expect("small");
                                u32::from(index)
                                    .checked_sub(crossed)
                                    .map_or(index, |outer| {
                                        DeBruijnIndex::from(
                                            u32::from(spread(DeBruijnIndex::from(outer))) + crossed,
                                        )
                                    })
                            };
                            expected_intuitionistic.clear();
                            expected_intuitionistic.extend(
                                child_intuitionistic
                                    .iter()
                                    .map(|&index| lift(Zone::Intuitionistic, index)),
                            );
                            expected_linear.clear();
                            expected_linear.extend(
                                child_linear.iter().map(|&index| lift(Zone::Linear, index)),
                            );
                            let expected = thinning(&expected_intuitionistic, &expected_linear);
                            assert_eq!(ambient.place(edge, crossing), Ok(expected));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn a_cover_unions_its_children()
{
    let crossings = [(0_usize, 0_usize), (1, 0), (0, 1), (1, 1)].map(|(intuitionistic, linear)| {
        Crossing::new(BinderDepth::from(intuitionistic), BinderDepth::from(linear))
    });
    let mut children = Vec::new();
    for &crossing in &crossings {
        let wide =
            |zone: Zone, base: usize| BinderDepth::from(base + usize::from(crossing.depth(zone)));
        for intuitionistic in subsets(wide(Zone::Intuitionistic, 2)) {
            for linear in subsets(wide(Zone::Linear, 1)) {
                children.push((thinning(&intuitionistic, &linear), crossing));
            }
        }
    }
    for &(ref first, first_crossing) in &children {
        for &(ref second, second_crossing) in &children {
            let pair = [(first, first_crossing), (second, second_crossing)];
            let cover = Cover::of(iter::empty(), &pair.iter().copied());
            let union = reference_union(&[], &pair);
            for zone in ZONES {
                assert!(union.get(&zone).is_some_and(|carried| {
                    carried.iter().copied().eq(cover.support().indices(zone))
                }));
            }
            assert_eq!(cover.edges().len(), 2);
            for (edge, &(child, crossing)) in cover.edges().iter().zip(&pair) {
                assert_eq!(cover.support().place(edge, crossing).as_ref(), Ok(child));
            }
            assert_eq!(
                check_cover(
                    cover.support().scope(),
                    iter::empty(),
                    cover.edges(),
                    pair.iter()
                        .map(|&(child, crossing)| (child.scope(), crossing)),
                ),
                Ok(())
            );
        }
    }
}

#[test]
fn a_cover_refuses_every_forged_edge()
{
    let index = DeBruijnIndex::from;
    // A node whose two children each stand under one binder of either zone:
    // the first selects its local binders and the node's outer slot 0 of
    // both zones, the second outer slot 1 of both zones.
    let crossing = Crossing::new(BinderDepth::from(1_usize), BinderDepth::from(1_usize));
    let first = thinning(&[index(0), index(1)], &[index(0), index(1)]);
    let second = thinning(&[index(3)], &[index(3)]);
    let pair = [(&first, crossing), (&second, crossing)];
    let cover = Cover::of(iter::empty(), &pair.iter().copied());
    let scope = cover.support().scope();
    assert_eq!(
        scope,
        Scope::new(BinderDepth::from(2_usize), BinderDepth::from(2_usize))
    );
    let children = || {
        pair.iter()
            .map(|&(child, crossing)| (child.scope(), crossing))
    };
    assert_eq!(
        check_cover(scope, iter::empty(), cover.edges(), children()),
        Ok(())
    );

    let [ref first_edge, ref second_edge] = *cover.edges()
    else {
        panic!("two edges");
    };
    assert_eq!(
        check_cover(
            scope,
            iter::empty(),
            core::slice::from_ref(first_edge),
            children()
        ),
        Err(CoverError::Arity)
    );
    for zone in ZONES {
        let with = |edge: &Thinning, zone: Zone, slots: &[DeBruijnIndex]| match zone {
            Zone::Intuitionistic => {
                thinning(slots, &edge.indices(Zone::Linear).collect::<Vec<_>>())
            },
            Zone::Linear => thinning(
                &edge.indices(Zone::Intuitionistic).collect::<Vec<_>>(),
                slots,
            ),
        };
        // A widened edge: its child selects one slot fewer.
        let widened = with(first_edge, zone, &[index(0), index(1), index(2)]);
        assert_eq!(
            check_cover(
                scope,
                iter::empty(),
                &[widened, second_edge.clone()],
                children()
            ),
            Err(CoverError::Domain(zone))
        );
        // An edge past the scope: outer slot 3 of a two-slot scope.
        let beyond = with(second_edge, zone, &[index(4)]);
        assert_eq!(
            check_cover(
                scope,
                iter::empty(),
                &[first_edge.clone(), beyond],
                children()
            ),
            Err(CoverError::OutOfScope(zone))
        );
        // An own position past the scope.
        assert_eq!(
            check_cover(
                scope,
                iter::once((zone, index(2))),
                cover.edges(),
                children()
            ),
            Err(CoverError::OutOfScope(zone))
        );
        // A widened scope: slot 2 of the zone is selected by nothing.
        let wider = match zone {
            Zone::Intuitionistic => {
                Scope::new(BinderDepth::from(3_usize), BinderDepth::from(2_usize))
            },
            Zone::Linear => Scope::new(BinderDepth::from(2_usize), BinderDepth::from(3_usize)),
        };
        assert_eq!(
            check_cover(wider, iter::empty(), cover.edges(), children()),
            Err(CoverError::Unused(zone))
        );
        // The widened slot named by the node itself is covered again.
        assert_eq!(
            check_cover(
                wider,
                iter::once((zone, index(2))),
                cover.edges(),
                children()
            ),
            Ok(())
        );
        // A narrowed edge selects fewer slots than its child holds.
        let narrowed = with(second_edge, zone, &[]);
        assert_eq!(
            check_cover(
                scope,
                iter::empty(),
                &[first_edge.clone(), narrowed],
                children()
            ),
            Err(CoverError::Domain(zone))
        );
    }
}

#[test]
fn placement_reports_index_overflow()
{
    let ceiling = DeBruijnIndex::from(u32::MAX);
    let below = DeBruijnIndex::from(u32::MAX - 1);
    let one = BinderDepth::from(1_usize);
    for zone in ZONES {
        let crossing = Crossing::of(zone, one);
        let outer_slot = Thinning::leaf(zone, DeBruijnIndex::from(1_u32));
        let local_slot = Thinning::leaf(zone, DeBruijnIndex::from(0_u32));
        assert_eq!(
            Thinning::leaf(zone, below).place(&outer_slot, crossing),
            Ok(Thinning::leaf(zone, ceiling))
        );
        assert_eq!(
            Thinning::leaf(zone, ceiling).place(&outer_slot, crossing),
            Err(PlacementError::IndexOverflow)
        );
        assert_eq!(
            Thinning::leaf(zone, ceiling).place(
                &Thinning::leaf(zone, DeBruijnIndex::from(0_u32)),
                Crossing::default()
            ),
            Ok(Thinning::leaf(zone, ceiling))
        );
        assert_eq!(
            Thinning::leaf(zone, ceiling).place(&local_slot, crossing),
            Ok(Thinning::leaf(zone, DeBruijnIndex::from(0_u32)))
        );
        assert_eq!(
            Thinning::leaf(zone, ceiling)
                .place(&Thinning::leaf(zone, DeBruijnIndex::from(2_u32)), crossing),
            Err(PlacementError::OutOfScope(zone))
        );
    }
}

#[test]
fn rank_and_select_are_inverse()
{
    for zone in ZONES {
        for selected in subsets(BinderDepth::from(5_usize)) {
            let thinning = match zone {
                Zone::Intuitionistic => thinning(&selected, &[]),
                Zone::Linear => thinning(&[], &selected),
            };
            for raw in 0_u32 .. 6 {
                let index = DeBruijnIndex::from(raw);
                match selected.iter().position(|held| *held == index) {
                    Some(rank) => {
                        let rank = DeBruijnIndex::from(u32::try_from(rank).expect("small"));
                        assert_eq!(thinning.rank(zone, index), Maybe::Present(rank));
                        assert_eq!(thinning.select(zone, rank), Ok(index));
                    },
                    None => assert_eq!(
                        thinning.rank(zone, index),
                        Maybe::Absent(unselected::Absent::Unselected)
                    ),
                }
            }
            let width = DeBruijnIndex::from(u32::try_from(selected.len()).expect("small"));
            assert_eq!(
                thinning.select(zone, width),
                Err(PlacementError::OutOfScope(zone))
            );
        }
    }
}

#[test]
fn selections_refuse_unordered_indices()
{
    let index = DeBruijnIndex::from;
    let ascending = alloc::vec![index(0), index(2)];
    for (unordered, case) in [
        (alloc::vec![index(1), index(1)], "repeated"),
        (alloc::vec![index(2), index(0)], "descending"),
    ] {
        assert_eq!(
            Thinning::from_ascending(&unordered, &ascending),
            Err(SelectionError::Unordered(Zone::Intuitionistic)),
            "{case} intuitionistic"
        );
        assert_eq!(
            Thinning::from_ascending(&ascending, &unordered),
            Err(SelectionError::Unordered(Zone::Linear)),
            "{case} linear"
        );
        assert_eq!(
            Thinning::from_ascending(&unordered, &unordered),
            Err(SelectionError::Unordered(Zone::Intuitionistic)),
            "{case} both"
        );
    }
    let accepted = Thinning::from_ascending(&ascending, &ascending).expect("strictly ascending");
    assert!(
        accepted
            .indices(Zone::Intuitionistic)
            .eq(ascending.iter().copied())
    );
    assert!(accepted.indices(Zone::Linear).eq(ascending.iter().copied()));
}

#[test]
fn every_refusal_renders_its_rule()
{
    let rendered: BTreeSet<alloc::string::String> = [
        SelectionError::Unordered(Zone::Intuitionistic).to_string(),
        SelectionError::Unordered(Zone::Linear).to_string(),
        CoverError::Arity.to_string(),
        CoverError::Domain(Zone::Intuitionistic).to_string(),
        CoverError::Domain(Zone::Linear).to_string(),
        CoverError::OutOfScope(Zone::Intuitionistic).to_string(),
        CoverError::OutOfScope(Zone::Linear).to_string(),
        CoverError::Unused(Zone::Intuitionistic).to_string(),
        CoverError::Unused(Zone::Linear).to_string(),
        PlacementError::IndexOverflow.to_string(),
        PlacementError::OutOfScope(Zone::Intuitionistic).to_string(),
        PlacementError::OutOfScope(Zone::Linear).to_string(),
    ]
    .into_iter()
    .collect();
    assert_eq!(rendered.len(), 12);
}

/// Selections of every form: rows at each form's boundaries, and
/// pseudo-random ones whose gaps run from contiguous to millions of binders.
///
/// # Specification
/// - ensures: strictly ascending selections, the empty one first.
/// - provides: the domain the encoding rows range over.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the generator is the rows' domain; the boundary row
///   checks that it reaches every form.
/// - witness: `support::tests::one_encoding_per_selection`
/// - witness: `support::tests::the_mode_switches_at_its_boundaries`
#[spec(ensures: |ret| ret.first().is_some_and(Vec::is_empty)
    && ret.iter().all(|listed| listed.windows(2).all(|pair| pair.first() < pair.last())))]
fn selections() -> Vec<Vec<DeBruijnIndex>>
{
    let index = DeBruijnIndex::from;
    let mut out: Vec<Vec<DeBruijnIndex>> = alloc::vec![
        Vec::new(),
        alloc::vec![index(0)],
        alloc::vec![index(55)],
        alloc::vec![index(56)],
        alloc::vec![index(0), index(56)],
        (0 .. 56).map(index).collect(),
        (0 .. 57).map(index).collect(),
        (56 .. 120).map(index).collect(),
        (0 .. 2001).step_by(2).map(index).collect(),
        alloc::vec![index(1000), index(5000), index(9000)],
        alloc::vec![index(u32::MAX)],
        alloc::vec![index(0), index(u32::MAX)],
        (u32::MAX.wrapping_sub(3) ..= u32::MAX).map(index).collect(),
    ];
    let mut state = 0x9E37_79B9_7F4A_7C15_u64;
    for max_gap in [1_u64, 2, 3, 8, 40, 300, 5_000, 100_000] {
        for count in [3_usize, 40, 500] {
            let mut at = state.wrapping_rem(100);
            let mut listed = Vec::with_capacity(count);
            for _ in 0 .. count {
                listed.push(index(u32::try_from(at).expect("the gaps stay inside u32")));
                state ^= state.wrapping_shl(13);
                state ^= state.wrapping_shr(7);
                state ^= state.wrapping_shl(17);
                at = at
                    .wrapping_add(1)
                    .wrapping_add(state.checked_rem(max_gap).expect("every gap is positive"));
            }
            out.push(listed);
        }
    }
    out
}

/// A code's length in words, as the reference sizing counts it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Words(usize);

/// The form and length the encoder's rule gives `listed`, each form's length
/// summed from its fields.
///
/// # Specification
/// - ensures: the shortest code the selection admits — dense, a run when it is
///   contiguous, sparse while it holds at most `2^24` indices — dense on a tie
///   and run before sparse, with its length in words.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the rule restated over the forms' field widths, which the
///   boundary row checks against hand-computed sizes.
/// - witness: `support::tests::the_mode_switches_at_its_boundaries`
#[spec(ensures: |ret| ret.1.0 >= 1)]
fn sized(listed: &[DeBruijnIndex]) -> (Coding, Words)
{
    let words = |payload: u64| {
        let short = payload.saturating_add(8).div_ceil(64);
        if short <= 31 {
            short
        }
        else {
            payload.div_ceil(64).saturating_add(1)
        }
    };
    let (Some(&first), Some(&last)) = (listed.first(), listed.last())
    else {
        return (Coding::Dense, Words(1));
    };
    let count = u64::try_from(listed.len()).expect("a listed count fits");
    let (first, last) = (u64::from(u32::from(first)), u64::from(u32::from(last)));
    let universe = last.saturating_add(1);
    let mut best = (Coding::Dense, words(universe));
    let admitted = count <= 1_u64 << 24_u32;
    if admitted && last.saturating_sub(first).saturating_add(1) == count && best.1 > 1 {
        best = (Coding::Run, 1);
    }
    if admitted {
        let width = if universe <= count {
            0
        }
        else {
            universe.checked_div(count).map_or(0, u64::ilog2)
        };
        let sparse = words(
            30_u64
                .saturating_add(count.saturating_mul(u64::from(width)))
                .saturating_add(count)
                .saturating_add(last.wrapping_shr(width)),
        );
        if sparse < best.1 {
            best = (Coding::Sparse, sparse);
        }
    }
    (
        best.0,
        Words(usize::try_from(best.1).expect("a code's length fits")),
    )
}

#[test]
fn one_encoding_per_selection()
{
    let generated = selections();
    let mut built: Vec<Thinning> = Vec::new();
    let mut reading = alloc::string::String::new();
    for (position, intuitionistic) in generated.iter().enumerate() {
        let partner = generated
            .get(position.wrapping_mul(7).wrapping_rem(generated.len()))
            .expect("a partner row");
        for (int, lin) in [
            (intuitionistic, &Vec::new()),
            (&Vec::new(), intuitionistic),
            (intuitionistic, partner),
        ] {
            let held = thinning(int, lin);
            for (zone, listed) in [(Zone::Intuitionistic, int), (Zone::Linear, lin)] {
                reading.clear();
                reading
                    .write_fmt(format_args!("{zone:?} of {held:?}"))
                    .expect("a reading writes");
                assert_eq!(
                    held.indices(zone).len(),
                    listed.len(),
                    "{reading}: its length"
                );
                assert!(
                    held.indices(zone).eq(listed.iter().copied()),
                    "{reading}: ascending"
                );
                assert!(
                    held.indices(zone).rev().eq(listed.iter().rev().copied()),
                    "{reading}: descending"
                );
                for (rank, &named) in listed.iter().enumerate() {
                    let rank = DeBruijnIndex::from(u32::try_from(rank).expect("a small rank"));
                    assert_eq!(
                        held.rank(zone, named),
                        Maybe::Present(rank),
                        "{reading}: rank"
                    );
                    assert_eq!(held.select(zone, rank), Ok(named), "{reading}: select");
                }
                for unselected in [0_u32, 1, 56, 57, 1001, u32::MAX] {
                    let unselected = DeBruijnIndex::from(unselected);
                    if !listed.contains(&unselected) {
                        assert_eq!(
                            held.rank(zone, unselected),
                            Maybe::Absent(unselected::Absent::Unselected),
                            "{reading}: an unselected index ranks absent"
                        );
                    }
                }
                let cuts = listed.iter().flat_map(|&named| {
                    let named = u64::from(u32::from(named));
                    [named, named.saturating_add(1)]
                });
                for cut in iter::once(0_u64).chain(cuts.step_by(17)) {
                    let crossed = BinderDepth::from(usize::try_from(cut).expect("a cut fits"));
                    assert!(
                        held.outside(zone, crossed).eq(listed
                            .iter()
                            .copied()
                            .filter(|&named| u64::from(u32::from(named)) >= cut)),
                        "{reading}: cut past {cut}"
                    );
                }
            }
            assert_eq!(held.view().to_thinning(), held, "owned again");
            // Fed descending and twice over, the union is the same code.
            let mut union = Union::new();
            for (zone, listed) in [(Zone::Intuitionistic, int), (Zone::Linear, lin)] {
                for &named in listed.iter().rev().chain(listed.iter()) {
                    union.name(zone, named);
                }
            }
            assert_eq!(
                union.equals(held.view()),
                Agreement::Same,
                "the union agrees"
            );
            assert_eq!(union.finish(), held, "the union is the same code");
            built.push(held);
        }
    }
    // Distinct selections have distinct codes.
    for (position, held) in built.iter().enumerate() {
        for other in built.iter().skip(position.saturating_add(1)) {
            let same_selection = ZONES
                .into_iter()
                .all(|zone| held.indices(zone).eq(other.indices(zone)));
            assert_eq!(held == other, same_selection, "{held:?} against {other:?}");
        }
    }
}

#[test]
fn the_mode_switches_at_its_boundaries()
{
    let index = DeBruijnIndex::from;
    let every = |step: usize| (0_u32 .. 128).step_by(step).map(index).collect::<Vec<_>>();
    // Each row's form and length, sized by hand from the fields.
    for (listed, coding, words, reading) in [
        (
            alloc::vec![index(55)],
            Coding::Dense,
            1,
            "the last binder the word holds",
        ),
        (
            alloc::vec![index(56)],
            Coding::Run,
            1,
            "the first binder past it",
        ),
        (
            (0 .. 56).map(index).collect(),
            Coding::Dense,
            1,
            "a full word ties a run",
        ),
        (
            (0 .. 57).map(index).collect(),
            Coding::Run,
            1,
            "one binder more is a run",
        ),
        (
            (56 .. 120).map(index).collect(),
            Coding::Run,
            1,
            "a run past the word",
        ),
        (
            alloc::vec![index(0), index(56)],
            Coding::Sparse,
            1,
            "two indices a word apart",
        ),
        (
            alloc::vec![index(1000), index(5000), index(9000)],
            Coding::Sparse,
            2,
            "a deep sparse support",
        ),
        (every(2), Coding::Dense, 3, "every second binder of 128"),
        (every(4), Coding::Dense, 3, "every fourth ties sparse"),
        (every(8), Coding::Sparse, 2, "every eighth is sparse"),
        (
            (0 .. 2001).step_by(2).map(index).collect(),
            Coding::Dense,
            33,
            "a dense code past 31 words takes the long form",
        ),
    ] {
        assert_eq!(
            sized(&listed),
            (coding, Words(words)),
            "{reading}: the reference sizing"
        );
        for zone in ZONES {
            let (int, lin) = match zone {
                Zone::Intuitionistic => (listed.clone(), Vec::new()),
                Zone::Linear => (Vec::new(), listed.clone()),
            };
            let owned = thinning(&int, &lin);
            let held = owned.view();
            assert_eq!(held.coding(zone), coding, "{zone:?}: {reading}");
            assert_eq!(
                usize::from(held.words()),
                words,
                "{zone:?}: {reading}: words"
            );
        }
    }
    // Every generated selection takes the reference form, in either zone and
    // after a code in the other one.
    let mut reached = BTreeSet::new();
    for listed in selections() {
        let (coding, Words(words)) = sized(&listed);
        reached.insert(coding);
        let both = thinning(&[index(3)], &listed);
        let both = both.view();
        let expected_words = if listed.is_empty() {
            1
        }
        else {
            words.saturating_add(1)
        };
        assert_eq!(
            usize::from(both.words()),
            expected_words,
            "{listed:?} after a code"
        );
        let alone = thinning(&listed, &[]);
        let alone = alone.view();
        assert_eq!(alone.coding(Zone::Intuitionistic), coding, "{listed:?}");
        assert_eq!(usize::from(alone.words()), words, "{listed:?}: words");
        if !listed.is_empty() {
            assert_eq!(both.coding(Zone::Linear), coding, "{listed:?}: second");
        }
    }
    assert_eq!(
        reached,
        BTreeSet::from([Coding::Dense, Coding::Sparse, Coding::Run]),
        "the generator reaches every form"
    );
    // The empty selection is the empty dense code of the intuitionistic zone.
    let empty = Thinning::empty();
    assert_eq!(empty.view().coding(Zone::Intuitionistic), Coding::Dense);
    assert_eq!(empty.view().coding(Zone::Linear), Coding::Omitted);
    assert_eq!(usize::from(empty.view().words()), 1);
    assert_eq!(ThinningRef::empty(), empty.view());
    // A variable's support is one word wherever its binder stands.
    for zone in ZONES {
        for named in [0_u32, 55, 56, 1000, u32::MAX] {
            let leaf = ThinningRef::leaf(zone, index(named));
            let listed = alloc::vec![index(named)];
            let (int, lin) = match zone {
                Zone::Intuitionistic => (listed, Vec::new()),
                Zone::Linear => (Vec::new(), listed),
            };
            assert_eq!(leaf, thinning(&int, &lin).view(), "{zone:?} {named}");
            assert_eq!(usize::from(leaf.words()), 1, "{zone:?} {named}: one word");
            assert_eq!(
                Thinning::leaf(zone, index(named)).view(),
                leaf,
                "{zone:?} {named}"
            );
        }
    }
}

#[test]
fn union_is_canonical()
{
    let index = DeBruijnIndex::from;
    let beside = [index(1)];
    // One buffer per selection the passes below build, refilled per pass.
    let (mut lifted, mut moved) = (Vec::new(), Vec::new());
    for listed in selections() {
        for zone in ZONES {
            let other = match zone {
                Zone::Intuitionistic => Zone::Linear,
                Zone::Linear => Zone::Intuitionistic,
            };
            let (int, lin): (&[DeBruijnIndex], &[DeBruijnIndex]) = match zone {
                Zone::Intuitionistic => (&listed, &beside),
                Zone::Linear => (&beside, &listed),
            };
            let expected = thinning(int, lin);
            // Split between two children: one uncrossed, one standing under
            // `crossed` more binders, which selects every index raised past
            // them and binders of its own below them.
            let crossed = 3_u32;
            let half = listed.len().div_ceil(2);
            let (near, far) = listed.split_at(half);
            lifted.clear();
            lifted.extend(
                [index(0), index(2)].into_iter().chain(
                    far.iter()
                        .filter_map(|&named| u32::from(named).checked_add(crossed).map(index)),
                ),
            );
            if lifted.len() != far.len().saturating_add(2) {
                continue;
            }
            let near = thinning(near, &[]);
            let raised = thinning(&lifted, &[]);
            let (near, raised) = match zone {
                Zone::Intuitionistic => (near, raised),
                Zone::Linear => {
                    moved.clear();
                    moved.extend(near.indices(Zone::Intuitionistic));
                    let near = thinning(&[], &moved);
                    moved.clear();
                    moved.extend(raised.indices(Zone::Intuitionistic));
                    (near, thinning(&[], &moved))
                },
            };
            let depth = BinderDepth::from(usize::try_from(crossed).expect("small"));
            for order in [false, true] {
                let mut union = Union::new();
                if order {
                    union.child(raised.view(), Crossing::of(zone, depth));
                    union.name(other, index(1));
                }
                else {
                    union.name(other, index(1));
                    union.child(near.view(), Crossing::default());
                    union.child(raised.view(), Crossing::of(zone, depth));
                }
                union.child(near.view(), Crossing::default());
                assert_eq!(
                    union.equals(expected.view()),
                    Agreement::Same,
                    "{zone:?} {listed:?}: agrees"
                );
                assert_eq!(
                    union.finish(),
                    expected,
                    "{zone:?} {listed:?}: order {order}"
                );
            }
            assert_eq!(
                Thinning::covering(iter::once((other, index(1))), [
                    (&raised, Crossing::of(zone, depth)),
                    (&near, Crossing::default()),
                ]),
                expected,
                "{zone:?} {listed:?}: covering"
            );
        }
    }
    // An inline union that turns gathered keeps what it held.
    let mut union = Union::new();
    union.name(Zone::Intuitionistic, index(4));
    union.child(thinning(&[index(9)], &[]).view(), Crossing::default());
    union.name(Zone::Linear, index(0));
    union.name(Zone::Intuitionistic, index(4000));
    assert_eq!(
        union.finish(),
        thinning(&[index(4), index(9), index(4000)], &[index(0)])
    );
}

#[test]
fn a_stored_support_reads_back()
{
    let generated = selections();
    let (before, after) = generated.split_at(generated.len().div_ceil(2));
    let mut arena = WordArena::new();
    let store = |listed: &[DeBruijnIndex], arena: &mut WordArena| {
        let held = thinning(listed, &[DeBruijnIndex::from(0)]);
        let mark = arena.mark();
        let slot = arena.store(&held);
        assert_eq!(
            arena.mark() == mark,
            usize::from(held.view().words()) == 1,
            "{held:?}: only a wide code takes the arena's words"
        );
        let mut union = Union::new();
        for zone in ZONES {
            for named in held.indices(zone) {
                union.name(zone, named);
            }
        }
        let from_union = arena.store_union(union);
        assert_eq!(
            arena.read(from_union),
            arena.read(slot),
            "{held:?}: from a union"
        );
        (slot, held)
    };
    let kept: Vec<_> = before
        .iter()
        .map(|listed| store(listed, &mut arena))
        .collect();
    let mark = arena.mark();
    let dropped: Vec<_> = after
        .iter()
        .map(|listed| store(listed, &mut arena))
        .collect();
    for &(slot, ref held) in kept.iter().chain(&dropped) {
        assert_eq!(arena.read(slot), Maybe::Present(held.view()), "{held:?}");
    }
    arena.truncate(mark);
    for &(slot, ref held) in &kept {
        assert_eq!(
            arena.read(slot),
            Maybe::Present(held.view()),
            "{held:?}: kept"
        );
    }
    for &(slot, ref held) in &dropped {
        let expected = if usize::from(held.view().words()) == 1 {
            Maybe::Present(held.view())
        }
        else {
            Maybe::Absent(unstored::Absent::Unstored)
        };
        assert_eq!(arena.read(slot), expected, "{held:?}: truncated");
    }
}

#[test]
fn a_slot_unions_and_compares_as_its_support()
{
    let index = DeBruijnIndex::from;
    let depth = |binders: usize| BinderDepth::from(binders);
    let crossings = [
        Crossing::default(),
        Crossing::of(Zone::Intuitionistic, depth(1)),
        Crossing::of(Zone::Intuitionistic, depth(3)),
        Crossing::of(Zone::Linear, depth(1)),
    ];
    // Unions before the child: empty, holding one inline name, and gathered
    // by a linear name.
    let starts: [&[(Zone, u32)]; 3] = [&[], &[(Zone::Intuitionistic, 2)], &[(Zone::Linear, 0)]];
    let start = |names: &[(Zone, u32)]| {
        let mut union = Union::new();
        for &(zone, named) in names {
            union.name(zone, index(named));
        }
        union
    };
    let mut arena = WordArena::new();
    for listed in selections() {
        for held in [
            thinning(&listed, &[]),
            thinning(&[], &listed),
            thinning(&listed, &[index(0)]),
        ] {
            let slot = arena.store(&held);
            for names in starts {
                for crossing in crossings {
                    let mut by_view = start(names);
                    by_view.child(held.view(), crossing);
                    let mut by_slot = start(names);
                    by_slot.stored_child(slot, &arena, crossing);
                    assert_eq!(
                        by_slot.finish(),
                        by_view.finish(),
                        "{held:?} {names:?} {crossing:?}"
                    );
                }
                let mut same = start(names);
                same.child(held.view(), Crossing::default());
                let expected = same.equals(held.view());
                assert_eq!(
                    same.equals_stored(slot, &arena),
                    expected,
                    "{held:?} {names:?}"
                );
                let mut wider = start(names);
                wider.child(held.view(), Crossing::default());
                wider.name(Zone::Intuitionistic, index(70));
                assert_eq!(
                    wider.equals_stored(slot, &arena),
                    wider.equals(held.view()),
                    "{held:?} {names:?}: wider"
                );
            }
        }
    }
}

#[test]
fn outside_cuts_at_the_crossing()
{
    let index = DeBruijnIndex::from;
    for listed in [alloc::vec![index(0), index(1), index(3)], alloc::vec![
        index(0),
        index(1),
        index(3),
        index(100)
    ]] {
        let held = thinning(&listed, &listed);
        for zone in ZONES {
            for crossed in 0_u32 ..= 4 {
                let depth = BinderDepth::from(usize::try_from(crossed).expect("small"));
                let expected: Vec<DeBruijnIndex> = listed
                    .iter()
                    .copied()
                    .filter(|&named| u32::from(named) >= crossed)
                    .collect();
                let cut = held.outside(zone, depth);
                assert_eq!(
                    cut.len(),
                    expected.len(),
                    "{zone:?} past {crossed}: its length"
                );
                assert!(
                    cut.eq(expected.iter().copied()),
                    "{zone:?} past {crossed}: ascending"
                );
                assert!(
                    held.outside(zone, depth)
                        .rev()
                        .eq(expected.iter().rev().copied()),
                    "{zone:?} past {crossed}: descending"
                );
            }
        }
    }
}

#[test]
fn a_union_equals_exactly_its_finished_thinning()
{
    let index = DeBruijnIndex::from;
    for (listed, wider, narrower, reading) in [
        (
            alloc::vec![index(0), index(3)],
            alloc::vec![index(0), index(3), index(5)],
            alloc::vec![index(0)],
            "an inline union",
        ),
        (
            alloc::vec![index(0), index(3), index(100)],
            alloc::vec![index(0), index(3), index(100), index(101)],
            alloc::vec![index(0), index(100)],
            "a spilled union",
        ),
    ] {
        let mut union = Union::new();
        for &named in listed.iter().rev() {
            union.name(Zone::Intuitionistic, named);
            union.name(Zone::Linear, named);
        }
        let own = thinning(&listed, &listed);
        assert_eq!(
            Agreement::Same,
            union.equals(own.view()),
            "{reading}: its own thinning"
        );
        assert_eq!(
            Agreement::Different,
            union.equals(thinning(&wider, &listed).view()),
            "{reading}: an index more"
        );
        assert_eq!(
            Agreement::Different,
            union.equals(thinning(&listed, &narrower).view()),
            "{reading}: an index fewer"
        );
        assert_eq!(
            union.finish(),
            own,
            "{reading}: comparing left the union whole"
        );
        let mut reused = Union::new();
        for &named in &listed {
            reused.name(Zone::Linear, named);
        }
        reused.clear();
        assert_eq!(
            Agreement::Same,
            reused.equals(Thinning::empty().view()),
            "{reading}: a cleared union is empty"
        );
    }
}

#[test]
fn a_thinning_prints_its_indices_in_either_form()
{
    let index = DeBruijnIndex::from;
    for (selection, printed, reading) in [
        (
            thinning(&[index(0), index(3)], &[index(1)]),
            "Thinning { intuitionistic: [DeBruijnIndex(0), DeBruijnIndex(3)], linear: [DeBruijnIndex(1)] }",
            "an inline selection",
        ),
        (
            thinning(&[index(0), index(100)], &[index(1)]),
            "Thinning { intuitionistic: [DeBruijnIndex(0), DeBruijnIndex(100)], linear: [DeBruijnIndex(1)] }",
            "a sparse selection",
        ),
        (
            thinning(&[index(56)], &[index(1)]),
            "Thinning { intuitionistic: [DeBruijnIndex(56)], linear: [DeBruijnIndex(1)] }",
            "a run",
        ),
    ] {
        assert_eq!(alloc::format!("{selection:?}"), printed, "{reading}");
        assert_eq!(
            alloc::format!("{:?}", selection.view()),
            printed,
            "{reading}: in place"
        );
    }
}
