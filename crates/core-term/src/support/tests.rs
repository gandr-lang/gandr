use alloc::collections::BTreeSet;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::iter;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Cover;
use super::CoverError;
use super::Crossing;
use super::PlacementError;
use super::Scope;
use super::SelectionError;
use super::Thinning;
use super::check_cover;
use super::unselected;
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
#[spec(ensures: |ret| ret.indices(Zone::Intuitionistic) == intuitionistic && ret.indices(Zone::Linear) == linear)]
fn thinning(
    intuitionistic: &[DeBruijnIndex],
    linear: &[DeBruijnIndex],
) -> Thinning
{
    Thinning::from_ascending(intuitionistic.to_vec(), linear.to_vec())
        .expect("fixture selections ascend")
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
            for &index in child.indices(zone) {
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
                            let own: Vec<(Zone, DeBruijnIndex)> = own_intuitionistic
                                .iter()
                                .map(|&index| (Zone::Intuitionistic, index))
                                .chain(own_linear.iter().map(|&index| (Zone::Linear, index)))
                                .collect();
                            let cover =
                                Cover::of(own.iter().copied(), &iter::once((&child, crossing)));
                            let union = reference_union(&own, &[(&child, crossing)]);
                            for zone in ZONES {
                                let carried: BTreeSet<DeBruijnIndex> =
                                    cover.support().indices(zone).iter().copied().collect();
                                assert_eq!(union.get(&zone), Some(&carried));
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
                            let ambient = thinning(
                                &cover
                                    .support()
                                    .indices(Zone::Intuitionistic)
                                    .iter()
                                    .copied()
                                    .map(spread)
                                    .collect::<Vec<_>>(),
                                &cover
                                    .support()
                                    .indices(Zone::Linear)
                                    .iter()
                                    .copied()
                                    .map(spread)
                                    .collect::<Vec<_>>(),
                            );
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
                            let expected = thinning(
                                &child_intuitionistic
                                    .iter()
                                    .map(|&index| lift(Zone::Intuitionistic, index))
                                    .collect::<Vec<_>>(),
                                &child_linear
                                    .iter()
                                    .map(|&index| lift(Zone::Linear, index))
                                    .collect::<Vec<_>>(),
                            );
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
    let crossings: Vec<Crossing> = [(0_usize, 0_usize), (1, 0), (0, 1), (1, 1)]
        .into_iter()
        .map(|(intuitionistic, linear)| {
            Crossing::new(BinderDepth::from(intuitionistic), BinderDepth::from(linear))
        })
        .collect();
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
                let carried: BTreeSet<DeBruijnIndex> =
                    cover.support().indices(zone).iter().copied().collect();
                assert_eq!(union.get(&zone), Some(&carried));
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
            Zone::Intuitionistic => thinning(slots, edge.indices(Zone::Linear)),
            Zone::Linear => thinning(edge.indices(Zone::Intuitionistic), slots),
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
            Thinning::from_ascending(unordered.clone(), ascending.clone()),
            Err(SelectionError::Unordered(Zone::Intuitionistic)),
            "{case} intuitionistic"
        );
        assert_eq!(
            Thinning::from_ascending(ascending.clone(), unordered.clone()),
            Err(SelectionError::Unordered(Zone::Linear)),
            "{case} linear"
        );
        assert_eq!(
            Thinning::from_ascending(unordered.clone(), unordered),
            Err(SelectionError::Unordered(Zone::Intuitionistic)),
            "{case} both"
        );
    }
    let accepted =
        Thinning::from_ascending(ascending.clone(), ascending.clone()).expect("strictly ascending");
    assert_eq!(accepted.indices(Zone::Intuitionistic), ascending.as_slice());
    assert_eq!(accepted.indices(Zone::Linear), ascending.as_slice());
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
