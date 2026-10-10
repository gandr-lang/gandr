//! The causal web compared colour by colour with the event order it was built
//! from, and its named refusals read through the public surface.

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_deep_inference::CausalWeb;
use gandr_theory_deep_inference::EventIndex;
use gandr_theory_deep_inference::EventOrder;
use gandr_theory_deep_inference::HomomorphismFrontier;
use gandr_theory_deep_inference::RefinementVerdict;
use gandr_theory_deep_inference::SliceStepCount;
use gandr_theory_deep_inference::WebRelation;
use gandr_theory_deep_inference::WebVertex;
use gandr_theory_deep_inference::causal_web;
use gandr_theory_deep_inference::event_order;
use gandr_theory_deep_inference::refines;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_z;
use crate::fixture::c_cell;
use crate::fixture::f_cell;

/// The order of `cell` fired at both arguments of `Add(Succ(Zero),
/// Succ(Zero))`, dropping instance-unit firings.
///
/// # Specification
/// - ensures: two events exactly when the cell changes `Succ(Zero)`, and no
///   events when that firing is an instance unit.
/// - panics: when the two steps do not replay, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — cells firing on Succ(Zero), used at its two disjoint
///   copies. One root firing predicts the non-unit event count; canonical keys
///   and independent colours distinguish dropping a real event or merging the
///   two positions.
/// - witness: `tests::causal_web::independent_tracelet_web_matches_canonical_event_order`
#[spec(captures: moved = {
    let input = Toy::succ(Toy::zero());
    matches!(gandr_theory_coherent_resolutions::rewrite_at(&cell, &input, &at![]),
        Maybe::Present(reached) if reached != input)
}, ensures: |output|
    usize::from(output.event_count()) == usize::from(moved).saturating_mul(2))]
fn two_event_order(cell: Cell<ToyAlphabet>) -> EventOrder<ToyAlphabet>
{
    let mut store = CellStore::new();
    let cell = store.insert(cell);
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let path = [CellApp { cell, at: at![0] }, CellApp { cell, at: at![1] }];
    event_order(&store, &peak, &path).expect("the two-event fixture replays")
}

/// The order of `cell` fired once at the root of `Succ(Zero)`.
///
/// # Specification
/// - ensures: one event exactly when the cell changes `Succ(Zero)`, and no
///   event for an instance-unit firing.
/// - panics: when the step does not replay, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L1 — a cell firing at the fixed root. A root rewrite predicts
///   whether the event survives; the cardinality frontier distinguishes this
///   one-event input from the two-event source.
/// - witness: `tests::causal_web::refusal_frontiers_remain_named_in_public_api`
#[spec(captures: moved = {
    let input = Toy::succ(Toy::zero());
    matches!(gandr_theory_coherent_resolutions::rewrite_at(&cell, &input, &at![]),
        Maybe::Present(reached) if reached != input)
}, ensures: |output|
    usize::from(output.event_count()) == usize::from(moved))]
fn one_event_order(cell: Cell<ToyAlphabet>) -> EventOrder<ToyAlphabet>
{
    let mut store = CellStore::new();
    let cell = store.insert(cell);
    let peak = Toy::succ(Toy::zero());
    let path = [CellApp { cell, at: at![] }];
    event_order(&store, &peak, &path).expect("the one-event fixture replays")
}

/// The order of (add-Z) fired twice at the root of `Add(Zero, Add(Zero,
/// Zero))`: the second step needs the first's result, so the two events are
/// dependent.
///
/// # Specification
/// - ensures: two events, with the second directly dependent on the first.
/// - panics: when the two steps do not replay, which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: L3 — two root add-Z firings. Event count and the directed
///   dependency observer distinguish a dropped repetition, independence or
///   reversed precedence; the projected web checks both colours.
/// - witness: `tests::causal_web::dependent_tracelet_web_matches_canonical_event_order`
#[spec(ensures: |output| usize::from(output.event_count()) == 2
    && bool::from(output.depends_directly(EventIndex::from(1), EventIndex::from(0))))]
fn dependent_order() -> EventOrder<ToyAlphabet>
{
    let mut store = CellStore::new();
    let cell = store.insert(add_z());
    let peak = Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::zero()));
    let path = [CellApp { cell, at: at![] }, CellApp { cell, at: at![] }];
    event_order(&store, &peak, &path).expect("the dependent fixture replays")
}

/// `Succ(Zero) ~> Succ(Succ(Zero))`: the same redex as (f) with a different
/// right-hand side, so its events carry different keys.
///
/// # Specification
/// trivial.
fn alternate_cell() -> Cell<ToyAlphabet>
{
    toy_cell(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())))
}

/// Assert that `web` holds `order`'s canonical keys and reads every ordered
/// pair of distinct vertices in the colour `order` decides.
///
/// # Specification
/// - ensures: the canonical key list and every ordered distinct pair agree.
/// - panics: when the web disagrees with the order on any key or pair.
///
/// # Adequacy
/// - hypothesis: L1 — a projected web and its source event order. Canonical
///   keys and all directed pair colours validate the correspondence;
///   independent, directly dependent and transitively dependent fixtures
///   separate reversed coordinates, lost ancestry and copied labels.
/// - witness: `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`
/// - witness: `tests::causal_web::independent_tracelet_web_matches_canonical_event_order`
/// - witness: `tests::causal_web::dependent_tracelet_web_matches_canonical_event_order`
#[spec(ensures: {
    let canonical = order.canonical_order();
    canonical.len() == web.events.len()
        && canonical.iter().enumerate().all(|(index, event)| match order.key(*event) {
            Maybe::Present(key) => web.events.get(index) == Some(&key),
            Maybe::Absent(_) => false,
        })
        && canonical.iter().enumerate().all(|(left_index, left)|
            canonical.iter().enumerate().all(|(right_index, right)| {
                left_index == right_index || {
                    let expected = if bool::from(order.precedes(*left, *right)) {
                        WebRelation::Precedes
                    } else if bool::from(order.precedes(*right, *left)) {
                        WebRelation::Follows
                    } else {
                        WebRelation::Independent
                    };
                    web.relation(WebVertex::from(left_index), WebVertex::from(right_index)) == expected
                }
            }))
})]
fn assert_web_matches_order(
    order: &EventOrder<ToyAlphabet>,
    web: &CausalWeb,
)
{
    let canonical = order.canonical_order();
    assert_eq!(canonical.len(), web.events.len(), "one vertex per event");
    for (vertex, event_index) in canonical.iter().copied().enumerate() {
        let Maybe::Present(key) = order.key(event_index)
        else {
            panic!("the canonical order names the order's own events");
        };
        assert_eq!(
            Maybe::Present(&key),
            web.event(WebVertex::from(vertex)),
            "each vertex carries its event's key"
        );
    }
    for (left_index, left) in canonical.iter().copied().enumerate() {
        for (right_index, right) in canonical.iter().copied().enumerate() {
            if left_index == right_index {
                continue;
            }
            let expected = if bool::from(order.precedes(left, right)) {
                WebRelation::Precedes
            }
            else if bool::from(order.precedes(right, left)) {
                WebRelation::Follows
            }
            else {
                WebRelation::Independent
            };
            assert_eq!(
                expected,
                web.relation(WebVertex::from(left_index), WebVertex::from(right_index)),
                "each pair reads the colour the order decides"
            );
        }
    }
}

#[test]
fn independent_tracelet_web_matches_canonical_event_order()
{
    let order = two_event_order(f_cell());
    let web = causal_web(&order);
    assert_web_matches_order(&order, &web);
    assert_eq!(
        WebRelation::Independent,
        web.relation(WebVertex::from(0_usize), WebVertex::from(1_usize)),
        "two applications at incomparable positions are white"
    );
    let RefinementVerdict::Refines { witness } = refines(&web, &web)
    else {
        panic!("an identical public web must refine itself");
    };
    assert_eq!(
        SliceStepCount::from(0_usize),
        witness.step_count(),
        "with the empty chain"
    );
}

#[test]
fn dependent_tracelet_web_matches_canonical_event_order()
{
    let order = dependent_order();
    let web = causal_web(&order);
    assert_web_matches_order(&order, &web);
    assert_eq!(
        WebRelation::Precedes,
        web.relation(WebVertex::from(0_usize), WebVertex::from(1_usize)),
        "the dependent pair is one green edge"
    );
    assert_eq!(
        WebRelation::Follows,
        web.relation(WebVertex::from(1_usize), WebVertex::from(0_usize)),
        "read from its head"
    );
}

#[test]
fn a_precedence_reached_only_through_an_intermediate_event_is_green()
{
    // Three events whose outer two are independent of each other and both
    // dependent on the middle one: (c) at `[0, 0]`, a duplicating rule at the
    // enclosing `[0]`, then (f) at `[0, 1]`, a position the duplication
    // filled. The first precedes the last only through the middle, so the web
    // must fold the middle event's ancestors rather than read direct edges.
    let mut store = CellStore::new();
    let collapse = store.insert(c_cell());
    let duplicate = store.insert(toy_cell(
        Toy::add(Toy::zero(), Toy::var("x")),
        Toy::add(Toy::var("x"), Toy::var("x")),
    ));
    let peel = store.insert(f_cell());
    let peak = Toy::add(
        Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::succ(Toy::zero())),
        Toy::zero(),
    );
    let path = [
        CellApp {
            cell: collapse,
            at: at![0, 0],
        },
        CellApp {
            cell: duplicate,
            at: at![0],
        },
        CellApp {
            cell: peel,
            at: at![0, 1],
        },
    ];
    let order = event_order(&store, &peak, &path).expect("the three-event fixture replays");
    let (first, last) = (EventIndex::from(0_usize), EventIndex::from(2_usize));
    assert!(
        !bool::from(order.depends_directly(last, first)),
        "the outer two events are independent of each other"
    );
    assert!(
        bool::from(order.precedes(first, last)),
        "and the first precedes the last through the middle one"
    );
    let web = causal_web(&order);
    assert_web_matches_order(&order, &web);
    assert_eq!(
        WebRelation::Precedes,
        web.relation(WebVertex::from(0_usize), WebVertex::from(2_usize)),
        "so the web carries the transitive green edge"
    );
}

#[test]
fn refusal_frontiers_remain_named_in_public_api()
{
    let same_cardinality_mismatch = causal_web(&two_event_order(alternate_cell()));
    let source = causal_web(&two_event_order(f_cell()));
    assert_eq!(
        RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::EdgeStrengtheningSimulation,
        },
        refines(&same_cardinality_mismatch, &source),
        "different labels over one vertex count need a correspondence"
    );
    let different_cardinality = causal_web(&one_event_order(f_cell()));
    assert_eq!(
        RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::OpenHDownHomomorphism,
        },
        refines(&different_cardinality, &source),
        "a different vertex count needs a homomorphism"
    );
    let malformed = CausalWeb {
        events: Box::default(),
        precedes: source.precedes.clone(),
    };
    assert_eq!(
        RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::MalformedWeb,
        },
        refines(&malformed, &source),
        "a web whose relation is not square over its events is refused"
    );
}
