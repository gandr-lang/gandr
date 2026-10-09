//! Earned shift equivalence on the two-redex `cong2` body, whose two readings
//! are one composite.
//!
//! The body is two redex nodes whiskered into one `Add` frame. It runs over
//! the toy alphabet because a sequent term has exactly one command position
//! and so cannot carry two applications at incomparable positions; the
//! sequent-side refusals are pinned in the module's own unit tests.

use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_deep_inference::derive_shift_equivalence;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::add_z;
use crate::fixture::cong2_body;
use crate::fixture::cong2_pair;
use crate::fixture::cong2_store;
use crate::fixture::f_cell;
use crate::fixture::run;

/// The two rules the frame whiskers share no seam, so the enumerator's verdict
/// for the pair is the empty family in both orders.
#[test]
fn the_cong2_cell_pair_has_trivial_overlap()
{
    let (store, f, g) = cong2_store();
    let Maybe::Present(f_cell) = store.get(f)
    else {
        panic!("f is stored");
    };
    let Maybe::Present(g_cell) = store.get(g)
    else {
        panic!("g is stored");
    };
    assert!(
        overlaps_between((f, f_cell), (g, g_cell)).is_empty(),
        "f's right-hand side offers g no seam"
    );
    assert!(
        overlaps_between((g, g_cell), (f, f_cell)).is_empty(),
        "and g's offers f none either, so the pair is trivial in both orders"
    );
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        ToyAlphabet::convexity_discharge(&store),
        "and the store carries the discharge the third conjunct is skipped under"
    );
}

/// Incomparable positions, trivial overlap, and the discharge carried as a
/// warrant rather than swept for: the pair earns its witness.
#[test]
fn the_cong2_pair_earns_its_shift_equivalence_witness()
{
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let (first, second) = cong2_pair(f, g);
    assert_eq!(
        PositionOrder::Incomparable,
        ToyAlphabet::position_order(&first.at, &second.at),
        "the two redex nodes sit at the frame's two argument positions"
    );
    let witness = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect("disjoint positions, trivial overlap, discharge applies");
    assert_eq!(peak, witness.peak, "the witness records the body it spans");
    assert_eq!(
        Toy::add(Toy::zero(), Toy::zero()),
        witness.joins_at,
        "both readings reach one composite"
    );
    assert_eq!(
        ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        witness.convexity,
        "and the witness carries the warrant its convexity conjunct was skipped under"
    );
}

/// The identification is checked by replay, never granted by the guard alone.
#[test]
fn the_cong2_composite_replays_under_both_sequentializations()
{
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let (first, second) = cong2_pair(f, g);
    let witness = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect("the cong2 pair earns its witness");
    assert!(
        bool::from(witness.replay(&store)),
        "replay confirms the identification instead of the guard asserting it"
    );
    assert_eq!(
        witness.joins_at,
        run(&store, &peak, &witness.first_then_second()),
        "f then g reaches the composite"
    );
    assert_eq!(
        witness.joins_at,
        run(&store, &peak, &witness.second_then_first()),
        "and so does g then f"
    );
}

/// The replay check stays falsifiable: a composite neither reading reaches
/// fails it.
#[test]
fn a_retargeted_composite_no_longer_replays()
{
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let (first, second) = cong2_pair(f, g);
    let mut witness = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect("the cong2 pair earns its witness");
    witness.joins_at = Toy::zero();
    assert!(
        !bool::from(witness.replay(&store)),
        "a composite neither reading reaches fails replay, so the check is real"
    );
}

/// A pair whose two orders do reach one term is still refused, because the
/// cells overlap: the guard is a property of the cells, not a rediscovery that
/// these two happened to commute.
#[test]
fn an_overlapping_toy_pair_at_disjoint_positions_is_refused()
{
    let mut store = CellStore::new();
    let z = store.insert(add_z());
    let s = store.insert(add_s());
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    let first = CellApp {
        cell: z,
        at: at![0],
    };
    let second = CellApp {
        cell: s,
        at: at![1],
    };
    let forward = run(&store, &peak, &[first.clone(), second.clone()]);
    let backward = run(&store, &peak, &[second.clone(), first.clone()]);
    assert_eq!(
        forward, backward,
        "the two orders do reach one term at this instance"
    );
    let refusal = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect_err("and the pair is refused all the same");
    let ShiftObstruction::GenuineOverlap { overlap } = refusal
    else {
        panic!("the overlap conjunct is what refuses this pair");
    };
    assert_eq!(
        (z, s),
        (overlap.left, overlap.right),
        "the refusal carries an overlap of exactly this cell pair"
    );
    // The seam that makes the pair genuinely interfering is add-S's right-hand
    // side running into add-Z's left-hand side; the enumerator reports it in
    // the other order of the pair, which the guard also asks.
    let Maybe::Present(z_cell) = store.get(z)
    else {
        panic!("add-Z is stored");
    };
    let Maybe::Present(s_cell) = store.get(s)
    else {
        panic!("add-S is stored");
    };
    assert!(
        !overlaps_between((s, s_cell), (z, z_cell)).is_empty(),
        "add-S's right-hand side runs into add-Z's left-hand side at a seam"
    );
}

/// One application inside the other is not an adjacent pair.
#[test]
fn a_nested_toy_pair_is_refused()
{
    let (store, f, g) = cong2_store();
    let peak = cong2_body();
    let outer = CellApp {
        cell: g,
        at: at![1],
    };
    let inner = CellApp {
        cell: f,
        at: at![1, 0],
    };
    let refusal = derive_shift_equivalence(&store, &peak, &outer, &inner)
        .expect_err("one application inside the other is not an adjacent pair");
    assert_eq!(
        ShiftObstruction::ComparablePositions {
            order: PositionOrder::Encloses
        },
        refusal,
        "the position conjunct refuses the nesting"
    );
}

/// The per-query cost is linear, but the number of queries a canonical
/// schedule needs is not: five pairwise disjoint redexes scheduled in reverse
/// are bubbled into canonical order by adjacent transpositions, and every
/// transposition is one independence question.
#[test]
fn an_adjacent_transposition_schedule_asks_a_quadratic_number_of_questions()
{
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let redex = Toy::succ(Toy::zero());
    let peak = Toy::add(
        redex.clone(),
        Toy::add(
            redex.clone(),
            Toy::add(redex.clone(), Toy::add(redex.clone(), redex)),
        ),
    );
    let canonical: Vec<CellApp<ToyAlphabet>> = vec![
        CellApp {
            cell: f,
            at: at![0],
        },
        CellApp {
            cell: f,
            at: at![1, 0],
        },
        CellApp {
            cell: f,
            at: at![1, 1, 0],
        },
        CellApp {
            cell: f,
            at: at![1, 1, 1, 0],
        },
        CellApp {
            cell: f,
            at: at![1, 1, 1, 1],
        },
    ];
    let length = canonical.len();
    let reached = run(&store, &peak, &canonical);

    let mut schedule: Vec<CellApp<ToyAlphabet>> = canonical.iter().rev().cloned().collect();
    assert_eq!(
        reached,
        run(&store, &peak, &schedule),
        "the reversed schedule reaches the same term to begin with"
    );
    let mut questions = 0_usize;
    let mut settled = false;
    while !settled {
        settled = true;
        for index in 0 .. length.saturating_sub(1) {
            let next = index.saturating_add(1);
            let left = schedule[index].clone();
            let right = schedule[next].clone();
            if left.at.steps() <= right.at.steps() {
                continue;
            }
            let prefix = run(&store, &peak, &schedule[.. index]);
            derive_shift_equivalence(&store, &prefix, &left, &right)
                .expect("pairwise disjoint redexes earn the witness at every intermediate");
            questions = questions.saturating_add(1);
            schedule.swap(index, next);
            settled = false;
        }
    }

    assert_eq!(canonical, schedule, "the schedule reached canonical order");
    assert_eq!(
        reached,
        run(&store, &peak, &schedule),
        "and the identification held: the canonical schedule reaches the same term"
    );
    // Five steps replay in five rewrites; sorting them cost ten questions.
    assert_eq!(5_usize, length, "five steps");
    assert_eq!(
        10_usize, questions,
        "and ten independence questions, which is the reversed schedule's worst case"
    );
}

/// An unresolvable identifier is refused by name.
#[test]
fn a_pair_naming_an_unstored_cell_is_refused()
{
    let (store, f, _g) = cong2_store();
    let peak = cong2_body();
    let missing = CellId::from(7_usize);
    let refusal = derive_shift_equivalence(
        &store,
        &peak,
        &CellApp {
            cell: f,
            at: at![0],
        },
        &CellApp {
            cell: missing,
            at: at![1],
        },
    )
    .expect_err("an unresolvable identifier is refused");
    assert_eq!(
        ShiftObstruction::<ToyAlphabet>::UnknownCell { cell: missing },
        refusal,
        "the refusal names the identifier that resolved to nothing"
    );
}

/// A body whose right argument is not a `g`-redex: the guard passes and the
/// instance check declines, carrying the step.
#[test]
fn a_step_that_does_not_fire_carries_the_step()
{
    let (store, f, g) = cong2_store();
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let (first, second) = cong2_pair(f, g);
    let refusal = derive_shift_equivalence(&store, &peak, &first, &second)
        .expect_err("g has no redex at the frame's right argument");
    assert_eq!(
        ShiftObstruction::StepDoesNotFire {
            step: Box::new(second)
        },
        refusal,
        "the refusal carries the step that did not fire"
    );
}
