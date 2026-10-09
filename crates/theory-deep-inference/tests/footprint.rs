//! The polarized footprint measured against the shift guard: where the
//! instance-derived polarized test and the guard disagree, and why.
//!
//! Each pair is classified by both tests and by a third column the answer
//! needs: whether the pair actually commutes with its addresses as recorded.
//! The comparison has four cells:
//!
//! - **licensed by both**: a pair at incomparable positions whose cells do not
//!   overlap;
//! - **footprint only**: four rows with three causes: a read/read overlap at
//!   one address, a nested pair inside a carried frame, and two pairs the
//!   guard's cell-keyed overlap conjunct refuses although the instance is
//!   disjoint, one whose overlap family also carries a real composition seam
//!   and one whose family is nothing but metavariable seams;
//! - **guard only**: asserted empty over the whole table, the containment the
//!   "strictly larger" claim needs;
//! - **neither**: pairs that do not commute.
//!
//! Only the hole-seam row is attributable to the enumerator counting a
//! metavariable position as a seam; repairing that would stop the guard
//! refusing it, while the schematic row's genuine composition seam would keep
//! it refused. Addresses here move where the source's do not, so a rule that
//! relocates its frame reports the vacated addresses as written and is
//! refused, conservatively.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::ToyPos;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_deep_inference::FootprintIndependence;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_deep_inference::derive_shift_equivalence;
use gandr_theory_deep_inference::footprint_independence;
use gandr_theory_deep_inference::match_footprint;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::add_z;
use crate::fixture::c_cell;
use crate::fixture::f_cell;
use crate::fixture::fire;
use crate::fixture::g_cell;
use crate::fixture::stored;

/// Which of the two independence tests license a pair at one peak.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LicensedBy
{
    /// Both the shift guard and the polarized test license it.
    Both,
    /// Only the polarized test licenses it.
    FootprintOnly,
    /// Only the shift guard licenses it: the cell the containment claim says
    /// stays empty.
    GuardOnly,
    /// Neither test licenses it.
    Neither,
}

/// Whether the two recorded orders both fire from a peak and reach one term:
/// the ground truth the two verdicts are measured against.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Commutation
{
    /// Both orders fire and reach the same term.
    Commutes,
    /// An order fails to fire, or the two reach different terms.
    Diverges,
}

/// One row of the differential table.
struct Row
{
    /// The store the pair's cells live in.
    store: CellStore<ToyAlphabet>,
    /// The term both orders start from.
    peak: Toy,
    /// The application recorded first.
    left: CellApp<ToyAlphabet>,
    /// The application recorded second.
    right: CellApp<ToyAlphabet>,
    /// Which tests license the pair.
    licensed: LicensedBy,
    /// Whether the pair commutes as recorded.
    commutation: Commutation,
}

/// Addresses in a deterministic order, so a footprint class compares entrywise
/// whatever the alphabet's enumeration order.
///
/// # Specification
/// trivial.
fn sorted(mut positions: Vec<ToyPos>) -> Vec<ToyPos>
{
    positions.sort_by(|left, right| left.steps().cmp(right.steps()));
    positions
}

/// (bump-left): `Add(Zero, y) ~> Add(Succ(Zero), y)`.
///
/// The root `Add` is matched and left standing, the left child is rewritten,
/// and `y` is carried through untouched and unmoved: the three footprint
/// classes in one cell.
///
/// # Specification
/// trivial.
fn bump_left() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::zero(), Toy::var("y")),
        Toy::add(Toy::succ(Toy::zero()), Toy::var("y")),
    )
}

/// (bump-left-twice): `Add(Zero, y) ~> Add(Succ(Succ(Zero)), y)`.
///
/// # Specification
/// trivial.
fn bump_left_twice() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::zero(), Toy::var("y")),
        Toy::add(Toy::succ(Toy::succ(Toy::zero())), Toy::var("y")),
    )
}

/// (bump-right): `Add(y, Zero) ~> Add(y, Succ(Zero))`, bump-left's mirror.
///
/// # Specification
/// trivial.
fn bump_right() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::var("y"), Toy::zero()),
        Toy::add(Toy::var("y"), Toy::succ(Toy::zero())),
    )
}

/// (relocate): `Add(Zero, y) ~> Succ(y)`: the hole instance changes address.
///
/// # Specification
/// trivial.
fn relocate() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::add(Toy::zero(), Toy::var("y")),
        Toy::succ(Toy::var("y")),
    )
}

/// (peel): `Succ(Succ(x)) ~> Succ(x)`, a right-hand side exposing a hole.
///
/// # Specification
/// trivial.
fn peel() -> Cell<ToyAlphabet>
{
    toy_cell(
        Toy::succ(Toy::succ(Toy::var("x"))),
        Toy::succ(Toy::var("x")),
    )
}

/// Whether the two recorded orders both fire from `peak` and reach one term.
///
/// # Specification
/// trivial.
fn commutation(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    left: &CellApp<ToyAlphabet>,
    right: &CellApp<ToyAlphabet>,
) -> Commutation
{
    let forward = fire(store, peak, left).and_then(|term| fire(store, &term, right));
    let backward = fire(store, peak, right).and_then(|term| fire(store, &term, left));
    match (forward, backward) {
        | (Maybe::Present(first), Maybe::Present(second)) if first == second => {
            Commutation::Commutes
        },
        | _ => Commutation::Diverges,
    }
}

/// The polarized test's verdict for a pair at one peak, a step that is no
/// transition reading as a write at its own address.
///
/// # Specification
/// trivial.
fn polarized(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    left: &CellApp<ToyAlphabet>,
    right: &CellApp<ToyAlphabet>,
) -> FootprintIndependence<ToyAlphabet>
{
    let Ok(first) = match_footprint(store, peak, left)
    else {
        return FootprintIndependence::WriteWrite {
            position: left.at.clone(),
        };
    };
    let Ok(second) = match_footprint(store, peak, right)
    else {
        return FootprintIndependence::WriteWrite {
            position: right.at.clone(),
        };
    };
    footprint_independence(&first, &second)
}

/// Which of the two tests license a pair at one peak.
///
/// # Specification
/// trivial.
fn licensed_by(
    store: &CellStore<ToyAlphabet>,
    peak: &Toy,
    left: &CellApp<ToyAlphabet>,
    right: &CellApp<ToyAlphabet>,
) -> LicensedBy
{
    let guard = derive_shift_equivalence(store, peak, left, right).is_ok();
    let footprint = polarized(store, peak, left, right) == FootprintIndependence::Independent;
    match (guard, footprint) {
        | (true, true) => LicensedBy::Both,
        | (false, true) => LicensedBy::FootprintOnly,
        | (true, false) => LicensedBy::GuardOnly,
        | (false, false) => LicensedBy::Neither,
    }
}

/// One table row over a fresh store holding the two cells in order.
///
/// # Specification
/// trivial.
fn row(
    cells: (Cell<ToyAlphabet>, Cell<ToyAlphabet>),
    peak: Toy,
    at: (ToyPos, ToyPos),
    ruling: (LicensedBy, Commutation),
) -> Row
{
    let mut store = CellStore::new();
    let left = store.insert(cells.0);
    let right = store.insert(cells.1);
    Row {
        store,
        peak,
        left: CellApp {
            cell: left,
            at: at.0,
        },
        right: CellApp {
            cell: right,
            at: at.1,
        },
        licensed: ruling.0,
        commutation: ruling.1,
    }
}

/// The whole differential table, one row per fixture.
///
/// # Specification
/// trivial.
fn table() -> Vec<Row>
{
    vec![
        // Licensed by both: the cong2 pair.
        row(
            (f_cell(), g_cell()),
            Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero()))),
            (at![0], at![1]),
            (LicensedBy::Both, Commutation::Commutes),
        ),
        // Footprint only: a read/read overlap at one address.
        row(
            (bump_left(), bump_right()),
            Toy::add(Toy::zero(), Toy::zero()),
            (at![], at![]),
            (LicensedBy::FootprintOnly, Commutation::Commutes),
        ),
        // Footprint only: a redex inside a carried frame.
        row(
            (bump_left(), f_cell()),
            Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
            (at![], at![1]),
            (LicensedBy::FootprintOnly, Commutation::Commutes),
        ),
        // Footprint only: a cell-keyed overlap on a real composition seam the
        // instance does not realize.
        row(
            (add_z(), add_s()),
            Toy::add(
                Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
                Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
            ),
            (at![0], at![1]),
            (LicensedBy::FootprintOnly, Commutation::Commutes),
        ),
        // Footprint only: a cell-keyed overlap whose only seam is a hole.
        row(
            (peel(), c_cell()),
            Toy::add(
                Toy::succ(Toy::succ(Toy::zero())),
                Toy::add(Toy::zero(), Toy::zero()),
            ),
            (at![0], at![1]),
            (LicensedBy::FootprintOnly, Commutation::Commutes),
        ),
        // Neither: two rules at one address, one destroying what the other
        // matches and preserves.
        row(
            (c_cell(), bump_left()),
            Toy::add(Toy::zero(), Toy::zero()),
            (at![], at![]),
            (LicensedBy::Neither, Commutation::Diverges),
        ),
        // Neither: two rules rewriting one child from one root.
        row(
            (bump_left(), bump_left_twice()),
            Toy::add(Toy::zero(), Toy::zero()),
            (at![], at![]),
            (LicensedBy::Neither, Commutation::Diverges),
        ),
        // Neither: a relocating rule whose frame carries the other's redex.
        row(
            (relocate(), f_cell()),
            Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
            (at![], at![1]),
            (LicensedBy::Neither, Commutation::Diverges),
        ),
    ]
}

#[test]
fn a_ground_redex_writes_its_whole_match_image()
{
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::zero());
    let footprint = match_footprint(&store, &peak, &CellApp {
        cell: f,
        at: at![0],
    })
    .expect("f fires at the frame's left argument");
    assert_eq!(
        vec![at![0], at![0, 0]],
        sorted(footprint.written),
        "a ground rule matches and destroys every node it covers"
    );
    assert!(
        footprint.read.is_empty(),
        "nothing under a ground redex survives to be read-only"
    );
    assert!(
        footprint.framed.is_empty(),
        "and a ground rule has no hole instance to carry"
    );
}

#[test]
fn a_preserved_root_is_read_and_its_hole_is_framed()
{
    // The three classes separated pointwise by one application: the root `Add`
    // is matched and survives (read), the left child is rewritten (written),
    // and `y`'s instance is carried without being inspected (framed), so it is
    // not in the footprint at all.
    let mut store = CellStore::new();
    let bump = store.insert(bump_left());
    let peak = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let footprint = match_footprint(&store, &peak, &CellApp {
        cell: bump,
        at: at![],
    })
    .expect("bump-left fires at the root");
    assert_eq!(
        vec![at![]],
        sorted(footprint.read),
        "the matched root survives the rewrite as the same node"
    );
    assert_eq!(
        vec![at![0]],
        sorted(footprint.written),
        "and the child it matched as Zero does not"
    );
    assert_eq!(
        vec![at![1], at![1, 0]],
        sorted(footprint.framed),
        "the hole instance is carried, so it is frame and not footprint"
    );
}

#[test]
fn two_root_rules_sharing_only_a_read_node_are_independent()
{
    // Two applications at the same address. The guard refuses them at its
    // first conjunct, and they commute, because their only shared address is
    // one both of them merely read.
    let mut store = CellStore::new();
    let left_bump = store.insert(bump_left());
    let right_bump = store.insert(bump_right());
    let peak = Toy::add(Toy::zero(), Toy::zero());
    let left = CellApp {
        cell: left_bump,
        at: at![],
    };
    let right = CellApp {
        cell: right_bump,
        at: at![],
    };
    let first = match_footprint(&store, &peak, &left).expect("bump-left fires");
    let second = match_footprint(&store, &peak, &right).expect("bump-right fires");
    assert_eq!(
        vec![at![]],
        sorted(first.read.clone()),
        "bump-left reads the root"
    );
    assert_eq!(
        vec![at![]],
        sorted(second.read.clone()),
        "and so does bump-right, so the overlap is read/read"
    );
    assert_eq!(
        FootprintIndependence::Independent,
        footprint_independence(&first, &second),
        "read/read overlap is not a collision: the polarized reading's whole content"
    );
    assert_eq!(
        Err(ShiftObstruction::ComparablePositions {
            order: PositionOrder::Same
        }),
        derive_shift_equivalence(&store, &peak, &left, &right),
        "and the guard refuses at its first conjunct, one address being one position"
    );
    assert_eq!(
        Commutation::Commutes,
        commutation(&store, &peak, &left, &right),
        "the extra licence is earned: both orders reach one term"
    );
    let Maybe::Present(reached) =
        fire(&store, &peak, &left).and_then(|term| fire(&store, &term, &right))
    else {
        panic!("bump-left then bump-right fires");
    };
    assert_eq!(
        Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())),
        reached,
        "and the term they reach is the one both children bumped"
    );
}

#[test]
fn a_redex_inside_a_carried_frame_is_licensed()
{
    // A redex inside the substitution part of another redex commutes with it,
    // which the position conjunct cannot see and the polarized test sees,
    // because the frame is not in the footprint.
    let mut store = CellStore::new();
    let bump = store.insert(bump_left());
    let f = store.insert(f_cell());
    let peak = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let outer = CellApp {
        cell: bump,
        at: at![],
    };
    let inner = CellApp {
        cell: f,
        at: at![1],
    };
    assert_eq!(
        FootprintIndependence::Independent,
        polarized(&store, &peak, &outer, &inner),
        "the inner redex sits in the outer's frame, which the footprint excludes"
    );
    assert_eq!(
        Err(ShiftObstruction::ComparablePositions {
            order: PositionOrder::Encloses
        }),
        derive_shift_equivalence(&store, &peak, &outer, &inner),
        "the guard refuses the nesting without asking what the nesting is inside"
    );
    assert_eq!(
        Commutation::Commutes,
        commutation(&store, &peak, &outer, &inner),
        "and the pair commutes, addresses and all"
    );
}

#[test]
fn a_schematic_overlap_does_not_survive_as_an_instance_overlap()
{
    // The guard's overlap conjunct is cell-keyed: it asks whether the two rules
    // could ever interfere, over every instance. The polarized test is
    // instance-keyed. On a peak where the two matches are disjoint subtrees,
    // the schematic overlap buys nothing and the pair commutes.
    let mut store = CellStore::new();
    let zero_rule = store.insert(add_z());
    let succ_rule = store.insert(add_s());
    let peak = Toy::add(
        Toy::add(Toy::zero(), Toy::succ(Toy::zero())),
        Toy::add(Toy::succ(Toy::zero()), Toy::zero()),
    );
    let left = CellApp {
        cell: zero_rule,
        at: at![0],
    };
    let right = CellApp {
        cell: succ_rule,
        at: at![1],
    };
    let refusal = derive_shift_equivalence(&store, &peak, &left, &right)
        .expect_err("the cell pair overlaps, so the guard refuses");
    let ShiftObstruction::GenuineOverlap { overlap } = refusal
    else {
        panic!("the overlap conjunct is what refuses this pair");
    };
    assert_eq!(
        OverlapKind::Composition,
        overlap.kind,
        "the enumerator reports a composition seam for this pair"
    );
    // The seam the guard refuses at is add-Z's bare right-hand side, the
    // enumerator's metavariable seam, which would not survive its repair.
    let zero_cell = stored(&store, zero_rule);
    let succ_cell = stored(&store, succ_rule);
    assert_eq!(zero_rule, overlap.left, "the reported seam is add-Z's");
    assert_eq!(
        Maybe::Present(Toy::var("x")),
        ToyAlphabet::subterm_cmd_at(zero_cell.rhs(), &overlap.seam),
        "and it addresses a bare metavariable, as the hole-seam row's does"
    );
    // What separates this row from the hole-seam one: the pair's family also
    // carries a genuine composition seam, add-S's right-hand side running into
    // add-Z's left-hand side at a constructor position, so the refusal survives
    // an enumerator repair. Only the instance is disjoint.
    let genuine = overlaps_between((succ_rule, succ_cell), (zero_rule, zero_cell))
        .into_iter()
        .find(|candidate| {
            ToyAlphabet::subterm_cmd_at(succ_cell.rhs(), &candidate.seam)
                == Maybe::Present(Toy::add(Toy::var("m"), Toy::var("n")))
        })
        .expect("add-S's right-hand side runs into add-Z's left-hand side");
    assert_eq!(
        OverlapKind::Composition,
        genuine.kind,
        "that seam is a composition overlap and not a critical pair"
    );
    assert_eq!(
        FootprintIndependence::Independent,
        polarized(&store, &peak, &left, &right),
        "and this instance's two match images do not meet at any address"
    );
    assert_eq!(
        Commutation::Commutes,
        commutation(&store, &peak, &left, &right),
        "the pair commutes here"
    );
}

#[test]
fn a_hole_seam_refusal_is_the_enumerator_gap_and_not_polarization()
{
    // This row's guard refusal is the enumerator counting a metavariable
    // position as a composition seam, so it is not scored as a win for the
    // polarized reading. The assertions pin the seam, and the whole family, as
    // bare holes.
    let mut store = CellStore::new();
    let peel_rule = store.insert(peel());
    let ground = store.insert(c_cell());
    let peak = Toy::add(
        Toy::succ(Toy::succ(Toy::zero())),
        Toy::add(Toy::zero(), Toy::zero()),
    );
    let left = CellApp {
        cell: peel_rule,
        at: at![0],
    };
    let right = CellApp {
        cell: ground,
        at: at![1],
    };
    assert_eq!(
        PositionOrder::Incomparable,
        ToyAlphabet::position_order(&left.at, &right.at),
        "the first conjunct passes: the two redexes are disjoint subtrees"
    );
    let refusal = derive_shift_equivalence(&store, &peak, &left, &right)
        .expect_err("the enumerator reports the pair overlapping");
    let ShiftObstruction::GenuineOverlap { overlap } = refusal
    else {
        panic!("the overlap conjunct is what refuses this pair");
    };
    let peel_cell = stored(&store, overlap.left);
    assert_eq!(
        Maybe::Present(Toy::var("x")),
        ToyAlphabet::subterm_cmd_at(peel_cell.rhs(), &overlap.seam),
        "the seam addresses a bare metavariable, which critical-pair theory excludes"
    );
    // This row's whole family is that gap, which separates it from the
    // schematic row: repair the enumerator and the guard stops refusing this
    // pair, while the schematic pair stays refused.
    let ground_cell = stored(&store, ground);
    let mut family = overlaps_between((peel_rule, peel_cell), (ground, ground_cell));
    family.extend(overlaps_between(
        (ground, ground_cell),
        (peel_rule, peel_cell),
    ));
    assert!(!family.is_empty(), "the enumerator does report the pair");
    for candidate in &family {
        assert_eq!(
            Maybe::Present(Toy::var("x")),
            ToyAlphabet::subterm_cmd_at(stored(&store, candidate.left).rhs(), &candidate.seam),
            "every seam in this pair's family is the bare metavariable"
        );
    }
    assert_eq!(
        FootprintIndependence::Independent,
        polarized(&store, &peak, &left, &right),
        "the polarized test never consults the enumerator, so it is not affected"
    );
    assert_eq!(
        Commutation::Commutes,
        commutation(&store, &peak, &left, &right),
        "and the pair commutes"
    );
}

#[test]
fn a_rule_that_destroys_a_node_another_only_reads_is_refused()
{
    // Read/write is a collision even though read/read is not: bump-left
    // matches the root and leaves it standing, add-Z tears it down.
    let mut store = CellStore::new();
    let bump = store.insert(bump_left());
    let zero_rule = store.insert(add_z());
    let peak = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let reader = match_footprint(&store, &peak, &CellApp {
        cell: bump,
        at: at![],
    })
    .expect("bump-left fires at the root");
    let writer = match_footprint(&store, &peak, &CellApp {
        cell: zero_rule,
        at: at![],
    })
    .expect("add-Z fires at the root");
    assert_eq!(
        FootprintIndependence::ReadWrite { position: at![0] },
        footprint_independence(&reader, &writer),
        "bump-left rewrites the Zero add-Z matched and left standing"
    );
    assert_eq!(
        FootprintIndependence::ReadWrite { position: at![] },
        footprint_independence(&writer, &reader),
        "and add-Z tears down the root bump-left matched and left standing"
    );
}

#[test]
fn two_rules_rewriting_one_child_collide_on_writes()
{
    let mut store = CellStore::new();
    let once = store.insert(bump_left());
    let twice = store.insert(bump_left_twice());
    let peak = Toy::add(Toy::zero(), Toy::zero());
    let first = match_footprint(&store, &peak, &CellApp {
        cell: once,
        at: at![],
    })
    .expect("bump-left fires");
    let second = match_footprint(&store, &peak, &CellApp {
        cell: twice,
        at: at![],
    })
    .expect("bump-left-twice fires");
    assert_eq!(
        FootprintIndependence::WriteWrite { position: at![0] },
        footprint_independence(&first, &second),
        "two rules rewriting one child collide there, read/read root notwithstanding"
    );
}

#[test]
fn a_pair_colliding_several_ways_reports_the_earliest_address_it_scans()
{
    // Collisions are searched in the left footprint's `written` order, which
    // is the alphabet's own, so a pair colliding at every address of one match
    // image names the first of them rather than an arbitrary one.
    let mut store = CellStore::new();
    let ground = store.insert(c_cell());
    let peak = Toy::add(Toy::zero(), Toy::zero());
    let step = CellApp {
        cell: ground,
        at: at![],
    };
    let footprint = match_footprint(&store, &peak, &step).expect("c fires at the root");
    let enumerated = ToyAlphabet::command_positions(&peak);
    assert_eq!(
        3_usize,
        enumerated.len(),
        "the match image is the root and its two arguments"
    );
    assert_eq!(
        enumerated, footprint.written,
        "a ground rule writes its whole match image, in the alphabet's own enumeration order"
    );
    assert_eq!(
        FootprintIndependence::WriteWrite {
            position: enumerated[0].clone()
        },
        footprint_independence(&footprint, &footprint),
        "and the collision reported is the earliest address of that scan"
    );
}

#[test]
fn every_footprint_partitions_exactly_the_addresses_its_redex_covers()
{
    // The datum's shape claim over the whole fixture family: the three classes
    // are pairwise disjoint, cover the match image exactly (the redex root and
    // everything it encloses, nothing above it), and each comes out in the
    // alphabet's enumeration order.
    for fixture in table() {
        for step in [&fixture.left, &fixture.right] {
            let footprint = match_footprint(&fixture.store, &fixture.peak, step)
                .expect("every step the differential table records is a transition");
            assert_eq!(
                step.at, footprint.at,
                "the footprint is attached to the step that was fired"
            );
            let addresses = ToyAlphabet::command_positions(&fixture.peak);
            let covered = addresses
                .iter()
                .filter(|position| {
                    matches!(
                        ToyAlphabet::position_order(&step.at, position),
                        PositionOrder::Same | PositionOrder::Encloses
                    )
                })
                .cloned()
                .collect::<Vec<_>>();
            let mut classified = footprint.written.clone();
            classified.extend(footprint.read.iter().cloned());
            classified.extend(footprint.framed.iter().cloned());
            let mut seen: Vec<ToyPos> = Vec::new();
            for position in &classified {
                assert!(
                    !seen.contains(position),
                    "the three classes are disjoint, so each address is classified once"
                );
                seen.push(position.clone());
            }
            assert_eq!(
                sorted(covered),
                sorted(classified),
                "the classes cover the match image exactly"
            );
            for class in [&footprint.written, &footprint.read, &footprint.framed] {
                let enumerated = class
                    .iter()
                    .map(|position| addresses.iter().position(|candidate| candidate == position))
                    .collect::<Option<Vec<_>>>()
                    .expect("every classified address is one the alphabet enumerates");
                assert!(
                    enumerated.is_sorted_by(|earlier, later| earlier < later),
                    "each class keeps the alphabet's enumeration order"
                );
            }
        }
    }
}

#[test]
fn a_relocated_frame_is_refused_because_addresses_move()
{
    // The source's footprints range over machine addresses, which do not move;
    // a term position does. `relocate` carries its hole instance from address
    // [1] to address [0], so the footprint reports [1] as written and refuses,
    // conservatively, because the recorded schedule cannot be reordered. The
    // two redexes do commute once the inner one is re-addressed, and that
    // residual map is the debt an adoption inherits.
    let mut store = CellStore::new();
    let mover = store.insert(relocate());
    let f = store.insert(f_cell());
    let peak = Toy::add(Toy::zero(), Toy::succ(Toy::zero()));
    let outer = CellApp {
        cell: mover,
        at: at![],
    };
    let inner = CellApp {
        cell: f,
        at: at![1],
    };
    assert_eq!(
        FootprintIndependence::WriteWrite { position: at![1] },
        polarized(&store, &peak, &outer, &inner),
        "the vacated address counts as written, so the pair is refused"
    );
    assert_eq!(
        Commutation::Diverges,
        commutation(&store, &peak, &outer, &inner),
        "and the refusal is right: the recorded inner address is gone after the move"
    );
    let Maybe::Present(relocated) = fire(&store, &peak, &outer)
    else {
        panic!("the mover fires");
    };
    let Maybe::Present(inner_first) =
        fire(&store, &peak, &inner).and_then(|term| fire(&store, &term, &outer))
    else {
        panic!("f then the mover fires");
    };
    let Maybe::Present(outer_first) = fire(&store, &relocated, &CellApp {
        cell: f,
        at: at![0],
    })
    else {
        panic!("f fires at its residual");
    };
    assert_eq!(
        inner_first, outer_first,
        "the two derivations agree once the inner redex is tracked to its residual"
    );
}

#[test]
fn the_cong2_pair_is_licensed_by_both_tests()
{
    let mut store = CellStore::new();
    let f = store.insert(f_cell());
    let g = store.insert(g_cell());
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())));
    assert_eq!(
        LicensedBy::Both,
        licensed_by(
            &store,
            &peak,
            &CellApp {
                cell: f,
                at: at![0]
            },
            &CellApp {
                cell: g,
                at: at![1]
            }
        ),
        "the pair the guard was built for is licensed by the polarized test too"
    );
}

#[test]
fn the_polarized_test_refuses_a_pair_that_does_not_commute()
{
    let mut store = CellStore::new();
    let ground = store.insert(c_cell());
    let bump = store.insert(bump_left());
    let peak = Toy::add(Toy::zero(), Toy::zero());
    let left = CellApp {
        cell: ground,
        at: at![],
    };
    let right = CellApp {
        cell: bump,
        at: at![],
    };
    assert_eq!(
        LicensedBy::Neither,
        licensed_by(&store, &peak, &left, &right),
        "a pair at one address whose rules destroy each other's match is refused twice"
    );
    assert_eq!(
        Commutation::Diverges,
        commutation(&store, &peak, &left, &right),
        "and the refusals are right"
    );
}

#[test]
fn the_guard_licenses_nothing_the_polarized_test_refuses()
{
    // The containment the "strictly larger commuting class" claim needs: over
    // the whole table, no row is licensed by the guard alone.
    let rows = table();
    let guard_only = rows
        .iter()
        .filter(|fixture| {
            licensed_by(&fixture.store, &fixture.peak, &fixture.left, &fixture.right)
                == LicensedBy::GuardOnly
        })
        .count();
    assert_eq!(
        0_usize, guard_only,
        "no fixture is licensed by the guard alone"
    );
    assert_eq!(
        8_usize,
        rows.len(),
        "and the table is the one this suite documents"
    );
}

#[test]
fn every_row_of_the_differential_table_rules_as_recorded()
{
    let mut both = 0_usize;
    let mut footprint_only = 0_usize;
    let mut neither = 0_usize;
    for fixture in table() {
        let licensed = licensed_by(&fixture.store, &fixture.peak, &fixture.left, &fixture.right);
        assert_eq!(
            fixture.licensed, licensed,
            "each row is classified as recorded"
        );
        let commutes = commutation(&fixture.store, &fixture.peak, &fixture.left, &fixture.right);
        assert_eq!(
            fixture.commutation, commutes,
            "each row commutes as recorded"
        );
        match licensed {
            | LicensedBy::Both => {
                assert_eq!(
                    Commutation::Commutes,
                    commutes,
                    "a pair both tests license must commute"
                );
                both = both.saturating_add(1);
            },
            | LicensedBy::FootprintOnly => {
                assert_eq!(
                    Commutation::Commutes,
                    commutes,
                    "every extra licence the polarized test grants must be earned"
                );
                footprint_only = footprint_only.saturating_add(1);
            },
            | LicensedBy::GuardOnly => panic!("the containment claim says this cell is empty"),
            | LicensedBy::Neither => {
                neither = neither.saturating_add(1);
            },
        }
    }
    assert_eq!(1_usize, both, "one row is licensed by both tests");
    assert_eq!(
        4_usize, footprint_only,
        "four rows are licensed by the polarized test alone"
    );
    assert_eq!(3_usize, neither, "and three rows by neither");
}
