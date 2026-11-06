//! Probe 12 of the presented-spaces frame: the Euler characteristic of a face
//! poset, read from a Morse matching and from the Möbius function.
//!
//! The crate's greedy matching pairs a cell with a cell one rank up whose
//! boundary holds it, and it keeps the gradient acyclic. The cells it leaves
//! unpaired are critical. The first count is the sum of the critical cells,
//! each signed by the parity of its rank. The second count adjoins a bottom
//! `0̂` below every cell and reads the Möbius function: it is minus the sum of
//! `μ(0̂, x)` over the cells `x`. By Philip Hall's theorem, that count is the
//! Euler characteristic of the order complex of the poset.
//!
//! The two counts agree on each poset whose every boundary counts as a sphere
//! one rank down: each `μ(0̂, x)` is then `(−1)^(rank + 1)`. A face poset here
//! always holds the whole carrier as its top cell, so its order complex is a
//! cone and the Möbius count is one. The Morse count is the alternating count
//! of the cells by rank, and it parts from one where a boundary is no sphere.

use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::collapse;
use gandr_theory_discrete_morse::greedy;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementSet;

use super::faces::Carrier;
use super::faces::Points;
use super::faces::corpus;
use super::faces::face_poset;
use super::faces::whole;

/// An Euler characteristic.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Euler(i64);

/// The cells of a poset as the counts read them: the poset, each cell's
/// boundary as a bit row, and its rank.
#[derive(Debug)]
struct Cells<'poset>
{
    /// The poset the greedy matching reads.
    poset: &'poset GradedPoset<Points>,
    /// Each cell's boundary, one bit for each cell strictly below it.
    boundary: Vec<u64>,
    /// Each cell's rank.
    rank: Vec<usize>,
}

/// The two counts of one poset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Counts
{
    /// The critical cells of the greedy matching, signed by rank.
    morse: Euler,
    /// Minus the sum of the Möbius function from the adjoined bottom.
    mobius: Euler,
    /// The cells the matching leaves critical.
    critical: Euler,
    /// Whether every cell's boundary counts as a sphere one rank down.
    boundaries: Boundaries,
}

/// Whether every cell's boundary has the Möbius value of a sphere one rank
/// down.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Boundaries
{
    /// Every boundary does.
    Spherical,
    /// Some boundary does not.
    NotSpherical,
}

/// The cells of `poset`.
///
/// # Specification
/// trivial.
fn cells(poset: &GradedPoset<Points>) -> Cells<'_>
{
    let count = usize::from(poset.count());
    let boundary = (0 .. count)
        .map(|cell| {
            u64::from(
                poset
                    .boundary(Element::from(cell))
                    .expect("a cell of the poset")
                    .meet(ElementSet::from(u64::MAX)),
            )
        })
        .collect();
    let rank = (0 .. count)
        .map(|cell| {
            usize::from(
                poset
                    .rank(Element::from(cell))
                    .expect("a cell of the poset"),
            )
        })
        .collect();
    Cells {
        poset,
        boundary,
        rank,
    }
}

impl Cells<'_>
{
    /// The cells in order of rank: a linear extension of the order.
    ///
    /// # Specification
    /// trivial.
    fn by_rank(&self) -> Vec<Element>
    {
        let mut order: Vec<usize> = (0 .. self.rank.len()).collect();
        order.sort_by_key(|&cell| self.rank.get(cell).copied().unwrap_or_default());
        order.into_iter().map(Element::from).collect()
    }

    /// Both counts.
    ///
    /// # Specification
    /// trivial.
    fn counts(&self) -> Counts
    {
        let sign = |rank: usize| {
            if rank.is_multiple_of(2) {
                1_i64
            }
            else {
                -1_i64
            }
        };
        let order = self.by_rank();
        let mut complex = self.poset;
        let matching = greedy(&mut complex, &order).expect("the poset reads its faces");
        // The crate's check finds the greedy matching acyclic, with each
        // partner naming its cell back.
        let checked = collapse(
            &mut matching.on(&mut complex),
            &order,
            Budget::from(order.len()),
        )
        .expect("the check reads the poset");
        assert_eq!(checked.faults(), Faults::default(), "{self:?}");
        let mut morse = 0_i64;
        let mut critical = 0_i64;
        for (cell, class) in matching.cells().iter().zip(matching.classes()) {
            if *class == Class::Critical {
                let rank = self
                    .rank
                    .get(usize::from(*cell))
                    .copied()
                    .unwrap_or_default();
                morse = morse.saturating_add(sign(rank));
                critical = critical.saturating_add(1);
            }
        }
        // μ(0̂, x) = −(μ(0̂, 0̂) + the sum of μ(0̂, y) over the cells y below x),
        // read in order of rank so each term below is final.
        let mut mu = vec![0_i64; self.rank.len()];
        for cell in order.into_iter().map(usize::from) {
            let boundary = self.boundary.get(cell).copied().unwrap_or_default();
            let below: i64 = (0 .. self.rank.len())
                .filter(|&lower| (boundary >> lower) & 1 == 1)
                .map(|lower| mu.get(lower).copied().unwrap_or_default())
                .fold(0_i64, i64::saturating_add);
            if let Some(slot) = mu.get_mut(cell) {
                *slot = 0_i64.saturating_sub(1_i64.saturating_add(below));
            }
        }
        let mobius = 0_i64.saturating_sub(mu.iter().copied().fold(0_i64, i64::saturating_add));
        // A cell whose boundary is a sphere of one dimension less has
        // μ(0̂, x) = (−1)^(rank + 1), by Philip Hall's theorem.
        let spherical = mu
            .iter()
            .zip(&self.rank)
            .all(|(&value, &rank)| value == 0_i64.saturating_sub(sign(rank)));
        Counts {
            morse: Euler(morse),
            mobius: Euler(mobius),
            critical: Euler(critical),
            boundaries: if spherical {
                Boundaries::Spherical
            }
            else {
                Boundaries::NotSpherical
            },
        }
    }
}

/// Every face family over a carrier of one to three points: each set of the
/// nonempty faces short of the whole carrier, which the face poset adds.
///
/// # Specification
/// trivial.
fn families() -> Vec<(Carrier, Vec<Points>)>
{
    let mut families = Vec::new();
    for points in 1_u32 ..= 3 {
        let carrier = Carrier(points);
        let proper: Vec<Points> = (1 .. whole(carrier).0).map(Points).collect();
        for family in 0_u64 .. 1_u64 << proper.len() {
            let faces = proper
                .iter()
                .enumerate()
                .filter(|&(index, _)| (family >> index) & 1 == 1)
                .map(|(_, &face)| face)
                .collect();
            families.push((carrier, faces));
        }
    }
    families
}

#[test]
fn the_two_counts_agree_where_every_boundary_is_a_sphere()
{
    let generated = families();
    let shapes = corpus();
    let posets: Vec<GradedPoset<Points>> = generated
        .iter()
        .map(|&(carrier, ref faces)| face_poset(carrier, faces))
        .chain(
            shapes
                .iter()
                .map(|shape| face_poset(shape.carrier, &shape.faces)),
        )
        .collect();
    let (mut spherical, mut agree, mut differ) = (0_usize, 0_usize, 0_usize);
    for (index, poset) in posets.iter().enumerate() {
        let read = cells(poset);
        let counts = read.counts();
        let family = index < generated.len();
        // The whole carrier is a top cell, so the order complex is a cone,
        // and the Möbius count reads its Euler characteristic, one.
        assert_eq!(counts.mobius, Euler(1), "{read:?}");
        // Each matched pair spans one rank, so the critical cells keep the
        // alternating count of all the cells.
        let alternating = read
            .rank
            .iter()
            .map(|&rank| {
                if rank.is_multiple_of(2) {
                    1_i64
                }
                else {
                    -1_i64
                }
            })
            .fold(0_i64, i64::saturating_add);
        assert_eq!(counts.morse, Euler(alternating), "{read:?}");
        // The weak Morse inequality: at least as many critical cells as the
        // size of the Euler characteristic.
        assert!(
            counts.critical >= Euler(counts.morse.0.saturating_abs()),
            "{read:?}"
        );
        if counts.boundaries == Boundaries::Spherical {
            assert_eq!(counts.morse, counts.mobius, "{read:?}");
        }
        if !family {
            continue;
        }
        if counts.boundaries == Boundaries::Spherical {
            spherical = spherical.saturating_add(1);
        }
        else if counts.morse == counts.mobius {
            agree = agree.saturating_add(1);
        }
        else {
            differ = differ.saturating_add(1);
        }
    }
    // Over the 69 face families, the counts agree on the 14 whose boundaries
    // are spheres and on 18 of the 55 others. They part on 37.
    assert_eq!((spherical, agree, differ), (14, 18, 37));
    // The corpus shapes by hand: `Square` has the corner `tl`, the two sides
    // through it one rank up, the two other sides at rank zero, and the
    // whole square at rank two.
    let read: Vec<(Euler, Euler)> = shapes
        .iter()
        .map(|shape| {
            let poset = face_poset(shape.carrier, &shape.faces);
            let counts = cells(&poset).counts();
            (counts.morse, counts.mobius)
        })
        .collect();
    assert_eq!(read, [
        (Euler(0), Euler(1)),
        (Euler(0), Euler(1)),
        (Euler(1), Euler(1)),
        (Euler(2), Euler(1)),
    ]);
}
