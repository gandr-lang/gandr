//! Probe 12 of the presented-spaces frame: the Euler characteristic of a face
//! poset, read from a Morse matching and from the Möbius function.
//!
//! A greedy Morse matching pairs a cell with a cell that covers it one rank
//! up, and it keeps the reversed cover graph acyclic. The cells it leaves
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

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Element;

use super::faces::Carrier;
use super::faces::Points;
use super::faces::corpus;
use super::faces::face_poset;
use super::faces::whole;

/// An Euler characteristic.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Euler(i64);

/// The cells of a poset as the counts read them: each cell's boundary as a
/// bit row, and its rank.
#[derive(Debug)]
struct Cells
{
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
fn cells(poset: &GradedPoset<Points>) -> Cells
{
    let count = usize::from(poset.count());
    let boundary = (0 .. count)
        .map(|cell| {
            u64::from(
                poset
                    .boundary(Element::from(cell))
                    .expect("a cell of the poset"),
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
    Cells { boundary, rank }
}

/// A cell, by its place in the poset.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CellIndex(usize);

impl Cells
{
    /// The cells in order of rank: a linear extension of the order.
    ///
    /// # Specification
    /// trivial.
    fn by_rank(&self) -> Vec<CellIndex>
    {
        let mut order: Vec<CellIndex> = (0 .. self.rank.len()).map(CellIndex).collect();
        order.sort_by_key(|&cell| self.rank.get(cell.0).copied().unwrap_or_default());
        order
    }

    /// Whether `upper` covers `lower` one rank up: `lower` lies in its
    /// boundary, nothing lies between them, and the ranks differ by one.
    ///
    /// # Specification
    /// trivial.
    fn covers(
        &self,
        lower: CellIndex,
        upper: CellIndex,
    ) -> Cover
    {
        let below = |cell: usize, set: u64| (set >> cell) & 1 == 1;
        let upper_boundary = self.boundary.get(upper.0).copied().unwrap_or_default();
        let between = (0 .. self.rank.len()).any(|middle| {
            below(middle, upper_boundary)
                && below(
                    lower.0,
                    self.boundary.get(middle).copied().unwrap_or_default(),
                )
        });
        let step = self
            .rank
            .get(lower.0)
            .copied()
            .unwrap_or_default()
            .saturating_add(1)
            == self.rank.get(upper.0).copied().unwrap_or_default();
        if below(lower.0, upper_boundary) && !between && step {
            Cover::OneUp
        }
        else {
            Cover::Not
        }
    }

    /// The modified cover graph of `matching` has a directed cycle: each
    /// cover points down, except a matched cover, which points up.
    ///
    /// # Specification
    /// trivial.
    fn cyclic(
        &self,
        matching: &[Option<CellIndex>],
    ) -> Cycle
    {
        let count = self.rank.len();
        let mut edges: Vec<Vec<usize>> = vec![Vec::new(); count];
        for upper in (0 .. count).map(CellIndex) {
            for lower in (0 .. count).map(CellIndex) {
                if self.covers(lower, upper) == Cover::Not {
                    continue;
                }
                let matched = matching.get(lower.0).copied().flatten() == Some(upper);
                let (from, to) = if matched {
                    (lower, upper)
                }
                else {
                    (upper, lower)
                };
                if let Some(row) = edges.get_mut(from.0) {
                    row.push(to.0);
                }
            }
        }
        // Each cell is white, grey while on the search path, or black once
        // left; a grey cell met again closes a cycle.
        let mut colour = vec![0_u8; count];
        let mut stack: Vec<(usize, usize)> = Vec::with_capacity(count);
        for start in 0 .. count {
            if colour.get(start).copied() != Some(0) {
                continue;
            }
            stack.push((start, 0));
            if let Some(slot) = colour.get_mut(start) {
                *slot = 1;
            }
            while let Some(&mut (node, ref mut next)) = stack.last_mut() {
                let row = edges.get(node).map_or(&[][..], Vec::as_slice);
                if let Some(&target) = row.get(*next) {
                    *next = next.saturating_add(1);
                    match colour.get(target).copied() {
                        Some(1) => return Cycle::Found,
                        Some(0) => {
                            if let Some(slot) = colour.get_mut(target) {
                                *slot = 1;
                            }
                            stack.push((target, 0));
                        },
                        _ => {},
                    }
                }
                else {
                    if let Some(slot) = colour.get_mut(node) {
                        *slot = 2;
                    }
                    let _ = stack.pop();
                }
            }
        }
        Cycle::None
    }

    /// A greedy acyclic matching: each cell in order of rank pairs with the
    /// first unmatched cell that covers it one rank up, when the pair keeps
    /// the modified cover graph acyclic.
    ///
    /// # Specification
    /// trivial.
    fn matching(&self) -> Vec<Option<CellIndex>>
    {
        let count = self.rank.len();
        let mut matching: Vec<Option<CellIndex>> = vec![None; count];
        let order = self.by_rank();
        for &lower in &order {
            if matching.get(lower.0).copied().flatten().is_some() {
                continue;
            }
            for &upper in &order {
                let free = matching.get(upper.0).copied().flatten().is_none();
                if !free || self.covers(lower, upper) == Cover::Not {
                    continue;
                }
                if let Some(slot) = matching.get_mut(lower.0) {
                    *slot = Some(upper);
                }
                if let Some(slot) = matching.get_mut(upper.0) {
                    *slot = Some(lower);
                }
                if self.cyclic(&matching) == Cycle::Found {
                    if let Some(slot) = matching.get_mut(lower.0) {
                        *slot = None;
                    }
                    if let Some(slot) = matching.get_mut(upper.0) {
                        *slot = None;
                    }
                }
                else {
                    break;
                }
            }
        }
        matching
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
        let matching = self.matching();
        let mut morse = 0_i64;
        let mut critical = 0_i64;
        for (cell, partner) in matching.iter().enumerate() {
            if partner.is_none() {
                morse =
                    morse.saturating_add(sign(self.rank.get(cell).copied().unwrap_or_default()));
                critical = critical.saturating_add(1);
            }
        }
        // μ(0̂, x) = −(μ(0̂, 0̂) + the sum of μ(0̂, y) over the cells y below x),
        // read in order of rank so each term below is final.
        let mut mu = vec![0_i64; self.rank.len()];
        for cell in self.by_rank() {
            let boundary = self.boundary.get(cell.0).copied().unwrap_or_default();
            let below: i64 = (0 .. self.rank.len())
                .filter(|&lower| (boundary >> lower) & 1 == 1)
                .map(|lower| mu.get(lower).copied().unwrap_or_default())
                .fold(0_i64, i64::saturating_add);
            if let Some(slot) = mu.get_mut(cell.0) {
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

/// Whether one cell covers another one rank up.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cover
{
    /// It does.
    OneUp,
    /// It does not.
    Not,
}

/// Whether a directed graph holds a cycle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cycle
{
    /// It does.
    Found,
    /// It does not.
    None,
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
    let posets = generated
        .iter()
        .map(|&(carrier, ref faces)| face_poset(carrier, faces))
        .chain(
            shapes
                .iter()
                .map(|shape| face_poset(shape.carrier, &shape.faces)),
        );
    let mut differ = 0_usize;
    for poset in posets {
        let read = cells(&poset);
        let counts = read.counts();
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
        if counts.boundaries == Boundaries::Spherical {
            assert_eq!(counts.morse, counts.mobius, "{read:?}");
        }
        else if counts.morse != counts.mobius {
            differ = differ.saturating_add(1);
        }
    }
    assert!(
        differ > 0,
        "some boundary is no sphere, and the counts part"
    );
    // The corpus shapes by hand: `Square` has the corner `tl`, the two sides
    // through it one rank up, the two other sides at rank zero, and the
    // whole square at rank two.
    let read: Vec<(Euler, Euler)> = shapes
        .iter()
        .map(|shape| {
            let counts = cells(&face_poset(shape.carrier, &shape.faces)).counts();
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
