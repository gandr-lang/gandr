//! The face poset of a shape, with its cells as data, read back from its
//! lattice of subcomplexes.
//!
//! Each face is a cell that holds its points as data. A cell's boundary is
//! the set of cells below it. A subcomplex is a set of cells that holds the
//! boundary of each of its cells. The suite computes the subcomplexes and
//! their join-irreducible members from their definitions, apart from the
//! crate and from Birkhoff's theorem. It checks that the crate's lattice is
//! the same, that the spectrum is the closures of the cells, and that the two
//! maps of the read-back carry each point to the cell whose closure it is.
//!
//! The face poset is the nonempty faces that a shape names and the whole
//! carrier. On the corpus shapes and on every family of faces over up to
//! three points, the spectrum gives the face poset back.

use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::Budget;
use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementSet;

use crate::faces::Carrier;
use crate::faces::Points;
use crate::faces::corpus;
use crate::faces::face_poset;
use crate::faces::square;

/// Room for every subcomplex of a face poset of up to eight cells.
const BUDGET: usize = 256;

/// A set of cells of one face poset, as a bit mask over the cells' indices.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Cells(u64);

impl Cells
{
    /// Whether every cell of `self` is a cell of `other`.
    ///
    /// # Specification
    /// trivial.
    fn within(
        self,
        other: Self,
    ) -> Comparison
    {
        if self.0 & !other.0 == 0 {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

/// The closure of each cell, from the inclusion of the cells' points: the
/// cell and every cell whose points it holds.
///
/// # Specification
/// trivial.
fn closures(cells: &[Points]) -> Vec<Cells>
{
    cells
        .iter()
        .map(|&upper| {
            Cells(
                cells
                    .iter()
                    .enumerate()
                    .filter(|&(_, &lower)| lower.within(upper) == Comparison::Below)
                    .fold(0_u64, |bits, (index, _)| {
                        let shift = u32::try_from(index).expect("a small index");
                        bits | 1_u64
                            .checked_shl(shift)
                            .expect("fewer cells than a word has bits")
                    }),
            )
        })
        .collect()
}

/// Every subcomplex: each set of cells that holds the closure of each of its
/// cells, in mask order.
///
/// # Specification
/// trivial.
fn subcomplexes(closures: &[Cells]) -> Vec<Cells>
{
    let width = u32::try_from(closures.len()).expect("a small complex");
    let count = 1_u64
        .checked_shl(width)
        .expect("fewer cells than a word has bits");
    (0 .. count)
        .map(Cells)
        .filter(|&set| {
            closures.iter().enumerate().all(|(index, &closure)| {
                let shift = u32::try_from(index).expect("a small index");
                set.0.checked_shr(shift).unwrap_or(0) & 1 == 0
                    || closure.within(set) == Comparison::Below
            })
        })
        .collect()
}

/// The join-irreducible members of `lattice`: each nonempty member that is
/// not the union of the members strictly below it, in mask order.
///
/// # Specification
/// trivial.
fn join_irreducibles(lattice: &[Cells]) -> Vec<Cells>
{
    lattice
        .iter()
        .copied()
        .filter(|&member| {
            let below = lattice
                .iter()
                .filter(|&&other| other != member && other.within(member) == Comparison::Below)
                .fold(0_u64, |bits, other| bits | other.0);
            member != Cells::default() && below != member.0
        })
        .collect()
}

/// How the lattice of subcomplexes of a face poset stands.
#[derive(Debug, Eq, PartialEq)]
struct Reading
{
    /// How many subcomplexes the face poset has.
    subcomplexes: usize,
    /// How many of them are join-irreducible.
    spectrum: usize,
}

/// Reads the face poset of `faces` over `carrier` back from its lattice of
/// subcomplexes through the crate, and checks every step against the
/// definitions.
///
/// # Specification
/// trivial.
fn read_back(
    carrier: Carrier,
    faces: &[Points],
) -> Reading
{
    let poset: GradedPoset<Points> = face_poset(carrier, faces);
    let cells = poset.cells();
    let closures = closures(cells);
    let lattice = subcomplexes(&closures);
    let spectrum = join_irreducibles(&lattice);
    let read = poset
        .read_back(Budget::from(BUDGET))
        .expect("a face poset reads back");
    let members: Vec<Cells> = read
        .subcomplexes()
        .members()
        .iter()
        .map(|&member| Cells(u64::from(member)))
        .collect();
    assert_eq!(members, lattice, "the subcomplexes of {faces:?}");
    let points: Vec<Cells> = read
        .spectrum()
        .points()
        .iter()
        .map(|&point| Cells(u64::from(point)))
        .collect();
    assert_eq!(points, spectrum, "the spectrum of {faces:?}");
    for (point, &cell) in read.to_cells().images().iter().enumerate() {
        let closure = poset
            .closure(cell)
            .expect("a cell of the poset")
            .meet(ElementSet::from(u64::MAX));
        assert_eq!(
            read.spectrum().points().get(point),
            Some(&closure),
            "point {point} of {faces:?} is the closure of {cell:?}"
        );
        assert_eq!(
            read.from_cells().images().get(usize::from(cell)),
            Some(&Element::from(point)),
            "the map from the cells inverts the map to them"
        );
    }
    for (lower, &below) in cells.iter().enumerate() {
        for (upper, &above) in cells.iter().enumerate() {
            assert_eq!(
                poset
                    .compare(Element::from(lower), Element::from(upper))
                    .expect("cells of the poset"),
                below.within(above),
                "the cells {below:?} and {above:?} of {faces:?}"
            );
        }
    }
    assert!(
        closures.iter().enumerate().all(|(cell, &closure)| {
            poset
                .closure(Element::from(cell))
                .map(|row| row.meet(ElementSet::from(u64::MAX)))
                == Ok(ElementSet::from(closure.0))
        }),
        "each closure is the cells whose points the cell holds"
    );
    Reading {
        subcomplexes: lattice.len(),
        spectrum: spectrum.len(),
    }
}

#[test]
fn square_has_twenty_one_subcomplexes_and_its_six_cells_as_spectrum()
{
    // The four sides, the corner `tl` and the whole square are the cells. A
    // subcomplex holding the left or the top side holds `tl`, so the left,
    // top and `tl` cells give five subcomplexes, the right and bottom sides
    // four, and the whole square one more.
    let square = square();
    assert_eq!(read_back(square.carrier, &square.faces), Reading {
        subcomplexes: 21,
        spectrum: 6,
    });
}

#[test]
fn every_corpus_shape_reads_its_face_poset_back_from_its_subcomplexes()
{
    // `Config` names two faces whose union is the carrier. As a cell, the
    // carrier is the top of its own closure, which is join-irreducible.
    let expected = [
        ("Two", 3_usize, 2_usize),
        ("Three", 3, 2),
        ("Config", 5, 3),
        ("Square", 21, 6),
    ];
    let shapes = corpus();
    assert_eq!(shapes.len(), expected.len(), "every corpus shape is read");
    for (shape, (name, subcomplexes, spectrum)) in shapes.iter().zip(expected) {
        assert!(shape.named.starts_with(name), "{}", shape.named);
        assert_eq!(
            read_back(shape.carrier, &shape.faces),
            Reading {
                subcomplexes,
                spectrum
            },
            "{}",
            shape.named
        );
    }
}

#[test]
fn every_small_face_family_reads_back_from_its_subcomplexes()
{
    // Every family of faces over a carrier of up to three points, 278
    // families: the round trip holds on each.
    let mut faces: Vec<Points> = Vec::new();
    let mut families = 0_usize;
    for size in 0 ..= 3_u32 {
        let carrier = Carrier(size);
        let masks = 1_u64.checked_shl(size).expect("a small carrier");
        let count = 1_u64
            .checked_shl(u32::try_from(masks).expect("a small family"))
            .expect("a family of at most eight faces");
        for family in 0 .. count {
            faces.clear();
            faces.extend(
                (0 .. masks)
                    .filter(|&mask| {
                        let shift = u32::try_from(mask).expect("a small mask");
                        family.checked_shr(shift).unwrap_or(0) & 1 == 1
                    })
                    .map(Points),
            );
            let reading = read_back(carrier, &faces);
            assert_eq!(
                reading.spectrum,
                face_poset(carrier, &faces).cells().len(),
                "{faces:?} over {carrier:?}"
            );
            families = families.saturating_add(1);
        }
    }
    assert_eq!(families, 278, "every family over up to three points");
}
