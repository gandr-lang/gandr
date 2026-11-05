//! The face poset of a shape, with its cells as data, read back from its
//! lattice of subcomplexes.
//!
//! The spectrum suite reads the faces of a shape as sets of points. The
//! lattice they generate has the least face of each point as its spectrum. A
//! face that is the union of smaller faces is then not in the spectrum, so the
//! spectrum differs from the face poset on `Config` and `Square`.
//!
//! Here each face is a cell that holds its points as data. A cell's boundary
//! is the set of cells below it. A subcomplex is a set of cells that holds the
//! boundary of each of its cells. The subcomplexes form a finite distributive
//! lattice under union and intersection. The suite computes the
//! join-irreducible elements of that lattice from their definition: a
//! nonempty subcomplex that is not the union of the subcomplexes strictly
//! below it. Each of them is the boundary of one cell together with the cell.
//! The crate's entailment orders the cells, and that order is the order of the
//! spectrum. So the spectrum gives the face poset back on every corpus shape.
//!
//! The face poset is the one the spectrum suite compares: the nonempty faces
//! that a shape names and the whole carrier.

use gandr_theory_shapes::Membership;
use gandr_theory_shapes::PointCount;

use crate::carriers::Mask;
use crate::spectrum::Family;
use crate::spectrum::Verdict;
use crate::spectrum::corpus;
use crate::spectrum::entails;
use crate::spectrum::included;
use crate::spectrum::whole;

/// A set of cells of one face poset, as a bit mask over the cells' indices.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Cells(u64);

/// The place of a cell in its face poset.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CellIndex(usize);

impl Cells
{
    /// The set that holds exactly the cell at `index`.
    ///
    /// # Specification
    /// trivial.
    fn single(index: CellIndex) -> Self
    {
        let shift = u32::try_from(index.0).expect("a small index");
        Self(
            1_u64
                .checked_shl(shift)
                .expect("fewer cells than a word has bits"),
        )
    }

    /// Whether every cell of `self` is a cell of `other`.
    ///
    /// # Specification
    /// trivial.
    fn within(
        self,
        other: Self,
    ) -> Membership
    {
        if self.0 & !other.0 == 0 {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }
}

/// A face poset whose cells hold their points as data.
#[derive(Debug)]
struct Complex
{
    /// The carrier the cells' points lie in.
    carrier: PointCount,
    /// Each cell's points, in mask order. The index of a cell is its place
    /// here.
    cells: Vec<Mask>,
    /// The closure of each cell: the cell and its boundary, by index.
    closures: Vec<Cells>,
}

/// The face poset of `faces` over `carrier`, with its cells as data: the
/// nonempty faces and the whole carrier, each one cell.
///
/// # Specification
/// trivial.
fn complex(
    carrier: PointCount,
    faces: &[Mask],
) -> Complex
{
    let top = whole(carrier);
    let mut cells: Vec<Mask> = faces
        .iter()
        .copied()
        .filter(|face| face.0 != 0)
        .chain([top])
        .collect();
    cells.sort_unstable_by_key(|cell| cell.0);
    cells.dedup();
    let mut closures = Vec::with_capacity(cells.len());
    for &upper in &cells {
        let mut closure = Cells::default();
        for (index, &lower) in cells.iter().enumerate() {
            if included(lower, upper) == Membership::Inside {
                closure = Cells(closure.0 | Cells::single(CellIndex(index)).0);
            }
        }
        closures.push(closure);
    }
    Complex {
        carrier,
        cells,
        closures,
    }
}

/// Every subcomplex of `complex`: each set of cells that holds the closure of
/// each of its cells, in mask order.
///
/// # Specification
/// trivial.
fn subcomplexes(complex: &Complex) -> Vec<Cells>
{
    let width = u32::try_from(complex.cells.len()).expect("a small complex");
    let count = 1_u64
        .checked_shl(width)
        .expect("fewer cells than a word has bits");
    let mut lattice = Vec::new();
    for bits in 0 .. count {
        let set = Cells(bits);
        let mut closed = true;
        for (index, &closure) in complex.closures.iter().enumerate() {
            if Cells::single(CellIndex(index)).within(set) == Membership::Inside
                && closure.within(set) == Membership::Outside
            {
                closed = false;
            }
        }
        if closed {
            lattice.push(set);
        }
    }
    lattice
}

/// The join-irreducible elements of `lattice`: each nonempty element that is
/// not the union of the elements strictly below it, in mask order.
///
/// # Specification
/// trivial.
fn join_irreducibles(lattice: &[Cells]) -> Vec<Cells>
{
    let mut irreducible = Vec::new();
    for &element in lattice {
        let mut below = Cells::default();
        for &other in lattice {
            if other != element && other.within(element) == Membership::Inside {
                below = Cells(below.0 | other.0);
            }
        }
        if element != Cells::default() && below != element {
            irreducible.push(element);
        }
    }
    irreducible
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
/// subcomplexes, and checks the round trip.
///
/// The join-irreducible subcomplexes are the closures of the cells, one for
/// each cell. The crate's entailment orders the cells as inclusion orders
/// their closures.
///
/// # Specification
/// trivial.
fn read_back(
    carrier: PointCount,
    faces: &[Mask],
) -> Reading
{
    let complex = complex(carrier, faces);
    let lattice = subcomplexes(&complex);
    let spectrum = join_irreducibles(&lattice);
    let mut closures = complex.closures.clone();
    closures.sort_unstable();
    assert_eq!(
        spectrum, closures,
        "the spectrum of {faces:?} over {carrier:?} is its cells"
    );
    for (below, &lower) in complex.cells.iter().enumerate() {
        for (above, &upper) in complex.cells.iter().enumerate() {
            let order = match complex.closures[below].within(complex.closures[above]) {
                Membership::Inside => Verdict::Holds,
                Membership::Outside => Verdict::Refuted,
            };
            assert_eq!(
                entails(complex.carrier, lower, Family::single(upper)),
                order,
                "the cells {lower:?} and {upper:?} of {faces:?}"
            );
        }
    }
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
    let square = corpus()
        .into_iter()
        .find(|shape| shape.named.starts_with("Square"))
        .expect("the corpus states `Square`");
    let faces: Vec<Mask> = square.faces.members().collect();
    assert_eq!(read_back(square.carrier, &faces), Reading {
        subcomplexes: 21,
        spectrum: 6,
    });
}

#[test]
fn every_corpus_shape_reads_its_face_poset_back_from_its_subcomplexes()
{
    // `Config` names two faces whose union is the carrier. The spectrum suite
    // drops the carrier from the spectrum, since it is no point's least face.
    // As a cell, the carrier is the top of its own closure, which is
    // join-irreducible.
    let expected = [
        ("Two", 3_usize, 2_usize),
        ("Three", 3, 2),
        ("Config", 5, 3),
        ("Square", 21, 6),
    ];
    let shapes = corpus();
    assert_eq!(shapes.len(), expected.len(), "every corpus shape is read");
    let mut faces: Vec<Mask> = Vec::new();
    for (shape, (name, subcomplexes, spectrum)) in shapes.iter().zip(expected) {
        assert!(shape.named.starts_with(name), "{}", shape.named);
        faces.clear();
        faces.extend(shape.faces.members());
        assert_eq!(
            read_back(shape.carrier, &faces),
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
    // Every family of faces over a carrier of up to three points: the round
    // trip holds on each, the unions and meets of the spectrum suite with them.
    let mut faces: Vec<Mask> = Vec::new();
    for size in 0 ..= 3_usize {
        let carrier = PointCount::from(size);
        let width = u32::try_from(size).expect("a small carrier");
        let masks = 1_usize.checked_shl(width).expect("a small carrier");
        let families = 1_u64
            .checked_shl(u32::try_from(masks).expect("a small family"))
            .expect("a family of at most eight faces");
        for family in 0 .. families {
            faces.clear();
            faces.extend(
                (0 .. masks)
                    .filter(|&mask| {
                        let shift = u32::try_from(mask).expect("a small mask");
                        family.checked_shr(shift).unwrap_or(0) & 1 == 1
                    })
                    .map(Mask),
            );
            let reading = read_back(carrier, &faces);
            assert_eq!(
                reading.spectrum,
                complex(carrier, &faces).cells.len(),
                "{faces:?} over {carrier:?}"
            );
        }
    }
}
