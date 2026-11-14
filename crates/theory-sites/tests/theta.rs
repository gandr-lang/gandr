//! The chain restriction at level two: the wreath of the chain catalogue over
//! itself, whose objects are Θ₂'s under the site's maps.
//!
//! The oracle is an enumeration of Θ₂'s objects `[n](m_1, …, m_n)`
//! independent of the wreath. Each one is written as the outer chain of `n`
//! vertices carrying the chain of `m_i` vertices, or the empty shape when `m_i`
//! is zero, and found in the restriction. The maps are the site's, so their
//! counts are pinned against the site's own enumeration here. `tests::oracle`
//! sets them beside Θ₂'s by Leclerc and Mimram's Definition 1.

use alloc::sync::Arc;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_sites::CaseCount;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Spot;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathCocone;
use gandr_theory_sites::WreathMap;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathShapeObstruction;
use gandr_theory_sites::WreathStratum;
use gandr_theory_sites::shape_class;
use quenchant_shape::shape::Maybe;

use crate::fixture::Length;
use crate::fixture::column;
use crate::fixture::index;
use crate::fixture::level_one;
use crate::fixture::restriction;
use crate::fixture::theta;

/// A Θ₂ object `[n](m_1, …, m_n)`: one column length `m_i` per outer vertex,
/// of which there is at least one.
#[repr(transparent)]
#[derive(Clone, Debug)]
struct Theta
{
    /// The column lengths, in vertex order.
    columns: Vec<Length>,
}

/// The size a column of `length` adds: nothing for the empty shape, and its
/// vertices and wires for a chain.
///
/// # Specification
/// trivial.
fn column_size(Length(length): Length) -> ShapeSize
{
    if length == 0 {
        ShapeSize::from(0_usize)
    }
    else {
        ShapeSize::from(length.saturating_mul(2).saturating_add(1))
    }
}

/// Every Θ₂ object of total size at most `bound`: the outer chain's vertices
/// and wires, `2n + 1`, plus each column's size.
///
/// # Specification
/// trivial.
fn theta_two(bound: ShapeSize) -> Vec<Theta>
{
    let bound = usize::from(bound);
    let mut objects = Vec::new();
    let mut outer = 1_usize;
    let mut digits: Vec<usize> = Vec::new();
    while let Some(budget) = bound.checked_sub(outer.saturating_mul(2).saturating_add(1)) {
        digits.clear();
        digits.resize(outer, 0);
        loop {
            let total = digits.iter().fold(0_usize, |sum, digit| {
                sum.saturating_add(usize::from(column_size(Length(*digit))))
            });
            if total <= budget {
                objects.push(Theta {
                    columns: digits.iter().copied().map(Length).collect(),
                });
            }
            let mut carried = true;
            for digit in &mut digits {
                let next = digit.saturating_add(1);
                if usize::from(column_size(Length(next))) <= budget {
                    *digit = next;
                    carried = false;
                    break;
                }
                *digit = 0;
            }
            if carried {
                break;
            }
        }
        outer = outer.saturating_add(1);
    }
    objects
}

/// How many maps run between the objects at `among`.
///
/// # Specification
/// trivial.
fn map_count(
    wreath: &Wreath<Catalogue>,
    among: &[ShapeIndex],
) -> CaseCount
{
    CaseCount::from(
        among
            .iter()
            .flat_map(|source| among.iter().map(move |target| (*source, *target)))
            .map(|(source, target)| wreath.hom(source, target).len())
            .sum::<usize>(),
    )
}

/// Whether `object` is a pasting scheme: it has an outer vertex, and no point
/// at either level.
///
/// # Specification
/// trivial.
fn pasting_scheme(object: &WreathShape<Shape>) -> Membership
{
    let pointless = |shape: &Shape| usize::from(shape.point_count()) == 0;
    if usize::from(object.outer().vertex_count()) > 0
        && pointless(object.outer())
        && object.columns().iter().all(pointless)
    {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// At total sizes nine, eleven and thirteen the restriction holds 26, 54 and
/// 114 objects with 793, 4008 and 21119 maps, and Θ₂ holds 8, 16 and 32. Each
/// Θ₂ object is found at a class of its own, and those classes are exactly
/// the restriction's pasting schemes, which hold 61, 209 and 733 maps.
#[test]
fn the_chain_restriction_holds_theta_two_at_the_bound()
{
    let cases = [
        (9_usize, 26_usize, 793_usize, 8_usize, 61_usize),
        (11, 54, 4008, 16, 209),
        (13, 114, 21_119, 32, 733),
    ];
    for (bound, objects, maps, held, scheme_maps) in cases {
        let restriction = restriction(ShapeSize::from(bound));
        let every: Vec<ShapeIndex> = (0 .. restriction.objects().len())
            .map(ShapeIndex::from)
            .collect();
        assert_eq!(every.len(), objects, "objects at {bound}");
        assert_eq!(
            usize::from(map_count(&restriction, &every)),
            maps,
            "maps at {bound}"
        );
        let thetas = theta_two(ShapeSize::from(bound));
        assert_eq!(thetas.len(), held, "Θ₂'s objects at {bound}");
        let mut found: Vec<ShapeIndex> = thetas
            .iter()
            .map(|object| index(&restriction, &theta(&object.columns)))
            .collect();
        found.sort_unstable();
        let schemes: Vec<ShapeIndex> = restriction
            .objects()
            .iter()
            .zip(&every)
            .filter(|&(object, _)| pasting_scheme(object) == Membership::Inside)
            .map(|(_, index)| *index)
            .collect();
        assert_eq!(
            found, schemes,
            "Θ₂ at {bound} is one-to-one onto the pasting schemes"
        );
        assert_eq!(
            usize::from(map_count(&restriction, &schemes)),
            scheme_maps,
            "the pasting schemes' maps at {bound}"
        );
    }
}

/// With both catalogues at size three and total size six, `W ≀ W` holds 209
/// objects, 7 of them chains at both levels. They are the restriction's 7
/// objects, each found at a class of its own in `W ≀ W`, and every hom set
/// between two of them has one count in both, 44 maps in all. `[1](1)` is
/// among them, so the inclusion of an empty column is compared too.
#[test]
fn the_chain_restriction_is_the_full_sub_site_of_the_wreath()
{
    let (level, total) = (ShapeSize::from(3_usize), ShapeSize::from(6_usize));
    let wirings = Catalogue::build(level).expect("the catalogue builds");
    let full = Wreath::build(&wirings, &wirings, total);
    let chains = Catalogue::chains(level).expect("the chain catalogue builds");
    let restricted = Wreath::build(&chains, &chains, total);
    assert_eq!(full.objects().len(), 209);
    let in_the_chains = full
        .objects()
        .iter()
        .filter(|object| {
            Wreath::<Catalogue>::lies_in(&[Family::Chains, Family::Chains], object)
                == Membership::Inside
        })
        .count();
    assert_eq!(in_the_chains, 7);
    assert_eq!(restricted.objects().len(), 7);
    let placed: Vec<ShapeIndex> = restricted
        .objects()
        .iter()
        .map(|object| index(&full, object))
        .collect();
    let mut distinct = placed.clone();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(distinct.len(), 7, "each object has a class of its own");
    for (source, from) in placed.iter().enumerate() {
        for (target, to) in placed.iter().enumerate() {
            assert_eq!(
                restricted
                    .hom(ShapeIndex::from(source), ShapeIndex::from(target))
                    .len(),
                full.hom(*from, *to).len(),
                "the hom set from {} to {}",
                restricted.objects()[source],
                restricted.objects()[target]
            );
        }
    }
    let every: Vec<ShapeIndex> = (0 .. 7_usize).map(ShapeIndex::from).collect();
    assert_eq!(usize::from(map_count(&restricted, &every)), 44);
}

/// The site keeps faces only, with the empty column initial. At total size
/// thirteen `[1](0) → [1](1)` has one map, where Θ₂ has the 2-cell's source
/// and its target. `[1](2) → [2](1, 1)` has none, where Θ₂ has two
/// monomorphisms, each collapsing a column onto an identity 2-cell.
#[test]
fn the_site_keeps_faces_only_with_the_empty_column_initial()
{
    let restriction = restriction(ShapeSize::from(13_usize));
    let at = |lengths: &[usize]| {
        let columns: Vec<Length> = lengths.iter().copied().map(Length).collect();
        index(&restriction, &theta(&columns))
    };
    assert_eq!(restriction.hom(at(&[0]), at(&[1])).len(), 1);
    assert_eq!(restriction.hom(at(&[2]), at(&[1, 1])).len(), 0);
}

/// Over the restriction at total size thirteen, the bigon, two wires between
/// one pair of vertices, carrying two empty columns lies outside the family: a
/// cycle at the outer level. So does the 1-chain carrying a bigon. `W ≀ W` at
/// total size four holds the bigon's object, so the refusal is the family's.
/// The 7-chain of empty columns and the 1-chain carrying the 6-chain lie past
/// the bound. One column under the 2-chain is refused with both counts.
#[test]
fn a_cycle_at_the_outer_level_is_refused_by_name()
{
    let restriction = restriction(ShapeSize::from(13_usize));
    let bigon = shape!(2; 0 > 1, 0 > 1);
    let empty = Shape::default;
    let object = |outer: Shape, columns: Vec<Shape>| {
        WreathShape::new(outer, columns).expect("one column per outer vertex")
    };
    let over_the_bigon = object(bigon.clone(), vec![empty(), empty()]);
    assert_eq!(
        restriction.find(&over_the_bigon),
        Maybe::Absent(shape_class::Absent::OutsideTheFamily)
    );
    assert_eq!(
        restriction.find(&object(column(Length(1)), vec![bigon])),
        Maybe::Absent(shape_class::Absent::OutsideTheFamily)
    );
    let wirings = Catalogue::build(ShapeSize::from(4_usize)).expect("the catalogue builds");
    let full = Wreath::build(&wirings, &wirings, ShapeSize::from(4_usize));
    assert!(matches!(full.find(&over_the_bigon), Maybe::Present(_)));
    assert_eq!(
        restriction.find(&object(column(Length(7)), vec![empty(); 7])),
        Maybe::Absent(shape_class::Absent::PastTheBound)
    );
    assert_eq!(
        restriction.find(&object(column(Length(1)), vec![column(Length(6))])),
        Maybe::Absent(shape_class::Absent::PastTheBound)
    );
    assert_eq!(
        WreathShape::new(column(Length(2)), vec![empty()]),
        Err(WreathShapeObstruction::Columns {
            vertices: EdgeCount::from(2_usize),
            columns: EdgeCount::from(1_usize),
        })
    );
}

/// At each object of the chain restriction to total size nine, the faces are
/// the objects of the whole wreath with a map into it, in its order, and each
/// hom set between two faces is the whole wreath's. An object past the bound
/// and two outside the chains are named as `find` names them (#7453).
#[test]
fn the_faces_are_the_full_sub_wreath_on_the_objects_with_a_map_in_7453()
{
    let bound = ShapeSize::from(9_usize);
    let chains = Catalogue::chains(bound).expect("the chain catalogue builds");
    let whole = Wreath::build(&chains, &chains, bound);
    for (at, object) in whole.objects().iter().enumerate() {
        let target = ShapeIndex::from(at);
        let Maybe::Present(faces) = Wreath::faces(&chains, &chains, bound, object)
        else {
            panic!("{object} is held at the bound");
        };
        let expected = whole
            .objects()
            .iter()
            .enumerate()
            .filter(|&(source, _)| !whole.hom(ShapeIndex::from(source), target).is_empty())
            .map(|(_, face)| face);
        assert!(faces.objects().iter().eq(expected), "the faces of {object}");
        for (source, from) in faces.objects().iter().enumerate() {
            for (onto, to) in faces.objects().iter().enumerate() {
                assert_eq!(
                    faces.hom(ShapeIndex::from(source), ShapeIndex::from(onto)),
                    whole.hom(index(&whole, from), index(&whole, to)),
                    "the maps from {from} to {to} among the faces of {object}"
                );
            }
        }
    }
    let empty = Shape::default;
    let object = |outer: Shape, columns: Vec<Shape>| {
        WreathShape::new(outer, columns).expect("one column per outer vertex")
    };
    let bigon = shape!(2; 0 > 1, 0 > 1);
    for (absent, reason) in [
        (theta(&[Length(6)]), shape_class::Absent::PastTheBound),
        (
            object(bigon.clone(), vec![empty(), empty()]),
            shape_class::Absent::OutsideTheFamily,
        ),
        (
            object(column(Length(1)), vec![bigon]),
            shape_class::Absent::OutsideTheFamily,
        ),
    ] {
        assert_eq!(
            Wreath::faces(&chains, &chains, bound, &absent).map(|faces| faces.objects().len()),
            Maybe::Absent(reason),
            "the faces of {absent}"
        );
    }
}

/// The top degree at each total size from one to nine is the highest degree
/// among the objects of the chain restriction there (#7453).
#[test]
fn the_top_degree_is_the_highest_degree_of_the_whole_wreath_7453()
{
    for size in 1 ..= 9_usize {
        let bound = ShapeSize::from(size);
        let chains = Catalogue::chains(bound).expect("the chain catalogue builds");
        let highest = Wreath::build(&chains, &chains, bound)
            .objects()
            .iter()
            .map(Wreath::<Catalogue>::degree)
            .max()
            .unwrap_or_else(|| Degree::from(0_usize));
        assert_eq!(
            Wreath::top_degree(&chains, &chains, bound),
            highest,
            "at total size {size}"
        );
    }
}

/// The cells of `cocone` with the objects of `wreath` in place of their
/// positions, so that the cocones of one object over two wreaths compare.
///
/// # Specification
/// trivial.
fn cells_of<'held, Glue>(
    cocone: &'held WreathCocone<SiteMap, Glue>,
    wreath: &'held Wreath<Catalogue>,
) -> impl Iterator<
    Item = (
        Edge,
        Spot,
        &'held WreathShape<Shape>,
        &'held WreathMap<SiteMap>,
    ),
> + 'held
{
    cocone.cells().iter().map(|cell| {
        (
            cell.column,
            cell.spot,
            &wreath.objects()[usize::from(cell.object)],
            &cell.map,
        )
    })
}

/// Over the faces of each object of degree two or more in the chain
/// restriction to total size nine, level two is certified at the object's
/// degree, and the object's cocone has the cells, the maps and the glue of its
/// cocone over the whole wreath (#7453).
#[test]
fn level_two_over_the_faces_agrees_with_the_whole_7453()
{
    let bound = ShapeSize::from(9_usize);
    let chains = Arc::new(Catalogue::chains(bound).expect("the chain catalogue builds"));
    let level: &Catalogue = &chains;
    let whole = Arc::new(Wreath::build(level, level, bound));
    let top = Wreath::top_degree(level, level, bound);
    let below = level_one(&chains);
    let certified = WreathStratum::certify(Arc::clone(&whole), top, below.clone())
        .expect("level two over the whole wreath is certified");
    let mut agreed = 0_usize;
    for (at, object) in whole.objects().iter().enumerate() {
        let degree = Wreath::<Catalogue>::degree(object);
        if degree < Degree::from(2_usize) {
            continue;
        }
        let Maybe::Present(faces) = Wreath::faces(level, level, bound, object)
        else {
            panic!("{object} is held at the bound");
        };
        let faces = Arc::new(faces);
        let over_faces = WreathStratum::certify(Arc::clone(&faces), degree, below.clone())
            .unwrap_or_else(|refused| panic!("level two over the faces of {object}: {refused:?}"));
        let cocone_in = |stratum: &WreathStratum, at: ShapeIndex| {
            stratum
                .cocones()
                .iter()
                .position(|cocone| cocone.object() == at)
                .expect("each object of degree two to the degree has a cocone")
        };
        let in_whole = &certified.cocones()[cocone_in(&certified, ShapeIndex::from(at))];
        let in_faces = &over_faces.cocones()[cocone_in(&over_faces, index(&*faces, object))];
        assert!(
            cells_of(in_faces, &faces).eq(cells_of(in_whole, &whole)),
            "the cells of {object}"
        );
        assert_eq!(
            in_faces.outer(),
            in_whole.outer(),
            "the outer grafts of {object}"
        );
        assert_eq!(
            in_faces.inner(),
            in_whole.inner(),
            "the columns' glue of {object}"
        );
        agreed = agreed.saturating_add(1);
    }
    assert_eq!(agreed, 23, "each object of degree two or more agrees");
}
