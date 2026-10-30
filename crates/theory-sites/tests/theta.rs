//! The chain restriction at level two: the wreath of the chain catalogue over
//! itself, whose objects are Θ₂'s under the site's maps.
//!
//! The oracle is an enumeration of Θ₂'s objects `[n](m_1, …, m_n)`
//! independent of the wreath. Each one is written as the outer chain of `n`
//! vertices carrying the chain of `m_i` vertices, or the empty shape when `m_i`
//! is zero, and found in the restriction. The maps are the site's, so their
//! counts are pinned against the site's own enumeration here. `tests::oracle`
//! sets them beside Θ₂'s by Leclerc and Mimram's Definition 1.

use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_sites::CaseCount;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathShapeObstruction;
use gandr_theory_sites::shape_class;
use quenchant_shape::shape::Maybe;

/// A chain's vertex count, or a column's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Length(usize);

/// A Θ₂ object `[n](m_1, …, m_n)`: the outer length `n`, at least one, and
/// one column length `m_i` per outer vertex.
#[derive(Clone, Debug)]
struct Theta
{
    /// The outer length.
    outer: Length,
    /// The column lengths, in vertex order.
    columns: Vec<Length>,
}

/// The chain of `length` vertices.
///
/// # Specification
/// trivial.
fn chain(Length(length): Length) -> Shape
{
    Shape::chain(EdgeCount::from(length)).expect("the chain is admitted")
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
                    outer: Length(outer),
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

/// The restriction's object for `theta`: the outer chain carrying the chain of
/// each column's length, the empty shape for length zero.
///
/// # Specification
/// trivial.
fn encode(theta: &Theta) -> WreathShape<Shape>
{
    let column = |length: Length| {
        if length.0 == 0 {
            Shape::default()
        }
        else {
            chain(length)
        }
    };
    WreathShape::new(
        chain(theta.outer),
        theta.columns.iter().copied().map(column).collect(),
    )
    .expect("one column per outer vertex")
}

/// The chain restriction at level two, every object of total size at most
/// `bound`.
///
/// # Specification
/// trivial.
fn restriction(bound: ShapeSize) -> Wreath<Catalogue>
{
    let chains = Catalogue::chains(bound).expect("the chain catalogue builds");
    Wreath::build(&chains, &chains, bound)
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

/// The index of `object`'s class in `wreath`, which holds it.
///
/// # Specification
/// trivial.
fn index(
    wreath: &Wreath<Catalogue>,
    object: &WreathShape<Shape>,
) -> ShapeIndex
{
    match wreath.find(object) {
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("{object} is held: {reason:?}"),
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
    for (bound, objects, maps, theta, scheme_maps) in cases {
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
        assert_eq!(thetas.len(), theta, "Θ₂'s objects at {bound}");
        let mut found: Vec<ShapeIndex> = thetas
            .iter()
            .map(|theta| index(&restriction, &encode(theta)))
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
    let at = |outer: usize, columns: &[usize]| {
        index(
            &restriction,
            &encode(&Theta {
                outer: Length(outer),
                columns: columns.iter().copied().map(Length).collect(),
            }),
        )
    };
    assert_eq!(restriction.hom(at(1, &[0]), at(1, &[1])).len(), 1);
    assert_eq!(restriction.hom(at(1, &[2]), at(2, &[1, 1])).len(), 0);
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
        restriction.find(&object(chain(Length(1)), vec![bigon])),
        Maybe::Absent(shape_class::Absent::OutsideTheFamily)
    );
    let wirings = Catalogue::build(ShapeSize::from(4_usize)).expect("the catalogue builds");
    let full = Wreath::build(&wirings, &wirings, ShapeSize::from(4_usize));
    assert!(matches!(full.find(&over_the_bigon), Maybe::Present(_)));
    assert_eq!(
        restriction.find(&object(chain(Length(7)), vec![empty(); 7])),
        Maybe::Absent(shape_class::Absent::PastTheBound)
    );
    assert_eq!(
        restriction.find(&object(chain(Length(1)), vec![chain(Length(6))])),
        Maybe::Absent(shape_class::Absent::PastTheBound)
    );
    assert_eq!(
        WreathShape::new(chain(Length(2)), vec![empty()]),
        Err(WreathShapeObstruction::Columns {
            vertices: EdgeCount::from(2_usize),
            columns: EdgeCount::from(1_usize),
        })
    );
}
