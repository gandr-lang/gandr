//! The chain restriction's fixtures the Θ₂ and Θ₃ suites share: a column
//! chain, the restriction at level two, a Θ₂ object as the restriction writes
//! it, an object's class, level one certified at a catalogue's top degree,
//! level two certified at its wreath's, and the wreath at level three.

use alloc::sync::Arc;

use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Level;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathStratum;
use quenchant_shape::shape::Maybe;

/// A chain's vertex count, a column's, or a shift by that many vertices.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Length(pub usize);

/// The chain of `length` vertices, or the empty shape at length zero.
///
/// # Specification
/// trivial.
pub fn column(Length(length): Length) -> Shape
{
    if length == 0 {
        Shape::default()
    }
    else {
        Shape::chain(EdgeCount::from(length)).expect("the chain is admitted")
    }
}

/// The chain restriction at level two, every object of total size at most
/// `bound`.
///
/// # Specification
/// trivial.
pub fn restriction(bound: ShapeSize) -> Wreath<Catalogue>
{
    let chains = Catalogue::chains(bound).expect("the chain catalogue builds");
    Wreath::build(&chains, &chains, bound)
}

/// The Θ₂ object `[n](m_1, …, m_n)` with one column length `m_i` per outer
/// vertex: the outer chain of `n` vertices carrying each column.
///
/// # Specification
/// trivial.
pub fn theta(columns: &[Length]) -> WreathShape<Shape>
{
    WreathShape::new(
        column(Length(columns.len())),
        columns.iter().copied().map(column).collect(),
    )
    .expect("one column per outer vertex")
}

/// The index of `object`'s class in `level`, which holds it.
///
/// # Specification
/// trivial.
pub fn index<L>(
    level: &L,
    object: &L::Object,
) -> ShapeIndex
where
    L: Level,
{
    match level.find(object) {
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("{object} is held: {reason:?}"),
    }
}

/// Level one over `catalogue`, certified at the top degree of its shapes.
///
/// # Specification
/// trivial.
pub fn level_one(catalogue: &Arc<Catalogue>) -> SegalStratum
{
    let top = catalogue
        .shapes()
        .iter()
        .map(Degree::of)
        .max()
        .expect("the catalogue holds shapes");
    SegalStratum::certify(Arc::clone(catalogue), top).expect("level one is certified")
}

/// Level two over `catalogue` to total size `bound`, certified at the top
/// degree of its objects over [`level_one`].
///
/// # Specification
/// trivial.
pub fn level_two(
    catalogue: &Arc<Catalogue>,
    bound: ShapeSize,
) -> WreathStratum
{
    let level: &Catalogue = catalogue;
    let wreath = Arc::new(Wreath::build(level, level, bound));
    let top = wreath
        .objects()
        .iter()
        .map(Wreath::<Catalogue>::degree)
        .max()
        .expect("the wreath holds objects");
    WreathStratum::certify(wreath, top, level_one(catalogue)).expect("level two is certified")
}

/// The wreath at level three over `below`'s catalogue and its level-two
/// wreath, every object of total size at most `bound`.
///
/// # Specification
/// trivial.
pub fn level_three(
    below: &WreathStratum,
    bound: ShapeSize,
) -> Arc<Wreath<Wreath<Catalogue>>>
{
    Arc::new(Wreath::build(
        below.below().catalogue(),
        below.wreath(),
        bound,
    ))
}
