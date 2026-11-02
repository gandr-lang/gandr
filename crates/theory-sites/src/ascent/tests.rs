//! The covers at levels two and three with a kind of glue left out, the form
//! the condition's unmediated family is stated on.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec;

use gandr_theory_circuit_algebras::EdgeCount;
use quenchant_shape::shape::Maybe;

use super::LevelDefect;
use super::WreathStratum;
use super::cocone;
use super::colimit;
use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::level::Level as _;
use crate::shape::Shape;
use crate::shape::ShapeSize;
use crate::stratum::SegalStratum;
use crate::wreath::Wreath;
use crate::wreath::WreathShape;

/// The outer 2-chain of empty columns is two 1-cells glued by one outer graft.
/// Its whole cover is a colimit against every object of the chain restriction.
/// Without the graft, two 1-cells sent apart agree, and no map restricts to
/// them: the condition names that family unmediated.
#[test]
fn a_cover_without_its_outer_graft_leaves_a_family_unmediated()
{
    let bound = ShapeSize::from(13_usize);
    let chains = Arc::new(Catalogue::chains(bound).expect("the chain catalogue builds"));
    let level: &Catalogue = &chains;
    let wreath = Wreath::build(level, level, bound);
    let top = level
        .shapes()
        .iter()
        .map(Degree::of)
        .max()
        .expect("the catalogue holds shapes");
    let below = SegalStratum::certify(Arc::clone(&chains), top).expect("level one is certified");
    let outer = Shape::chain(EdgeCount::from(2_usize)).expect("the 2-chain is admitted");
    let object = WreathShape::new(outer, vec![Shape::default(), Shape::default()])
        .expect("one column per outer vertex");
    let index = match wreath.find(&object) {
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("{object} is held: {reason:?}"),
    };
    let whole = cocone(&wreath, &below, (index, &object)).expect("the cover is read");
    assert_eq!(whole.outer.len(), 1, "one outer graft");
    let tests = || (0 .. wreath.objects().len()).map(ShapeIndex::from);
    assert!(
        tests().all(|test| colimit(&wreath, &below, &whole, test).is_ok()),
        "the whole cover is a colimit"
    );
    let mut cut = whole;
    cut.outer = Box::default();
    let unmediated = tests()
        .filter(|&test| {
            matches!(
                colimit(&wreath, &below, &cut, test),
                Err(LevelDefect::Unmediated { .. })
            )
        })
        .count();
    assert_ne!(
        unmediated, 0,
        "a family of two 1-cells sent apart is unmediated"
    );
}

/// At level three over the chains, the suspension `[1]([1](2))` of the
/// vertical composite is two cells glued by its column's object, whose
/// level-two cocone glues the two 2-cells along their shared wire. Its whole
/// cover is a colimit against every object of the restriction. Without the
/// column's glue, the two cells' inner maps agree whatever level two reads of
/// them, and the condition names a family no map restricts to.
#[test]
fn a_level_three_cover_without_its_column_glue_leaves_a_family_unmediated()
{
    let bound = ShapeSize::from(11_usize);
    let chains = Arc::new(Catalogue::chains(bound).expect("the chain catalogue builds"));
    let level: &Catalogue = &chains;
    let two = Arc::new(Wreath::build(level, level, bound));
    let top = |degrees: &mut dyn Iterator<Item = Degree>| degrees.max().expect("objects");
    let one = SegalStratum::certify(
        Arc::clone(&chains),
        top(&mut level.shapes().iter().map(Degree::of)),
    )
    .expect("level one is certified");
    let degree = top(&mut two.objects().iter().map(Wreath::<Catalogue>::degree));
    let below =
        WreathStratum::certify(Arc::clone(&two), degree, one).expect("level two is certified");
    let three = Wreath::build(level, &*two, bound);
    let chain =
        |length: usize| Shape::chain(EdgeCount::from(length)).expect("the chain is admitted");
    let composite = WreathShape::new(chain(1), vec![chain(2)]).expect("one column");
    let object = WreathShape::new(chain(1), vec![composite]).expect("one column");
    let index = match three.find(&object) {
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("{object} is held: {reason:?}"),
    };
    let whole = cocone(&three, &below, (index, &object)).expect("the cover is read");
    assert_eq!(
        (whole.cells.len(), whole.inner.len()),
        (2, 1),
        "two cells glued by their column"
    );
    let tests = || (0 .. three.objects().len()).map(ShapeIndex::from);
    assert!(
        tests().all(|test| colimit(&three, &below, &whole, test).is_ok()),
        "the whole cover is a colimit"
    );
    let mut cut = whole;
    cut.inner = Box::default();
    let unmediated = tests()
        .filter(|&test| {
            matches!(
                colimit(&three, &below, &cut, test),
                Err(LevelDefect::Unmediated { .. })
            )
        })
        .count();
    assert_ne!(
        unmediated, 0,
        "a family of two 2-cells sent apart in one column is unmediated"
    );
}
