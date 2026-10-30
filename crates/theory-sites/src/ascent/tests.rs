//! The level-two cover with a kind of graft left out, the form the
//! condition's unmediated family is stated on.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec;

use gandr_theory_circuit_algebras::EdgeCount;
use quenchant_shape::shape::Maybe;

use super::LevelDefect;
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
        tests().all(|test| colimit(&wreath, &whole, test).is_ok()),
        "the whole cover is a colimit"
    );
    let mut cut = whole;
    cut.outer = Box::default();
    let unmediated = tests()
        .filter(|&test| {
            matches!(
                colimit(&wreath, &cut, test),
                Err(LevelDefect::Unmediated { .. })
            )
        })
        .count();
    assert_ne!(
        unmediated, 0,
        "a family of two 1-cells sent apart is unmediated"
    );
}
