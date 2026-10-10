//! The point-count suite: the grade, the grounded stratum, the deletions
//! and the codegeneracy.

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Invertibility;
use gandr_theory_sites::PointCount;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::VertexSet;
use gandr_theory_sites::codegeneracies;
use gandr_theory_sites::core_decomposition;
use gandr_theory_sites::deletion_classes;
use gandr_theory_sites::grounded_stratum;
use gandr_theory_sites::homs;
use gandr_theory_sites::split_lowering;

/// Every shape at size four is uniquely its core beside its points, and a
/// corolla beside two points has the corolla as its core.
#[test]
fn every_shape_is_its_core_beside_its_points()
{
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    assert_eq!(core_decomposition(&catalogue).verdict(), Verdict::Holds);
    let shape = shape!(3; o > 1, 1 > o);
    let core = shape.core().expect("the core is admitted");
    assert_eq!(core, shape!(1; o > 0, 0 > o));
    assert_eq!(usize::from(shape.point_count()), 2);
    assert_eq!(
        core.beside_points(PointCount::from(2))
            .expect("the points fit")
            .key(),
        shape.key()
    );
}

/// The grounded shapes are the shapes without points at size four.
#[test]
fn grounded_shapes_are_the_zero_stratum()
{
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    assert_eq!(grounded_stratum(&catalogue).verdict(), Verdict::Holds);
}

/// `• → ∅` is not invertible and is split by `∅ → •`; every deletion at
/// size four is split, lowers the point count and the degree by its
/// kernel, and keeps the core.
#[test]
fn the_codegeneracy_is_split()
{
    let point = shape!(1);
    let empty = shape!(0);
    let deletion = site_map!([{}], []);
    assert_eq!(homs(&point, &empty), vec![deletion.clone()]);
    assert_eq!(deletion.invertibility(&empty), Invertibility::NotInvertible);
    let section = site_map!([], []);
    section.validate(&empty, &point).expect("∅ → • is a map");
    assert_eq!(
        section.then(&deletion),
        Ok(SiteMap::identity(&empty)),
        "δ ∘ s = id"
    );
    assert_ne!(
        deletion.then(&section),
        Ok(SiteMap::identity(&point)),
        "s ∘ δ is ε, not the identity"
    );
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    let site = Site::new(&catalogue);
    assert_eq!(split_lowering(&site).verdict(), Verdict::Holds);
    assert_eq!(codegeneracies(&site).verdict(), Verdict::Holds);
}

/// The deletions out of every shape at size four are addressed by their
/// kernels; out of `•⊔•` there are three classes.
#[test]
fn deletions_are_addressed_by_kernels()
{
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    let site = Site::new(&catalogue);
    assert_eq!(deletion_classes(&site).verdict(), Verdict::Holds);
    let two_points = shape!(2);
    let mut kernels: Vec<VertexSet> = [shape!(1), shape!(0)]
        .iter()
        .flat_map(|target| homs(&two_points, target))
        .filter(|map| map.kernel() != VertexSet::EMPTY)
        .map(|map| map.kernel())
        .collect();
    kernels.sort();
    kernels.dedup();
    let single = |vertex: usize| VertexSet::single(Edge::from(vertex));
    assert_eq!(kernels, vec![
        single(0),
        single(1),
        single(0).union(single(1))
    ]);
}
