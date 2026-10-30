//! The profiles suite: the family of shapes whose every vertex has a profile
//! from a set, its catalogue as the full sub-site on those shapes, and the
//! stratum over it, vacuous above its top shape.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;

use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Corolla;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Family;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Vacuity;
use quenchant_shape::shape::Maybe;

/// The profile of `inputs` input legs and `outputs` output legs.
///
/// # Specification
/// trivial.
fn profile(
    inputs: PortCount,
    outputs: PortCount,
) -> Profile
{
    Profile { inputs, outputs }
}

/// A magma's profiles: the binary operation and the constant.
///
/// # Specification
/// trivial.
fn magma() -> BTreeSet<Profile>
{
    [
        profile(PortCount::from(2), PortCount::from(1)),
        profile(PortCount::from(0), PortCount::from(1)),
    ]
    .into_iter()
    .collect()
}

/// The binary operation fed by two constants, the magma's one shape of
/// degree five.
///
/// # Specification
/// trivial.
fn fed() -> Shape
{
    shape!(3; 0 > o, 1 > 0, 2 > 0)
}

/// A magma holds the empty shape, the point, its two corollas and what they
/// graft into. It refuses a vertex of another profile, the point beside
/// anything, and two points. With no profile the family holds the empty shape
/// and the point alone.
#[test]
fn the_profiles_hold_the_shapes_their_corollas_fill()
{
    let family = Family::Profiles(magma());
    let held = [
        shape!(0),
        shape!(1),
        shape!(1; 0 > o),
        shape!(1; o > 0, o > 0, 0 > o),
        shape!(2; o > 0, o > 0, o > 1, 0 > 1, 1 > o),
        fed(),
    ];
    for shape in &held {
        assert_eq!(family.holds(shape), Membership::Inside, "{shape} is held");
    }
    let refused = [
        shape!(1; o > 0, 0 > o),
        shape!(1; o > 0, 0 > o, 0 > o),
        shape!(2; o > 0, o > 0, 0 > 1, 1 > o),
        shape!(2; 1 > o),
        shape!(2),
    ];
    for shape in &refused {
        assert_eq!(
            family.holds(shape),
            Membership::Outside,
            "{shape} is refused"
        );
    }
    let none = Family::Profiles(BTreeSet::new());
    assert_eq!(
        none.holds(&shape!(0)),
        Membership::Inside,
        "the empty shape"
    );
    assert_eq!(none.holds(&shape!(1)), Membership::Inside, "the point");
    assert_eq!(
        none.holds(&shape!(1; 0 > o)),
        Membership::Outside,
        "a constant has no profile in the empty set"
    );
}

/// At size five the magma's catalogue is the wiring catalogue's classes the
/// family holds, in its order, with each hom set the wiring catalogue's, and
/// it reaches the wirings' degree. At size seven it holds eleven shapes and
/// reaches seven.
#[test]
fn the_profile_catalogue_is_the_full_sub_site_on_its_shapes()
{
    let bound = ShapeSize::from(5);
    let sub = Catalogue::profiles(bound, magma()).expect("the catalogue builds");
    let wirings = Catalogue::build(bound).expect("the catalogue builds");
    let held: Vec<(ShapeIndex, &Shape)> = wirings
        .entries()
        .filter(|entry| sub.family().holds(entry.1) == Membership::Inside)
        .collect();
    assert_eq!(
        sub.shapes(),
        held.iter().map(|entry| entry.1.clone()).collect::<Vec<_>>(),
        "the magma's shapes at size five"
    );
    for (source, &(wide_source, _)) in held.iter().enumerate() {
        for (target, &(wide_target, _)) in held.iter().enumerate() {
            assert_eq!(
                sub.maps(ShapeIndex::from(source), ShapeIndex::from(target)),
                wirings.maps(wide_source, wide_target),
                "the hom set from class {source} to class {target}"
            );
        }
    }
    assert_eq!(sub.reach(), wirings.reach(), "the wirings' reach");
    let seven = Catalogue::profiles(ShapeSize::from(7), magma()).expect("the catalogue builds");
    assert_eq!(seven.shapes().len(), 11, "the magma's shapes at size seven");
    assert_eq!(seven.reach(), Degree::from(7), "the seven points' degree");
}

/// At size seven the magma's stratum of degree seven is certified over its
/// three corollas and the seven shapes of degree two to five. It names six and
/// seven vacuous, and its replay is admitted. A claim from degree four is
/// refused at the binary operation fed by two constants, and degree eight, past
/// the reach, by its degree.
#[test]
fn the_magma_stratum_names_its_vacuous_degrees()
{
    let catalogue =
        Arc::new(Catalogue::profiles(ShapeSize::from(7), magma()).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(7))
        .expect("degree seven is certified");
    assert_eq!(
        stratum
            .corollas()
            .iter()
            .map(Corolla::profile)
            .collect::<Vec<_>>(),
        [
            Profile::default(),
            profile(PortCount::from(0), PortCount::from(1)),
            profile(PortCount::from(2), PortCount::from(1)),
        ],
        "the point, the constant and the binary operation"
    );
    assert_eq!(
        stratum.cocones().len(),
        7,
        "every shape of degree two to five"
    );
    assert_eq!(
        stratum.vacuity(),
        Vacuity::new(Degree::from(5), Degree::from(7)),
        "six and seven are vacuous"
    );
    assert_eq!(stratum.vacuity().replay(&catalogue), Ok(()), "the replay");
    let fed = match catalogue.find(&fed()) {
        Maybe::Present(index) => match catalogue.shape(index) {
            Maybe::Present(shape) => shape.clone(),
            Maybe::Absent(reason) => panic!("no shape at its class: {reason:?}"),
        },
        Maybe::Absent(reason) => panic!("the fed operation is absent: {reason:?}"),
    };
    assert_eq!(
        Vacuity::new(Degree::from(4), Degree::from(7)).replay(&catalogue),
        Err(Uncertified::Condition {
            witness: fed,
            degree: Degree::from(5),
        }),
        "degree five holds a shape"
    );
    assert_eq!(
        Vacuity::new(Degree::from(5), Degree::from(8)).replay(&catalogue),
        Err(Uncertified::Degree {
            degree: Degree::from(8)
        }),
        "a claim past the reach"
    );
    assert!(
        matches!(
            SegalStratum::certify(Arc::clone(&catalogue), Degree::from(8)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(8)
        ),
        "no wiring at size seven has degree eight"
    );
}
