//! The corolla stratum suite: its certification, an equivalence of species
//! as a finite certificate, and the corolla restriction of a natural
//! isomorphism of the free algebras.

use alloc::collections::BTreeMap;

use gandr_theory_sites::Bijection;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::CorollaStratum;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Element;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::Equivalence;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::GeneratorIndex;
use gandr_theory_sites::Natural;
use gandr_theory_sites::Port;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Species;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::restrict;
use quenchant_shape::shape::Maybe;

/// A profile's legs: its inputs, then its outputs.
#[derive(Clone, Copy, Debug)]
struct Legs(usize, usize);

/// How many generators a species holds at one profile.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Generators(usize);

/// A bijection's forward table, then its backward table, by position.
#[derive(Clone, Copy, Debug)]
struct Tables<'tables>(&'tables [usize], &'tables [usize]);

/// The profile of `inputs` input legs and `outputs` output legs.
///
/// # Specification
/// trivial.
fn profile(Legs(inputs, outputs): Legs) -> Profile
{
    Profile {
        inputs: PortCount::from(inputs),
        outputs: PortCount::from(outputs),
    }
}

/// The species with the given generator counts.
///
/// # Specification
/// trivial.
fn species(counts: &[(Legs, Generators)]) -> Species
{
    Species::new(
        counts
            .iter()
            .map(|&(legs, Generators(count))| (profile(legs), GeneratorCount::from(count)))
            .collect(),
    )
}

/// A binary operation and a constant: `mul : 2 → 1` and `e : 0 → 1`.
///
/// # Specification
/// trivial.
fn monoid() -> Species
{
    species(&[(Legs(2, 1), Generators(1)), (Legs(0, 1), Generators(1))])
}

/// The bijection whose forward and backward tables are `forward` and
/// `backward`.
///
/// # Specification
/// trivial.
fn bijection(Tables(forward, backward): Tables<'_>) -> Bijection
{
    let table =
        |images: &[usize]| Table::new(images.iter().copied().map(ElementIndex::from).collect());
    Bijection {
        forward: table(forward),
        backward: table(backward),
    }
}

/// The catalogue position of the corolla of `legs`.
///
/// # Specification
/// trivial.
fn corolla(
    stratum: &CorollaStratum<'_>,
    legs: Legs,
) -> ShapeIndex
{
    match stratum.corolla(profile(legs)) {
        | Maybe::Present(corolla) => corolla.index(),
        | Maybe::Absent(reason) => panic!("the corolla is within the bound: {reason:?}"),
    }
}

/// The catalogue position of `shape`'s class.
///
/// # Specification
/// trivial.
fn position(
    catalogue: &Catalogue,
    shape: &Shape,
) -> ShapeIndex
{
    match catalogue.find(shape) {
        | Maybe::Present(index) => index,
        | Maybe::Absent(reason) => panic!("the class is within the bound: {reason:?}"),
    }
}

/// At size five the stratum is the fifteen corollas of at most four legs, each
/// with its legs' permutations as automorphisms; the binary corolla holds two
/// elements of one binary generator, the identity attachment first. Degree two
/// is refused by its degree, and the catalogue at size zero, which lacks the
/// point, by the empty shape the corolla condition fails at.
#[test]
fn the_corolla_stratum_is_certified_at_degree_one_alone()
{
    let catalogue = Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds");
    let stratum =
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
    assert_eq!(
        stratum.corollas().len(),
        15,
        "every corolla of at most four legs"
    );
    let factorial = |count: usize| (1 ..= count).product::<usize>();
    for corolla in stratum.corollas() {
        let legs = corolla.profile();
        assert_eq!(
            corolla.automorphisms().len(),
            factorial(usize::from(legs.inputs)) * factorial(usize::from(legs.outputs)),
            "the automorphisms of {legs:?} permute its inputs and its outputs"
        );
    }
    let elements = monoid().elements(profile(Legs(2, 1)));
    assert_eq!(
        elements,
        [
            Element::new(
                GeneratorIndex::from(0),
                vec![Port::from(0), Port::from(1)],
                vec![Port::from(0)]
            ),
            Element::new(
                GeneratorIndex::from(0),
                vec![Port::from(1), Port::from(0)],
                vec![Port::from(0)]
            ),
        ],
        "one binary generator, attached in order and crossed"
    );
    assert_eq!(
        monoid().elements(profile(Legs(0, 1))).len(),
        1,
        "the constant has one element"
    );
    assert!(
        monoid().elements(profile(Legs(1, 1))).is_empty(),
        "an uninhabited profile has none"
    );
    assert!(
        matches!(
            CorollaStratum::certify(&catalogue, Degree::from(2)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(2)
        ),
        "the stratum above the corollas is not certified here"
    );
    let empty = Catalogue::build(ShapeSize::from(0)).expect("the catalogue builds");
    assert!(
        matches!(
            CorollaStratum::certify(&empty, Degree::from(1)),
            Err(Uncertified::Condition { witness }) if witness == Shape::default()
        ),
        "without the point the corolla condition fails at the empty shape"
    );
}

/// The input swap of a binary generator and the exchange of two binary
/// generators are equivalences; exchanging the two generators at the in-order
/// attachment alone is a bijection that does not commute with the input swap,
/// and is refused there at the first element. A table that is not injective,
/// unequal counts, a missing table and a generator past the bound are refused
/// by name.
#[test]
fn an_equivalence_commutes_with_the_corolla_automorphisms()
{
    let catalogue = Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds");
    let stratum =
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
    let binary = corolla(&stratum, Legs(2, 1));
    let constant = corolla(&stratum, Legs(0, 1));
    let monoid = monoid();
    let swap = BTreeMap::from([
        (binary, bijection(Tables(&[1, 0], &[1, 0]))),
        (constant, bijection(Tables(&[0], &[0]))),
    ]);
    let checked = Equivalence::check(&stratum, (&monoid, &monoid), swap.clone())
        .expect("the swap is natural");
    assert_eq!(checked.components(), &swap);
    let two = species(&[(Legs(2, 1), Generators(2))]);
    let exchange = BTreeMap::from([(binary, bijection(Tables(&[2, 3, 0, 1], &[2, 3, 0, 1])))]);
    assert!(
        Equivalence::check(&stratum, (&two, &two), exchange).is_ok(),
        "exchanging the generators at every attachment is natural"
    );
    let crossed = BTreeMap::from([(binary, bijection(Tables(&[2, 1, 0, 3], &[2, 1, 0, 3])))]);
    let Err(Defect::NotNatural {
        corolla,
        shape,
        map,
        element,
    }) = Equivalence::check(&stratum, (&two, &two), crossed)
    else {
        panic!("a bijection that ignores the attachment's swap is not natural");
    };
    let binary_shape = match catalogue.shape(binary) {
        | Maybe::Present(shape) => shape.clone(),
        | Maybe::Absent(reason) => panic!("the corolla is in the catalogue: {reason:?}"),
    };
    assert_eq!(
        (corolla, shape, element),
        (binary, binary, ElementIndex::from(0))
    );
    assert_ne!(
        map,
        SiteMap::identity(&binary_shape),
        "the swap of the inputs, not the identity"
    );
    let collapsed = BTreeMap::from([
        (binary, bijection(Tables(&[0, 0], &[0, 1]))),
        (constant, bijection(Tables(&[0], &[0]))),
    ]);
    assert_eq!(
        Equivalence::check(&stratum, (&monoid, &monoid), collapsed),
        Err(Defect::NotInverse {
            shape: binary,
            element: ElementIndex::from(1),
        })
    );
    let one = species(&[(Legs(2, 1), Generators(1))]);
    assert_eq!(
        Equivalence::check(&stratum, (&one, &two), BTreeMap::new()),
        Err(Defect::Cardinality { shape: binary })
    );
    assert_eq!(
        Equivalence::check(
            &stratum,
            (&monoid, &monoid),
            BTreeMap::from([(binary, bijection(Tables(&[0, 1], &[0, 1])))])
        ),
        Err(Defect::Tables { shape: constant })
    );
    let ternary = species(&[(Legs(3, 1), Generators(1))]);
    assert_eq!(
        Equivalence::check(&stratum, (&ternary, &ternary), BTreeMap::new()),
        Err(Defect::PastTheBound {
            profile: profile(Legs(3, 1))
        })
    );
}

/// The swap's extension is a bijection at every shape of size five, the swap
/// of the binary label at the graft of the constant into the operation, and
/// restricts to the swap. The same family with the identity at the graft is a
/// bijection at every shape but not natural, and is refused at the inclusion
/// of the binary corolla into the graft; a family missing its shapes is
/// refused at the first.
#[test]
fn restriction_reflects_a_natural_isomorphism_to_its_species()
{
    let catalogue = Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds");
    let stratum =
        CorollaStratum::certify(&catalogue, Degree::from(1)).expect("degree one is certified");
    let binary = corolla(&stratum, Legs(2, 1));
    let constant = corolla(&stratum, Legs(0, 1));
    let monoid = monoid();
    let swap = Equivalence::check(
        &stratum,
        (&monoid, &monoid),
        BTreeMap::from([
            (binary, bijection(Tables(&[1, 0], &[1, 0]))),
            (constant, bijection(Tables(&[0], &[0]))),
        ]),
    )
    .expect("the swap is natural");
    let natural = swap.extend(&stratum, (&monoid, &monoid));
    assert_eq!(natural.components().len(), catalogue.shapes().len());
    let graft = position(&catalogue, &shape!(2; 0 > 1, o > 1, 1 > o));
    let at_graft = natural
        .components()
        .get(usize::from(graft))
        .expect("the graft is within the bound");
    assert_eq!(
        at_graft,
        &bijection(Tables(&[1, 0], &[1, 0])),
        "the constant is fixed and the operation's attachments swap"
    );
    assert_eq!(restrict(&stratum, (&monoid, &monoid), &natural), Ok(swap));
    let mut tampered: Vec<Bijection> = natural.components().to_vec();
    if let Some(slot) = tampered.get_mut(usize::from(graft)) {
        *slot = bijection(Tables(&[0, 1], &[0, 1]));
    }
    let Err(Defect::NotNatural {
        corolla,
        shape,
        element,
        ..
    }) = restrict(&stratum, (&monoid, &monoid), &Natural::new(tampered))
    else {
        panic!("the identity at the graft does not commute with the swap at its operation");
    };
    assert_eq!(
        (corolla, shape, element),
        (binary, graft, ElementIndex::from(0))
    );
    assert_eq!(
        restrict(&stratum, (&monoid, &monoid), &Natural::new(Vec::new())),
        Err(Defect::Tables {
            shape: ShapeIndex::from(0)
        })
    );
}
