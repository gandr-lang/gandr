//! The strata suite: certification at degree one and above, an equivalence of
//! species as a finite certificate, and the corolla restriction of a natural
//! isomorphism of the free algebras.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WiringObstruction;
use gandr_theory_sites::Bijection;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::Cocones;
use gandr_theory_sites::Defect;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Element;
use gandr_theory_sites::ElementIndex;
use gandr_theory_sites::End;
use gandr_theory_sites::Ends;
use gandr_theory_sites::Equivalence;
use gandr_theory_sites::GeneratorCount;
use gandr_theory_sites::GeneratorIndex;
use gandr_theory_sites::Graft;
use gandr_theory_sites::Leg;
use gandr_theory_sites::Level as _;
use gandr_theory_sites::Membership;
use gandr_theory_sites::Natural;
use gandr_theory_sites::Outcome;
use gandr_theory_sites::Port;
use gandr_theory_sites::PortCount;
use gandr_theory_sites::Profile;
use gandr_theory_sites::SegalDefect;
use gandr_theory_sites::SegalFailure;
use gandr_theory_sites::SegalStratum;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeIndex;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::SiteMap;
use gandr_theory_sites::Species;
use gandr_theory_sites::Spot;
use gandr_theory_sites::StratumImage;
use gandr_theory_sites::Table;
use gandr_theory_sites::Uncertified;
use gandr_theory_sites::Unreplayed;
use gandr_theory_sites::Wreath;
use gandr_theory_sites::WreathShape;
use gandr_theory_sites::WreathStratum;
use gandr_theory_sites::direct_core;
use gandr_theory_sites::restrict;
use gandr_theory_sites::segal;
use gandr_theory_sites::segal_two;
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
    stratum: &SegalStratum,
    legs: Legs,
) -> ShapeIndex
{
    match stratum.corolla(profile(legs)) {
        Maybe::Present(corolla) => corolla.index(),
        Maybe::Absent(reason) => panic!("the corolla is within the bound: {reason:?}"),
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
        Maybe::Present(index) => index,
        Maybe::Absent(reason) => panic!("the class is within the bound: {reason:?}"),
    }
}

/// The elements at a corolla attach each generator's legs in every order, the
/// inputs before the outputs, and a labelling of a graft reads one element
/// per vertex in vertex order; a table reads back the images it was given.
#[test]
fn elements_attach_every_leg_order_and_labellings_read_by_vertex()
{
    let monoid = monoid();
    let binary = monoid.elements(profile(Legs(2, 1)));
    let read: Vec<(GeneratorIndex, Vec<Port>, Vec<Port>)> = binary
        .iter()
        .map(|element| {
            (
                element.generator(),
                element.inputs().to_vec(),
                element.outputs().to_vec(),
            )
        })
        .collect();
    let port = Port::from;
    assert_eq!(read, [
        (
            GeneratorIndex::from(0_usize),
            Vec::from([port(0_usize), port(1_usize)]),
            Vec::from([port(0_usize)])
        ),
        (
            GeneratorIndex::from(0_usize),
            Vec::from([port(1_usize), port(0_usize)]),
            Vec::from([port(0_usize)])
        ),
    ]);
    let constant = monoid.elements(profile(Legs(0, 1)));
    assert_eq!(constant.len(), 1);
    let grafted = shape!(2; 1 > 0, o > 0, 0 > o);
    let labels: Vec<Vec<Element>> = monoid
        .labellings(&grafted)
        .iter()
        .map(|labelling| labelling.labels().to_vec())
        .collect();
    assert_eq!(labels, [
        Vec::from([binary[0].clone(), constant[0].clone()]),
        Vec::from([binary[1].clone(), constant[0].clone()]),
    ]);
    assert_eq!(bijection(Tables(&[1, 0], &[0, 1])).forward.images(), [
        ElementIndex::from(1_usize),
        ElementIndex::from(0_usize)
    ]);
}

/// At size five the stratum is the fifteen corollas of at most four legs, each
/// with its legs' permutations as automorphisms; the binary corolla holds two
/// elements of one binary generator, the identity attachment first. Degree
/// zero is refused by its degree, and the catalogue at size zero, which lacks
/// the point, by the empty shape the corolla condition fails at.
#[test]
fn the_corolla_stratum_is_certified_at_degree_one()
{
    let catalogue = Arc::new(Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
    assert!(
        stratum.cocones().is_empty(),
        "degree one holds no shape above the corollas"
    );
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
            SegalStratum::certify(Arc::clone(&catalogue), Degree::from(0)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(0)
        ),
        "the stratum below the corollas is not certified"
    );
    let empty = Arc::new(Catalogue::build(ShapeSize::from(0)).expect("the catalogue builds"));
    assert!(
        matches!(
            SegalStratum::certify(empty, Degree::from(1)),
            Err(Uncertified::Condition { witness, degree })
                if witness == Shape::default() && degree == Degree::from(1)
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
    let catalogue = Arc::new(Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
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
        Maybe::Present(shape) => shape.clone(),
        Maybe::Absent(reason) => panic!("the corolla is in the catalogue: {reason:?}"),
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
/// refused at the first, and one with a shape too many past the last. Two
/// species with different term counts at a shape are refused there.
#[test]
fn restriction_reflects_a_natural_isomorphism_to_its_species()
{
    let catalogue = Arc::new(Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
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
    let mut longer: Vec<Bijection> = natural.components().to_vec();
    longer.push(Bijection::default());
    assert_eq!(
        restrict(&stratum, (&monoid, &monoid), &Natural::new(longer)),
        Err(Defect::Tables {
            shape: ShapeIndex::from(catalogue.shapes().len())
        })
    );
    let doubled = species(&[(Legs(2, 1), Generators(2)), (Legs(0, 1), Generators(1))]);
    let Err(Defect::Cardinality { shape }) = restrict(&stratum, (&monoid, &doubled), &natural)
    else {
        panic!("two binary generators hold twice the terms of one");
    };
    let form = catalogue.shape(shape);
    assert!(
        matches!(form, Maybe::Present(form) if monoid.labellings(form).len() != doubled.labellings(form).len()),
        "the refused shape is one whose term counts differ"
    );
    assert_eq!(stratum.catalogue().shapes(), catalogue.shapes());
}

/// At size five the stratum of degree two holds the nineteen shapes of two
/// vertices and no inner wire, each the colimit of its two corollas with no
/// graft. The swap checked there extends to the family it extends to at
/// degree one and restricts back, and the family with the identity at the
/// graft is refused at the inclusion of the binary corolla into it. At size
/// four the closed chain of a constant into a co-constant, of degree three, is
/// the pushout of its two corollas along their one shared leg; the condition
/// holds at every degree the catalogue reaches over the admitted families and
/// fails at the two points against the point over the blanket ones; degree
/// five lies past every shape there.
#[test]
fn a_shape_of_degree_two_is_the_colimit_of_its_corollas()
{
    let catalogue = Arc::new(Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(2))
        .expect("degree two is certified");
    assert_eq!(stratum.degree(), Degree::from(2));
    assert_eq!(
        stratum.cocones().len(),
        19,
        "every pair of corollas within the bound"
    );
    assert!(
        stratum
            .cocones()
            .iter()
            .all(|cocone| cocone.inclusions().len() == 2 && cocone.grafts().is_empty()),
        "a shape of degree two is two corollas side by side"
    );
    let (binary, point) = (corolla(&stratum, Legs(2, 1)), corolla(&stratum, Legs(0, 0)));
    let beside = position(&catalogue, &shape!(2; o > 0, o > 0, 0 > o));
    let cocone = stratum
        .cocones()
        .iter()
        .find(|cocone| cocone.shape() == beside)
        .expect("the operation beside a point is of degree two");
    let mut included: Vec<ShapeIndex> = cocone
        .inclusions()
        .iter()
        .map(|inclusion| inclusion.corolla)
        .collect();
    included.sort_unstable();
    let mut expected = vec![binary, point];
    expected.sort_unstable();
    assert_eq!(
        included, expected,
        "the operation's corolla and the point's"
    );

    let constant = corolla(&stratum, Legs(0, 1));
    let monoid = monoid();
    let tables = BTreeMap::from([
        (binary, bijection(Tables(&[1, 0], &[1, 0]))),
        (constant, bijection(Tables(&[0], &[0]))),
    ]);
    let swap = Equivalence::check(&stratum, (&monoid, &monoid), tables)
        .expect("the swap is natural at degree two");
    let one = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(1))
        .expect("degree one is certified");
    let natural = swap.extend(&stratum, (&monoid, &monoid));
    assert_eq!(
        natural,
        swap.extend(&one, (&monoid, &monoid)),
        "the corolla tables determine one family at every degree"
    );
    assert_eq!(restrict(&stratum, (&monoid, &monoid), &natural), Ok(swap));
    let graft = position(&catalogue, &shape!(2; 0 > 1, o > 1, 1 > o));
    let mut tampered: Vec<Bijection> = natural.components().to_vec();
    if let Some(slot) = tampered.get_mut(usize::from(graft)) {
        *slot = bijection(Tables(&[0, 1], &[0, 1]));
    }
    let Err(Defect::NotNatural {
        corolla: refused,
        shape,
        ..
    }) = restrict(&stratum, (&monoid, &monoid), &Natural::new(tampered))
    else {
        panic!("the identity at the graft does not commute with the swap at its operation");
    };
    assert_eq!((refused, shape), (binary, graft));

    let small = Arc::new(Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds"));
    let three = SegalStratum::certify(Arc::clone(&small), Degree::from(3))
        .expect("degree three is certified");
    let chain = position(&small, &shape!(2; 0 > 1));
    let cocone = three
        .cocones()
        .iter()
        .find(|cocone| cocone.shape() == chain)
        .expect("the closed chain is of degree three");
    let &[graft] = cocone.grafts()
    else {
        panic!("one inner wire, one graft");
    };
    let at = |leg: Leg| {
        cocone
            .inclusions()
            .get(usize::from(leg.vertex))
            .map(|inclusion| inclusion.corolla)
    };
    assert_eq!(
        (at(graft.producer), at(graft.consumer)),
        (
            Some(corolla(&three, Legs(0, 1))),
            Some(corolla(&three, Legs(1, 0)))
        ),
        "the constant's output leg glued to the co-constant's input leg"
    );
    assert_eq!(
        graft,
        Graft {
            wire: graft.wire,
            producer: Leg {
                vertex: graft.producer.vertex,
                wire: Wire::from(0),
            },
            consumer: Leg {
                vertex: graft.consumer.vertex,
                wire: Wire::from(0),
            },
        },
        "each corolla's one leg"
    );
    assert_ne!(graft.producer.vertex, graft.consumer.vertex);
    assert!(
        matches!(
            segal(&small, Degree::from(4), Cocones::Admitted),
            Outcome::Holds { cases } if usize::from(cases) == 620
        ),
        "twenty shapes of degree two to four, each against thirty-one"
    );
    let Outcome::Fails {
        witness: SegalFailure {
            shape,
            test,
            defect,
        },
        ..
    } = segal(&small, Degree::from(2), Cocones::Blanket)
    else {
        panic!("the blanket families include a fold");
    };
    let identity = SiteMap::identity(&shape!(1));
    assert_eq!(
        (shape, test, defect),
        (shape!(2), shape!(1), SegalDefect::Unmediated {
            family: vec![identity.clone(), identity].into_boxed_slice()
        }),
        "both points onto the one point is a family no map induces"
    );
    assert!(
        matches!(
            SegalStratum::certify(Arc::clone(&small), Degree::from(5)),
            Err(Uncertified::Degree { degree }) if degree == Degree::from(5)
        ),
        "no shape of degree five at size four"
    );
}

/// The chain of `length` vertices, or the empty shape for zero.
///
/// # Specification
/// trivial.
fn column(length: EdgeCount) -> Shape
{
    if usize::from(length) == 0 {
        Shape::default()
    }
    else {
        Shape::chain(length).expect("the chain is admitted")
    }
}

/// The Θ₂ object `[n](m_1, …, m_n)` as the outer `n`-chain carrying the
/// columns' chains.
///
/// # Specification
/// trivial.
fn theta(
    outer: EdgeCount,
    columns: &[EdgeCount],
) -> WreathShape<Shape>
{
    WreathShape::new(column(outer), columns.iter().copied().map(column).collect())
        .expect("one column per outer vertex")
}

/// The top degree of `catalogue`'s shapes, where level one is certified.
///
/// # Specification
/// trivial.
fn top(catalogue: &Catalogue) -> Degree
{
    catalogue
        .shapes()
        .iter()
        .map(Degree::of)
        .max()
        .expect("the catalogue holds shapes")
}

/// The whisker `[2](1, 0)`, the horizontal composite `[2](1, 1)` and the
/// vertical composite `[1](2)` are each the colimit of their two cells over
/// the chain restriction at total size thirteen. The whisker's second cell is
/// its empty column's 1-cell, glued to the 2-cell by the one outer graft; the
/// vertical composite's two 2-cells meet along one inner graft. At degree five
/// level two holds the cocones of the 16 objects of degree two to five, and at
/// eleven, the bound's top, 111 cocones of 398 cells from level one's five.
#[test]
fn the_whisker_and_both_composites_are_certified_at_level_two()
{
    let bound = ShapeSize::from(13_usize);
    let chains = Arc::new(Catalogue::chains(bound).expect("the chain catalogue builds"));
    let level: &Catalogue = &chains;
    let wreath = Wreath::build(level, level, bound);
    let below =
        SegalStratum::certify(Arc::clone(&chains), top(level)).expect("level one is certified");
    assert_eq!(below.cocones().len(), 5);
    let stratum = WreathStratum::certify(&wreath, Degree::from(5_usize), below)
        .expect("level two is certified at degree five");
    let [zero, one, two] = [0_usize, 1, 2].map(EdgeCount::from);
    let cases = [
        (
            theta(two, &[one, zero]),
            [Spot::Vertex(Edge::from(0_usize)), Spot::Empty],
            1,
            0,
        ),
        (
            theta(two, &[one, one]),
            [Spot::Vertex(Edge::from(0_usize)); 2],
            1,
            0,
        ),
        (
            theta(one, &[two]),
            [
                Spot::Vertex(Edge::from(0_usize)),
                Spot::Vertex(Edge::from(1_usize)),
            ],
            0,
            1,
        ),
    ];
    for (object, spots, outer, inner) in cases {
        let Maybe::Present(at) = wreath.find(&object)
        else {
            panic!("{object} is an object of the restriction");
        };
        let cocone = stratum
            .cocones()
            .iter()
            .find(|cocone| cocone.object() == at)
            .unwrap_or_else(|| panic!("{object} has a cocone"));
        let read: Vec<Spot> = cocone.cells().iter().map(|cell| cell.spot).collect();
        assert_eq!(read, spots, "{object}'s cells");
        assert_eq!(
            (cocone.outer().len(), cocone.inner().len()),
            (outer, inner),
            "{object}'s grafts"
        );
    }
    assert_eq!(stratum.cocones().len(), 16);
    let below =
        SegalStratum::certify(Arc::clone(&chains), top(level)).expect("level one is certified");
    let whole = WreathStratum::certify(&wreath, Degree::from(11_usize), below)
        .expect("level two is certified at the bound's top");
    assert_eq!(whole.cocones().len(), 111);
    let cells: usize = whole
        .cocones()
        .iter()
        .map(|cocone| cocone.cells().len())
        .sum();
    assert_eq!(cells, 398);
}

/// Level two's grounded objects, an empty column among them, form a direct
/// category with automorphisms: over the chain restriction at total size
/// thirteen, 766 maps between grounded objects, and over `W ≀ W` at total
/// size four, 109, every one raising and strictly raising the degree unless
/// invertible. A map of the whole wreath lowers: the point's deletion is
/// fenced, never read.
#[test]
fn level_two_is_direct_with_automorphisms_on_its_grounded_objects()
{
    let bound = ShapeSize::from(13_usize);
    let chains = Catalogue::chains(bound).expect("the chain catalogue builds");
    let restriction = Wreath::build(&chains, &chains, bound);
    assert_eq!(direct_core(&Site::new(&restriction)), Outcome::Holds {
        cases: 766.into()
    });
    let small = ShapeSize::from(4_usize);
    let wirings = Catalogue::build(small).expect("the catalogue builds");
    let wreath = Wreath::build(&wirings, &wirings, small);
    assert_eq!(direct_core(&Site::new(&wreath)), Outcome::Holds {
        cases: 109.into()
    });
    let [zero, one] = [0_usize, 1].map(EdgeCount::from);
    let point = WreathShape::new(column(one), vec![column(one)]).expect("one column");
    assert_eq!(Wreath::<Catalogue>::grounded(&point), Membership::Inside);
    let fat = theta(one, &[zero]);
    assert_eq!(Wreath::<Catalogue>::grounded(&fat), Membership::Inside);
    let dot = Shape::from_ends(EdgeCount::from(1_usize), vec![]).expect("the point");
    let pointed = WreathShape::new(column(one), vec![dot]).expect("one column");
    assert_eq!(Wreath::<Catalogue>::grounded(&pointed), Membership::Outside);
}

/// Two 2-cells each the other's source are no level-two object, as Leclerc and
/// Mimram's Lemma 3 states of a pasting scheme. The carrier refuses the wiring
/// they would make by name, as a directed cycle, whether it stands as a column
/// or as the outer shape of two columns. So no level holds a shape whose cells
/// meet in a cycle. Every object of `W ≀ W` at total size five is the colimit
/// of its cells.
#[test]
fn two_cells_each_the_others_source_are_refused_at_level_two()
{
    let cycle = || {
        Shape::from_ends(EdgeCount::from(2_usize), vec![
            Ends::new(
                End::Vertex(Edge::from(0_usize)),
                End::Vertex(Edge::from(1_usize)),
            ),
            Ends::new(
                End::Vertex(Edge::from(1_usize)),
                End::Vertex(Edge::from(0_usize)),
            ),
        ])
    };
    let refused = |obstruction: &ShapeObstruction| {
        matches!(
            *obstruction,
            ShapeObstruction::Carrier(WiringObstruction::DirectedCycle { .. })
        )
    };
    let [zero, one] = [0_usize, 1].map(EdgeCount::from);
    let as_column = cycle().map(|inner| WreathShape::new(column(one), vec![inner]));
    assert!(
        matches!(as_column, Err(ref obstruction) if refused(obstruction)),
        "two opposite 2-cells in one column are refused as a directed cycle: {as_column:?}"
    );
    let as_outer = cycle().map(|outer| WreathShape::new(outer, vec![column(zero), column(zero)]));
    assert!(
        matches!(as_outer, Err(ref obstruction) if refused(obstruction)),
        "two opposite cells across columns are refused as a directed cycle: {as_outer:?}"
    );
    let small = ShapeSize::from(5_usize);
    let wirings = Arc::new(Catalogue::build(small).expect("the catalogue builds"));
    let level: &Catalogue = &wirings;
    let wreath = Wreath::build(level, level, small);
    let below =
        SegalStratum::certify(Arc::clone(&wirings), top(level)).expect("level one is certified");
    assert_eq!(
        segal_two(&wreath, &below, Degree::from(5_usize)),
        Outcome::Holds {
            cases: 46592.into()
        }
    );
    let stratum = WreathStratum::certify(&wreath, Degree::from(5_usize), below)
        .expect("level two over the wirings is certified at five");
    assert_eq!(stratum.cocones().len(), 208);
}

/// #4034: at size five the stratum of degree three replays from its image to
/// its own corollas and cocones. An image damaged at its version, its length,
/// its catalogue, its degree, its corollas, its cocones' shapes, an inclusion
/// and a graft is refused under each name.
#[test]
fn a_stratum_replays_its_image_and_refuses_a_damaged_one_4034()
{
    let catalogue = Arc::new(Catalogue::build(ShapeSize::from(5)).expect("the catalogue builds"));
    let stratum = SegalStratum::certify(Arc::clone(&catalogue), Degree::from(3))
        .expect("degree three is certified");
    let image = stratum.image();
    let replayed =
        SegalStratum::replay(Arc::clone(&catalogue), &image).expect("the stratum's image replays");
    assert_eq!(replayed.degree(), stratum.degree());
    assert_eq!(replayed.vacuity(), stratum.vacuity());
    assert_eq!(replayed.corollas(), stratum.corollas());
    assert_eq!(replayed.cocones(), stratum.cocones());
    assert_eq!(replayed.image(), image, "the image is canonical");

    let replay = |image: &StratumImage| SegalStratum::replay(Arc::clone(&catalogue), image).err();
    let mut bytes = Vec::from(image.clone());
    *bytes.first_mut().expect("the version byte") = 2;
    assert_eq!(
        replay(&StratumImage::from(bytes)),
        Some(Unreplayed::Malformed)
    );
    let mut bytes = Vec::from(image.clone());
    let _last = bytes.pop();
    assert_eq!(
        replay(&StratumImage::from(bytes)),
        Some(Unreplayed::Malformed)
    );
    let small = Arc::new(Catalogue::build(ShapeSize::from(4)).expect("the catalogue builds"));
    assert_eq!(
        SegalStratum::replay(small, &image).err(),
        Some(Unreplayed::Catalogue)
    );

    let words: Vec<u64> = image
        .as_ref()
        .get(1 ..)
        .expect("an image leads with its version")
        .chunks_exact(8)
        .map(|word| u64::from_le_bytes(word.try_into().expect("eight bytes")))
        .collect();
    let imaged = |words: &[u64]| {
        let mut bytes = vec![1_u8];
        bytes.extend(words.iter().flat_map(|word| word.to_le_bytes()));
        StratumImage::from(bytes)
    };
    let damaged = |position: usize, word: u64| {
        let mut words = words.clone();
        *words.get_mut(position).expect("the word is in the image") = word;
        replay(&imaged(&words))
    };
    assert_eq!(damaged(1, 0), Some(Unreplayed::Degree), "degree zero");
    assert_eq!(damaged(1, 6), Some(Unreplayed::Degree), "past every shape");
    let first = *words.get(3).expect("a corolla");
    assert_eq!(damaged(3, first + 1), Some(Unreplayed::Corollas));
    assert_eq!(
        damaged(1, 2),
        Some(Unreplayed::Cocones),
        "the cocones of degree three stand past degree two"
    );
    // The positions among the words of the first cocone's first inclusion's
    // hom-set position, and of the first graft's producer wire.
    let (inclusion, graft) = {
        let at = |position: usize| {
            usize::try_from(*words.get(position).expect("the word is in the image"))
                .expect("the word counts")
        };
        let past = |cursor: usize, by: usize| cursor.checked_add(by).expect("the image is short");
        let times = |count: usize, by: usize| count.checked_mul(by).expect("the image is short");
        let corollas = at(2);
        let mut cursor = past(3, corollas);
        let cocones = at(cursor);
        cursor = past(cursor, 1);
        let mut inclusion = None;
        let mut graft = None;
        for _cocone in 0 .. cocones {
            let inclusions = at(past(cursor, 1));
            let _first = inclusion.get_or_insert_with(|| past(cursor, 3));
            cursor = past(cursor, past(2, times(2, inclusions)));
            let grafts = at(cursor);
            if grafts > 0 {
                let _first = graft.get_or_insert_with(|| past(cursor, 3));
            }
            cursor = past(cursor, past(1, times(5, grafts)));
        }
        (
            inclusion.expect("a cocone includes a corolla"),
            graft.expect("a cocone grafts two corollas"),
        )
    };
    let cocone = stratum.cocones().first().expect("a cocone").shape();
    assert_eq!(
        damaged(inclusion, u64::MAX >> 1_u32),
        Some(Unreplayed::Cocone { shape: cocone }),
        "a position past the hom set"
    );
    let grafted = stratum
        .cocones()
        .iter()
        .find(|cocone| !cocone.grafts().is_empty())
        .expect("a cocone grafts")
        .shape();
    let wire = *words.get(graft).expect("the producer's wire");
    assert_eq!(
        damaged(graft, wire + 1),
        Some(Unreplayed::Cocone { shape: grafted }),
        "a producer's leg its inclusion does not send onto the wire"
    );
}
