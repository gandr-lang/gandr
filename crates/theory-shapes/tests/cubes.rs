//! Monotone maps between cubes as homomorphisms of free distributive
//! lattices, set against the face formulas that the crate decides.
//!
//! The cube on `n` axes is the set of vertices `{0, 1}ⁿ`, ordered axis by
//! axis. It is the spectrum of the free distributive lattice on `n`
//! generators, whose elements are polynomials in the generators. The duality
//! crate holds both, and a monotone map from the cube on `n` axes to the cube
//! on `m` axes is dual there to a homomorphism from the lattice on `m`
//! generators to the lattice on `n`. The suite enumerates both sides apart
//! and checks that each round trip is the identity. It also checks that a
//! composite of maps is dual to the composite of homomorphisms in the other
//! order.
//!
//! A polynomial is also a face formula over carriers of two points, with the
//! atom `xᵢ ∈ {1}` for each generator. Every atom of it is monotone, so this
//! crate decides it in the monotone band, also when it joins terms on two
//! variables. The suite checks each decision against the truth tables. A
//! formula that pins a vertex holds the lower point `xᵢ ∈ {0}` as well, and
//! beside a join of terms this crate refuses it. The suite checks that
//! refusal too.
//!
//! The reference readings are written apart from both crates: a table is
//! monotone when it holds above every vertex where it holds, and a set of
//! terms is an antichain when no term meets every generator of another.

use gandr_theory_shapes::Evidence;
use gandr_theory_shapes::Formula;
use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Node;
use gandr_theory_shapes::NodeId;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::Problem;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::Variable;
use gandr_theory_shapes::decide;
use gandr_theory_stone_duality::CubeMap;
use gandr_theory_stone_duality::Generator;
use gandr_theory_stone_duality::GeneratorCount;
use gandr_theory_stone_duality::Homomorphism;
use gandr_theory_stone_duality::Polynomial;
use gandr_theory_stone_duality::Table;
use gandr_theory_stone_duality::Term;
use gandr_theory_stone_duality::Vertex;

/// The Dedekind numbers: how many monotone functions a cube of up to four
/// axes carries, which is how many elements its free distributive lattice
/// has.
const DEDEKIND: [usize; 5] = [2, 3, 6, 20, 168];

/// How many maps an enumeration visits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
struct Maps(usize);

/// One digit of an odometer: an index into the choices of one position.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Digit(usize);

/// The word with only the bit at `index` set.
///
/// # Specification
/// trivial.
fn bit(index: Vertex) -> Table
{
    let shift = u32::try_from(u64::from(index)).expect("a small vertex");
    Table::from(1_u64.checked_shl(shift).expect("a vertex below a word"))
}

/// The vertex with only the axis `axis` at `1`.
///
/// # Specification
/// trivial.
fn axis_bit(axis: Generator) -> Vertex
{
    let shift = u32::try_from(usize::from(axis)).expect("a small axis");
    Vertex::from(1_u64.checked_shl(shift).expect("an axis below a word"))
}

/// The vertices of the cube on `axes` axes, in mask order.
///
/// # Specification
/// trivial.
fn vertices(axes: GeneratorCount) -> impl Iterator<Item = Vertex>
{
    let shift = u32::try_from(usize::from(axes)).expect("a small cube");
    (0 .. 1_u64.checked_shl(shift).expect("a small cube")).map(Vertex::from)
}

/// The axes of a cube, in order.
///
/// # Specification
/// trivial.
fn axes_of(axes: GeneratorCount) -> impl Iterator<Item = Generator>
{
    (0 .. usize::from(axes)).map(Generator::from)
}

/// Whether a table holds at a vertex, read from its bits.
///
/// # Specification
/// trivial.
fn holds(
    table: Table,
    vertex: Vertex,
) -> Membership
{
    if u64::from(table) & u64::from(bit(vertex)) == 0 {
        Membership::Outside
    }
    else {
        Membership::Inside
    }
}

/// Whether one vertex lies below another, axis by axis, as membership of the
/// lower in the down-set of the upper.
///
/// # Specification
/// trivial.
fn below(
    lower: Vertex,
    upper: Vertex,
) -> Membership
{
    if u64::from(lower) & u64::from(upper) == u64::from(lower) {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether a table is monotone, by every pair of vertices.
///
/// # Specification
/// trivial.
fn monotone(
    axes: GeneratorCount,
    table: Table,
) -> Membership
{
    let kept = vertices(axes).all(|lower| {
        vertices(axes).all(|upper| {
            below(lower, upper) == Membership::Outside
                || holds(table, lower) == Membership::Outside
                || holds(table, upper) == Membership::Inside
        })
    });
    if kept {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether a table of vertex images keeps every pair of vertices in order.
///
/// # Specification
/// trivial.
fn keeps_order(
    source: GeneratorCount,
    images: &[Vertex],
) -> Membership
{
    let kept = vertices(source).zip(images).all(|(lower, low)| {
        vertices(source).zip(images).all(|(upper, high)| {
            below(lower, upper) == Membership::Outside || below(*low, *high) == Membership::Inside
        })
    });
    if kept {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Every table on the cube of `axes` axes, in mask order.
///
/// # Specification
/// trivial.
fn tables(axes: GeneratorCount) -> impl Iterator<Item = Table>
{
    let last = vertices(axes).fold(0_u64, |bits, vertex| bits | u64::from(bit(vertex)));
    (0 ..= last).map(Table::from)
}

/// Every monotone truth table on a cube, in mask order.
///
/// # Specification
/// trivial.
fn monotone_tables(axes: GeneratorCount) -> Vec<Table>
{
    tables(axes)
        .filter(|table| monotone(axes, *table) == Membership::Inside)
        .collect()
}

/// The terms a table over the terms of a lattice chooses, in mask order.
///
/// # Specification
/// trivial.
fn terms_of(
    axes: GeneratorCount,
    chosen: Table,
) -> Vec<Term>
{
    vertices(axes)
        .filter(|vertex| holds(chosen, *vertex) == Membership::Inside)
        .map(|vertex| Term::from(u64::from(vertex)))
        .collect()
}

/// Whether no term of a set meets every generator of another.
///
/// # Specification
/// trivial.
fn antichain(terms: &[Term]) -> Membership
{
    let free = terms.iter().all(|lower| {
        terms.iter().all(|upper| {
            lower == upper || u64::from(*lower) & u64::from(*upper) != u64::from(*lower)
        })
    });
    if free {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Every polynomial in normal form, in order: each set of terms that is an
/// antichain, which the duality crate keeps whole. Written apart from the
/// truth tables.
///
/// # Specification
/// trivial.
fn antichains(axes: GeneratorCount) -> Vec<Polynomial>
{
    let mut found = Vec::new();
    for chosen in tables(axes) {
        let terms = terms_of(axes, chosen);
        if antichain(&terms) == Membership::Inside {
            let polynomial = Polynomial::from_terms(terms);
            assert_eq!(polynomial.terms(), terms_of(axes, chosen).as_slice());
            found.push(polynomial);
        }
    }
    found
}

/// The map whose coordinate on each axis of the target is the table that
/// the digit for that axis chooses.
///
/// # Specification
/// trivial.
fn map_of_digits(
    source: GeneratorCount,
    target: GeneratorCount,
    coordinates: &[Table],
    digits: &[Digit],
) -> CubeMap
{
    let images: Vec<Vertex> = vertices(source)
        .map(|vertex| {
            axes_of(target)
                .zip(digits)
                .filter(|&(_, digit)| holds(coordinates[digit.0], vertex) == Membership::Inside)
                .fold(Vertex::from(0), |image, (axis, _)| {
                    Vertex::from(u64::from(image) | u64::from(axis_bit(axis)))
                })
        })
        .collect();
    let ordered = keeps_order(source, &images);
    let map = CubeMap::new(source, target, images).expect("a tuple of monotone coordinates");
    assert_eq!(ordered, Membership::Inside);
    map
}

/// The homomorphism to the lattice on `target` generators whose images are
/// the polynomials the digits choose.
///
/// # Specification
/// trivial.
fn homomorphism_of_digits(
    target: GeneratorCount,
    polynomials: &[Polynomial],
    digits: &[Digit],
) -> Homomorphism
{
    let images: Vec<Polynomial> = digits
        .iter()
        .map(|digit| polynomials[digit.0].clone())
        .collect();
    Homomorphism::new(target, images).expect("a homomorphism")
}

/// Advances an odometer whose digits each run below `base`, and says whether
/// it turned over.
///
/// # Specification
/// trivial.
fn advance(
    digits: &mut [Digit],
    base: Digit,
) -> Membership
{
    for digit in digits {
        digit.0 = digit.0.saturating_add(1);
        if digit.0 < base.0 {
            return Membership::Inside;
        }
        digit.0 = 0;
    }
    Membership::Outside
}

/// Visits each map from the cube on `source` axes to the cube on `target`
/// axes whose coordinates are drawn from `coordinates`, one tuple at a time,
/// and returns how many it visited.
///
/// # Specification
/// trivial.
fn each_map(
    source: GeneratorCount,
    target: GeneratorCount,
    coordinates: &[Table],
    mut visit: impl FnMut(&CubeMap),
) -> Maps
{
    let mut digits = vec![Digit::default(); usize::from(target)];
    let mut visited = Maps(0);
    loop {
        visit(&map_of_digits(source, target, coordinates, &digits));
        visited = Maps(visited.0.saturating_add(1));
        if advance(&mut digits, Digit(coordinates.len())) == Membership::Outside {
            return visited;
        }
    }
}

/// Every map from the cube on `source` axes to the cube on `target` axes
/// whose coordinates are drawn from `coordinates`, in odometer order.
///
/// # Specification
/// trivial.
fn maps(
    source: GeneratorCount,
    target: GeneratorCount,
    coordinates: &[Table],
) -> Vec<CubeMap>
{
    let mut digits = vec![Digit::default(); usize::from(target)];
    let mut all = Vec::new();
    loop {
        all.push(map_of_digits(source, target, coordinates, &digits));
        if advance(&mut digits, Digit(coordinates.len())) == Membership::Outside {
            return all;
        }
    }
}

/// Checks that each composite of a map from the cube on `first` axes to the
/// cube on `middle` axes with a map from there to the cube on `last` axes is
/// dual to the composite of their homomorphisms in the other order. The
/// second maps and their homomorphisms are read once for every first map.
///
/// # Specification
/// trivial.
fn check_composites(
    first: GeneratorCount,
    middle: GeneratorCount,
    last: GeneratorCount,
)
{
    let afters: Vec<(CubeMap, Homomorphism)> = maps(middle, last, &monotone_tables(middle))
        .into_iter()
        .map(|after| {
            let outer = Homomorphism::of_cube_map(&after).expect("a homomorphism");
            (after, outer)
        })
        .collect();
    let _maps = each_map(first, middle, &monotone_tables(first), |before| {
        let inner = Homomorphism::of_cube_map(before).expect("a homomorphism");
        for pair in &afters {
            let composite = before.followed_by(&pair.0).expect("a composite");
            assert_eq!(
                Homomorphism::of_cube_map(&composite),
                pair.1.followed_by(&inner)
            );
        }
    });
}

/// Visits each homomorphism from the lattice on `count` generators to the
/// lattice on `target` generators whose images are drawn from `polynomials`,
/// and returns how many it visited.
///
/// # Specification
/// trivial.
fn each_homomorphism(
    count: GeneratorCount,
    target: GeneratorCount,
    polynomials: &[Polynomial],
    mut visit: impl FnMut(&Homomorphism),
) -> Maps
{
    let mut digits = vec![Digit::default(); usize::from(count)];
    let mut visited = Maps(0);
    loop {
        visit(&homomorphism_of_digits(target, polynomials, &digits));
        visited = Maps(visited.0.saturating_add(1));
        if advance(&mut digits, Digit(polynomials.len())) == Membership::Outside {
            return visited;
        }
    }
}

/// How many monotone maps go from the cube on `source` axes to the cube on
/// `target` axes: the Dedekind number of `source` to the power `target`.
///
/// # Specification
/// trivial.
fn count(
    source: GeneratorCount,
    target: GeneratorCount,
) -> Maps
{
    let width = u32::try_from(usize::from(target)).expect("a small cube");
    Maps(
        DEDEKIND
            .get(usize::from(source))
            .and_then(|number| number.checked_pow(width))
            .expect("a cube of at most four axes"),
    )
}

/// The pairs of cubes on at most four axes whose maps the suite enumerates
/// whole: every pair with at most `2¹⁸` maps. The pairs from four axes to
/// three and to four hold about `4.7·10⁶` and `8·10⁸` maps. They are left
/// out, because a map acts on each coordinate alone, and every coordinate
/// on four axes is a map to one axis, which is enumerated.
///
/// # Specification
/// trivial.
fn enumerated() -> Vec<(GeneratorCount, GeneratorCount)>
{
    (0 ..= 4_usize)
        .flat_map(|source| {
            (0 ..= 4_usize)
                .map(move |target| (GeneratorCount::from(source), GeneratorCount::from(target)))
        })
        .filter(|&(source, target)| count(source, target) <= Maps(1 << 18_u32))
        .collect()
}

/// Every table of vertex images from one cube to another that the odometer
/// `digits` names, as images.
///
/// # Specification
/// trivial.
fn images_of_digits(digits: &[Digit]) -> Vec<Vertex>
{
    digits
        .iter()
        .map(|digit| Vertex::from(u64::try_from(digit.0).expect("a small vertex")))
        .collect()
}

/// The conjunction of a list of atoms as a table, `⊤` when the list is
/// empty.
///
/// # Specification
/// trivial.
fn conjunction(atoms: Vec<Node>) -> Formula
{
    let count = atoms.len();
    let mut nodes = atoms;
    if nodes.is_empty() {
        nodes.push(Node::Top);
    }
    let mut root = 0_usize;
    for operand in 1 .. count {
        nodes.push(Node::And(NodeId::from(root), NodeId::from(operand)));
        root = nodes.len().saturating_sub(1);
    }
    Formula::new(nodes).expect("an ordered table")
}

/// The face formula that pins every variable to a vertex over carriers of two
/// points: the atom `xᵢ ∈ {vᵢ}` for each axis.
///
/// # Specification
/// trivial.
fn vertex_formula(
    axes: GeneratorCount,
    vertex: Vertex,
) -> Formula
{
    let two = PointCount::from(2_usize);
    conjunction(
        axes_of(axes)
            .map(|axis| {
                let value = match below(axis_bit(axis), vertex) {
                    Membership::Inside => Point::from(1_usize),
                    Membership::Outside => Point::from(0_usize),
                };
                Node::Member(
                    Variable::from(usize::from(axis)),
                    Subshape::new(two, &[value]).expect("a point of two"),
                )
            })
            .collect(),
    )
}

/// The face formula of a polynomial over carriers of two points: each term
/// the meet of the atoms `xᵢ ∈ {1}` of its generators, and the terms joined.
/// The empty term is `⊤`, and the empty join is `⊥`.
///
/// # Specification
/// trivial.
fn polynomial_formula(
    axes: GeneratorCount,
    polynomial: &Polynomial,
) -> Formula
{
    let one =
        Subshape::new(PointCount::from(2_usize), &[Point::from(1_usize)]).expect("a point of two");
    let mut nodes: Vec<Node> = Vec::new();
    let mut root: Option<usize> = None;
    for term in polynomial.terms() {
        let first = nodes.len();
        let mut generators = axes_of(axes)
            .filter(|axis| {
                below(axis_bit(*axis), Vertex::from(u64::from(*term))) == Membership::Inside
            })
            .peekable();
        if generators.peek().is_none() {
            nodes.push(Node::Top);
        }
        for axis in generators {
            nodes.push(Node::Member(Variable::from(usize::from(axis)), one.clone()));
            let last = nodes.len().saturating_sub(1);
            if last > first {
                let previous = last.saturating_sub(1);
                let left = if previous == first { first } else { previous };
                nodes.push(Node::And(NodeId::from(left), NodeId::from(last)));
            }
        }
        let term_root = nodes.len().saturating_sub(1);
        root = Some(root.map_or(term_root, |joined| {
            nodes.push(Node::Or(NodeId::from(joined), NodeId::from(term_root)));
            nodes.len().saturating_sub(1)
        }));
    }
    if nodes.is_empty() {
        nodes.push(Node::Bottom);
    }
    Formula::new(nodes).expect("an ordered table")
}

/// Decides `premise ⊢ conclusion` over carriers of two points with this
/// crate's entailment, validates the evidence, and reads the answer as
/// membership. A query outside the crate's band is refused as admission
/// refuses it.
///
/// # Specification
/// trivial.
fn entailed(
    axes: GeneratorCount,
    premise: Formula,
    conclusion: Formula,
) -> Result<Membership, ShapeError>
{
    let problem = Problem::new(
        vec![PointCount::from(2_usize); usize::from(axes)],
        premise,
        conclusion,
    )?;
    let evidence = decide(&problem)?;
    Ok(match evidence {
        Evidence::Holds(derivation) => {
            assert_eq!(derivation.validate(&problem), Ok(()));
            Membership::Inside
        },
        Evidence::Refuted(model) => {
            assert_eq!(model.validate(&problem), Ok(()));
            Membership::Outside
        },
    })
}

/// The truth table of a polynomial on the cube of `axes` axes, from the
/// duality crate.
///
/// # Specification
/// trivial.
fn table_of(
    axes: GeneratorCount,
    polynomial: &Polynomial,
) -> Table
{
    polynomial
        .table(axes)
        .expect("a polynomial on the cube's generators")
}

/// Checks that a term of a polynomial holds at a vertex by this crate's
/// entailment.
///
/// # Specification
/// trivial.
fn term_holds(
    axes: GeneratorCount,
    term: Term,
    vertex: Vertex,
) -> Membership
{
    let single = polynomial_formula(axes, &Polynomial::term(term));
    match entailed(axes, vertex_formula(axes, vertex), single) {
        Ok(answer) => answer,
        Err(error) => panic!("one term is refused by {error:?}"),
    }
}

#[test]
fn the_monotone_tables_are_the_polynomials_one_to_one()
{
    // Both sides are enumerated apart, and each has the Dedekind number of
    // elements.
    for (size, dedekind) in DEDEKIND.into_iter().enumerate() {
        let axes = GeneratorCount::from(size);
        let tables = monotone_tables(axes);
        let polynomials = antichains(axes);
        assert_eq!((tables.len(), polynomials.len()), (dedekind, dedekind));
        for table in &tables {
            let polynomial = Polynomial::from_table(axes, *table).expect("a monotone table");
            assert_eq!(table_of(axes, &polynomial), *table);
        }
        for polynomial in &polynomials {
            let table = table_of(axes, polynomial);
            assert_eq!(Polynomial::from_table(axes, table).as_ref(), Ok(polynomial));
        }
    }
}

#[test]
fn every_monotone_map_of_cubes_is_a_homomorphism_and_back()
{
    for (source, target) in enumerated() {
        let tables = monotone_tables(source);
        let polynomials = antichains(source);
        // From the maps: each tuple of monotone coordinates is a monotone map,
        // and its homomorphism reads back to it.
        let maps = each_map(source, target, &tables, |map| {
            let homomorphism = Homomorphism::of_cube_map(map).expect("a homomorphism");
            assert_eq!(homomorphism.cube_map().as_ref(), Ok(map));
        });
        // From the homomorphisms: each tuple of polynomials gives a monotone
        // map, which reads back to it.
        let homomorphisms = each_homomorphism(target, source, &polynomials, |homomorphism| {
            let map = homomorphism.cube_map().expect("a map");
            assert_eq!(keeps_order(source, map.images()), Membership::Inside);
            assert_eq!(Homomorphism::of_cube_map(&map).as_ref(), Ok(homomorphism));
        });
        assert_eq!(
            (maps, homomorphisms),
            (count(source, target), count(source, target))
        );
    }
}

#[test]
fn every_monotone_vertex_table_is_a_tuple_of_monotone_coordinates()
{
    // The maps above are tuples of monotone coordinates. Here every table of
    // vertex images is tried, and the monotone ones are counted. Their number
    // is the number of tuples wherever the tables are few enough to try.
    for (source, target) in enumerated() {
        let width = vertices(source).count();
        let base = vertices(target).count();
        let tried = base.checked_pow(u32::try_from(width).expect("a small cube"));
        if tried.is_none_or(|tried| tried > 1 << 16_u32) {
            continue;
        }
        assert_eq!(
            monotone_vertex_tables(source, target),
            count(source, target),
            "{source:?} to {target:?}"
        );
    }
}

/// Tries every table of vertex images from the cube on `source` axes to the
/// cube on `target` axes, checks that the duality crate admits exactly the
/// tables that keep the order, and counts them.
///
/// # Specification
/// trivial.
fn monotone_vertex_tables(
    source: GeneratorCount,
    target: GeneratorCount,
) -> Maps
{
    let base = vertices(target).count();
    let mut digits = vec![Digit::default(); vertices(source).count()];
    let mut monotone_maps = Maps(0);
    loop {
        let images = images_of_digits(&digits);
        let ordered = keeps_order(source, &images);
        match CubeMap::new(source, target, images) {
            Ok(_) => {
                assert_eq!(ordered, Membership::Inside);
                monotone_maps = Maps(monotone_maps.0.saturating_add(1));
            },
            Err(_) => assert_eq!(ordered, Membership::Outside),
        }
        if advance(&mut digits, Digit(base)) == Membership::Outside {
            return monotone_maps;
        }
    }
}

/// Whether some term of a polynomial holds at a vertex, each term decided by
/// this crate's entailment on its own.
///
/// # Specification
/// trivial.
fn holds_by_terms(
    axes: GeneratorCount,
    polynomial: &Polynomial,
    vertex: Vertex,
) -> Membership
{
    let held = polynomial
        .terms()
        .iter()
        .any(|term| term_holds(axes, *term, vertex) == Membership::Inside);
    if held {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

#[test]
fn a_composite_of_maps_is_a_substitution_of_polynomials()
{
    // `g ∘ f` is dual to the homomorphism of `g` followed by that of `f`.
    let pairs = enumerated();
    for &(first, middle) in &pairs {
        for &(_, last) in pairs.iter().filter(|&&(source, _)| source == middle) {
            let pairs_tried = count(first, middle).0.saturating_mul(count(middle, last).0);
            if pairs_tried > 1 << 15_u32 {
                continue;
            }
            check_composites(first, middle, last);
        }
    }
}

#[test]
fn the_crate_decides_every_monotone_polynomial()
{
    // The crate admits every polynomial as a formula. The corner term of a
    // vertex entails a polynomial exactly when its table holds at the vertex,
    // and between two polynomials entailment is the inclusion of their
    // tables. A formula that pins a vertex below the top holds a lower point,
    // and beside a join of terms it stays refused.
    for (size, &elements) in DEDEKIND.iter().enumerate() {
        let axes = GeneratorCount::from(size);
        let polynomials = antichains(axes);
        assert_eq!(polynomials.len(), elements);
        let tables: Vec<Table> = polynomials
            .iter()
            .map(|polynomial| table_of(axes, polynomial))
            .collect();
        let top = vertices(axes).last().expect("a vertex");
        for (polynomial, &table) in polynomials.iter().zip(&tables) {
            let whole = polynomial_formula(axes, polynomial);
            for vertex in vertices(axes) {
                assert_eq!(
                    holds_by_terms(axes, polynomial, vertex),
                    holds(table, vertex)
                );
                let corner =
                    polynomial_formula(axes, &Polynomial::term(Term::from(u64::from(vertex))));
                assert_eq!(
                    entailed(axes, corner, whole.clone()),
                    Ok(holds(table, vertex)),
                    "{vertex:?} against {polynomial:?}"
                );
                let pinned = entailed(axes, vertex_formula(axes, vertex), whole.clone());
                if polynomial.terms().len() > 1 && vertex != top {
                    assert!(
                        matches!(pinned, Err(ShapeError::Disjunction(_))),
                        "{vertex:?} against {polynomial:?}"
                    );
                }
                else {
                    assert_eq!(pinned, Ok(holds(table, vertex)));
                }
            }
        }
        for (lower, &lower_table) in polynomials.iter().zip(&tables) {
            for (upper, &upper_table) in polynomials.iter().zip(&tables) {
                let lower_bits = u64::from(lower_table);
                let order = if lower_bits & u64::from(upper_table) == lower_bits {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                };
                let answer = entailed(
                    axes,
                    polynomial_formula(axes, lower),
                    polynomial_formula(axes, upper),
                );
                assert_eq!(answer, Ok(order), "{lower:?} below {upper:?}");
            }
        }
    }
}
