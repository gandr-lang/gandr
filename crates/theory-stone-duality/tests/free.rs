//! The free distributive lattice against its truth tables, and its
//! homomorphisms against the maps of cubes they are dual to.
//!
//! The reference readings here are written apart from the crate: a table is
//! monotone when it holds above every vertex where it holds, and a map of
//! cubes is monotone when it keeps every pair of vertices in order.

use gandr_theory_stone_duality::Comparison;
use gandr_theory_stone_duality::CubeMap;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Generator;
use gandr_theory_stone_duality::GeneratorCount;
use gandr_theory_stone_duality::Homomorphism;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::Polynomial;
use gandr_theory_stone_duality::Table;
use gandr_theory_stone_duality::Term;
use gandr_theory_stone_duality::Vertex;

/// The Dedekind numbers: the monotone tables on the cubes of up to four axes.
const DEDEKIND: [usize; 5] = [2, 3, 6, 20, 168];

/// Whether a table or a map keeps the order of the cube.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Order
{
    /// Every pair of vertices keeps its order.
    Kept,
    /// Some pair of vertices loses its order.
    Broken,
}

/// The word with only the bit at `index` set.
///
/// # Specification
/// trivial.
fn bit(index: Vertex) -> Table
{
    let shift = u32::try_from(u64::from(index)).expect("a small vertex");
    Table::from(1_u64.checked_shl(shift).expect("a vertex below a word"))
}

/// The table that holds at every vertex of the cube on `axes` axes.
///
/// # Specification
/// trivial.
fn whole(axes: GeneratorCount) -> Table
{
    let vertices = 1_u32
        .checked_shl(u32::try_from(usize::from(axes)).expect("a small cube"))
        .expect("a small cube");
    Table::from(
        u64::MAX
            .checked_shr(64_u32.checked_sub(vertices).expect("a small cube"))
            .expect("a small cube"),
    )
}

/// The vertices of the cube on `axes` axes, read from its bits.
///
/// # Specification
/// trivial.
fn vertices(axes: GeneratorCount) -> impl Iterator<Item = Vertex>
{
    let count = u64::from(whole(axes)).count_ones();
    (0 .. u64::from(count)).map(Vertex::from)
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

/// Whether one vertex lies below another, axis by axis.
///
/// # Specification
/// trivial.
fn below(
    lower: Vertex,
    upper: Vertex,
) -> Comparison
{
    if u64::from(lower) & u64::from(upper) == u64::from(lower) {
        Comparison::Below
    }
    else {
        Comparison::NotBelow
    }
}

/// Whether a table is monotone, by every pair of vertices.
///
/// # Specification
/// trivial.
fn monotone(
    axes: GeneratorCount,
    table: Table,
) -> Order
{
    let kept = vertices(axes).all(|lower| {
        vertices(axes).all(|upper| {
            below(lower, upper) == Comparison::NotBelow
                || holds(table, lower) == Membership::Outside
                || holds(table, upper) == Membership::Inside
        })
    });
    if kept { Order::Kept } else { Order::Broken }
}

/// Every table on the cube of `axes` axes, in mask order.
///
/// # Specification
/// trivial.
fn tables(axes: GeneratorCount) -> impl Iterator<Item = Table>
{
    (0 ..= u64::from(whole(axes))).map(Table::from)
}

/// The polynomial of each monotone table on the cube of `axes` axes.
///
/// # Specification
/// trivial.
fn polynomials(axes: GeneratorCount) -> Vec<Polynomial>
{
    tables(axes)
        .filter(|table| monotone(axes, *table) == Order::Kept)
        .map(|table| Polynomial::from_table(axes, table).expect("a monotone table"))
        .collect()
}

/// Every table of vertex images from the cube on `source` axes to the cube on
/// `target` axes, by an odometer over the vertices.
///
/// # Specification
/// trivial.
fn vertex_tables(
    source: GeneratorCount,
    target: GeneratorCount,
) -> Vec<Vec<Vertex>>
{
    let width = vertices(source).count();
    let base = vertices(target).count();
    let mut digits = vec![0_usize; width];
    let mut all = Vec::new();
    'tables: loop {
        all.push(
            digits
                .iter()
                .map(|digit| Vertex::from(u64::try_from(*digit).expect("a small vertex")))
                .collect(),
        );
        for digit in &mut digits {
            *digit = digit.saturating_add(1);
            if *digit < base {
                continue 'tables;
            }
            *digit = 0;
        }
        return all;
    }
}

/// Whether a table of vertex images keeps every pair of vertices in order.
///
/// # Specification
/// trivial.
fn keeps_order(images: &[Vertex]) -> Order
{
    let kept = images.iter().enumerate().all(|(lower, low)| {
        images.iter().enumerate().all(|(upper, high)| {
            let lower = Vertex::from(u64::try_from(lower).expect("a small vertex"));
            let upper = Vertex::from(u64::try_from(upper).expect("a small vertex"));
            below(lower, upper) == Comparison::NotBelow || below(*low, *high) == Comparison::Below
        })
    });
    if kept { Order::Kept } else { Order::Broken }
}

/// Checks every table of vertex images between two cubes: the monotone ones
/// are admitted, read as homomorphisms and back, and counted as tuples of
/// monotone coordinates.
///
/// # Specification
/// trivial.
fn check_maps(
    source: GeneratorCount,
    target: GeneratorCount,
)
{
    let mut admitted = 0_usize;
    for images in vertex_tables(source, target) {
        let ordered = keeps_order(&images);
        match CubeMap::new(source, target, images) {
            Ok(map) => {
                admitted = admitted.saturating_add(1);
                assert_eq!(ordered, Order::Kept);
                let homomorphism = Homomorphism::of_cube_map(&map).expect("a homomorphism");
                assert_eq!(
                    (homomorphism.source(), homomorphism.target()),
                    (target, source)
                );
                assert_eq!(homomorphism.cube_map(), Ok(map));
            },
            Err(DualityError::CubeMapNotMonotone(..)) => assert_eq!(ordered, Order::Broken),
            Err(error) => panic!("refused by {error:?}"),
        }
    }
    let dedekind = DEDEKIND[usize::from(source)];
    let power = u32::try_from(usize::from(target)).expect("a small cube");
    assert_eq!(Some(admitted), dedekind.checked_pow(power));
}

/// The homomorphism to the lattice on `target` generators that sends each
/// generator to its image in `images`.
///
/// # Specification
/// trivial.
fn homomorphism_of(
    target: GeneratorCount,
    images: &[&Polynomial],
) -> Homomorphism
{
    let owned: Vec<Polynomial> = images.iter().map(|image| (*image).clone()).collect();
    Homomorphism::new(target, owned).expect("a homomorphism")
}

/// Checks every homomorphism from the lattice on `source` generators to the
/// lattice on `target` generators: each reads back from its map of cubes.
///
/// # Specification
/// trivial.
fn check_homomorphisms(
    source: GeneratorCount,
    target: GeneratorCount,
)
{
    let images = polynomials(target);
    let mut picked: Vec<&Polynomial> = Vec::with_capacity(usize::from(source));
    let mut digits = vec![0_usize; usize::from(source)];
    'homomorphisms: loop {
        picked.clear();
        picked.extend(digits.iter().map(|digit| &images[*digit]));
        let homomorphism = homomorphism_of(target, &picked);
        let map = homomorphism.cube_map().expect("a map");
        assert_eq!(Homomorphism::of_cube_map(&map), Ok(homomorphism));
        for digit in &mut digits {
            *digit = digit.saturating_add(1);
            if *digit < images.len() {
                continue 'homomorphisms;
            }
            *digit = 0;
        }
        return;
    }
}

/// Checks that a composite of maps of cubes is dual to the composite of their
/// homomorphisms, in the other order.
///
/// # Specification
/// trivial.
fn check_composites(
    first: GeneratorCount,
    middle: GeneratorCount,
    last: GeneratorCount,
)
{
    let before: Vec<CubeMap> = vertex_tables(first, middle)
        .into_iter()
        .filter_map(|images| CubeMap::new(first, middle, images).ok())
        .collect();
    let afters: Vec<CubeMap> = vertex_tables(middle, last)
        .into_iter()
        .filter_map(|images| CubeMap::new(middle, last, images).ok())
        .collect();
    let identity = Homomorphism::identity(first).expect("an identity");
    for before in &before {
        let inner = Homomorphism::of_cube_map(before).expect("a homomorphism");
        assert_eq!(inner.followed_by(&identity).as_ref(), Ok(&inner));
        for after in &afters {
            let outer = Homomorphism::of_cube_map(after).expect("a homomorphism");
            let composite = before.followed_by(after).expect("a composite");
            assert_eq!(
                Homomorphism::of_cube_map(&composite),
                outer.followed_by(&inner)
            );
        }
    }
}

#[test]
fn generators_and_terms_are_checked_by_index()
{
    let last = Term::generator(Generator::from(63)).expect("a generator in the word");
    assert_eq!(u64::from(last), 1_u64 << 63_u32);
    assert_eq!(usize::from(last.reach()), 64);
    assert_eq!(usize::from(Term::TOP.reach()), 0);
    assert_eq!(
        Term::generator(Generator::from(64)),
        Err(DualityError::GeneratorOutside(Generator::from(64)))
    );
    assert_eq!(
        Polynomial::generator(Generator::from(64)),
        Err(DualityError::GeneratorOutside(Generator::from(64)))
    );
    let fifth = Polynomial::generator(Generator::from(5)).expect("a generator");
    assert_eq!(usize::from(fifth.reach()), 6);
    let fifth_term = Term::generator(Generator::from(5)).expect("a generator");
    assert!(fifth_term.generators().eq([Generator::from(5)]));
    // An image past the target, too many images and too wide a target.
    let second = Polynomial::generator(Generator::from(2)).expect("a generator");
    assert_eq!(
        Homomorphism::new(GeneratorCount::from(2), vec![second]),
        Err(DualityError::GeneratorOutside(Generator::from(2)))
    );
    assert_eq!(
        Homomorphism::new(GeneratorCount::from(65), Vec::new()),
        Err(DualityError::TooManyGenerators(GeneratorCount::from(65)))
    );
    assert_eq!(
        Homomorphism::new(GeneratorCount::from(1), vec![Polynomial::bottom(); 65]),
        Err(DualityError::TooManyGenerators(GeneratorCount::from(65)))
    );
}

/// A polynomial built again from its own terms by absorption, so the form
/// a table gives meets the form a list of terms gives.
///
/// # Specification
/// trivial.
fn rebuilt(polynomial: &Polynomial) -> Polynomial
{
    Polynomial::from_terms(polynomial.terms().to_vec())
}

#[test]
fn polynomials_and_monotone_tables_go_one_to_one()
{
    for (size, dedekind) in DEDEKIND.into_iter().enumerate() {
        let axes = GeneratorCount::from(size);
        let mut admitted = 0_usize;
        for table in tables(axes) {
            match Polynomial::from_table(axes, table) {
                Ok(polynomial) => {
                    admitted = admitted.saturating_add(1);
                    assert_eq!(monotone(axes, table), Order::Kept);
                    assert_eq!(polynomial.table(axes), Ok(table));
                    assert_eq!(rebuilt(&polynomial), polynomial);
                    for vertex in vertices(axes) {
                        assert_eq!(polynomial.holds_at(vertex), holds(table, vertex));
                    }
                },
                Err(DualityError::TableNotMonotone(lower, upper)) => {
                    assert_eq!(monotone(axes, table), Order::Broken);
                    assert_eq!(
                        (holds(table, lower), holds(table, upper)),
                        (Membership::Inside, Membership::Outside)
                    );
                    assert_eq!(below(lower, upper), Comparison::Below);
                    assert_eq!(
                        u64::from(lower).count_ones().checked_add(1),
                        Some(u64::from(upper).count_ones())
                    );
                },
                Err(error) => panic!("{table:?} on {size} axes refused by {error:?}"),
            }
        }
        assert_eq!(admitted, dedekind, "{size} axes");
    }
    let two = GeneratorCount::from(2);
    assert_eq!(
        Polynomial::from_table(two, Table::from(0b0001)),
        Err(DualityError::TableNotMonotone(
            Vertex::from(0),
            Vertex::from(1)
        ))
    );
    assert_eq!(
        Polynomial::from_table(GeneratorCount::from(1), Table::from(0b100)),
        Err(DualityError::VertexOutside(Vertex::from(2)))
    );
    let seven = GeneratorCount::from(7);
    assert_eq!(
        Polynomial::from_table(seven, Table::from(0)),
        Err(DualityError::TooWide(seven))
    );
    assert_eq!(
        Polynomial::top().table(seven),
        Err(DualityError::TooWide(seven))
    );
    let third = Polynomial::generator(Generator::from(3)).expect("a generator");
    assert_eq!(
        third.table(two),
        Err(DualityError::GeneratorOutside(Generator::from(3)))
    );
    assert_eq!(
        Polynomial::top().table(GeneratorCount::from(0)),
        Ok(Table::from(1))
    );
    assert_eq!(Polynomial::bottom().table(two), Ok(Table::from(0)));
}

#[test]
fn meet_join_and_order_follow_the_tables()
{
    let axes = GeneratorCount::from(3);
    let all = polynomials(axes);
    let tables: Vec<Table> = all
        .iter()
        .map(|polynomial| polynomial.table(axes).expect("a table"))
        .collect();
    for (left, left_table) in all.iter().zip(&tables) {
        assert_eq!(Polynomial::bottom().compare(left), Comparison::Below);
        assert_eq!(left.compare(&Polynomial::top()), Comparison::Below);
        for (right, right_table) in all.iter().zip(&tables) {
            let left_bits = u64::from(*left_table);
            let right_bits = u64::from(*right_table);
            assert_eq!(
                left.meet(right).table(axes),
                Ok(Table::from(left_bits & right_bits))
            );
            assert_eq!(
                left.join(right).table(axes),
                Ok(Table::from(left_bits | right_bits))
            );
            let order = if left_bits & right_bits == left_bits {
                Comparison::Below
            }
            else {
                Comparison::NotBelow
            };
            assert_eq!(left.compare(right), order);
            // The same pair spread past the cube's word takes the path of
            // terms, and it agrees with the path of tables.
            let (wide_left, wide_right) = (spread(left), spread(right));
            assert_eq!(wide_left.meet(&wide_right), spread(&left.meet(right)));
            assert_eq!(wide_left.join(&wide_right), spread(&left.join(right)));
            assert_eq!(wide_left.compare(&wide_right), order);
        }
    }
    // Every set of terms on three generators joins to the polynomial of its
    // table, so the normal form does not depend on the input.
    for chosen in tables_of_terms() {
        let mut table = Table::from(0);
        let mut joined = Polynomial::bottom();
        for term_vertex in vertices(axes) {
            if holds(chosen, term_vertex) == Membership::Outside {
                continue;
            }
            let term = Term::from(u64::from(term_vertex));
            joined = joined.join(&Polynomial::term(term));
            for vertex in vertices(axes) {
                if below(term_vertex, vertex) == Comparison::Below {
                    table = Table::from(u64::from(table) | u64::from(bit(vertex)));
                }
            }
        }
        assert_eq!(Ok(joined), Polynomial::from_table(axes, table));
    }
    // Absorption keeps the least terms, once each, in order.
    let normal = Polynomial::from_terms(vec![
        Term::from(0b011),
        Term::from(0b001),
        Term::from(0b001),
        Term::from(0b110),
    ]);
    assert_eq!(normal.terms(), &[Term::from(0b001), Term::from(0b110)]);
    assert_eq!(Polynomial::from_terms(Vec::new()), Polynomial::bottom());
}

/// A polynomial on three generators with its second and third generators
/// moved to six and seven, past the cube's word.
///
/// # Specification
/// trivial.
fn spread(polynomial: &Polynomial) -> Polynomial
{
    let moved: Vec<Term> = polynomial
        .terms()
        .iter()
        .map(|term| {
            let bits = u64::from(*term);
            Term::from((bits & 0b001) | ((bits & 0b110) << 5_u32))
        })
        .collect();
    Polynomial::from_terms(moved)
}

/// Every set of the eight terms on three generators, as a table over them.
///
/// # Specification
/// trivial.
fn tables_of_terms() -> impl Iterator<Item = Table>
{
    tables(GeneratorCount::from(3))
}

#[test]
fn cube_maps_and_homomorphisms_go_one_to_one()
{
    for (source, target) in [(0, 2), (1, 1), (1, 3), (2, 2), (2, 3), (3, 1), (3, 2)] {
        check_maps(GeneratorCount::from(source), GeneratorCount::from(target));
    }
    for (source, target) in [(1, 2), (2, 1), (2, 2)] {
        check_homomorphisms(GeneratorCount::from(source), GeneratorCount::from(target));
    }
    let one = GeneratorCount::from(1);
    assert_eq!(
        CubeMap::new(one, one, vec![Vertex::from(1), Vertex::from(0)]),
        Err(DualityError::CubeMapNotMonotone(
            Vertex::from(0),
            Vertex::from(1)
        ))
    );
    assert_eq!(
        CubeMap::new(one, one, vec![Vertex::from(0)]),
        Err(DualityError::ImageCount)
    );
    assert_eq!(
        CubeMap::new(one, one, vec![Vertex::from(0), Vertex::from(2)]),
        Err(DualityError::VertexOutside(Vertex::from(2)))
    );
    let seven = GeneratorCount::from(7);
    assert_eq!(
        CubeMap::new(seven, one, Vec::new()),
        Err(DualityError::TooWide(seven))
    );
    let identity =
        CubeMap::new(one, one, vec![Vertex::from(0), Vertex::from(1)]).expect("the identity");
    assert_eq!(identity.image(Vertex::from(1)), Ok(Vertex::from(1)));
    assert_eq!(
        identity.image(Vertex::from(2)),
        Err(DualityError::VertexOutside(Vertex::from(2)))
    );
    let wide = Homomorphism::new(one, vec![Polynomial::bottom(); 7]).expect("a homomorphism");
    assert_eq!(wide.cube_map(), Err(DualityError::TooWide(seven)));
}

#[test]
fn substitution_composes_homomorphisms()
{
    for (first, middle, last) in [(1, 1, 2), (1, 2, 1), (2, 1, 2), (2, 2, 2), (2, 2, 1)] {
        check_composites(
            GeneratorCount::from(first),
            GeneratorCount::from(middle),
            GeneratorCount::from(last),
        );
    }
    let one = GeneratorCount::from(1);
    let two = GeneratorCount::from(2);
    let zeroth = Polynomial::generator(Generator::from(0)).expect("a generator");
    let projection = Homomorphism::new(two, vec![zeroth]).expect("a homomorphism");
    let second = Polynomial::generator(Generator::from(1)).expect("a generator");
    assert_eq!(
        projection.apply(&second),
        Err(DualityError::GeneratorOutside(Generator::from(1)))
    );
    assert_eq!(
        projection.apply(&Polynomial::bottom()),
        Ok(Polynomial::bottom())
    );
    assert_eq!(projection.apply(&Polynomial::top()), Ok(Polynomial::top()));
    assert_eq!(
        projection.followed_by(&projection),
        Err(DualityError::ImageCount)
    );
    let map = CubeMap::new(one, two, vec![Vertex::from(0), Vertex::from(3)]).expect("a map");
    assert_eq!(map.followed_by(&map), Err(DualityError::ImageCount));
    // Into the lattice on eight generators, past the cube's word.
    let eight = GeneratorCount::from(8);
    let generator =
        |index: usize| Polynomial::generator(Generator::from(index)).expect("a generator");
    let wide = Homomorphism::new(eight, vec![
        generator(6).join(&generator(7)),
        generator(0).meet(&generator(7)),
    ])
    .expect("a homomorphism");
    let both = generator(0).meet(&generator(1));
    assert_eq!(
        wide.apply(&both),
        Ok(Polynomial::from_terms(vec![Term::from(0b1000_0001)]))
    );
    assert_eq!(
        wide.apply(&generator(0).join(&generator(1))),
        Ok(generator(6).join(&generator(7)))
    );
    assert_eq!(
        wide.apply(&generator(2)),
        Err(DualityError::GeneratorOutside(Generator::from(2)))
    );
    let swap: Vec<Polynomial> = (0 .. 8_usize)
        .map(|index| match index {
            6 => generator(7),
            7 => generator(6),
            other => generator(other),
        })
        .collect();
    let swap = Homomorphism::new(eight, swap).expect("a homomorphism");
    let swapped = Homomorphism::new(eight, vec![
        generator(7).join(&generator(6)),
        generator(0).meet(&generator(6)),
    ]);
    assert_eq!(wide.followed_by(&swap), swapped);
    let identity = Homomorphism::identity(eight).expect("an identity");
    assert_eq!(wide.followed_by(&identity).as_ref(), Ok(&wide));
}
