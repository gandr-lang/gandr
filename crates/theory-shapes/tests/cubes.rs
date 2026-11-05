//! Monotone maps between cubes as homomorphisms of free distributive
//! lattices, set against the face formulas that the crate decides.
//!
//! The cube on `n` axes is the set of vertices `{0, 1}ⁿ`, ordered axis by
//! axis. It is the spectrum of the free distributive lattice on `n`
//! generators. An element of that lattice is a polynomial in the generators.
//! Its normal form is the antichain of its terms, and a term is a meet of
//! generators. A polynomial reads as a monotone function on the cube. It
//! holds at a vertex when one of its terms holds there.
//!
//! A monotone map from the cube on `n` axes to the cube on `m` axes is dual
//! to a homomorphism from the lattice on `m` generators to the lattice on `n`.
//! The homomorphism sends each generator to the polynomial of one coordinate
//! of the map. The suite enumerates both sides and checks that each round
//! trip is the identity. It also checks that a composite of maps is dual to
//! the substitution of polynomials in the other order.
//!
//! A polynomial is also a face formula over carriers of two points, with the
//! atom `xᵢ ∈ {1}` for each generator. The crate decides such a formula only
//! when it is `⊥` or one term. A join of terms on two variables is a
//! disjunction across variables, and the crate refuses it. The suite checks
//! the crate's decisions against the truth tables wherever the crate decides.
//! It also counts the polynomials that the crate refuses.
//!
//! Every value here is a bit set in one machine word, so the enumeration
//! allocates nothing. Cubes have at most four axes, so a vertex set and a
//! term set each fit in sixteen bits.

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

/// The word of type `$word` with only the bit at `$index` set.
macro_rules! bit {
    ($word:ty, $index:expr) => {
        <$word>::from(1_u8)
            .checked_shl(u32::try_from($index).expect("a small index"))
            .expect("an index below the word's width")
    };
}

/// `Inside` when the condition holds, and `Outside` otherwise.
macro_rules! membership {
    ($inside:expr) => {
        if $inside {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    };
}

/// The Dedekind numbers: how many monotone functions a cube of up to four
/// axes carries, which is how many elements its free distributive lattice
/// has.
const DEDEKIND: [usize; 5] = [2, 3, 6, 20, 168];

/// The number of axes of a cube, which is the number of generators of its
/// lattice. At most four.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Axes(usize);

/// One axis of a cube, which is one generator of its lattice.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Axis(usize);

/// A vertex of a cube: the mask of the axes at which it is `1`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Vertex(usize);

/// A term of a free distributive lattice: the mask of the generators it
/// meets. The empty term is `⊤`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Term(usize);

/// A function on the vertices of a cube as its truth table: the set of the
/// vertices where it holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Table(u64);

/// A polynomial of a free distributive lattice in normal form: the set of
/// its terms, no term within another. The empty set is `⊥`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Polynomial(u64);

/// A homomorphism of free distributive lattices: the polynomial that each
/// generator of its source goes to, by generator. The entries past the
/// source's generators are `⊥`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Homomorphism([Polynomial; 4]);

/// A map between cubes as its truth table: the image of each vertex of its
/// source, by vertex. The entries past the source's vertices are the zero
/// vertex.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Map([Vertex; 16]);

/// How many maps an enumeration visits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
struct Maps(usize);

impl Axes
{
    /// The vertices of the cube, in mask order.
    ///
    /// # Specification
    /// trivial.
    fn vertices(self) -> impl Iterator<Item = Vertex>
    {
        (0 .. bit!(usize, self.0)).map(Vertex)
    }

    /// The axes of the cube, in order.
    ///
    /// # Specification
    /// trivial.
    fn axes(self) -> impl Iterator<Item = Axis>
    {
        (0 .. self.0).map(Axis)
    }
}

impl Vertex
{
    /// Whether the vertex is `1` on an axis.
    ///
    /// # Specification
    /// trivial.
    fn on(
        self,
        axis: Axis,
    ) -> Membership
    {
        membership!(self.0 & bit!(usize, axis.0) != 0)
    }

    /// The vertex that is also `1` on an axis.
    ///
    /// # Specification
    /// trivial.
    fn raised(
        self,
        axis: Axis,
    ) -> Self
    {
        Self(self.0 | bit!(usize, axis.0))
    }

    /// Whether this vertex is below another, axis by axis.
    ///
    /// # Specification
    /// trivial.
    fn below(
        self,
        other: Self,
    ) -> Membership
    {
        membership!(self.0 & other.0 == self.0)
    }
}

impl Term
{
    /// Whether the term holds at a vertex: every generator it meets is `1`
    /// there.
    ///
    /// # Specification
    /// trivial.
    fn holds_at(
        self,
        vertex: Vertex,
    ) -> Membership
    {
        membership!(self.0 & vertex.0 == self.0)
    }

    /// Whether the term meets a generator.
    ///
    /// # Specification
    /// trivial.
    fn meets(
        self,
        axis: Axis,
    ) -> Membership
    {
        membership!(self.0 & bit!(usize, axis.0) != 0)
    }

    /// Whether every generator this term meets is one that `other` meets.
    ///
    /// # Specification
    /// trivial.
    fn within(
        self,
        other: Self,
    ) -> Membership
    {
        membership!(self.0 & other.0 == self.0)
    }
}

impl Table
{
    /// Whether the table holds at a vertex.
    ///
    /// # Specification
    /// trivial.
    fn at(
        self,
        vertex: Vertex,
    ) -> Membership
    {
        membership!(self.0 & bit!(u64, vertex.0) != 0)
    }

    /// The table that also holds at a vertex.
    ///
    /// # Specification
    /// trivial.
    fn with(
        self,
        vertex: Vertex,
    ) -> Self
    {
        Self(self.0 | bit!(u64, vertex.0))
    }
}

impl Polynomial
{
    /// `⊥`, the join of no term.
    const BOTTOM: Self = Self(0);
    /// `⊤`, the empty term alone.
    const TOP: Self = Self(1);

    /// The set that also holds a term.
    ///
    /// # Specification
    /// trivial.
    fn with(
        self,
        term: Term,
    ) -> Self
    {
        Self(self.0 | bit!(u64, term.0))
    }

    /// The terms of the set, in mask order.
    ///
    /// # Specification
    /// trivial.
    fn terms(self) -> impl Iterator<Item = Term>
    {
        let mut rest = self.0;
        core::iter::from_fn(move || {
            if rest == 0 {
                return None;
            }
            let lowest = usize::try_from(rest.trailing_zeros()).expect("a small index");
            rest ^= bit!(u64, lowest);
            Some(Term(lowest))
        })
    }

    /// The normal form of a set of terms by absorption: each term that no
    /// other term of the set is within.
    ///
    /// # Specification
    /// trivial.
    fn normal(self) -> Self
    {
        self.terms()
            .filter(|term| {
                self.terms()
                    .all(|other| other == *term || other.within(*term) == Membership::Outside)
            })
            .fold(Self::BOTTOM, Self::with)
    }

    /// The meet of two polynomials: each term of one met with each term of
    /// the other, in normal form.
    ///
    /// # Specification
    /// trivial.
    fn meet(
        self,
        other: Self,
    ) -> Self
    {
        self.terms()
            .flat_map(|outer| other.terms().map(move |inner| Term(outer.0 | inner.0)))
            .fold(Self::BOTTOM, Self::with)
            .normal()
    }

    /// The join of two polynomials: their terms together, in normal form.
    ///
    /// # Specification
    /// trivial.
    fn join(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 | other.0).normal()
    }
}

impl Map
{
    /// The image of a vertex.
    ///
    /// # Specification
    /// trivial.
    fn image(
        &self,
        vertex: Vertex,
    ) -> Vertex
    {
        self.0[vertex.0]
    }
}

/// The truth table of a polynomial: the vertices where one of its terms
/// holds.
///
/// # Specification
/// trivial.
fn table_of(
    axes: Axes,
    polynomial: Polynomial,
) -> Table
{
    axes.vertices()
        .filter(|vertex| {
            polynomial
                .terms()
                .any(|term| term.holds_at(*vertex) == Membership::Inside)
        })
        .fold(Table(0), Table::with)
}

/// The polynomial of a truth table: its minimal vertices, read as terms.
///
/// # Specification
/// trivial.
fn polynomial_of(
    axes: Axes,
    table: Table,
) -> Polynomial
{
    axes.vertices()
        .filter(|vertex| {
            table.at(*vertex) == Membership::Inside
                && axes.vertices().all(|other| {
                    other == *vertex
                        || table.at(other) == Membership::Outside
                        || other.below(*vertex) == Membership::Outside
                })
        })
        .map(|vertex| Term(vertex.0))
        .fold(Polynomial::BOTTOM, Polynomial::with)
}

/// Every monotone truth table on a cube, in mask order: each table that
/// holds above every vertex where it holds.
///
/// # Specification
/// trivial.
fn monotone_tables(axes: Axes) -> Vec<Table>
{
    let last = bit!(u64, bit!(usize, axes.0)).saturating_sub(1);
    (0 ..= last)
        .map(Table)
        .filter(|table| {
            axes.vertices().all(|lower| {
                table.at(lower) == Membership::Outside
                    || axes.vertices().all(|upper| {
                        lower.below(upper) == Membership::Outside
                            || table.at(upper) == Membership::Inside
                    })
            })
        })
        .collect()
}

/// Every polynomial in normal form, in mask order: each set of terms that is
/// its own normal form. Written apart from the truth tables.
///
/// # Specification
/// trivial.
fn antichains(axes: Axes) -> Vec<Polynomial>
{
    let last = bit!(u64, bit!(usize, axes.0)).saturating_sub(1);
    (0 ..= last)
        .map(Polynomial)
        .filter(|polynomial| polynomial.normal() == *polynomial)
        .collect()
}

/// The image of a polynomial under the homomorphism `images`: the join over
/// its terms of the meet of the images of each term's generators.
///
/// # Specification
/// trivial.
fn substitute(
    polynomial: Polynomial,
    images: &Homomorphism,
) -> Polynomial
{
    polynomial
        .terms()
        .map(|term| {
            images
                .0
                .iter()
                .enumerate()
                .filter(|&(generator, _)| term.meets(Axis(generator)) == Membership::Inside)
                .fold(Polynomial::TOP, |met, (_, image)| met.meet(*image))
        })
        .fold(Polynomial::BOTTOM, Polynomial::join)
}

/// The homomorphism dual to a map of cubes: each generator of the target's
/// lattice goes to the polynomial of the map's coordinate on that axis.
///
/// # Specification
/// trivial.
fn homomorphism_of(
    source: Axes,
    target: Axes,
    map: &Map,
) -> Homomorphism
{
    let mut images = [Polynomial::BOTTOM; 4];
    for axis in target.axes() {
        let coordinate = source
            .vertices()
            .filter(|vertex| map.image(*vertex).on(axis) == Membership::Inside)
            .fold(Table(0), Table::with);
        images[axis.0] = polynomial_of(source, coordinate);
    }
    Homomorphism(images)
}

/// The map of cubes dual to a homomorphism: each vertex goes to the vertex
/// that is `1` on each axis whose generator's image holds at the vertex.
///
/// # Specification
/// trivial.
fn map_of(
    source: Axes,
    target: Axes,
    homomorphism: &Homomorphism,
) -> Map
{
    let mut images = [Vertex(0); 16];
    for vertex in source.vertices() {
        images[vertex.0] = target
            .axes()
            .filter(|axis| {
                homomorphism.0[axis.0]
                    .terms()
                    .any(|term| term.holds_at(vertex) == Membership::Inside)
            })
            .fold(Vertex(0), Vertex::raised);
    }
    Map(images)
}

/// Whether a map of cubes is monotone: it keeps every pair of vertices in
/// order.
///
/// # Specification
/// trivial.
fn monotone(
    source: Axes,
    map: &Map,
) -> Membership
{
    membership!(source.vertices().all(|lower| {
        source.vertices().all(|upper| {
            lower.below(upper) == Membership::Outside
                || map.image(lower).below(map.image(upper)) == Membership::Inside
        })
    }))
}

/// Visits each map from the cube on `source` axes to the cube on `target`
/// axes whose coordinates are drawn from `coordinates`, one tuple at a time,
/// and returns how many it visited.
///
/// # Specification
/// trivial.
fn each_map(
    source: Axes,
    target: Axes,
    coordinates: &[Table],
    mut visit: impl FnMut(&Map),
) -> Maps
{
    let mut digits = [0_usize; 4];
    let mut visited = Maps(0);
    loop {
        let mut images = [Vertex(0); 16];
        for axis in target.axes() {
            let coordinate = coordinates[digits[axis.0]];
            for vertex in source.vertices() {
                if coordinate.at(vertex) == Membership::Inside {
                    images[vertex.0] = images[vertex.0].raised(axis);
                }
            }
        }
        visit(&Map(images));
        visited = Maps(visited.0.saturating_add(1));
        let mut axis = 0_usize;
        loop {
            if axis == target.0 {
                return visited;
            }
            digits[axis] = digits[axis].saturating_add(1);
            if digits[axis] < coordinates.len() {
                break;
            }
            digits[axis] = 0;
            axis = axis.saturating_add(1);
        }
    }
}

/// Visits each homomorphism from the lattice on `target` generators whose
/// images are drawn from `polynomials`, one tuple at a time, and returns how
/// many it visited.
///
/// # Specification
/// trivial.
fn each_homomorphism(
    target: Axes,
    polynomials: &[Polynomial],
    mut visit: impl FnMut(&Homomorphism),
) -> Maps
{
    let mut digits = [0_usize; 4];
    let mut visited = Maps(0);
    loop {
        let mut images = [Polynomial::BOTTOM; 4];
        for axis in target.axes() {
            images[axis.0] = polynomials[digits[axis.0]];
        }
        visit(&Homomorphism(images));
        visited = Maps(visited.0.saturating_add(1));
        let mut axis = 0_usize;
        loop {
            if axis == target.0 {
                return visited;
            }
            digits[axis] = digits[axis].saturating_add(1);
            if digits[axis] < polynomials.len() {
                break;
            }
            digits[axis] = 0;
            axis = axis.saturating_add(1);
        }
    }
}

/// How many monotone maps go from the cube on `source` axes to the cube on
/// `target` axes: the Dedekind number of `source` to the power `target`.
///
/// # Specification
/// trivial.
fn count(
    source: Axes,
    target: Axes,
) -> Maps
{
    let width = u32::try_from(target.0).expect("a small cube");
    Maps(
        DEDEKIND
            .get(source.0)
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
fn enumerated() -> Vec<(Axes, Axes)>
{
    (0 ..= 4_usize)
        .flat_map(|source| (0 ..= 4_usize).map(move |target| (Axes(source), Axes(target))))
        .filter(|&(source, target)| count(source, target) <= Maps(1 << 18))
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
    axes: Axes,
    vertex: Vertex,
) -> Formula
{
    let two = PointCount::from(2_usize);
    conjunction(
        axes.axes()
            .map(|axis| {
                let value = match vertex.on(axis) {
                    Membership::Inside => Point::from(1_usize),
                    Membership::Outside => Point::from(0_usize),
                };
                Node::Member(
                    Variable::from(axis.0),
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
    axes: Axes,
    polynomial: Polynomial,
) -> Formula
{
    let one =
        Subshape::new(PointCount::from(2_usize), &[Point::from(1_usize)]).expect("a point of two");
    let mut nodes: Vec<Node> = Vec::new();
    let mut root: Option<usize> = None;
    for term in polynomial.terms() {
        let first = nodes.len();
        let mut generators = axes
            .axes()
            .filter(|axis| term.meets(*axis) == Membership::Inside)
            .peekable();
        if generators.peek().is_none() {
            nodes.push(Node::Top);
        }
        for axis in generators {
            nodes.push(Node::Member(Variable::from(axis.0), one.clone()));
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

/// Decides `premise ⊢ conclusion` over carriers of two points with the
/// crate's entailment, validates the evidence, and reads the answer as
/// membership. A query outside the crate's band is refused as admission
/// refuses it.
///
/// # Specification
/// trivial.
fn entailed(
    axes: Axes,
    premise: Formula,
    conclusion: Formula,
) -> Result<Membership, ShapeError>
{
    let problem = Problem::new(vec![PointCount::from(2_usize); axes.0], premise, conclusion)?;
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

#[test]
fn the_monotone_tables_are_the_polynomials_one_to_one()
{
    // Both sides are enumerated apart, and each has the Dedekind number of
    // elements.
    for (size, dedekind) in DEDEKIND.into_iter().enumerate() {
        let axes = Axes(size);
        let tables = monotone_tables(axes);
        let polynomials = antichains(axes);
        assert_eq!((tables.len(), polynomials.len()), (dedekind, dedekind));
        for table in &tables {
            assert_eq!(table_of(axes, polynomial_of(axes, *table)), *table);
        }
        for polynomial in &polynomials {
            assert_eq!(
                polynomial_of(axes, table_of(axes, *polynomial)),
                *polynomial
            );
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
            assert_eq!(monotone(source, map), Membership::Inside);
            let homomorphism = homomorphism_of(source, target, map);
            assert_eq!(map_of(source, target, &homomorphism), *map);
        });
        // From the homomorphisms: each tuple of polynomials gives a monotone
        // map, which reads back to it.
        let homomorphisms = each_homomorphism(target, &polynomials, |homomorphism| {
            let map = map_of(source, target, homomorphism);
            assert_eq!(monotone(source, &map), Membership::Inside);
            assert_eq!(homomorphism_of(source, target, &map), *homomorphism);
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
        let vertices = bit!(usize, source.0);
        let images = bit!(usize, target.0);
        let tried = images.checked_pow(u32::try_from(vertices).expect("a small cube"));
        if tried.is_none_or(|tried| tried > bit!(usize, 16_usize)) {
            continue;
        }
        let mut digits = [Vertex(0); 16];
        let mut monotone_maps = Maps(0);
        'tables: loop {
            if monotone(source, &Map(digits)) == Membership::Inside {
                monotone_maps = Maps(monotone_maps.0.saturating_add(1));
            }
            for vertex in source.vertices() {
                let next = digits[vertex.0].0.saturating_add(1);
                if next < images {
                    digits[vertex.0] = Vertex(next);
                    continue 'tables;
                }
                digits[vertex.0] = Vertex(0);
            }
            break;
        }
        assert_eq!(
            monotone_maps,
            count(source, target),
            "{source:?} to {target:?}"
        );
    }
}

#[test]
fn a_composite_of_maps_is_a_substitution_of_polynomials()
{
    // `g ∘ f` is dual to the homomorphism that substitutes the images under
    // `f`'s homomorphism into the images under `g`'s.
    let pairs = enumerated();
    for &(first, middle) in &pairs {
        for &(_, last) in pairs.iter().filter(|&&(source, _)| source == middle) {
            let pairs_tried = count(first, middle).0.saturating_mul(count(middle, last).0);
            if pairs_tried > bit!(usize, 15_usize) {
                continue;
            }
            let before = monotone_tables(first);
            let afters = monotone_tables(middle);
            let _maps = each_map(first, middle, &before, |before| {
                let inner = homomorphism_of(first, middle, before);
                let _maps = each_map(middle, last, &afters, |after| {
                    let outer = homomorphism_of(middle, last, after);
                    let mut composite = [Vertex(0); 16];
                    for vertex in first.vertices() {
                        composite[vertex.0] = after.image(before.image(vertex));
                    }
                    let mut substituted = [Polynomial::BOTTOM; 4];
                    for axis in last.axes() {
                        substituted[axis.0] = substitute(outer.0[axis.0], &inner);
                    }
                    assert_eq!(
                        homomorphism_of(first, last, &Map(composite)),
                        Homomorphism(substituted)
                    );
                });
            });
        }
    }
}

#[test]
fn the_crate_decides_a_polynomial_only_when_it_is_one_term()
{
    // At each vertex the crate decides each term of a polynomial, and the
    // join of those answers is the truth table. The crate admits the whole
    // polynomial only when it is `⊥` or one term, and then it agrees with the
    // table. It refuses the rest as disjunctions across variables. The ones
    // it decides are the join-irreducible elements and `⊥`, `2ⁿ + 1` of the
    // Dedekind number.
    for (size, decided) in [2_usize, 3, 5, 9, 17].into_iter().enumerate() {
        let axes = Axes(size);
        let polynomials = antichains(axes);
        let mut admitted = 0_usize;
        for &polynomial in &polynomials {
            let table = table_of(axes, polynomial);
            // The count stops at two terms. Two terms already decide the band.
            let terms = polynomial.terms().take(2).count();
            for vertex in axes.vertices() {
                let by_terms = membership!(polynomial.terms().any(|term| {
                    let single = polynomial_formula(axes, Polynomial::BOTTOM.with(term));
                    entailed(axes, vertex_formula(axes, vertex), single) == Ok(Membership::Inside)
                }));
                assert_eq!(by_terms, table.at(vertex));
                let whole = polynomial_formula(axes, polynomial);
                match entailed(axes, vertex_formula(axes, vertex), whole) {
                    Ok(answer) => {
                        assert!(terms <= 1, "{polynomial:?} is admitted");
                        assert_eq!(answer, table.at(vertex));
                    },
                    Err(ShapeError::Disjunction(_)) => {
                        assert!(terms > 1, "{polynomial:?} is refused");
                    },
                    Err(error) => panic!("{polynomial:?} is refused by {error:?}"),
                }
            }
            if terms <= 1 {
                admitted = admitted.saturating_add(1);
            }
        }
        assert_eq!(admitted, decided);
        // Between the polynomials it decides, the crate's entailment is the
        // order of the lattice.
        let singles: Vec<Polynomial> = polynomials
            .iter()
            .copied()
            .filter(|polynomial| polynomial.terms().take(2).count() <= 1)
            .collect();
        for &lower in &singles {
            for &upper in &singles {
                let below = membership!(
                    table_of(axes, lower).0 & table_of(axes, upper).0 == table_of(axes, lower).0
                );
                let answer = entailed(
                    axes,
                    polynomial_formula(axes, lower),
                    polynomial_formula(axes, upper),
                );
                assert_eq!(answer, Ok(below), "{lower:?} below {upper:?}");
            }
        }
    }
}
