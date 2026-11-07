//! The simplices of a triangle as a complex, the schemes over it that the
//! tests state by hand, and the simplicial complexes of a few surfaces.

use alloc::collections::BTreeMap;

use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Scheme;
use gandr_theory_discrete_morse::Standing;

/// A simplex on the vertices of a triangle, as a bit mask over the vertices
/// `a`, `b` and `c`. A mask with another bit names no cell of the triangle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Simplex(pub u8);

/// The vertex `a`.
pub const A: Simplex = Simplex(0b001);
/// The vertex `b`.
pub const B: Simplex = Simplex(0b010);
/// The vertex `c`.
pub const C: Simplex = Simplex(0b100);
/// The edge from `a` to `b`.
pub const AB: Simplex = Simplex(0b011);
/// The edge from `a` to `c`.
pub const AC: Simplex = Simplex(0b101);
/// The edge from `b` to `c`.
pub const BC: Simplex = Simplex(0b110);
/// The whole triangle.
pub const ABC: Simplex = Simplex(0b111);

/// The cells of the hollow triangle, each after its faces.
pub const HOLLOW: [Simplex; 6] = [A, B, C, AB, AC, BC];

/// The cells of the filled triangle, each after its faces.
pub const FILLED: [Simplex; 7] = [A, B, C, AB, AC, BC, ABC];

/// A fourth vertex `d`, outside the triangle.
pub const D: Simplex = Simplex(0b1000);

/// Why a test scheme refuses a cell.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Refused(pub Simplex);

/// The simplices of a triangle with the classes that a test states. Each
/// face has the incidence of its sign times `weight`.
#[derive(Debug)]
pub struct Triangle
{
    /// The factor of each incidence: one for the triangle, two for a broken
    /// complex.
    pub weight: i64,
    /// The class of each cell that a test names. Every other cell is
    /// critical.
    pub classes: BTreeMap<Simplex, Class<Simplex>>,
    /// The cells whose class the scheme refuses to give.
    pub refuses: Vec<Simplex>,
}

impl Triangle
{
    /// The triangle with the incidence one and the matching of `pairs`: each
    /// pair of a redundant cell and its partner one dimension up.
    ///
    /// # Specification
    /// trivial.
    pub fn matched(pairs: &[(Simplex, Simplex)]) -> Self
    {
        let mut classes = BTreeMap::new();
        for &(redundant, partner) in pairs {
            let _redundant = classes.insert(redundant, Class::Redundant(partner));
            let _collapsible = classes.insert(partner, Class::Collapsible(redundant));
        }
        Self {
            weight: 1,
            classes,
            refuses: Vec::new(),
        }
    }
}

impl Complex for Triangle
{
    type Cell = Simplex;
    type Fault = Refused;

    /// Whether `cell` is a nonempty set of the three vertices.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &Simplex,
    ) -> Result<Standing, Refused>
    {
        if cell.0 != 0 && cell.0 & !ABC.0 == 0 {
            Ok(Standing::Inside)
        }
        else {
            Ok(Standing::Outside)
        }
    }

    /// The faces of `cell`, each without one vertex, the signs alternating
    /// from plus in the order of the vertices. A vertex has no face.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Simplex,
        faces: &mut Vec<(Simplex, Incidence)>,
    ) -> Result<(), Refused>
    {
        push_faces(*cell, Incidence::from(self.weight), faces);
        Ok(())
    }
}

impl Scheme for Triangle
{
    /// The class that the test names for `cell`, or critical.
    ///
    /// # Specification
    /// trivial.
    fn class(
        &mut self,
        cell: &Simplex,
    ) -> Result<Class<Simplex>, Refused>
    {
        if self.refuses.contains(cell) {
            return Err(Refused(*cell));
        }
        Ok(self.classes.get(cell).cloned().unwrap_or(Class::Critical))
    }
}

/// Push the faces of `cell` onto `faces`, each without one vertex, the signs
/// alternating from plus in the order of the vertices and each times
/// `weight`. A vertex has no face.
///
/// # Specification
/// trivial.
fn push_faces(
    cell: Simplex,
    weight: Incidence,
    faces: &mut Vec<(Simplex, Incidence)>,
)
{
    if cell.0.count_ones() < 2 {
        return;
    }
    let mut sign = 1_i64;
    for bit in 0 .. u8::BITS {
        let vertex = 1_u8.checked_shl(bit).expect("a bit of the mask");
        if cell.0 & vertex != 0 {
            faces.push((
                Simplex(cell.0 & !vertex),
                Incidence::from(sign.saturating_mul(i64::from(weight))),
            ));
            sign = 0_i64.saturating_sub(sign);
        }
    }
}

/// A simplicial complex on at most eight vertices, given by its facets: each
/// cell is a nonempty set of the vertices of one facet, and each face has the
/// incidence of its sign.
#[derive(Debug)]
#[repr(transparent)]
pub struct Facets(pub Vec<Simplex>);

impl Facets
{
    /// The boundary of the tetrahedron on `a`, `b`, `c` and `d`: a sphere.
    ///
    /// # Specification
    /// trivial.
    pub fn sphere() -> Self
    {
        Self(Vec::from([
            Simplex(0b0111),
            Simplex(0b1011),
            Simplex(0b1101),
            Simplex(0b1110),
        ]))
    }

    /// The projective plane on six vertices: each edge of the complete graph
    /// lies in two of its ten triangles.
    ///
    /// # Specification
    /// trivial.
    pub fn projective_plane() -> Self
    {
        Self(Vec::from([
            Simplex(0b00_0111),
            Simplex(0b00_1101),
            Simplex(0b01_1001),
            Simplex(0b11_0001),
            Simplex(0b10_0011),
            Simplex(0b01_0110),
            Simplex(0b10_1100),
            Simplex(0b01_1010),
            Simplex(0b11_0100),
            Simplex(0b10_1010),
        ]))
    }

    /// The torus on seven vertices: the triangles `{i, i + 1, i + 3}` and
    /// `{i, i + 2, i + 3}` modulo seven.
    ///
    /// # Specification
    /// trivial.
    pub fn torus() -> Self
    {
        let mut triangles = Vec::new();
        for first in 0 .. 7_u32 {
            for steps in [[0_u32, 1, 3], [0_u32, 2, 3]] {
                let mut mask = 0_u8;
                for step in steps {
                    let vertex = first
                        .checked_add(step)
                        .and_then(|sum| sum.checked_rem(7))
                        .expect("a vertex");
                    mask |= 1_u8.checked_shl(vertex).expect("a vertex");
                }
                triangles.push(Simplex(mask));
            }
        }
        Self(triangles)
    }

    /// The cells, each after its faces: by the number of vertices, and then by
    /// mask.
    ///
    /// # Specification
    /// trivial.
    pub fn cells(&self) -> Vec<Simplex>
    {
        let mut cells: Vec<Simplex> = (1 ..= u8::MAX)
            .map(Simplex)
            .filter(|cell| self.0.iter().any(|facet| cell.0 & !facet.0 == 0))
            .collect();
        cells.sort_by_key(|cell| (cell.0.count_ones(), cell.0));
        cells
    }
}

impl Complex for Facets
{
    type Cell = Simplex;
    type Fault = Refused;

    /// Whether `cell` is a nonempty set of the vertices of a facet.
    ///
    /// # Specification
    /// trivial.
    fn standing(
        &mut self,
        cell: &Simplex,
    ) -> Result<Standing, Refused>
    {
        if cell.0 != 0 && self.0.iter().any(|facet| cell.0 & !facet.0 == 0) {
            Ok(Standing::Inside)
        }
        else {
            Ok(Standing::Outside)
        }
    }

    /// The faces of `cell`, each without one vertex, the signs alternating
    /// from plus in the order of the vertices.
    ///
    /// # Specification
    /// trivial.
    fn faces(
        &mut self,
        cell: &Simplex,
        faces: &mut Vec<(Simplex, Incidence)>,
    ) -> Result<(), Refused>
    {
        push_faces(*cell, Incidence::from(1_i64), faces);
        Ok(())
    }
}
