//! The simplices of a triangle as a complex, and the schemes over it that the
//! tests state by hand.

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
        if cell.0.count_ones() < 2 {
            return Ok(());
        }
        let mut sign = 1_i64;
        for bit in 0 .. u8::BITS {
            let vertex = 1_u8.checked_shl(bit).expect("a bit of the mask");
            if cell.0 & vertex != 0 {
                faces.push((
                    Simplex(cell.0 & !vertex),
                    Incidence::from(sign.saturating_mul(self.weight)),
                ));
                sign = 0_i64.saturating_sub(sign);
            }
        }
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
