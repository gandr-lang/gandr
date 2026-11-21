//! Brown's collapsing scheme, and the check of a scheme on a set of cells.
//!
//! A collapsing scheme gives each cell of a complex a class. A critical cell
//! stays. A redundant cell is a face of its partner, one dimension up. A
//! collapsible cell is the partner of a redundant cell, one dimension down.
//! The scheme is a matching when each partner names its cell back, and the
//! complex admits each pair: by default, the incidence of each redundant cell
//! in its partner's boundary is one or minus one. The matching is acyclic when
//! no gradient path returns to its start. A gradient path runs from a
//! redundant cell up to its partner, and then down to another redundant face
//! of that partner.
//!
//! A bar complex has more cells than a caller can list, so [`collapse`] checks
//! a scheme on the cells the caller gives. The walk of the gradient follows
//! each redundant face it meets, also past the given cells, up to a budget.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;

use crate::complex::Complex;
use crate::complex::Incidence;
use crate::complex::Invertibility;
use crate::complex::Standing;
use crate::error::MorseError;
use crate::gradient::Place;
use crate::gradient::cycles;

wrapper! {
    /// The most redundant cells that the walk of a gradient reaches before
    /// the check refuses.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Budget(usize);
}

wrapper! {
    /// A number of cells, of pairs or of edges.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Count(usize);
}

impl Count
{
    /// The count one more than this, or this count at the largest count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn one_more(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// The class of a cell under a matching.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Class<Cell>
{
    /// No pair holds the cell, so it stays.
    Critical,
    /// The cell is a face of its partner, one dimension up.
    Redundant(Cell),
    /// The partner is a face of the cell, one dimension down.
    Collapsible(Cell),
}

/// A complex that gives the class of each of its cells, as Brown's
/// collapsing scheme does on a bar complex.
pub trait Scheme: Complex
{
    /// The class of `cell`.
    ///
    /// # Specification
    /// - requires: `cell` lies in the complex.
    /// - provides: the class that the scheme gives `cell`, with its partner
    ///   when a pair holds it.
    /// - fails: with the caller's fault, when the scheme cannot decide.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Errors
    /// - [`Complex::Fault`]: the scheme cannot decide.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the test schemes give each class once, and a scheme
    ///   that fails gives its fault back. The witnesses cover the schemes in
    ///   this crate's suite, not each implementation outside it.
    /// - witness: `tests::collapse::the_matching_of_a_triangle_collapses_onto_one_vertex`
    /// - witness: `tests::collapse::a_fault_of_the_scheme_is_given_back_as_its_own`
    fn class(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Class<Self::Cell>, Self::Fault>;
}

/// What the check of a scheme finds wrong with it as an acyclic matching.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Faults
{
    /// The cells whose partner does not name them back.
    pub unpaired: Count,
    /// The partners that do not lie in the complex.
    pub outside: Count,
    /// The redundant cells that cannot pair with their partner: the
    /// complex's [`Complex::pairing`] refuses them. By default, their
    /// incidence in the partner's boundary is not one or minus one.
    pub uninvertible: Count,
    /// The edges of the gradient that close a cycle.
    pub cycles: Count,
}

/// The critical cells among the cells a check reads, and what the check
/// finds wrong.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Collapse<Cell>
{
    /// The given cells that the scheme calls critical, in the given order.
    critical: Vec<Cell>,
    /// What the check finds wrong.
    faults: Faults,
    /// The pairs that the walk reaches: each redundant cell with its partner,
    /// the given cells first and then each one past them.
    pairs: Vec<(Cell, Cell)>,
}

impl<Cell> Collapse<Cell>
{
    /// The given cells that the scheme calls critical, in the given order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn critical(&self) -> &[Cell]
    {
        &self.critical
    }

    /// What the check finds wrong: zero in each count for an acyclic
    /// matching.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn faults(&self) -> Faults
    {
        self.faults
    }

    /// The number of redundant cells that the walk reaches: the given ones,
    /// and each redundant face of a partner past them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn visited(&self) -> Count
    {
        Count(self.pairs.len())
    }

    /// The pairs that the walk reaches: each redundant cell with its partner,
    /// the given cells first and then each one past them, each once.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pairs(&self) -> &[(Cell, Cell)]
    {
        &self.pairs
    }

    /// The critical cells and the pairs, moved out of the check.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (Vec<Cell>, Vec<(Cell, Cell)>)
    {
        (self.critical, self.pairs)
    }
}

/// Check `scheme` as an acyclic matching on `cells`, and keep the critical
/// cells among them.
///
/// The check reads the class of each given cell. A collapsible cell's partner
/// must lie in the complex and name the cell back. Then the walk starts at
/// each redundant cell. Its partner must lie in the complex and name it back,
/// and the complex's [`Complex::pairing`] must admit the pair: by default, an
/// incidence of one or minus one. The walk goes on to each other redundant
/// face of the partner, also past the given cells. The gradient graph has an
/// edge from each redundant cell to each redundant face it goes on to, and
/// the check counts the edges that close a cycle.
///
/// # Specification
/// - requires: each given cell lies in the complex.
/// - ensures: the critical cells are the given cells that the scheme calls
///   critical, in the given order. Each count of the faults counts the cells or
///   edges that its field names. The walk reaches at most `budget` redundant
///   cells.
/// - provides: the critical cells, the faults, and the pairs that the walk
///   reaches.
/// - fails: the scheme's own fault stops the check and comes back as
///   [`MorseError::Complex`]. A walk that reaches more than `budget` redundant
///   cells stops at once with [`MorseError::PastBudget`].
/// - panics: none.
/// - intension: the check reads the class of each given cell once. For each
///   redundant cell the walk reaches, it reads the partner's standing, class
///   and faces once, and the class of each face once. The cycle search reads
///   each redundant cell and each edge once.
///
/// # Errors
/// - [`MorseError::Complex`]: the scheme refuses a cell.
/// - [`MorseError::PastBudget`]: the walk reaches more than `budget` redundant
///   cells.
///
/// # Adequacy
/// - hypothesis: L3 — a triangle's matching onto one vertex keeps that vertex
///   critical with no fault. Four broken schemes each raise their own count by
///   one: a partner that names another cell, a partner outside the complex, an
///   incidence of two, and two pairs whose gradient turns back. A pair that the
///   complex refuses under a context raises its count at the incidence one. A
///   budget one short of the walk refuses it, and the exact budget does not. A
///   failing scheme gives its fault back.
/// - witness: `tests::collapse::the_matching_of_a_triangle_collapses_onto_one_vertex`
/// - witness: `tests::collapse::a_partner_that_names_another_cell_is_unpaired`
/// - witness: `tests::collapse::a_partner_outside_the_complex_is_counted`
/// - witness: `tests::collapse::an_incidence_of_two_pairs_no_cells`
/// - witness: `tests::collapse::a_scheme_whose_gradient_turns_back_closes_a_cycle`
/// - witness: `tests::collapse::a_walk_past_its_budget_is_refused`
/// - witness: `tests::collapse::a_fault_of_the_scheme_is_given_back_as_its_own`
/// - witness: `tests::equivalence::a_pair_under_a_context_is_refused_at_the_incidence_one`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |done| done.pairs.len() <= usize::from(budget)))]
#[inline]
pub fn collapse<'cells, Cells, S>(
    scheme: &mut S,
    cells: Cells,
    budget: Budget,
) -> Result<Collapse<S::Cell>, MorseError<S::Fault>>
where
    S: Scheme,
    S::Cell: 'cells,
    Cells: IntoIterator<Item = &'cells S::Cell>,
{
    let mut critical = Vec::new();
    let mut faults = Faults::default();
    let mut places: BTreeMap<S::Cell, Place> = BTreeMap::new();
    let mut redundant: Vec<(S::Cell, S::Cell)> = Vec::new();
    for cell in cells {
        let class = scheme.class(cell)?;
        match class {
            Class::Critical => critical.push(cell.clone()),
            Class::Redundant(partner) => {
                if !places.contains_key(cell) {
                    let _new = places.insert(cell.clone(), Place::from(redundant.len()));
                    redundant.push((cell.clone(), partner));
                }
            },
            Class::Collapsible(partner) => {
                let standing = scheme.standing(&partner)?;
                if standing == Standing::Outside {
                    faults.outside = faults.outside.one_more();
                }
                let back = scheme.class(&partner)?;
                match back {
                    Class::Redundant(ref named) if named == cell => {},
                    Class::Critical | Class::Redundant(_) | Class::Collapsible(_) => {
                        faults.unpaired = faults.unpaired.one_more();
                    },
                }
            },
        }
    }
    let mut edges: Vec<Vec<Place>> = Vec::with_capacity(redundant.len());
    let mut faces: Vec<(S::Cell, Incidence)> = Vec::new();
    let mut fresh: Vec<(S::Cell, S::Cell)> = Vec::new();
    while edges.len() < redundant.len() {
        if redundant.len() > usize::from(budget) {
            return Err(MorseError::PastBudget(budget));
        }
        let mut targets = Vec::new();
        let Some(&(ref cell, ref partner)) = redundant.get(edges.len())
        else {
            break;
        };
        let standing = scheme.standing(partner)?;
        if standing == Standing::Outside {
            faults.outside = faults.outside.one_more();
        }
        let back = scheme.class(partner)?;
        match back {
            Class::Collapsible(ref named) if named == cell => {},
            Class::Critical | Class::Redundant(_) | Class::Collapsible(_) => {
                faults.unpaired = faults.unpaired.one_more();
            },
        }
        faces.clear();
        scheme.faces(partner, &mut faces)?;
        // The cell's own incidence is read in the same pass, so the faces
        // are read once. A cell that is no face keeps the incidence zero.
        let mut incidence = Incidence::default();
        while let Some((face, at)) = faces.pop() {
            if face == *cell {
                incidence = at;
                continue;
            }
            let class = scheme.class(&face)?;
            match class {
                Class::Redundant(beyond) => match places.get(&face) {
                    Some(&place) => targets.push(place),
                    None => fresh.push((face, beyond)),
                },
                Class::Critical | Class::Collapsible(_) => {},
            }
        }
        if scheme.pairing(cell, partner, incidence)? == Invertibility::NotInvertible {
            faults.uninvertible = faults.uninvertible.one_more();
        }
        while let Some((face, beyond)) = fresh.pop() {
            if let Some(&held) = places.get(&face) {
                targets.push(held);
                continue;
            }
            let place = Place::from(redundant.len());
            let _new = places.insert(face.clone(), place);
            redundant.push((face, beyond));
            targets.push(place);
        }
        edges.push(targets);
    }
    faults.cycles = cycles(&edges);
    Ok(Collapse {
        critical,
        faults,
        pairs: redundant,
    })
}
