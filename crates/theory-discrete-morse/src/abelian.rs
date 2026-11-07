//! The abelianisation of a scheme: its composites read as integer chains.
//!
//! A chain counts each cell with an integer. It forgets the order of the
//! cells in a composite and the context of each occurrence, so it is the
//! linear shadow of a composite. A redundant cell goes to the negative of its
//! incidence times the other faces of its partner, and a partner goes to zero.
//! The witness of a redundant cell is its partner times the same sign, and
//! its boundary is the replacement less the cell. Conjugation changes
//! nothing, because the chains commute.
//!
//! Through this reading, the collapse of the boundary of a critical cell is
//! the Morse boundary that [`reduct`](crate::reduct()) gives.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use crate::collapse::Class;
use crate::collapse::Scheme;
use crate::complex::Complex;
use crate::complex::Incidence;
use crate::complex::Invertibility;
use crate::complex::Standing;
use crate::equivalence::Closure;
use crate::equivalence::Composites;
use crate::equivalence::Definition;
use crate::equivalence::Images;
use crate::error::MorseError;

/// An integer chain: each cell with its coefficient, in cell order, with no
/// coefficient zero.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Chain<Cell>(Vec<(Cell, Incidence)>);

impl<Cell> Chain<Cell>
{
    /// Each cell with its coefficient, in cell order, with no coefficient
    /// zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn terms(&self) -> &[(Cell, Incidence)]
    {
        &self.0
    }
}

/// Add `coefficient` times `cell` to `sum`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`MorseError::Overflow`]: the sum passes the 64-bit integers.
fn add<Cell, Fault>(
    sum: &mut BTreeMap<Cell, Incidence>,
    cell: &Cell,
    coefficient: Incidence,
) -> Result<(), MorseError<Fault>>
where
    Cell: Clone + Ord,
{
    let slot = sum.entry(cell.clone()).or_default();
    *slot = slot.plus(coefficient).ok_or(MorseError::Overflow)?;
    Ok(())
}

/// Add `scale` times each term of `terms` to `sum`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// - [`MorseError::Overflow`]: a product or a sum passes the 64-bit integers.
fn add_scaled<Cell, Fault>(
    sum: &mut BTreeMap<Cell, Incidence>,
    terms: &[(Cell, Incidence)],
    scale: Incidence,
) -> Result<(), MorseError<Fault>>
where
    Cell: Clone + Ord,
{
    for &(ref cell, coefficient) in terms {
        add(
            sum,
            cell,
            coefficient.times(scale).ok_or(MorseError::Overflow)?,
        )?;
    }
    Ok(())
}

/// The chain of `sum`, with each zero coefficient dropped.
///
/// # Specification
/// trivial.
fn chain<Cell>(sum: BTreeMap<Cell, Incidence>) -> Chain<Cell>
{
    Chain(
        sum.into_iter()
            .filter(|&(_, coefficient)| coefficient != Incidence::default())
            .collect(),
    )
}

/// A scheme read through integer chains: the abelianisation of its
/// composites.
#[derive(Debug)]
pub struct Abelian<'scheme, S>
where
    S: Scheme,
{
    /// The scheme read.
    scheme: &'scheme mut S,
    /// The faces of the last cell read, kept so that no read allocates once
    /// it has grown.
    faces: Vec<(S::Cell, Incidence)>,
}

impl<'scheme, S> Abelian<'scheme, S>
where
    S: Scheme,
{
    /// `scheme` read through integer chains.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(scheme: &'scheme mut S) -> Self
    {
        Self {
            scheme,
            faces: Vec::new(),
        }
    }

    /// The boundary of `cell` as a chain.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`MorseError::Complex`]: the scheme cannot read the faces.
    /// - [`MorseError::Overflow`]: a sum passes the 64-bit integers.
    #[inline]
    pub fn boundary(
        &mut self,
        cell: &S::Cell,
    ) -> Result<Chain<S::Cell>, MorseError<S::Fault>>
    {
        let mut sum = BTreeMap::new();
        self.faces.clear();
        self.scheme
            .faces(cell, &mut self.faces)
            .map_err(MorseError::Complex)?;
        add_scaled(&mut sum, &self.faces, Incidence::from(1_i64))?;
        Ok(chain(sum))
    }

    /// The boundary of the chain `of`, summed over its terms.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`MorseError::Complex`]: the scheme cannot read the faces.
    /// - [`MorseError::Overflow`]: a product or a sum passes the 64-bit
    ///   integers.
    fn boundary_of(
        &mut self,
        of: &Chain<S::Cell>,
    ) -> Result<Chain<S::Cell>, MorseError<S::Fault>>
    {
        let mut sum = BTreeMap::new();
        for &(ref cell, coefficient) in &of.0 {
            self.faces.clear();
            self.scheme
                .faces(cell, &mut self.faces)
                .map_err(MorseError::Complex)?;
            add_scaled(&mut sum, &self.faces, coefficient)?;
        }
        Ok(chain(sum))
    }
}

impl<S> Complex for Abelian<'_, S>
where
    S: Scheme,
{
    type Cell = S::Cell;
    type Fault = MorseError<S::Fault>;

    /// Whether `cell` lies in the scheme's complex.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn standing(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Standing, Self::Fault>
    {
        self.scheme.standing(cell).map_err(MorseError::Complex)
    }

    /// Push each face of `cell` onto `faces`, with its incidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn faces(
        &mut self,
        cell: &Self::Cell,
        faces: &mut Vec<(Self::Cell, Incidence)>,
    ) -> Result<(), Self::Fault>
    {
        self.scheme.faces(cell, faces).map_err(MorseError::Complex)
    }

    /// The scheme's own pairing condition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pairing(
        &mut self,
        face: &Self::Cell,
        cell: &Self::Cell,
        incidence: Incidence,
    ) -> Result<Invertibility, Self::Fault>
    {
        self.scheme
            .pairing(face, cell, incidence)
            .map_err(MorseError::Complex)
    }
}

impl<S> Scheme for Abelian<'_, S>
where
    S: Scheme,
{
    /// The scheme's class of `cell`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Class<Self::Cell>, Self::Fault>
    {
        self.scheme.class(cell).map_err(MorseError::Complex)
    }
}

impl<S> Composites for Abelian<'_, S>
where
    S: Scheme,
{
    type Composite = Chain<S::Cell>;
    type Witness = Chain<S::Cell>;

    /// The chain of `cell` once.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generator(
        &mut self,
        cell: &Self::Cell,
    ) -> Result<Self::Composite, Self::Fault>
    {
        Ok(Chain(vec![(cell.clone(), Incidence::from(1_i64))]))
    }

    /// The zero chain: an identity has no cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn identity(
        &mut self,
        _composite: &Self::Composite,
    ) -> Result<Self::Composite, Self::Fault>
    {
        Ok(Chain(Vec::new()))
    }

    /// Push each cell of the chain onto `cells`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn generators(
        &mut self,
        composite: &Self::Composite,
        cells: &mut Vec<Self::Cell>,
    ) -> Result<(), Self::Fault>
    {
        cells.extend(composite.0.iter().map(|&(ref cell, _)| cell.clone()));
        Ok(())
    }

    /// The chain with each mapped cell replaced by its coefficient times its
    /// image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn substitute(
        &mut self,
        composite: &Self::Composite,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Composite, Self::Fault>
    {
        let mut sum = BTreeMap::new();
        for &(ref cell, coefficient) in &composite.0 {
            match images.of(cell) {
                Some(image) => add_scaled(&mut sum, &image.0, coefficient)?,
                None => add(&mut sum, cell, coefficient)?,
            }
        }
        Ok(chain(sum))
    }

    /// The other faces of `partner`, each times the negative of the
    /// incidence of `redundant` and its own; the witness is `partner` times
    /// the same sign.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn definition(
        &mut self,
        redundant: &Self::Cell,
        partner: &Self::Cell,
    ) -> Result<Definition<Self::Composite, Self::Witness>, Self::Fault>
    {
        self.faces.clear();
        self.scheme
            .faces(partner, &mut self.faces)
            .map_err(MorseError::Complex)?;
        let mut incidence = Incidence::default();
        let mut others = BTreeMap::new();
        for &(ref face, at) in &self.faces {
            if face == redundant {
                incidence = at;
            }
            else {
                add(&mut others, face, at)?;
            }
        }
        let sign = incidence.negated().ok_or(MorseError::Overflow)?;
        let mut replacement = BTreeMap::new();
        add_scaled(&mut replacement, &chain(others).0, sign)?;
        let mut witness = BTreeMap::new();
        add(&mut witness, partner, sign)?;
        Ok(Definition {
            replacement: chain(replacement),
            witness: chain(witness),
        })
    }

    /// Whether the boundary of `witness` is `target` less `source`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn replays(
        &mut self,
        witness: &Self::Witness,
        source: &Self::Composite,
        target: &Self::Composite,
    ) -> Result<Closure, Self::Fault>
    {
        let boundary = self.boundary_of(witness)?;
        let mut difference = BTreeMap::new();
        add_scaled(&mut difference, &target.0, Incidence::from(1_i64))?;
        add_scaled(&mut difference, &source.0, Incidence::from(-1_i64))?;
        Ok(if chain(difference) == boundary {
            Closure::Closes
        }
        else {
            Closure::Open
        })
    }

    /// The witness chain with each mapped cell replaced by its coefficient
    /// times its image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carry(
        &mut self,
        witness: &Self::Witness,
        images: &Images<'_, Self::Cell, Self::Composite>,
    ) -> Result<Self::Witness, Self::Fault>
    {
        self.substitute(witness, images)
    }

    /// The sum of the two chains: homotopies compose by addition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compose(
        &mut self,
        first: &Self::Witness,
        second: &Self::Witness,
    ) -> Result<Self::Witness, Self::Fault>
    {
        let mut sum = BTreeMap::new();
        add_scaled(&mut sum, &first.0, Incidence::from(1_i64))?;
        add_scaled(&mut sum, &second.0, Incidence::from(1_i64))?;
        Ok(chain(sum))
    }

    /// Each coefficient of `composite` times the witness of its cell: the
    /// chain homotopy at a chain, or nothing where no cell has a witness.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn whisker(
        &mut self,
        composite: &Self::Composite,
        witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Option<Self::Witness>, Self::Fault>
    {
        let mut sum = BTreeMap::new();
        let mut found = None;
        for &(ref cell, coefficient) in &composite.0 {
            if let Some(image) = witnesses.of(cell) {
                add_scaled(&mut sum, &image.0, coefficient)?;
                found = Some(());
            }
        }
        Ok(found.map(|()| chain(sum)))
    }

    /// The chain of `cell` once: chains commute, so conjugation changes
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn conjugate(
        &mut self,
        cell: &Self::Cell,
        _witnesses: &Images<'_, Self::Cell, Self::Witness>,
    ) -> Result<Self::Composite, Self::Fault>
    {
        self.generator(cell)
    }
}
