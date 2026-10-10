//! Public-API law witnesses.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::CartesianDiagonalPreservation;
use crate::boundary::CartesianProjectionPreservation;
use crate::boundary::CartesianStructurePreservation;
use crate::vdc::SigMorphism;
use crate::vdc::SignatureRef;

/// A componentwise action on a finite product of VDC signatures.
///
/// The action is intentionally first-order: one tight action is recorded per
/// product factor. This is the runtime shadow of the W-action used by the
/// cartesian law; no second law interface is introduced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WCartesianAction
{
    /// The source product acted on.
    source: SignatureRef,
    /// The target product produced by the action.
    target: SignatureRef,
    /// One factor action per product component, in declaration order.
    components: Box<[SigMorphism]>,
}

impl WCartesianAction
{
    /// Construct a W-action over the supplied product factors.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        source: SignatureRef,
        target: SignatureRef,
        components: Vec<SigMorphism>,
    ) -> Self
    {
        Self {
            source,
            target,
            components: components.into_boxed_slice(),
        }
    }

    /// Check all cartesian obligations and return their runtime witness.
    ///
    /// # Specification
    /// - requires: none; nominal boundaries and malformed factor lists are
    ///   checked.
    /// - ensures: succeeds only when factor projections, the diagonal, and the
    ///   complete product structure are all preserved.
    /// - provides: deterministic law statuses on every failure.
    /// - fails: returns [`CartesianLawError`] for a non-product boundary or a
    ///   failed cartesian obligation.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CartesianLawError::SourceNotProduct`] or
    /// [`CartesianLawError::TargetNotProduct`] for non-product boundaries, and
    /// [`CartesianLawError::Violation`] when any law status is false.
    #[inline]
    /// # Adequacy
    /// - hypothesis: L3 — separate projection, diagonal and structure defects
    ///   are refused by the law suite. The predicate observes status coherence
    ///   and nominal-boundary refusal, not the coordinate laws alone.
    /// - witness: `tests::laws::tests::w_cartesian_action_preserves_projections_diagonal_and_structure`
    #[spec(ensures: |out| match out { Ok(witness) | Err(CartesianLawError::Violation(witness)) => bool::from(witness.structure) == (bool::from(witness.projections) && bool::from(witness.diagonal)) && out.is_ok() == bool::from(witness.structure), Err(CartesianLawError::SourceNotProduct) => matches!(self.source.parts(), quenchant_shape::shape::Maybe::Absent(_)), Err(CartesianLawError::TargetNotProduct) => matches!(self.source.parts(), quenchant_shape::shape::Maybe::Present(_)) && matches!(self.target.parts(), quenchant_shape::shape::Maybe::Absent(_)) })]
    pub fn checked_witness(&self) -> Result<CartesianWitness, CartesianLawError>
    {
        let source = match self.source.parts() {
            | quenchant_shape::shape::Maybe::Present(parts) => parts,
            | quenchant_shape::shape::Maybe::Absent(_) => {
                return Err(CartesianLawError::SourceNotProduct);
            },
        };
        let target = match self.target.parts() {
            | quenchant_shape::shape::Maybe::Present(parts) => parts,
            | quenchant_shape::shape::Maybe::Absent(_) => {
                return Err(CartesianLawError::TargetNotProduct);
            },
        };
        let source_width = source.clone().count();
        let same_width =
            source_width == target.clone().count() && source_width == self.components.len();
        let projections = same_width
            && self.components.iter().zip(source.zip(target)).all(
                |(component, (source_factor, target_factor))| {
                    component.src.to_node() == source_factor
                        && component.tgt.to_node() == target_factor
                },
            );
        let diagonal = same_width
            && self.components.windows(2).all(|pair| {
                pair.first().is_some_and(|first| {
                    pair.get(1)
                        .is_some_and(|second| first.src == second.src && first.tgt == second.tgt)
                })
            });
        let structure = same_width && projections && diagonal;
        let witness = CartesianWitness {
            projections: CartesianProjectionPreservation::from(projections),
            diagonal: CartesianDiagonalPreservation::from(diagonal),
            structure: CartesianStructurePreservation::from(structure),
        };
        if !structure {
            return Err(CartesianLawError::Violation(witness));
        }
        Ok(witness)
    }
}

/// The checked status of the three LAW-VDC-CARTESIAN obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CartesianWitness
{
    /// Preservation of every product projection.
    pub projections: CartesianProjectionPreservation,
    /// Preservation of the product diagonal.
    pub diagonal: CartesianDiagonalPreservation,
    /// Preservation of the complete product structure.
    pub structure: CartesianStructurePreservation,
}

/// Failure reported by the checked W-cartesian action.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CartesianLawError
{
    /// The source boundary is not a product signature.
    SourceNotProduct,
    /// The target boundary is not a product signature.
    TargetNotProduct,
    /// At least one cartesian status is false.
    Violation(CartesianWitness),
}

impl core::fmt::Display for CartesianLawError
{
    /// Render the typed refusal and its boundary evidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::SourceNotProduct => f.write_str("cartesian source is not a product"),
            | Self::TargetNotProduct => f.write_str("cartesian target is not a product"),
            | Self::Violation(witness) => write!(
                f,
                "cartesian laws fail: projections={}, diagonal={}, structure={}",
                bool::from(witness.projections),
                bool::from(witness.diagonal),
                bool::from(witness.structure)
            ),
        }
    }
}
impl core::error::Error for CartesianLawError
{
}
