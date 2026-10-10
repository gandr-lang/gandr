//! The endpoint-only cube category: exchange and weakening, without diagonals.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::Dimension;
use crate::boundary::DimensionCount;
use crate::boundary::ShapeError;

/// A bridge endpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Endpoint
{
    /// The first endpoint.
    Zero,
    /// The second endpoint.
    One,
}

/// A shape term; there are no operations besides the two endpoint constants.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BridgeTerm
{
    /// An endpoint constant.
    Endpoint(Endpoint),
    /// A source coordinate.
    Variable(Dimension),
}

/// A map from a source affine context to the context indexed by its images.
///
/// # Specification
/// - ensures: every variable image lies in the source and occurs at most once.
/// - provides: explicit substitution data; omitted coordinates implement
///   weakening, permutations implement exchange, and duplicate endpoints are
///   permitted. Repeated variables are contraction and cannot be constructed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 finite map enumeration separates affine substitutions from
///   cartesian substitutions and checks closure under composition.
/// - witness: `tests::affine::small_affine_maps_compose_without_contraction`
/// - witness: `tests::affine::diagonal_and_bad_maps_are_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AffineMap
{
    /// Cardinality of the source context.
    source: DimensionCount,
    /// One term per target coordinate.
    images: Vec<BridgeTerm>,
}

impl AffineMap
{
    /// Admits an endpoint-or-injection substitution.
    ///
    /// # Specification
    /// - ensures: all variable images are distinct and within the source.
    /// - fails: out-of-range or repeated variable images are refused by
    ///   identity.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::DimensionOutside`] or [`ShapeError::Contraction`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 all small term vectors and L3 malformed maps
    ///   distinguish forbidden diagonals from permitted repeated constants.
    /// - witness: `tests::affine::small_affine_maps_compose_without_contraction`
    /// - witness: `tests::affine::diagonal_and_bad_maps_are_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|map| map.source == source) || ret.is_err())]
    pub fn new(
        source: DimensionCount,
        images: Vec<BridgeTerm>,
    ) -> Result<Self, ShapeError>
    {
        let mut used = vec![false; source.0];
        for term in &images {
            if let BridgeTerm::Variable(dim) = *term {
                let entry = used
                    .get_mut(dim.0)
                    .ok_or(ShapeError::DimensionOutside(dim))?;
                if *entry {
                    return Err(ShapeError::Contraction(dim));
                }
                *entry = true;
            }
        }
        Ok(Self { source, images })
    }

    /// Reads source and target dimensions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn dimensions(&self) -> (DimensionCount, DimensionCount)
    {
        (self.source, DimensionCount(self.images.len()))
    }

    /// Reads the target coordinates' terms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn images(&self) -> &[BridgeTerm]
    {
        &self.images
    }

    /// Composes `source → middle → target` by substitution of coordinate terms.
    ///
    /// # Specification
    /// - ensures: each target endpoint is unchanged and each target variable is
    ///   replaced by its image under `self`; the result is affine.
    /// - fails: nonmatching middle contexts are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::DifferentContext`] for noncomposable maps. A
    /// [`ShapeError::DimensionOutside`] denotes broken internal map invariants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 all composable small maps check term substitution,
    ///   identities and associativity; L3 distinguishes middle-context errors.
    /// - witness: `tests::affine::small_affine_maps_compose_without_contraction`
    /// - witness: `tests::affine::diagonal_and_bad_maps_are_refused`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|map| map.dimensions()
        == (self.source, DimensionCount(next.images.len()))) || ret.is_err())]
    pub fn then(
        &self,
        next: &Self,
    ) -> Result<Self, ShapeError>
    {
        if self.images.len() != next.source.0 {
            return Err(ShapeError::DifferentContext);
        }
        let mut images = Vec::with_capacity(next.images.len());
        for &term in &next.images {
            images.push(match term {
                | BridgeTerm::Endpoint(_) => term,
                | BridgeTerm::Variable(dim) => *self
                    .images
                    .get(dim.0)
                    .ok_or(ShapeError::DimensionOutside(dim))?,
            });
        }
        // Injection composed with injection remains injective on variable images.
        Ok(Self {
            source: self.source,
            images,
        })
    }
}
