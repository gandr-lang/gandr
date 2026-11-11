//! Semantic wrappers for primitive values crossing the VDC reflection boundary.
//!
//! These wrappers keep Rust primitives out of crate-defined signatures while
//! naming each scalar in the vocabulary of the reflected
//! virtual-double-category layer. All wrappers are representation-transparent
//! and expose only explicit conversions.

/// Generates a `#[repr(transparent)]` `Copy` newtype over a scalar carrier,
/// with both `From` conversions.
macro_rules! copy_wrapper {
    ($name:ident, $inner:ty, $doc:literal) => {
        #[doc = $doc]
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name($inner);

        impl From<$inner> for $name
        {
            /// Convert the scalar boundary without changing its representation.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $inner) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $inner
        {
            /// Convert the scalar boundary without changing its representation.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

copy_wrapper!(
    CertificateInvertibility,
    bool,
    "Whether every cell fired by a reflected certificate is invertible."
);
copy_wrapper!(
    CheckContextDeclaration,
    bool,
    "Whether a two-sided VDC checking context declares an object variable."
);
copy_wrapper!(
    CutCoherence,
    bool,
    "Whether a directed cut was admitted on the invertible coherence lane."
);
copy_wrapper!(
    CutDeclination,
    bool,
    "Whether a directed cut was declined by the acyclicity gate."
);
copy_wrapper!(
    DerivationIndex,
    usize,
    "Index into a VDC checker derivation environment."
);
copy_wrapper!(
    DerivationReplay,
    bool,
    "Whether a reflected derivation replays in the engine store."
);
copy_wrapper!(
    DescTableEmptyStatus,
    bool,
    "Whether a reflected description registry is empty."
);
copy_wrapper!(
    DescTableLength,
    usize,
    "Number of descriptions registered in a reflected VDC description table."
);
copy_wrapper!(
    DiagramCarrierEmptyStatus,
    bool,
    "Whether a finite reflected diagram has an empty carrier."
);
copy_wrapper!(
    DiagramCarrierLength,
    usize,
    "Number of carrier objects in a finite reflected diagram."
);
copy_wrapper!(
    DirectedContextDeclaration,
    bool,
    "Whether a directed VDC context declares an object variable."
);
copy_wrapper!(
    DirectedHomReflexivity,
    bool,
    "Whether a directed hom lies on the reflexive diagonal."
);
copy_wrapper!(
    DirectedObjectCovariance,
    bool,
    "Whether a directed reflected object is sorted covariantly."
);
copy_wrapper!(
    DiscreteHomInhabitation,
    bool,
    "Whether a discrete reflected hom has a reflexive inhabitant."
);
copy_wrapper!(
    IsoValidity,
    bool,
    "Whether a reflected protype isomorphism validates by replay."
);
copy_wrapper!(
    MotiveCovariance,
    bool,
    "Whether a directed-J motive keeps the moving endpoint covariant."
);
copy_wrapper!(
    RewriteCompletion,
    bool,
    "Whether a rewrite path reached a normal form within its budget."
);
copy_wrapper!(
    RewriteReachability,
    bool,
    "Whether one command pattern reaches another within a rewrite budget."
);
copy_wrapper!(
    RewriteStepBudget,
    usize,
    "Maximum number of rewrite steps a VDC path query may take."
);
copy_wrapper!(
    RoundTripIdentity,
    bool,
    "Whether an isomorphism round trip replays to the identity transformation."
);
copy_wrapper!(
    SigMorphismIdentity,
    bool,
    "Whether a reflected signature morphism is the identity renaming."
);
copy_wrapper!(
    VdcCellEquality,
    bool,
    "Whether two reflected VDC cells are replay-equivalent."
);
copy_wrapper!(
    CartesianProjectionPreservation,
    bool,
    "Whether a W-cartesian action preserves every product projection."
);
copy_wrapper!(
    CartesianDiagonalPreservation,
    bool,
    "Whether a W-cartesian action preserves the product diagonal."
);
copy_wrapper!(
    CartesianStructurePreservation,
    bool,
    "Whether a W-cartesian action preserves the complete cartesian structure."
);
