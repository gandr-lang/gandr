//! The refusals of the element-identity rules, with the endpoint and the
//! component that each refusal names.

use core::fmt;

use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_term::LayerPosition;

use crate::error::CompTypeWitness;
use crate::error::ValueTypeWitness;
use crate::error::replay::KernelVerdict;

/// A refusal of the element-identity rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityError
{
    /// The domain is closed but has no clause in the identity fold.
    OutsideFold(ValueTypeWitness),
    /// A reflexivity's point does not reach an endpoint: the forced
    /// conversion leaves them apart, and the dialogue the reflexivity carries
    /// for that endpoint does not replay as their convertibility.
    EndpointsDiffer
    {
        /// The source endpoint's content digest.
        left: ContentDigest,
        /// The target endpoint's content digest.
        right: ContentDigest,
        /// The endpoint the point did not reach.
        side: EndpointSide,
        /// That endpoint's dialogue's replay verdict.
        verdict: KernelVerdict,
    },
    /// A reflexivity's point and one endpoint that the kernel's own evaluation
    /// runs past the replay's budget: the evaluation decides nothing, so the
    /// pair is undecided, not apart. The readmission answers the report with
    /// the dialogue of that pair alone.
    EndpointsUndecided
    {
        /// The point's content digest.
        point: ContentDigest,
        /// The source endpoint's content digest.
        left: ContentDigest,
        /// The target endpoint's content digest.
        right: ContentDigest,
        /// The endpoint whose pair the evaluation did not decide.
        side: EndpointSide,
    },
    /// A definition's type conversion meets two path endpoints its forced
    /// reading leaves apart, and the dialogue the definition carries for that
    /// pair does not replay as their convertibility.
    RelatedEndpointsDiffer
    {
        /// The expected type's endpoint's content digest.
        left: ContentDigest,
        /// The synthesized type's endpoint's content digest.
        right: ContentDigest,
        /// The pair's dialogue's replay verdict.
        verdict: KernelVerdict,
    },
    /// The fibre is neutral: the domain is open, or the endpoints are not
    /// canonical, so no introduction but `here` inhabits it.
    NeutralFibre,
    /// The fibre is empty, so it has no diagonal evidence.
    EmptyFibre,
    /// An identity of universe paths is observed only through a higher field.
    HigherFieldRequired,
    /// An identity of functions is introduced only by a higher evaluation.
    HigherEvaluationRequired,
    /// A list identity needs a guarded observation.
    RecursiveObservation,
    /// A universe identity between distinct codes needs certificate evidence.
    CertificateOperation,
    /// Endpoints of an identity operation do not share a boundary.
    Boundary,
    /// A higher field requests no layer.
    ZeroDepth,
    /// A higher field reached an unguarded cycle at this layer.
    NonProductive(LayerPosition),
    /// A higher field exhausted its instruction allowance.
    DepthBound,
    /// A higher field names a layer it does not have.
    UnknownLayer(LayerPosition),
    /// A higher field's evidence count differs from its guard count.
    GuardEvidence,
    /// A higher evaluation's component count differs from its coverage.
    Coverage,
    /// Coverage generation exhausted its allowance.
    CoverageBudget,
    /// A higher evaluation's dialogue did not certify its returned value.
    Evaluation
    {
        /// The component, in coverage order.
        component: Component,
        /// The function whose evaluation failed.
        side: EvaluationSide,
        /// The replay's verdict.
        verdict: KernelVerdict,
    },
    /// A higher evaluation relates functions that mention bound variables.
    OpenFunctions,
    /// A quantified evaluation's step does not apply the two functions its
    /// premise relates at one input.
    QuantifiedStep
    {
        /// The component, in coverage order.
        component: Component,
    },
    /// A quantified evaluation applies a function whose own domain binds a
    /// function: the fragment boundary, since related inputs there would need
    /// function identity between them.
    HigherOrderDomain
    {
        /// The component, in coverage order.
        component: Component,
    },
    /// A returned endpoint's computation synthesizes no returner.
    ReturnedNonReturner(CompTypeWitness),
    /// A telescope transport's second identity does not lie over its first:
    /// it does not synthesize the identity, in the family's fibre at the
    /// path's target, from the start transported along the path.
    NotOver
    {
        /// The identity over the path the transport owes.
        expected: ValueTypeWitness,
        /// The identity the second component synthesizes.
        actual: ValueTypeWitness,
    },
    /// A bridge's domain reaches a sealed atom whose declaration states no
    /// interface: the relation between two elements of an abstract type is the
    /// abstraction's to choose, so no fold clause reads it.
    BridgeAtSealedType(ValueTypeWitness),
    /// An identity's domain reaches a sealed atom whose interface states a
    /// relation and its reflexivity but no law contracting its singletons, so
    /// its relation is not known to be an identity system.
    AtomTransport(ValueTypeWitness),
}

impl fmt::Display for IdentityError
{
    /// Name the refusal class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::OutsideFold(_) => f.write_str("identity at a type outside the identity fold"),
            Self::EndpointsDiffer { .. } => f.write_str("reflexivity between differing endpoints"),
            Self::EndpointsUndecided { .. } => {
                f.write_str("reflexivity whose endpoint the kernel's evaluation leaves undecided")
            },
            Self::RelatedEndpointsDiffer { .. } => {
                f.write_str("a definition's related endpoints do not replay")
            },
            Self::NeutralFibre => f.write_str("an identity fibre is neutral"),
            Self::EmptyFibre => f.write_str("an identity fibre is empty"),
            Self::HigherFieldRequired => {
                f.write_str("an identity of universe paths needs a higher field")
            },
            Self::HigherEvaluationRequired => {
                f.write_str("an identity of functions needs a higher evaluation")
            },
            Self::RecursiveObservation => {
                f.write_str("a list identity needs a guarded observation")
            },
            Self::CertificateOperation => {
                f.write_str("a universe identity needs certificate evidence")
            },
            Self::Boundary => f.write_str("identity endpoints do not share a boundary"),
            Self::ZeroDepth => f.write_str("a higher field requests no layer"),
            Self::NonProductive(_) => f.write_str("non-productive higher field"),
            Self::DepthBound => f.write_str("a higher field exhausted its allowance"),
            Self::UnknownLayer(_) => f.write_str("a higher field names an absent layer"),
            Self::GuardEvidence => {
                f.write_str("a higher field's evidence does not match its guards")
            },
            Self::Coverage => f.write_str("a higher evaluation does not match its coverage"),
            Self::CoverageBudget => {
                f.write_str("higher-evaluation coverage exhausted its allowance")
            },
            Self::Evaluation { .. } => f.write_str("a higher evaluation's dialogue did not replay"),
            Self::OpenFunctions => f.write_str("a higher evaluation relates open functions"),
            Self::QuantifiedStep { .. } => {
                f.write_str("a quantified step does not apply its premise's functions at one input")
            },
            Self::HigherOrderDomain { .. } => f.write_str(
                "a quantified evaluation applies a function whose domain is higher order",
            ),
            Self::ReturnedNonReturner(_) => f.write_str("a returned endpoint over a non-returner"),
            Self::NotOver { .. } => f.write_str("an identity that does not lie over its path"),
            Self::BridgeAtSealedType(_) => f.write_str("a bridge at a sealed type"),
            Self::AtomTransport(_) => {
                f.write_str("an identity at a sealed type whose interface states no identity law")
            },
        }
    }
}

impl core::error::Error for IdentityError
{
}

/// The endpoint of an identity a reflexivity refusal names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EndpointSide
{
    /// The source endpoint, `a` in `Path[.A = A](a, b)`.
    Left,
    /// The target endpoint, `b` in `Path[.A = A](a, b)`.
    Right,
}

/// A zero-based position in kernel-generated constructor coverage.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Component(pub usize);

/// Which endpoint's evaluation failed to replay.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvaluationSide
{
    /// The source function.
    Left,
    /// The target function.
    Right,
}
