//! Typed admission uses the core checker's formed expected type.

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::FormedCompType;
use gandr_core_checker::check_comp;
use gandr_core_term::ComputationId;

use crate::LowerError;
use crate::image::Image;
use crate::lower_computation;

/// The stage that refused a typed compilation request.
#[derive(Debug, Eq, PartialEq)]
pub enum BridgeError
{
    /// The core judgement refused the computation.
    NotChecked(CheckRefusal),
    /// The positive image vocabulary refused the checked computation.
    NotLowered(LowerError),
}
impl core::fmt::Display for BridgeError
{
    /// Render the original stage and refusal.
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
            | Self::NotChecked(ref _error) => f.write_str("core checker refused the computation"),
            | Self::NotLowered(ref error) => write!(f, "image lowering refused: {error}"),
        }
    }
}
impl core::error::Error for BridgeError
{
}
/// The typed gate's decision, retaining any refusal.
#[derive(Debug, Eq, PartialEq)]
pub enum TypedVerdict
{
    /// The checker and lowering both admitted the computation.
    Admitted,
    /// The gate refused at the named stage.
    Refused(BridgeError),
}
/// Check at a formed computation type before lowering.
///
/// # Specification
/// - ensures: only a successful core check may enter lowering; its arena is
///   borrowed directly, with no cloned term or invented unknown type.
/// - fails: `NotChecked` preserves the checker refusal; `NotLowered` preserves
///   the image refusal after a successful check.
/// - panics: none.
///
/// # Errors
/// Returns the matching `BridgeError` stage.
///
/// # Adequacy
/// - hypothesis: L3 an ill-typed case refused before image construction and a
///   typed text outside the image separate the two gates.
/// - witness: `tests::lowering::a_computation_the_checker_refuses_never_reaches_the_lowering`
/// - witness: `tests::typed::typed_refusals_preserve_stage_and_payload`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |image| image.nodes().last().is_some_and(|node| node.kind == crate::image::NodeKind::Cut)))]
#[inline]
pub fn check_and_lower(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
    expected: FormedCompType,
) -> Result<Image, BridgeError>
{
    check_comp(context, computation, expected).map_err(BridgeError::NotChecked)?;
    lower_computation(context.arena(), computation).map_err(BridgeError::NotLowered)
}
/// Classify the full typed gate without discarding its failure evidence.
///
/// # Specification
/// - ensures: Admitted exactly when checking and lowering succeed, otherwise
///   retains the stage's typed refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 a typed integer and wrong expected type separate acceptance
///   from refusal without changing the input computation.
/// - witness: `tests::typed::the_typed_verdict_reports_what_the_checker_would_say`
#[spec(ensures: |ret| ret != TypedVerdict::Admitted || context.arena().computation(computation).is_some())]
#[inline]
pub fn is_typed(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
    expected: FormedCompType,
) -> TypedVerdict
{
    match check_and_lower(context, computation, expected) {
        | Ok(_) => TypedVerdict::Admitted,
        | Err(error) => TypedVerdict::Refused(error),
    }
}
