//! Iterative positive-core lowering over borrowed arena nodes.

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal as CoreLiteral;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;

use crate::image::BinderIndex;
use crate::image::CtorTag;
use crate::image::Image;
use crate::image::ImageError;
use crate::image::Literal;
use crate::image::Node;
use crate::image::NodeIndex;
use crate::image::NodeKind;

/// A core former outside the positive image vocabulary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Form
{
    /// A native function or operation.
    Primitive,
    /// Function introduction.
    Lambda,
    /// Function elimination.
    Application,
    /// Thunk elimination.
    Force,
    /// Universe-path transport.
    Transport,
    /// Text literal.
    String,
    /// Decimal literal.
    Numeric,
    /// Declaration reference.
    Constant,
    /// Suspended computation.
    Thunk,
    /// Universe lift.
    Lift,
    /// Quoted value type.
    Quote,
    /// Quoted computation type.
    QuoteComputation,
    /// Static function.
    StaticLambda,
    /// Static application.
    StaticApplication,
    /// Native path reflexivity.
    PathRefl,
    /// Native product path.
    PathProduct,
    /// Native equivalence.
    PathEquiv,
}
impl core::fmt::Display for Form
{
    /// Render the excluded former's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::Primitive => "a native primitive",
            | Self::Lambda => "an abstraction",
            | Self::Application => "an application",
            | Self::Force => "a forced thunk",
            | Self::Transport => "path transport",
            | Self::String => "a string literal",
            | Self::Numeric => "a numeric literal",
            | Self::Constant => "a constant",
            | Self::Thunk => "a thunk",
            | Self::Lift => "a lift",
            | Self::Quote => "a quoted value type",
            | Self::QuoteComputation => "a quoted computation type",
            | Self::StaticLambda => "a static abstraction",
            | Self::StaticApplication => "a static application",
            | Self::PathRefl => "path reflexivity",
            | Self::PathProduct => "a product path",
            | Self::PathEquiv => "an equivalence path",
        })
    }
}
/// Why a source program cannot become an image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LowerError
{
    /// The vocabulary does not represent this former.
    OutsideSlice(Form),
    /// No binder in this zone answers the index.
    UnboundVariable
    {
        /// The variable's zone.
        zone: Zone,
        /// Distance from the innermost binder.
        index: DeBruijnIndex,
    },
    /// A computation address does not resolve.
    DanglingComputation(ComputationId),
    /// A value address does not resolve.
    DanglingValue(ValueId),
    /// The core integer does not fit the signed 64-bit wire payload.
    IntegerOutOfRange,
    /// The image cannot encode another record.
    ImageRefused(ImageError),
    /// The traversal's operand stack does not match its scheduled assembly.
    MachineInvariant,
}
impl core::fmt::Display for LowerError
{
    /// Render the refusal without erasing its payload.
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
            | Self::OutsideSlice(form) => write!(f, "image does not represent {form}"),
            | Self::UnboundVariable { zone, index } => {
                let zone = match zone {
                    | Zone::Intuitionistic => "intuitionistic",
                    | Zone::Linear => "linear",
                };
                write!(f, "unbound {zone} variable {}", u32::from(index))
            },
            | Self::DanglingComputation(_) => f.write_str("computation address does not resolve"),
            | Self::DanglingValue(_) => f.write_str("value address does not resolve"),
            | Self::IntegerOutOfRange => f.write_str("integer exceeds signed 64-bit image range"),
            | Self::ImageRefused(error) => write!(f, "{error}"),
            | Self::MachineInvariant => {
                f.write_str("lowering operand stack disagrees with traversal")
            },
        }
    }
}
impl core::error::Error for LowerError
{
}
impl From<ImageError> for LowerError
{
    /// Preserve an image refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: ImageError) -> Self
    {
        Self::ImageRefused(error)
    }
}
impl TryFrom<&IntegerLiteral> for Literal
{
    type Error = LowerError;
    /// Convert an arbitrary-precision core literal to the signed wire payload.
    ///
    /// # Specification
    /// - ensures: success preserves the integer, including `i64::MIN`.
    /// - fails: `IntegerOutOfRange` outside the signed 64-bit interval.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `IntegerOutOfRange` when the magnitude or signed value is too
    /// wide.
    ///
    /// # Adequacy
    /// - hypothesis: L3 both signed endpoints and their adjacent outsiders
    ///   separate overflow, sign and asymmetric minimum faults.
    /// - witness: `tests::lowering::integer_payloads_cover_both_signed_extremes`
    #[spec(ensures: |ret| ret.is_err() || (i64::from(ret.as_ref().copied().unwrap_or_default()) < 0) == (integer.sign() == Sign::Negative))]
    #[inline]
    fn try_from(integer: &IntegerLiteral) -> Result<Self, Self::Error>
    {
        let magnitude = integer
            .magnitude()
            .as_ref()
            .parse::<u64>()
            .map_err(|_range| LowerError::IntegerOutOfRange)?;
        let value = match integer.sign() {
            | Sign::NonNegative => {
                i64::try_from(magnitude).map_err(|_range| LowerError::IntegerOutOfRange)
            },
            | Sign::Negative if magnitude == i64::MIN.unsigned_abs() => Ok(i64::MIN),
            | Sign::Negative => {
                let positive =
                    i64::try_from(magnitude).map_err(|_range| LowerError::IntegerOutOfRange)?;
                positive.checked_neg().ok_or(LowerError::IntegerOutOfRange)
            },
        };
        let value = value?;
        Ok(Self::from(value))
    }
}
/// Number of in-scope intuitionistic binders.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Depth(u32);
/// Work awaiting an explicit traversal step.
#[derive(Clone, Copy)]
enum Step
{
    /// Lower a computation at its binder depth.
    Computation(ComputationId, Depth),
    /// Lower a value at its binder depth.
    Value(ValueId, Depth),
    /// Assemble an operation from completed child records.
    Build(NodeKind, CtorTag, Arity),
}
/// Number of operands an assembly consumes.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Arity(usize);

/// Lower a closed positive-core computation without claiming it is typed.
///
/// # Specification
/// - ensures: success returns one terminal cut over a dependency-ordered image;
///   bind and case scope their bodies, pair fields retain source order.
/// - fails: unsupported form, unbound variable, dangling node, out-of-range
///   literal, image limit, or an inconsistent traversal stack.
/// - panics: none; term depth consumes heap frames rather than the call stack.
///
/// # Errors
/// Returns the corresponding `LowerError`; never substitutes a value.
///
/// # Adequacy
/// - hypothesis: L2 ordered image observations and L3 binder distances,
///   excluded forms, dangling roots and integer boundaries distinguish the
///   translation's decisions on the represented positive fragment.
/// - witness: `tests::lowering::a_variable_lowers_to_its_distance_from_the_innermost_binder`
/// - witness: `tests::lowering::each_dispatch_arm_binds_its_own_payload`
/// - witness: `tests::lowering::a_pair_lowers_to_its_tag_with_two_fields`
/// - witness: `tests::lowering::supported_excluded_core_forms_are_refused_by_name`
/// - witness: `tests::lowering::a_free_variable_is_refused_rather_than_lowered`
/// - witness: `tests::lowering::dangling_roots_and_deep_programs_fail_without_recursion`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |image| image.nodes().last().is_some_and(|node| node.kind == NodeKind::Cut)))]
#[inline]
pub fn lower_computation(
    core: &CoreArena,
    root: ComputationId,
) -> Result<Image, LowerError>
{
    let mut image = Image::new();
    let mut steps = vec![
        Step::Build(NodeKind::Cut, CtorTag::Unit, Arity(1)),
        Step::Computation(root, Depth(0)),
    ];
    let mut emitted: Vec<NodeIndex> = Vec::new();
    while let Some(step) = steps.pop() {
        match step {
            | Step::Computation(id, depth) => {
                let computation = core
                    .computation(id)
                    .ok_or(LowerError::DanglingComputation(id))?;
                match *computation {
                    | Computation::Primitive { .. } => {
                        return Err(LowerError::OutsideSlice(Form::Primitive));
                    },
                    | Computation::Return(value) => steps.push(Step::Value(value, depth)),
                    | Computation::Bind(bound, body) => {
                        steps.push(Step::Build(NodeKind::Bind, CtorTag::Unit, Arity(2)));
                        steps.push(Step::Computation(body, Depth(depth.0.saturating_add(1))));
                        steps.push(Step::Computation(bound, depth));
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => {
                        steps.push(Step::Build(NodeKind::Case, CtorTag::Unit, Arity(3)));
                        let inner = Depth(depth.0.saturating_add(1));
                        steps.push(Step::Computation(on_right, inner));
                        steps.push(Step::Computation(on_left, inner));
                        steps.push(Step::Value(scrutinee, depth));
                    },
                    | Computation::Lambda(_) => return Err(LowerError::OutsideSlice(Form::Lambda)),
                    | Computation::Application(..) => {
                        return Err(LowerError::OutsideSlice(Form::Application));
                    },
                    | Computation::Force(_) => return Err(LowerError::OutsideSlice(Form::Force)),
                    | Computation::Transport(..) => {
                        return Err(LowerError::OutsideSlice(Form::Transport));
                    },
                }
            },
            | Step::Value(id, depth) => {
                let value = core.value(id).ok_or(LowerError::DanglingValue(id))?;
                let mut node = Node {
                    kind: NodeKind::Ctor,
                    tag: CtorTag::Unit,
                    binder: BinderIndex::default(),
                    literal: Literal::default(),
                    operands: Vec::new(),
                };
                match *value {
                    | Value::Primitive { .. } => {
                        return Err(LowerError::OutsideSlice(Form::Primitive));
                    },
                    | Value::Unit => {},
                    | Value::Literal(CoreLiteral::Integer(ref integer)) => {
                        node.kind = NodeKind::Lit;
                        let literal = Literal::try_from(integer)?;
                        node.literal = literal;
                    },
                    | Value::Variable { zone, index } => {
                        if zone != Zone::Intuitionistic || u32::from(index) >= depth.0 {
                            return Err(LowerError::UnboundVariable { zone, index });
                        }
                        node.kind = NodeKind::Var;
                        node.binder = BinderIndex::from(u32::from(index));
                    },
                    | Value::Pair(first, second) => {
                        steps.push(Step::Build(NodeKind::Ctor, CtorTag::Pair, Arity(2)));
                        steps.push(Step::Value(second, depth));
                        steps.push(Step::Value(first, depth));
                        continue;
                    },
                    | Value::Injection(side, payload) => {
                        let tag = match side {
                            | Side::Left => CtorTag::Inl,
                            | Side::Right => CtorTag::Inr,
                        };
                        steps.push(Step::Build(NodeKind::Ctor, tag, Arity(1)));
                        steps.push(Step::Value(payload, depth));
                        continue;
                    },
                    | Value::Literal(CoreLiteral::Text(_)) => {
                        return Err(LowerError::OutsideSlice(Form::String));
                    },
                    | Value::Literal(CoreLiteral::Numeric(_)) => {
                        return Err(LowerError::OutsideSlice(Form::Numeric));
                    },
                    | Value::Constant(_) => return Err(LowerError::OutsideSlice(Form::Constant)),
                    | Value::Thunk(_) => return Err(LowerError::OutsideSlice(Form::Thunk)),
                    | Value::Lift { .. } => return Err(LowerError::OutsideSlice(Form::Lift)),
                    | Value::Quote(_) => return Err(LowerError::OutsideSlice(Form::Quote)),
                    | Value::QuoteComputation(_) => {
                        return Err(LowerError::OutsideSlice(Form::QuoteComputation));
                    },
                    | Value::StaticLambda(_) => {
                        return Err(LowerError::OutsideSlice(Form::StaticLambda));
                    },
                    | Value::StaticApplication(..) => {
                        return Err(LowerError::OutsideSlice(Form::StaticApplication));
                    },
                    | Value::PathRefl(_) => return Err(LowerError::OutsideSlice(Form::PathRefl)),
                    | Value::PathProduct(..) => {
                        return Err(LowerError::OutsideSlice(Form::PathProduct));
                    },
                    | Value::PathEquiv { .. } => {
                        return Err(LowerError::OutsideSlice(Form::PathEquiv));
                    },
                }
                let index = image.push(node)?;
                emitted.push(index);
            },
            | Step::Build(kind, tag, arity) => {
                let start = emitted
                    .len()
                    .checked_sub(arity.0)
                    .ok_or(LowerError::MachineInvariant)?;
                let operands: Vec<NodeIndex> = emitted.drain(start ..).collect();
                let node = Node {
                    kind,
                    tag,
                    binder: BinderIndex::default(),
                    literal: Literal::default(),
                    operands,
                };
                let index = image.push(node)?;
                emitted.push(index);
            },
        }
    }
    Ok(image)
}
