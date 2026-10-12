//! First-order descriptions interpreted in the native core arena.
//!
//! Description syntax stays in the theory tier. This module supplies its
//! core interpretation, retaining nominal heads and explicit value arguments.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_theory_levitation::Code;
use gandr_theory_levitation::CodeNode;
use gandr_theory_levitation::CodeView;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NameRef;
use gandr_theory_levitation::PrimTy;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::ValueTypeNode;
use gandr_theory_levitation::ValueTypeRef;
use gandr_theory_levitation::ValueTypeView;

use crate::CoreArena;
use crate::DataSignature;
use crate::ValueTypeId;

/// A named type's explicit argument count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TypeArity(pub usize);

/// A parameter's position in its declaration telescope, counted from the
/// outside.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParameterLevel(pub usize);

/// The number of telescope parameters in scope at an interpretation site.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParameterDepth(pub usize);

/// A resolved symbolic type reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeBinding
{
    /// A parameter or manifest closed type, already interpreted in the arena.
    Type(ValueTypeId),
    /// An ordinary value used as an index, never quoted as a type.
    Value(crate::ValueId),
    /// A telescope binder, resolved to a de Bruijn index at its use site.
    Parameter
    {
        /// Absolute telescope position.
        level: ParameterLevel,
        /// The already-decoded classifier, needed when the binder denotes a
        /// type.
        classifier: ValueTypeId,
    },
    /// A native nominal head with its explicit application arity.
    Nominal
    {
        /// Admission position of the datatype declaration.
        declaration: ConstantIndex,
        /// Number of explicit type arguments.
        arity: TypeArity,
    },
}

/// A borrowed local name, avoiding copies of the global interpretation table.
#[derive(Clone, Copy, Debug)]
pub struct LocalBinding<'names>
{
    /// The telescope's source name.
    pub name: &'names Name,
    /// Its binding in the interpretation environment.
    pub binding: TypeBinding,
}

/// The interpretation of recursive and named type leaves.
#[derive(Clone, Copy, Debug)]
pub struct DecodeContext<'names>
{
    /// The single recursive sort this interpretation binds.
    pub self_sort: NameRef<'names>,
    /// The nominal application substituted for that recursive sort.
    pub self_type: ValueTypeId,
    /// Parameter scope at this node, including every preceding telescope
    /// binder.
    pub depth: ParameterDepth,
    /// Local binders, with the innermost binding last; locals shadow globals.
    pub locals: &'names [LocalBinding<'names>],
    /// Resolved parameters and named datatypes; missing names are refused.
    pub types: &'names BTreeMap<Name, TypeBinding>,
}

impl<'names> DecodeContext<'names>
{
    /// Resolve the last local binding before consulting the global table.
    ///
    /// # Specification
    /// - ensures: locals shadow globals without changing either environment.
    /// - fails: an absent name returns `UnresolvedType`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the unresolved source name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a local parameter shadows a closed global type of the
    ///   same name.
    /// - witness: `description::tests::native_indices_remain_values_under_telescope_scope`
    #[spec(ensures: |result| result.is_ok() == (self.locals.iter().any(|local| local.name == name) || self.types.contains_key(name)))]
    fn binding(
        self,
        name: &Name,
    ) -> Result<&'names TypeBinding, DecodeError>
    {
        self.locals
            .iter()
            .rev()
            .find(|local| local.name == name)
            .map(|local| &local.binding)
            .or_else(|| self.types.get(name))
            .ok_or_else(|| DecodeError::UnresolvedType(name.clone()))
    }
}

/// A description with no interpretation in the current core fragment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodeError
{
    /// Atom abstraction needs its own native former.
    AtomAbstraction,
    /// The negative greatest-fixpoint former is absent.
    CodataNu,
    /// The payload-coproduct reading has no summand; native empty data remains
    /// valid.
    Uninhabited,
    /// The single-sort reading was offered another recursive sort.
    ForeignSort(Name),
    /// A whole-description carrier requires exactly one declared sort.
    MultiSorted,
    /// A field names no supplied type binding.
    UnresolvedType(Name),
    /// A named application does not match the supplied binding's arity.
    AppliedType(Name),
    /// The core has no primitive with these semantics.
    Primitive(PrimTy),
    /// A malformed code fails its fixed-arity invariant.
    MalformedCode,
    /// The supplied parameter classifiers disagree with the description.
    ParameterArity,
}

impl core::fmt::Display for DecodeError
{
    /// Render the exact refusal, including its offending name when present.
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
            | Self::AtomAbstraction => f.write_str("atom abstraction has no native former"),
            | Self::CodataNu => {
                f.write_str("codata requires the negative greatest-fixpoint former")
            },
            | Self::Uninhabited => f.write_str("an empty payload coproduct has no summand"),
            | Self::ForeignSort(ref name) => write!(f, "recursive sort `{name}` is not bound"),
            | Self::MultiSorted => f.write_str("this interpretation requires one declared sort"),
            | Self::UnresolvedType(ref name) => write!(f, "type `{name}` is not bound"),
            | Self::AppliedType(ref name) => {
                write!(f, "type `{name}` has the wrong application arity")
            },
            | Self::Primitive(primitive) => write!(
                f,
                "primitive `{}` has no native interpretation",
                primitive.label().as_ref()
            ),
            | Self::MalformedCode => f.write_str("description violates its fixed-arity invariant"),
            | Self::ParameterArity => {
                f.write_str("parameter classifiers disagree with the description")
            },
        }
    }
}

impl core::error::Error for DecodeError
{
}

/// A pending postorder interpretation step.
enum Frame<'code, G>
{
    /// Interpret a description code node.
    Code(CodeNode<'code, G>),
    /// Interpret a symbolic type reference.
    Type(ValueTypeNode<'code>),
    /// Interpret an explicit nominal argument in the value language.
    Argument(ValueTypeNode<'code>),
    /// Turn an interpreted type argument into its positive code.
    QuoteArgument,
    /// Combine two payloads into a product.
    Product,
    /// Combine two payloads into a sum.
    Sum,
    /// Apply a resolved nominal head to the last interpreted arguments.
    Apply(ConstantIndex, TypeArity),
}

/// Interpret a code, erasing its grades and attributes but preserving shape.
///
/// # Specification
/// - requires: supplied type ids belong to `arena` and have the intended scope.
/// - ensures: unit, product and sum retain their constructors and order; the
///   bound recursive sort denotes `context.self_type`; named applications
///   become native nominal heads over quoted explicit arguments.
/// - fails: returns the named unsupported leaf, unresolved binding, foreign
///   sort or application-arity refusal; malformed code never fabricates a type.
/// - panics: none.
///
/// # Errors
/// Returns `AtomAbstraction`, `ForeignSort`, `UnresolvedType`, `AppliedType`,
/// `Primitive` or `MalformedCode` at the first unreadable node.
///
/// # Adequacy
/// - hypothesis: L3 — exact decoded shapes separate products from sums, order,
///   leaf resolution, unsupported formers and nominal application arguments.
/// - witness: `description::tests::decode_interprets_the_first_order_fragment`
/// - witness: `description::tests::decode_declines_the_deferred_leaves`
#[inline]
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
pub fn decode<G>(
    arena: &mut CoreArena,
    code: &Code<G>,
    context: DecodeContext<'_>,
) -> Result<ValueTypeId, DecodeError>
{
    interpret(arena, vec![Frame::Code(code.to_node())], context)
}

/// Interpret a symbolic field reference in the supplied name environment.
///
/// # Specification
/// - requires: supplied type ids belong to `arena` and have the intended scope.
/// - ensures: resolved types retain their identity; applied nominal heads
///   retain their declaration position and the order of quoted arguments.
/// - fails: unresolved names, unsupported primitives and wrong arities are
///   typed refusals.
/// - panics: none.
///
/// # Errors
/// Returns `UnresolvedType`, `AppliedType`, `Primitive` or `MalformedCode`.
///
/// # Adequacy
/// - hypothesis: L3 — a named application and unresolved or misapplied siblings
///   distinguish nominal decoding from an opaque-name fallback.
/// - witness: `description::tests::native_applications_preserve_heads_and_arguments`
#[inline]
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
pub fn decode_ref(
    arena: &mut CoreArena,
    reference: &ValueTypeRef,
    context: DecodeContext<'_>,
) -> Result<ValueTypeId, DecodeError>
{
    interpret::<()>(arena, vec![Frame::Type(reference.to_node())], context)
}

/// Interpret constructor payloads as a right-associated coproduct.
///
/// This carrier describes payload shape; it never replaces a nominal datatype.
///
/// # Specification
/// - requires: supplied type ids belong to `arena` and have the intended scope.
/// - ensures: constructor declaration order is summand order, with singleton
///   payloads unwrapped and recursive occurrences retaining the supplied
///   carrier.
/// - fails: codata, multiple sorts and an empty coproduct are declined
///   explicitly; payload refusals propagate unchanged.
/// - panics: none.
///
/// # Errors
/// Returns `CodataNu`, `MultiSorted`, `Uninhabited` or a `decode` refusal.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one and two constructors and both polarities
///   distinguish empty, singleton and coproduct behavior.
/// - witness: `description::tests::decode_desc_is_the_constructor_coproduct`
/// - witness: `description::tests::decode_desc_declines_codata_and_the_uninhabited`
#[inline]
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
pub fn decode_desc<G>(
    arena: &mut CoreArena,
    description: &SignDesc<G>,
    context: DecodeContext<'_>,
) -> Result<ValueTypeId, DecodeError>
{
    single_data_sort(description)?;
    let mut summands = Vec::with_capacity(description.ctors.len());
    for constructor in &description.ctors {
        let summand = decode(arena, &constructor.code, context)?;
        summands.push(summand);
    }
    let Some(mut result) = summands.pop()
    else {
        return Err(DecodeError::Uninhabited);
    };
    for summand in summands.into_iter().rev() {
        result = arena.value_type_sum(&[summand, result]);
    }
    Ok(result)
}

/// Decode the constructor table into a native nominal signature.
///
/// # Specification
/// - requires: parameter classifiers and `context` have matching de Bruijn
///   scopes; `kind` is the positive universe intended to bound constructor
///   fields.
/// - ensures: parameters and kind are retained; tags follow declaration order;
///   nullary codes produce no fields, products flatten in field order, and
///   recursive leaves retain the native self application. Empty data is
///   admitted.
/// - fails: non-data or multi-sort descriptions, mismatched parameter arity,
///   and unreadable field codes are declined explicitly.
/// - panics: none.
///
/// # Errors
/// Returns `CodataNu`, `MultiSorted`, `ParameterArity` or a `decode` refusal.
///
/// # Adequacy
/// - hypothesis: L3 — native signatures distinguish empty data from an empty
///   payload coproduct and retain recursive heads and constructor tag order.
/// - witness: `description::tests::native_signatures_keep_nominality_and_empty_data`
#[inline]
#[spec(ensures: |result| result.as_ref().map_or(true, |signature| signature.constructors().len() == description.ctors.len() && signature.parameters().len() == description.params.len() && signature.kind() == kind))]
pub fn decode_signature<G>(
    arena: &mut CoreArena,
    description: &SignDesc<G>,
    context: DecodeContext<'_>,
    parameters: Vec<ValueTypeId>,
    kind: ValueTypeId,
) -> Result<DataSignature, DecodeError>
{
    single_data_sort(description)?;
    if parameters.len() != description.params.len() {
        return Err(DecodeError::ParameterArity);
    }
    let mut constructors = Vec::with_capacity(description.ctors.len());
    for constructor in &description.ctors {
        let mut fields = Vec::new();
        let mut pending = vec![constructor.code.to_node()];
        while let Some(node) = pending.pop() {
            match node.view() {
                | CodeView::Unit => {},
                | CodeView::Prod(mut children) => {
                    let left = children.next().ok_or(DecodeError::MalformedCode)?;
                    let right = children.next().ok_or(DecodeError::MalformedCode)?;
                    pending.push(right);
                    pending.push(left);
                },
                | CodeView::Var(_)
                | CodeView::Sum(_)
                | CodeView::Field { .. }
                | CodeView::Bind { .. } => {
                    let field = interpret(arena, vec![Frame::Code(node)], context)?;
                    fields.push(field);
                },
            }
        }
        constructors.push(fields);
    }
    Ok(DataSignature::new(parameters, constructors, kind))
}

/// Enforce the single positive sort boundary of the native data interpretation.
///
/// # Specification
/// - ensures: success means exactly one sort and data polarity.
/// - fails: `CodataNu` for codata, `MultiSorted` for any other sort
///   cardinality.
/// - panics: none.
///
/// # Errors
/// Returns `CodataNu` or `MultiSorted`.
///
/// # Adequacy
/// - hypothesis: L3 — polarity and sort count independently separate refusals.
/// - witness: `description::tests::decode_desc_declines_codata_and_the_uninhabited`
/// - witness: `description::tests::decode_desc_declines_a_multi_sorted_signature`
#[spec(ensures: |result| result.is_ok() == (description.polarity == DeclPolarity::Data && description.sorts.len() == 1))]
fn single_data_sort<G>(description: &SignDesc<G>) -> Result<(), DecodeError>
{
    if description.polarity == DeclPolarity::Codata {
        return Err(DecodeError::CodataNu);
    }
    if description.sorts.len() != 1 {
        return Err(DecodeError::MultiSorted);
    }
    Ok(())
}

/// Drain the first-order decoder's explicit worklist.
///
/// # Specification
/// - requires: initial frames name finite code trees and resolved ids share
///   `arena`.
/// - ensures: child order and resolved nominal identity are preserved.
/// - fails: unreadable leaves and operand-stack arity failures are typed
///   errors.
/// - panics: none.
///
/// # Errors
/// Returns any leaf refusal or `MalformedCode` for an inconsistent worklist.
///
/// # Adequacy
/// - hypothesis: L3 — nested shapes and applied references expose reordered or
///   dropped operands; deferred leaves cannot become fabricated opaque types.
/// - witness: `description::tests::decode_interprets_the_first_order_fragment`
/// - witness: `description::tests::native_applications_preserve_heads_and_arguments`
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
fn interpret<G>(
    arena: &mut CoreArena,
    mut pending: Vec<Frame<'_, G>>,
    context: DecodeContext<'_>,
) -> Result<ValueTypeId, DecodeError>
{
    let mut values = Vec::new();
    let mut arguments = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            | Frame::Code(node) => match node.view() {
                | CodeView::Unit => values.push(arena.value_type_unit()),
                | CodeView::Var(sort) => {
                    if sort.as_ref() != context.self_sort.as_ref() {
                        return Err(DecodeError::ForeignSort(sort.clone()));
                    }
                    values.push(context.self_type);
                },
                | CodeView::Prod(mut children) | CodeView::Sum(mut children) => {
                    let left = children.next().ok_or(DecodeError::MalformedCode)?;
                    let right = children.next().ok_or(DecodeError::MalformedCode)?;
                    pending.push(if matches!(node.view(), CodeView::Prod(_)) {
                        Frame::Product
                    }
                    else {
                        Frame::Sum
                    });
                    pending.push(Frame::Code(right));
                    pending.push(Frame::Code(left));
                },
                | CodeView::Field { ty, .. } => pending.push(Frame::Type(ty.to_node())),
                | CodeView::Bind { .. } => return Err(DecodeError::AtomAbstraction),
            },
            | Frame::Type(node) => match node.view() {
                | ValueTypeView::Prim(primitive) => {
                    let ty = decode_primitive(arena, primitive)?;
                    values.push(ty);
                },
                | ValueTypeView::Param(name) => {
                    let ty = interpret_binding(arena, name, context)?;
                    values.push(ty);
                },
                | ValueTypeView::Ctor { head, args } => {
                    let binding = context.binding(head)?;
                    match *binding {
                        | TypeBinding::Type(_) | TypeBinding::Parameter { .. } if args.len() == 0 =>
                        {
                            let ty = interpret_binding(arena, head, context)?;
                            values.push(ty);
                        },
                        | TypeBinding::Nominal { declaration, arity } if args.len() == arity.0 => {
                            pending.push(Frame::Apply(declaration, arity));
                            let start = pending.len();
                            pending.extend(args.map(Frame::Argument));
                            let suffix = pending
                                .get_mut(start ..)
                                .ok_or(DecodeError::MalformedCode)?;
                            suffix.reverse();
                        },
                        | TypeBinding::Type(_)
                        | TypeBinding::Value(_)
                        | TypeBinding::Parameter { .. }
                        | TypeBinding::Nominal { .. } => {
                            return Err(DecodeError::AppliedType(head.clone()));
                        },
                    }
                },
            },
            | Frame::Argument(node) => {
                if let ValueTypeView::Param(name) = node.view() {
                    match *context.binding(name)? {
                        | TypeBinding::Value(value) => {
                            arguments.push(value);
                            continue;
                        },
                        | TypeBinding::Parameter { level, .. } => {
                            let value = parameter_value(arena, level, context.depth)?;
                            arguments.push(value);
                            continue;
                        },
                        | TypeBinding::Type(_) | TypeBinding::Nominal { .. } => {},
                    }
                }
                pending.push(Frame::QuoteArgument);
                pending.push(Frame::Type(node));
            },
            | Frame::QuoteArgument => {
                let ty = values.pop().ok_or(DecodeError::MalformedCode)?;
                arguments.push(arena.value_quote(ty));
            },
            | Frame::Product | Frame::Sum => {
                let right = values.pop().ok_or(DecodeError::MalformedCode)?;
                let left = values.pop().ok_or(DecodeError::MalformedCode)?;
                values.push(if matches!(frame, Frame::Product) {
                    arena.value_type_product(&[left, right])
                }
                else {
                    arena.value_type_sum(&[left, right])
                });
            },
            | Frame::Apply(declaration, arity) => {
                let start = arguments
                    .len()
                    .checked_sub(arity.0)
                    .ok_or(DecodeError::MalformedCode)?;
                let applied = arguments.drain(start ..).collect();
                values.push(arena.value_type_data(declaration, applied));
            },
        }
    }
    let result = values.pop().ok_or(DecodeError::MalformedCode)?;
    if !values.is_empty() || !arguments.is_empty() {
        return Err(DecodeError::MalformedCode);
    }
    Ok(result)
}

/// Interpret a named type without treating an ordinary index as a type code.
///
/// # Specification
/// - requires: bindings and classifiers share the arena.
/// - ensures: parameters decode at their declared universe and current scope.
/// - fails: unbound names, value bindings, malformed scopes and unapplied
///   families refuse.
/// - panics: none.
///
/// # Errors
/// Returns a name or telescope refusal rather than inventing a classifier.
///
/// # Adequacy
/// - hypothesis: L3 — a telescope with both a type and a value distinguishes
///   quotation and scope.
/// - witness: `description::tests::native_indices_remain_values_under_telescope_scope`
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
fn interpret_binding(
    arena: &mut CoreArena,
    name: &Name,
    context: DecodeContext<'_>,
) -> Result<ValueTypeId, DecodeError>
{
    match *context.binding(name)? {
        | TypeBinding::Type(ty) => Ok(ty),
        | TypeBinding::Parameter { level, classifier } => {
            let Some(&crate::ValueType::Universe {
                sort: crate::Sort::Ground(gandr_kernel_term::GroundSort::Value),
                level: ref target,
            }) = arena.value_type(classifier)
            else {
                return Err(DecodeError::AppliedType(name.clone()));
            };
            let target = target.clone();
            let value = parameter_value(arena, level, context.depth)?;
            Ok(arena.value_type_element(value, target))
        },
        | TypeBinding::Nominal {
            declaration,
            arity: TypeArity(0),
        } => Ok(arena.value_type_data(declaration, Vec::new())),
        | TypeBinding::Value(_) | TypeBinding::Nominal { .. } => {
            Err(DecodeError::AppliedType(name.clone()))
        },
    }
}

/// Resolve a telescope level in the intuitionistic parameter scope.
///
/// # Specification
/// - ensures: successful variables point to exactly `depth - level - 1`.
/// - fails: a binder outside the scope or index representation refuses.
/// - panics: none.
///
/// # Errors
/// Returns `ParameterArity` for an impossible telescope coordinate.
///
/// # Adequacy
/// - hypothesis: L3 — two different telescope depths expose an off-by-one
///   binder conversion.
/// - witness: `description::tests::native_indices_remain_values_under_telescope_scope`
#[spec(ensures: |result| result.as_ref().map_or(true, |id| matches!(arena.value(*id), Some(&crate::Value::Variable { zone: crate::Zone::Intuitionistic, index }) if usize::try_from(u32::from(index)).ok().and_then(|index| index.checked_add(level.0)).and_then(|sum| sum.checked_add(1)) == Some(depth.0))))]
fn parameter_value(
    arena: &mut CoreArena,
    level: ParameterLevel,
    depth: ParameterDepth,
) -> Result<crate::ValueId, DecodeError>
{
    let index = depth
        .0
        .checked_sub(level.0)
        .and_then(|remaining| remaining.checked_sub(1))
        .ok_or(DecodeError::ParameterArity)?;
    let index = u32::try_from(index).map_err(|_overflow| DecodeError::ParameterArity)?;
    Ok(arena.value_variable(
        crate::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(index),
    ))
}

/// Interpret supported primitives without inventing opaque substitutes.
///
/// # Specification
/// - ensures: Integer, String and Unit retain their native types; Boolean is
///   the canonical sum of two units.
/// - fails: every other primitive returns `Primitive` with its exact tag.
/// - panics: none.
///
/// # Errors
/// Returns `Primitive` when the core lacks the declared primitive semantics.
///
/// # Adequacy
/// - hypothesis: L3 — each supported primitive and every unsupported tag is
///   observed independently; Boolean's two summands are units.
/// - witness: `description::tests::decode_boolean_retrofits_to_one_plus_one`
/// - witness: `description::tests::decode_declines_the_deferred_leaves`
#[spec(ensures: |result| result.as_ref().map_or(true, |id| arena.value_type(*id).is_some()))]
fn decode_primitive(
    arena: &mut CoreArena,
    primitive: PrimTy,
) -> Result<ValueTypeId, DecodeError>
{
    match primitive {
        | PrimTy::Integer => Ok(arena.value_type_base(BaseType::Integer)),
        | PrimTy::StringTy => Ok(arena.value_type_base(BaseType::String)),
        | PrimTy::Unit => Ok(arena.value_type_unit()),
        | PrimTy::Boolean => {
            let unit = arena.value_type_unit();
            Ok(arena.value_type_sum(&[unit, unit]))
        },
        | PrimTy::Char
        | PrimTy::U32
        | PrimTy::U64
        | PrimTy::I32
        | PrimTy::I64
        | PrimTy::F32
        | PrimTy::F64
        | PrimTy::Unknown => Err(DecodeError::Primitive(primitive)),
    }
}

#[cfg(test)]
mod tests;
