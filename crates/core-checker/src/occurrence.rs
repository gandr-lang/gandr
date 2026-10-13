//! The strict-positivity walk a data declaration passes before its fields
//! form, mirroring the kernel's.
//!
//! A declaration's own admission position names the block being admitted. A
//! field may name it in exactly two forms — directly, `T ps`, or as the
//! codomain of a thunked function whose domains do not name it,
//! `U (Π ȳ. F (T ps))` — and always at the parameter variables in telescope
//! order. Every other occurrence is refused by name, and a reference to a
//! later position is a reference outside the block.
//!
//! Both checkers run this walk before a data declaration forms and refuse by
//! the same names: `NegativeOccurrence`, `NestedOccurrence`, `IndexOccurrence`,
//! `NonUniformOccurrence` and `CrossBlockReference`, each carrying the kernel's
//! `OccurrenceSite` and each classified as malformed source. A declaration the
//! checker admits, the kernel admits on readmission; one it refuses never
//! reaches the bridge. Witness:
//! `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::OccurrenceSite;
use gandr_kernel_term::ParameterPosition;

use crate::CheckRefusal;

/// Any node of the core arena, as one ordered key.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AnyNode
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Which head a [`Reach::Head`] stands at.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum HeadSite
{
    /// The field's own type, the one place a thunk opens a function.
    Field,
    /// The type a function codomain returns.
    Codomain,
}

/// Where a node stands relative to the two admitted recursive field forms.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reach
{
    /// A field's own type, or the type a function codomain returns, under
    /// `depth` binders: a uniform self application is admitted here.
    Head
    {
        /// The binders crossed since the field's root.
        depth: Binders,
        /// Which head this is.
        site: HeadSite,
    },
    /// The computation type under the field's thunk, before any domain.
    Thunk,
    /// The computation type past at least one function domain, under `depth`
    /// binders.
    Chain
    {
        /// The binders crossed since the field's root.
        depth: Binders,
    },
    /// Under a function's domain, at any depth.
    Domain,
    /// Inside another family's arguments or under a field-local former.
    Nested,
    /// Inside a term a type reads.
    Term,
}

/// What a self occurrence earns at its reach, least severe first.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Finding
{
    /// No refused occurrence.
    Admitted,
    /// A head occurrence at non-parameter arguments.
    NonUniform,
    /// An occurrence nested in another former.
    Nested,
    /// An occurrence inside a term a type reads.
    Index,
    /// An occurrence under a function's domain.
    Negative,
}

/// Whether a self application's arguments are the parameter variables.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Uniformity
{
    /// One argument per parameter, each the parameter's variable in order.
    Uniform,
    /// Anything else.
    NonUniform,
}

/// The length of a declaration's parameter telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Telescope(usize);

/// The reach of a child that nests inside a former at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn nest(reach: Reach) -> Reach
{
    match reach {
        | Reach::Domain => Reach::Domain,
        | Reach::Term => Reach::Term,
        | Reach::Head { .. } | Reach::Thunk | Reach::Chain { .. } | Reach::Nested => Reach::Nested,
    }
}

/// The reach of a child a type reads as a term, from a former at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn term(reach: Reach) -> Reach
{
    match reach {
        | Reach::Domain => Reach::Domain,
        | Reach::Head { .. } | Reach::Thunk | Reach::Chain { .. } | Reach::Nested | Reach::Term => {
            Reach::Term
        },
    }
}

/// Whether `arguments` are the parameter variables in telescope order, seen
/// from under `depth` binders past the telescope.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Uniform` exactly when there is one argument per parameter and
///   the `i`th is the intuitionistic variable at distance `depth + parameters -
///   1 - i`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a family applied to a constant or to its parameters out
///   of order is non-uniform; `List A` applied to `A`, directly and under a
///   function field's binder, is uniform.
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
#[spec(ensures: |ret| ret == Uniformity::NonUniform || arguments.len() == telescope.0)]
fn uniform(
    arena: &CoreArena,
    arguments: &[ValueId],
    depth: Binders,
    telescope: Telescope,
) -> Uniformity
{
    let Telescope(parameters) = telescope;
    let all = arguments.len() == parameters
        && arguments.iter().enumerate().all(|(position, &argument)| {
            let expected = usize::try_from(u32::from(depth))
                .ok()
                .and_then(|depth| depth.checked_add(parameters))
                .and_then(|scope| scope.checked_sub(position))
                .and_then(|scope| scope.checked_sub(1))
                .and_then(|distance| u32::try_from(distance).ok())
                .map(DeBruijnIndex::from);
            matches!(
                (arena.value(argument), expected),
                (Some(&Value::Variable { zone: Zone::Intuitionistic, index }), Some(wanted)) if index == wanted
            )
        });
    if all {
        Uniformity::Uniform
    }
    else {
        Uniformity::NonUniform
    }
}

/// The finding of a self occurrence at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn found(
    reach: Reach,
    uniformity: Uniformity,
) -> Finding
{
    match (reach, uniformity) {
        | (Reach::Domain, _) => Finding::Negative,
        | (Reach::Term, _) => Finding::Index,
        | (Reach::Nested | Reach::Thunk | Reach::Chain { .. }, _) => Finding::Nested,
        | (Reach::Head { .. }, Uniformity::Uniform) => Finding::Admitted,
        | (Reach::Head { .. }, Uniformity::NonUniform) => Finding::NonUniform,
    }
}

/// The reach a thunk's body takes from a thunk type at `reach`.
///
/// # Specification
/// trivial.
#[inline]
const fn thunked(reach: Reach) -> Reach
{
    match reach {
        | Reach::Head {
            site: HeadSite::Field,
            ..
        } => Reach::Thunk,
        | Reach::Head {
            site: HeadSite::Codomain,
            ..
        }
        | Reach::Thunk
        | Reach::Chain { .. }
        | Reach::Domain
        | Reach::Nested
        | Reach::Term => nest(reach),
    }
}

/// The reach a function codomain takes from a function type at `reach`,
/// past one domain that binds when `binds` holds.
///
/// # Specification
/// trivial.
#[inline]
fn codomain(
    reach: Reach,
    binds: Binding,
) -> Reach
{
    let past = |depth: Binders| match binds {
        | Binding::Binds => depth.deeper(),
        | Binding::Closed => depth,
    };
    match reach {
        | Reach::Thunk => Reach::Chain {
            depth: past(Binders::NONE),
        },
        | Reach::Chain { depth } => Reach::Chain { depth: past(depth) },
        | Reach::Head { .. } | Reach::Domain | Reach::Nested | Reach::Term => reach,
    }
}

/// Whether a function type's codomain stands under its domain's binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// A dependent arrow: the codomain is under one binder.
    Binds,
    /// A plain arrow: the codomain is closed over the domain.
    Closed,
}

/// The most severe self occurrence in one root's type, or the first later
/// position it names.
///
/// # Specification
/// - requires: `telescope` is the declaration's telescope length and `root` is
///   scoped under it.
/// - ensures: `Err(index)` when the root names a position after `position`;
///   otherwise the most severe finding over every self occurrence, with the two
///   admitted forms finding nothing.
/// - provides: the syntactic half of strict positivity; formation is the other
///   half.
/// - fails: a later position, as its index.
/// - panics: none.
///
/// # Errors
/// The later position a reference names.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node and reach pair
///   is expanded once.
/// - measure: the unexpanded pairs reachable from the root, finite because the
///   arena is acyclic and reaches are finite per node.
///
/// # Adequacy
/// - hypothesis: L3 — a negative, a nested, an index and a non-uniform
///   occurrence, and a reference to a later position, each surface as their own
///   finding, while the direct and function forms of `Nat`, `List A` and `Tree`
///   find nothing.
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|later| *later > position))]
fn worst(
    arena: &CoreArena,
    position: ConstantIndex,
    telescope: Telescope,
    root: ValueTypeId,
    start: Reach,
) -> Result<Finding, ConstantIndex>
{
    let mut pending: Vec<(AnyNode, Reach)> = Vec::from([(AnyNode::ValueType(root), start)]);
    let mut seen: BTreeSet<(AnyNode, Reach)> = BTreeSet::new();
    let mut worst = Finding::Admitted;
    while let Some((node, reach)) = pending.pop() {
        if !seen.insert((node, reach)) {
            continue;
        }
        match node {
            | AnyNode::ValueType(id) => match arena.value_type(id) {
                | Some(&ValueType::Data {
                    declaration,
                    ref arguments,
                }) => {
                    if declaration > position {
                        return Err(declaration);
                    }
                    let inner = if declaration == position {
                        let depth = match reach {
                            | Reach::Head { depth, .. } => depth,
                            | Reach::Thunk
                            | Reach::Chain { .. }
                            | Reach::Domain
                            | Reach::Nested
                            | Reach::Term => Binders::NONE,
                        };
                        let admitted = uniform(arena, arguments, depth, telescope);
                        worst = worst.max(found(reach, admitted));
                        term(reach)
                    }
                    else {
                        nest(reach)
                    };
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), inner)),
                    );
                },
                | Some(&ValueType::Abstract(index)) => {
                    if index > position {
                        return Err(index);
                    }
                    if index == position {
                        worst = worst.max(found(term(reach), Uniformity::NonUniform));
                    }
                },
                | Some(&ValueType::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::ValueType(field), nest(reach))),
                    );
                },
                | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                    pending.extend(
                        parts
                            .iter()
                            .map(|&part| (AnyNode::ValueType(part), nest(reach))),
                    );
                },
                | Some(&ValueType::Lift { inner, .. }) => {
                    pending.push((AnyNode::ValueType(inner), term(reach)));
                },
                | Some(&ValueType::StaticPi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), term(reach)));
                    pending.push((AnyNode::ValueType(codomain), term(reach)));
                },
                | Some(&ValueType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), term(reach)));
                },
                | Some(&ValueType::PathUniverse(source, target)) => {
                    pending.push((AnyNode::Value(source), term(reach)));
                    pending.push((AnyNode::Value(target), term(reach)));
                },
                | Some(&ValueType::Path {
                    carrier,
                    left,
                    right,
                }) => {
                    pending.push((AnyNode::ValueType(carrier), nest(reach)));
                    pending.push((AnyNode::Value(left), term(reach)));
                    pending.push((AnyNode::Value(right), term(reach)));
                },
                | Some(&ValueType::Thunk(body)) => {
                    pending.push((AnyNode::CompType(body), thunked(reach)));
                },
                | Some(&ValueType::List(element)) => {
                    pending.push((AnyNode::ValueType(element), nest(reach)));
                },
                | Some(&ValueType::Stack { input, output }) => {
                    pending.push((AnyNode::CompType(input), Reach::Domain));
                    pending.push((AnyNode::CompType(output), nest(reach)));
                },
                | Some(&(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Unknown))
                | None => {},
            },
            | AnyNode::CompType(id) => match arena.comp_type(id) {
                | Some(&CompType::Arrow {
                    domain,
                    codomain: rest,
                }) => {
                    pending.push((AnyNode::ValueType(domain), Reach::Domain));
                    pending.push((AnyNode::CompType(rest), codomain(reach, Binding::Closed)));
                },
                | Some(&CompType::Pi {
                    domain,
                    codomain: rest,
                }) => {
                    pending.push((AnyNode::ValueType(domain), Reach::Domain));
                    pending.push((AnyNode::CompType(rest), codomain(reach, Binding::Binds)));
                },
                | Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => {
                    let inner = match reach {
                        | Reach::Chain { depth } => Reach::Head {
                            depth,
                            site: HeadSite::Codomain,
                        },
                        | Reach::Thunk => Reach::Nested,
                        | Reach::Head { .. } | Reach::Domain | Reach::Nested | Reach::Term => reach,
                    };
                    pending.push((AnyNode::ValueType(result), inner));
                    pending.extend(
                        effects
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), nest(reach))),
                    );
                },
                | Some(&CompType::With(first, second)) => {
                    pending.push((AnyNode::CompType(first), nest(reach)));
                    pending.push((AnyNode::CompType(second), nest(reach)));
                },
                | Some(&CompType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), term(reach)));
                },
                | Some(&CompType::Unknown) | None => {},
            },
            | AnyNode::Value(id) => match arena.value(id) {
                | Some(&Value::Constant(index)) => {
                    if index > position {
                        return Err(index);
                    }
                    if index == position {
                        worst = worst.max(found(term(reach), Uniformity::NonUniform));
                    }
                },
                | Some(&Value::Constructor {
                    datatype,
                    ref fields,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(datatype), reach));
                    pending.extend(fields.iter().map(|&field| (AnyNode::Value(field), reach)));
                },
                | Some(&Value::Record(ref fields)) => {
                    pending.extend(fields.values().map(|&field| (AnyNode::Value(field), reach)));
                },
                | Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    pending.push((AnyNode::ValueType(path_type), reach));
                    pending.push((AnyNode::Value(forward), reach));
                    pending.push((AnyNode::Value(backward), reach));
                },
                | Some(&Value::Tuple(ref components)) => {
                    pending.extend(
                        components
                            .iter()
                            .map(|&component| (AnyNode::Value(component), reach)),
                    );
                },
                | Some(
                    &(Value::PathProduct(first, second)
                    | Value::Funext(first, second)
                    | Value::Equiv(first, second)
                    | Value::ListCons(first, second)
                    | Value::StaticApplication(first, second)),
                ) => {
                    pending.push((AnyNode::Value(first), reach));
                    pending.push((AnyNode::Value(second), reach));
                },
                | Some(&Value::Reify(ref frames)) => {
                    for frame in frames.iter() {
                        match *frame {
                            | StackFrame::Apply(value) => {
                                pending.push((AnyNode::Value(value), reach));
                            },
                            | StackFrame::Bind(body) => {
                                pending.push((AnyNode::Computation(body), reach));
                            },
                            | StackFrame::Project(_) => {},
                        }
                    }
                },
                | Some(
                    &(Value::PathRefl(body)
                    | Value::Here(body)
                    | Value::Injection(_, body)
                    | Value::Lift { body, .. }
                    | Value::StaticLambda(body)
                    | Value::Mark { body, .. }),
                ) => {
                    pending.push((AnyNode::Value(body), reach));
                },
                | Some(&(Value::Thunk(body) | Value::Returned(body))) => {
                    pending.push((AnyNode::Computation(body), reach));
                },
                | Some(&Value::Quote(quoted)) => pending.push((AnyNode::ValueType(quoted), reach)),
                | Some(&Value::QuoteComputation(quoted)) => {
                    pending.push((AnyNode::CompType(quoted), reach));
                },
                | Some(
                    &(Value::Primitive { .. }
                    | Value::Variable { .. }
                    | Value::ListNil
                    | Value::Literal(_)
                    | Value::Hole(_)),
                )
                | None => {},
            },
            | AnyNode::Computation(id) => match arena.computation(id) {
                | Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), reach));
                    pending.push((AnyNode::CompType(motive), reach));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&branch| (AnyNode::Computation(branch), reach)),
                    );
                },
                | Some(&Computation::Primitive { ref arguments, .. }) => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), reach)),
                    );
                },
                | Some(
                    &(Computation::RecordProjection(value, _)
                    | Computation::TupleProjection(value, _)
                    | Computation::Return(value)
                    | Computation::Force(value)),
                ) => {
                    pending.push((AnyNode::Value(value), reach));
                },
                | Some(
                    &(Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. }
                    | Computation::Mark { body, .. }
                    | Computation::Reset(body)
                    | Computation::Shift(body)
                    | Computation::Project(_, body)),
                ) => {
                    pending.push((AnyNode::Computation(body), reach));
                },
                | Some(&Computation::With(first, second)) => {
                    pending.push((AnyNode::Computation(first), reach));
                    pending.push((AnyNode::Computation(second), reach));
                },
                | Some(
                    &(Computation::Resume(stack, body)
                    | Computation::Split {
                        scrutinee: stack,
                        body,
                        ..
                    }),
                ) => {
                    pending.push((AnyNode::Value(stack), reach));
                    pending.push((AnyNode::Computation(body), reach));
                },
                | Some(&Computation::Perform {
                    ref signature,
                    payload,
                    ..
                }) => {
                    pending.push((AnyNode::Value(payload), reach));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach)),
                    );
                },
                | Some(&Computation::Handle {
                    ref signature,
                    subject,
                    on_return,
                    ref clauses,
                }) => {
                    pending.push((AnyNode::Computation(subject), reach));
                    pending.push((AnyNode::Computation(on_return), reach));
                    pending.extend(
                        clauses
                            .iter()
                            .map(|clause| (AnyNode::Computation(clause.body), reach)),
                    );
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), reach)),
                    );
                },
                | Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.push((AnyNode::ValueType(element), reach));
                    pending.push((AnyNode::ValueType(result), reach));
                    pending.push((AnyNode::Value(list), reach));
                    pending.push((AnyNode::Computation(on_nil), reach));
                    pending.push((AnyNode::Computation(on_cons), reach));
                },
                | Some(&Computation::Application(head, argument)) => {
                    pending.push((AnyNode::Computation(head), reach));
                    pending.push((AnyNode::Value(argument), reach));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    pending.push((AnyNode::Computation(bound), reach));
                    pending.push((AnyNode::Computation(body), reach));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), reach));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&branch| (AnyNode::Computation(branch), reach)),
                    );
                },
                | Some(&Computation::Transport(path, value)) => {
                    pending.push((AnyNode::Value(path), reach));
                    pending.push((AnyNode::Value(value), reach));
                },
                | Some(&Computation::PathTransport {
                    motive,
                    path,
                    value,
                }) => {
                    pending.push((AnyNode::ValueType(motive), term(reach)));
                    pending.push((AnyNode::Value(path), reach));
                    pending.push((AnyNode::Value(value), reach));
                },
                | Some(&Computation::Hole(_)) | None => {},
            },
        }
    }
    Ok(worst)
}

/// The refusal a finding earns at one site.
///
/// # Specification
/// trivial.
#[inline]
const fn refusal(
    finding: Finding,
    site: OccurrenceSite,
) -> Result<(), CheckRefusal>
{
    match finding {
        | Finding::Admitted => Ok(()),
        | Finding::NonUniform => Err(CheckRefusal::NonUniformOccurrence(site)),
        | Finding::Nested => Err(CheckRefusal::NestedOccurrence(site)),
        | Finding::Index => Err(CheckRefusal::IndexOccurrence(site)),
        | Finding::Negative => Err(CheckRefusal::NegativeOccurrence(site)),
    }
}

/// Refuse every occurrence of a data declaration's own family outside the
/// two admitted field forms, and every reference past its block.
///
/// # Specification
/// - requires: `position` is the admission position the declaration takes, and
///   `signature`'s parameters and fields are scoped as the signature states.
/// - ensures: success exactly when no parameter names the family, every field
///   names it only directly or as a thunked function's codomain whose domains
///   do not name it, always at the parameter variables in order, and nothing
///   names a later position.
/// - provides: the strict-positivity and head-uniformity judgement the
///   formation of a recursive block rests on; it runs before any field forms,
///   as the kernel's does, so both checkers refuse the same site by the same
///   name.
/// - fails: the first site in parameter-then-field order that refuses.
/// - panics: none.
///
/// # Errors
/// `CrossBlockReference`, `NegativeOccurrence`, `IndexOccurrence`,
/// `NestedOccurrence` or `NonUniformOccurrence` at the refused site; a
/// parameter naming the family is always an index occurrence.
///
/// # Adequacy
/// - hypothesis: L3 — `Nat`, `List A` and `Tree` with a function field are
///   admitted; a `T → A` field domain, a non-uniform head, a later reference, a
///   nested and an index occurrence are each refused by name at their site, by
///   this checker and by the kernel.
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(
    CheckRefusal::CrossBlockReference { .. }
    | CheckRefusal::NegativeOccurrence(_)
    | CheckRefusal::IndexOccurrence(_)
    | CheckRefusal::NestedOccurrence(_)
    | CheckRefusal::NonUniformOccurrence(_))))]
pub fn occurrences(
    arena: &CoreArena,
    position: ConstantIndex,
    signature: &DataSignature,
) -> Result<(), CheckRefusal>
{
    for (index, &parameter) in signature.parameters().iter().enumerate() {
        let site = OccurrenceSite::Parameter(ParameterPosition::from(index));
        let finding = worst(arena, position, Telescope(index), parameter, Reach::Term)
            .map_err(|later| CheckRefusal::CrossBlockReference { site, index: later })?;
        if finding != Finding::Admitted {
            return Err(CheckRefusal::IndexOccurrence(site));
        }
    }
    let telescope = Telescope(signature.parameters().len());
    for (tag, fields) in signature.constructors().iter().enumerate() {
        for (field, &root) in fields.iter().enumerate() {
            let site = OccurrenceSite::Field {
                tag: ConstructorTag::from(tag),
                field: FieldPosition::from(field),
            };
            let finding = worst(arena, position, telescope, root, Reach::Head {
                depth: Binders::NONE,
                site: HeadSite::Field,
            })
            .map_err(|later| CheckRefusal::CrossBlockReference { site, index: later })?;
            refusal(finding, site)?;
        }
    }
    Ok(())
}
