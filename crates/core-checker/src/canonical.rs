//! The canonical forms that the holder of a built-in role answers.
//!
//! A role's holder is ordinary source, so the checker never believes its
//! mark. It compares the holder with the form that the role states, and
//! refuses a holder that departs from it, naming the first place where it
//! departs.
//!
//! The signature type of an inductive-recursive definition is a data
//! declaration over one parameter `O : Type`. Its constructors are, in this
//! order, `ι(e : O)`, `σ(A : Type, f : A -> Sig(O))` and
//! `δ(A : Type, f : (A -> O) -> Sig(O))`, where `Sig` is the holder applied to
//! its parameter (Kovács 2026, § 2.2). A field's type stands under the
//! parameter and the fields before it, so `O` is the variable one binder out
//! inside `ι` and two binders out inside `σ` and `δ`.
//!
//! # References
//!
//! - `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: the signature type
//!   of § 2.2 and its three constructors.

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::Purity;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Departure;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;

/// Compare the data declaration at `holder` with the canonical signature
/// type of an inductive-recursive definition.
///
/// # Specification
/// - requires: `signature` is the signature of the data declaration at
///   `holder`, its nodes in `arena`.
/// - ensures: `Ok(())` exactly when the signature has one value-universe
///   parameter, no index and the constructors `ι(e : O)`, `σ(A : Type, f : A ->
///   Sig(O))` and `δ(A : Type, f : (A -> O) -> Sig(O))` in this order, each
///   arrow pure and `Sig` the holder at its parameter.
/// - fails: the first [`Departure`] in the order parameters, indices,
///   constructors, then each constructor's arity and fields in tag and field
///   order.
/// - panics: none.
///
/// # Errors
/// - [`Departure::Parameters`]: another number of parameters, or one that is no
///   value universe.
/// - [`Departure::Indices`]: an index telescope.
/// - [`Departure::Constructors`]: another number of constructors.
/// - [`Departure::Arity`]: a constructor with another number of fields.
/// - [`Departure::Field`]: the first field whose type departs.
///
/// # Adequacy
/// - hypothesis: L3 — the canonical signature is admitted. A signature with `σ`
///   and `δ` swapped, a second parameter, two constructors, a `δ` of one field,
///   an `ι` field that is a universe and a `σ` returning another family are
///   each refused at their first departure.
/// - witness: `canonical::tests::the_canonical_signature_type_is_admitted_5254`
/// - witness: `canonical::tests::a_signature_type_is_refused_at_its_first_departure_5254`
#[spec(ensures: |ret| ret.is_err()
    || (signature.parameters().len() == 1
        && signature.indices().is_empty()
        && signature.constructors().iter().map(alloc::vec::Vec::len).eq([1_usize, 2, 2])))]
pub fn signature(
    arena: &CoreArena,
    holder: ConstantIndex,
    signature: &DataSignature,
) -> Result<(), Departure>
{
    let field = |tag: usize, position: usize| Departure::Field {
        tag: ConstructorTag::from(tag),
        field: FieldPosition::from(position),
    };
    // A variable `index` binders out, as a value of the intuitionistic zone.
    let variable = |value: ValueId, index: u32| {
        matches!(
            arena.value(value),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: found,
            }) if found == DeBruijnIndex::from(index)
        )
    };
    let universe = |value_type: ValueTypeId| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            })
        )
    };
    // The type that the variable `index` binders out decodes to.
    let element = |value_type: ValueTypeId, index: u32| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Element { code, .. }) if variable(code, index)
        )
    };
    // The domain and codomain of a thunked arrow.
    let arrow = |value_type: ValueTypeId| -> Result<(ValueTypeId, CompTypeId), ()> {
        let Some(&ValueType::Thunk(body)) = arena.value_type(value_type)
        else {
            return Err(());
        };
        match arena.comp_type(body) {
            Some(&CompType::Arrow { domain, codomain }) => Ok((domain, codomain)),
            Some(_) | None => Err(()),
        }
    };
    // The result of a pure returner.
    let returned = |comp_type: CompTypeId| -> Result<ValueTypeId, ()> {
        match arena.comp_type(comp_type) {
            Some(&CompType::Returner {
                result,
                ref effects,
            }) if effects.purity() == Purity::Pure => Ok(result),
            Some(_) | None => Err(()),
        }
    };
    // The holder applied to the variable `index` binders out.
    let family = |value_type: ValueTypeId, index: u32| {
        matches!(
            arena.value_type(value_type),
            Some(&ValueType::Data { declaration, ref arguments })
                if declaration == holder
                    && matches!(**arguments, [argument] if variable(argument, index))
        )
    };
    let [parameter] = *signature.parameters()
    else {
        return Err(Departure::Parameters);
    };
    if !universe(parameter) {
        return Err(Departure::Parameters);
    }
    if !signature.indices().is_empty() {
        return Err(Departure::Indices);
    }
    let [ref iota, ref sigma, ref delta] = *signature.constructors()
    else {
        return Err(Departure::Constructors);
    };
    // ι(e : O).
    let [stop] = **iota
    else {
        return Err(Departure::Arity(ConstructorTag::from(0_usize)));
    };
    if !element(stop, 0) {
        return Err(field(0, 0));
    }
    // σ(A : Type, f : A -> Sig(O)).
    let [shape, rest] = **sigma
    else {
        return Err(Departure::Arity(ConstructorTag::from(1_usize)));
    };
    if !universe(shape) {
        return Err(field(1, 0));
    }
    let picked = arrow(rest).and_then(|(domain, codomain)| {
        let result = returned(codomain)?;
        if element(domain, 0) && family(result, 1) {
            Ok(())
        }
        else {
            Err(())
        }
    });
    if picked.is_err() {
        return Err(field(1, 1));
    }
    // δ(A : Type, f : (A -> O) -> Sig(O)).
    let [shape, rest] = **delta
    else {
        return Err(Departure::Arity(ConstructorTag::from(2_usize)));
    };
    if !universe(shape) {
        return Err(field(2, 0));
    }
    let decoded = arrow(rest).and_then(|(domain, codomain)| {
        let result = returned(codomain)?;
        let (inner, decode) = arrow(domain)?;
        let output = returned(decode)?;
        if element(inner, 0) && element(output, 1) && family(result, 1) {
            Ok(())
        }
        else {
            Err(())
        }
    });
    if decoded.is_err() {
        return Err(field(2, 1));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
