//! Retrofitted descriptions for the primitive formers, so generic operations
//! cover builtins and declared data uniformly.
//!
//! Each function returns a [`SignDesc`] for a builtin, so the generic programs
//! of this crate — equality, serialization, inspection — apply to `Boolean`,
//! `Option`, `Pair`, sums and `List` exactly as they apply to a declared
//! datatype. The retrofits use the same first-order fragment: `Boolean` is
//! `1 + 1` (two nullary constructors); `List` is recursive through
//! [`Code::var`]. Every parameter and field carries the grade the caller
//! supplies, its own unit grade, since the grade vocabulary is the
//! consumer's.

use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::NominalSerial;
use crate::code::Attrs;
use crate::code::Code;
use crate::code::Name;
use crate::code::ValueTypeRef;
use crate::desc::CtorDesc;
use crate::desc::DeclPolarity;
use crate::desc::NominalId;
use crate::desc::ParamDesc;
use crate::desc::SignDesc;

/// The retrofit description of `Option(a)`: `None = 1`, `Some = a`.
///
/// # Specification
/// - ensures: one parameter `a` and the two constructors, in that order, at the
///   result sort `Option`; `a` and `Some`'s field carry `grade`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both stand-in grades, the nullary tag and the field tag
///   are observed through exact parameter, constructor and payload records;
///   dropped parameters, reversed tags and erased grades change those records.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::list_is_recursive`
/// - witness: `builtin::tests::retrofits_preserve_parameters_payloads_and_grades`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Option"
    && desc.params.iter().map(|param| param.name.as_ref()).eq(["a"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(["None", "Some"])
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Option"))]
pub fn option_desc<G>(grade: G) -> SignDesc<G>
where
    G: Clone,
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Option"),
        [param("a", grade.clone())],
        [
            nullary("None", "Option"),
            CtorDesc::new("Some", param_field("a", grade), "Option", Attrs::empty()),
        ],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The retrofit description of `Boolean` as `1 + 1`: two nullary
/// constructors `False` and `True`.
///
/// # Specification
/// - ensures: no parameters and the constructors `False` then `True`, so
///   `False` is tag `0` and `True` tag `1`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both nullary tags are observed through their exact
///   descriptor payloads and through generic equality; a spurious parameter,
///   swapped tags or a non-unit payload changes at least one observer.
/// - witness: `builtin::tests::generic_programs_cover_builtins_uniformly`
/// - witness: `builtin::tests::boolean_tags_are_nullary_and_parameter_free`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Boolean"
    && desc.params.is_empty()
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(["False", "True"])
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Boolean"
        && matches!(ctor.code.view(), crate::code::CodeView::Unit)))]
pub fn bool_desc<G>() -> SignDesc<G>
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Boolean"),
        Vec::new(),
        [nullary("False", "Boolean"), nullary("True", "Boolean")],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The retrofit description of `List(a)`: `Nil = 1`, `Cons = a × var`,
/// recursive through [`Code::var`].
///
/// # Specification
/// - ensures: one parameter `a`, then `Nil` and `Cons`, whose payload is the
///   field `a` times a recursive occurrence of `List`; `a` and the field carry
///   `grade`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both stand-in grades and the nil/cons boundary are
///   observed through exact payload codes and recursion status; erasing the
///   grade, reversing the product or losing the recursive sort changes them.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::list_is_recursive`
/// - witness: `builtin::tests::retrofits_preserve_parameters_payloads_and_grades`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "List"
    && desc.params.iter().map(|param| param.name.as_ref()).eq(["a"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(["Nil", "Cons"])
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "List"))]
pub fn list_desc<G>(grade: G) -> SignDesc<G>
where
    G: Clone,
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "List"),
        [param("a", grade.clone())],
        [
            nullary("Nil", "List"),
            CtorDesc::new(
                "Cons",
                Code::prod(param_field("a", grade), Code::var("List")),
                "List",
                Attrs::empty(),
            ),
        ],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The retrofit description of `Pair(a, b)`: one constructor `Pair` whose
/// payload is `a × b`.
///
/// # Specification
/// - ensures: parameters `a` and `b`, and one constructor whose payload is the
///   two fields in order; every parameter and field carries `grade`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both stand-in grades and the two distinct parameter names
///   are observed through exact parameters and the ordered payload; erasure, a
///   missing factor or swapped fields changes those records.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::retrofits_preserve_parameters_payloads_and_grades`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Pair"
    && desc.params.iter().map(|param| param.name.as_ref()).eq(["a", "b"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(["Pair"])
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Pair"))]
pub fn pair_desc<G>(grade: G) -> SignDesc<G>
where
    G: Clone,
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Pair"),
        [param("a", grade.clone()), param("b", grade.clone())],
        [CtorDesc::new(
            "Pair",
            Code::prod(param_field("a", grade.clone()), param_field("b", grade)),
            "Pair",
            Attrs::empty(),
        )],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// The retrofit description of the binary sum `Sum(a, b)`: `Inl = a`,
/// `Inr = b`.
///
/// # Specification
/// - ensures: parameters `a` and `b`, and the constructors `Inl` over `a` then
///   `Inr` over `b`; every parameter and field carries `grade`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both stand-in grades and both injection tags are observed
///   through exact parameter and field records; swapping tags or their
///   parameters, dropping an injection or erasing grades changes them.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::retrofits_preserve_parameters_payloads_and_grades`
#[inline]
#[must_use]
#[spec(ensures: |ref desc| desc.id.name.as_ref() == "Sum"
    && desc.params.iter().map(|param| param.name.as_ref()).eq(["a", "b"])
    && desc.ctors.iter().map(|ctor| ctor.name.as_ref()).eq(["Inl", "Inr"])
    && desc.ctors.iter().all(|ctor| ctor.result.as_ref() == "Sum"))]
pub fn sum_desc<G>(grade: G) -> SignDesc<G>
where
    G: Clone,
{
    SignDesc::new(
        NominalId::new(NominalSerial::from(0_u64), "Sum"),
        [param("a", grade.clone()), param("b", grade.clone())],
        [
            CtorDesc::new(
                "Inl",
                param_field("a", grade.clone()),
                "Sum",
                Attrs::empty(),
            ),
            CtorDesc::new("Inr", param_field("b", grade), "Sum", Attrs::empty()),
        ],
        Vec::new(),
        Vec::new(),
        DeclPolarity::Data,
        Attrs::empty(),
    )
}

/// An unattributed parameter of the given name and grade.
///
/// # Specification
/// trivial.
fn param<N, G>(
    name: N,
    grade: G,
) -> ParamDesc<G>
where
    N: Into<Name>,
{
    ParamDesc::new(name, grade, Attrs::empty())
}

/// A nullary constructor of the given name (`1`), targeting the result sort
/// `of`.
///
/// # Specification
/// trivial.
fn nullary<N, R, G>(
    name: N,
    of: R,
) -> CtorDesc<G>
where
    N: Into<Name>,
    R: Into<Name>,
{
    CtorDesc::new(name, Code::unit(), of, Attrs::empty())
}

/// An unattributed field over the type parameter of the given name, at the
/// given grade.
///
/// # Specification
/// trivial.
fn param_field<N, G>(
    name: N,
    grade: G,
) -> Code<G>
where
    N: Into<Name>,
{
    Code::field(ValueTypeRef::param(name), grade, Attrs::empty())
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::boundary::ConstructorTag;
    use crate::generic::DescValue;
    use crate::generic::Payload;
    use crate::generic::generic_eq;
    use crate::generic::serialize_desc;
    use crate::test_support::Grade;
    use crate::wellformed::check_desc;

    #[test]
    fn every_retrofit_is_well_formed()
    {
        for desc in [
            bool_desc(),
            option_desc(Grade::One),
            pair_desc(Grade::One),
            sum_desc(Grade::One),
            list_desc(Grade::One),
        ] {
            assert!(
                check_desc(&desc).is_empty(),
                "the retrofit `{}` is well-formed",
                desc.id.name
            );
        }
    }

    #[test]
    fn generic_programs_cover_builtins_uniformly()
    {
        // The generic consumers apply to `Boolean` exactly as to declared data.
        let boolean: SignDesc<Grade> = bool_desc();
        assert_eq!(
            "sign Boolean { sort Boolean : Type; }",
            serialize_desc(&boolean).as_ref(),
            "the builtin renders through the same inspection notation — sorts, operations, \
             and rules; constructors carry no member spelling"
        );
        let truth = DescValue::new(ConstructorTag::from(1_usize), Payload::unit());
        let falsity = DescValue::new(ConstructorTag::from(0_usize), Payload::unit());
        assert!(
            bool::from(generic_eq(&boolean, &truth, &truth)),
            "True == True"
        );
        assert!(
            !bool::from(generic_eq(&boolean, &truth, &falsity)),
            "True ≠ False"
        );
    }

    #[test]
    fn list_is_recursive()
    {
        assert!(
            bool::from(list_desc(Grade::One).is_recursive()),
            "List recurses through Cons"
        );
        assert!(
            !bool::from(option_desc(Grade::One).is_recursive()),
            "Option is non-recursive"
        );
    }

    #[test]
    fn boolean_tags_are_nullary_and_parameter_free()
    {
        let desc = bool_desc::<Grade>();
        assert_eq!(desc.id.name.as_ref(), "Boolean");
        assert!(desc.params.is_empty());
        assert_eq!(
            desc.ctors
                .iter()
                .map(|ctor| ctor.name.as_ref())
                .collect::<Vec<_>>(),
            ["False", "True"]
        );
        for ctor in &desc.ctors {
            assert_eq!(ctor.result.as_ref(), "Boolean");
            assert_eq!(ctor.code, Code::unit());
        }
    }

    #[test]
    fn retrofits_preserve_parameters_payloads_and_grades()
    {
        for grade in [Grade::One, Grade::Omega] {
            let field_a = Code::field(ValueTypeRef::param("a"), grade, Attrs::empty());
            let field_b = Code::field(ValueTypeRef::param("b"), grade, Attrs::empty());
            for (desc, params, names, codes, result) in [
                (
                    option_desc(grade),
                    &["a"][..],
                    &["None", "Some"][..],
                    alloc::vec![Code::unit(), field_a.clone()],
                    "Option",
                ),
                (
                    list_desc(grade),
                    &["a"][..],
                    &["Nil", "Cons"][..],
                    alloc::vec![Code::unit(), Code::prod(field_a.clone(), Code::var("List"))],
                    "List",
                ),
                (
                    pair_desc(grade),
                    &["a", "b"][..],
                    &["Pair"][..],
                    alloc::vec![Code::prod(field_a.clone(), field_b.clone())],
                    "Pair",
                ),
                (
                    sum_desc(grade),
                    &["a", "b"][..],
                    &["Inl", "Inr"][..],
                    alloc::vec![field_a, field_b],
                    "Sum",
                ),
            ] {
                assert_eq!(desc.id.name.as_ref(), result);
                assert_eq!(
                    desc.params
                        .iter()
                        .map(|param| param.name.as_ref())
                        .collect::<Vec<_>>(),
                    params
                );
                assert!(desc.params.iter().all(|param| param.grade == grade));
                assert_eq!(
                    desc.ctors
                        .iter()
                        .map(|ctor| ctor.name.as_ref())
                        .collect::<Vec<_>>(),
                    names
                );
                assert!(desc.ctors.iter().all(|ctor| ctor.result.as_ref() == result));
                assert_eq!(
                    desc.ctors.iter().map(|ctor| &ctor.code).collect::<Vec<_>>(),
                    codes.iter().collect::<Vec<_>>()
                );
            }
        }
    }
}
