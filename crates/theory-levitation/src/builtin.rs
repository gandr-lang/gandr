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
/// - hypothesis: L3 — the retrofit passes the declaration table and is not
///   recursive.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::list_is_recursive`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — the generic programs read the retrofit as they read a
///   declared datatype: it renders, and its two values compare by tag.
/// - witness: `builtin::tests::generic_programs_cover_builtins_uniformly`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — the retrofit passes the declaration table and is
///   recursive.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
/// - witness: `builtin::tests::list_is_recursive`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — the retrofit passes the declaration table.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
#[inline]
#[must_use]
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
/// - hypothesis: L3 — the retrofit passes the declaration table.
/// - witness: `builtin::tests::every_retrofit_is_well_formed`
#[inline]
#[must_use]
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
}
