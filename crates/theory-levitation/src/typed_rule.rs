//! Typed 2-cell faces: a [`RuleFace`] together with a signature context.
//!
//! A [`RuleFace`] stores a rewrite `lhs ==> rhs` as an untyped pair of
//! [`FreeTerm`]s with host-side well-formedness ([`check_desc`]). A typed face
//! is that face together with a signature context: each pattern variable
//! paired with the type it ranges over, the decoded type of the field the
//! variable fills. The signature context is the head of a dependent sum over
//! the signature, the two free terms its tail.
//!
//! The type universe is the consumer's: the context is generic over the
//! decoded type `T`, and the decoder that reads a field code into a `T` is
//! supplied by the caller ([`PatternContext::from_field_codes`]). This crate
//! never names a core type. The face is reused whole; a typed face wraps it
//! and changes nothing about its encoding.
//!
//! [`FreeTerm`]: crate::FreeTerm
//! [`check_desc`]: crate::check_desc

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::ContextTotality;
use crate::boundary::NameRef;
use crate::code::Code;
use crate::code::Name;
use crate::rule::RuleFace;

quenchant_shape::reason_enum! {
    /// Why a signature context types no pattern variable of a name.
    pub mod pattern_variable {
        /// The reason the variable is untyped.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The context binds no variable of that name.
            Unbound,
        }
    }
}

/// A signature context for a rule face: each pattern variable paired with the
/// type it ranges over, the head of the typed face.
///
/// The types are obtained by decoding each variable's field code, so the
/// context is a bridge from the description layer into the consumer's type
/// universe.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PatternContext<T>
{
    /// The pattern variables and their decoded types, in declaration order.
    pub vars: Box<[(Name, T)]>,
}

impl<T> PatternContext<T>
{
    /// A context from explicit `{variable, decoded type}` bindings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new<V>(vars: V) -> Self
    where
        V: Into<Box<[(Name, T)]>>,
    {
        Self { vars: vars.into() }
    }

    /// Build a signature context by decoding each pattern variable's field
    /// code with `decode`.
    ///
    /// # Specification
    /// - requires: `bindings` pairs each pattern variable with the first-order
    ///   field code it fills; `decode` reads a field code into the consumer's
    ///   type universe.
    /// - ensures: a context binding each variable to `decode` of its code, in
    ///   the given order.
    /// - fails: the first error `decode` returns, which stops the build.
    /// - panics: none of its own; a panic in `decode` propagates.
    ///
    /// # Errors
    /// Returns the first error `decode` raises on a binding's code.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, successful multi-binding and failed-prefix
    ///   inputs are observed through exact bindings, errors and decoder calls;
    ///   reordering, a skipped binding, a second decode or continuing past the
    ///   first refusal changes an observer.
    /// - witness: `typed_rule::tests::signature_context_decodes_field_codes`
    /// - witness: `typed_rule::tests::signature_context_propagates_decode_failure`
    /// - witness: `typed_rule::tests::context_decoding_visits_each_binding_once_and_stops_at_failure`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        | Ok(ref context) => context.vars.len() == bindings.len()
            && context.vars.iter().zip(bindings).all(|(bound, input)| bound.0 == input.0),
        | Err(_) => !bindings.is_empty(),
    })]
    pub fn from_field_codes<G, E, D>(
        bindings: &[(Name, Code<G>)],
        mut decode: D,
    ) -> Result<Self, E>
    where
        D: FnMut(&Code<G>) -> Result<T, E>,
    {
        let mut vars = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let (ref name, ref code) = *binding;
            vars.push((name.clone(), decode(code)?));
        }
        Ok(Self { vars: vars.into() })
    }

    /// The decoded type bound to `var`.
    ///
    /// # Specification
    /// - ensures: the type of the first binding named `var`, or
    ///   [`pattern_variable::Absent::Unbound`] when no binding is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty contexts, missing names and duplicate names
    ///   with distinct types separate absence, wrong-name lookup and selecting
    ///   a later duplicate; the returned type is the observer.
    /// - witness: `typed_rule::tests::signature_context_decodes_field_codes`
    /// - witness: `typed_rule::tests::context_lookup_selects_the_first_duplicate`
    #[inline]
    #[spec(ensures: |ref found| match *found {
        | Maybe::Present(ty) => self.vars.iter().find(|binding| binding.0.as_ref() == var.as_ref())
            .is_some_and(|binding| core::ptr::eq(core::ptr::from_ref(ty), &raw const binding.1)),
        | Maybe::Absent(_) => self.vars.iter().all(|binding| binding.0.as_ref() != var.as_ref()),
    })]
    pub fn type_of(
        &self,
        var: NameRef<'_>,
    ) -> Maybe<&T, pattern_variable::Absent>
    {
        self.vars
            .iter()
            .find(|binding| binding.0.as_ref() == var.as_ref())
            .map_or(
                Maybe::Absent(pattern_variable::Absent::Unbound),
                |binding| Maybe::Present(&binding.1),
            )
    }
}

/// A typed 2-cell face: a [`RuleFace`] refined with a decoded
/// [`PatternContext`].
///
/// The face is reused whole — its untyped term pair, its derived variable
/// metadata and its provenance — never rewritten.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypedRuleFace<T>
{
    /// The untyped face, reused whole.
    pub face: RuleFace,
    /// The decoded signature context typing the face's pattern variables.
    pub context: PatternContext<T>,
}

impl<T> TypedRuleFace<T>
{
    /// A typed face from an untyped face and its decoded signature context.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        face: RuleFace,
        context: PatternContext<T>,
    ) -> Self
    {
        Self { face, context }
    }

    /// Whether every pattern variable the face declares (its derived variable
    /// metadata) is typed by the context.
    ///
    /// # Specification
    /// - ensures: positive exactly when every `self.face.vars` entry's variable
    ///   has a [`PatternContext::type_of`] entry.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no declared variables, all typed variables and a
    ///   missing declared variable separate vacuous totality from partial
    ///   coverage; the verdict detects inverted or existential quantification.
    /// - witness: `typed_rule::tests::typed_face_context_totality_tracks_declared_variables`
    /// - witness: `typed_rule::tests::an_empty_face_context_is_total`
    #[inline]
    #[must_use]
    #[spec(ensures: |total| bool::from(total) == self.face.vars.iter().all(|meta| {
        self.context.vars.iter().any(|binding| binding.0 == meta.var)
    }))]
    pub fn is_context_total(&self) -> ContextTotality
    {
        ContextTotality::from(self.face.vars.iter().all(|meta| {
            matches!(
                self.context.type_of(meta.var.as_name_ref()),
                Maybe::Present(_)
            )
        }))
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::*;
    use crate::boundary::RuleVariableLinearity;
    use crate::code::AtomSort;
    use crate::code::Attrs;
    use crate::code::CodeView;
    use crate::code::PrimTy;
    use crate::code::ValueTypeRef;
    use crate::code::ValueTypeView;
    use crate::desc::SurfaceSpan;
    use crate::rule::FreeTerm;
    use crate::rule::RuleVarMeta;
    use crate::rule::Variance;
    use crate::test_support::Grade;

    /// A stand-in type universe for the decoder the consumer supplies.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum TestType
    {
        /// The unit type.
        Unit,
        /// The integer type.
        Integer,
        /// The carrier of the description being typed.
        Carrier,
    }

    /// The stand-in decoder's refusals.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum TestDecodeError
    {
        /// An atom-abstraction, which this decoder does not read.
        AtomAbstraction,
        /// Any other code shape this decoder does not read.
        Unsupported,
    }

    /// A stand-in decoder: `1` to the unit type, an `Integer` field to the
    /// integer type, `var Self` to the carrier; an atom-abstraction is
    /// refused.
    ///
    /// # Specification
    /// - ensures: unit, integer fields and the recursive sort `Self` decode to
    ///   their corresponding stand-in types.
    /// - fails: atom abstractions have their own error; every other unsupported
    ///   former has `TestDecodeError::Unsupported`.
    /// - panics: none.
    ///
    /// # Errors
    /// Refuses an atom abstraction or an unsupported former.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported unit, integer and self-recursive codes are
    ///   separated from a different recursive sort and a non-integer field by
    ///   exact types/errors; missing arms and broadened support fail a witness.
    /// - witness: `typed_rule::tests::signature_context_decodes_field_codes`
    /// - witness: `typed_rule::tests::signature_context_propagates_decode_failure`
    /// - witness: `typed_rule::tests::decoder_distinguishes_recursive_and_field_boundaries`
    #[spec(ensures: |ref result| matches!(*result, Err(TestDecodeError::AtomAbstraction))
        == matches!(code.view(), CodeView::Bind { .. }))]
    fn decode(code: &Code<Grade>) -> Result<TestType, TestDecodeError>
    {
        match code.view() {
            | CodeView::Unit => Ok(TestType::Unit),
            | CodeView::Field { ty, .. } => match ty.view() {
                | ValueTypeView::Prim(PrimTy::Integer) => Ok(TestType::Integer),
                | _ => Err(TestDecodeError::Unsupported),
            },
            | CodeView::Var(sort) if sort.as_ref() == "Self" => Ok(TestType::Carrier),
            | CodeView::Bind { .. } => Err(TestDecodeError::AtomAbstraction),
            | _ => Err(TestDecodeError::Unsupported),
        }
    }

    /// An `Integer` field code.
    ///
    /// # Specification
    /// trivial.
    fn integer_field() -> Code<Grade>
    {
        Code::field(
            ValueTypeRef::prim(PrimTy::Integer),
            Grade::One,
            Attrs::empty(),
        )
    }

    #[test]
    fn signature_context_decodes_field_codes()
    {
        let ctx = PatternContext::from_field_codes(
            &[("x".into(), integer_field()), ("y".into(), Code::unit())],
            decode,
        )
        .expect("first-order fields decode");
        assert_eq!(
            Maybe::Present(&TestType::Integer),
            ctx.type_of(NameRef::from("x")),
            "the primitive field decodes to its type"
        );
        assert_eq!(
            Maybe::Present(&TestType::Unit),
            ctx.type_of(NameRef::from("y")),
            "the unit code decodes to the unit type"
        );
        assert_eq!(
            Maybe::Absent(pattern_variable::Absent::Unbound),
            ctx.type_of(NameRef::from("z")),
            "an unbound variable has no type"
        );
    }

    #[test]
    fn typed_face_context_totality_tracks_declared_variables()
    {
        // The face `f(x) ==> x` declares the pattern variable `x`.
        let face = RuleFace::new(
            FreeTerm::op("f", [FreeTerm::var("x")]),
            FreeTerm::var("x"),
            [RuleVarMeta::new(
                "x",
                Variance::Producer,
                RuleVariableLinearity::from(true),
            )],
            SurfaceSpan::new(0_usize.into(), 4_usize.into()),
        );
        let typed = TypedRuleFace::new(
            face.clone(),
            PatternContext::from_field_codes(&[("x".into(), integer_field())], decode)
                .expect("decodes"),
        );
        assert!(
            bool::from(typed.is_context_total()),
            "every declared pattern variable is typed"
        );

        // A context missing `x` is not total.
        let untyped: TypedRuleFace<TestType> =
            TypedRuleFace::new(face, PatternContext::new(Vec::new()));
        assert!(
            !bool::from(untyped.is_context_total()),
            "a variable with no decoded type breaks totality"
        );
    }

    #[test]
    fn signature_context_propagates_decode_failure()
    {
        let bind = Code::bind(AtomSort::named("a"), Code::var("Self"));
        let result = PatternContext::from_field_codes(&[("x".into(), bind)], decode);
        assert_eq!(
            Err(TestDecodeError::AtomAbstraction),
            result,
            "a field code the decoder refuses fails the context build"
        );
    }

    #[test]
    fn context_decoding_visits_each_binding_once_and_stops_at_failure()
    {
        let mut calls = Vec::new();
        let empty = PatternContext::from_field_codes::<Grade, _, _>(&[], |code| {
            calls.push(code.clone());
            decode(code)
        })
        .expect("empty decoding succeeds");
        assert!(empty.vars.is_empty());
        assert!(calls.is_empty());
        let bad = Code::bind(AtomSort::named("a"), Code::unit());
        let bindings = [
            (Name::from("x"), integer_field()),
            (Name::from("y"), bad.clone()),
            (Name::from("z"), Code::unit()),
        ];
        let failed = PatternContext::from_field_codes(&bindings, |code| {
            calls.push(code.clone());
            decode(code)
        });
        assert_eq!(failed, Err(TestDecodeError::AtomAbstraction));
        assert_eq!(calls, [integer_field(), bad]);
        calls.clear();
        let bindings = [
            (Name::from("y"), Code::unit()),
            (Name::from("x"), integer_field()),
        ];
        let context = PatternContext::from_field_codes(&bindings, |code| {
            calls.push(code.clone());
            decode(code)
        })
        .expect("both codes decode");
        assert_eq!(calls, [Code::unit(), integer_field()]);
        assert_eq!(context.vars.as_ref(), [
            (Name::from("y"), TestType::Unit),
            (Name::from("x"), TestType::Integer)
        ]);
    }

    #[test]
    fn context_lookup_selects_the_first_duplicate()
    {
        let context = PatternContext::new([
            (Name::from("x"), TestType::Integer),
            (Name::from("x"), TestType::Unit),
        ]);
        assert_eq!(
            context.type_of(NameRef::from("x")),
            Maybe::Present(&TestType::Integer)
        );
        assert_eq!(
            context.type_of(NameRef::from("y")),
            Maybe::Absent(pattern_variable::Absent::Unbound)
        );
        assert_eq!(
            PatternContext::<TestType>::new([]).type_of(NameRef::from("x")),
            Maybe::Absent(pattern_variable::Absent::Unbound)
        );
    }

    #[test]
    fn an_empty_face_context_is_total()
    {
        let face = RuleFace::new(
            FreeTerm::var("x"),
            FreeTerm::var("x"),
            [],
            SurfaceSpan::new(0_usize.into(), 0_usize.into()),
        );
        assert!(bool::from(
            TypedRuleFace::new(face, PatternContext::<TestType>::new([])).is_context_total()
        ));
    }

    #[test]
    fn decoder_distinguishes_recursive_and_field_boundaries()
    {
        assert_eq!(decode(&Code::var("Self")), Ok(TestType::Carrier));
        assert_eq!(
            decode(&Code::var("Other")),
            Err(TestDecodeError::Unsupported)
        );
        assert_eq!(
            decode(&Code::field(
                ValueTypeRef::prim(PrimTy::Boolean),
                Grade::One,
                Attrs::empty()
            )),
            Err(TestDecodeError::Unsupported)
        );
    }
}
