//! The four-class failure classifier every refusal carries.
//!
//! # Whose fact a failure is, decided by a type
//!
//! The four classes record whose fact a failure is: an absence the author has
//! not supplied yet, a form the lowering cannot represent, a form the author
//! wrote wrongly, or a fault of the lowering's own. The split is sharper than a
//! three-way one, because an author-written form the lowering declines to
//! represent is a different fact from an author-written form that is simply
//! wrong, and only the first says anything about the fragment's reach.
//!
//! The classes are `gandr-core-term`'s, shared with every other producer of
//! refusals in the core pipeline; the classifier below is this crate's own. It
//! is a `const` function, exhaustive and wildcard-free, and it is blind to its
//! payload: a classification cannot vary with a span or a name, and a refusal
//! added without a class does not compile.
//!
//! # The absence class has no inhabitant here, and that is the point
//!
//! Nothing this crate refuses is an absence. The obligation ledger is fed by
//! declaration *shape* — a signature no definition completes — and never by a
//! classified failure, so a lowering failure cannot be spelled as an
//! obligation. The class exists so the vocabulary is complete and so a later
//! absence has somewhere to land; its emptiness today is the statement itself.
//!
//! # A repaired form is the author's, a foreign tree is the caller's
//!
//! A form the parser had to repair, or one holding two operands where its rule
//! takes one, was written wrongly by the author, so it classifies as malformed
//! source alongside every other author mistake. A tree molded under another
//! grammar, or carrying a mold the grammar does not hold, says nothing about
//! the source: the caller handed the lowering a tree and a grammar that do not
//! belong together, which is a fault of the run, never of the text.

use anodized::spec;
pub use gandr_core_term::FailureClass;

use crate::error::LoweringRefusal;

impl LoweringRefusal<'_>
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the variant alone — two refusals
    ///   of one variant classify alike whatever their spans, names or
    ///   suggestions hold — and every reserved, unadmitted, wrong-sort or
    ///   wrong-arity form, every graded bridge and every unread ascription
    ///   classifies as unrepresentable, the exhausted allowance, the grammar
    ///   mismatch and the unknown mold as engine faults, and every other
    ///   refusal as malformed source.
    /// - provides: the fact a report groups by and a job alarming on the
    ///   fragment's reach counts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned class table, and the payload-blindness
    ///   claim is separated by two inhabitants of one variant differing in
    ///   every payload field, asserted to classify alike.
    /// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
    /// - witness: `classify::tests::the_classification_ignores_the_payload`
    /// - witness: `classify::tests::the_absence_class_has_no_inhabitant`
    #[spec(
        ensures: |ret| match *self {
            | Self::OutOfFragment { .. }
            | Self::GradedBridge { .. }
            | Self::UnreadAscription { .. } => matches!(ret, FailureClass::Unrepresentable),
            | Self::BudgetExceeded { .. }
            | Self::GrammarMismatch { .. }
            | Self::UnknownMold { .. } => matches!(ret, FailureClass::EngineFault),
            | Self::UnresolvedName { .. }
            | Self::UnresolvedTypeHead { .. }
            | Self::DuplicateSignature { .. }
            | Self::DuplicateDefinition { .. }
            | Self::DuplicateImportAlias { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::UnknownMember { .. }
            | Self::LowercaseModuleName { .. } => {
                matches!(ret, FailureClass::MalformedSource)
            },
        },
    )]
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::UnresolvedName { .. }
            | Self::UnresolvedTypeHead { .. }
            | Self::DuplicateSignature { .. }
            | Self::DuplicateDefinition { .. }
            | Self::DuplicateImportAlias { .. }
            | Self::ShadowedBuiltin { .. }
            | Self::MalformedLiteral { .. }
            | Self::MalformedForm { .. }
            | Self::UnknownAttribute { .. }
            | Self::DuplicateAttribute { .. }
            | Self::MissingPayload { .. }
            | Self::NonValuePayload { .. }
            | Self::IllTypedPayload { .. }
            | Self::ForwardMemberReference { .. }
            | Self::UnknownMember { .. }
            | Self::LowercaseModuleName { .. } => FailureClass::MalformedSource,
            | Self::OutOfFragment { .. }
            | Self::GradedBridge { .. }
            | Self::UnreadAscription { .. } => FailureClass::Unrepresentable,
            | Self::BudgetExceeded { .. }
            | Self::GrammarMismatch { .. }
            | Self::UnknownMold { .. } => FailureClass::EngineFault,
        }
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::FailureClass;
    use crate::attribute::AttributeSchema;
    use crate::attribute::PayloadForm;
    use crate::attribute::suggestion;
    use crate::error::AscriptionForm;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::lower::LoweringBudget;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;

    /// The whole refusal vocabulary, one inhabitant each, spans left empty.
    ///
    /// # Specification
    /// - requires: the built-in attribute registry contains `owes`.
    /// - ensures: the 22 current refusal variants have distinct
    ///   representatives; payloads are fixtures rather than evidence of a real
    ///   lowering failure.
    /// - provides: the domain of the finite classification checks.
    /// - fails: never.
    /// - panics: if the named built-in attribute is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pairwise discriminants detect a repeated
    ///   representative that would hide another case behind the same expected
    ///   class. The class table observes every returned row; adding a variant
    ///   requires extending this finite fixture, not merely assuming that its
    ///   current size is exhaustive.
    /// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
    #[spec(
        ensures: |ret| {
            ret.iter().enumerate().all(|(position, refusal)| {
                ret.iter()
                    .skip(position.saturating_add(1_usize))
                    .all(|other| core::mem::discriminant(refusal) != core::mem::discriminant(other))
            })
        },
    )]
    fn vocabulary() -> [LoweringRefusal<'static>; 22_usize]
    {
        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        let owes = registered(SurfaceName::from("owes"));

        [
            LoweringRefusal::UnresolvedName {
                span: empty,
                name: SurfaceName::from("x"),
            },
            LoweringRefusal::UnresolvedTypeHead {
                span: empty,
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span: empty,
                name: SurfaceName::from("x"),
                first: empty,
            },
            LoweringRefusal::DuplicateDefinition {
                span: empty,
                name: SurfaceName::from("x"),
                first: empty,
            },
            LoweringRefusal::OutOfFragment {
                span: empty,
                form: FormName::from(NamedKind("lazy_product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved,
            },
            LoweringRefusal::MalformedLiteral {
                span: empty,
                form: FormName::from(NamedKind("number")),
            },
            LoweringRefusal::MalformedForm {
                span: empty,
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            LoweringRefusal::UnknownAttribute {
                span: empty,
                name: SurfaceName::from("check"),
                suggestion: Maybe::Absent(suggestion::Absent::BeyondBound),
            },
            LoweringRefusal::DuplicateAttribute {
                span: empty,
                name: SurfaceName::from("checks"),
                first: empty,
            },
            LoweringRefusal::MissingPayload {
                span: empty,
                name: owes,
                expected: AttributeSchema::Integer,
            },
            LoweringRefusal::NonValuePayload {
                span: empty,
                name: owes,
                form: FormName::from(NamedKind("ret_expression")),
            },
            LoweringRefusal::IllTypedPayload {
                span: empty,
                name: owes,
                expected: AttributeSchema::Integer,
                written: PayloadForm::Text,
            },
            LoweringRefusal::BudgetExceeded {
                budget: LoweringBudget::from(0_usize),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(0_u64),
                grammar: GrammarFingerprint::from(1_u64),
            },
            LoweringRefusal::UnknownMold {
                span: empty,
                mold: MoldId::from(0_u32),
            },
            LoweringRefusal::DuplicateImportAlias {
                span: empty,
                alias: SurfaceName::from("parse"),
                first: empty,
            },
            LoweringRefusal::ShadowedBuiltin {
                span: empty,
                name: SurfaceName::from("list"),
            },
            LoweringRefusal::GradedBridge {
                span: empty,
                grade: SurfaceName::from("1"),
            },
            LoweringRefusal::ForwardMemberReference {
                span: empty,
                name: SurfaceName::from("second"),
                declared: empty,
            },
            LoweringRefusal::UnknownMember {
                span: empty,
                module: SurfaceName::from("Facts"),
                member: SurfaceName::from("hidden"),
            },
            LoweringRefusal::UnreadAscription {
                span: empty,
                name: SurfaceName::from("T"),
                form: AscriptionForm::Abstract,
            },
            LoweringRefusal::LowercaseModuleName {
                span: empty,
                name: SurfaceName::from("natAdd"),
            },
        ]
    }

    #[test]
    fn every_refusal_carries_its_pinned_class()
    {
        let expected = [
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unrepresentable,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
            FailureClass::EngineFault,
            FailureClass::EngineFault,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unrepresentable,
            FailureClass::MalformedSource,
            FailureClass::MalformedSource,
            FailureClass::Unrepresentable,
            FailureClass::MalformedSource,
        ];

        for (refusal, class) in vocabulary().into_iter().zip(expected) {
            assert_eq!(
                refusal.classify(),
                class,
                "the class table is pinned row by row"
            );
        }
    }

    #[test]
    fn the_classification_ignores_the_payload()
    {
        // One variant, every payload field different: a classifier reading a
        // span, a form or a boundary would separate these two.
        let reserved = LoweringRefusal::OutOfFragment {
            span: span(ByteOffset::from(0_usize), ByteOffset::from(1_usize)),
            form: FormName::from(NamedKind("lazy_product_type")),
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::Reserved,
        };
        let arity = LoweringRefusal::OutOfFragment {
            span: span(ByteOffset::from(40_usize), ByteOffset::from(90_usize)),
            form: FormName::from(NamedKind("lambda_expression")),
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::Arity(OperandCount::from(7_usize)),
        };

        assert_eq!(
            reserved.classify(),
            arity.classify(),
            "classification is a function of the variant alone"
        );
        assert_eq!(
            arity.classify(),
            FailureClass::Unrepresentable,
            "both inhabitants classify as the fragment's own boundary"
        );
    }

    #[test]
    fn the_absence_class_has_no_inhabitant()
    {
        // The ledger is fed by declaration shape, never by a classified
        // failure, so nothing this crate refuses may classify as an absence.
        for refusal in vocabulary() {
            assert_ne!(
                refusal.classify(),
                FailureClass::UserAbsence,
                "no refusal of this crate may be read as an author absence"
            );
        }
    }
}
