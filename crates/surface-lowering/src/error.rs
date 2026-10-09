//! The crate's typed refusal vocabulary, [`LoweringRefusal`], and the payloads
//! that say where a form left the fragment or how it was malformed.
//!
//! Every refusal about the source names the span it rejected, because the
//! diagnostic a driver renders has to point somewhere. Nothing here panics,
//! repairs a malformed form, or admits a node it could not read.
//!
//! # Names and forms are different mistakes
//!
//! An identifier no table answers is an unresolved *name* — the author wrote a
//! spelling nothing binds. A node whose *form* has no reading where it stands
//! is out of fragment — the author wrote something the core has no node for at
//! that position. Keeping them apart is what lets a misspelled type head carry
//! a suggestion-shaped repair while a lambda in value position carries a
//! statement about the polarity discipline instead.
//!
//! # Out of fragment covers four boundaries, and names which
//!
//! A reserved form is parsed so it can be declined by name; an unadmitted form
//! is one the grammar parses and the fragment has no reading for at all; a form
//! of the wrong sort is a well-formed former in the wrong place; a form offered
//! the wrong number of operands is a shape the core cannot build. All four are
//! the lowering declining to represent what was written, so they share a
//! class, and [`FragmentBoundary`] is the discriminating payload that keeps
//! their witnesses apart.
//!
//! # A malformed form is the parser's repair, read back
//!
//! The parser never fails: where the source falls short of the grammar it
//! inserts grout or a closing tile and moves on, and where juxtaposition puts
//! two forms in a hole that takes one it keeps both. The lowering reads every
//! such shape back as [`LoweringRefusal::MalformedForm`], naming the form, the
//! fault and the bytes the fault stands at, so a repaired tree is never
//! lowered as if the source had written it.

use core::error::Error;
use core::fmt;

use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::MoldId;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeSchema;
use crate::attribute::PayloadForm;
use crate::attribute::RegisteredAttribute;
use crate::attribute::suggestion;
use crate::form::FormName;
use crate::form::Repair;
use crate::lower::LoweringBudget;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;
use crate::resolve::SurfaceName;

quenchant_shape::reason_enum! {
    /// Why a refusal names no span of the source.
    pub mod refusal_span {
        /// The refusal is about the run, not about a position in the source.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal concerns the lowering run as a whole.
            Run,
        }
    }
}

/// The sort a node was read at, which its position in its parent fixes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentSort
{
    /// The root of a source: a module's declarations.
    Module,
    /// A module's own child: a declaration.
    Declaration,
    /// A value type, the sort a declaration is declared at.
    ValueType,
    /// A computation type, reached under `U` and `F` and to an arrow's right.
    CompType,
    /// A value, the sort a definition's body is at.
    Value,
    /// A computation, reached under a thunk and to an application's left.
    Computation,
}

impl fmt::Display for FragmentSort
{
    /// Writes the sort's name.
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
            | Self::Module => f.write_str("a module"),
            | Self::Declaration => f.write_str("a declaration"),
            | Self::ValueType => f.write_str("a value type"),
            | Self::CompType => f.write_str("a computation type"),
            | Self::Value => f.write_str("a value"),
            | Self::Computation => f.write_str("a computation"),
        }
    }
}

/// Which way a form left the fragment at the position it was written.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentBoundary
{
    /// The form is reserved: parsed so it can be declined by name.
    Reserved,
    /// The form is parsed by the grammar and has no reading in the fragment.
    Unadmitted,
    /// The form is a former of the fragment, but not of the sort its position
    /// demands.
    WrongSort,
    /// The form is a former of this sort, offered a number of operands it does
    /// not take.
    Arity(OperandCount),
}

impl fmt::Display for FragmentBoundary
{
    /// Writes the way the form left the fragment.
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
            | Self::Reserved => f.write_str("is reserved and declined"),
            | Self::Unadmitted => f.write_str("is not admitted by the fragment"),
            | Self::WrongSort => f.write_str("is not a former of this sort"),
            | Self::Arity(operands) => write!(f, "does not take {operands} operands"),
        }
    }
}

/// How a form's pieces fell short of its rule.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FormFault
{
    /// The parser repaired the form where the source fell short.
    Repaired(Repair),
    /// A hole the form's rule requires holds nothing.
    MissingOperand,
    /// A hole holds more forms than the rule takes, or an operand stands where
    /// the rule has no hole.
    ExtraOperand,
    /// One of the form's own tiles stands where the rule does not place it.
    MisplacedTile,
}

impl fmt::Display for FormFault
{
    /// Writes how the form fell short.
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
            | Self::Repaired(repair) => write!(f, "holds {repair}"),
            | Self::MissingOperand => f.write_str("leaves an operand unwritten"),
            | Self::ExtraOperand => f.write_str("has an operand where it takes none"),
            | Self::MisplacedTile => f.write_str("has a tile out of place"),
        }
    }
}

/// Every way this crate refuses a module.
///
/// The vocabulary is closed and every refusal carries a class, which the
/// classifier reads from the variant alone.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LoweringRefusal<'source>
{
    /// A term name no binder or earlier declaration answers.
    UnresolvedName
    {
        /// The bytes the name covers.
        span: ByteSpan,
        /// The identifier as it was written.
        name: SurfaceName<'source>,
    },

    /// A type head no table entry answers at the arity it was written with.
    UnresolvedTypeHead
    {
        /// The bytes the head covers.
        span: ByteSpan,
        /// The identifier as it was written.
        name: SurfaceName<'source>,
        /// How many arguments the head was written with, which selects the
        /// table that failed to answer it.
        arity: HeadArity,
    },

    /// A second signature for one name.
    DuplicateSignature
    {
        /// The bytes the second signature covers.
        span: ByteSpan,
        /// The name declared twice.
        name: SurfaceName<'source>,
        /// The bytes the first signature covers.
        first: ByteSpan,
    },

    /// A second definition for one name.
    DuplicateDefinition
    {
        /// The bytes the second definition covers.
        span: ByteSpan,
        /// The name defined twice.
        name: SurfaceName<'source>,
        /// The bytes the first definition covers.
        first: ByteSpan,
    },

    /// A form the fragment does not admit where it was written.
    OutOfFragment
    {
        /// The bytes the form covers.
        span: ByteSpan,
        /// The form that was written.
        form: FormName,
        /// The sort the position demanded.
        sort: FragmentSort,
        /// Which way the form left the fragment.
        boundary: FragmentBoundary,
    },

    /// A literal node whose own text is not a lexeme of its kind.
    MalformedLiteral
    {
        /// The bytes the literal covers.
        span: ByteSpan,
        /// The literal form whose lexeme shape was not met.
        form: FormName,
    },

    /// A form whose pieces fall short of its rule, the parser's repairs
    /// included.
    MalformedForm
    {
        /// The bytes the fault stands at: the repair, the empty hole, the
        /// extra operand or the misplaced tile.
        span: ByteSpan,
        /// The form whose rule was not met.
        form: FormName,
        /// How the pieces fell short.
        fault: FormFault,
    },

    /// An attribute name the registry does not hold.
    UnknownAttribute
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
        /// The nearest registered name within the suggestion bound.
        suggestion: Maybe<RegisteredAttribute, suggestion::Absent>,
    },

    /// One attribute written twice for one declared name.
    DuplicateAttribute
    {
        /// The bytes the second attribute covers.
        span: ByteSpan,
        /// The attribute name written twice.
        name: SurfaceName<'source>,
        /// The bytes the first attribute covers.
        first: ByteSpan,
    },

    /// An attribute whose schema takes a payload, written with none.
    MissingPayload
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
        /// The registered name whose schema went unsatisfied.
        name: RegisteredAttribute,
        /// The schema that takes a payload.
        expected: AttributeSchema,
    },

    /// An attribute payload that is not a value of the fragment.
    NonValuePayload
    {
        /// The bytes the payload covers.
        span: ByteSpan,
        /// The registered name whose payload was written.
        name: RegisteredAttribute,
        /// The form the payload was written as.
        form: FormName,
    },

    /// An attribute payload whose form its schema does not admit.
    IllTypedPayload
    {
        /// The bytes the payload covers, or the attribute's own bytes when the
        /// schema takes no payload and one was written.
        span: ByteSpan,
        /// The registered name whose schema was contradicted.
        name: RegisteredAttribute,
        /// The schema the name carries.
        expected: AttributeSchema,
        /// The form the payload was written as.
        written: PayloadForm,
    },

    /// The lowering's work allowance ran out.
    BudgetExceeded
    {
        /// The allowance the caller set.
        budget: LoweringBudget,
    },

    /// The tree was molded under a grammar other than the one it was lowered
    /// with, so its molds would be read against the wrong table.
    GrammarMismatch
    {
        /// The fingerprint the tree carries.
        tree: GrammarFingerprint,
        /// The fingerprint of the grammar the lowering was given.
        grammar: GrammarFingerprint,
    },

    /// A node carries a mold the grammar's table does not hold.
    UnknownMold
    {
        /// The bytes the node covers.
        span: ByteSpan,
        /// The mold the node carries.
        mold: MoldId,
    },
}

impl fmt::Display for LoweringRefusal<'_>
{
    /// Writes the refusal and the position it names.
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
            | Self::UnresolvedName { span, name } => {
                write!(f, "no declaration or binder answers `{name}` at {span}")
            },
            | Self::UnresolvedTypeHead { span, name, arity } => {
                write!(f, "no type head answers `{name}` {arity} at {span}")
            },
            | Self::DuplicateSignature { span, name, first } => {
                write!(
                    f,
                    "`{name}` already has a signature at {first}; a second at {span}"
                )
            },
            | Self::DuplicateDefinition { span, name, first } => {
                write!(
                    f,
                    "`{name}` already has a definition at {first}; a second at {span}"
                )
            },
            | Self::OutOfFragment {
                span,
                form,
                sort,
                boundary,
            } => write!(f, "{form} at {span}, read as {sort}, {boundary}"),
            | Self::MalformedLiteral { span, form } => {
                write!(f, "the text at {span} is not the lexeme of {form}")
            },
            | Self::MalformedForm { span, form, fault } => write!(f, "{form} {fault} at {span}"),
            | Self::UnknownAttribute {
                span,
                name,
                suggestion,
            } => match suggestion {
                | Maybe::Present(nearest) => write!(
                    f,
                    "no attribute is registered as `{name}` at {span}; the nearest is `{nearest}`"
                ),
                | Maybe::Absent(_) => write!(f, "no attribute is registered as `{name}` at {span}"),
            },
            | Self::DuplicateAttribute { span, name, first } => write!(
                f,
                "the attribute `{name}` is already written at {first}; a second at {span}"
            ),
            | Self::MissingPayload {
                span,
                name,
                expected,
            } => write!(f, "`{name}` at {span} takes {expected} and was given none"),
            | Self::NonValuePayload { span, name, form } => {
                write!(
                    f,
                    "the payload of `{name}` at {span} is {form}, not a value"
                )
            },
            | Self::IllTypedPayload {
                span,
                name,
                expected,
                written,
            } => write!(
                f,
                "`{name}` at {span} takes {expected} and was given {written}"
            ),
            | Self::BudgetExceeded { budget } => {
                write!(f, "the lowering outran its allowance of {budget} steps")
            },
            | Self::GrammarMismatch { tree, grammar } => write!(
                f,
                "the tree was molded under grammar {:#018x}, not the grammar {:#018x} it was lowered with",
                u64::from(tree),
                u64::from(grammar)
            ),
            | Self::UnknownMold { span, mold } => write!(
                f,
                "the mold {} at {span} is not in the grammar's table",
                u32::from(mold)
            ),
        }
    }
}

impl Error for LoweringRefusal<'_>
{
}

impl LoweringRefusal<'_>
{
    /// The bytes of the source this refusal is about.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the span the variant rejected, which for a duplicate is the
    ///   second occurrence rather than the first, so the reported position is
    ///   the one an author would delete; the run absence for the allowance
    ///   refusal and the grammar mismatch, which are about the run rather than
    ///   about a position in the source.
    /// - provides: the position a diagnostic renders the refusal at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each variant's exact span asserted, and the two
    ///   spanless variants asserted absent; a variant reporting a sibling
    ///   field's span breaks its own row.
    /// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
    #[inline]
    pub const fn span(&self) -> Maybe<ByteSpan, refusal_span::Absent>
    {
        match *self {
            | Self::UnresolvedName { span, .. }
            | Self::UnresolvedTypeHead { span, .. }
            | Self::DuplicateSignature { span, .. }
            | Self::DuplicateDefinition { span, .. }
            | Self::OutOfFragment { span, .. }
            | Self::MalformedLiteral { span, .. }
            | Self::MalformedForm { span, .. }
            | Self::UnknownAttribute { span, .. }
            | Self::DuplicateAttribute { span, .. }
            | Self::MissingPayload { span, .. }
            | Self::NonValuePayload { span, .. }
            | Self::IllTypedPayload { span, .. }
            | Self::UnknownMold { span, .. } => Maybe::Present(span),
            | Self::BudgetExceeded { .. } | Self::GrammarMismatch { .. } => {
                Maybe::Absent(refusal_span::Absent::Run)
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;

    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::FormFault;
    use super::FragmentBoundary;
    use super::FragmentSort;
    use super::LoweringRefusal;
    use super::refusal_span;
    use crate::attribute::AttributeSchema;
    use crate::attribute::PayloadForm;
    use crate::attribute::suggestion;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Repair;
    use crate::lower::LoweringBudget;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;

    /// One inhabitant of every variant, each with its own rejected span.
    ///
    /// # Specification
    /// trivial.
    fn every_variant() -> [LoweringRefusal<'static>; 15_usize]
    {
        let owes = registered(SurfaceName::from("owes"));
        let s = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        [
            LoweringRefusal::UnresolvedName {
                span: s(1_usize, 2_usize),
                name: SurfaceName::from("x"),
            },
            LoweringRefusal::UnresolvedTypeHead {
                span: s(3_usize, 4_usize),
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span: s(5_usize, 6_usize),
                name: SurfaceName::from("x"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::DuplicateDefinition {
                span: s(7_usize, 8_usize),
                name: SurfaceName::from("x"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::OutOfFragment {
                span: s(9_usize, 10_usize),
                form: FormName::from(NamedKind("product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved,
            },
            LoweringRefusal::MalformedLiteral {
                span: s(11_usize, 12_usize),
                form: FormName::from(NamedKind("number")),
            },
            LoweringRefusal::MalformedForm {
                span: s(23_usize, 23_usize),
                form: FormName::DECLARATION,
                fault: FormFault::MissingOperand,
            },
            LoweringRefusal::UnknownAttribute {
                span: s(13_usize, 14_usize),
                name: SurfaceName::from("check"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            },
            LoweringRefusal::DuplicateAttribute {
                span: s(15_usize, 16_usize),
                name: SurfaceName::from("checks"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::MissingPayload {
                span: s(17_usize, 18_usize),
                name: owes,
                expected: AttributeSchema::Integer,
            },
            LoweringRefusal::NonValuePayload {
                span: s(19_usize, 20_usize),
                name: owes,
                form: FormName::from(NamedKind("ret_expression")),
            },
            LoweringRefusal::IllTypedPayload {
                span: s(21_usize, 22_usize),
                name: owes,
                expected: AttributeSchema::Integer,
                written: PayloadForm::Text,
            },
            LoweringRefusal::BudgetExceeded {
                budget: LoweringBudget::from(4_usize),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(1_u64),
                grammar: GrammarFingerprint::from(2_u64),
            },
            LoweringRefusal::UnknownMold {
                span: s(24_usize, 25_usize),
                mold: MoldId::from(9_u32),
            },
        ]
    }

    #[test]
    fn every_refusal_names_the_span_it_rejected()
    {
        let s = |start: usize, end: usize| {
            Maybe::Present(span(ByteOffset::from(start), ByteOffset::from(end)))
        };
        let run = Maybe::Absent(refusal_span::Absent::Run);
        let expected = [
            s(1_usize, 2_usize),
            s(3_usize, 4_usize),
            s(5_usize, 6_usize),
            s(7_usize, 8_usize),
            s(9_usize, 10_usize),
            s(11_usize, 12_usize),
            s(23_usize, 23_usize),
            s(13_usize, 14_usize),
            s(15_usize, 16_usize),
            s(17_usize, 18_usize),
            s(19_usize, 20_usize),
            s(21_usize, 22_usize),
            run,
            run,
            s(24_usize, 25_usize),
        ];

        for (refusal, position) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                refusal.span(),
                position,
                "each refusal reports its own rejected span"
            );
        }
        assert_eq!(
            expected.len(),
            every_variant().len(),
            "the pinned table covers the whole vocabulary"
        );
    }

    #[test]
    fn every_refusal_renders_its_own_text()
    {
        let expected = [
            "no declaration or binder answers `x` at 1..2",
            "no type head answers `Intgr` bare at 3..4",
            "`x` already has a signature at 0..1; a second at 5..6",
            "`x` already has a definition at 0..1; a second at 7..8",
            "`product_type` at 9..10, read as a value type, is reserved and declined",
            "the text at 11..12 is not the lexeme of `number`",
            "`def_value` leaves an operand unwritten at 23..23",
            "no attribute is registered as `check` at 13..14; the nearest is `checks`",
            "the attribute `checks` is already written at 0..1; a second at 15..16",
            "`owes` at 17..18 takes an integer payload and was given none",
            "the payload of `owes` at 19..20 is `ret_expression`, not a value",
            "`owes` at 21..22 takes an integer payload and was given a text payload",
            "the lowering outran its allowance of 4 steps",
            "the tree was molded under grammar 0x0000000000000001, not the grammar \
             0x0000000000000002 it was lowered with",
            "the mold 9 at 24..25 is not in the grammar's table",
        ];

        for (refusal, rendering) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                format!("{refusal}"),
                String::from(rendering),
                "each refusal renders its own text"
            );
        }
        assert_eq!(
            expected.len(),
            every_variant().len(),
            "the pinned table covers the whole vocabulary"
        );
    }

    #[test]
    fn an_unknown_attribute_with_no_near_name_renders_without_a_suggestion()
    {
        let refusal = LoweringRefusal::UnknownAttribute {
            span: span(ByteOffset::from(0_usize), ByteOffset::from(7_usize)),
            name: SurfaceName::from("expects"),
            suggestion: Maybe::Absent(suggestion::Absent::BeyondBound),
        };

        assert_eq!(
            format!("{refusal}"),
            String::from("no attribute is registered as `expects` at 0..7"),
            "the suggestionless arm names the miss and nothing else"
        );
    }

    #[test]
    fn the_four_fragment_boundaries_render_apart()
    {
        let expected = [
            (FragmentBoundary::Reserved, "is reserved and declined"),
            (
                FragmentBoundary::Unadmitted,
                "is not admitted by the fragment",
            ),
            (FragmentBoundary::WrongSort, "is not a former of this sort"),
            (
                FragmentBoundary::Arity(OperandCount::from(3_usize)),
                "does not take 3 operands",
            ),
        ];

        for (boundary, rendering) in expected {
            assert_eq!(
                format!("{boundary}"),
                String::from(rendering),
                "each boundary names the way the form left the fragment"
            );
        }
    }

    #[test]
    fn every_form_fault_renders_apart()
    {
        let expected = [
            (
                FormFault::Repaired(Repair::Grout(GroutShape::Convex)),
                "holds grout for a missing term",
            ),
            (
                FormFault::Repaired(Repair::Grout(GroutShape::Prefix)),
                "holds grout for a missing operand",
            ),
            (
                FormFault::Repaired(Repair::Grout(GroutShape::Postfix)),
                "holds grout for a missing operand",
            ),
            (
                FormFault::Repaired(Repair::Grout(GroutShape::Infix)),
                "holds grout for a missing operator",
            ),
            (
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)),
                "holds a `)` the source never wrote",
            ),
            (
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Bracket)),
                "holds a `]` the source never wrote",
            ),
            (
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)),
                "holds a `}` the source never wrote",
            ),
            (FormFault::MissingOperand, "leaves an operand unwritten"),
            (
                FormFault::ExtraOperand,
                "has an operand where it takes none",
            ),
            (FormFault::MisplacedTile, "has a tile out of place"),
        ];

        for (fault, rendering) in expected {
            assert_eq!(
                format!("{fault}"),
                String::from(rendering),
                "each fault names how the form fell short"
            );
        }
    }

    #[test]
    fn every_form_name_is_pinned()
    {
        let expected = [
            (FormName::ROOT, "`source_file`"),
            (FormName::UNIT, "`unit`"),
            (FormName::TUPLE, "`tuple_expression`"),
            (FormName::ANNOTATION, "`annotation_expression`"),
            (FormName::SIGNATURE, "`def_signature`"),
            (FormName::FUNCTION, "`def_function`"),
            (FormName::RECURSIVE, "`def_rec`"),
            (FormName::PARAMETERS, "`parameters`"),
            (FormName::PARAMETER, "`parameter`"),
            (FormName::TYPE_ABSTRACTION, "`type_abstraction`"),
            (FormName::GRADE, "`grade`"),
            (FormName::BLOCK, "`block`"),
            (FormName::INTERPOLATION, "`string_interpolation`"),
            (FormName::ATTRIBUTE, "`attribute`"),
            (FormName::DECLARATION, "`def_value`"),
        ];

        for (name, rendering) in expected {
            assert_eq!(
                format!("{name}"),
                String::from(rendering),
                "the form name table is pinned row by row"
            );
        }
        assert_eq!(
            expected.len(),
            FormName::ALL.len(),
            "the pinned table covers every name the lowering spells itself"
        );
    }

    #[test]
    fn the_form_names_are_pairwise_distinct()
    {
        for (first, left) in FormName::ALL.into_iter().enumerate() {
            for (second, right) in FormName::ALL.into_iter().enumerate() {
                if first == second {
                    continue;
                }
                assert_ne!(
                    left, right,
                    "two forms sharing a name would render one diagnostic for two mistakes"
                );
            }
        }
    }

    #[test]
    fn every_fragment_sort_renders_its_own_name()
    {
        let expected = [
            (FragmentSort::Module, "a module"),
            (FragmentSort::Declaration, "a declaration"),
            (FragmentSort::ValueType, "a value type"),
            (FragmentSort::CompType, "a computation type"),
            (FragmentSort::Value, "a value"),
            (FragmentSort::Computation, "a computation"),
        ];

        for (sort, rendering) in expected {
            assert_eq!(
                format!("{sort}"),
                String::from(rendering),
                "each sort names itself"
            );
        }
        assert_eq!(
            expected.len(),
            6_usize,
            "the pinned table covers every sort a node is read at"
        );
    }
}
