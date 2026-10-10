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
//! When recovering from malformed source, the parser inserts grout or a
//! closing tile, and where juxtaposition puts two forms in a hole that takes
//! one it keeps both. The lowering reads every
//! such shape back as [`LoweringRefusal::MalformedForm`], naming the form, the
//! fault and the bytes the fault stands at, so a repaired tree is never
//! lowered as if the source had written it.

use core::error::Error;
use core::fmt;

use anodized::spec;
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
use crate::import::ONE_SOURCE;
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
///
/// # Specification
/// - requires: a producer selects the sort demanded by the rejected position.
/// - ensures: the tag reports the expected sort, not the rejected form's sort.
/// - provides: the polarity and position at which representation was requested.
/// - fails: not applicable to the tag itself.
/// - panics: none.
/// - executable: none — the tag holds no parent, grammar or position from which
///   the required sort could be derived.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration at the root and a lambda in value position
///   report module and value respectively, separating expected sort from the
///   form's own sort. These witnesses bound the claim to those positions.
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentSort
{
    /// The root of a source: a module's declarations.
    Module,
    /// A module's own child: a declaration.
    Declaration,
    /// A value type, the sort a declaration is declared at.
    ValueType,
    /// A computation type, reached under `+U` and `-F` and to an arrow's right.
    CompType,
    /// A value, the sort a definition's body is at.
    Value,
    /// A computation, reached under a thunk and to an application's left.
    Computation,
    /// A pattern, the binder of a `run` statement.
    Pattern,
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
            | Self::Pattern => f.write_str("a pattern"),
        }
    }
}

/// Which way a form left the fragment at the position it was written.
///
/// # Specification
/// - requires: the producer identifies the boundary crossed by the source form.
/// - ensures: reserved, unadmitted, wrong-sort and wrong-arity reports remain
///   distinct; an arity report carries the number of operands offered.
/// - provides: why a parsed form has no representation at this position.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — the tag and offered count do not hold the grammar,
///   admission policy or actual operands needed to verify the report.
///
/// # Adequacy
/// - hypothesis: L3 — one reserved former, unadmitted forms, a wrong-sort
///   lambda and zero/two-operand refusals distinguish the four boundaries by
///   exact typed payloads. The fixtures do not enumerate every grammar form.
/// - witness: `lower::tests::the_reserved_lazy_product_is_declined`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
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
///
/// # Specification
/// - requires: a producer reports the fault observed in the form's children.
/// - ensures: parser repair, missing operand, extra operand and misplaced tile
///   reports retain distinct meanings; a repair retains its shape.
/// - provides: the structural reason a form could not be read.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — a fault holds neither the syntax node nor the rule and
///   children needed to establish that the reported fault occurred.
///
/// # Adequacy
/// - hypothesis: L3 — repaired, juxtaposed and misplaced-tile fixtures carry
///   different exact faults and spans. The raw missing-operand variant is
///   included in the span projection fixture; the source examples are not a
///   complete enumeration of malformed child sequences.
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
/// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
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

/// A module ascription form the fragment does not read yet.
///
/// # Specification
/// - requires: a producer selects the ascription form actually written.
/// - ensures: opaque ascription, abstract type, kinded type and parameterized
///   type reports do not become a transparent manifest-type interpretation.
/// - provides: which unread ascription obligation prevented admission.
/// - fails: not applicable to the report itself.
/// - panics: none.
/// - executable: none — the tag does not hold an ascription tree or its
///   components, so it cannot validate the producer's classification.
///
/// # Adequacy
/// - hypothesis: L3 — opaque, abstract and kinded components are asserted as
///   typed refusals; a manifest component is admitted instead of conflated with
///   a kinded one. These fixtures do not establish every parameterized form.
/// - witness: `modules::modules::opaque_module_ascription_is_declined_not_read_as_transparent`
/// - witness: `modules::modules::a_bare_type_component_declines_and_keeps_its_siblings`
/// - witness: `modules::modules::a_kinded_type_component_is_declined_by_name_and_a_manifest_one_is_not`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AscriptionForm
{
    /// Opaque ascription `:>`, which seals what it hides.
    Opaque,
    /// A bare type component `type T` under transparent ascription: an
    /// abstract type, whose meaning is sealing's.
    Abstract,
    /// A kinded type component `type T : κ`, declaring a type family.
    Kinded,
    /// A type component binding parameters, `type T(a : A) …`.
    Parameterized,
}

impl fmt::Display for AscriptionForm
{
    /// Writes the form and what it waits on.
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
            | Self::Opaque => f.write_str("is ascribed opaquely with `:>`"),
            | Self::Abstract => f.write_str(
                "is an abstract type component, given its meaning only by opaque ascription `:>`",
            ),
            | Self::Kinded => f.write_str("is a kinded type component, a type family"),
            | Self::Parameterized => f.write_str("is a type component that binds parameters"),
        }
    }
}

/// The crate's global and declaration-local refusals.
///
/// The vocabulary is closed and every refusal carries a class, which the
/// classifier reads from the variant alone.
///
/// # Specification
/// - requires: producers supply the identities and positions of the reported
///   failure; callers may also construct unvalidated diagnostic records.
/// - ensures: the variant identifies the failure kind and retains its payload;
///   span projection selects the rejected occurrence, not an earlier duplicate.
/// - provides: structured diagnostic data, not a certificate that the failure
///   occurred or that the payload belongs to a particular syntax tree.
/// - fails: not applicable to the stored report itself.
/// - panics: none.
/// - executable: none — the report does not own the syntax tree, lexical scope,
///   grammar or budget execution needed to authenticate its payload. Projection
///   and classification have their own executable predicates.
///
/// # Adequacy
/// - hypothesis: L3 — all current variants have exact span observations,
///   including earlier-versus-rejected duplicates and the two run absences.
///   Classification is observed independently of payload; this does not prove
///   that an arbitrary constructed report describes a real lowering failure.
/// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
/// - witness: `classify::tests::every_refusal_carries_its_pinned_class`
/// - witness: `classify::tests::the_classification_ignores_the_payload`
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

    /// A second import binding an alias an earlier import already binds.
    DuplicateImportAlias
    {
        /// The bytes the second import covers.
        span: ByteSpan,
        /// The alias imported twice.
        alias: SurfaceName<'source>,
        /// The bytes the first import covers.
        first: ByteSpan,
    },

    /// A declared name or a binder over a builtin, under the policy that
    /// forbids shadowing one.
    ShadowedBuiltin
    {
        /// The bytes of the name that shadows.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
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

    /// A thunk type written with a grade other than the default `ω`, which
    /// the core has no bridge for.
    GradedBridge
    {
        /// The bytes the grade covers.
        span: ByteSpan,
        /// The grade as it was written.
        grade: SurfaceName<'source>,
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

    /// A module member named at or after the position of the member that
    /// names it.
    ForwardMemberReference
    {
        /// The bytes the reference covers.
        span: ByteSpan,
        /// The member's name as the reference wrote it.
        name: SurfaceName<'source>,
        /// The bytes of the member's own name, where it is declared.
        declared: ByteSpan,
    },

    /// A module that exports no member of this name: a path selecting a
    /// member the module hid or never declared, or a signature component no
    /// member supplies.
    UnknownMember
    {
        /// The bytes the selection or the component covers.
        span: ByteSpan,
        /// The module, as the path or the declaration spelled it.
        module: SurfaceName<'source>,
        /// The member's name.
        member: SurfaceName<'source>,
    },

    /// A module ascription form the fragment does not read yet.
    UnreadAscription
    {
        /// The bytes of the ascription's tile or the component's name.
        span: ByteSpan,
        /// The module or the type component the form ascribes.
        name: SurfaceName<'source>,
        /// The form.
        form: AscriptionForm,
    },

    /// A top-level module named with a lowercase initial, a spelling the
    /// grammar reserves for nested modules.
    LowercaseModuleName
    {
        /// The bytes the declaration covers.
        span: ByteSpan,
        /// The name as it was written.
        name: SurfaceName<'source>,
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
            | Self::DuplicateImportAlias { span, alias, first } => write!(
                f,
                "the import alias `{alias}` at {span} is already bound by the import at {first}: \
                 {ONE_SOURCE}"
            ),
            | Self::ShadowedBuiltin { span, name } => write!(
                f,
                "`{name}` at {span} shadows a builtin name, which the active policy forbids"
            ),
            | Self::OutOfFragment {
                span,
                form,
                sort,
                boundary,
            } => write!(f, "{form} at {span}, read as {sort}, {boundary}"),
            | Self::GradedBridge { span, grade } => write!(
                f,
                "the bridge's grade `{grade}` at {span} is not the default `ω`, the only grade \
                 the fragment admits"
            ),
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
            | Self::ForwardMemberReference {
                span,
                name,
                declared,
            } => write!(
                f,
                "the member `{name}` at {span} is declared at {declared}, at or after the member \
                 naming it; a member names only the members before it"
            ),
            | Self::UnknownMember {
                span,
                module,
                member,
            } => write!(
                f,
                "the module `{module}` exports no member `{member}` at {span}"
            ),
            | Self::UnreadAscription { span, name, form } => {
                write!(
                    f,
                    "`{name}` at {span} {form}; the fragment does not read it yet"
                )
            },
            | Self::LowercaseModuleName { span, name } => write!(
                f,
                "the module `{name}` at {span} is named with a lowercase initial; a top-level \
                 module's name starts with an uppercase letter"
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
    /// - hypothesis: L3 — the const predicate separates source spans from the
    ///   two run absences. The current finite vocabulary is enumerated with
    ///   exact spans, including distinct earlier and rejected occurrences; this
    ///   witness catches returning the wrong span within a variant.
    /// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
    #[spec(
        ensures: |ret| {
            matches!(ret, Maybe::Absent(refusal_span::Absent::Run))
                == matches!(
                    *self,
                    Self::BudgetExceeded { .. } | Self::GrammarMismatch { .. }
                )
        },
    )]
    #[inline]
    pub const fn span(&self) -> Maybe<ByteSpan, refusal_span::Absent>
    {
        match *self {
            | Self::UnresolvedName { span, .. }
            | Self::UnresolvedTypeHead { span, .. }
            | Self::DuplicateSignature { span, .. }
            | Self::DuplicateDefinition { span, .. }
            | Self::DuplicateImportAlias { span, .. }
            | Self::ShadowedBuiltin { span, .. }
            | Self::OutOfFragment { span, .. }
            | Self::GradedBridge { span, .. }
            | Self::MalformedLiteral { span, .. }
            | Self::MalformedForm { span, .. }
            | Self::UnknownAttribute { span, .. }
            | Self::DuplicateAttribute { span, .. }
            | Self::MissingPayload { span, .. }
            | Self::NonValuePayload { span, .. }
            | Self::IllTypedPayload { span, .. }
            | Self::ForwardMemberReference { span, .. }
            | Self::UnknownMember { span, .. }
            | Self::UnreadAscription { span, .. }
            | Self::LowercaseModuleName { span, .. }
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
    use anodized::spec;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::AscriptionForm;
    use super::FormFault;
    use super::FragmentBoundary;
    use super::FragmentSort;
    use super::LoweringRefusal;
    use super::refusal_span;
    use crate::attribute::AttributeSchema;
    use crate::attribute::PayloadForm;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::lower::LoweringBudget;
    use crate::resolve::HeadArity;
    use crate::resolve::SurfaceName;

    /// One inhabitant of every variant, each with its own rejected span.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the current 22-variant fixture has no repeated variant tag;
    ///   source-bearing variants carry separately observable rejected spans.
    /// - provides: a finite domain for the exact span projection witness.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the predicate checks pairwise tag distinctness, while
    ///   the span witness separates payload selection and run absence. Coverage
    ///   is for the current vocabulary; a new variant requires extending this
    ///   fixture.
    /// - witness: `error::tests::every_refusal_names_the_span_it_rejected`
    #[spec(
        ensures: |ret| {
            ret.iter().enumerate().all(|(index, left)| {
                ret.iter()
                    .skip(index.saturating_add(1_usize))
                    .all(|right| core::mem::discriminant(left) != core::mem::discriminant(right))
            })
        },
    )]
    fn every_variant() -> [LoweringRefusal<'static>; 22_usize]
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
                form: FormName::from(NamedKind("lazy_product_type")),
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
            LoweringRefusal::DuplicateImportAlias {
                span: s(26_usize, 27_usize),
                alias: SurfaceName::from("parse"),
                first: s(0_usize, 1_usize),
            },
            LoweringRefusal::ShadowedBuiltin {
                span: s(28_usize, 29_usize),
                name: SurfaceName::from("list"),
            },
            LoweringRefusal::GradedBridge {
                span: s(30_usize, 31_usize),
                grade: SurfaceName::from("1"),
            },
            LoweringRefusal::ForwardMemberReference {
                span: s(32_usize, 33_usize),
                name: SurfaceName::from("second"),
                declared: s(40_usize, 46_usize),
            },
            LoweringRefusal::UnknownMember {
                span: s(34_usize, 35_usize),
                module: SurfaceName::from("Facts"),
                member: SurfaceName::from("hidden"),
            },
            LoweringRefusal::UnreadAscription {
                span: s(36_usize, 37_usize),
                name: SurfaceName::from("T"),
                form: AscriptionForm::Abstract,
            },
            LoweringRefusal::LowercaseModuleName {
                span: s(38_usize, 39_usize),
                name: SurfaceName::from("natAdd"),
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
            s(26_usize, 27_usize),
            s(28_usize, 29_usize),
            s(30_usize, 31_usize),
            s(32_usize, 33_usize),
            s(34_usize, 35_usize),
            s(36_usize, 37_usize),
            s(38_usize, 39_usize),
        ];

        for (refusal, position) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                refusal.span(),
                position,
                "each refusal reports its own rejected span"
            );
        }
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
}
