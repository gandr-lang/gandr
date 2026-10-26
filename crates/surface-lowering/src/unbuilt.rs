//! The features the lowering has not built, each named where a refusal
//! declines it.
//!
//! # A refusal names its feature where it is raised
//!
//! A form the fragment reserves or does not admit carries the [`Unbuilt`]
//! feature it stops at, written by the site that refuses it:
//! [`FragmentBoundary::Reserved`](crate::FragmentBoundary::Reserved) and
//! [`FragmentBoundary::Unadmitted`](crate::FragmentBoundary::Unadmitted) take
//! the feature as their payload, and the dispatch table's declined kinds,
//! [`Former::Reserved`](crate::Former::Reserved) and
//! [`Former::Unadmitted`](crate::Former::Unadmitted), carry theirs. A site
//! that names no feature does not compile. Each feature answers its spelling,
//! the qualifier a fixture's `refuses("OutOfFragment.<spelling>")` names it
//! by, and the issue tracking it: an open issue of its own, or one a shared
//! cause shares (#2529). `check:tracking` holds every issue open, or closed as
//! not planned.
//!
//! **Choice.** The feature is chosen at the site; the alternative, a table
//! from a refused form and the sort its position demands to an issue, named
//! one feature for every reason a form is refused, and fell back to the epic
//! for every form the table missed. A form refused for several reasons names
//! several features: an instantiation is a recursive call's claim, a partial
//! supply, a combined supply or a stage resident, each by its site.
//! **Reversal.** A feature whose sites disagree on its issue is split.

use core::fmt;

use crate::classify::TrackingIssue;

/// The qualifier a fixture's `refuses` expectation names an unbuilt feature
/// by, after `OutOfFragment.`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Spelling(&'static str);

impl AsRef<str> for Spelling
{
    /// The spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for Spelling
{
    /// Writes the spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// A feature the lowering has not built, named by the site that refuses it.
///
/// # Specification
/// - requires: built at a refusing site.
/// - ensures: one spelling and one tracking issue per feature, distinct
///   spellings across features.
/// - panics: none.
/// - executable: none — this data type has no call boundary;
///   [`Unbuilt::spelling`] and [`Unbuilt::tracking`] carry its readings, and
///   the witness checks the spellings apart.
///
/// # Adequacy
/// - hypothesis: L3 — every feature's spelling is read back to that feature
///   alone.
/// - witness: `unbuilt::tests::every_feature_is_spelled_apart`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unbuilt
{
    /// A projection, `e.1` or `e.field`, where the fragment reads none, or a
    /// path the projection does not resolve.
    Projection,
    /// An index `xs[i]` outside a view-answering method's body.
    Index,
    /// A module packed into a value, `pack [T, …] e`.
    Pack,
    /// A module packed at its model type, `pack M at Model(T)`, of a shape the
    /// lowering does not read.
    PackModel,
    /// A model's manifest sorts forgotten, `forget[sort C = A, …](m) at
    /// Model(T)`, of a shape the lowering does not read.
    ForgetModel,
    /// The type of a packed module, `package [T, …] P`.
    PackageType,
    /// The statement `unpack … = e ;`.
    Unpack,
    /// An annotation `(e : T)` read where a type, or nothing, is read.
    Annotation,
    /// A number literal written with the `f32` suffix, which has no atom yet:
    /// the integer widths and `f64` are built.
    TypedNumber,
    /// The shell block, `#!{ … }`.
    ShellBlock,
    /// A constructor field at a finite grade other than `1`.
    FieldGrade,
    /// The as-pattern `p as x`.
    AsPattern,
    /// The list pattern `[p, …]`.
    ListPattern,
    /// The rest pattern `..p`.
    RestPattern,
    /// The union type `A | B`.
    Union,
    /// The operator declaration `op infixl 6 "spelling" ;`.
    OperatorDeclaration,
    /// A recursive call's claim the lowering does not read: two claims at once,
    /// a resident that is no claim, a measure, a stage or a cost.
    RecursiveClaim,
    /// The shared fork `fork !(…) { … } ;`.
    SharedFork,
    /// The endpoint copy `dup(e)`.
    Dup,
    /// The statement `acquire …;`.
    Acquire,
    /// The statement `release …;`.
    Release,
    /// A type at a stage, `T[i]`, written under a form that places none.
    StagedType,
    /// The unknown type `?`.
    UnknownType,
    /// String interpolation where the prelude holds no `string.append` to
    /// fold it with.
    Interpolation,
    /// A match on a view, `case e with v { … }`.
    CaseView,
    /// A bind expression standing where a term is read.
    Bind,
    /// A circuit declaration where a term is read.
    Circuit,
    /// A codata declaration where a term is read.
    Codata,
    /// A word pattern `g ∷ p` where a term is read, or one whose head is no
    /// letter.
    ConsPattern,
    /// A constructor pattern where a term is read.
    ConstructorPattern,
    /// A derived rule where a term is read.
    Derive,
    /// An extern block.
    ExternBlock,
    /// A host escape.
    HostEscape,
    /// An injection pattern where a term is read.
    LabelledSumPattern,
    /// A literal pattern other than a number or a boolean, or one where a term
    /// is read.
    LiteralPattern,
    /// A manifest sort where a term is read.
    ManifestSort,
    /// An or-pattern whose alternatives bind names, or one where a term is
    /// read.
    OrPattern,
    /// A telescope pattern where a term is read.
    TelescopePattern,
    /// A theory declaration where a term is read.
    Theory,
    /// A tuple pattern where a term is read.
    TuplePattern,
    /// A shell block's command substitution.
    CommandSubstitution,
    /// A shell block's double-quoted string.
    DoubleQuotedString,
    /// A shell block's environment assignment.
    EnvironmentAssignment,
    /// A shell block's file descriptor.
    FileDescriptor,
    /// A shell block's glob.
    Glob,
    /// A shell block's list operator.
    ListOperator,
    /// A shell block's pipeline.
    Pipeline,
    /// A shell block's redirection operator.
    RedirectionOperator,
    /// A shell block's word.
    ShellWord,
    /// A shell block's single-quoted string.
    SingleQuotedString,
    /// A shell block's subshell.
    Subshell,
    /// A shell block's variable expansion.
    VariableExpansion,
    /// A shell block's variable name.
    VariableName,
    /// A thunk's grade, `thunk[r] { … }`.
    ThunkGrade,
    /// A grade on a list, run or prefix type.
    TypeGrade,
    /// The type abstraction `fn [T] { … }`.
    TypeAbstraction,
    /// The statement `val p = e ;`.
    Val,
    /// A capitalised name where a value is read that names no constructor,
    /// declaration or type.
    UnknownConstructor,
    /// An infix form the lowering does not read: an operator outside the
    /// prelude's vocabulary, or a word `g ∷ w` whose `g` is neither a loop
    /// nor `back` of one; a `g` that names nothing is unresolved.
    InfixForm,
    /// A prefix operator outside the prelude's vocabulary.
    PrefixOperator,
    /// A match of no arms over a type no data switch reads, such as the
    /// empty sum, written with its answer type.
    EmptyCase,
    /// A form where a pattern is read that no pattern reading takes and the
    /// table declines by no feature of its own.
    UnreadPattern,
    /// A stated type component whose held declaration the collection does not
    /// carry.
    StatedType,
    /// A universe level at or past the largest the lowering counts: the
    /// largest has no universe above it.
    UniverseLevel,
    /// A capability form over a host table in conflict.
    CapabilityHost,
    /// A presentation block whose body the description does not read.
    Presentation,
    /// A recorded move that is no call and no closing name.
    RecordedMove,
    /// A dialogue move that is no endpoint's call of one move.
    DialogueMove,
    /// A supply whose residents mix a named supply with what is no supply.
    CombinedSupply,
    /// A staged supply no declaration owns.
    UnownedSupply,
    /// A capability scope over a theory no declaration owns, so no
    /// declaration owes its laws.
    UnownedScope,
    /// A method call whose declaration the collection does not carry.
    MethodCall,
    /// A manifest model type of a shape the lowering does not read.
    ManifestModel,
    /// A model type over a theory the lowering does not present.
    ModelType,
    /// A loop's name inside a pattern rather than as an arm's whole pattern.
    LoopPattern,
    /// A session type the protocol builder does not read.
    SessionProtocol,
    /// A stage supply whose resident is no single tile.
    StageResident,
    /// A univalence resident not written in digits alone.
    UaCount,
    /// A univalence description the lowering does not read.
    UaDescription,
    /// A cell member with parameters, a side that is no closed term, or a rule
    /// arrow.
    CellMember,
    /// The constructor member `C(fields) : T` of a data block.
    ConstructorBlockMember,
    /// An attribute block on a data block's generator.
    GeneratorAttribute,
    /// A model signature the derivation cannot state.
    ModelSignature,
}

impl Unbuilt
{
    /// Every feature, in declaration order.
    pub const ALL: [Self; 82_usize] = [
        Self::Projection,
        Self::Index,
        Self::Pack,
        Self::PackModel,
        Self::ForgetModel,
        Self::PackageType,
        Self::Unpack,
        Self::Annotation,
        Self::TypedNumber,
        Self::ShellBlock,
        Self::FieldGrade,
        Self::AsPattern,
        Self::ListPattern,
        Self::RestPattern,
        Self::Union,
        Self::OperatorDeclaration,
        Self::RecursiveClaim,
        Self::SharedFork,
        Self::Dup,
        Self::Acquire,
        Self::Release,
        Self::StagedType,
        Self::UnknownType,
        Self::Interpolation,
        Self::CaseView,
        Self::Bind,
        Self::Circuit,
        Self::Codata,
        Self::ConsPattern,
        Self::ConstructorPattern,
        Self::Derive,
        Self::ExternBlock,
        Self::HostEscape,
        Self::LabelledSumPattern,
        Self::LiteralPattern,
        Self::ManifestSort,
        Self::OrPattern,
        Self::TelescopePattern,
        Self::Theory,
        Self::TuplePattern,
        Self::CommandSubstitution,
        Self::DoubleQuotedString,
        Self::EnvironmentAssignment,
        Self::FileDescriptor,
        Self::Glob,
        Self::ListOperator,
        Self::Pipeline,
        Self::RedirectionOperator,
        Self::ShellWord,
        Self::SingleQuotedString,
        Self::Subshell,
        Self::VariableExpansion,
        Self::VariableName,
        Self::ThunkGrade,
        Self::TypeGrade,
        Self::TypeAbstraction,
        Self::Val,
        Self::UnknownConstructor,
        Self::InfixForm,
        Self::PrefixOperator,
        Self::EmptyCase,
        Self::UnreadPattern,
        Self::StatedType,
        Self::UniverseLevel,
        Self::CapabilityHost,
        Self::Presentation,
        Self::RecordedMove,
        Self::CombinedSupply,
        Self::UnownedSupply,
        Self::UnownedScope,
        Self::MethodCall,
        Self::ManifestModel,
        Self::ModelType,
        Self::LoopPattern,
        Self::SessionProtocol,
        Self::StageResident,
        Self::UaCount,
        Self::UaDescription,
        Self::CellMember,
        Self::ConstructorBlockMember,
        Self::GeneratorAttribute,
        Self::ModelSignature,
    ];

    /// The qualifier a fixture's `refuses` expectation names the feature by:
    /// the refused form's kind, with a reading where the form stands for
    /// several features.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the feature's spelling, distinct from every other feature's.
    /// - provides: the payload of `OutOfFragment.<spelling>`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table is the specification; a predicate would
    ///   restate it row by row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every feature's spelling is asserted apart from every
    ///   other's.
    /// - witness: `unbuilt::tests::every_feature_is_spelled_apart`
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> Spelling
    {
        Spelling(match self {
            Self::Projection => "projection_expression",
            Self::Index => "index_expression",
            Self::Pack => "pack_expression",
            Self::PackModel => "pack_model_expression",
            Self::ForgetModel => "forget_model_expression",
            Self::PackageType => "package_type",
            Self::Unpack => "unpack_statement",
            Self::Annotation => "annotation_expression",
            Self::TypedNumber => "typed_number",
            Self::ShellBlock => "shell_block",
            Self::FieldGrade => "grade.declaration",
            Self::AsPattern => "as_pattern",
            Self::ListPattern => "list_pattern",
            Self::RestPattern => "rest_pattern",
            Self::Union => "union_type",
            Self::OperatorDeclaration => "operator_declaration",
            Self::RecursiveClaim => "instantiation_expression.computation",
            Self::SharedFork => "fork_shared_statement",
            Self::Dup => "dup_expression",
            Self::Acquire => "acquire_statement",
            Self::Release => "release_statement",
            Self::StagedType => "staged_type",
            Self::UnknownType => "unknown_type",
            Self::Interpolation => "string_interpolation",
            Self::CaseView => "case_with_view",
            Self::Bind => "bind_expression",
            Self::Circuit => "circuit_declaration",
            Self::Codata => "codata_declaration",
            Self::ConsPattern => "cons_pattern",
            Self::ConstructorPattern => "constructor_pattern",
            Self::Derive => "derive_declaration",
            Self::ExternBlock => "extern_block",
            Self::HostEscape => "host_escape",
            Self::LabelledSumPattern => "labelled_sum_pattern",
            Self::LiteralPattern => "literal_pattern",
            Self::ManifestSort => "manifest_sort",
            Self::OrPattern => "or_pattern",
            Self::TelescopePattern => "telescope_pattern",
            Self::Theory => "theory_declaration",
            Self::TuplePattern => "tuple_pattern",
            Self::CommandSubstitution => "command_substitution",
            Self::DoubleQuotedString => "double_quoted_string",
            Self::EnvironmentAssignment => "environment_assignment",
            Self::FileDescriptor => "file_descriptor",
            Self::Glob => "glob_expression",
            Self::ListOperator => "list_operator",
            Self::Pipeline => "pipeline",
            Self::RedirectionOperator => "redirection_operator",
            Self::ShellWord => "shell_word",
            Self::SingleQuotedString => "single_quoted_string",
            Self::Subshell => "subshell",
            Self::VariableExpansion => "variable_expansion",
            Self::VariableName => "variable_name",
            Self::ThunkGrade => "grade.value",
            Self::TypeGrade => "grade.value_type",
            Self::TypeAbstraction => "type_abstraction",
            Self::Val => "val_statement",
            Self::UnknownConstructor => "constructor",
            Self::InfixForm => "binary_expression",
            Self::PrefixOperator => "unary_expression",
            Self::EmptyCase => "case_expression",
            Self::UnreadPattern => "pattern",
            Self::StatedType => "stated_type",
            Self::UniverseLevel => "universe_type",
            Self::CapabilityHost => "capability_type",
            Self::Presentation => "presentation",
            Self::RecordedMove => "recorded_move",
            Self::DialogueMove => "dialogue_move",
            Self::CombinedSupply => "instantiation_expression.combined",
            Self::UnownedSupply => "instantiation_expression.unowned",
            Self::UnownedScope => "handle_expression.unowned",
            Self::MethodCall => "method_call",
            Self::ManifestModel => "manifest_type",
            Self::ModelType => "model_type",
            Self::LoopPattern => "loop_pattern",
            Self::SessionProtocol => "session_protocol",
            Self::StageResident => "instantiation_expression.stage",
            Self::UaCount => "ua_count",
            Self::UaDescription => "ua_description",
            Self::CellMember => "cell_member",
            Self::ConstructorBlockMember => "constructor_block_member",
            Self::GeneratorAttribute => "attribute",
            Self::ModelSignature => "model_signature",
        })
    }

    /// The issue tracking the feature.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the open issue whose landing builds the feature, shared by
    ///   the features one cause holds back.
    /// - provides: the issue every face of the refusal names.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table is the specification; a predicate would
    ///   restate it row by row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the census's features are pinned to their issues.
    /// - witness: `classify::tests::a_form_out_of_the_fragment_names_the_issue_tracking_it`
    #[inline]
    #[must_use]
    pub const fn tracking(self) -> TrackingIssue
    {
        match self {
            Self::Projection => TrackingIssue::PROJECTION,
            Self::Index => TrackingIssue::UNHELD_INDEX,
            Self::Pack | Self::PackModel | Self::PackageType | Self::Unpack | Self::ForgetModel => {
                TrackingIssue::PACKAGES
            },
            Self::TypedNumber => TrackingIssue::TYPED_NUMBER,
            Self::FieldGrade => TrackingIssue::FIELD_GRADE,
            Self::Union => TrackingIssue::UNION,
            Self::OperatorDeclaration | Self::PrefixOperator => TrackingIssue::OPERATOR_DECLARATION,
            Self::RecursiveClaim => TrackingIssue::RECURSIVE_CLAIM,
            Self::SharedFork | Self::Dup | Self::Acquire | Self::Release => {
                TrackingIssue::SHARED_SESSIONS
            },
            Self::StagedType => TrackingIssue::PLACED_STAGE,
            Self::UnknownType => TrackingIssue::UNKNOWN_TYPE,
            Self::CaseView => TrackingIssue::CASE_VIEW,
            Self::ThunkGrade => TrackingIssue::THUNK_GRADE,
            Self::InfixForm => TrackingIssue::INFIX_FORM,
            Self::EmptyCase => TrackingIssue::EMPTY_CASE_ANSWER,
            Self::ExternBlock | Self::HostEscape => TrackingIssue::EXTERN_BLOCK,
            Self::ShellBlock
            | Self::CommandSubstitution
            | Self::DoubleQuotedString
            | Self::EnvironmentAssignment
            | Self::FileDescriptor
            | Self::Glob
            | Self::ListOperator
            | Self::Pipeline
            | Self::RedirectionOperator
            | Self::ShellWord
            | Self::SingleQuotedString
            | Self::Subshell
            | Self::VariableExpansion
            | Self::VariableName => TrackingIssue::SHELL_BLOCK,
            Self::Bind
            | Self::Circuit
            | Self::Codata
            | Self::Derive
            | Self::ManifestSort
            | Self::Theory => TrackingIssue::DECLARATION_AS_TERM,
            Self::AsPattern
            | Self::ListPattern
            | Self::RestPattern
            | Self::ConsPattern
            | Self::ConstructorPattern
            | Self::LabelledSumPattern
            | Self::LiteralPattern
            | Self::OrPattern
            | Self::TelescopePattern
            | Self::TuplePattern
            | Self::LoopPattern
            | Self::UnreadPattern => TrackingIssue::PATTERN_FORM,
            Self::Annotation => TrackingIssue::ANNOTATION,
            Self::Interpolation => TrackingIssue::INTERPOLATION,
            Self::TypeGrade => TrackingIssue::TYPE_GRADE,
            Self::TypeAbstraction => TrackingIssue::TYPE_ABSTRACTION,
            Self::Val => TrackingIssue::VAL,
            Self::UnknownConstructor | Self::UniverseLevel | Self::CapabilityHost => {
                TrackingIssue::AUTHOR_ERROR_AS_UNBUILT
            },
            Self::StatedType | Self::MethodCall => TrackingIssue::UNCARRIED_DECLARATION,
            Self::Presentation => TrackingIssue::PRESENTATION,
            Self::RecordedMove | Self::DialogueMove => TrackingIssue::MOVES,
            Self::CombinedSupply | Self::UnownedSupply | Self::StageResident => {
                TrackingIssue::SUPPLIES
            },
            Self::UnownedScope => TrackingIssue::UNOWNED_SCOPE,
            Self::ManifestModel | Self::ModelType | Self::ModelSignature => {
                TrackingIssue::MODEL_TYPE
            },
            Self::SessionProtocol => TrackingIssue::SESSION_PROTOCOL,
            Self::UaCount | Self::UaDescription => TrackingIssue::UA_RESIDENT,
            Self::CellMember | Self::ConstructorBlockMember | Self::GeneratorAttribute => {
                TrackingIssue::DATA_MEMBER
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;

    use super::Spelling;
    use super::Unbuilt;

    #[test]
    fn every_feature_is_spelled_apart()
    {
        let mut spelled: BTreeMap<Spelling, Unbuilt> = BTreeMap::new();
        for feature in Unbuilt::ALL {
            let first = *spelled.entry(feature.spelling()).or_insert(feature);
            assert_eq!(
                first,
                feature,
                "`{}` spells one feature",
                feature.spelling()
            );
        }
        assert_eq!(
            spelled.len(),
            Unbuilt::ALL.len(),
            "every feature is listed once"
        );
    }
}
