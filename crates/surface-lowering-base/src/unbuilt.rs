//! The features the lowering has not built, each named where a refusal
//! declines it.
//!
//! # A refusal names its feature where it is raised
//!
//! A form the fragment reserves or does not admit carries the [`Unbuilt`]
//! feature it stops at, written by the site that refuses it:
//! [`FragmentBoundary::Reserved`](crate::error::FragmentBoundary::Reserved) and
//! [`FragmentBoundary::Unadmitted`](crate::error::FragmentBoundary::Unadmitted)
//! take the feature as their payload, and the dispatch table's declined kinds,
//! [`Former::Reserved`](crate::form::Former::Reserved) and
//! [`Former::Unadmitted`](crate::form::Former::Unadmitted), carry theirs. A
//! site that names no feature does not compile. Each feature answers its
//! spelling, the qualifier a fixture's `refuses("OutOfFragment.<spelling>")`
//! names it by, and the issue tracking it: an open issue of its own, or one a
//! shared cause shares (#2529). `check:tracking` holds every issue open, or
//! closed as not planned.
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

/// Generate [`Unbuilt`], its list [`Unbuilt::ALL`] and its spellings from one
/// list, so a new feature takes its place in each at once.
macro_rules! unbuilt {
    ($( $(#[doc = $doc:literal])* $variant:ident => $spelling:literal ),* $(,)?) => {
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
            $( $(#[doc = $doc])* $variant, )*
        }

        impl Unbuilt
        {
            /// Every feature, in declaration order.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// The qualifier a fixture's `refuses` expectation names the feature
            /// by: the refused form's kind, with a reading where the form stands
            /// for several features.
            ///
            /// # Specification
            /// - requires: nothing.
            /// - ensures: the feature's spelling, distinct from every other
            ///   feature's.
            /// - provides: the payload of `OutOfFragment.<spelling>`.
            /// - fails: never.
            /// - panics: none.
            /// - executable: none — the list is the specification; a predicate
            ///   would restate it row by row.
            ///
            /// # Adequacy
            /// - hypothesis: L3 — every feature's spelling is asserted apart from
            ///   every other's.
            /// - witness: `unbuilt::tests::every_feature_is_spelled_apart`
            #[inline]
            #[must_use]
            pub const fn spelling(self) -> Spelling
            {
                Spelling(match self {
                    $(Self::$variant => $spelling,)*
                })
            }
        }
    };
}

unbuilt! {
    /// A projection, `e.1` or `e.field`, where the fragment reads none, or a
    /// path the projection does not resolve.
    Projection => "projection_expression",
    /// A module packed at its model type, `pack M at Model(T)`, of a shape the
    /// lowering does not read.
    PackModel => "pack_model_expression",
    /// A model's manifest sorts forgotten, `forget[sort C = A, …](m) at
    /// Model(T)`, of a shape the lowering does not read.
    ForgetModel => "forget_model_expression",
    /// An annotation `(e : T)` read where a type, or nothing, is read.
    Annotation => "annotation_expression",
    /// A number literal written with the `f32` suffix, which has no atom yet:
    /// the integer widths and `f64` are built.
    TypedNumber => "typed_number",
    /// The shell block, `#!{ … }`.
    ShellBlock => "shell_block",
    /// A constructor field at a finite grade other than `1`.
    FieldGrade => "grade.declaration",
    /// The as-pattern `p as x`.
    AsPattern => "as_pattern",
    /// The list pattern `[p, …]`.
    ListPattern => "list_pattern",
    /// The rest pattern `..p`.
    RestPattern => "rest_pattern",
    /// The union type `A | B`.
    Union => "union_type",
    /// A recursive call's claim the lowering does not read: two claims at once,
    /// a resident that is no claim, a measure, a stage or a cost.
    RecursiveClaim => "instantiation_expression.computation",
    /// A call through a mutual block's joint whose member stages a parameter
    /// after its first, or passes leading parameters unchanged: the joint
    /// reads one domain, not a telescope.
    JointTelescope => "mutual_block.staged_after_first",
    /// The shared fork `fork !(…) { … } ;`.
    SharedFork => "fork_expression.shared",
    /// The endpoint copy `dup e`.
    Dup => "dup_expression",
    /// The statement `acquire …;`.
    Acquire => "acquire_expression",
    /// The statement `release …;`.
    Release => "release_expression",
    /// A type at a stage, `T[i]`, written under a form that places none.
    StagedType => "staged_type",
    /// The unknown type `?`.
    UnknownType => "unknown_type",
    /// String interpolation where the prelude holds no `string.append` to
    /// fold it with.
    Interpolation => "string_interpolation",
    /// A match on a view, `match e with v { … }`.
    MatchView => "match_with_view",
    /// A bind expression standing where a term is read.
    Bind => "bind_expression",
    /// A circuit declaration where a term is read.
    Circuit => "circuit_declaration",
    /// A codata declaration where a term is read.
    Codata => "codata_declaration",
    /// A word pattern `g ∷ p` where a term is read, or one whose head is no
    /// letter.
    ConsPattern => "cons_pattern",
    /// A constructor pattern where a term is read.
    ConstructorPattern => "constructor_pattern",
    /// A derived rule where a term is read.
    DerivedRule => "derived_rule_declaration",
    /// An extern block.
    ExternBlock => "extern_block",
    /// A host escape.
    HostEscape => "host_escape",
    /// An injection pattern where a term is read.
    LabelledSumPattern => "labelled_sum_pattern",
    /// A literal pattern other than a number or a boolean, or one where a term
    /// is read.
    LiteralPattern => "literal_pattern",
    /// A manifest sort where a term is read.
    ManifestSort => "manifest_sort",
    /// An or-pattern whose alternatives bind names, or one where a term is
    /// read.
    OrPattern => "or_pattern",
    /// A telescope pattern where a term is read.
    TelescopePattern => "telescope_pattern",
    /// A theory declaration where a term is read.
    Theory => "theory_declaration",
    /// A tuple pattern where a term is read.
    TuplePattern => "tuple_pattern",
    /// A shell block's command substitution.
    CommandSubstitution => "command_substitution",
    /// A shell block's double-quoted string.
    DoubleQuotedString => "double_quoted_string",
    /// A shell block's environment assignment.
    EnvironmentAssignment => "environment_assignment",
    /// A shell block's file descriptor.
    FileDescriptor => "file_descriptor",
    /// A shell block's glob.
    Glob => "glob_expression",
    /// A shell block's list operator.
    ListOperator => "list_operator",
    /// A shell block's pipeline.
    Pipeline => "pipeline",
    /// A shell block's redirection operator.
    RedirectionOperator => "redirection_operator",
    /// A shell block's word.
    ShellWord => "shell_word",
    /// A shell block's single-quoted string.
    SingleQuotedString => "single_quoted_string",
    /// A shell block's subshell.
    Subshell => "subshell",
    /// A shell block's variable expansion.
    VariableExpansion => "variable_expansion",
    /// A shell block's variable name.
    VariableName => "variable_name",
    /// A thunk's grade, `thunk[r] { … }`.
    ThunkGrade => "grade.value",
    /// A grade on a list, run or prefix type.
    TypeGrade => "grade.value_type",
    /// The type abstraction `fun [T] { … }`.
    TypeAbstraction => "type_abstraction",
    /// An infix form the lowering does not read: an operator outside the
    /// prelude's vocabulary, or a word `g ∷ w` whose `g` is neither a loop
    /// nor `back` of one; a `g` that names nothing is unresolved.
    InfixForm => "binary_expression",
    /// A prefix operator outside the prelude's vocabulary.
    PrefixOperator => "unary_expression",
    /// A match of no arms over a type no data switch reads, such as the
    /// empty sum, written with its answer type.
    EmptyMatch => "match_expression",
    /// A form where a pattern is read that no pattern reading takes and the
    /// table declines by no feature of its own.
    UnreadPattern => "pattern",
    /// A stated type component whose held declaration the collection does not
    /// carry.
    StatedType => "stated_type",
    /// A presentation block whose body the description does not read.
    Presentation => "presentation",
    /// A recorded move that is no call and no closing name.
    RecordedMove => "recorded_move",
    /// A dialogue move that is no endpoint's call of one move.
    DialogueMove => "dialogue_move",
    /// A supply whose residents mix a named supply with what is no supply.
    CombinedSupply => "instantiation_expression.combined",
    /// A staged supply no declaration owns.
    UnownedSupply => "instantiation_expression.unowned",
    /// A capability scope over a theory no declaration owns, so no
    /// declaration owes its laws.
    UnownedScope => "handle_expression.unowned",
    /// A method call whose declaration the collection does not carry.
    MethodCall => "method_call",
    /// A manifest model type of a shape the lowering does not read.
    ManifestModel => "manifest_type",
    /// A model type over a theory the lowering does not present.
    ModelType => "model_type",
    /// A loop's name inside a pattern rather than as an arm's whole pattern.
    LoopPattern => "loop_pattern",
    /// A session type the protocol builder does not read.
    SessionProtocol => "session_protocol",
    /// A stage supply whose resident is no single tile.
    StageResident => "instantiation_expression.stage",
    /// A stratum resident, or a chain's cell count, not written in digits
    /// alone.
    UaCount => "ua_count",
    /// A univalence description the lowering does not read.
    UaDescription => "ua_description",
    /// A composite's shape that is no `chain(m)`.
    ComposePasting => "compose_pasting",
    /// A cell member with parameters, a side that is no closed term, or a rule
    /// arrow.
    CellMember => "cell_member",
    /// An attribute block on a data block's generator.
    GeneratorAttribute => "attribute",
    /// A model signature the derivation cannot state.
    ModelSignature => "model_signature",
    /// The terms `Terms(S)` of a theory outside one plain sort: several sorts,
    /// an indexed one, or an operation that binds, abstracts or returns
    /// several results.
    TermsType => "terms_type.sorted",
    /// The terms `Terms(S)` of a theory that states a law, which the initial
    /// model carries as a cell.
    LawTerms => "terms_type.law",
    /// A multi-output constructor grading an input or an output `[1]`: the
    /// linear reading, whose values are circuits.
    LinearPorts => "linear_ports",
    /// A pattern naming a multi-output constructor with no output: the joint
    /// pattern over a node's outputs, the linear reading's. At grade ω a value
    /// is one port, matched as `C(x).l`.
    PortPattern => "port_pattern",
    /// An inner attribute block at a source's root, `@![ … ]`: the source it
    /// decorates has no key of its own yet.
    SourceAttribute => "inner_attribute_block",
    /// A value a static bracket fixes that the lowering does not read: a
    /// face's value that is no record written in place.
    FixedValue => "staged_type.fixed_value",
    /// A static bracket over a record type a field of which names an earlier
    /// field.
    DependentPatch => "staged_type.dependent",
}

impl Unbuilt
{
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
            Self::PackModel | Self::ForgetModel => TrackingIssue::PACKAGES,
            Self::TypedNumber => TrackingIssue::TYPED_NUMBER,
            Self::FieldGrade => TrackingIssue::FIELD_GRADE,
            Self::Union => TrackingIssue::UNION,
            Self::PrefixOperator => TrackingIssue::USER_OPERATORS,
            Self::RecursiveClaim => TrackingIssue::RECURSIVE_CLAIM,
            Self::JointTelescope => TrackingIssue::JOINT_TELESCOPE,
            Self::SharedFork | Self::Dup | Self::Acquire | Self::Release => {
                TrackingIssue::SHARED_SESSIONS
            },
            Self::StagedType => TrackingIssue::PLACED_STAGE,
            Self::UnknownType => TrackingIssue::UNKNOWN_TYPE,
            Self::MatchView => TrackingIssue::MATCH_VIEW,
            Self::ThunkGrade => TrackingIssue::THUNK_GRADE,
            Self::InfixForm => TrackingIssue::INFIX_FORM,
            Self::EmptyMatch => TrackingIssue::EMPTY_CASE_ANSWER,
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
            | Self::DerivedRule
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
            Self::ComposePasting => TrackingIssue::ITERATED_SITE,
            Self::TermsType => TrackingIssue::SORTED_TERMS,
            Self::LawTerms => TrackingIssue::LAW_CELL,
            Self::CellMember | Self::GeneratorAttribute => TrackingIssue::DATA_MEMBER,
            Self::LinearPorts | Self::PortPattern => TrackingIssue::LINEAR_PORTS,
            Self::SourceAttribute => TrackingIssue::SOURCE_ATTRIBUTE,
            Self::FixedValue | Self::DependentPatch => TrackingIssue::PATCHED_TYPE,
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
