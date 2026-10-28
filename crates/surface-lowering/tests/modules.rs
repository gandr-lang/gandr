//! Module declarations and nested modules, lowered: every member flattened to
//! one declaration in source order under its structured name, every path
//! governed by the module that binds it, inline signatures matched coercively
//! against the body, and the refusals a module, a member and a component
//! earn, each asserted through the declarations the lowering hands a checker
//! and through the checker's verdicts over them.
//!
//! The module cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

mod functors;

mod models;

use alloc::sync::Arc;
use core::fmt::Write as _;

use anodized::spec;
use gandr_core_checker::AbstractType;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::ComponentOrdinal;
use gandr_core_checker::Declaration;
use gandr_core_checker::Mismatch;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::SealSite;
use gandr_core_checker::SealingSite;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::Value as KernelValue;
use gandr_kernel_term::decode;
use gandr_surface_grammar::NamedKind;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::AscriptionForm;
use gandr_surface_lowering::AttributeSchema;
use gandr_surface_lowering::Coerced;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::Ending;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::FragmentSort;
use gandr_surface_lowering::Labelled;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweredStructure;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OperandCount;
use gandr_surface_lowering::PayloadForm;
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::Repair;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::TelescopeFault;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::PathResolution;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering::namespace::Recognized;
use gandr_surface_lowering::namespace::SegmentCount;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

/// A source lowered over its own arena.
///
/// # Specification
/// - requires: the module is interpreted against its retained arena.
/// - ensures: emitted bodies and signatures remain readable in that arena after
///   checker append operations.
/// - provides: a paired lowering fixture, not globally authenticated numeric
///   identifiers.
/// - fails: none as a data value.
/// - panics: none.
/// - executable: none — type-level invariant expansion is unavailable in the
///   enabled facade; `finish` checks the arena membership relation.
///
/// # Adequacy
/// - hypothesis: L2 on the named parsed fixtures — lowered members are checked
///   through the same arena, including mismatched ascribed components.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
struct Lowered<'source>
{
    /// The lowered module.
    module: LoweredModule<'source>,
    /// The arena its core nodes were minted into.
    arena: CoreArena,
}

/// What one declaration amounts to, as these tests compare it.
///
/// # Specification
/// - requires: a value is interpreted as the normalization of one declaration
///   outcome.
/// - ensures: completed, signature-only, body-only and refused outcomes stay
///   distinct; a refusal retains its payload.
/// - provides: a coordinate-independent outcome observer.
/// - fails: none as a data value.
/// - panics: none.
/// - executable: none — the original declaration is not retained; `rows` checks
///   the exact normalization.
///
/// # Adequacy
/// - hypothesis: L3 — ordered declarations and held manifest refusals
///   distinguish the successful shapes from an erased or displaced refusal.
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::manifest_refusals_propagate_transitively_before_minting`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Amounts<'source>
{
    /// A signature and a definition, both lowered.
    Completed,
    /// A signature alone: the obligation the module owes.
    Uncompleted,
    /// A definition alone.
    Bodied,
    /// A native data signature.
    Data,
    /// A decoded codata signature.
    Codata,
    /// A sealed abstract type.
    Abstract,
    /// A world declaration.
    World,
    /// The lowering's refusal.
    Refused(LoweringRefusal<'source>),
}

/// What the checker said about one declaration, as these tests compare it.
///
/// # Specification
/// - requires: a value is interpreted as the normalization of one checking
///   verdict.
/// - ensures: checked, synthesized, owed and refused outcomes remain distinct,
///   with type mismatch separated from other refusals.
/// - provides: the checking observer for module fixtures.
/// - fails: none as a data value.
/// - panics: none.
/// - executable: none — the original checker report is not retained; `verdicts`
///   checks positional and outcome-shape constraints.
///
/// # Adequacy
/// - hypothesis: L3 — mismatched components and body holes distinguish a
///   refusal from an obligation and a successful check.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::a_dangling_member_signature_is_an_obligation`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Judgement
{
    /// The body checked against the declared type.
    Checked,
    /// The unsigned body synthesised its type.
    Synthesised,
    /// The body is a hole, owed.
    Owed,
    /// The body waits on owed holes.
    Suspended,
    /// The body's type does not convert to the declared one.
    Mismatched,
    /// Any other refusal.
    Refused,
    /// A nominal declaration, a sealed abstract type's atom or a data
    /// signature, admitted.
    Declared,
}

/// One module's stratum item, as these tests compare it.
///
/// # Specification
/// - requires: component coordinates are interpreted against their source
///   module.
/// - ensures: the path, ordered value and module inventories, and coercion
///   status stay independently observable.
/// - provides: an export view that omits arena-local type identifiers.
/// - fails: none as a data value.
/// - panics: none.
/// - executable: none — the source structure is not retained; `strata` checks
///   the complete normalized view and the builders specify their updates.
///
/// # Adequacy
/// - hypothesis: L2 on the named goldens — reordering and hiding change exports
///   without changing member admission order; nesting retains parent paths.
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
/// - witness: `tests::modules::module_signature_matching_hides_extra_members`
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[derive(Debug, Eq, PartialEq)]
struct Stratum
{
    /// The module's dotted path.
    path: String,
    /// Its value components, in export order, with their positions.
    values: Vec<(String, ConstantIndex)>,
    /// Its nested modules, in export order.
    modules: Vec<String>,
    /// Whether matching coerced its body.
    coerced: Coerced,
}

impl Stratum
{
    /// The expected item of the module at `path`, exporting nothing yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an expected stratum starts with no exports and retains its
    ///   coercion status.
    /// - provides: the initial state of an expected export inventory.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and coerced module fixtures distinguish an
    ///   empty inventory from a copied export list or a changed coercion flag.
    /// - witness: `tests::modules::an_empty_module_is_not_an_unread_one`
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    #[spec(
            ensures: |ret| ret.values.is_empty() && ret.modules.is_empty() && ret.coerced == coerced,
        )]
    fn new<Path>(
        path: Path,
        coerced: Coerced,
    ) -> Self
    where
        Path: Into<String>,
    {
        Self {
            path: path.into(),
            values: Vec::new(),
            modules: Vec::new(),
            coerced,
        }
    }

    /// This item, exporting the value component `name` at `position` next.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one value component is appended without changing the
    ///   nested-module inventory or coercion flag.
    /// - provides: an ordered expected value inventory.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — multi-member and reordered signatures compare the
    ///   whole export inventory, distinguishing append from replacement.
    /// - witness: `tests::modules::module_members_admit_in_source_order`
    /// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
    #[spec(
            captures: before = (self.values.len(), self.modules.len(), self.coerced),
            ensures: |ret| {
                ret.values.len() == before.0.saturating_add(1)
                    && ret.modules.len() == before.1
                    && ret.coerced == before.2
            },
        )]
    fn value<Name, Position>(
        mut self,
        name: Name,
        position: Position,
    ) -> Self
    where
        Name: Into<String>,
        Position: Into<ConstantIndex>,
    {
        self.values.push((name.into(), position.into()));
        self
    }

    /// This item, exporting the nested module `name` next.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one nested-module component is appended without changing the
    ///   value inventory or coercion flag.
    /// - provides: an ordered expected module inventory.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested module fixtures compare parent and child
    ///   inventories, distinguishing an append from replacing earlier
    ///   components.
    /// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
    #[spec(
            captures: before = (self.modules.len(), self.values.len(), self.coerced),
            ensures: |ret| {
                ret.modules.len() == before.0.saturating_add(1)
                    && ret.values.len() == before.1
                    && ret.coerced == before.2
            },
        )]
    fn module<Name>(
        mut self,
        name: Name,
    ) -> Self
    where
        Name: Into<String>,
    {
        self.modules.push(name.into());
        self
    }
}

/// `source` parsed under the built-in grammar, which reads it without
/// repair, and lowered against an empty outermost scope.
///
/// # Specification
/// - requires: the source parses cleanly and fits the default lowering
///   allowance.
/// - ensures: the lowered module and its retained arena agree on every emitted
///   core coordinate.
/// - provides: a real parser-to-lowering fixture with no outermost names.
/// - fails: none for an accepted fixture.
/// - panics: on parsing, repair or engine refusal.
///
/// # Adequacy
/// - hypothesis: L2 on the named module goldens — complete and body-only
///   members retain their actual core nodes in the paired arena.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
#[spec(
        ensures: |ret| {
            ret.module
                .declarations()
                .iter()
                .all(|declaration| match declaration.outcome() {
                    | DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => {
                        ret.arena.value_type(declared_type).is_some()
                            && ret.arena.value(body).is_some()
                    },
                    | DeclarationOutcome::Uncompleted { declared_type } => {
                        ret.arena.value_type(declared_type).is_some()
                    },
                    | DeclarationOutcome::Bodied { body } => ret.arena.value(body).is_some(),
                    | DeclarationOutcome::Data(index) => matches!(ret.module.data(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Codata(index) => matches!(ret.module.codata(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Abstract(sealing) => ret.arena.value_type(sealing.kind).is_some() && ret.arena.value_type(sealing.representation).is_some(),
                    | DeclarationOutcome::Refused(_) | DeclarationOutcome::World => true,
                })
        },
    )]
fn lower<'source, Text>(source: Text) -> Lowered<'source>
where
    Text: Into<SourceText<'source>>,
{
    let source = source.into();
    let pbg = built_in().expect("the built-in grammar builds");
    let parsed = parse(&pbg, source).expect("the parser reads the source");
    assert!(
        bool::from(parsed.is_clean()),
        "the parser reads the source without repair: {source}"
    );
    finish(&pbg, &parsed.into_tree())
}

/// `source` parsed under the built-in grammar, which repairs it, and
/// lowered against an empty outermost scope.
///
/// # Specification
/// - requires: the parser repairs the fixture and the lowering engine accepts
///   its tree.
/// - ensures: emitted core coordinates remain readable in the retained arena
///   despite local repairs.
/// - provides: a repaired-source fixture without discarding unrelated members.
/// - fails: none for an accepted fixture.
/// - panics: on an unparseable or clean source, or an engine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — malformed members and repaired containers preserve their
///   independently asserted surviving declarations.
/// - witness: `tests::modules::a_malformed_member_is_repaired_and_its_siblings_kept`
/// - witness: `tests::modules::a_repaired_container_keeps_its_member`
#[spec(
        ensures: |ret| {
            ret.module
                .declarations()
                .iter()
                .all(|declaration| match declaration.outcome() {
                    | DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => {
                        ret.arena.value_type(declared_type).is_some()
                            && ret.arena.value(body).is_some()
                    },
                    | DeclarationOutcome::Uncompleted { declared_type } => {
                        ret.arena.value_type(declared_type).is_some()
                    },
                    | DeclarationOutcome::Bodied { body } => ret.arena.value(body).is_some(),
                    | DeclarationOutcome::Data(index) => matches!(ret.module.data(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Codata(index) => matches!(ret.module.codata(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Abstract(sealing) => ret.arena.value_type(sealing.kind).is_some() && ret.arena.value_type(sealing.representation).is_some(),
                    | DeclarationOutcome::Refused(_) | DeclarationOutcome::World => true,
                })
        },
    )]
fn repaired<'source, Text>(source: Text) -> Lowered<'source>
where
    Text: Into<SourceText<'source>>,
{
    let source = source.into();
    let pbg = built_in().expect("the built-in grammar builds");
    let parsed = parse(&pbg, source).expect("the parser reads the source");
    assert!(
        !bool::from(parsed.is_clean()),
        "the parser repairs the source: {source}"
    );
    finish(&pbg, &parsed.into_tree())
}

/// `tree` lowered against an empty outermost scope.
///
/// # Specification
/// - requires: the grammar matches the tree and the engine accepts it within
///   the default allowance.
/// - ensures: the module’s body and signature identifiers refer to nodes in the
///   paired arena.
/// - provides: a coherent lowered fixture rather than detached numeric
///   identifiers.
/// - fails: none for an accepted fixture.
/// - panics: if the lowering engine refuses the tree.
///
/// # Adequacy
/// - hypothesis: L2 on the named goldens — successful and locally refused
///   members coexist while successful nodes remain readable by the checker.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::a_transparent_abstract_component_reads_its_type_member`
#[spec(
        ensures: |ret| {
            ret.module
                .declarations()
                .iter()
                .all(|declaration| match declaration.outcome() {
                    | DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => {
                        ret.arena.value_type(declared_type).is_some()
                            && ret.arena.value(body).is_some()
                    },
                    | DeclarationOutcome::Uncompleted { declared_type } => {
                        ret.arena.value_type(declared_type).is_some()
                    },
                    | DeclarationOutcome::Bodied { body } => ret.arena.value(body).is_some(),
                    | DeclarationOutcome::Data(index) => matches!(ret.module.data(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Codata(index) => matches!(ret.module.codata(index), Maybe::Present(signature) if ret.arena.value_type(signature.kind()).is_some()),
                    | DeclarationOutcome::Abstract(sealing) => ret.arena.value_type(sealing.kind).is_some() && ret.arena.value_type(sealing.representation).is_some(),
                    | DeclarationOutcome::Refused(_) | DeclarationOutcome::World => true,
                })
        },
    )]
fn finish<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Lowered<'source>
{
    let mut arena = CoreArena::new();
    let module = lower_module(
        pbg,
        tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the module lowers");
    Lowered { module, arena }
}

/// The dotted path of `declaration` in `module`.
///
/// # Specification
/// - requires: the declaration and container coordinates belong to the module;
///   name segments contain no period.
/// - ensures: the container path — a derived rule's statement's theory —
///   followed by the declaration’s own name, joined with periods.
/// - provides: an arena-coordinate-independent declaration key for these
///   fixtures.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — top-level and nested members retain every container
///   segment, distinguishing same-leaf names in different modules.
/// - witness: `tests::modules::modules_lower_to_named_member_declarations`
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[spec(
        ensures: |ret| {
            let theory = module.theory_of(declaration);
            let prefix: &[SurfaceName<'_>] = match (theory.as_ref(), declaration.container()) {
                | (Some(theory), _) => core::slice::from_ref(theory),
                | (None, gandr_surface_lowering::Container::TopLevel(_)) => &[],
                | (None, gandr_surface_lowering::Container::Module(index)) => module
                    .structures()
                    .get(usize::from(index))
                    .map_or(&[], LoweredStructure::path),
            };
            ret.split('.').eq(prefix
                .iter()
                .map(AsRef::as_ref)
                .chain(core::iter::once(declaration.name().as_ref())))
        },
    )]
fn dotted(
    module: &LoweredModule<'_>,
    declaration: &LoweredDeclaration<'_>,
) -> String
{
    module
        .path_of(declaration)
        .iter()
        .map(|segment| String::from(segment.as_ref()))
        .collect::<Vec<String>>()
        .join(".")
}

/// Each declaration of `lowered`, in admission order: its dotted path, its
/// role and what it amounts to.
///
/// # Specification
/// - requires: a coherent parsed fixture with period-free name segments.
/// - ensures: one row per declaration in admission order, preserving its
///   qualified name, role and semantic outcome.
/// - provides: the normalized declaration observer used by module goldens.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the named goldens — source order and explicit held
///   refusals distinguish omission, reordering and outcome erasure.
/// - witness: `tests::modules::module_members_admit_in_source_order`
/// - witness: `tests::modules::manifest_refusals_propagate_transitively_before_minting`
#[spec(
        ensures: |ret| {
            ret.len() == lowered.module.declarations().iter().len()
                && ret.iter().zip(lowered.module.declarations()).all(
                    |(&(ref path, role, amounts), declaration)| {
                        role == declaration.role()
                            && {
                                let theory = lowered.module.theory_of(declaration);
                                let prefix: &[SurfaceName<'_>] = match (theory.as_ref(), declaration.container()) {
                                    | (Some(theory), _) => core::slice::from_ref(theory),
                                    | (None, gandr_surface_lowering::Container::TopLevel(_)) => &[],
                                    | (None, gandr_surface_lowering::Container::Module(index)) => lowered
                                        .module
                                        .structures()
                                        .get(usize::from(index))
                                        .map_or(&[], LoweredStructure::path),
                                };
                                path.split('.').eq(prefix
                                    .iter()
                                    .map(AsRef::as_ref)
                                    .chain(core::iter::once(declaration.name().as_ref())))
                            }
                            && match (amounts, declaration.outcome()) {
                                | (Amounts::Completed, DeclarationOutcome::Completed { .. })
                                | (
                                    Amounts::Uncompleted,
                                    DeclarationOutcome::Uncompleted { .. },
                                )
                                | (Amounts::Bodied, DeclarationOutcome::Bodied { .. })
                                | (Amounts::Data, DeclarationOutcome::Data(_))
                                | (Amounts::Codata, DeclarationOutcome::Codata(_))
                                | (Amounts::Abstract, DeclarationOutcome::Abstract(_))
                                | (Amounts::World, DeclarationOutcome::World) => true,
                                | (
                                    Amounts::Refused(actual),
                                    DeclarationOutcome::Refused(expected),
                                ) => actual == expected,
                                | _ => false,
                            }
                    },
                )
        },
    )]
fn rows<'source>(lowered: &Lowered<'source>) -> Vec<(String, Role, Amounts<'source>)>
{
    lowered
        .module
        .declarations()
        .iter()
        .map(|declaration| {
            let amounts = match declaration.outcome() {
                DeclarationOutcome::Completed { .. } => Amounts::Completed,
                DeclarationOutcome::Uncompleted { .. } => Amounts::Uncompleted,
                DeclarationOutcome::Bodied { .. } => Amounts::Bodied,
                DeclarationOutcome::Data(_) => Amounts::Data,
                DeclarationOutcome::Codata(_) => Amounts::Codata,
                DeclarationOutcome::Abstract(_) => Amounts::Abstract,
                DeclarationOutcome::World => Amounts::World,
                DeclarationOutcome::Refused(refusal) => Amounts::Refused(refusal),
            };
            (
                dotted(&lowered.module, declaration),
                declaration.role(),
                amounts,
            )
        })
        .collect()
}

/// One expected row.
///
/// # Specification
/// trivial.
fn row<Path>(
    path: Path,
    role: Role,
    amounts: Amounts<'_>,
) -> (String, Role, Amounts<'_>)
where
    Path: Into<String>,
{
    (path.into(), role, amounts)
}

/// The declaration of `lowered` at `path` in `role`.
///
/// # Specification
/// - requires: one declaration has the requested qualified path and role.
/// - ensures: the matching declaration is borrowed from the fixture’s
///   admission-ordered array.
/// - provides: a role-sensitive selector, not a same-leaf-name lookup.
/// - fails: none when the requested declaration exists.
/// - panics: if no declaration matches.
///
/// # Adequacy
/// - hypothesis: L3 — nested and ascribed declarations distinguish qualified
///   paths and declared versus witness roles.
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
/// - witness: `tests::modules::a_missing_signature_component_is_rejected_at_the_signature`
#[spec(
        ensures: |ret| {
            ret.role() == role
                && {
                    let prefix: &[SurfaceName<'_>] = match ret.container() {
                        | gandr_surface_lowering::Container::TopLevel(_) => &[],
                        | gandr_surface_lowering::Container::Module(index) => lowered
                            .module
                            .structures()
                            .get(usize::from(index))
                            .map_or(&[], LoweredStructure::path),
                    };
                    path.as_ref().split('.').eq(prefix
                        .iter()
                        .map(AsRef::as_ref)
                        .chain(core::iter::once(ret.name().as_ref())))
                }
                && matches!(
                    lowered.module.declarations().search(&ret.constant(), LoweredDeclaration::constant),
                    Maybe::Present(stored) if core::ptr::eq(&raw const *stored, &raw const *ret)
                )
        },
    )]
fn declaration<'lowered, 'source, Path>(
    lowered: &'lowered Lowered<'source>,
    path: Path,
    role: Role,
) -> &'lowered LoweredDeclaration<'source>
where
    Path: AsRef<str>,
{
    let path = path.as_ref();
    lowered
        .module
        .declarations()
        .iter()
        .find(|declaration| {
            declaration.role() == role && dotted(&lowered.module, declaration) == path
        })
        .unwrap_or_else(|| panic!("a {role:?} declaration at `{path}`"))
}

/// The body of the declared name at `path`.
///
/// # Specification
/// - requires: the declared name has a completed or body-only outcome.
/// - ensures: the selected declaration’s body identifier.
/// - provides: the core body used by structural assertions.
/// - fails: none on the required outcome variants.
/// - panics: if the name is absent or has no body.
///
/// # Adequacy
/// - hypothesis: L3 — module member selections retain the exact constant body
///   instead of a sibling’s coordinate or a signature identifier.
/// - witness: `tests::modules::a_backward_member_reference_resolves`
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[spec(
        ensures: |ret| {
            lowered.module.declarations().iter().any(|declaration| declaration.role() == Role::Declared && { let prefix: &[SurfaceName<'_>] = match declaration.container() { gandr_surface_lowering::Container::TopLevel(_) => &[], gandr_surface_lowering::Container::Module(index) => lowered.module.structures().get(usize::from(index)).map_or(&[], LoweredStructure::path), }; path.as_ref().split('.').eq(prefix.iter().map(AsRef::as_ref).chain(core::iter::once(declaration.name().as_ref()))) } && matches!(declaration.outcome(), DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } if body == ret))
        },
    )]
fn body_of<Path>(
    lowered: &Lowered<'_>,
    path: Path,
) -> ValueId
where
    Path: AsRef<str>,
{
    let path = path.as_ref();
    match declaration(lowered, path, Role::Declared).outcome() {
        DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => body,
        outcome @ (DeclarationOutcome::Uncompleted { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => {
            panic!("`{path}` has a body, not {outcome:?}")
        },
    }
}

/// The constant the body of the declared name at `path` is.
///
/// # Specification
/// - requires: the selected declaration’s body is a constant reference.
/// - ensures: that body’s exact referenced constant, not the declaration’s own
///   admission position.
/// - provides: a semantic resolution observer.
/// - fails: none on a constant body.
/// - panics: if the declaration is absent or its body is not a constant.
///
/// # Adequacy
/// - hypothesis: L3 — backward references and nested selections name their
///   target’s admission coordinate rather than the referring declaration.
/// - witness: `tests::modules::a_backward_member_reference_resolves`
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
#[spec(
        ensures: |ret| {
            lowered.module.declarations().iter().any(|declaration| {
                declaration.role() == Role::Declared
                    && {
                        let prefix: &[SurfaceName<'_>] = match declaration.container() {
                            | gandr_surface_lowering::Container::TopLevel(_) => &[],
                            | gandr_surface_lowering::Container::Module(index) => lowered
                                .module
                                .structures()
                                .get(usize::from(index))
                                .map_or(&[], LoweredStructure::path),
                        };
                        path.as_ref().split('.').eq(prefix
                            .iter()
                            .map(AsRef::as_ref)
                            .chain(core::iter::once(declaration.name().as_ref())))
                    }
                    && match declaration.outcome() {
                        | DeclarationOutcome::Completed { body, .. }
                        | DeclarationOutcome::Bodied { body } => {
                            lowered.arena.value(body) == Some(&Value::Constant(ret))
                        },
                        | _ => false,
                    }
            })
        },
    )]
fn constant_read_by<Path>(
    lowered: &Lowered<'_>,
    path: Path,
) -> ConstantIndex
where
    Path: AsRef<str>,
{
    let path = path.as_ref();
    match lowered.arena.value(body_of(lowered, path)) {
        Some(&Value::Constant(constant)) => constant,
        other => panic!("`{path}` is a constant, not {other:?}"),
    }
}

/// The declared type of the declaration at `path` in `role`.
///
/// # Specification
/// - requires: the selected role and qualified name have a lowered signature.
/// - ensures: the exact declared type of that declaration.
/// - provides: a role-sensitive type observer for ascriptions and witnesses.
/// - fails: none on the required outcome variants.
/// - panics: if the name is absent or has no signature.
///
/// # Adequacy
/// - hypothesis: L3 — written and derived member signatures distinguish their
///   core types and the ascription origin that supplies them.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::member_signature_attaches_and_wins_over_derived_function_type`
#[spec(
        ensures: |ret| {
            lowered.module.declarations().iter().any(|declaration| declaration.role() == role && { let prefix: &[SurfaceName<'_>] = match declaration.container() { gandr_surface_lowering::Container::TopLevel(_) => &[], gandr_surface_lowering::Container::Module(index) => lowered.module.structures().get(usize::from(index)).map_or(&[], LoweredStructure::path), }; path.as_ref().split('.').eq(prefix.iter().map(AsRef::as_ref).chain(core::iter::once(declaration.name().as_ref()))) } && matches!(declaration.outcome(), DeclarationOutcome::Completed { declared_type, .. } | DeclarationOutcome::Uncompleted { declared_type } if declared_type == ret))
        },
    )]
fn declared_type_of<Path>(
    lowered: &Lowered<'_>,
    path: Path,
    role: Role,
) -> ValueTypeId
where
    Path: AsRef<str>,
{
    let path = path.as_ref();
    match declaration(lowered, path, role).outcome() {
        DeclarationOutcome::Completed { declared_type, .. }
        | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
        outcome @ (DeclarationOutcome::Bodied { .. }
        | DeclarationOutcome::Data(_)
        | DeclarationOutcome::Codata(_)
        | DeclarationOutcome::Abstract(_)
        | DeclarationOutcome::World
        | DeclarationOutcome::Refused(_)) => {
            panic!("`{path}` has a declared type, not {outcome:?}")
        },
    }
}

/// The bytes the origin of the type `declared` covers.
///
/// # Specification
/// - requires: the type has an origin in this fixture’s table.
/// - ensures: the span recorded for that value-type identifier.
/// - provides: the source observer for a written or derived signature.
/// - fails: none for a recorded type.
/// - panics: if the origin is absent.
///
/// # Adequacy
/// - hypothesis: L3 — ascribed member types retain the written component’s
///   span, distinct from the member body or another component.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::computation_signed_module_member_origin_mirrors_ascription_encoding`
#[spec(
        ensures: |ret| matches!(lowered.module.origins().value_type(declared), Maybe::Present(origin) if ret == origin.span()),
    )]
fn origin_of(
    lowered: &Lowered<'_>,
    declared: ValueTypeId,
) -> ByteSpan
{
    match lowered.module.origins().value_type(declared) {
        Maybe::Present(origin) => origin.span(),
        Maybe::Absent(absent) => panic!("every minted type has an origin, not {absent:?}"),
    }
}

/// Every module's stratum item, in pre-order.
///
/// # Specification
/// - requires: a coherent parsed fixture with period-free name segments.
/// - ensures: one stratum per structure in preorder, preserving each ordered
///   export inventory and coercion flag.
/// - provides: the semantic export observer used by module goldens.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on the named goldens — nested modules, reordered exports
///   and hidden members distinguish preorder from admission order and the
///   public inventory from every collected member.
/// - witness: `tests::modules::nested_modules_lower_as_parent_members_and_project`
/// - witness: `tests::modules::a_reordered_signature_matches_and_canonicalizes`
/// - witness: `tests::modules::module_signature_matching_hides_extra_members`
#[spec(
        ensures: |ret| {
            ret.len() == lowered.module.structures().len()
                && ret
                    .iter()
                    .zip(lowered.module.structures())
                    .all(|(actual, structure)| {
                        actual.coerced == structure.coerced()
                            && actual
                                .path
                                .split('.')
                                .eq(structure.path().iter().map(AsRef::as_ref))
                            && actual.values.len() == structure.values().len()
                            && actual.values.iter().zip(structure.values()).all(
                                |(&(ref name, constant), value)| {
                                    name == value.name.as_ref() && constant == value.constant
                                },
                            )
                            && actual
                                .modules
                                .iter()
                                .map(String::as_str)
                                .eq(structure.modules().iter().map(AsRef::as_ref))
                    })
        },
    )]
fn strata(lowered: &Lowered<'_>) -> Vec<Stratum>
{
    lowered
        .module
        .structures()
        .iter()
        .map(|structure| Stratum {
            path: {
                let mut path = String::new();
                for (index, segment) in structure.path().iter().enumerate() {
                    if index > 0 {
                        path.push('.');
                    }
                    path.push_str(AsRef::<str>::as_ref(segment));
                }
                path
            },
            values: structure
                .values()
                .iter()
                .map(|value| (String::from(value.name.as_ref()), value.constant))
                .collect(),
            modules: structure
                .modules()
                .iter()
                .map(|name| String::from(name.as_ref()))
                .collect(),
            coerced: structure.coerced(),
        })
        .collect()
}

/// The checker's report over every declaration `lowered` did not refuse, the
/// reducts the module mints kept as the dispatcher keeps them.
///
/// # Specification
/// - requires: the fixture’s core identifiers belong to its arena and fit the
///   checker’s default allowance.
/// - ensures: every unrefused declaration is checked at its original admission
///   coordinate; lowering refusals are not submitted.
/// - provides: a real checking report over the lowered core.
/// - fails: checking refusals remain in the returned report.
/// - panics: none for a coherent fixture.
///
/// # Adequacy
/// - hypothesis: L3 — matching and mismatching signatures, body-only members
///   and signature obligations preserve their distinct checker verdicts.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::a_dangling_member_signature_is_an_obligation`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "test fixture: the body walks every lowered declaration and checks the module; the check walks the declarations once"
    )
)]
#[spec(
        ensures: |ret| {
            ret.judged()
                .iter()
                .map(gandr_core_checker::Judged::constant)
                .eq(lowered
                    .module
                    .declarations()
                    .iter()
                    .filter(|declaration| {
                        !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))
                    })
                    .map(LoweredDeclaration::constant))
        },
    )]
fn report(lowered: &mut Lowered<'_>) -> ModuleReport
{
    let declarations: Vec<Declaration> = lowered
        .module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let (declared, defined) = match declaration.outcome() {
                DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(if declaration.role() == Role::Admitted {
                        body::Absent::Hosted
                    }
                    else {
                        body::Absent::Hole
                    }),
                ),
                DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                DeclarationOutcome::Data(index) => {
                    return match lowered.module.data(index) {
                        Maybe::Present(signature) => Some(Declaration::data(
                            declaration.constant(),
                            Arc::clone(signature),
                            OriginToken::from(usize::from(declaration.origin())),
                        )),
                        Maybe::Absent(_) => None,
                    };
                },
                DeclarationOutcome::Codata(index) => {
                    return match lowered.module.codata(index) {
                        Maybe::Present(signature) => Some(Declaration::codata(
                            declaration.constant(),
                            Arc::clone(signature),
                            OriginToken::from(usize::from(declaration.origin())),
                        )),
                        Maybe::Absent(_) => None,
                    };
                },
                DeclarationOutcome::Abstract(sealing) => {
                    let site = SealSite::new(
                        SealingSite::from(usize::from(sealing.sealing)),
                        ComponentOrdinal::from(usize::from(sealing.component)),
                    );
                    return Some(Declaration::abstract_type(
                        declaration.constant(),
                        AbstractType::new(
                            sealing.kind,
                            sealing.representation,
                            sealing.extent,
                            site,
                        ),
                        OriginToken::from(usize::from(declaration.origin())),
                    ));
                },
                DeclarationOutcome::World => {
                    return Some(Declaration::world(
                        declaration.constant(),
                        OriginToken::from(usize::from(declaration.origin())),
                    ));
                },
                DeclarationOutcome::Refused(_) => return None,
            };
            Some(Declaration::new(
                declaration.constant(),
                declared,
                defined,
                OriginToken::from(usize::from(declaration.origin())),
            ))
        })
        .collect();
    let mut context = CheckingContext::new(&mut lowered.arena, CheckBudget::DEFAULT);
    context.keep_reducts(lowered.module.reducts());
    context.keep_reducts(lowered.module.forgets());
    check_module(&mut context, &declarations)
}

/// The checker's judgement of every declaration `lowered` did not refuse,
/// by admission position.
///
/// # Specification
/// - requires: a coherent lowered fixture accepted by the checker’s run budget.
/// - ensures: one normalized judgement per unrefused declaration in admission
///   order; a type mismatch remains distinct from another checking refusal.
/// - provides: the semantic checker observer used by module goldens.
/// - fails: checking failures are represented, not panicked away.
/// - panics: none for a coherent fixture.
///
/// # Adequacy
/// - hypothesis: L3 — a correct component, a mismatched component and an
///   uncompleted signature distinguish checked, mismatched and owed results.
/// - witness: `tests::modules::a_nonempty_ascription_checks_each_component_at_its_member`
/// - witness: `tests::modules::a_dangling_member_signature_is_an_obligation`
/// - witness: `tests::modules::opaque_ascription_seals`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "test fixture: the body checks every lowered declaration; the check walks the declarations once beside the judgements"
    )
)]
#[spec(
        ensures: |ret| {
            let mut actual = ret.iter();
            lowered
                .module
                .declarations()
                .iter()
                .filter(|declaration| {
                    !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))
                })
                .all(|declaration| match actual.next() {
                    | Some(&(constant, judgement)) if constant == declaration.constant() => {
                        match judgement {
                            | Judgement::Checked => matches!(
                                declaration.outcome(),
                                DeclarationOutcome::Completed { .. }
                            ),
                            | Judgement::Synthesised => {
                                matches!(declaration.outcome(), DeclarationOutcome::Bodied { .. })
                            },
                            | Judgement::Owed => matches!(
                                declaration.outcome(),
                                DeclarationOutcome::Uncompleted { .. }
                            ),
                            | Judgement::Suspended => matches!(
                                declaration.outcome(),
                                DeclarationOutcome::Completed { .. } | DeclarationOutcome::Bodied { .. }
                            ),
                            | Judgement::Mismatched | Judgement::Refused => true,
                            | Judgement::Declared => matches!(
                                declaration.outcome(),
                                DeclarationOutcome::Abstract(_) | DeclarationOutcome::Data(_)
                            ),
                        }
                    },
                    | _ => false,
                })
                && actual.next().is_none()
        },
    )]
fn verdicts(lowered: &mut Lowered<'_>) -> Vec<(ConstantIndex, Judgement)>
{
    report(lowered)
        .judged()
        .iter()
        .map(|judged| {
            let judgement = match judged.verdict() {
                Verdict::Data => Judgement::Declared,
                Verdict::Checked { .. } => Judgement::Checked,
                Verdict::Synthesised { .. } => Judgement::Synthesised,
                Verdict::Owed(_) => Judgement::Owed,
                Verdict::Suspended(_) => Judgement::Suspended,
                Verdict::Refused(CheckRefusal::TypeMismatch(_)) => Judgement::Mismatched,
                Verdict::Refused(_) => Judgement::Refused,
            };
            (judged.constant(), judgement)
        })
        .collect()
}

/// One expected judgement.
///
/// # Specification
/// trivial.
fn judged<Position>(
    position: Position,
    judgement: Judgement,
) -> (ConstantIndex, Judgement)
where
    Position: Into<ConstantIndex>,
{
    (position.into(), judgement)
}

/// The bytes of the `occurrence`th appearance, counting from zero, of
/// `needle` in `source`.
///
/// # Specification
/// - requires: the requested nonoverlapping occurrence of the needle exists.
/// - ensures: the returned source slice is exactly the needle at that
///   occurrence.
/// - provides: an independent lexical location oracle.
/// - fails: none when the occurrence exists.
/// - panics: when the requested occurrence is absent.
///
/// # Adequacy
/// - hypothesis: L3 — repeated member names distinguish the later fault’s span
///   from the earlier declaration it conflicts with.
/// - witness: `tests::modules::duplicate_module_member_definition_is_rejected`
/// - witness: `tests::modules::signatures_attach_to_their_defs`
#[spec(
        ensures: |ret| {
            source
                .as_ref()
                .get(usize::from(ret.start()) .. usize::from(ret.end()))
                == Some(needle.as_ref())
        },
    )]
fn span_of<Source, Needle, Occurrence>(
    source: Source,
    needle: Needle,
    occurrence: Occurrence,
) -> ByteSpan
where
    Source: AsRef<str>,
    Needle: AsRef<str>,
    Occurrence: Into<usize>,
{
    let (source, needle, occurrence) = (source.as_ref(), needle.as_ref(), occurrence.into());
    let (start, _) = source
        .match_indices(needle)
        .nth(occurrence)
        .unwrap_or_else(|| panic!("`{needle}` appears {occurrence} times over"));
    let end = start
        .checked_add(needle.len())
        .expect("the appearance ends inside the source");
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("the span is ordered")
}

/// The bytes of the last segment of the first path in `source` written
/// `written`: the name a selection selects.
///
/// # Specification
/// - requires: the dotted spelling occurs in the source and has a final
///   segment.
/// - ensures: the final segment of the first occurrence, ending where the
///   complete spelling ends.
/// - provides: an independent location oracle for governed selections.
/// - fails: none for a present dotted spelling.
/// - panics: when the spelling is absent or has no period.
///
/// # Adequacy
/// - hypothesis: L3 — nested selections distinguish the selected member’s span
///   from the whole path and its governing prefix.
/// - witness: `tests::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
/// - witness: `tests::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
#[spec(
        ensures: |ret| {
            written
                .as_ref()
                .rsplit_once('.')
                .is_some_and(|(_prefix, member)| {
                    source
                        .as_ref()
                        .get(usize::from(ret.start()) .. usize::from(ret.end()))
                        == Some(member)
                        && Some(usize::from(ret.end()))
                            == source
                                .as_ref()
                                .find(written.as_ref())
                                .and_then(|start| start.checked_add(written.as_ref().len()))
                })
        },
    )]
fn selected<Source, Written>(
    source: Source,
    written: Written,
) -> ByteSpan
where
    Source: AsRef<str>,
    Written: AsRef<str>,
{
    let (source, written) = (source.as_ref(), written.as_ref());
    let at = source.find(written).expect("the path is written");
    let end = at
        .checked_add(written.len())
        .expect("the path ends inside the source");
    let (_, member) = written.rsplit_once('.').expect("the path selects");
    let start = end
        .checked_sub(member.len())
        .expect("the member ends the path");
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("the span is ordered")
}

/// The empty span at byte `at`.
///
/// # Specification
/// trivial.
fn gap<At>(at: At) -> ByteSpan
where
    At: Into<ByteOffset>,
{
    let at = at.into();
    ByteSpan::new(at, at).expect("the span is ordered")
}

/// The name spelled `text`.
///
/// # Specification
/// trivial.
fn name<'text, Text>(text: Text) -> SurfaceName<'text>
where
    Text: Into<SurfaceName<'text>>,
{
    text.into()
}

/// The path `text` renders as.
///
/// # Specification
/// trivial.
fn path<Text>(text: Text) -> NamePath
where
    Text: Into<DottedName<'static>>,
{
    NamePath::from(text.into())
}

#[test]
fn modules_lower_to_named_member_declarations()
{
    let source = "module Config {\n  def first = 0;\n  module limits { module hard { module \
                      detail { def note = 1; } } }\n  def after = 2;\n}\ndef top = \
                      Config.limits.hard.detail.note;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Config.first", Role::Declared, Amounts::Bodied),
            row(
                "Config.limits.hard.detail.note",
                Role::Declared,
                Amounts::Bodied
            ),
            row("Config.after", Role::Declared, Amounts::Bodied),
            row("top", Role::Declared, Amounts::Bodied),
        ],
        "the nested member is one declaration, admitted in source order after its siblings"
    );
    assert_eq!(
        declaration(&lowered, "Config.limits.hard.detail.note", Role::Declared).constant(),
        ConstantIndex::from(1_usize),
        "the member takes the position after the sibling written before it"
    );
    assert_eq!(
        constant_read_by(&lowered, "top"),
        ConstantIndex::from(1_usize),
        "a path to it reads that position"
    );

    let names = lowered.module.structured_names();
    let report = report(&mut lowered);
    let readmission = bridge::readmit(&mut lowered.arena, &report);
    let artifact = decode(readmission.export(names).as_image()).expect("the export decodes");
    let exported: Vec<(Vec<String>, Option<KernelValue>)> = artifact
        .declarations()
        .iter()
        .map(|marked| {
            let body = match *marked.declaration().content() {
                DeclarationContent::Def { body, .. } => artifact.arena().value(body).cloned(),
                DeclarationContent::Axiom { .. }
                | DeclarationContent::Data { .. }
                | DeclarationContent::Codata { .. }
                | DeclarationContent::AbstractType { .. } => None,
            };
            let segments = marked
                .declaration()
                .name()
                .segments()
                .iter()
                .map(|segment| String::from(segment.as_ref()))
                .collect();
            (segments, body)
        })
        .collect();
    let named = |segments: &[&str]| {
        segments
            .iter()
            .map(|&segment| String::from(segment))
            .collect::<Vec<String>>()
    };
    assert_eq!(
        exported
            .iter()
            .map(|declaration| declaration.0.clone())
            .collect::<Vec<Vec<String>>>(),
        [
            named(&["Config", "first"]),
            named(&["Config", "limits", "hard", "detail", "note"]),
            named(&["Config", "after"]),
            named(&["top"]),
        ],
        "each declaration crosses under its own segments, five for the nested member"
    );
    assert_eq!(
        exported
            .last()
            .and_then(|declaration| declaration.1.clone()),
        Some(KernelValue::Constant(ConstantIndex::from(1_usize))),
        "and the reference reads the member's kernel position, never its name"
    );
}

#[test]
fn module_members_admit_in_source_order()
{
    let source = "module M { def a = 1; module n { def b = a; } def c = a; }\ndef d = M.n.b;";
    let mut lowered = lower(source);
    let positions: Vec<(String, ConstantIndex)> = lowered
        .module
        .declarations()
        .iter()
        .map(|declaration| (dotted(&lowered.module, declaration), declaration.constant()))
        .collect();
    assert_eq!(
        positions,
        [
            (String::from("M.a"), ConstantIndex::from(0_usize)),
            (String::from("M.n.b"), ConstantIndex::from(1_usize)),
            (String::from("M.c"), ConstantIndex::from(2_usize)),
            (String::from("d"), ConstantIndex::from(3_usize)),
        ],
        "members take positions in source order, a nested member between its parent's"
    );
    assert_eq!(
        [
            constant_read_by(&lowered, "M.n.b"),
            constant_read_by(&lowered, "M.c"),
            constant_read_by(&lowered, "d"),
        ],
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
        ],
        "a member reads an earlier member of its own or an enclosing module by position"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
            judged(2_usize, Judgement::Synthesised),
            judged(3_usize, Judgement::Synthesised),
        ],
        "and the checker reads each member as the declaration it is"
    );
}

#[test]
fn a_user_module_selection_is_governed_and_a_free_target_still_projects()
{
    let source = "module M { def field = 1; }\ndef use_field = M.field;\ndef free = 1;\ndef \
                      free_field = free.field;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.field", Role::Declared, Amounts::Bodied),
            row("use_field", Role::Declared, Amounts::Bodied),
            row("free", Role::Declared, Amounts::Bodied),
            row("free_field", Role::Declared, Amounts::Bodied),
        ],
        "the module selection resolves; a selection no module governs is the field of the \
             record its head holds, not a module refusal"
    );
    assert_eq!(
        constant_read_by(&lowered, "use_field"),
        ConstantIndex::from(0_usize),
        "the selection reads the member's position"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
            judged(2_usize, Judgement::Synthesised),
            judged(3_usize, Judgement::Refused),
        ],
        "the module selection checks, and the checker refuses a field of an integer"
    );
}

#[test]
fn nested_modules_lower_as_parent_members_and_project()
{
    let source = "module Outer : #{ inner: #{ answer: Integer } } { def outer_hidden = 1; \
                      module inner : #{ answer: Integer } { def inner_hidden = 2; def answer = \
                      42; } }\ndef use_answer = Outer.inner.answer;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Outer.outer_hidden", Role::Declared, Amounts::Bodied),
            row("Outer.inner.inner_hidden", Role::Declared, Amounts::Bodied),
            row("Outer.inner.answer", Role::Declared, Amounts::Completed),
            row("Outer.inner.answer", Role::Witness, Amounts::Completed),
            row("use_answer", Role::Declared, Amounts::Bodied),
        ],
        "the nested module's members are the parent's members, and the parent's \
             signature states the nested component's type a second time"
    );
    assert_eq!(
        strata(&lowered),
        [
            Stratum::new("Outer", Coerced(true)).module("inner"),
            Stratum::new("Outer.inner", Coerced(true)).value("answer", 2_usize),
        ],
        "each module exports exactly what its signature names"
    );
    assert_eq!(
        constant_read_by(&lowered, "use_answer"),
        ConstantIndex::from(2_usize),
        "the path through the nested module reads the member"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
            judged(2_usize, Judgement::Checked),
            judged(3_usize, Judgement::Checked),
            judged(4_usize, Judgement::Synthesised),
        ],
        "and every declaration checks"
    );
}

#[test]
fn deeply_nested_modules_lower_and_resolve_at_every_depth()
{
    let depth = 8_usize;
    let mut source = String::from("module Outer { def depth_outer = 0;");
    for level in 0_usize .. depth {
        write!(source, " module level{level} {{ def depth{level} = 0;")
            .expect("writing to a string never fails");
    }
    for _level in 0_usize .. depth {
        source.push_str(" }");
    }
    source.push_str(" }\ndef use_outer = Outer.depth_outer;\n");
    let mut prefix = String::from("Outer");
    for level in 0_usize .. depth {
        write!(prefix, ".level{level}").expect("writing to a string never fails");
        writeln!(source, "def use{level} = {prefix}.depth{level};")
            .expect("writing to a string never fails");
    }
    let mut lowered = lower(source.as_str());

    let strata = strata(&lowered);
    assert_eq!(strata.len(), depth + 1, "one stratum item per module");
    assert_eq!(
        strata
            .last()
            .map(|stratum| (stratum.path.clone(), stratum.values.clone())),
        Some((
            prefix.clone(),
            Vec::from([(format!("depth{}", depth - 1), ConstantIndex::from(depth))])
        )),
        "the innermost module is last, under the path of every enclosing module"
    );
    let innermost = format!("{prefix}.depth{}", depth - 1);
    assert_eq!(
        lowered
            .module
            .path_of(declaration(&lowered, &innermost, Role::Declared))
            .len(),
        depth + 2,
        "the innermost member's name has a segment per module and its own"
    );
    assert_eq!(
        constant_read_by(&lowered, "use_outer"),
        ConstantIndex::from(0_usize),
        "the outermost member resolves"
    );
    for level in 0_usize .. depth {
        assert_eq!(
            constant_read_by(&lowered, format!("use{level}")),
            ConstantIndex::from(level + 1),
            "the member at depth {level} resolves through its path"
        );
    }
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| judgement == Judgement::Synthesised),
        "and every declaration checks"
    );
}

/// #2687: a dotted name declares in the modules its prefix names, each opened
/// where the source declares none: a theory and a module written through one
/// prefix share its module, a path reads the module's member, and a model
/// reads the theory by its path.
#[test]
fn a_dotted_name_declares_in_the_modules_its_prefix_names_2687()
{
    let source = "theory Gandr.Shape {\n  oper label : String;\n}\nmodule Gandr.Tools {\n  def \
                  answer : Integer = 42;\n}\nmodule Shaped : Model(Gandr.Shape) {\n  def label : \
                  String = \"shaped\";\n}\ndef asked : Integer = Gandr.Tools.answer;\n";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Theory", Role::Declared, Amounts::Data),
            row("Gandr.Shape", Role::Declared, Amounts::Completed),
            row("Gandr.Tools.answer", Role::Declared, Amounts::Completed),
            row("Shaped.label", Role::Declared, Amounts::Completed),
            row("Shaped.label", Role::Witness, Amounts::Completed),
            row("asked", Role::Declared, Amounts::Completed),
        ],
        "the theory and the module stand in `Gandr`, the model at the top level"
    );
    assert_eq!(
        constant_read_by(&lowered, "asked"),
        ConstantIndex::from(2_usize),
        "the member resolves through the module the prefix opened"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Declared | Judgement::Checked | Judgement::Synthesised
        )),
        "and every declaration checks, the `Theory` code declared: {judgements:?}"
    );
}

/// #2687: a dotted name's prefix naming a module a form of its own writes is
/// refused at the segment, naming the module's own name.
#[test]
fn a_dotted_prefix_naming_a_written_module_is_refused_2687()
{
    let source = "module Gandr {\n  def x : Integer = 1;\n}\ntheory Gandr.Shape {\n  oper label \
                  : String;\n}\n";
    assert_eq!(
        rows(&lower(source)),
        [
            row("Gandr.x", Role::Declared, Amounts::Completed),
            row("Theory", Role::Declared, Amounts::Data),
            row(
                "Shape",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                    span: span_of(source, "Gandr", 1_usize),
                    name: name("Gandr"),
                    first: span_of(source, "Gandr", 0_usize),
                })
            ),
        ],
        "the theory is refused as `Gandr` defined twice, at the top level"
    );
}

#[test]
fn a_reordered_signature_matches_and_canonicalizes()
{
    let source =
        "module M : #{ second: Integer, first: Integer } { def first = 1; def second = 2; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.first", Role::Declared, Amounts::Completed),
            row("M.second", Role::Declared, Amounts::Completed),
        ],
        "the members are admitted in source order"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(true))
            .value("second", 1_usize)
            .value("first", 0_usize)],
        "and exported in signature order"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(1_usize, Judgement::Checked),
        ],
        "each checked at the type its component states"
    );
}

#[test]
fn a_missing_signature_component_is_rejected_at_the_signature()
{
    let source = "module M : #{ x: Integer, y: Integer, z: Integer } { def x = 1; def y = 2; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.x", Role::Declared, Amounts::Completed),
            row("M.y", Role::Declared, Amounts::Completed),
            row(
                "M.z",
                Role::Held,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: span_of(source, "z", 0_usize),
                    module: name("M"),
                    member: name("z"),
                })
            ),
        ],
        "the missing component is refused at the signature, naming the module and the \
             component"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(true))
            .value("x", 0_usize)
            .value("y", 1_usize)],
        "the components that are present are exported"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(1_usize, Judgement::Checked),
        ],
        "and check"
    );
}

#[test]
fn a_nonempty_ascription_checks_each_component_at_its_member()
{
    let source = "module M : #{ x: Integer, y: String } { def x = 1; def y = 2; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.x", Role::Declared, Amounts::Completed),
            row("M.y", Role::Declared, Amounts::Completed),
        ],
        "each component's type becomes its member's signature"
    );
    assert_eq!(
        origin_of(&lowered, declared_type_of(&lowered, "M.y", Role::Declared)),
        span_of(source, "String", 0_usize),
        "the member is declared at the type its component wrote"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(1_usize, Judgement::Mismatched),
        ],
        "so the component that disagrees fails at its own member and the other checks"
    );
}

#[test]
fn a_manifest_type_component_expands_in_later_components()
{
    let source = "module M : #{ type T = Integer, value: T } { def value = 1; }\ndef used = \
                      M.value;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.value", Role::Declared, Amounts::Completed),
            row("used", Role::Declared, Amounts::Bodied),
        ],
        "the manifest component declares nothing of its own"
    );
    let structure = lowered
        .module
        .structures()
        .first()
        .expect("the module has a stratum item");
    let defined = match *structure.types() {
        [ref manifest] if manifest.name == name("T") => manifest.defined,
        ref other => panic!("one manifest component `T`, not {other:?}"),
    };
    assert_eq!(
        Maybe::Present(declared_type_of(&lowered, "M.value", Role::Declared)),
        defined,
        "the later component's `T` is the type the manifest component names"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(2_usize, Judgement::Synthesised),
        ],
        "and checks at it"
    );

    let earlier = "module M : #{ value: T, type T = Integer } { def value = 1; }";
    let refused = rows(&lower(earlier));
    assert!(
        matches!(
            refused.as_slice(),
            [(path, Role::Declared, Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                span,
                name: head,
                ..
            }))] if path == "M.value"
                && *span == span_of(earlier, "T", 0_usize)
                && *head == name("T")
        ),
        "a component sees only the manifest components written before it, got {refused:?}"
    );
}

#[test]
fn manifest_refusals_propagate_transitively_before_minting()
{
    let source = "module M : #{ type A = Missing, type B = A, value: B } { def value = unbound; }\ndef after = 2;";
    let lowered = lower(source);
    let fault = Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
        span: span_of(source, "Missing", 0_usize),
        name: name("Missing"),
        arity: gandr_surface_lowering::HeadArity::Nullary,
    });
    assert_eq!(
        rows(&lowered),
        [
            row("M.value", Role::Declared, fault),
            row("M.A", Role::Held, fault),
            row("M.B", Role::Held, fault),
            row("after", Role::Declared, Amounts::Bodied),
        ],
        "the earlier signature failure wins over the member's independent body failure"
    );
    let components = lowered.module.structures().first().expect("module").types();
    assert!(matches!(components, [first, second]
            if first.name == name("A") && second.name == name("B")
                && matches!(first.defined, Maybe::Absent(_))
                && matches!(second.defined, Maybe::Absent(_))));
}

#[test]
fn a_kinded_type_component_forms_at_its_classifier()
{
    let operator = "module M : #{ type Pair : Type -> Type, both : Pair(Integer) } { type \
                        Pair(a : Type) = a * a; def both = (1, 2); }";
    let mut lowered = lower(operator);
    assert_eq!(
        rows(&lowered),
        [
            row("M.both", Role::Declared, Amounts::Completed),
            row("M.Pair", Role::Witness, Amounts::Completed),
        ],
        "the family member reads the component, whose one declaration checks it at its kind"
    );
    let witness = declaration(&lowered, "M.Pair", Role::Witness);
    let DeclarationOutcome::Completed {
        declared_type,
        body,
    } = witness.outcome()
    else {
        panic!("the witness is a checked definition");
    };
    assert!(
        matches!(
            lowered.arena.value_type(declared_type),
            Some(&ValueType::StaticPi { .. })
        ),
        "the kind is the static arrow over its classifiers"
    );
    assert!(
        matches!(lowered.arena.value(body), Some(&Value::StaticLambda(code))
                if matches!(lowered.arena.value(code), Some(&Value::Quote(_)))),
        "and the member checks at it as the operator over its code"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked)
        ],
        "both the member, at the family applied, and the operator check"
    );

    let indexed = "module Indexed : #{ type Hom : Integer -> Integer } { type Hom(n : Integer) \
                       = Integer; }";
    let mut lowered = lower(indexed);
    assert_eq!(
        rows(&lowered),
        [row("Indexed.Hom", Role::Witness, Amounts::Completed)],
        "a kind over a type that classifies no codes still lowers"
    );
    let report = report(&mut lowered);
    assert!(
        matches!(
            report.judged(),
            [judged] if matches!(
                judged.verdict(),
                Verdict::Refused(CheckRefusal::StaticClassifierExpected { found, .. })
                    if lowered.arena.value_type(found) == Some(&ValueType::Base(BaseType::Integer))
            )
        ),
        "and the checker refuses it, naming the type that is no classifier: {:?}",
        report.judged()
    );

    let sealed = "module M :> #{ type Pair : Type -> Type } { type Pair(a : Type) = a * a; }";
    assert_eq!(
        rows(&lower(sealed)),
        [row(
            "M.Pair",
            Role::Abstract,
            Amounts::Refused(LoweringRefusal::UnreadAscription {
                span: span_of(sealed, "Pair", 0_usize),
                name: name("Pair"),
                form: AscriptionForm::Kinded,
            })
        )],
        "an opaque operator would be an atom at a kind no universe is, and is refused by name"
    );
    let represented = "module M :> #{ type Pair : Type -> Type } { type Pair = Integer; }";
    assert_eq!(
        rows(&lower(represented)),
        [row(
            "M.Pair",
            Role::Abstract,
            Amounts::Refused(LoweringRefusal::UnreadAscription {
                span: span_of(represented, "Pair", 0_usize),
                name: name("Pair"),
                form: AscriptionForm::Kinded,
            })
        )],
        "and so is one whose member is a plain type, which the operator would take as its \
             representation"
    );

    let manifest = "module M : #{ type Hom = Integer } { }";
    let lowered = lower(manifest);
    assert_eq!(rows(&lowered), [], "the manifest component is read");
    assert!(
        matches!(
            lowered.module.structures().first().map(LoweredStructure::types),
            Some([component]) if component.name == name("Hom")
                && matches!(component.defined, Maybe::Present(_))
        ),
        "and recorded with the type it names"
    );
}

#[test]
fn a_component_check_carries_its_members_expectation()
{
    let indexed = "module Indexed : #{ type Hom : Integer -> Integer } { @[ \
                       refuses(\"StaticClassifierExpected\") ] type Hom(n : Integer) = Integer; }";
    let lowered = lower(indexed);
    assert_eq!(
        rows(&lowered),
        [row("Indexed.Hom", Role::Witness, Amounts::Completed)],
        "the attributed member is read as the plain one is"
    );
    let witness = declaration(&lowered, "Indexed.Hom", Role::Witness);
    let Maybe::Present(key) = witness.signature()
    else {
        panic!("the family's witness carries its member's form as its expectation half");
    };
    assert!(
        matches!(lowered.module.attributes().entries(key), [entry]
                if entry.name().as_ref() == "refuses"
                    && entry.span() == span_of(indexed, "refuses(\"StaticClassifierExpected\")", 0_usize)),
        "and the member's attribute is filed under it"
    );

    let transparent = "module M : #{ type T : Type } { @[ checks ] type T = Integer; }";
    let lowered = lower(transparent);
    let witness = declaration(&lowered, "M.T", Role::Witness);
    assert!(
        matches!(witness.signature(), Maybe::Present(key)
                if matches!(lowered.module.attributes().entries(key), [entry]
                    if entry.name().as_ref() == "checks")),
        "a transparent component's witness reads its member's expectation too"
    );

    let unread = "module M { @[ checks ] type T = Integer; def x = 1; }";
    let found = rows(&lower(unread));
    assert!(
        found.contains(&row(
            "M.T",
            Role::Held,
            Amounts::Refused(LoweringRefusal::MalformedForm {
                span: span_of(unread, "checks", 0_usize),
                form: FormName::MODULE,
                fault: FormFault::MisplacedTile,
            })
        )),
        "an expectation no component's check reads, on a member that yields nothing, states \
             nothing, and the member is refused where it is written, got {found:?}"
    );
}

#[test]
fn a_type_member_s_refusal_is_reported_once_1087()
{
    let source = "module M : #{ count : Integer, type Q } {\n  def count = 3;\n  @[ checks ] type Q \
                  = Path(Integer, count, 3);\n}\n";
    let found = rows(&lower(source));
    let refused: Vec<Role> = found
        .iter()
        .filter(|&&(_, _, ref amounts)| matches!(*amounts, Amounts::Refused(_)))
        .map(|&(_, role, _)| role)
        .collect();
    assert_eq!(
        refused,
        [Role::Held],
        "the member refused under a transparent ascription is reported at the member, and the \
         component's witness, refused with it, yields nothing: {found:?}"
    );
}

#[test]
fn a_sealed_atom_reads_the_identity_its_type_member_states()
{
    let stated = |payload: &str| {
        format!(
            "def rel(a : Integer, b : Integer) -> -F Type {{ return Integer }}\ndef refl(a : \
             Integer) -> -F Integer {{ return 0 }}\ndef law = 0;\nmodule M :> #{{ type T, seed : \
             T }} {{ @[ identity({payload}) ] type T = Integer; def seed = 7; }}"
        )
    };
    for (payload, count) in [("(rel, refl, law)", 3_usize), ("(rel, refl)", 2_usize)] {
        let source = stated(payload);
        let lowered = lower(source.as_str());
        let atom = declaration(&lowered, "M.T", Role::Abstract);
        let named: Vec<Option<ConstantIndex>> = ["rel", "refl", "law"]
            .into_iter()
            .take(count)
            .map(|path| Some(declaration(&lowered, path, Role::Declared).constant()))
            .collect();
        let read: Vec<Option<ConstantIndex>> = lowered
            .module
            .interface(atom)
            .iter()
            .map(|&member| match lowered.arena.value(member) {
                Some(&Value::Constant(constant)) => Some(constant),
                Some(_) | None => None,
            })
            .collect();
        assert_eq!(
            read, named,
            "the atom reads the {count} declarations its member's `identity` names, in order"
        );
    }
    let plain = lower("module M :> #{ type T, seed : T } { type T = Integer; def seed = 7; }");
    assert!(
        plain
            .module
            .interface(declaration(&plain, "M.T", Role::Abstract))
            .is_empty(),
        "an atom whose member states no identity reads none"
    );
    let source = stated("(rel, refl, law, law)");
    let found = rows(&lower(source.as_str()));
    assert!(
        found.contains(&row(
            "M.T",
            Role::Abstract,
            Amounts::Refused(LoweringRefusal::IllTypedPayload {
                span: span_of(source.as_str(), "(rel, refl, law, law)", 0_usize),
                name: RegisteredAttribute::IDENTITY,
                expected: AttributeSchema::Interface,
                written: PayloadForm::OtherValue,
            })
        )),
        "four names are no interface, refused at the payload: {found:?}"
    );
}

#[test]
fn a_kinded_type_component_declares_an_abstract_member()
{
    let source = "module M :> #{ type Ob : Type, probe : Ob } { type Ob = Integer; def probe \
                      = 1; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.Ob", Role::Abstract, Amounts::Abstract),
            row("M.probe", Role::Declared, Amounts::Completed),
        ],
        "the kinded component declares one abstract member"
    );
    assert_eq!(
        lowered
            .arena
            .value_type(declared_type_of(&lowered, "M.probe", Role::Declared)),
        Some(&ValueType::Abstract(ConstantIndex::from(0_usize))),
        "the value component is typed at the abstract member, not at what its body infers"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Declared),
            judged(2_usize, Judgement::Checked)
        ],
        "and the body checks at it inside the seal"
    );
}

#[test]
fn a_kinded_type_component_spine_declares_its_arity()
{
    let source = "module M : #{ type Hom : Type -> Type -> Type, probe : Integer } { type \
                      Hom(a : Type, b : Type) = a * b; def probe = 1; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.probe", Role::Declared, Amounts::Completed),
            row("M.Hom", Role::Witness, Amounts::Completed),
        ],
        "the module carrying an arity-two kinded component lowers"
    );
    let DeclarationOutcome::Completed { body, .. } =
        declaration(&lowered, "M.Hom", Role::Witness).outcome()
    else {
        panic!("the witness is a checked definition");
    };
    assert!(
        matches!(lowered.arena.value(body), Some(&Value::StaticLambda(inner))
                if matches!(lowered.arena.value(inner), Some(&Value::StaticLambda(code))
                    if matches!(lowered.arena.value(code), Some(&Value::Quote(_))))),
        "the spine's two arrows are the operator's two parameters"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked)
        ],
        "and the operator checks at the spine"
    );

    let short = "module M : #{ type Hom : Type -> Type -> Type, probe : Integer } { type \
                     Hom(a : Type) = a; def probe = 1; }";
    assert_eq!(
        rows(&lower(short)),
        [
            row("M.probe", Role::Declared, Amounts::Completed),
            row(
                "M.Hom",
                Role::Held,
                Amounts::Refused(LoweringRefusal::FamilyTelescope {
                    span: span_of(short, "Hom", 1_usize),
                    name: name("Hom"),
                    fault: TelescopeFault::Arity {
                        stated: OperandCount::from(2_usize),
                        written: OperandCount::from(1_usize),
                    },
                })
            ),
        ],
        "a member of another arity is refused naming both counts, never truncated"
    );
}

/// #611: the parentheses written around a kind, or around a codomain of
/// its spine, only group; a kind in parentheses states what the kind
/// inside does.
#[test]
fn a_kind_reads_through_its_grouping_parentheses()
{
    for (kind, parameters) in [
        ("Type -> Type", "a : Type"),
        ("(Type -> Type)", "a : Type"),
        ("((Type -> Type))", "a : Type"),
        ("Type -> (Type -> Type)", "a : Type, b : Type"),
        ("(Type -> (Type -> Type))", "a : Type, b : Type"),
    ] {
        let source = format!(
            "module M : #{{ type Hom : {kind}, probe : Integer }} {{ type Hom({parameters}) = \
                 a; def probe = 1; }}"
        );
        let mut lowered = lower(source.as_str());
        assert_eq!(
            rows(&lowered),
            [
                row("M.probe", Role::Declared, Amounts::Completed),
                row("M.Hom", Role::Witness, Amounts::Completed),
            ],
            "`{kind}` states as many domains as `{parameters}` binds"
        );
        let judgements = verdicts(&mut lowered);
        assert!(
            judgements
                .iter()
                .all(|&(_, judgement)| judgement == Judgement::Checked),
            "and the operator checks at `{kind}`: {judgements:?}"
        );
    }

    let family = "module M : #{ type Hom : ((a : Integer, b : Integer) => Type) } { type \
                      Hom(a : Integer, b : Integer) = Integer; }";
    let mut lowered = lower(family);
    assert_eq!(
        rows(&lowered),
        [row("M.Hom", Role::Witness, Amounts::Completed)],
        "a family kind in parentheses states its telescope's two indices"
    );
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| judgement == Judgement::Checked),
        "which the checker admits"
    );
}

#[test]
fn a_manifest_family_component_binds_two_parameters()
{
    let source = "module M : #{ type Hom(a : Type, b : Type) = +U[ω] (a -> -F b), d : \
                      Integer } { def d = 1; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [row("M.d", Role::Declared, Amounts::Completed)],
        "the value component survives beside the parameterized type component"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(0_usize, Judgement::Checked)],
        "and checks"
    );

    let applied = "module M : #{ type Pair(a : Type, b : Type) = a * b, p : Pair(Integer, \
                       String) } { def p = (1, \"x\"); }";
    let mut lowered = lower(applied);
    assert_eq!(
        lowered
            .arena
            .value_type(declared_type_of(&lowered, "M.p", Role::Declared))
            .map(|stated| matches!(stated, ValueType::Product(parts) if parts.len() == 2_usize)),
        Some(true),
        "a later component applying the family reads its type over both arguments"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(0_usize, Judgement::Checked)],
        "which the member inhabits"
    );
}

#[test]
fn a_type_component_arity_mismatch_is_refused_by_name()
{
    let under = "module N : #{ type Hom(a : Type, b : Type) = +U[ω] (a -> -F b), bad : Hom } \
                     { def bad = 1; }";
    assert_eq!(
        rows(&lower(under)),
        [row(
            "N.bad",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::OutOfFragment {
                span: span_of(under, "Hom", 1_usize),
                form: FormName::from(NamedKind("type_identifier")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Arity(OperandCount::from(0_usize)),
            })
        )],
        "a family named with no arguments is refused, never read as an ambient atom"
    );

    let over = "module N : #{ type T = Integer, bad : T(Integer) } { def bad = 1; }";
    assert_eq!(
        rows(&lower(over)),
        [row(
            "N.bad",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                span: span_of(over, "T", 1_usize),
                name: name("T"),
                arity: gandr_surface_lowering::HeadArity::Unary,
            })
        )],
        "a nullary component given an argument is refused by its name and arity"
    );
}

#[test]
fn a_transparent_abstract_component_reads_its_type_member()
{
    let source = "module M : #{ type T, value: T } { type T = Integer; def value = 1; }\ndef \
                      used : M.T;\ndef used = M.value;\ndef wrong : M.T;\ndef wrong = \"text\";";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.value", Role::Declared, Amounts::Completed),
            row("M.T", Role::Witness, Amounts::Completed),
            row("used", Role::Declared, Amounts::Completed),
            row("wrong", Role::Declared, Amounts::Completed),
        ],
        "the component mints no atom: its one declaration checks the member's kind"
    );
    let structure = lowered
        .module
        .structures()
        .first()
        .expect("the module has a stratum item");
    let defined = match *structure.types() {
        [ref component] if component.name == name("T") => component.defined,
        ref other => panic!("one type component `T`, not {other:?}"),
    };
    assert!(
        structure.sealed().is_empty(),
        "a transparent ascription seals nothing"
    );
    for path in ["M.value", "used"] {
        assert_eq!(
            Maybe::Present(declared_type_of(&lowered, path, Role::Declared)),
            defined,
            "`{path}` is stated at the type the member names"
        );
    }
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked),
            judged(3_usize, Judgement::Checked),
            judged(4_usize, Judgement::Mismatched),
        ],
        "so the client reads the member's own type, and only a value of it checks"
    );
}

#[test]
fn an_abstract_component_kinds_at_a_universe()
{
    let kinded = "module M : #{ type T : Type[+, 0] } { type T = Integer; }";
    let mut lowered = lower(kinded);
    assert_eq!(
        rows(&lowered),
        [row("M.T", Role::Witness, Amounts::Completed)],
        "the written kind is checked by the component's one declaration"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(1_usize, Judgement::Checked)],
        "and the member's type inhabits it"
    );

    let classified = "module M : #{ type T : Integer } { type T = Integer; }";
    let mut lowered = lower(classified);
    assert_eq!(
        verdicts(&mut lowered),
        [judged(1_usize, Judgement::Mismatched)],
        "a kind that is no universe classifies no type"
    );

    let sealed = "module M :> #{ type T : Type[+, 0] } { type T = Integer; }";
    let mut lowered = lower(sealed);
    assert_eq!(
        rows(&lowered),
        [row("M.T", Role::Abstract, Amounts::Abstract)],
        "an opaque ascription declares the abstract type at the written kind"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(0_usize, Judgement::Declared)],
        "which the checker admits"
    );

    let unsorted = "module M :> #{ type T : Integer } { type T = Integer; }";
    let mut lowered = lower(unsorted);
    assert_eq!(
        verdicts(&mut lowered),
        [judged(0_usize, Judgement::Refused)],
        "and an abstract type at a kind that is no universe is refused"
    );
}

#[test]
fn an_abstract_component_with_no_type_member_is_refused_by_name()
{
    let unknown = |source: &'static str| {
        Amounts::Refused(LoweringRefusal::UnknownMember {
            span: span_of(source, "T", 0_usize),
            module: name("M"),
            member: name("T"),
        })
    };
    let transparent = "module M : #{ type T, value: Integer } { def value = 1; }";
    assert_eq!(
        rows(&lower(transparent)),
        [
            row("M.value", Role::Declared, Amounts::Completed),
            row("M.T", Role::Held, unknown(transparent)),
        ],
        "the component names a type member the body does not declare, and its sibling \
             is matched"
    );
    let sealed = "module M :> #{ type T, value: T } { def value = 1; }\ndef after = 2;";
    assert_eq!(
        rows(&lower(sealed)),
        [
            row("M.T", Role::Abstract, unknown(sealed)),
            row("M.value", Role::Declared, unknown(sealed)),
            row("after", Role::Declared, Amounts::Bodied),
        ],
        "an atom without a representation is refused, and so is every member stated at it"
    );
}

#[test]
fn a_repeated_type_member_is_refused_naming_the_first()
{
    let source = "module M { type T = Integer; type T = String; def value : T; def value = 1; }";
    let lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row(
                "M.T",
                Role::Held,
                Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                    span: span_of(source, "T", 1_usize),
                    name: name("T"),
                    first: span_of(source, "T", 0_usize),
                })
            ),
            row("M.value", Role::Declared, Amounts::Completed),
        ],
        "the second member is refused and the first still reads"
    );
}

#[test]
fn a_top_level_type_member_names_its_type_for_the_source_1834()
{
    let source = "type T = Integer; def value : T; def value = 1;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [row("value", Role::Declared, Amounts::Completed)],
        "a type member at the top level declares nothing of its own"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(1_usize, Judgement::Checked)],
        "and the declaration naming it checks at the type it names"
    );

    let mistyped = "type T = Integer; def value : T; def value = \"one\";";
    assert_eq!(
        verdicts(&mut lower(mistyped)),
        [judged(1_usize, Judgement::Mismatched)],
        "a value of another type is refused at it"
    );

    let repeated = "type T = Integer; type T = String; def value : T; def value = 1;";
    assert_eq!(
        rows(&lower(repeated)),
        [
            row(
                "T",
                Role::Held,
                Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                    span: span_of(repeated, "T", 1_usize),
                    name: name("T"),
                    first: span_of(repeated, "T", 0_usize),
                })
            ),
            row("value", Role::Declared, Amounts::Completed),
        ],
        "a second member of the name is refused and the first still reads"
    );

    let early = "def value : T; def value = 1; type T = Integer;";
    assert!(
        matches!(rows(&lower(early)).as_slice(), [(
            _,
            Role::Declared,
            Amounts::Refused(LoweringRefusal::UnresolvedTypeHead { .. })
        )]),
        "a declaration written before the member does not see it"
    );
}

#[test]
fn a_type_member_names_a_computation_type_3080()
{
    let source = "module M { type C = -F Integer; def one() -> C { return 1 } }\ntype D = -F \
                  Integer;\ndef two() -> D { return 2 }\nmodule Fam { type T(a : Type) = -F a; \
                  def some1() -> T(Integer) { return 1 } }\ntype G = Integer -> -F Integer;\ndef \
                  inc() -> G { fn (n) { return n } }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.one", Role::Declared, Amounts::Completed),
            row("two", Role::Declared, Amounts::Completed),
            row("Fam.some1", Role::Declared, Amounts::Completed),
            row("inc", Role::Declared, Amounts::Completed),
        ],
        "a returner, a family into returners and a function into one each lower as a member"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(3_usize, Judgement::Checked),
            judged(5_usize, Judgement::Checked),
            judged(7_usize, Judgement::Checked),
        ],
        "and each declaration naming one checks at the computation type it names"
    );
    assert!(
        matches!(
            *lowered.module.structures().first().expect("module").types(),
            [ref member] if member.name == name("C")
                && member.defined == Maybe::Absent(gandr_surface_lowering::manifest_type::Absent::Computation)
        ),
        "the module exports the member as a computation type, not as one that did not lower"
    );

    let mistyped = "type D = -F Integer;\ndef two() -> D { return \"two\" }";
    assert_eq!(
        verdicts(&mut lower(mistyped)),
        [judged(1_usize, Judgement::Mismatched)],
        "a body returning another type is refused at the member's computation type"
    );

    let misread = "type D = -F Integer;\ndef bad(x : D) -> -F Integer { return 1 }";
    assert!(
        matches!(
            rows(&lower(misread)).as_slice(),
            [(_, Role::Declared, Amounts::Refused(LoweringRefusal::OutOfFragment {
                span,
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
                ..
            }))] if *span == span_of(misread, "D", 1_usize)
        ),
        "a computation member named where a value type is read is refused at the name"
    );

    let sealed = "module S :> #{ type T, v : T } { type T = -F Integer; def v = 1; }";
    let representation = Amounts::Refused(LoweringRefusal::OutOfFragment {
        span: span_of(sealed, "-F Integer", 0_usize),
        form: FormName::from(NamedKind("f_type")),
        sort: FragmentSort::ValueType,
        boundary: FragmentBoundary::WrongSort,
    });
    assert_eq!(
        rows(&lower(sealed)),
        [
            row("S.T", Role::Abstract, representation),
            row("S.v", Role::Declared, representation),
        ],
        "a seal over a computation member is refused at its definition, and its atom's \
         readers with it"
    );

    let instance = "module Pt :> #{ type V, v : V } { type V = Integer; def v = 3; }\nmodule \
                    Mk(S : #{ type V, v : V }) { type K = -F S.V; def k() -> K { return S.v } \
                    }\nmodule I = Mk(Pt);\ndef through() -> I.K { I.k() }\ndef lie() -> I.K { \
                    return true }";
    let judgements = verdicts(&mut lower(instance));
    assert_eq!(
        judgements
            .iter()
            .rev()
            .take(2_usize)
            .map(|&(_, judgement)| judgement)
            .collect::<Vec<_>>(),
        [Judgement::Mismatched, Judgement::Checked],
        "an instance's computation member reads its template's renamed to the argument's \
         atom: the instance's run inhabits it and a boolean does not"
    );

    let argued = "module Q { type V = -F Integer; }\nmodule Mk(S : #{ type V }) { def one() -> \
                  Integer { 1 } }\nmodule J = Mk(Q);";
    assert!(
        rows(&lower(argued)).iter().any(|found| matches!(
            *found,
            (ref path, Role::Witness, Amounts::Refused(LoweringRefusal::OutOfFragment {
                span,
                boundary: FragmentBoundary::WrongSort,
                ..
            })) if path == "J.V" && span == span_of(argued, "-F Integer", 0_usize)
        )),
        "a computation member argued for a functor's abstract parameter refuses its witness"
    );
}

/// #3142: a family's body is expanded where it is applied and never checked
/// where it is written, so a parameter it passes to a data type answers at the
/// kind it is written with, in a module and at the top level; the same name in
/// a signature is judged there and keeps no such label.
#[test]
fn a_family_s_parameter_under_a_data_type_answers_at_its_kind_3142()
{
    let source = "data Maybe(a : Type) : Type {\n  None : Maybe(a);\n  Some : (x : a) --> \
                  Maybe(a);\n}\nmodule Loose { type R(a : Type) = Maybe(a); }\ntype Top(a : \
                  Type) = Maybe(a);\ndef g(a : Type, m : Maybe(a)) -> Integer { 0 }\n";
    let argument = |declared: &str| {
        let start = source.find(declared).expect("the family is written") + declared.len() - 2;
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(start + 1))
            .expect("one byte is a span")
    };
    let lowered = lower(source);
    let kinds: Vec<_> = lowered
        .module
        .origins()
        .labels()
        .iter()
        .filter_map(|label| match label.labelled {
            Labelled::Kind(kind) => Some((label.span, lowered.arena.value_type(kind).cloned())),
            Labelled::ValueType { .. }
            | Labelled::CompType { .. }
            | Labelled::Value(_)
            | Labelled::Endpoint(_)
            | Labelled::Bound(_)
            | Labelled::Branch { .. } => None,
        })
        .collect();
    let universe = Some(ValueType::Universe {
        sort: gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        level: gandr_kernel_strata::Level::zero(),
    });
    assert_eq!(
        kinds,
        [
            (argument("R(a : Type) = Maybe(a)"), universe.clone()),
            (argument("Top(a : Type) = Maybe(a)"), universe),
        ],
        "each `a` in a family's `Maybe(a)` answers at `Type`, and `g`'s at none"
    );
}

#[test]
fn a_type_member_is_named_only_after_it_is_written()
{
    let source = "module M { type T = Integer; def value : T; def value = 1; module N { def \
                      inner : T; def inner = 2; } }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.value", Role::Declared, Amounts::Completed),
            row("M.N.inner", Role::Declared, Amounts::Completed),
        ],
        "a type member declares nothing of its own"
    );
    let defined = match *lowered.module.structures().first().expect("module").types() {
        [ref member] if member.name == name("T") => member.defined,
        ref other => panic!("one exported type member `T`, not {other:?}"),
    };
    for path in ["M.value", "M.N.inner"] {
        assert_eq!(
            Maybe::Present(declared_type_of(&lowered, path, Role::Declared)),
            defined,
            "`{path}` reads the member by its bare name, in its module and a nested one"
        );
    }
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked),
        ],
        "and checks at it"
    );

    let early = "module M { def value : T; def value = 1; type T = Integer; }";
    assert_eq!(
        rows(&lower(early)),
        [row(
            "M.value",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                span: span_of(early, "T", 0_usize),
                name: name("T"),
                arity: gandr_surface_lowering::HeadArity::Nullary,
            })
        )],
        "a member written before the type member does not see it"
    );
}

#[test]
fn a_sealed_component_over_a_refused_member_is_refused_with_it()
{
    let source = "module M :> #{ type T, value: T } { type T = Missing; def value = 1; }\ndef \
                      client : M.T;\ndef client = M.value;\ndef after = 2;";
    let fault = Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
        span: span_of(source, "Missing", 0_usize),
        name: name("Missing"),
        arity: gandr_surface_lowering::HeadArity::Nullary,
    });
    assert_eq!(
        rows(&lower(source)),
        [
            row("M.T", Role::Abstract, fault),
            row("M.T", Role::Held, fault),
            row("M.value", Role::Declared, fault),
            row("client", Role::Declared, fault),
            row("after", Role::Declared, Amounts::Bodied),
        ],
        "the atom carries its representation's refusal to the members and the client"
    );
}

#[test]
fn a_module_path_is_governed_through_lowering_not_merely_registered()
{
    let source = "module Facts : #{ total: Integer } { def hidden = 1; def total = 2; module \
                      inner { def answer = 3; } }\ndef total_used = Facts.total;\ndef hidden_used = \
                      Facts.hidden;\ndef inner_used = Facts.inner;\ndef never_used = Facts.never;";
    let lowered = lower(source);
    let unknown = |written: &'static str, member: &'static str| {
        Amounts::Refused(LoweringRefusal::UnknownMember {
            span: selected(source, written),
            module: name("Facts"),
            member: name(member),
        })
    };
    assert_eq!(
        rows(&lowered),
        [
            row("Facts.hidden", Role::Declared, Amounts::Bodied),
            row("Facts.total", Role::Declared, Amounts::Completed),
            row("Facts.inner.answer", Role::Declared, Amounts::Bodied),
            row("total_used", Role::Declared, Amounts::Bodied),
            row(
                "hidden_used",
                Role::Declared,
                unknown("Facts.hidden", "hidden")
            ),
            row(
                "inner_used",
                Role::Declared,
                unknown("Facts.inner", "inner")
            ),
            row(
                "never_used",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "Facts.never"),
                    module: name("Facts"),
                    member: name("never"),
                })
            ),
        ],
        "the exported component resolves; the hidden member, the hidden nested module and \
             the undeclared component are refused by name"
    );
    assert_eq!(
        constant_read_by(&lowered, "total_used"),
        ConstantIndex::from(1_usize),
        "the exported component reads its member"
    );
}

#[test]
fn a_deep_module_path_is_governed_at_the_depth_that_binds_it()
{
    let source = "module Facts { module inner { module core { def answer = 3; } } }\ndef \
                      answer_used = Facts.inner.core.answer;\ndef missing_used = \
                      Facts.inner.core.missing;\ndef nowhere_used = Facts.nowhere.core.answer;";
    let lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Facts.inner.core.answer", Role::Declared, Amounts::Bodied),
            row("answer_used", Role::Declared, Amounts::Bodied),
            row(
                "missing_used",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "Facts.inner.core.missing"),
                    module: name("Facts.inner.core"),
                    member: name("missing"),
                })
            ),
            row(
                "nowhere_used",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "Facts.nowhere"),
                    module: name("Facts"),
                    member: name("nowhere"),
                })
            ),
        ],
        "the refusal names the module that governs the absent segment, at its own depth"
    );
    assert_eq!(
        constant_read_by(&lowered, "answer_used"),
        ConstantIndex::from(0_usize),
        "and the complete path reads the member"
    );
}

#[test]
fn a_module_namespace_is_not_a_projectable_record()
{
    let source = "module M { def x = 1; module inner { def y = 2; } }\ndef known = M.x;\ndef \
                      unknown = M.nonesuch;\ndef whole = M.inner;";
    let lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.x", Role::Declared, Amounts::Bodied),
            row("M.inner.y", Role::Declared, Amounts::Bodied),
            row("known", Role::Declared, Amounts::Bodied),
            row(
                "unknown",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "M.nonesuch"),
                    module: name("M"),
                    member: name("nonesuch"),
                })
            ),
            row(
                "whole",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::OutOfFragment {
                    span: span_of(source, "M.inner", 0_usize),
                    form: FormName::from(NamedKind("projection_expression")),
                    sort: FragmentSort::Value,
                    boundary: FragmentBoundary::WrongSort,
                })
            ),
        ],
        "a known member selects; an unknown one is refused as no member, and a module is \
             not a value to select from or to stand alone"
    );
    assert_eq!(
        constant_read_by(&lowered, "known"),
        ConstantIndex::from(0_usize),
        "the known member reads its position"
    );
}

#[test]
fn a_hidden_or_absent_user_module_component_is_declined_as_a_hole()
{
    let source = "module Facts : #{ total: Integer } { def hidden = 1; def total = 2; }\ndef \
                      total_used = Facts.total;\ndef hidden_used = Facts.hidden;\ndef never_used = \
                      Facts.never;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Facts.hidden", Role::Declared, Amounts::Bodied),
            row("Facts.total", Role::Declared, Amounts::Completed),
            row("total_used", Role::Declared, Amounts::Bodied),
            row(
                "hidden_used",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "Facts.hidden"),
                    module: name("Facts"),
                    member: name("hidden"),
                })
            ),
            row(
                "never_used",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "Facts.never"),
                    module: name("Facts"),
                    member: name("never"),
                })
            ),
        ],
        "a hidden and an absent component are each refused by name"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Synthesised),
        ],
        "and the component that is exported checks"
    );
}

#[test]
fn module_signature_matching_hides_extra_members()
{
    let source = "module M : #{ visible: Integer } { def hidden = 1; def visible = 2; }\ndef \
                      shown = M.visible;\ndef hid = M.hidden;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.hidden", Role::Declared, Amounts::Bodied),
            row("M.visible", Role::Declared, Amounts::Completed),
            row("shown", Role::Declared, Amounts::Bodied),
            row(
                "hid",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: selected(source, "M.hidden"),
                    module: name("M"),
                    member: name("hidden"),
                })
            ),
        ],
        "the member the signature omits is admitted and cannot be named from outside"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(true)).value("visible", 1_usize)],
        "the module exports only what its signature names"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Synthesised),
        ],
        "and the hidden member is still checked"
    );
}

#[test]
fn a_hidden_member_is_admitted_and_absent_from_the_namespace()
{
    let source = "module M : #{ visible: Integer } { def hidden = 1; def visible = hidden; }";
    let mut lowered = lower(source);
    assert_eq!(
        lowered
            .module
            .recognition()
            .resolve_path(&path("M.visible")),
        PathResolution::Complete(Recognized::ModuleComponent),
        "the exported member is in the module's namespace"
    );
    assert_eq!(
        lowered.module.recognition().resolve_path(&path("M.hidden")),
        PathResolution::UnknownMember {
            depth: SegmentCount::from(1_usize),
            namespace: Recognized::ModuleNamespace,
        },
        "the hidden member is not"
    );
    assert_eq!(
        constant_read_by(&lowered, "M.visible"),
        ConstantIndex::from(0_usize),
        "yet it is admitted, and a sibling reads it by position"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Checked),
        ],
        "and both check"
    );
}

#[test]
fn nested_member_signature_constrains_the_parent_binding()
{
    let source = "module Outer { def inner : #{ answer: Integer }; module inner : #{ answer: \
                      String } { def answer = \"wrong\"; } }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Outer.inner.answer", Role::Declared, Amounts::Completed),
            row("Outer.inner.answer", Role::Witness, Amounts::Completed),
        ],
        "the member signature states the nested component's type a second time"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Mismatched),
        ],
        "and the member that does not have it is refused"
    );

    let agreeing = "module Outer { def inner : #{ answer: Integer }; module inner : #{ \
                        answer: Integer } { def answer = 1; } }";
    assert_eq!(
        verdicts(&mut lower(agreeing)),
        [
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked),
        ],
        "a member signature that agrees checks"
    );
}

#[test]
fn a_nested_module_stated_at_a_non_record_type_is_the_wrong_sort()
{
    let found = rows(&lower(
        "module Outer : #{ inner: Integer } { module inner { def answer = 1; } }",
    ));
    assert!(
        found.iter().any(|&(_, _, ref amounts)| matches!(
            amounts,
            Amounts::Refused(LoweringRefusal::OutOfFragment {
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
                ..
            })
        )),
        "a module is stated only by a record of its components: {found:?}"
    );

    let deep = "module Outer : #{ inner: #{ deep: #{ x: Integer } } } { module inner { module \
                    deep { def x = 1; } } }";
    let found = rows(&lower(deep));
    assert!(
        !found
            .iter()
            .any(|&(_, _, ref amounts)| matches!(amounts, Amounts::Refused(_))),
        "a record stating a module nested two deep is read through each layer: {found:?}"
    );
    let found = rows(&lower(
        "module Outer : #{ inner: #{ deep: Integer } } { module inner { module deep { def x \
             = 1; } } }",
    ));
    assert!(
        found.iter().any(|&(_, _, ref amounts)| matches!(
            amounts,
            Amounts::Refused(LoweringRefusal::OutOfFragment {
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
                ..
            })
        )),
        "and at each layer only by a record: {found:?}"
    );
}

#[test]
fn member_signature_attaches_and_wins_over_derived_function_type()
{
    let source = "module M { def f : +U (Integer -> -F Integer); def f(x : Integer) -> -F \
                      Integer { return x } }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.f", Role::Declared, Amounts::Completed),
            row("M.f", Role::Witness, Amounts::Completed),
        ],
        "the written signature and the function are one member, its derived type a witness"
    );
    assert_eq!(
        origin_of(&lowered, declared_type_of(&lowered, "M.f", Role::Declared)),
        span_of(source, "+U (Integer -> -F Integer)", 0_usize),
        "the member is declared at the written signature"
    );
    assert_ne!(
        origin_of(&lowered, declared_type_of(&lowered, "M.f", Role::Witness)),
        span_of(source, "+U (Integer -> -F Integer)", 0_usize),
        "and the derived type is the witness's"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(1_usize, Judgement::Checked),
        ],
        "both check"
    );
}

#[test]
fn signatures_attach_to_their_defs()
{
    let source = "def answer : Integer;\ndef answer = 42;\ndef f : +U (Integer -> -F \
                      Integer);\ndef f(x : Integer) -> -F Integer { return x }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("answer", Role::Declared, Amounts::Completed),
            row("f", Role::Declared, Amounts::Completed),
            row("f", Role::Witness, Amounts::Completed),
        ],
        "each signature attaches to its definition"
    );
    assert_eq!(
        origin_of(
            &lowered,
            declared_type_of(&lowered, "answer", Role::Declared)
        ),
        span_of(source, "Integer", 0_usize),
        "the value's declared type is its signature's"
    );
    assert_eq!(
        origin_of(&lowered, declared_type_of(&lowered, "f", Role::Declared)),
        span_of(source, "+U (Integer -> -F Integer)", 0_usize),
        "and the function's explicit signature wins over its derived type"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Checked),
            judged(1_usize, Judgement::Checked),
            judged(2_usize, Judgement::Checked),
        ],
        "every declaration checks"
    );
}

#[test]
fn computation_signed_module_member_origin_mirrors_ascription_encoding()
{
    let member = "module M { def x : -F Integer; def x = pure 1; }";
    let top = "def x : -F Integer;\ndef x = pure 1;";
    let refusal = |source| {
        Amounts::Refused(LoweringRefusal::OutOfFragment {
            span: span_of(source, "-F Integer", 0_usize),
            form: FormName::from(NamedKind("f_type")),
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::WrongSort,
        })
    };
    let member_lowered = lower(member);
    let top_lowered = lower(top);
    assert_eq!(
        rows(&member_lowered),
        [row("M.x", Role::Declared, refusal(member))],
        "a member signed at a computation type is refused at its signature"
    );
    assert_eq!(
        rows(&top_lowered),
        [row("x", Role::Declared, refusal(top))],
        "exactly as the same declaration at the top level is"
    );
    let origin = |lowered: &Lowered<'_>, path: &str| {
        let token = declaration(lowered, path, Role::Declared).origin();
        match lowered.module.origins().declaration(token) {
            Maybe::Present(origin) => origin.span(),
            Maybe::Absent(absent) => panic!("the declaration has an origin, not {absent:?}"),
        }
    };
    assert_eq!(
        (origin(&member_lowered, "M.x"), origin(&top_lowered, "x")),
        (
            span_of(member, "def x : -F Integer;", 0_usize),
            span_of(top, "def x : -F Integer;", 0_usize),
        ),
        "and both are located at the signature that introduced the name"
    );
}

#[test]
fn a_later_seal_leaves_an_earlier_extent()
{
    let extent = |source: &str| {
        let lowered = lower(source);
        match lowered
            .module
            .declarations()
            .iter()
            .next()
            .map(LoweredDeclaration::outcome)
        {
            Some(DeclarationOutcome::Abstract(sealing)) => usize::from(sealing.extent),
            other => panic!("the first declaration is the abstract type: {other:?}"),
        }
    };
    let alone = "module Counter :> #{ type T, seed : T } { type T = Integer ; def seed = 7 ; }";
    let followed = "module Counter :> #{ type T, seed : T } { type T = Integer ; def seed = 7 ; \
                        }\nmodule Other :> #{ type U, one : U } { type U = Integer ; def one = 1 ; }";
    assert_eq!(
        extent(followed),
        extent(alone),
        "sealing a later module leaves the earlier module's seal where its own last member \
             put it"
    );
}

#[test]
fn opaque_ascription_seals()
{
    let source = "module Counter :> #{ type T, seed : T } { type T = Integer ; def seed = 7 ; \
                      }\ndef held : Counter.T ;\ndef held = Counter.seed ;\ndef n : Integer ;\ndef \
                      n = Counter.seed ;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Counter.T", Role::Abstract, Amounts::Abstract),
            row("Counter.seed", Role::Declared, Amounts::Completed),
            row("held", Role::Declared, Amounts::Completed),
            row("n", Role::Declared, Amounts::Completed),
        ],
        "the abstract component declares one abstract type, admitted before the members"
    );
    let structure = lowered
        .module
        .structures()
        .first()
        .expect("the module has a stratum item");
    assert!(
        matches!(*structure.sealed(), [component] if component.name == name("T")
                && component.atom == ConstantIndex::from(0_usize)),
        "the module exports its component as the atom: {:?}",
        structure.sealed()
    );
    assert!(structure.types().is_empty(), "and no type of its own");
    assert_eq!(
        lowered
            .module
            .structured_names()
            .get(&ConstantIndex::from(0_usize))
            .map(|path| path
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect::<Vec<&str>>()),
        Some(vec!["Counter", "T"]),
        "the atom is exported under its component's path"
    );
    let atom = ValueType::Abstract(ConstantIndex::from(0_usize));
    for path in ["Counter.seed", "held"] {
        assert_eq!(
            lowered
                .arena
                .value_type(declared_type_of(&lowered, path, Role::Declared)),
            Some(&atom),
            "`{path}` is stated at the atom"
        );
    }
    let Some(DeclarationOutcome::Abstract(sealing)) = lowered
        .module
        .declarations()
        .iter()
        .next()
        .map(LoweredDeclaration::outcome)
    else {
        panic!("the first declaration is the abstract type");
    };
    assert_eq!(
        (
            lowered.arena.value_type(sealing.representation),
            lowered.arena.value_type(sealing.kind),
            usize::from(sealing.extent),
            usize::from(sealing.sealing),
            usize::from(sealing.component),
        ),
        (
            Some(&ValueType::Base(BaseType::Integer)),
            Some(&ValueType::Universe {
                sort: gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
                level: gandr_kernel_strata::Level::constant(
                    gandr_kernel_strata::LevelConstant::ZERO
                ),
            }),
            2_usize,
            0_usize,
            0_usize,
        ),
        "its representation is the member, its kind the fuss-free universe, its seal \
             reaches the module's last member, and its site is the first module's first \
             component"
    );
    let report = report(&mut lowered);
    let judgements: Vec<(usize, bool)> = report
        .judged()
        .iter()
        .map(|judged| {
            (
                usize::from(judged.constant()),
                matches!(judged.verdict(), Verdict::Data | Verdict::Checked { .. }),
            )
        })
        .collect();
    assert_eq!(
        judgements,
        [
            (0_usize, true),
            (2_usize, true),
            (3_usize, true),
            (4_usize, false)
        ],
        "the member checks at the representation inside, a client at the atom outside, \
             and the atom is not its representation outside"
    );
    let leak = report
        .judged()
        .iter()
        .find(|judged| judged.constant() == ConstantIndex::from(4_usize))
        .map(gandr_core_checker::Judged::verdict);
    let Some(Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { synthesised, .. }))) =
        leak
    else {
        panic!("the leak is a type mismatch, not {leak:?}");
    };
    assert_eq!(
        lowered.arena.value_type(synthesised),
        Some(&atom),
        "naming the atom it found"
    );

    let early = "def early : Counter.T ;\ndef early = 1 ;\nmodule Counter :> #{ type T } { \
                     type T = Integer ; }";
    assert_eq!(
        rows(&lower(early)),
        [
            row(
                "early",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::ForwardMemberReference {
                    span: span_of(early, "Counter.T", 0_usize),
                    name: name("T"),
                    declared: span_of(early, "T", 1_usize),
                })
            ),
            row("Counter.T", Role::Abstract, Amounts::Abstract),
        ],
        "a declaration before the module does not read its atom"
    );
}

#[test]
fn a_signed_member_of_a_sealed_module_exports_its_witness()
{
    let source = "module Counter :> #{ type T, seed : T } { type T = Integer ; def seed : \
                      Integer ; def seed = 7 ; }\ndef held : Counter.T ;\ndef held = Counter.seed ;";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("Counter.T", Role::Abstract, Amounts::Abstract),
            row("Counter.seed", Role::Declared, Amounts::Completed),
            row("Counter.seed", Role::Witness, Amounts::Completed),
            row("held", Role::Declared, Amounts::Completed),
        ],
        "the member keeps its own type and a witness states the component's"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("Counter", Coerced(true)).value("seed", 3_usize)],
        "the module exports the witness in the member's place"
    );
    assert_eq!(
        constant_read_by(&lowered, "held"),
        ConstantIndex::from(3_usize),
        "so a client reads the member at the atom"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Declared),
            judged(2_usize, Judgement::Checked),
            judged(3_usize, Judgement::Checked),
            judged(4_usize, Judgement::Checked),
        ],
        "and every declaration checks"
    );
}

#[test]
fn a_qualified_type_reference_resolves_through_the_namespace()
{
    let source = "module Shapes { type Side = Integer ; module Inner { type Label = String ; } \
                      }\nmodule Box : #{ type Item = Integer, item : Item } { def item = 1 ; \
                      }\ndef side : Shapes.Side ;\ndef side = 3 ;\ndef label : Shapes.Inner.Label \
                      ;\ndef label = \"l\" ;\ndef boxed : Box.Item ;\ndef boxed = Box.item ;";
    let mut lowered = lower(source);
    let expected = [
        ("side", BaseType::Integer),
        ("label", BaseType::String),
        ("boxed", BaseType::Integer),
    ];
    for (path, base) in expected {
        assert_eq!(
            lowered
                .arena
                .value_type(declared_type_of(&lowered, path, Role::Declared)),
            Some(&ValueType::Base(base)),
            "`{path}` reads the type its path names"
        );
    }
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| judgement == Judgement::Checked),
        "and every declaration checks at it"
    );
}

#[test]
fn an_unbound_type_path_is_refused_by_name()
{
    let source = "module Shapes :> #{ side : Integer } { type Hidden = Integer ; def side = 1 \
                      ; }\ndef corner : Shapes.Corner ;\ndef hidden : Shapes.Hidden ;\ndef \
                      stranger : Nowhere.Side ;";
    let unknown = |member: &'static str| {
        Amounts::Refused(LoweringRefusal::UnknownMember {
            span: selected(source, format!("Shapes.{member}")),
            module: name("Shapes"),
            member: name(member),
        })
    };
    assert_eq!(
        rows(&lower(source)),
        [
            row("Shapes.side", Role::Declared, Amounts::Completed),
            row("corner", Role::Declared, unknown("Corner")),
            row("hidden", Role::Declared, unknown("Hidden")),
            row(
                "stranger",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                    span: span_of(source, "Nowhere", 0_usize),
                    name: name("Nowhere"),
                    arity: gandr_surface_lowering::HeadArity::Nullary,
                })
            ),
        ],
        "a type the module does not export, one its seal hides and a path no module \
             governs are each refused by name"
    );
}

#[test]
fn duplicate_module_member_definition_is_rejected()
{
    let source = "module M { def x = 1; def x = 2; }";
    assert_eq!(
        rows(&lower(source)),
        [row(
            "M.x",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                span: span_of(source, "def x = 2;", 0_usize),
                name: name("x"),
                first: span_of(source, "def x = 1;", 0_usize),
            })
        )],
        "the second definition is refused, naming the first"
    );
}

#[test]
fn a_module_opened_twice_in_one_container_is_refused()
{
    let opened = "module M { module n { def a = 1; } module n { def b = 2; } }";
    let rows_of = rows(&lower(opened));
    assert!(
        rows_of.iter().any(|&(_, _, ref amounts)| matches!(
            *amounts,
            Amounts::Refused(LoweringRefusal::DuplicateDefinition { name: refused, .. })
                if refused == name("n")
        )),
        "the second module named `n` is refused: {rows_of:?}"
    );
}

#[test]
fn a_dangling_member_signature_is_an_obligation()
{
    let source = "module M : #{} { def missing : Integer; }";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [row("M.missing", Role::Declared, Amounts::Uncompleted)],
        "a member signature without a definition is uncompleted"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(0_usize, Judgement::Owed)],
        "and owed"
    );
}

#[test]
fn a_malformed_member_is_repaired_and_its_siblings_kept()
{
    let source = "module M { def broken = ; def ok = 2; }";
    let mut lowered = lower(source);
    let unwritten = source.find("= ;").expect("the gap is written") + 1;
    assert_eq!(
        rows(&lowered),
        [
            row(
                "M.broken",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::MalformedForm {
                    span: gap(unwritten),
                    form: FormName::from(NamedKind("def_value")),
                    fault: FormFault::MissingOperand,
                })
            ),
            row("M.ok", Role::Declared, Amounts::Bodied),
        ],
        "the malformed member is refused at its gap and its sibling is kept"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [judged(1_usize, Judgement::Synthesised)],
        "and checks"
    );
}

/// #2484: a member definition with its `def` misspelt is refused at the word
/// and held under the name it declares, inside the module, so a signature of
/// that name beside it owes its body because of that refusal; a member that
/// misspells nothing is still refused under its module.
#[test]
fn a_member_definition_misspelt_is_held_under_its_name_2484()
{
    let refused = |source: &'static str| -> Vec<(String, LoweringRefusal<'static>)> {
        rows(&repaired(source))
            .into_iter()
            .filter_map(|(name, _, amounts)| match amounts {
                Amounts::Refused(refusal) => Some((name, refusal)),
                Amounts::Completed
                | Amounts::Uncompleted
                | Amounts::Bodied
                | Amounts::Data
                | Amounts::Codata
                | Amounts::Abstract
                | Amounts::World => None,
            })
            .collect()
    };
    let source = "module Counts {\n  def zero : Integer ;\n  de zero = 0 ;\n}\n";
    let word = source.find("de zero").expect("the misspelt keyword");
    let held = refused(source);
    assert!(
        held.iter().any(|&(ref name, ref refusal)| name == "Counts.zero"
            && matches!(*refusal, LoweringRefusal::MalformedForm {
                span,
                fault: FormFault::Misspelt(_),
                ..
            } if usize::from(span.start()) == word && usize::from(span.end()) == word.saturating_add(2))),
        "the member is refused at `de` under `zero`: {held:?}"
    );
    let stray = refused("module Counts {\n  zero one ;\n}\n");
    assert!(
        stray.iter().all(|&(ref name, ref refusal)| name == "Counts"
            && !matches!(*refusal, LoweringRefusal::MalformedForm {
                fault: FormFault::Misspelt(_),
                ..
            })),
        "a member that misspells no keyword is refused under its module: {stray:?}"
    );
}

#[test]
fn a_malformed_member_named_by_the_signature_is_reported_once()
{
    let source = "module Facts : #{ inner: #{ answer: Integer } } {\n  module inner : #{ \
                      answer: Integer } {\n";
    let lowered = repaired(source);
    let refused: Vec<_> = rows(&lowered)
        .into_iter()
        .filter_map(|(name, _, amounts)| match amounts {
            Amounts::Refused(refusal) => Some((name, refusal)),
            Amounts::Completed
            | Amounts::Uncompleted
            | Amounts::Bodied
            | Amounts::Data
            | Amounts::Codata
            | Amounts::Abstract
            | Amounts::World => None,
        })
        .collect();
    assert!(
        matches!(refused.as_slice(), [(_, LoweringRefusal::MalformedForm {
            fault: FormFault::Repaired(_),
            ..
        })]),
        "the open nested module is refused at its parse error alone, the signature \
             component naming it raising no unknown member: {refused:?}"
    );

    let sibling = "module Facts : #{ answer: Integer, other: Integer } {\n  def answer = ( 1 \
                       ;\n}\n";
    let lowered = repaired(sibling);
    let refused: Vec<_> = rows(&lowered)
        .into_iter()
        .filter_map(|(name, _, amounts)| match amounts {
            Amounts::Refused(refusal) => Some((name, refusal)),
            Amounts::Completed
            | Amounts::Uncompleted
            | Amounts::Bodied
            | Amounts::Data
            | Amounts::Codata
            | Amounts::Abstract
            | Amounts::World => None,
        })
        .collect();
    assert!(
        refused.iter().any(|&(_, ref refusal)| !matches!(
            refusal,
            LoweringRefusal::MalformedForm {
                fault: FormFault::Repaired(_),
                ..
            }
        )),
        "a repaired member silences only the component naming it, not a sibling the body \
             never declares: {refused:?}"
    );
}

#[test]
fn a_repaired_container_keeps_its_member()
{
    let source = "module M { def bad = ( 1 ; def good = 2; }\ndef good = 7;\n";
    let mut lowered = repaired(source);
    let found = rows(&lowered);
    assert!(
        matches!(
            found.as_slice(),
            [
                (bad, Role::Declared, Amounts::Refused(LoweringRefusal::MalformedForm {
                    form: refused,
                    fault: FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)),
                    ..
                })),
                (member, Role::Declared, Amounts::Bodied),
                (top, Role::Declared, Amounts::Bodied),
            ] if bad == "M.bad"
                && *refused == FormName::from(NamedKind("parenthesized_expression"))
                && member == "M.good"
                && top == "good"
        ),
        "the repair stays inside the member it repairs and names the group left open, \
             not the definition it cut short; the module keeps its other member and the \
             declaration after it, got {found:?}"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(false))
            .value("bad", 0_usize)
            .value("good", 1_usize)],
        "the module is closed where the author closed it"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(1_usize, Judgement::Synthesised),
            judged(2_usize, Judgement::Synthesised),
        ],
        "and both survivors check"
    );
}

#[test]
fn an_unread_module_body_is_refused_not_emptied()
{
    let source = "module M : #{\n  def x : Integer\n} {\n  def x = 1;\n}\n\ndef after = 1;\n";
    let lowered = repaired(source);
    let found = rows(&lowered);
    assert!(
        matches!(
            found.as_slice(),
            [
                (module, Role::Held, Amounts::Refused(LoweringRefusal::MalformedForm {
                    span,
                    form: FormName::MODULE,
                    fault: FormFault::MisplacedTile,
                })),
                (after, Role::Declared, Amounts::Bodied),
            ] if module == "M"
                && span.start() == span_of(source, "def", 0_usize).start()
                && after == "after"
        ),
        "the module is refused where its signature stops being read, and the declaration \
         after it is read on its own, got {found:?}"
    );
    assert_eq!(
        strata(&lowered),
        [],
        "and is not read as a module with no members"
    );
}

#[test]
fn a_readable_module_keeps_its_members_and_its_successor()
{
    let source = "module M {\n  def y = 2;\n}\n\ndef after = 1;\n";
    let mut lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [
            row("M.y", Role::Declared, Amounts::Bodied),
            row("after", Role::Declared, Amounts::Bodied),
        ],
        "both declarations survive as ordinary definitions"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
        ],
        "and check"
    );
}

#[test]
fn an_empty_module_is_not_an_unread_one()
{
    let source = "module M {}\n\ndef after = 1;\n";
    let lowered = lower(source);
    assert_eq!(
        rows(&lowered),
        [row("after", Role::Declared, Amounts::Bodied)],
        "an empty module refuses nothing and the declaration after it lands"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(false))],
        "the empty module is read"
    );
}

#[test]
fn an_unread_member_keeps_its_own_report()
{
    let source = "module M {\n  type = Type;\n}\n\ndef after = 1;\n";
    let lowered = repaired(source);
    let missing_name = span_of(source, "type", 0_usize).end();
    assert_eq!(
        rows(&lowered),
        [row(
            "M",
            Role::Held,
            Amounts::Refused(LoweringRefusal::MalformedForm {
                span: ByteSpan::new(missing_name, missing_name).expect("the span is ordered"),
                form: FormName::MODULE,
                fault: FormFault::Repaired(Repair::Unended(Ending::Unnamed)),
            })
        )],
        "the report is where the member's name belongs rather than over the whole declaration"
    );
    assert_eq!(
        strata(&lowered),
        [Stratum::new("M", Coerced(false))],
        "and the module itself is read"
    );
}

#[test]
fn module_name_case_boundary_covers_single_and_multi_names()
{
    for (spelled, readable) in [
        ("M", true),
        ("N", true),
        ("Nat", true),
        ("NatAdd", true),
        ("m", false),
        ("natAdd", false),
        ("intadd", false),
        ("monoid", false),
    ] {
        let source = format!(
            "module {spelled} : #{{ type T = Integer, zero : T, add : +U[ω] (T -> T -> -F \
                 T) }} {{ def zero = 0; def add(x : Integer, y : Integer) -> -F Integer {{ return \
                 x }} }}"
        );
        if readable {
            let mut lowered = lower(source.as_str());
            assert_eq!(
                rows(&lowered),
                [
                    row(
                        format!("{spelled}.zero"),
                        Role::Declared,
                        Amounts::Completed
                    ),
                    row(format!("{spelled}.add"), Role::Declared, Amounts::Completed),
                    row(format!("{spelled}.add"), Role::Witness, Amounts::Completed),
                ],
                "the uppercase module `{spelled}` keeps both components"
            );
            assert!(
                verdicts(&mut lowered)
                    .iter()
                    .all(|&(_, judgement)| judgement == Judgement::Checked),
                "and every declaration of `{spelled}` checks"
            );
        }
        else {
            let lowered = lower(source.as_str());
            let whole = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(source.len()))
                .expect("the span is ordered");
            assert_eq!(
                rows(&lowered),
                [row(
                    spelled,
                    Role::Held,
                    Amounts::Refused(LoweringRefusal::LowercaseModuleName {
                        span: whole,
                        name: name(spelled),
                    })
                )],
                "the lowercase module `{spelled}` is declined at its declaration, by name"
            );
            let plain = format!("module {spelled} {{ def zero = 0; }}\ndef after = 1;");
            let module = span_of(
                &plain,
                format!("module {spelled} {{ def zero = 0; }}"),
                0_usize,
            );
            assert_eq!(
                rows(&lower(plain.as_str())),
                [
                    row(
                        spelled,
                        Role::Held,
                        Amounts::Refused(LoweringRefusal::LowercaseModuleName {
                            span: module,
                            name: name(spelled),
                        })
                    ),
                    row("after", Role::Declared, Amounts::Bodied),
                ],
                "whatever the module holds, and the declaration after it still lands"
            );
        }
    }
}

#[test]
fn a_nested_module_declares_under_either_case_spelling()
{
    let uppercase = "module Config {\n  module Limits { def hard = 1; }\n  def soft = 2;\n}\n";
    assert_eq!(
        rows(&lower(uppercase)),
        [
            row("Config.Limits.hard", Role::Declared, Amounts::Bodied),
            row("Config.soft", Role::Declared, Amounts::Bodied),
        ],
        "an uppercase nested module is a module"
    );
    let lowercase = "module Config {\n  module limits { def hard = 1; }\n}\n";
    assert_eq!(
        rows(&lower(lowercase)),
        [row("Config.limits.hard", Role::Declared, Amounts::Bodied)],
        "and so is a lowercase one"
    );
}

#[test]
fn a_forward_member_reference_is_refused_by_position()
{
    let forward = |source: &str, path: &str, member: &str, written: usize, declared: usize| {
        let found = rows(&lower(source));
        let refusal = Amounts::Refused(LoweringRefusal::ForwardMemberReference {
            span: span_of(source, member, written),
            name: name(member),
            declared: span_of(source, member, declared),
        });
        assert!(
            found.contains(&row(path, Role::Declared, refusal)),
            "`{path}` is refused for naming `{member}` at or before its declaration in \
                 {source:?}, got {found:?}"
        );
    };
    forward(
        "module M { def a = b; def b = 1; }",
        "M.a",
        "b",
        0_usize,
        1_usize,
    );
    forward("module M { def a = a; }", "M.a", "a", 1_usize, 0_usize);
    forward(
        "data Circle : Type { Base : Circle; loop : Base <-> Base; }\nmodule M { def w : \
             Path(Circle, Base, Base) ; def w = loop ∷ here(Base) ; def loop = 1 ; }",
        "M.w",
        "loop",
        1_usize,
        2_usize,
    );
    forward(
        "module M { def a = here(1); def here = 1; }",
        "M.a",
        "here",
        0_usize,
        1_usize,
    );
    forward(
        "module M { module N { def a = b; } def b = 1; }",
        "M.N.a",
        "b",
        0_usize,
        1_usize,
    );
    let path_first = "def a = M.x;\nmodule M { def x = 1; }";
    assert_eq!(
        rows(&lower(path_first)),
        [
            row(
                "a",
                Role::Declared,
                Amounts::Refused(LoweringRefusal::ForwardMemberReference {
                    span: span_of(path_first, "M.x", 0_usize),
                    name: name("x"),
                    declared: span_of(path_first, "x", 1_usize),
                })
            ),
            row("M.x", Role::Declared, Amounts::Bodied),
        ],
        "a path written before the member it names is refused the same way"
    );
}

#[test]
fn a_type_member_reads_types_and_never_values()
{
    let phase = |source: &str, member: &str, reached: &str, (written, at): (&str, usize)| {
        let found = rows(&lower(source));
        let refused = |amounts: &Amounts<'_>| {
            *amounts
                == Amounts::Refused(LoweringRefusal::PhaseDependence {
                    span: span_of(source, written, at),
                    member: name(member),
                    reached: name(reached),
                })
        };
        assert!(
            found
                .iter()
                .any(|&(_, role, ref amounts)| role == Role::Held && refused(amounts)),
            "the type `{member}` is refused at `{written}`, naming the value `{reached}`, in \
             {source:?}: {found:?}"
        );
    };
    phase(
        "module M {\n  def count = 3;\n  type Q = Path(Integer, count, 3);\n}\n",
        "Q",
        "count",
        ("count", 1_usize),
    );
    phase(
        "module M {\n  def count = 3;\n  module N { type Q = Path(Integer, M.count, 3); }\n}\n",
        "Q",
        "count",
        ("M.count", 0_usize),
    );
    phase(
        "module S :> #{ type T, z : T, type P = Path(T, z, z) } {\n  type T = Integer;\n  def \
         z = 0;\n  type P = Path(Integer, 0, 0);\n}\n",
        "P",
        "z",
        ("z", 1_usize),
    );
    let static_only = "data Bit : Type { Low : Bit; High : Bit; }\nmodule M {\n  type Three = \
                       Path(Integer, 3, 3);\n  type Lowered = Path(Bit, Low, Low);\n  def three \
                       : Three ;\n  def three = here(3);\n}\n";
    let mut lowered = lower(static_only);
    let found = rows(&lowered);
    assert!(
        found
            .iter()
            .all(|&(_, _, ref amounts)| !matches!(*amounts, Amounts::Refused(_))),
        "a type reading a literal and a constructor, and a value reading that type, are read: \
         {found:?}"
    );
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and check"
    );
}

#[test]
fn a_backward_member_reference_resolves()
{
    let sibling = "module M { def b = 1; def a = b; }";
    let mut lowered = lower(sibling);
    assert_eq!(
        constant_read_by(&lowered, "M.a"),
        ConstantIndex::from(0_usize),
        "an earlier sibling resolves to its position"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
        ],
        "and checks"
    );
    let enclosing = "module M { def b = 1; module N { def a = b; } }";
    assert_eq!(
        constant_read_by(&lower(enclosing), "M.N.a"),
        ConstantIndex::from(0_usize),
        "so does an earlier member of an enclosing module"
    );
}

/// #1106: a nested module is a source-ordered member of its enclosing module,
/// so a member of the enclosing module, or of a module beside the nested one,
/// names the nested module's members through its name, under either case
/// spelling, as the nested module's own signature exports them.
#[test]
fn a_nested_module_is_named_from_inside_its_enclosing_module_1106()
{
    let nested = "module M { module inner { def answer = 41; } def total = inner.answer; }";
    let mut lowered = lower(nested);
    assert_eq!(
        constant_read_by(&lowered, "M.total"),
        ConstantIndex::from(0_usize),
        "the enclosing module's member reads the nested member's constant"
    );
    assert_eq!(
        verdicts(&mut lowered),
        [
            judged(0_usize, Judgement::Synthesised),
            judged(1_usize, Judgement::Synthesised),
        ],
        "and checks"
    );
    let sibling =
        "module M { module Inner { def answer = 41; } module other { def total = Inner.answer; } }";
    assert_eq!(
        constant_read_by(&lower(sibling), "M.other.total"),
        ConstantIndex::from(0_usize),
        "a module beside it reads it too, under a capitalised name"
    );
    let refused = |source: &str, refusal: LoweringRefusal<'_>| {
        let found = rows(&lower(source));
        assert!(
            found.contains(&row("M.total", Role::Declared, Amounts::Refused(refusal))),
            "`M.total` is refused {refusal:?} in {source:?}, got {found:?}"
        );
    };
    let hidden = "module M { module inner : #{ answer: Integer } { def hidden = 1; def answer = 2; \
                  } def total = inner.hidden; }";
    refused(hidden, LoweringRefusal::UnknownMember {
        span: span_of(hidden, "hidden", 1_usize),
        module: name("inner"),
        member: name("hidden"),
    });
    let later = "module M { def total = inner.answer; module inner { def answer = 41; } }";
    refused(later, LoweringRefusal::ForwardMemberReference {
        span: span_of(later, "inner.answer", 0_usize),
        name: name("answer"),
        declared: span_of(later, "answer", 1_usize),
    });
}
