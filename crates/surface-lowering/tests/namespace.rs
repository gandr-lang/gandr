//! The lowering of imports through the namespace engine: the import that
//! binds an alias through `alias_as`, the unit of several sources, a document
//! resumed after its closure, and each refusal an import answers. The engine's
//! own cases are in the integration target of `gandr-surface-lowering-base`.
//!
//! The import lowering's cases, in a `cfg(test)` module so the crate's lint
//! wall reads them as test code rather than as shipping code.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::Carried;
use gandr_core_term::CoreArena;
use gandr_kernel_term::OperationRules;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::ImportBinding;
use gandr_surface_lowering::ImportDeclaration;
use gandr_surface_lowering::ImportIndex;
use gandr_surface_lowering::ImportResolution;
use gandr_surface_lowering::ImportTarget;
use gandr_surface_lowering::ImportUri;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::MatchFault;
use gandr_surface_lowering::ModuleImports;
use gandr_surface_lowering::Onto;
use gandr_surface_lowering::ReadAs;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::Shadow;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::Unexported;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::UnitSource;
use gandr_surface_lowering::circuit::SignatureFault;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::description::DescriptionFault;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::lower_unit;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering::namespace::Trie;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

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

/// The bytes from `start` to `end`.
///
/// # Specification
/// - requires: the converted start does not exceed the converted end.
/// - ensures: the supplied byte endpoints are retained exactly.
/// - provides: an independent span fixture.
/// - fails: none for ordered endpoints.
/// - panics: if the converted endpoints are reversed.
/// - executable: none — the generic conversion consumes both inputs; retaining
///   them would add bounds or copies, while checking the result’s ordering
///   would only restate the span type.
///
/// # Adequacy
/// - hypothesis: L3 on ordered endpoint fixtures — duplicate aliases retain the
///   later and earlier source spans independently.
/// - witness: `tests::namespace::duplicate_source_import_alias_is_rejected_as_a_shadow`
fn bytes<Bound>(
    start: Bound,
    end: Bound,
) -> ByteSpan
where
    Bound: Into<ByteOffset>,
{
    ByteSpan::new(start.into(), end.into()).expect("the span is ordered")
}

/// The built-in grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// The tree the parser builds for `source` under `pbg`, repaired or not.
///
/// # Specification
/// - requires: the parser accepts the source under the supplied grammar.
/// - ensures: the returned tree retains that source and grammar, whether clean
///   or repaired.
/// - provides: a real parser-produced namespace fixture.
/// - fails: no parser failure is converted into an empty tree.
/// - panics: if parsing fails.
///
/// # Adequacy
/// - hypothesis: L3 — complete and missing-alias imports reach lowering with
///   their original spans rather than a synthetic replacement source.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::an_unqualified_import_binds_no_alias`
#[spec(
        ensures: |ret| ret.source() == source && ret.grammar() == pbg.fingerprint(),
    )]
fn parsed<'source>(
    pbg: &Pbg,
    source: SourceText<'source>,
) -> SyntaxTree<'source>
{
    parse(pbg, source)
        .expect("the parser reads the source")
        .into_tree()
}

/// `tree` lowered under `pbg` against the empty outermost scope.
///
/// # Specification
/// - requires: the grammar and tree are passed through unchanged.
/// - ensures: grammar mismatch is returned as an engine refusal; successful
///   declarations retain admission order.
/// - provides: a namespace-focused lowering fixture with no outermost names.
/// - fails: preserves the lowering engine’s refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — admitted and duplicate source imports preserve their
///   namespace effects and located refusal rather than silently resolving
///   addresses.
/// - witness: `tests::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `tests::namespace::duplicate_source_import_alias_becomes_a_refusal`
#[spec(
        ensures: |ret| match ret {
            | Ok(ref module) => {
                tree.grammar() == pbg.fingerprint()
                    && module
                        .declarations()
                        .iter()
                        .zip(module.declarations().iter().skip(1))
                        .all(|(left, right)| left.constant() < right.constant())
            },
            | Err(LoweringRefusal::GrammarMismatch { .. }) => tree.grammar() != pbg.fingerprint(),
            | Err(_) => tree.grammar() == pbg.fingerprint(),
        },
    )]
fn lowered<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    let mut arena = CoreArena::new();
    lower_module(
        pbg,
        tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
}

#[test]
fn source_import_reaches_the_namespace_engine_and_exposes_its_alias()
{
    let pbg = grammar();
    let module = lowered(
        &pbg,
        &parsed(
            &pbg,
            SourceText::from(
                include_str!("namespace/fixtures/source-import-reaches-the-namespace-engine-and-exposes-its-alias-module.gandr"),
            ),
        ),
    )
    .expect("import declarations lower");

    assert!(
        module.declarations().iter().next().is_none(),
        "an import is not a declaration"
    );
    assert_eq!(
        module
            .imports()
            .iter()
            .map(|import| (import.uri().as_ref(), import.binding()))
            .collect::<Vec<(&str, ImportBinding<'_>)>>(),
        Vec::from([
            (
                "file:///lib/parse.gandr",
                ImportBinding::Aliased(SurfaceName::from("parse"))
            ),
            (
                "file:///lib/list.gandr",
                ImportBinding::Aliased(SurfaceName::from("list_ext"))
            ),
        ]),
        "imports keep source order and their written operands"
    );
    let Maybe::Present(scope) = module.import_scope(SourceIndex::from(0_usize))
    else {
        panic!("the source binds two aliases");
    };
    assert_eq!(
        (
            scope.resolve(&path("parse")).map(|binding| binding.data),
            scope.resolve(&path("list_ext")).map(|binding| binding.data),
        ),
        (
            Maybe::Present(ImportIndex::from(0_usize)),
            Maybe::Present(ImportIndex::from(1_usize)),
        ),
        "each alias resolves to its import's source position"
    );
    assert_eq!(
        scope.export(),
        &Trie::empty(),
        "imports do not re-export their bindings"
    );
}

#[test]
fn an_import_binds_its_alias_and_resolves_no_address()
{
    let source = include_str!(
        "namespace/unformatted/an-import-binds-its-alias-and-resolves-no-address.gandr"
    );
    let pbg = grammar();
    let module = lowered(&pbg, &parsed(&pbg, SourceText::from(source))).expect("the module lowers");
    let span = bytes(0_usize, 49_usize);

    assert_eq!(
        module.imports(),
        [ImportDeclaration::new(
            ImportUri::from(String::from("file:///no/such/\"place\".gandr")),
            ImportBinding::Aliased(SurfaceName::from("far")),
            span,
            SourceIndex::from(0_usize),
            ImportResolution::Foreign,
        )]
        .as_slice(),
        "a scheme address is kept with its escapes decoded and nothing resolved, so an \
             address naming nothing still lowers"
    );
    let Maybe::Present(scope) = module.import_scope(SourceIndex::from(0_usize))
    else {
        panic!("the source binds an alias");
    };
    assert_eq!(
        listing_of(scope.visible()),
        Vec::from([(String::from("far"), ImportIndex::from(0_usize), span)]),
        "the alias is the one binding, to the import's position, tagged with its bytes"
    );
    assert_eq!(
        module.declarations().iter().len(),
        1_usize,
        "the declarations after an import are collected as before"
    );
}

/// The import namespace's dotted paths with their bindings.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every import binding is rendered in trie order with its exact
///   import index and source span.
/// - provides: a semantic import-namespace observer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source import retains its alias, index and span without
///   resolving or replacing its URI.
/// - witness: `tests::namespace::an_import_binds_its_alias_and_resolves_no_address`
#[spec(
        ensures: |ret| {
            ret.len() == usize::from(subject.binding_count())
                && ret.iter().zip(subject.iter()).all(
                    |(&(ref rendered, index, span), (bound, binding))| {
                        index == binding.data && span == binding.tag && {
                            if bound.segments().is_empty() {
                                rendered == "."
                            }
                            else {
                                rendered
                                    .chars()
                                    .eq(bound.segments().iter().enumerate().flat_map(
                                        |(index, segment)| {
                                            (index != 0)
                                                .then_some('.')
                                                .into_iter()
                                                .chain(segment.as_ref().chars())
                                        },
                                    ))
                            }
                        }
                    },
                )
        },
    )]
fn listing_of(subject: &Trie<ImportIndex, ByteSpan>) -> Vec<(String, ImportIndex, ByteSpan)>
{
    subject
        .iter()
        .map(|(bound, binding)| (format!("{bound}"), binding.data, binding.tag))
        .collect()
}

#[test]
fn duplicate_source_import_alias_is_rejected_as_a_shadow()
{
    let first = bytes(0_usize, 43_usize);
    let second = bytes(44_usize, 86_usize);
    let source = SourceIndex::from(0_usize);
    let mut imports = ModuleImports::new();
    imports
        .bind(ImportDeclaration::new(
            ImportUri::from(String::from("file:///lib/parse.gandr")),
            ImportBinding::Aliased(SurfaceName::from("parse")),
            first,
            source,
            ImportResolution::Foreign,
        ))
        .expect("a fresh alias binds");
    let refused = imports
        .bind(ImportDeclaration::new(
            ImportUri::from(String::from("file:///lib/list.gandr")),
            ImportBinding::Aliased(SurfaceName::from("parse")),
            second,
            source,
            ImportResolution::Foreign,
        ))
        .expect_err("two imports must not silently shadow at one alias");

    assert_eq!(
        refused,
        LoweringRefusal::DuplicateImportAlias {
            span: second,
            alias: SurfaceName::from("parse"),
            first,
        },
        "the import policy's shadow rejection names both imports"
    );
    let Maybe::Present(scope) = imports.scope(source)
    else {
        panic!("the first alias stays bound");
    };
    assert_eq!(
        (
            imports.declarations().len(),
            scope.resolve(&path("parse")).map(|binding| binding.data),
        ),
        (1_usize, Maybe::Present(ImportIndex::from(0_usize))),
        "a refused import is not kept and leaves the first binding in place"
    );
}

#[test]
fn an_unqualified_import_binds_no_alias()
{
    let pbg = grammar();
    let module = lowered(
        &pbg,
        &parsed(&pbg, SourceText::from("import \"./parse.gandr\" ;")),
    )
    .expect("an import with no alias lowers");

    assert_eq!(
        module.imports(),
        [ImportDeclaration::new(
            ImportUri::from(String::from("./parse.gandr")),
            ImportBinding::Unqualified,
            bytes(0_usize, 24_usize),
            SourceIndex::from(0_usize),
            ImportResolution::Path(ImportTarget::Unresolved),
        )]
        .as_slice(),
        "a path read alone names no source of its unit"
    );
    assert!(
        matches!(
            module.import_scope(SourceIndex::from(0_usize)),
            Maybe::Absent(_)
        ),
        "an unqualified import binds no alias"
    );
}

/// An import whose parse is repaired inside a form it holds, here a
/// declaration left unended after its path, is refused by that form, as every
/// reader refuses a nested repair, whether its imports are read alone or
/// lowered.
#[test]
fn an_import_repaired_inside_a_nested_form_is_refused_by_that_form()
{
    let pbg = grammar();
    let tree = parsed(&pbg, SourceText::from("import \"./base.gandr\" def ;"));
    let refused = |refusal: LoweringRefusal<'_>| {
        matches!(
            refusal,
            LoweringRefusal::MalformedForm {
                span,
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(_),
            } if span == bytes(25_usize, 25_usize)
        )
    };
    assert!(
        gandr_surface_lowering::written_imports(&pbg, &tree).is_err_and(refused),
        "the imports read alone are refused by the unended declaration"
    );
    assert!(
        lowered(&pbg, &tree).is_err_and(refused),
        "and so is the lowering"
    );
}

#[test]
fn an_unqualified_import_answers_a_name_its_source_declares()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-unqualified-import-answers-a-name-its-source-declares-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-unqualified-import-answers-a-name-its-source-declares-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<String> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some(format!("{refusal:?}"))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refusals,
        Vec::<String>::new(),
        "the importer's type head, value and constructor resolve in the base"
    );
    assert_eq!(
        module.declarations().iter().len(),
        4_usize,
        "the family, `one`, `again` and `made` are declared once each"
    );
}

/// The declarations of `module` the lowering refused, as their refusals read.
///
/// # Specification
/// trivial.
fn refused(module: &LoweredModule<'_>) -> Vec<String>
{
    module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some(format!("{refusal:?}"))
            }
            else {
                None
            }
        })
        .collect()
}

/// #6722: a bare `here` pattern names the empty word of the words that its
/// own source can name. The importer of the circle alone reads it as the
/// circle's empty word, though an earlier source of the unit mints the
/// sphere's words. The importer of both is refused as unannotated where the
/// scrutinee's position states no type.
#[test]
fn here_names_the_words_its_source_can_name_6722()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/here-names-the-words-its-source-can-name-6722-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/here-names-the-words-its-source-can-name-6722-2.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/here-names-the-words-its-source-can-name-6722-3.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(1_usize))],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/here-names-the-words-its-source-can-name-6722-4.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let outcomes: Vec<(String, bool)> = module
        .declarations()
        .iter()
        .filter(|declaration| ["counted", "ambiguous"].contains(&declaration.name().as_ref()))
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                matches!(
                    declaration.outcome(),
                    DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                        boundary: FragmentBoundary::Unannotated,
                        ..
                    })
                ),
            )
        })
        .collect();
    assert_eq!(
        outcomes,
        Vec::from([
            (String::from("counted"), false),
            (String::from("ambiguous"), true)
        ]),
        "`here` reads as the circle's empty word where the source sees the circle alone, and is unannotated where it sees both"
    );
}

#[test]
fn the_prelude_answers_a_name_nothing_written_binds_2302()
{
    // A source writing no import reads the prelude's `Eq` in a model type and
    // in an include, and its own `eq` shadows the prelude's; alone, it reads
    // neither.
    let pbg = grammar();
    let source = include_str!(
        "namespace/fixtures/the-prelude-answers-a-name-nothing-written-binds-2302.gandr"
    );
    let (text, unit) =
        gandr_surface_lowering::prelude::lay(SourceText::from(source), &Unit::single())
            .expect("a unit of one source lays after the prelude");
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        refused(&module),
        Vec::<String>::new(),
        "`Eq` answers from the prelude"
    );
    assert_eq!(
        include_faults(&module),
        Vec::new(),
        "the include reads the prelude's `Eq`"
    );
    let own = module
        .declarations()
        .iter()
        .rev()
        .find(|declaration| declaration.name() == SurfaceName::from("eq"))
        .expect("the source declares `eq`")
        .constant();
    let called = ByteOffset::from(text.rfind("eq true").expect("`mine` calls `eq`"));
    assert!(
        module
            .resolutions()
            .iter()
            .any(|&(span, resolved)| span.start() == called
                && resolved == gandr_surface_lowering::Resolution::Declaration(own)),
        "the source's own `eq` shadows the prelude's"
    );
    let alone = lowered_unit(
        &pbg,
        &parsed(&pbg, SourceText::from(source)),
        &Unit::single(),
    )
    .expect("the source lowers alone");
    assert_ne!(
        refused(&alone),
        Vec::<String>::new(),
        "alone, nothing answers `Eq`"
    );
}

/// #2767: `std.build`'s `theory Gandr.Package`, declared in the module its
/// dotted name opens, is read by its path from a source importing it: a model
/// of it stands, and one missing members is refused at each member.
#[test]
fn the_standard_package_theory_is_read_by_its_path_2767()
{
    let pbg = grammar();
    let source = include_str!(
        "namespace/fixtures/the-standard-package-theory-is-read-by-its-path-2767.gandr"
    );
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!("../../../library/std/src/build.gandr")),
            &[],
        ),
        (SourceText::from(source), &[ImportTarget::Source(
            SourceIndex::from(0_usize),
        )]),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let partial = text.rfind("Package)").expect("`Partial` names the theory");
    assert_eq!(
        refused(&module),
        [
            "version",
            "gandr",
            "features",
            "systems",
            "spelling",
            "authors",
            "licence",
            "documentation",
            "endpoint",
            "sources"
        ]
        .map(|member| format!("{:?}", LoweringRefusal::UnknownMember {
            span: ByteSpan::new(ByteOffset::from(partial), ByteOffset::from(partial + 7))
                .expect("a span"),
            module: SurfaceName::from("Partial"),
            member: SurfaceName::from(member),
        }))
        .to_vec(),
        "`Package` models the library's theory, and `Partial` lacks all but its `name`"
    );
}

/// #2687: a theory a source declares through a dotted name and keeps private
/// is refused to a source importing it, by its path, while the exported one
/// beside it in the same module is read.
#[test]
fn a_private_theory_in_a_dotted_module_is_refused_to_its_importer_2687()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-private-theory-in-a-dotted-module-is-refused-to-its-importer-2687-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-private-theory-in-a-dotted-module-is-refused-to-its-importer-2687-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let unseen = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("Unseen"))
        .map(gandr_surface_lowering::LoweredDeclaration::outcome);
    let hidden = text
        .rfind("Hidden")
        .expect("the importer names `Kit.Hidden`");
    let declared = text.find("Hidden").expect("the base declares `Kit.Hidden`");
    assert_eq!(
        unseen,
        Some(DeclarationOutcome::Refused(
            LoweringRefusal::UnexportedName {
                span: ByteSpan::new(ByteOffset::from(hidden), ByteOffset::from(hidden + 6))
                    .expect("a span"),
                name: SurfaceName::from("Hidden"),
                declared: ByteSpan::new(ByteOffset::from(declared), ByteOffset::from(declared + 6))
                    .expect("a span"),
                reason: Unexported::Private,
            }
        )),
        "the private theory is refused at its name in the path"
    );
    assert_eq!(
        refused(&module).len(),
        1_usize,
        "and the exported one beside it is read"
    );
}

/// #4514: a theory another source declares at a dotted path, `Store.Eff`, is
/// read by its path wherever a theory is named: a labelled row entry and a
/// scope's head, each fixing the theory's value sort, a module ascribed it, a
/// scope that module answers, and a rule's `under` row.
#[test]
fn an_imported_theory_at_a_dotted_path_is_named_wherever_a_theory_is_4514()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-theory-at-a-dotted-path-is-named-wherever-a-theory-is-4514-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-theory-at-a-dotted-path-is-named-wherever-a-theory-is-4514-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        refused(&module),
        Vec::<String>::new(),
        "each form reads the imported theory by its path"
    );
}

/// #2302: the prelude's `theory Eq` enters the presentation's constructors in
/// the prelude, as any block does, but offers none of them: a source laid
/// after it reads `Shape` as the type it declares, where the presentation's
/// `Shape` once answered and the code was refused.
#[test]
fn the_prelude_offers_no_presentation_constructor_2302()
{
    let pbg = grammar();
    let source = include_str!(
        "namespace/fixtures/the-prelude-offers-no-presentation-constructor-2302.gandr"
    );
    let (text, unit) =
        gandr_surface_lowering::prelude::lay(SourceText::from(source), &Unit::single())
            .expect("a unit of one source lays after the prelude");
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        refused(&module),
        Vec::<String>::new(),
        "`Shape` is the source's own type, not the presentation's constructor"
    );
}

/// #3287: the prelude's binary naturals declare the constructor `One`, which
/// answers only a name nothing written binds: a source declaring a type `One`
/// reads its own type where a value of `Type` is read, where the prelude's
/// constructor once answered and the path was refused.
#[test]
fn a_source_s_type_shadows_the_prelude_s_constructor_3287()
{
    let pbg = grammar();
    let source = include_str!(
        "namespace/fixtures/a-source-s-type-shadows-the-prelude-s-constructor-3287.gandr"
    );
    let (text, unit) =
        gandr_surface_lowering::prelude::lay(SourceText::from(source), &Unit::single())
            .expect("a unit of one source lays after the prelude");
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        refused(&module),
        Vec::<String>::new(),
        "`One` is the source's own type, not the prelude's constructor"
    );
}

#[test]
fn a_method_of_a_source_not_imported_is_out_of_scope()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(
                "pub module Str where { def len(self : shared Integer) -> -F Integer { pure self } }",
            ),
            &[],
        ),
        (
            SourceText::from(
                "pub module Bytes where { def len(self : shared Integer) -> -F Integer { pure 0 } }",
            ),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-method-of-a-source-not-imported-is-out-of-scope-1.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-method-of-a-source-not-imported-is-out-of-scope-2.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let outcome = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(gandr_surface_lowering::LoweredDeclaration::outcome)
    };

    assert!(
        !matches!(outcome("measured"), Some(DeclarationOutcome::Refused(_))),
        "a source importing `Str` alone calls its `len`, though the unit recognises `Bytes`: \
         {:?}",
        outcome("measured")
    );
    assert!(
        matches!(
            outcome("both"),
            Some(DeclarationOutcome::Refused(LoweringRefusal::AmbiguousMethod { first, second, .. }))
                if first == SurfaceName::from("Str") && second == SurfaceName::from("Bytes")
        ),
        "a source importing both sees both: {:?}",
        outcome("both")
    );
}

#[test]
fn two_imports_binding_one_name_refuse_its_use()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-2.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-3.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<String> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }) =
                declaration.outcome()
            {
                Some(String::from(name.as_ref()))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([String::from("one")]),
        "the use of a name two imports bind is refused, naming it"
    );
}

/// Two sources each declare a family with a constructor `Red`, and a third
/// imports both (#2713): a bare `Red` there is refused, naming both imports,
/// and `Signal.Red` and `Color.Red` each name their own family's constructor.
#[test]
fn a_constructor_two_imports_bind_is_refused_at_its_use_2713()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from("pub data Color : Type where { | Red : Color | Green : Color }"),
            &[],
        ),
        (
            SourceText::from("pub data Signal : Type where { | Red : Signal | Clear : Signal }"),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-constructor-two-imports-bind-is-refused-at-its-use-2713.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let outcome = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(gandr_surface_lowering::LoweredDeclaration::outcome)
    };

    for name in ["stop", "paint"] {
        assert!(
            !matches!(outcome(name), Some(DeclarationOutcome::Refused(_))),
            "`{name}` names its constructor through its family: {:?}",
            outcome(name)
        );
    }
    assert!(
        matches!(
            outcome("either"),
            Some(DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, import, other, .. }))
                if name == SurfaceName::from("Red") && import != other
        ),
        "a bare `Red` both imports bind is refused, naming both: {:?}",
        outcome("either")
    );
}

/// #1834: a type member written at a source's top level names its type in a
/// source importing it unqualified, which reaches the import; two imports
/// writing one name refuse its use, naming it; and an import's own imports
/// are not re-exported.
#[test]
fn an_imported_top_level_type_member_names_its_type_1834()
{
    let pbg = grammar();
    let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
    let (base, other, imported, both) = ([on(0_usize)], [on(1_usize)], [on(2_usize)], [
        on(0_usize),
        on(1_usize),
    ]);
    let (text, unit) = laid(&[
        (
            SourceText::from("pub type Band = *{low : Integer, high : Integer} ;"),
            &[],
        ),
        (SourceText::from("pub type Band = Integer ;"), &[]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-top-level-type-member-names-its-type-1834-1.gandr"
            )),
            &base,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-top-level-type-member-names-its-type-1834-2.gandr"
            )),
            &imported,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-top-level-type-member-names-its-type-1834-3.gandr"
            )),
            &both,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-imported-top-level-type-member-names-its-type-1834-4.gandr"
            )),
            &other,
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let outcome = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from(name))
            .map(gandr_surface_lowering::LoweredDeclaration::outcome)
    };
    for read in ["wide", "narrow"] {
        assert!(
            !matches!(outcome(read), Some(DeclarationOutcome::Refused(_))),
            "`{read}` names the synonym its import writes: {:?}",
            outcome(read)
        );
    }
    assert!(
        matches!(
            outcome("either"),
            Some(DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }))
                if name == SurfaceName::from("Band")
        ),
        "two imports writing `Band` refuse its use: {:?}",
        outcome("either")
    );
    assert!(
        matches!(
            outcome("far"),
            Some(DeclarationOutcome::Refused(
                LoweringRefusal::UnresolvedTypeHead { .. }
            ))
        ),
        "an import's own import is not re-exported: {:?}",
        outcome("far")
    );
    let imports: Vec<ByteSpan> = module
        .imports()
        .iter()
        .map(ImportDeclaration::span)
        .collect();
    for (index, label) in [(0_usize, "wide"), (4_usize, "narrow")] {
        assert!(
            imports
                .get(index)
                .is_some_and(|import| module.reached_imports().contains(import)),
            "`{label}`'s import is reached through the synonym"
        );
    }
}

#[test]
fn a_model_of_an_imported_theory_derives_its_signature_726()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-model-of-an-imported-theory-derives-its-signature-726-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-model-of-an-imported-theory-derives-its-signature-726-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let declarations: Vec<(String, String)> = module
        .declarations()
        .iter()
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                format!("{:?}", declaration.outcome()),
            )
        })
        .collect();
    assert!(
        declarations
            .iter()
            .all(|&(_, ref outcome)| !outcome.starts_with("Refused")),
        "`Model(Nat)` reads the imported block as a local one: {declarations:?}"
    );
}

/// #1993: a functor's argument names a module another source declares, read
/// through an unqualified import as any module path is, and reaches that
/// import; two imports declaring a module of the argument's name refuse the
/// application, naming it.
#[test]
fn a_functor_argument_reads_an_imported_module_1993()
{
    let pbg = grammar();
    let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
    let (base, both) = ([on(0_usize)], [on(0_usize), on(1_usize)]);
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-functor-argument-reads-an-imported-module-1993-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-functor-argument-reads-an-imported-module-1993-2.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-functor-argument-reads-an-imported-module-1993-3.gandr"
            )),
            &base,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-functor-argument-reads-an-imported-module-1993-4.gandr"
            )),
            &both,
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let refused: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| match declaration.outcome() {
            DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }) => Some((
                String::from(declaration.name().as_ref()),
                String::from(name.as_ref()),
            )),
            DeclarationOutcome::Refused(other) => Some((
                String::from(declaration.name().as_ref()),
                format!("{other:?}"),
            )),
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World => None,
        })
        .collect();
    assert_eq!(
        refused,
        [(String::from("EitherSquared"), String::from("Times"))],
        "the imported argument applies, and an argument two imports declare is refused by its \
         name"
    );
    let imports: Vec<ByteSpan> = module
        .imports()
        .iter()
        .map(ImportDeclaration::span)
        .collect();
    assert!(
        imports
            .first()
            .is_some_and(|import| module.reached_imports().contains(import)),
        "the argument reaches the import it is read through"
    );
}

/// The include faults a lowering's descriptions report, in the order the
/// unit's sources write them.
///
/// # Specification
/// trivial.
fn include_faults(module: &LoweredModule<'_>) -> Vec<SignatureFault>
{
    module
        .description_diagnostics()
        .iter()
        .filter_map(|diagnostic| {
            if let DescriptionFault::Signature(
                ref
                fault @ (SignatureFault::UnknownInclude(_) | SignatureFault::AmbiguousInclude(_)),
            ) = diagnostic.fault
            {
                Some(fault.clone())
            }
            else {
                None
            }
        })
        .collect()
}

/// #1224: an `include` names a theory of its own source or of one its source
/// imports unqualified, in the whole unit's lowering and in a document's
/// resumed after its closure alike. A theory two imports present is refused
/// as ambiguous; one only an import's import presents, or an aliased import,
/// is not seen.
#[test]
fn an_include_reads_the_theories_its_source_imports_1224()
{
    let pbg = grammar();
    let magma = SourceText::from(include_str!(
        "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-magma.gandr"
    ));
    let pointed = SourceText::from(include_str!(
        "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-pointed.gandr"
    ));
    let mag = Name::from("Mag");
    let (text, unit) = laid(&[
        (magma, &[]),
        (pointed, &[ImportTarget::Source(SourceIndex::from(0_usize))]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-1.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(1_usize))],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-3.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-include-reads-the-theories-its-source-imports-1224-4.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(4_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert_eq!(
        include_faults(&module),
        Vec::from([
            SignatureFault::UnknownInclude(mag.clone()),
            SignatureFault::UnknownInclude(mag.clone()),
            SignatureFault::AmbiguousInclude(mag),
        ]),
        "`Pointed` reads its import's `Mag`; `Through` and `Aliased` see none, `Both` two"
    );

    let (text, unit) = laid(&[
        (magma, &[]),
        (pointed, &[ImportTarget::Source(SourceIndex::from(0_usize))]),
    ]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the magma").to_vec())
            .expect("the magma alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut arena = CoreArena::new();
    let resumed = closure
        .resume(&joined, &unit, &mut arena, &mut Decisions::none())
        .expect("the unit lowers resumed");
    assert_eq!(
        include_faults(&resumed),
        Vec::new(),
        "the resumed document reads its closure's `Mag`"
    );
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    assert_eq!(resumed, whole, "the module the whole unit lowers to");
}

/// #776: a unit is lowered a source at a time, so a source lowers to the same
/// declarations, ids included, and the same leading arena rows whether or not
/// an importer follows it. Lowered pass by pass over the whole unit, the
/// importer's types were minted among the base's.
#[test]
fn a_source_lowers_alike_whatever_follows_it_776()
{
    let pbg = grammar();
    let base = SourceText::from(include_str!(
        "namespace/fixtures/a-source-lowers-alike-whatever-follows-it-776-base.gandr"
    ));
    let importer = SourceText::from(include_str!(
        "namespace/fixtures/a-source-lowers-alike-whatever-follows-it-776-importer.gandr"
    ));
    let (alone_text, alone_unit) = laid(&[(base, &[])]);
    let (whole_text, whole_unit) = laid(&[
        (base, &[]),
        (importer, &[ImportTarget::Source(SourceIndex::from(
            0_usize,
        ))]),
    ]);
    let mut alone_arena = CoreArena::new();
    let alone = lower_unit(
        &pbg,
        &parsed(&pbg, SourceText::from(alone_text.as_str())),
        &alone_unit,
        &mut alone_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the base alone lowers");
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &parsed(&pbg, SourceText::from(whole_text.as_str())),
        &whole_unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the base and its importer lower");
    let own = alone.declarations().iter().len();
    assert!(
        whole.declarations().iter().len() > own
            && whole.declarations().iter().all(|declaration| !matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(_)
            )),
        "the importer adds declarations of its own, and nothing is refused"
    );
    assert_eq!(
        whole.declarations().iter().take(own).collect::<Vec<_>>(),
        alone.declarations().iter().collect::<Vec<_>>(),
        "the base's declarations are the same, ids included, with the importer after it"
    );
    let start = CoreArena::new().watermark();
    assert!(
        alone_arena
            .values_since(start)
            .all(|id| whole_arena.value(id) == alone_arena.value(id))
            && alone_arena
                .computations_since(start)
                .all(|id| whole_arena.computation(id) == alone_arena.computation(id))
            && alone_arena
                .value_types_since(start)
                .all(|id| whole_arena.value_type(id) == alone_arena.value_type(id))
            && alone_arena
                .comp_types_since(start)
                .all(|id| whole_arena.comp_type(id) == alone_arena.comp_type(id)),
        "the base's arena rows lead the unit's arena"
    );
}

/// #1078: a `theory` block names the unit's one `Theory`, whatever the unit
/// lays before it. Alone, a source naming `Theory` and `Presents` mints the
/// code; behind a block it does not import, and behind one it imports, it takes
/// that block's code and every declaration of it stands. A source importing
/// both names the one code, with no ambiguity. The code a later source's block
/// took answered no name of that source. A block no manifest model type names
/// takes no forgetting map.
#[test]
fn a_theory_lowers_alike_whatever_the_unit_lays_before_it_1078()
{
    let pbg = grammar();
    let first = SourceText::from(include_str!(
        "namespace/fixtures/a-theory-lowers-alike-whatever-the-unit-lays-before-it-1078-first.gandr"
    ));
    let counting = include_str!(
        "namespace/fixtures/a-theory-lowers-alike-whatever-the-unit-lays-before-it-1078-counting.gandr"
    );
    let importing = format!(
        include_str!(
            "namespace/unformatted/a-theory-lowers-alike-whatever-the-unit-lays-before-it-1078-importing.gandr"
        ),
        counting = counting
    );
    let both = SourceText::from(include_str!(
        "namespace/fixtures/a-theory-lowers-alike-whatever-the-unit-lays-before-it-1078-both.gandr"
    ));
    let declared = |sources: &[(SourceText<'_>, &[ImportTarget])]| -> Vec<(String, bool)> {
        let (text, unit) = laid(sources);
        lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers")
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    String::from(declaration.name().as_ref()),
                    matches!(declaration.outcome(), DeclarationOutcome::Refused(_)),
                )
            })
            .collect()
    };
    let stood = |names: &[&str]| -> Vec<(String, bool)> {
        names
            .iter()
            .map(|&name| (String::from(name), false))
            .collect()
    };
    assert_eq!(
        declared(&[(SourceText::from(counting), &[])]),
        stood(&["Theory", "Monoid", "count"]),
        "alone, the block mints `Theory` and `count` reads it"
    );
    assert_eq!(
        declared(&[(first, &[]), (SourceText::from(counting), &[])]),
        stood(&["Theory", "Magma", "Monoid", "count"]),
        "behind a block it does not import, the source names that block's `Theory`"
    );
    assert_eq!(
        declared(&[
            (first, &[]),
            (SourceText::from(importing.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ])
        ]),
        stood(&["Theory", "Magma", "Monoid", "count"]),
        "behind a block it imports, the source names that block's `Theory`"
    );
    assert_eq!(
        declared(&[
            (first, &[]),
            (SourceText::from(counting), &[]),
            (both, &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ])
        ]),
        stood(&["Theory", "Magma", "Monoid", "count", "pick"]),
        "a source importing both blocks names one `Theory`"
    );
}

/// #1078: a univalence statement reads the `theory` blocks its own source
/// sees. Behind a source declaring `Monoid` that it does not import, `ua`
/// naming `Monoid` is refused as an unresolved name, as it is alone; through an
/// import of that source it reads the block. The statement read every block of
/// the unit by name.
#[test]
fn a_univalence_statement_reads_only_the_blocks_its_source_sees_1078()
{
    let pbg = grammar();
    let monoid = SourceText::from(include_str!(
        "namespace/fixtures/a-univalence-statement-reads-only-the-blocks-its-source-sees-1078-monoid.gandr"
    ));
    let stating = include_str!(
        "namespace/fixtures/a-univalence-statement-reads-only-the-blocks-its-source-sees-1078-stating.gandr"
    );
    let importing = format!(
        include_str!(
            "namespace/unformatted/a-univalence-statement-reads-only-the-blocks-its-source-sees-1078-importing.gandr"
        ),
        stating = stating
    );
    // Whether `unnamed` is refused, and whether at `Monoid` as an unresolved
    // name.
    let unnamed = |sources: &[(SourceText<'_>, &[ImportTarget])]| -> (bool, bool) {
        let (text, unit) = laid(sources);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        let outcome = module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == "unnamed")
            .expect("`unnamed` is declared")
            .outcome();
        (
            matches!(outcome, DeclarationOutcome::Refused(_)),
            matches!(
                outcome,
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName { name, .. })
                    if name.as_ref() == "Monoid"
            ),
        )
    };
    assert_eq!(
        unnamed(&[(SourceText::from(stating), &[])]),
        (true, true),
        "alone, `Monoid` names no block"
    );
    assert_eq!(
        unnamed(&[(monoid, &[]), (SourceText::from(stating), &[])]),
        (true, true),
        "behind a source it does not import, `Monoid` still names no block"
    );
    assert_eq!(
        unnamed(&[
            (monoid, &[]),
            (SourceText::from(importing.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize),)
            ]),
        ]),
        (false, false),
        "through an import, `Monoid` reads the imported block"
    );
}

/// #1033: a document parsed alone, laid after its closure's tree and resumed
/// on the closure's lowering lowers as the whole unit does over that tree, the
/// module and the arena alike, each time it is resumed, the closure's hole and
/// the document's numbered as the whole unit numbers them; its declarations
/// and arena are the ones the whole text's parse lowers to. A tree that does
/// not extend the closure's is lowered whole, and a document that refuses the
/// unit answers the whole lowering's refusal.
#[test]
fn a_document_resumed_after_its_closure_lowers_as_the_whole_1033()
{
    let pbg = grammar();
    let base = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-lowers-as-the-whole-1033-base.gandr"
    ));
    let importer = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-lowers-as-the-whole-1033-importer.gandr"
    ));
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (importer, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    assert!(
        whole
            .declarations()
            .iter()
            .all(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))),
        "nothing is refused"
    );
    for _ in 0_usize .. 2_usize {
        let mut arena = CoreArena::new();
        let resumed = closure
            .resume(&joined, &unit, &mut arena, &mut Decisions::none())
            .expect("the unit lowers resumed");
        assert_eq!(resumed, whole, "the module the whole unit lowers to");
        assert_eq!(arena, whole_arena, "the arena the whole unit mints");
    }
    let tree = parsed(&pbg, SourceText::from(text.as_str()));
    let mut text_arena = CoreArena::new();
    let from_text = lower_unit(
        &pbg,
        &tree,
        &unit,
        &mut text_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the whole text lowers");
    assert_eq!(
        from_text.declarations(),
        whole.declarations(),
        "the whole text's declarations"
    );
    assert_eq!(text_arena, whole_arena, "the whole text's arena");
    let mut fallback_arena = CoreArena::new();
    assert_eq!(
        closure.resume(&tree, &unit, &mut fallback_arena, &mut Decisions::none()),
        Ok(from_text),
        "a tree that does not extend the closure's is lowered whole"
    );
    assert_eq!(fallback_arena, text_arena);
    let refusing = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-lowers-as-the-whole-1033-refusing.gandr"
    ));
    let twice = [
        ImportTarget::Source(SourceIndex::from(0_usize)),
        ImportTarget::Source(SourceIndex::from(0_usize)),
    ];
    let (refused_text, refused_unit) = laid(&[(base, &[]), (refusing, &twice)]);
    let refused = parse(&pbg, refusing)
        .expect("the document parses")
        .after(closure.tree(), SourceText::from(refused_text.as_str()))
        .expect("the document lays after its closure")
        .into_tree();
    let expected = lower_unit(
        &pbg,
        &refused,
        &refused_unit,
        &mut CoreArena::new(),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    );
    assert!(
        expected.is_err(),
        "unfinished imports in a source that declares nothing refuse the unit"
    );
    assert_eq!(
        closure.resume(
            &refused,
            &refused_unit,
            &mut CoreArena::new(),
            &mut Decisions::none()
        ),
        expected
    );
}

/// #3321: a document resumed after its closure reads each table by
/// declaration — operation rules, stage bounds, region names, implicits,
/// model slots, supplies, handler laws and model plans — at the closure's
/// declarations and at its own as the whole lowering's module does, the
/// closure's declarations and the document's each filing every table.
#[test]
fn a_document_resumed_after_its_closure_reads_each_table_by_declaration_as_the_whole_3321()
{
    let pbg = grammar();
    let base = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-reads-each-table-by-declaration-as-the-whole-3321-base.gandr"
    ));
    let document = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-reads-each-table-by-declaration-as-the-whole-3321-document.gandr"
    ));
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (document, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the document is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the document's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut CoreArena::new(),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    let refused: Vec<(SurfaceName<'_>, DeclarationOutcome<'_>)> = whole
        .declarations()
        .iter()
        .filter(|declaration| matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
        .map(|declaration| (declaration.name(), declaration.outcome()))
        .collect();
    assert!(refused.is_empty(), "nothing is refused: {refused:?}");
    // Which of the eight tables `module` files an entry in at any of
    // `declarations`.
    let filed = |module: &LoweredModule<'_>, declarations: &[LoweredDeclaration<'_>]| {
        declarations.iter().fold([false; 8], |filed, declaration| {
            let constant = declaration.constant();
            let [
                rules,
                stages,
                regions,
                implicits,
                slots,
                supplies,
                laws,
                models,
            ] = filed;
            [
                rules || module.operation_rules(declaration) != OperationRules::default(),
                stages || !module.stages(declaration).is_empty(),
                regions || !module.region_names(constant).is_empty(),
                implicits || !module.implicits(constant).is_empty(),
                slots || !module.model_slots(constant).is_empty(),
                supplies || !module.supplies(declaration).is_empty(),
                laws || !module.handler_laws(declaration).is_empty(),
                models || !module.models(declaration).is_empty(),
            ]
        })
    };
    let (alone, _) = closure.alone().expect("the closure lowers to its end");
    let declared: Vec<LoweredDeclaration<'_>> = whole.declarations().iter().copied().collect();
    let (closure_part, document_part) = declared
        .split_at_checked(alone.declarations().iter().len())
        .expect("the closure's declarations lead the whole lowering's");
    assert_eq!(
        filed(&whole, closure_part),
        [true; 8],
        "the closure's declarations file every table"
    );
    assert_eq!(
        filed(&whole, document_part),
        [true; 8],
        "and so do the document's"
    );
    for _ in 0_usize .. 2_usize {
        let resumed = closure
            .resume(
                &joined,
                &unit,
                &mut CoreArena::new(),
                &mut Decisions::none(),
            )
            .expect("the unit lowers resumed");
        assert_eq!(
            resumed.declarations(),
            whole.declarations(),
            "the whole lowering's declarations"
        );
        for declaration in whole.declarations() {
            let (name, constant) = (declaration.name(), declaration.constant());
            assert_eq!(
                resumed.operation_rules(declaration),
                whole.operation_rules(declaration),
                "`{name:?}`'s operation rules"
            );
            assert_eq!(
                resumed.stages(declaration),
                whole.stages(declaration),
                "`{name:?}`'s stage bounds"
            );
            assert_eq!(
                resumed.region_names(constant),
                whole.region_names(constant),
                "`{name:?}`'s region names"
            );
            assert_eq!(
                resumed.implicits(constant),
                whole.implicits(constant),
                "`{name:?}`'s implicits"
            );
            assert_eq!(
                resumed.model_slots(constant),
                whole.model_slots(constant),
                "`{name:?}`'s model slots"
            );
            assert_eq!(
                resumed.supplies(declaration),
                whole.supplies(declaration),
                "`{name:?}`'s supplies"
            );
            assert_eq!(
                resumed.handler_laws(declaration),
                whole.handler_laws(declaration),
                "`{name:?}`'s handler laws"
            );
            assert_eq!(
                resumed.models(declaration),
                whole.models(declaration),
                "`{name:?}`'s model plans"
            );
        }
        assert_eq!(resumed, whole, "the module the whole unit lowers to");
    }
}

/// A closure whose own sources refuse the unit halts where the refusal
/// stands: it holds no module of its own, and a document resumed after it
/// answers the refusal the whole unit answers.
#[test]
fn a_closure_whose_unit_refuses_halts_and_answers_the_refusal()
{
    let pbg = grammar();
    let base = SourceText::from("def one = 1 ;");
    let refusing = SourceText::from(include_str!(
        "namespace/fixtures/a-document-resumed-after-its-closure-lowers-as-the-whole-1033-refusing.gandr"
    ));
    let twice = [
        ImportTarget::Source(SourceIndex::from(0_usize)),
        ImportTarget::Source(SourceIndex::from(0_usize)),
    ];
    let (text, unit) = laid(&[(base, &[]), (refusing, &twice)]);
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        text.clone(),
        unit.clone(),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    assert!(
        format!("{closure:?}").starts_with("ClosureLowering"),
        "the closure debugs as itself"
    );
    assert!(
        closure.alone().is_none(),
        "a halted closure holds no module of its own"
    );
    let tree = parsed(&pbg, SourceText::from(text.as_str()));
    let expected = lower_unit(
        &pbg,
        &tree,
        &unit,
        &mut CoreArena::new(),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    );
    assert!(
        expected.is_err(),
        "unfinished imports in a source that declares nothing refuse the unit"
    );
    assert_eq!(
        closure.resume(&tree, &unit, &mut CoreArena::new(), &mut Decisions::none()),
        expected
    );
}

/// #776: a closure's own module is the leading declarations its importer
/// lowers to, ids included. Onto the closure's own arena the document lowers
/// exactly as the whole unit does; onto that arena with more nodes minted after
/// it — what a checker judging the closure leaves — the closure's declarations
/// and rows stand unchanged, and the document declares what the whole unit
/// declares, minting as many nodes, after the added ones. A tree that does not
/// extend the closure's is left to the whole lowering, the arena untouched.
#[test]
fn a_document_lowered_onto_its_closure_s_arena_follows_its_nodes_776()
{
    /// Each declaration's name and the kind of its outcome.
    ///
    /// # Specification
    /// trivial.
    fn shape<'source>(
        module: &LoweredModule<'source>
    ) -> Vec<(String, core::mem::Discriminant<DeclarationOutcome<'source>>)>
    {
        module
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    String::from(declaration.name().as_ref()),
                    core::mem::discriminant(&declaration.outcome()),
                )
            })
            .collect()
    }
    let pbg = grammar();
    let base = SourceText::from(include_str!(
        "namespace/fixtures/a-document-lowered-onto-its-closure-s-arena-follows-its-nodes-776-base.gandr"
    ));
    let importer = SourceText::from(include_str!(
        "namespace/fixtures/a-document-lowered-onto-its-closure-s-arena-follows-its-nodes-776-importer.gandr"
    ));
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (importer, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the importer is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the importer's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut whole_arena = CoreArena::new();
    let whole = lower_unit(
        &pbg,
        &joined,
        &unit,
        &mut whole_arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
    .expect("the unit lowers");
    let (alone, alone_arena) = closure.alone().expect("the closure lowers to its end");
    let leading = alone.declarations().iter().len();
    assert_eq!(
        alone.declarations().iter().collect::<Vec<_>>(),
        whole
            .declarations()
            .iter()
            .take(leading)
            .collect::<Vec<_>>(),
        "the closure's own declarations lead the importer's"
    );
    let mut onto = alone_arena.clone();
    let uncarried = closure.carrying(&[], &[]);
    let Ok(Onto::Resumed(resumed)) = closure.resume_onto(
        &joined,
        &unit,
        &mut onto,
        &uncarried,
        &mut Decisions::none(),
    )
    else {
        panic!("the document resumes onto its closure's arena");
    };
    assert_eq!(
        resumed, whole,
        "onto the closure's own arena, the whole module"
    );
    assert_eq!(onto, whole_arena, "and the whole arena");
    let source = alone
        .declarations()
        .iter()
        .find_map(|declaration| {
            if let DeclarationOutcome::Completed { body, .. } = declaration.outcome() {
                Some(body)
            }
            else {
                None
            }
        })
        .expect("`one` is completed");
    let Maybe::Present(written) = alone.origins().value(source)
    else {
        panic!("`one`'s body is located");
    };
    let mut checked = alone_arena.clone();
    let elaborated = checked.value_unit();
    let _type = checked.value_type_unit();
    let added = checked.watermark();
    assert_ne!(added, alone_arena.watermark(), "nodes follow the closure's");
    let Ok(Onto::Resumed(after)) = closure.resume_onto(
        &joined,
        &unit,
        &mut checked,
        &closure.carrying(&[Carried::Value(source, elaborated)], &[]),
        &mut Decisions::none(),
    )
    else {
        panic!("the document resumes onto the checked arena");
    };
    assert_eq!(
        after.origins().value(elaborated),
        Maybe::Present(written),
        "a node minted after the closure's is located where its source is written"
    );
    let bodies = |module: &LoweredModule<'_>| {
        module
            .declarations()
            .iter()
            .skip(leading)
            .filter_map(|declaration| match declaration.outcome() {
                DeclarationOutcome::Completed { body, .. }
                | DeclarationOutcome::Bodied { body } => Some(module.origins().value(body)),
                DeclarationOutcome::Uncompleted { .. }
                | DeclarationOutcome::Data(_)
                | DeclarationOutcome::Codata(_)
                | DeclarationOutcome::Abstract(_)
                | DeclarationOutcome::World
                | DeclarationOutcome::Refused(_) => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        bodies(&after),
        bodies(&whole),
        "and the document's bodies where the whole lowering locates them"
    );
    assert_eq!(
        after
            .declarations()
            .iter()
            .take(leading)
            .collect::<Vec<_>>(),
        alone.declarations().iter().collect::<Vec<_>>(),
        "the closure's declarations stand"
    );
    assert_eq!(
        shape(&after),
        shape(&whole),
        "the whole unit's declarations"
    );
    let mark = alone_arena.watermark();
    assert_eq!(
        (
            checked.values_since(added).len(),
            checked.computations_since(added).len(),
            checked.value_types_since(added).len(),
            checked.comp_types_since(added).len(),
        ),
        (
            whole_arena.values_since(mark).len(),
            whole_arena.computations_since(mark).len(),
            whole_arena.value_types_since(mark).len(),
            whole_arena.comp_types_since(mark).len(),
        ),
        "the document mints as many nodes, after the added ones"
    );
    let tree = parsed(&pbg, SourceText::from(text.as_str()));
    let mut untouched = alone_arena.clone();
    assert!(
        matches!(
            closure.resume_onto(
                &tree,
                &unit,
                &mut untouched,
                &uncarried,
                &mut Decisions::none()
            ),
            Ok(Onto::Whole)
        ),
        "a tree that does not extend the closure's is left to the whole lowering"
    );
    assert_eq!(untouched, alone_arena, "its arena untouched");
}

#[test]
fn a_pending_declaration_is_not_exported()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("pub def owed : Integer ;"), &[]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-pending-declaration-is-not-exported.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnexportedName { name, reason: Unexported::Undefined, .. })
                if name.as_ref() == "owed"
        )),
        "a signature without a definition is not exported, and its use refuses by name"
    );
}

#[test]
fn an_aliased_import_qualifies_its_source_s_names()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-unqualified-import-answers-a-name-its-source-declares-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-aliased-import-qualifies-its-source-s-names.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some((
                    String::from(declaration.name().as_ref()),
                    format!("{refusal:?}"),
                ))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(refusals.len(), 1_usize, "only `lost` refuses: {refusals:?}");
    assert!(
        refusals
            .iter()
            .any(|&(ref name, ref refusal)| name == "lost"
                && refusal.starts_with("UnknownMember")
                && refusal.contains("\"two\"")),
        "a name the imported source does not declare is refused by name: {refusals:?}"
    );
}

/// #2687: `import text.greet ;` binds its module qualified, under the path
/// it names: a member reads as `text.greet.one`, as a term and as a type;
/// a member the module does not declare is refused naming the path; neither
/// a prefix of the path nor the member's bare name reads it.
#[test]
fn a_module_path_import_binds_its_module_qualified_2687()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-unqualified-import-answers-a-name-its-source-declares-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-import-binds-its-module-qualified-2687.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some((
                    String::from(declaration.name().as_ref()),
                    format!("{refusal:?}"),
                ))
            }
            else {
                None
            }
        })
        .collect();
    let named: Vec<&str> = refusals
        .iter()
        .map(|&(ref name, _)| name.as_str())
        .collect();
    assert_eq!(
        named,
        ["lost", "prefix", "bare"],
        "`again` reads through the path, the rest refuse: {refusals:?}"
    );
    assert!(
        refusals
            .iter()
            .any(|&(ref name, ref refusal)| name == "lost"
                && refusal.starts_with("UnknownMember")
                && refusal.contains("\"text.greet\"")
                && refusal.contains("\"two\"")),
        "a member the module does not declare is refused naming the path as written: \
         {refusals:?}"
    );
}

/// #2874: a type behind a module path of three names or four reads its
/// module's type, as the term path reads its value, and a type the module does
/// not declare is refused naming the whole path.
#[test]
fn a_type_reads_through_a_module_path_of_any_length_2874()
{
    let pbg = grammar();
    let token = include_str!(
        "namespace/fixtures/a-type-reads-through-a-module-path-of-any-length-2874-token.gandr"
    );
    let (text, unit) = laid(&[
        (SourceText::from(token), &[]),
        (SourceText::from(token), &[]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-type-reads-through-a-module-path-of-any-length-2874.gandr"
            )),
            &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
                ImportTarget::Source(SourceIndex::from(1_usize)),
            ],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refusals: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                Some((
                    String::from(declaration.name().as_ref()),
                    format!("{refusal:?}"),
                ))
            }
            else {
                None
            }
        })
        .collect();
    assert!(
        matches!(refusals.as_slice(), [(name, refusal)] if name == "lost"
            && refusal.starts_with("UnknownMember")
            && refusal.contains("\"a.b.c\"")
            && refusal.contains("\"Lost\"")),
        "`three` and `four` read their types through the path, and `lost` is refused naming \
         it: {refusals:?}"
    );
}

/// #2687: an import's list binds the names it lists by their own names,
/// beside the module the path binds qualified, and binds no other name by its
/// own; a quoted import with a list binds only those. A listed name its module
/// does not declare, or keeps private, refuses the importing source at the
/// name.
#[test]
fn an_import_list_binds_only_the_names_it_lists_2687()
{
    let pbg = grammar();
    let imported = SourceText::from(include_str!(
        "namespace/fixtures/an-import-list-binds-only-the-names-it-lists-2687-imported.gandr"
    ));
    let refusals = |importer: &'static str| -> Vec<(String, String)> {
        let (text, unit) = laid(&[
            (imported, &[]),
            (SourceText::from(importer), &[ImportTarget::Source(
                SourceIndex::from(0_usize),
            )]),
        ]);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                    Some((
                        String::from(declaration.name().as_ref()),
                        format!("{refusal:?}"),
                    ))
                }
                else {
                    None
                }
            })
            .collect()
    };

    let listed = refusals(include_str!(
        "namespace/fixtures/an-import-list-binds-only-the-names-it-lists-2687-listed.gandr"
    ));
    assert!(
        matches!(listed.as_slice(), [(name, refusal)] if name == "unlisted" && refusal.starts_with("UnresolvedName")),
        "the listed names read bare and the path reads qualified; an unlisted name does not \
         read bare: {listed:?}"
    );
    let quoted = refusals(include_str!(
        "namespace/fixtures/an-import-list-binds-only-the-names-it-lists-2687-quoted.gandr"
    ));
    assert!(
        matches!(quoted.as_slice(), [(name, refusal)] if name == "unlisted" && refusal.starts_with("UnresolvedName")),
        "an unaliased quoted import with a list binds what it lists and nothing else: \
         {quoted:?}"
    );
    let missing = refusals(include_str!(
        "namespace/fixtures/an-import-list-binds-only-the-names-it-lists-2687-missing.gandr"
    ));
    assert!(
        matches!(missing.as_slice(), [(name, refusal)] if name == "a"
            && refusal.starts_with("UnknownMember")
            && refusal.contains("\"text.greet\"")
            && refusal.contains("\"nothing\"")),
        "a listed name the module does not declare refuses the importer at the list: \
         {missing:?}"
    );
    let private = refusals(include_str!(
        "namespace/fixtures/an-import-list-binds-only-the-names-it-lists-2687-private.gandr"
    ));
    assert!(
        matches!(private.as_slice(), [(name, refusal)] if name == "a"
            && refusal.starts_with("UnexportedName")
            && refusal.contains("\"hidden\"")
            && refusal.contains("Private")),
        "a listed name the module keeps private refuses the importer at the list: {private:?}"
    );
}

#[test]
fn a_pending_member_read_through_an_alias_is_refused_at_the_member()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from("pub def owed : Integer ;"), &[]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-pending-member-read-through-an-alias-is-refused-at-the-member.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let member = text.find("base.owed").expect("the path is written") + "base.".len();

    assert!(
        module.declarations().iter().any(|declaration| matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::UnexportedName { span, name, reason: Unexported::Undefined, .. })
                if name.as_ref() == "owed" && span == bytes(member, member + "owed".len())
        )),
        "the refusal stands at the selected name, not the whole path"
    );
}

#[test]
fn an_unresolved_import_refuses_its_source()
{
    let pbg = grammar();
    let (text, unit) = laid(&[(
        SourceText::from(include_str!(
            "namespace/unformatted/an-unresolved-import-refuses-its-source.gandr"
        )),
        &[ImportTarget::Unresolved],
    )]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        matches!(
            *module.declarations().iter().collect::<Vec<_>>(),
            [declaration] if matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::ImportUnresolved { span, .. })
                    if span == bytes(0_usize, 26_usize)
            )
        ),
        "every declaration of the source is refused, naming the import"
    );
}

#[test]
fn an_import_closing_a_cycle_refuses_its_source()
{
    let pbg = grammar();
    let (text, unit) = laid(&[(
        SourceText::from(include_str!(
            "namespace/unformatted/an-import-closing-a-cycle-refuses-its-source.gandr"
        )),
        &[ImportTarget::Cycle],
    )]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    assert!(
        matches!(
            *module.declarations().iter().collect::<Vec<_>>(),
            [declaration] if matches!(
                declaration.outcome(),
                DeclarationOutcome::Refused(LoweringRefusal::ImportCycle { span, .. })
                    if span == bytes(0_usize, 23_usize)
            )
        ),
        "every declaration of the source is refused, naming the import on the cycle"
    );
}

/// #3072: an import naming no module of the package and no dependency its
/// lock records binds nothing, and refuses only the declarations reading
/// through it, at the alias; every other declaration of the source stands,
/// so the coordinates a package's sources import are read before its lock is
/// written.
#[test]
fn a_name_read_through_an_unlocked_alias_is_refused_at_it_3072()
{
    let pbg = grammar();
    let (text, unit) = laid(&[(
        SourceText::from(include_str!(
            "namespace/fixtures/a-name-read-through-an-unlocked-alias-is-refused-at-it-3072.gandr"
        )),
        &[ImportTarget::Unlocked],
    )]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let alias = text.find("hello.welcome").expect("the path is written");
    let outcome = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == name)
            .map(gandr_surface_lowering::LoweredDeclaration::outcome)
    };
    assert!(
        matches!(
            outcome("two"),
            Some(DeclarationOutcome::Refused(LoweringRefusal::UnlockedDependency { span, alias: named }))
                if named.as_ref() == "hello" && span == bytes(alias, alias + "hello".len())
        ),
        "the use is refused at the alias: {:?}",
        outcome("two")
    );
    assert!(
        !matches!(outcome("one"), Some(DeclarationOutcome::Refused(_)) | None),
        "a declaration reading nothing through the alias stands: {:?}",
        outcome("one")
    );
}

/// #3098: an import written at a signature naming fewer members than its
/// source exports settles, and binds the signature's members and no other:
/// a member the source exports and the signature does not state is no
/// member of the import, qualified or not.
#[test]
fn an_import_at_a_narrower_signature_settles_3098()
{
    let pbg = grammar();
    let exported = include_str!(
        "namespace/fixtures/an-import-at-a-narrower-signature-settles-3098-exported.gandr"
    );
    let theory = "theory Greeting where { oper welcome : String ; }\n";
    let outcomes = |importer: &str| {
        let (text, unit) = laid(&[
            (SourceText::from(exported), &[]),
            (SourceText::from(importer), &[ImportTarget::Source(
                SourceIndex::from(0_usize),
            )]),
        ]);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        module
            .declarations()
            .iter()
            .skip(2)
            .map(|declaration| {
                let refused = if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                    if let LoweringRefusal::UnknownMember { member, .. } = refusal {
                        Some(format!("UnknownMember {member}"))
                    }
                    else {
                        Some(format!("{refusal:?}"))
                    }
                }
                else {
                    None
                };
                (String::from(declaration.name().as_ref()), refused)
            })
            .collect::<Vec<_>>()
    };

    let qualified = outcomes(&format!(
        include_str!(
            "namespace/unformatted/an-import-at-a-narrower-signature-settles-3098-qualified.gandr"
        ),
        theory = theory
    ));
    assert!(
        matches!(
            qualified.as_slice(),
            [.., (greeting, None), (one, None), (two, Some(refused))]
                if greeting == "Greeting" && one == "one" && two == "two"
                    && refused == "UnknownMember count"
        ),
        "the signature's member reads and the source's other export is no member: \
         {qualified:?}"
    );

    let unqualified = outcomes(&format!(
        include_str!(
            "namespace/unformatted/an-import-at-a-narrower-signature-settles-3098-unqualified.gandr"
        ),
        theory = theory
    ));
    assert!(
        matches!(
            unqualified.as_slice(),
            [.., (one, None), (two, Some(_))] if one == "one" && two == "two"
        ),
        "an unqualified import at a signature binds its members alone: {unqualified:?}"
    );
}

/// #3098: an import written at a signature its source does not answer
/// refuses every declaration of the importing source at the signature,
/// naming the member: one the source exports no `pub` declaration of, one it
/// exports at another type, and one whose declaration writes no type.
#[test]
fn an_import_at_a_wider_signature_refuses_its_source_3098()
{
    let pbg = grammar();
    let exported = include_str!(
        "namespace/fixtures/an-import-at-a-wider-signature-refuses-its-source-3098-exported.gandr"
    );
    let refused = |members: &str| {
        let importer = format!(
            include_str!(
                "namespace/unformatted/an-import-at-a-wider-signature-refuses-its-source-3098-importer.gandr"
            ),
            members = members
        );
        let (text, unit) = laid(&[
            (SourceText::from(exported), &[]),
            (SourceText::from(importer.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ]),
        ]);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        let at = text.rfind("Wanted ;").expect("the signature is written");
        module
            .declarations()
            .iter()
            .skip(3)
            .map(|declaration| {
                if let DeclarationOutcome::Refused(LoweringRefusal::SignatureMismatch {
                    span,
                    signature,
                    member,
                    fault,
                    ..
                }) = declaration.outcome()
                    && span == bytes(at, at + "Wanted".len())
                    && signature.as_ref() == "Wanted"
                {
                    Some((String::from(member.as_ref()), fault))
                }
                else {
                    None
                }
            })
            .collect::<Vec<_>>()
    };

    for (members, member, fault) in [
        (
            "oper welcome : String ; oper extra : String ;",
            "extra",
            MatchFault::Missing,
        ),
        ("oper hidden : String ;", "hidden", MatchFault::Missing),
        ("oper welcome : Integer ;", "welcome", MatchFault::Sort),
        ("oper bare : String ;", "bare", MatchFault::Unstated),
    ] {
        let found = refused(members);
        assert!(
            !found.is_empty()
                && found.iter().all(|refusal| refusal
                    .as_ref()
                    .is_some_and(|&(ref named, faulted)| named == member && faulted == fault)),
            "`{members}` refuses every declaration of the importer at the signature, naming \
             `{member}` as {fault:?}: {found:?}"
        );
    }
}

/// The signatures the translation tests read a source at and through.
const VERSIONS: &str = include_str!("namespace/unformatted/versions.gandr");

/// The newer source the translation tests import.
const NEWER: &str = include_str!("namespace/unformatted/newer.gandr");

/// What the translation tests read of one declaration's outcome.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Seen
{
    /// Not refused.
    Settled,
    /// Refused `NotATranslation` at these bytes, naming this flow.
    Untranslated(ByteSpan, String),
    /// Refused `SignatureMismatch` at these bytes, naming this theory and
    /// this member, with how.
    Mismatched(ByteSpan, String, String, MatchFault),
    /// Refused otherwise, as debugged.
    Other(String),
}

/// The text `importer` is laid in after `exported`, which it imports, and
/// each declaration's name with what its outcome is seen as.
///
/// # Specification
/// trivial.
fn translated(
    pbg: &Pbg,
    exported: SourceText<'_>,
    importer: SourceText<'_>,
) -> (String, Vec<(String, Seen)>)
{
    let (text, unit) = laid(&[
        (exported, &[]),
        (importer, &[ImportTarget::Source(SourceIndex::from(
            0_usize,
        ))]),
    ]);
    let module = lowered_unit(pbg, &parsed(pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let found = module
        .declarations()
        .iter()
        .map(|declaration| {
            let seen = if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                if let LoweringRefusal::NotATranslation { span, name, .. } = refusal {
                    Seen::Untranslated(span, String::from(name.as_ref()))
                }
                else if let LoweringRefusal::SignatureMismatch {
                    span,
                    signature,
                    member,
                    fault,
                    ..
                } = refusal
                {
                    Seen::Mismatched(
                        span,
                        String::from(signature.as_ref()),
                        String::from(member.as_ref()),
                        fault,
                    )
                }
                else {
                    Seen::Other(format!("{refusal:?}"))
                }
            }
            else {
                Seen::Settled
            };
            (String::from(declaration.name().as_ref()), seen)
        })
        .collect();
    (text, found)
}

/// #3378: an import read through a flow binds its signature's members from
/// the flow's definitions over its source, qualified or not: a renaming binds
/// the source's own declaration, adding no constant, and any other member is
/// the importer's own declaration.
#[test]
fn an_import_via_a_flow_reads_its_source_through_it_3378()
{
    let pbg = grammar();
    let flow = "flow downgrade : Newer ~~> Older where { def answer = reply ; def tag = 9 ; }\n";
    for reads in [
        include_str!(
            "namespace/fixtures/an-import-via-a-flow-reads-its-source-through-it-3378-2.gandr"
        ),
        include_str!(
            "namespace/fixtures/an-import-via-a-flow-reads-its-source-through-it-3378-1.gandr"
        ),
    ] {
        let (_, found) = translated(
            &pbg,
            SourceText::from(NEWER),
            SourceText::from([VERSIONS, flow, reads].concat().as_str()),
        );
        assert!(
            found.iter().all(|&(_, ref seen)| *seen == Seen::Settled),
            "every declaration settles: {found:?}"
        );
        let named = |wanted: &str| {
            found
                .iter()
                .filter(|&&(ref name, _)| name == wanted)
                .count()
        };
        assert!(
            named("answer") == 0 && named("tag") == 1 && named("relayed") == 1,
            "the renaming `answer` declares nothing, and `tag` its one image: {found:?}"
        );
    }
}

/// #3498: an importer reads each declaration of its source as its import
/// binds it. Under an alias, the declaration's path follows the alias.
/// Through a flow, the member's name stands for the declaration that the
/// flow binds to it, after the alias where the import writes one. An
/// unqualified import reads every declaration by its own path.
#[test]
fn an_importer_reads_a_declaration_as_its_import_binds_it_3498()
{
    let pbg = grammar();
    let flow = "flow downgrade : Newer ~~> Older where { def answer = reply ; def tag = 9 ; }\n";
    let flowed = |import: &str| [VERSIONS, flow, import].concat();
    for (importer, expected) in [
        (
            String::from(include_str!(
                "namespace/fixtures/an-importer-reads-a-declaration-as-its-import-binds-it-3498-1.gandr"
            )),
            &[("label", "base.*"), ("reply", "base.*")][..],
        ),
        (
            flowed(include_str!(
                "namespace/fixtures/an-importer-reads-a-declaration-as-its-import-binds-it-3498-2.gandr"
            )),
            &[("reply", "old.answer"), ("tag", "old.tag")][..],
        ),
        (
            flowed(include_str!(
                "namespace/fixtures/an-importer-reads-a-declaration-as-its-import-binds-it-3498-3.gandr"
            )),
            &[("reply", "answer"), ("tag", "tag")][..],
        ),
        (
            String::from(include_str!(
                "namespace/fixtures/an-importer-reads-a-declaration-as-its-import-binds-it-3498-4.gandr"
            )),
            &[][..],
        ),
    ] {
        let (text, unit) = laid(&[
            (SourceText::from(NEWER), &[]),
            (SourceText::from(importer.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ]),
        ]);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        let mut found: Vec<(String, String)> = module
            .reads(SourceIndex::from(1_usize))
            .filter_map(|(constant, read)| {
                let declared = module
                    .declarations()
                    .iter()
                    .find(|declaration| declaration.constant() == constant)?;
                let written = match read {
                    ReadAs::Under(under) => format!("{}.*", under.as_ref()),
                    ReadAs::Member { under, member } => {
                        format!("{}.{}", under.as_ref(), member.as_ref())
                    },
                    ReadAs::Opened(member) => String::from(member.as_ref()),
                };
                Some((String::from(declared.name().as_ref()), written))
            })
            .collect();
        found.sort();
        let expected: Vec<(String, String)> = expected
            .iter()
            .map(|&(name, written)| (String::from(name), String::from(written)))
            .collect();
        assert_eq!(found, expected, "`{importer}`");
    }
}

/// #3378: a `via` reads the flow of its name declared before the import in
/// the importer, or one the imported source declares `pub`; any other name is
/// refused at the `via`, every declaration of the importer with it.
#[test]
fn a_via_reads_a_flow_declared_before_it_or_published_by_its_source_3378()
{
    let pbg = grammar();
    let flow =
        "flow downgrade : Newer ~~> Older where { def answer = reply ; def tag = label ; }\n";
    let import = "import \"./base.gandr\" as old : Older via downgrade ;\n";
    let read = include_str!(
        "namespace/fixtures/a-via-reads-a-flow-declared-before-it-or-published-by-its-source-3378-read.gandr"
    );
    let refusals = |exported: &str, importer: &str| {
        let (text, found) =
            translated(&pbg, SourceText::from(exported), SourceText::from(importer));
        let at = text.rfind("downgrade ;").expect("the via is written");
        let named =
            Seen::Untranslated(bytes(at, at + "downgrade".len()), String::from("downgrade"));
        let untranslated = found
            .iter()
            .filter(|&&(_, ref seen)| *seen == named)
            .count();
        let others = found
            .iter()
            .filter(|&&(_, ref seen)| *seen != named && *seen != Seen::Settled)
            .count();
        (untranslated, others)
    };
    let published = [VERSIONS, NEWER, include_str!("namespace/fixtures/a-via-reads-a-flow-declared-before-it-or-published-by-its-source-3378-published.gandr"), flow].concat();
    assert_eq!(
        refusals(&published, &[VERSIONS, import, read].concat()),
        (0_usize, 0_usize),
        "a flow the source publishes translates it"
    );
    let private = [VERSIONS, NEWER, "\n", flow].concat();
    for (exported, importer) in [
        (private.as_str(), [VERSIONS, import, read].concat()),
        (NEWER, [VERSIONS, import, flow, read].concat()),
        (NEWER, [VERSIONS, import, read].concat()),
    ] {
        let (untranslated, others) = refusals(exported, &importer);
        assert!(
            untranslated > 0 && others == 0,
            "a flow its source keeps private, one declared after the import, and none at all \
             each refuse the importer at the `via`: {untranslated} {others} `{importer}`"
        );
    }
}

/// #3378: an import read through a flow refuses every declaration of its
/// source when the source does not hold the flow's domain, at the flow's
/// name, or the flow's codomain does not hold the signature, at the
/// signature, each naming the member, a declaration reading through the
/// import included.
#[test]
fn a_translation_is_refused_at_its_domain_or_its_codomain_3378()
{
    let pbg = grammar();
    let flow =
        "flow downgrade : Newer ~~> Older where { def answer = reply ; def tag = label ; }\n";
    for (exported, signature, at, (theory, member, fault)) in [
        (
            "pub def reply : Integer = 42 ;",
            "Older",
            "downgrade",
            ("Newer", "label", MatchFault::Missing),
        ),
        (
            include_str!(
                "namespace/fixtures/a-translation-is-refused-at-its-domain-or-its-codomain-3378-1.gandr"
            ),
            "Older",
            "downgrade",
            ("Newer", "reply", MatchFault::Sort),
        ),
        (
            NEWER,
            "Wider",
            "Wider",
            ("Wider", "extra", MatchFault::Missing),
        ),
    ] {
        let importer = [
            VERSIONS,
            "theory Wider where { oper answer : Integer ; oper extra : Integer ; }\n",
            flow,
            &format!(
                include_str!("namespace/unformatted/a-translation-is-refused-at-its-domain-or-its-codomain-3378-2.gandr"), signature = signature
            ),
        ]
        .concat();
        let (text, found) = translated(
            &pbg,
            SourceText::from(exported),
            SourceText::from(importer.as_str()),
        );
        let start = text.rfind(at).expect("the refused name is written");
        let expected = Seen::Mismatched(
            bytes(start, start + at.len()),
            String::from(theory),
            String::from(member),
            fault,
        );
        let refused = found
            .iter()
            .filter(|&&(_, ref seen)| *seen != Seen::Settled)
            .collect::<Vec<_>>();
        assert!(
            refused.iter().all(|&&(_, ref seen)| *seen == expected)
                && ["Older", "Newer", "Wider", "one", "read"]
                    .iter()
                    .all(|&name| refused.iter().any(|&&(ref named, _)| named == name)),
            "`{signature} via downgrade` over `{exported}` refuses each declaration of the \
             importer as {expected:?}: {found:?}"
        );
    }
}

/// #3461: an import read through a renaming matches its signature's members
/// against the source's members the renaming reads, binds each under the
/// signature's name, and reads the source's declaration as that name, after
/// the alias where the import writes one. A pair reading no member of the
/// source is refused at the pair, naming the member. A pair giving the name
/// of a member the source keeps is refused at that name.
#[test]
fn an_import_renaming_reads_its_source_s_member_under_the_signature_s_name_3461()
{
    let pbg = grammar();
    let renamed = |import: &str, read: &str| {
        let importer = [
            VERSIONS,
            &format!(
                include_str!(
                    "namespace/unformatted/an-import-renaming-reads-its-source-s-member-under-the-signature-s-name-3461-renamed.gandr"
                ),
                import = import,
                read = read
            ),
        ]
        .concat();
        let (text, unit) = laid(&[
            (SourceText::from(NEWER), &[]),
            (SourceText::from(importer.as_str()), &[
                ImportTarget::Source(SourceIndex::from(0_usize)),
            ]),
        ]);
        let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
            .expect("the unit lowers");
        let refused: Vec<String> = module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                if let DeclarationOutcome::Refused(refusal) = declaration.outcome() {
                    Some(format!("{refusal:?}"))
                }
                else {
                    None
                }
            })
            .collect();
        let mut reads: Vec<(String, String)> = module
            .reads(SourceIndex::from(1_usize))
            .filter_map(|(constant, read)| {
                let declared = module
                    .declarations()
                    .iter()
                    .find(|declaration| declaration.constant() == constant)?;
                let written = match read {
                    ReadAs::Under(under) => format!("{}.*", under.as_ref()),
                    ReadAs::Member { under, member } => {
                        format!("{}.{}", under.as_ref(), member.as_ref())
                    },
                    ReadAs::Opened(member) => String::from(member.as_ref()),
                };
                Some((String::from(declared.name().as_ref()), written))
            })
            .collect();
        reads.sort();
        (refused, reads)
    };
    let owned = |pairs: &[(&str, &str)]| -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|&(name, written)| (String::from(name), String::from(written)))
            .collect()
    };
    assert_eq!(
        renamed(" as old", "old.answer"),
        (
            Vec::new(),
            owned(&[("label", "old.tag"), ("reply", "old.answer")])
        ),
        "an aliased import reads each source declaration under the name it is renamed to"
    );
    assert_eq!(
        renamed("", "answer"),
        (Vec::new(), owned(&[("label", "tag"), ("reply", "answer")])),
        "an unqualified import binds each renamed member bare"
    );

    let refusals = |renaming: &str| {
        let importer = [
            VERSIONS,
            &format!(
                include_str!(
                    "namespace/unformatted/an-import-renaming-reads-its-source-s-member-under-the-signature-s-name-3461-refused.gandr"
                ),
                renaming = renaming
            ),
        ]
        .concat();
        let (text, found) = translated(
            &pbg,
            SourceText::from(NEWER),
            SourceText::from(importer.as_str()),
        );
        let refused: Vec<Seen> = found
            .into_iter()
            .filter(|&(_, ref seen)| *seen != Seen::Settled)
            .map(|(_, seen)| seen)
            .collect();
        (text, refused)
    };
    let (text, refused) = refusals("reply as answer, lost as tag");
    let at = text.rfind("lost").expect("the pair is written");
    assert!(
        !refused.is_empty()
            && refused.iter().all(|seen| *seen
                == Seen::Mismatched(
                    bytes(at, at + "lost".len()),
                    String::from("Older"),
                    String::from("lost"),
                    MatchFault::Missing
                )),
        "a pair reading no member refuses the importer at it: {refused:?}"
    );
    let (_, refused) = refusals("reply as label");
    assert!(
        refused.iter().any(|seen| matches!(
            *seen,
            Seen::Other(ref refusal) if refusal.contains("DuplicateDefinition")
        )),
        "a pair giving a name the source keeps for a member of its own is refused: {refused:?}"
    );
}

#[test]
fn a_constructor_an_import_binds_again_refuses_its_family()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from("pub data Bit : Type where { | O : Bit | I : Bit }"),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-constructor-an-import-binds-again-refuses-its-family.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<(String, String)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { name, .. }) =
                declaration.outcome()
            {
                Some((
                    String::from(declaration.name().as_ref()),
                    String::from(name.as_ref()),
                ))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([(String::from("Other"), String::from("O"))]),
        "the importer's family is refused at its constructor `O`, which the base binds"
    );
}

#[test]
fn a_declaration_an_import_binds_again_is_refused()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-declaration-an-import-binds-again-is-refused.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let refused: Vec<(String, ByteSpan)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            if let DeclarationOutcome::Refused(LoweringRefusal::ImportShadows { other, .. }) =
                declaration.outcome()
            {
                Some((String::from(declaration.name().as_ref()), other))
            }
            else {
                None
            }
        })
        .collect();
    assert_eq!(
        refused,
        Vec::from([(String::from("one"), bytes(8_usize, 11_usize))]),
        "the importer's `one` is refused, naming the base's; `two` stands"
    );
}

/// #596: one attributed form written byte for byte in two sources of a
/// unit — its documentation apart, which no key reads — is keyed apart by
/// its source, so each declaration reads its own attribute and its own
/// documentation.
#[test]
fn one_form_in_two_sources_files_its_attributes_apart_596()
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/one-form-in-two-sources-files-its-attributes-apart-596-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/one-form-in-two-sources-files-its-attributes-apart-596-2.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/one-form-in-two-sources-files-its-attributes-apart-596-3.gandr"
            )),
            &[ImportTarget::Source(SourceIndex::from(0_usize))],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");

    let keys: Vec<_> = module
        .declarations()
        .iter()
        .filter(|declaration| declaration.name().as_ref() == "two")
        .filter_map(|declaration| match declaration.signature() {
            Maybe::Present(key) => Some(key),
            Maybe::Absent(_) => None,
        })
        .collect();
    let &[left, right] = keys.as_slice()
    else {
        panic!("each source declares its own `two`: {keys:?}");
    };
    assert_eq!(
        left.form(),
        right.form(),
        "the two forms are one form byte for byte"
    );
    assert_eq!(
        (left.source(), right.source()),
        (SourceIndex::from(1_usize), SourceIndex::from(2_usize)),
        "each key names the source holding its form"
    );
    for key in [left, right] {
        assert_eq!(
            module.attributes().entries(key).len(),
            1_usize,
            "each declaration reads its own `checks` alone"
        );
    }
    let documented = |key| match module.documentation(key) {
        Maybe::Present(documentation) => format!("{documentation:?}"),
        Maybe::Absent(_) => String::new(),
    };
    assert!(
        documented(left).contains("The left two.") && documented(right).contains("The right two."),
        "each declaration keeps its own documentation"
    );
}

/// The unit text of `sources` laid end to end, one newline apart, and the
/// unit that says where each starts and what its path imports name.
///
/// # Specification
/// - requires: each source imports only earlier ones.
/// - ensures: each source starts one byte after the one before it ends.
/// - provides: a several-source fixture.
/// - fails: never.
/// - panics: when a source imports a later one.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses resolve across the sources it lays.
/// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
#[spec(
        ensures: |ret| ret.1.sources().len() == sources.len()
            && sources.iter().all(|&(source, _)| ret.0.contains(<&str>::from(source))),
    )]
fn laid(sources: &[(SourceText<'_>, &[ImportTarget])]) -> (String, Unit)
{
    let mut text = String::new();
    let mut laid = Vec::with_capacity(sources.len());
    for &(source, imports) in sources {
        if !text.is_empty() {
            text.push('\n');
        }
        laid.push(UnitSource::new(
            ByteOffset::from(text.len()),
            imports.to_vec(),
        ));
        text.push_str(<&str>::from(source));
    }
    let unit = Unit::new(laid).expect("each source imports an earlier one");
    (text, unit)
}

/// `tree`, molded over the text `unit` lays out, lowered under `pbg`.
///
/// # Specification
/// - requires: `tree` was parsed from the text [`laid`] made with `unit`.
/// - ensures: as [`lowered`], over the unit.
/// - provides: the several-source lowering fixture.
/// - fails: preserves the lowering's refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses of [`laid`].
/// - witness: `tests::namespace::an_unqualified_import_answers_a_name_its_source_declares`
#[spec(
        ensures: |ret| matches!(ret, Err(LoweringRefusal::GrammarMismatch { .. })) == (tree.grammar() != pbg.fingerprint()),
    )]
fn lowered_unit<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    unit: &Unit,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    let mut arena = CoreArena::new();
    lower_unit(
        pbg,
        tree,
        unit,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
        &mut Decisions::none(),
    )
}

/// #1798: the second import of one alias is refused alone, so the rest of
/// the source lowers against the first and the attribute block before the
/// second import states its refusal.
#[test]
fn duplicate_source_import_alias_becomes_a_refusal()
{
    let pbg = grammar();
    let module = lowered(
        &pbg,
        &parsed(
            &pbg,
            SourceText::from(include_str!(
                "namespace/unformatted/duplicate-source-import-alias-becomes-a-refusal-module.gandr"
            )),
        ),
    )
    .expect("a second import of one alias refuses that import, not the module");
    let first = bytes(0_usize, 43_usize);
    let refused: Vec<(String, DeclarationOutcome<'_>)> = module
        .declarations()
        .iter()
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                declaration.outcome(),
            )
        })
        .filter(|entry| matches!(entry.1, DeclarationOutcome::Refused(_)))
        .collect();
    assert_eq!(
        refused,
        Vec::from([(
            String::from("import"),
            DeclarationOutcome::Refused(LoweringRefusal::DuplicateImportAlias {
                span: bytes(44_usize, 86_usize),
                alias: SurfaceName::from("parse"),
                first,
            })
        )]),
        "the second import is refused alone, naming the first, and `x` lowers"
    );
    assert_eq!(
        module
            .imports()
            .iter()
            .map(ImportDeclaration::span)
            .collect::<Vec<_>>(),
        Vec::from([first]),
        "the first import keeps its alias"
    );
}

/// Each importer reads its base by one route, and the last reads nothing: the
/// imports read through are the reached ones, the last alone is not.
#[test]
fn each_import_a_name_is_read_through_is_reached()
{
    let pbg = grammar();
    let on = |source: usize| [ImportTarget::Source(SourceIndex::from(source))];
    let (first, fourth) = (on(0_usize), on(4_usize));
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-2.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-3.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-4.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-5.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-6.gandr"
            )),
            &fourth,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-7.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-8.gandr"
            )),
            &first,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/each-import-a-name-is-read-through-is-reached-9.gandr"
            )),
            &first,
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let refused: Vec<String> = module
        .declarations()
        .iter()
        .filter(|declaration| matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
        .map(|declaration| String::from(declaration.name().as_ref()))
        .collect();
    assert_eq!(refused, Vec::<String>::new(), "every importer lowers");
    let imports: Vec<ByteSpan> = module
        .imports()
        .iter()
        .map(ImportDeclaration::span)
        .collect();
    let (idle, read) = imports.split_last().expect("the importers import");
    assert_eq!(
        module.reached_imports(),
        read,
        "a value, a constructor, a type head, a module member, one through an import of an \
         import, an aliased member and a method each reach the import they are read through"
    );
    assert!(
        !module.reached_imports().contains(idle),
        "an import nothing is read through is not reached"
    );
}

/// #6270: a parameter over a name an import answers keeps the imported
/// declaration it hides and reaches no import. A parameter over a name two
/// imports answer hides nothing, and its declaration is not refused.
#[test]
fn a_shadowing_binder_hides_an_import_and_reaches_none_6270()
{
    let pbg = grammar();
    let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/an-unqualified-import-answers-a-name-its-source-declares-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-shadowing-binder-hides-an-import-and-reaches-none-6270.gandr"
            )),
            &[on(0_usize)],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let end = text
        .find("hides(one")
        .expect("the parameter is written")
        .saturating_add("hides(one".len());
    let binder = ByteSpan::new(
        ByteOffset::from(end.saturating_sub("one".len())),
        ByteOffset::from(end),
    )
    .expect("the parameter is a span");
    let one = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name().as_ref() == "one")
        .map(LoweredDeclaration::constant)
        .expect("the base declares `one`");
    assert_eq!(
        module.shadows(),
        [Shadow {
            binder,
            hidden: Resolution::Declaration(one),
        }]
        .as_slice(),
        "the parameter hides the declaration the import answers"
    );
    assert!(
        module.reached_imports().is_empty(),
        "and no import is reached: only the parameter is read"
    );

    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/two-imports-binding-one-name-refuse-its-use-2.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-shadowing-binder-hides-an-import-and-reaches-none-6270-both.gandr"
            )),
            &[on(0_usize), on(1_usize)],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    assert!(
        module.shadows().is_empty(),
        "a parameter over a name two imports answer hides nothing"
    );
    assert!(
        module
            .declarations()
            .iter()
            .all(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_))),
        "and its declaration lowers"
    );
}

/// #4797: a source reads a module's value and type components through its
/// import, though a source laid before it in the unit, which it does not
/// import, declares a module of the same name with neither. A third source
/// reads the module through the same import first, as a walk's component
/// lays them. The base's private module refuses its importer as unexported,
/// and a source importing the importer reads the base's module through it.
#[test]
fn a_module_path_reads_the_module_its_source_sees_4797()
{
    let pbg = grammar();
    let on = |sources: &[usize]| {
        sources
            .iter()
            .map(|&source| ImportTarget::Source(SourceIndex::from(source)))
            .collect::<Vec<_>>()
    };
    let (both, shared, base, reader) = (
        on(&[0_usize, 1_usize]),
        on(&[0_usize]),
        on(&[1_usize]),
        on(&[4_usize]),
    );
    let (text, unit) = laid(&[
        (SourceText::from("def shared : Integer = 0;\n"), &[]),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-reads-the-module-its-source-sees-4797-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-reads-the-module-its-source-sees-4797-2.gandr"
            )),
            &both,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-reads-the-module-its-source-sees-4797-3.gandr"
            )),
            &shared,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-reads-the-module-its-source-sees-4797-4.gandr"
            )),
            &base,
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-module-path-reads-the-module-its-source-sees-4797-5.gandr"
            )),
            &reader,
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let refused: Vec<(String, bool)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let DeclarationOutcome::Refused(refusal) = declaration.outcome()
            else {
                return None;
            };
            Some((
                String::from(declaration.name().as_ref()),
                matches!(refusal, LoweringRefusal::UnexportedName { .. }),
            ))
        })
        .collect();
    assert_eq!(
        refused,
        [(String::from("hushed"), true)],
        "`read` and `far` read the base's modules past the later source's, and `hushed` is \
         refused the base's private module, not sent to the later source's"
    );
}

/// #6174: a theory that an imported source exports is a value where a type
/// reads one. `shapeOf(M.Shape)` lowers as `shapeOf(Small)` does for a local
/// theory. A path that names no member of `M` is refused by name.
#[test]
fn a_theory_an_import_exports_is_a_value_in_a_type_6174()
{
    let pbg = grammar();
    let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
    let (text, unit) = laid(&[
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-theory-an-import-exports-is-a-value-in-a-type-6174-1.gandr"
            )),
            &[],
        ),
        (
            SourceText::from(include_str!(
                "namespace/fixtures/a-theory-an-import-exports-is-a-value-in-a-type-6174-2.gandr"
            )),
            &[on(0_usize)],
        ),
    ]);
    let module = lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers");
    let refused: Vec<(String, bool)> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let DeclarationOutcome::Refused(refusal) = declaration.outcome()
            else {
                return None;
            };
            Some((
                String::from(declaration.name().as_ref()),
                matches!(refusal, LoweringRefusal::UnknownMember { .. }),
            ))
        })
        .collect();
    assert_eq!(
        refused,
        [(String::from("absent"), true)],
        "`qualified` reads the imported theory as a value, and `absent` is refused by name"
    );
}

/// The base the visibility witnesses import: each form exported by a `pub`
/// mark on its signature, its definition, before or after its attributes, and
/// each kept private by none.
const VISIBLE_BASE: &str = include_str!("namespace/fixtures/visible-base.gandr");

/// Each declaration of the unit `base` then `importer` lays, the importer
/// reading the base unqualified, with its refusal printed, or `None` where it
/// stands.
///
/// # Specification
/// trivial.
fn importer_outcomes(importer: SourceText<'_>) -> Vec<(String, Option<String>)>
{
    let pbg = grammar();
    let (text, unit) = laid(&[
        (SourceText::from(VISIBLE_BASE), &[]),
        (importer, &[ImportTarget::Source(SourceIndex::from(
            0_usize,
        ))]),
    ]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(gandr_surface_lowering::UnitSource::start)
        .expect("the importer is the second source");
    lowered_unit(&pbg, &parsed(&pbg, SourceText::from(text.as_str())), &unit)
        .expect("the unit lowers")
        .declarations()
        .iter()
        .filter(|declaration| declaration.span().start() >= start)
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                match declaration.outcome() {
                    DeclarationOutcome::Refused(refusal) => Some(format!("{refusal:?}")),
                    DeclarationOutcome::Completed { .. }
                    | DeclarationOutcome::Bodied { .. }
                    | DeclarationOutcome::Uncompleted { .. }
                    | DeclarationOutcome::Data(_)
                    | DeclarationOutcome::Codata(_)
                    | DeclarationOutcome::Abstract(_)
                    | DeclarationOutcome::World => None,
                },
            )
        })
        .collect()
}

/// #2687: a declaration a `pub` mark precedes is read by a source importing
/// its own — the mark on its signature or on its definition, before its
/// attributes or after them — as are a marked family's constructors, a
/// marked theory, a marked module's members and its methods.
#[test]
fn a_pub_declaration_is_read_by_its_importer_2687()
{
    let outcomes = importer_outcomes(SourceText::from(include_str!(
        "namespace/fixtures/a-pub-declaration-is-read-by-its-importer-2687-outcomes.gandr"
    )));
    let refused: Vec<_> = outcomes
        .iter()
        .filter(|&&(_, ref refusal)| refusal.is_some())
        .collect();
    assert_eq!(
        refused,
        Vec::<&(String, Option<String>)>::new(),
        "every exported form reads through the import"
    );
}

/// #2687: a declaration no `pub` mark precedes is private to its source. A
/// value, a family and its constructor, a module's member and a theory an
/// importer names are each refused as unexported at the use, naming the
/// declaration; a private module's method is out of scope; and a private
/// name binds nothing in the importer, which declares it again freely.
#[test]
fn a_private_declaration_is_refused_to_its_importer_2687()
{
    let outcomes = importer_outcomes(SourceText::from(include_str!(
        "namespace/fixtures/a-private-declaration-is-refused-to-its-importer-2687-outcomes.gandr"
    )));
    let private = |name: &str| format!("name: SurfaceName(SourceFragment(\"{name}\"))");
    let refused_as = |declaration: &str, name: &str| {
        outcomes.iter().any(|&(ref held, ref refusal)| {
            held == declaration
                && refusal.as_deref().is_some_and(|refusal| {
                    refusal.starts_with("UnexportedName")
                        && refusal.contains(&private(name))
                        && refusal.ends_with("reason: Private }")
                })
        })
    };
    for (declaration, name) in [
        ("g", "secret"),
        ("h", "Hid"),
        ("i", "H"),
        ("j", "Shut"),
        ("Closing", "Closed"),
    ] {
        assert!(
            refused_as(declaration, name),
            "`{declaration}` is refused at the private `{name}`: {outcomes:?}"
        );
    }
    assert!(
        outcomes
            .iter()
            .any(|&(ref held, ref refusal)| held == "k" && refusal.is_none()),
        "the private module's `width` is out of scope, so the exported one's is called alone: \
         {outcomes:?}"
    );
    assert!(
        outcomes
            .iter()
            .any(|&(ref held, ref refusal)| held == "secret" && refusal.is_none()),
        "the private `secret` binds nothing in the importer: {outcomes:?}"
    );
}

/// #2687: a `pub` mark exports the declaration after it and stands nowhere
/// else: before an import, before another mark and at the end of a source it
/// is refused as misplaced, at the mark.
#[test]
fn a_pub_mark_before_no_declaration_is_misplaced_2687()
{
    let pbg = grammar();
    let text = include_str!(
        "namespace/unformatted/a-pub-mark-before-no-declaration-is-misplaced-2687.gandr"
    );
    let module = lowered(&pbg, &parsed(&pbg, SourceText::from(text))).expect("the source lowers");
    let misplaced: Vec<ByteSpan> = module
        .declarations()
        .iter()
        .filter_map(|declaration| match declaration.outcome() {
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment {
                span,
                form,
                boundary: FragmentBoundary::Misplaced,
                ..
            }) if form == FormName::VISIBILITY => Some(span),
            DeclarationOutcome::Refused(_)
            | DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World => None,
        })
        .collect();
    let at = |offset: usize| bytes(offset, offset + "pub".len());
    assert_eq!(
        misplaced,
        [at(0_usize), at(28_usize), at(50_usize)],
        "the mark before the import, the first of two and the last are each misplaced"
    );
}

/// #3495: a `pub` mark before a word that strays yields to the word's own
/// refusal: `pub de answer = 42 ;` misspells `def`, and the source is refused
/// at `de`, as it is with no mark, not at the mark the stray leaves bare.
#[test]
fn a_mark_before_a_stray_word_yields_to_the_word_3495()
{
    let pbg = grammar();
    for (text, word) in [
        ("pub de answer = 42 ;\n", bytes(4_usize, 6_usize)),
        ("de answer = 42 ;\n", bytes(0_usize, 2_usize)),
    ] {
        let refused = lowered(&pbg, &parsed(&pbg, SourceText::from(text)))
            .expect_err("a source declaring nothing is refused whole");
        assert!(
            matches!(
                refused,
                LoweringRefusal::OutOfFragment {
                    span,
                    boundary: FragmentBoundary::TopLevel,
                    ..
                } if span == word
            ),
            "{text:?} is refused at the stray word: {refused:?}"
        );
    }
}

/// #2687: documentation written before a `pub` mark documents the declaration
/// the mark exports, as it does with no mark, and joins the documentation of
/// an attribute block after the mark in source order.
#[test]
fn documentation_before_a_pub_mark_documents_its_declaration_2687()
{
    let pbg = grammar();
    let text = include_str!(
        "namespace/fixtures/documentation-before-a-pub-mark-documents-its-declaration-2687.gandr"
    );
    let module = lowered(&pbg, &parsed(&pbg, SourceText::from(text))).expect("the source lowers");
    let documented = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == name)
            .and_then(
                |declaration| match module.documentation(declaration.introduced()) {
                    Maybe::Present(documentation) => Some(format!("{:?}", documentation.text())),
                    Maybe::Absent(_) => None,
                },
            )
    };
    assert_eq!(
        [
            documented("answer"),
            documented("Point"),
            documented("both")
        ],
        [
            Some(String::from("DocumentationText(\"The answer.\")")),
            Some(String::from("DocumentationText(\"A point.\")")),
            Some(String::from("DocumentationText(\"First.\\nSecond.\")")),
        ],
        "each marked declaration reads the documentation before its mark"
    );
}

/// #4947: a `//!` run before the first declaration documents the source
/// alone. A `pub` mark on that declaration carries only its `///` run.
#[test]
fn a_source_s_own_documentation_stays_off_its_marked_declaration_4947()
{
    let pbg = grammar();
    let text = include_str!(
        "namespace/fixtures/a-source-s-own-documentation-stays-off-its-marked-declaration-4947.gandr"
    );
    let module = lowered(&pbg, &parsed(&pbg, SourceText::from(text))).expect("the source lowers");
    let answer = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name().as_ref() == "answer")
        .expect("`answer` is declared");
    let read =
        |documentation: Maybe<&gandr_surface_lowering::Documentation<'_>, _>| match documentation {
            Maybe::Present(documentation) => Some(format!("{:?}", documentation.text())),
            Maybe::Absent(_) => None,
        };
    assert_eq!(
        (
            read(module.documentation(answer.introduced())),
            module
                .source_documentations()
                .values()
                .map(|documentation| format!("{:?}", documentation.text()))
                .collect::<Vec<_>>(),
        ),
        (
            Some(String::from("DocumentationText(\"The answer.\")")),
            vec![String::from("DocumentationText(\"A small source.\")")],
        ),
        "the `//!` run documents the source, and the `///` run the declaration"
    );
}

/// #2687: a document laid after its closure's tree stands under a root of its
/// own, and documentation written before a `pub` mark there still documents
/// the declaration the mark exports, as the editor's hover reads it.
#[test]
fn documentation_before_a_pub_mark_reaches_a_document_laid_after_its_closure_2687()
{
    let pbg = grammar();
    let base = SourceText::from(include_str!(
        "namespace/fixtures/documentation-before-a-pub-mark-reaches-a-document-laid-after-its-closure-2687-base.gandr"
    ));
    let document = SourceText::from(include_str!(
        "namespace/fixtures/documentation-before-a-pub-mark-reaches-a-document-laid-after-its-closure-2687-document.gandr"
    ));
    let imports = [ImportTarget::Source(SourceIndex::from(0_usize))];
    let (text, unit) = laid(&[(base, &[]), (document, &imports)]);
    let start = unit
        .sources()
        .get(1_usize)
        .map(|source| usize::from(source.start()))
        .expect("the document is the second source");
    let closure = ClosureLowering::new(
        Arc::new(grammar()),
        String::from(text.get(.. start).expect("the closure's text")),
        Unit::new(unit.sources().get(.. 1_usize).expect("the base").to_vec())
            .expect("the base alone is a unit"),
        LoweringBudget::DEFAULT,
        Recognition::default(),
        |pbg, closure| parse(pbg, closure).map(ParseResult::into_tree),
    )
    .expect("the closure parses");
    let joined = parse(
        &pbg,
        SourceText::from(text.get(start ..).expect("the document's text")),
    )
    .expect("the document parses")
    .after(closure.tree(), SourceText::from(text.as_str()))
    .expect("the document lays after its closure")
    .into_tree();
    let mut arena = CoreArena::new();
    let module = closure
        .resume(&joined, &unit, &mut arena, &mut Decisions::none())
        .expect("the document lowers resumed");
    let documented = |name: &str| {
        module
            .declarations()
            .iter()
            .find(|declaration| declaration.name().as_ref() == name)
            .and_then(
                |declaration| match module.documentation(declaration.introduced()) {
                    Maybe::Present(documentation) => Some(format!("{:?}", documentation.text())),
                    Maybe::Absent(_) => None,
                },
            )
    };
    assert_eq!(
        [
            documented("base"),
            documented("answer"),
            documented("plain")
        ],
        [
            Some(String::from("DocumentationText(\"The base.\")")),
            Some(String::from("DocumentationText(\"The answer.\")")),
            Some(String::from("DocumentationText(\"Plain.\")")),
        ],
        "a marked declaration in either root reads the documentation before its mark"
    );
}
