//! Recognition through the lowering: the lowering declares every name over
//! the outermost scope and reports every binder against it. The scope's own
//! cases are in the integration target of `gandr-surface-lowering-base`.
//!
//! The seed table here is a test table: the rows a prelude, a host or a
//! session will contribute are not part of the mechanism.
//!
//! The recognition cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Resolution;
use gandr_surface_lowering::Shadow;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_lowering::namespace::PathResolution;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_lowering::namespace::Recognized;
use gandr_surface_lowering::namespace::SeedEntry;
use gandr_surface_lowering::namespace::SeedKind;
use gandr_surface_lowering::namespace::SeedTable;
use gandr_surface_lowering::namespace::ShadowPolicy;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
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
/// - hypothesis: L3 on ordered endpoint fixtures — builtin shadow reports
///   retain the supplied source location under both policies.
/// - witness: `tests::recognition::a_shadowed_builtin_is_reported_as_a_warning`
/// - witness: `tests::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
fn site<Bound>(
    start: Bound,
    end: Bound,
) -> ByteSpan
where
    Bound: Into<ByteOffset>,
{
    ByteSpan::new(start.into(), end.into()).expect("the span is ordered")
}

/// The test seed table: five namespaces with one member each.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the ordered fixture table contains five namespace/member pairs
///   with their distinct seed kinds.
/// - provides: a finite hierarchy for governed-path and shadow-policy
///   witnesses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration over one seeded namespace changes the
///   resolution of that namespace's subtree alone.
/// - witness: `tests::recognition::user_shadowing_is_the_only_observable_delta`
#[spec(
        ensures: |ret| {
            let expected = [
                ("list", SeedKind::Namespace),
                ("list.each", SeedKind::Member),
                ("record", SeedKind::Namespace),
                ("record.get", SeedKind::Member),
                ("prim", SeedKind::Namespace),
                ("prim.id", SeedKind::Member),
                ("string", SeedKind::Namespace),
                ("string.escape", SeedKind::Member),
                ("env", SeedKind::Namespace),
                ("env.get", SeedKind::Member),
            ];
            ret.entries().len() == expected.len()
                && ret
                    .entries()
                    .iter()
                    .zip(expected)
                    .all(|(entry, (spelling, kind))| {
                        entry.kind == kind
                            && entry
                                .path
                                .segments()
                                .iter()
                                .map(AsRef::as_ref)
                                .eq(spelling.split('.'))
                    })
        },
    )]
fn table() -> SeedTable
{
    SeedTable::from(
        [
            ("list", SeedKind::Namespace),
            ("list.each", SeedKind::Member),
            ("record", SeedKind::Namespace),
            ("record.get", SeedKind::Member),
            ("prim", SeedKind::Namespace),
            ("prim.id", SeedKind::Member),
            ("string", SeedKind::Namespace),
            ("string.escape", SeedKind::Member),
            ("env", SeedKind::Namespace),
            ("env.get", SeedKind::Member),
        ]
        .into_iter()
        .map(|(text, kind)| SeedEntry {
            path: path(text),
            kind,
        })
        .collect::<Vec<SeedEntry>>(),
    )
}

/// The outermost scope over [`table`], under `policy`.
///
/// # Specification
/// trivial.
fn seeded(policy: ShadowPolicy) -> Recognition
{
    Recognition::new(&[table()], policy)
}

/// `source` parsed under the built-in grammar and lowered against
/// `outermost`, which must not refuse the module.
///
/// # Specification
/// - requires: the source parses cleanly and the lowering engine accepts it
///   under the supplied recognition context.
/// - ensures: emitted declarations keep source-bounded spans and admission
///   order while preserving the context’s observable policy effects.
/// - provides: a real source-to-core recognition fixture.
/// - fails: declaration-local refusals remain observable in the module.
/// - panics: on parsing, repair or engine refusal.
///
/// # Adequacy
/// - hypothesis: L3 — the same source under warning and rejection policies
///   distinguishes a retained definition from a located shadow refusal.
/// - witness: `tests::recognition::a_shadowed_builtin_is_reported_as_a_warning`
/// - witness: `tests::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
#[spec(
        ensures: |ret| {
            let spelled: &str = source.as_ref();
            ret.declarations()
                .iter()
                .all(|declaration| usize::from(declaration.span().end()) <= spelled.len())
                && ret
                    .declarations()
                    .iter()
                    .zip(ret.declarations().iter().skip(1))
                    .all(|(left, right)| left.constant() < right.constant())
        },
    )]
fn lowered(
    source: SourceText<'_>,
    outermost: Recognition,
) -> LoweredModule<'_>
{
    let pbg = built_in().expect("the built-in grammar builds");
    let parsed = parse(&pbg, source).expect("the parser reads the source");
    assert!(
        bool::from(parsed.is_clean()),
        "the source is one the parser accepts without repair"
    );
    let tree = parsed.into_tree();
    let mut arena = CoreArena::new();
    lower_module(&pbg, &tree, &mut arena, LoweringBudget::DEFAULT, outermost)
        .expect("the module lowers")
}

/// What each declaration of `module` amounts to, in admission order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one outcome per declaration, preserving admission order and every
///   refusal payload.
/// - provides: the semantic outcome sequence used by lowering witnesses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — warning and rejecting policies preserve different
///   declaration outcomes without changing their admission order.
/// - witness: `tests::recognition::user_shadowing_is_the_only_observable_delta`
#[spec(
        ensures: |ret| {
            ret.iter().copied().eq(module
                .declarations()
                .iter()
                .map(LoweredDeclaration::outcome))
        },
    )]
fn outcomes<'source>(module: &LoweredModule<'source>) -> Vec<DeclarationOutcome<'source>>
{
    module
        .declarations()
        .iter()
        .map(LoweredDeclaration::outcome)
        .collect()
}

#[test]
fn a_shadowed_builtin_is_reported_as_a_warning()
{
    let source =
        include_str!("recognition/fixtures/a-shadowed-builtin-is-reported-as-a-warning.gandr");
    let module = lowered(SourceText::from(source), seeded(ShadowPolicy::WarnAndAllow));
    assert_eq!(
        module.recognition().shadowed(),
        [ShadowedBuiltin {
            path: path("list"),
            span: site(4_usize, 8_usize),
        }]
        .as_slice(),
        "one warning, at the shadowing declaration's name"
    );
    assert!(
        outcomes(&module)
            .iter()
            .all(|outcome| !matches!(*outcome, DeclarationOutcome::Refused(_))),
        "warn-and-allow refuses nothing, the declaration using the name included"
    );
}

#[test]
fn a_declaration_shadowing_a_builtin_is_rejected_under_policy()
{
    let source = SourceText::from("def list = 1 ;");
    let allowed = lowered(source, seeded(ShadowPolicy::WarnAndAllow));
    assert!(
        matches!(outcomes(&allowed).as_slice(), [
            DeclarationOutcome::Bodied { .. }
        ]),
        "warn-and-allow lowers the declaration"
    );

    let refused = lowered(source, seeded(ShadowPolicy::Reject));
    assert_eq!(
        outcomes(&refused),
        Vec::from([DeclarationOutcome::Refused(
            LoweringRefusal::ShadowedBuiltin {
                span: site(4_usize, 8_usize),
                name: SurfaceName::from("list"),
            }
        )]),
        "the reject policy refuses the declaration at its name"
    );
    assert!(
        matches!(
            refused.recognition().resolve(&path("list.each")),
            Maybe::Present(_)
        ),
        "and the builtin keeps its name"
    );

    let member = lowered(
        SourceText::from("module M where { def list = 1 ; }"),
        seeded(ShadowPolicy::Reject),
    );
    assert!(
        matches!(outcomes(&member).as_slice(), [
            DeclarationOutcome::Bodied { .. }
        ]),
        "a module's member shadows nothing at the top level, whatever its name: {:?}",
        outcomes(&member)
    );
}

#[test]
fn a_module_or_functor_shadowing_a_builtin_is_rejected_under_policy()
{
    let builtins = || {
        SeedTable::from(Vec::from([SeedEntry {
            path: path("Prim"),
            kind: SeedKind::Namespace,
        }]))
    };
    for (written, at) in [
        ("module Prim where { def x = 1 ; }", site(7_usize, 11_usize)),
        (
            "module Prim(S : *{ x : Integer }) :> *{ y : Integer } where { def y = S.x ; }",
            site(7_usize, 11_usize),
        ),
    ] {
        let source = SourceText::from(written);
        let allowed = lowered(
            source,
            Recognition::new(&[builtins()], ShadowPolicy::WarnAndAllow),
        );
        assert_eq!(
            allowed.recognition().shadowed(),
            [ShadowedBuiltin {
                path: path("Prim"),
                span: at,
            }]
            .as_slice(),
            "`{written}` warns once, at its name"
        );

        let refused = lowered(
            source,
            Recognition::new(&[builtins()], ShadowPolicy::Reject),
        );
        assert!(
            outcomes(&refused).contains(&DeclarationOutcome::Refused(
                LoweringRefusal::ShadowedBuiltin {
                    span: at,
                    name: SurfaceName::from("Prim"),
                }
            )),
            "`{written}` is refused at its name under the reject policy: {:?}",
            outcomes(&refused)
        );
        assert!(
            matches!(
                refused.recognition().resolve(&path("Prim")),
                Maybe::Present(&Recognized::BuiltinNamespace(_))
            ),
            "and the builtin keeps its name"
        );
    }
}

#[test]
fn a_binder_shadowing_a_builtin_is_rejected_under_policy()
{
    for (written, at) in [
        (
            "def x = thunk { fun (list) { return list } } ;",
            site(21_usize, 25_usize),
        ),
        (
            "def f(list : Integer) -> -F Integer { return list }",
            site(6_usize, 10_usize),
        ),
        (
            "def x = thunk { let list = 1 ; return list } ;",
            site(20_usize, 24_usize),
        ),
    ] {
        let warned = lowered(
            SourceText::from(written),
            seeded(ShadowPolicy::WarnAndAllow),
        );
        assert_eq!(
            warned.recognition().shadowed(),
            [ShadowedBuiltin {
                path: path("list"),
                span: at,
            }]
            .as_slice(),
            "a lambda, parameter or `let` binder over a builtin is reported at the binder"
        );
        assert_eq!(
            warned.shadows(),
            [Shadow {
                binder: at,
                hidden: Resolution::Builtin,
            }]
            .as_slice(),
            "and the shadow index keeps the builtin it hides (#6270)"
        );

        let refused = lowered(SourceText::from(written), seeded(ShadowPolicy::Reject));
        assert_eq!(
            outcomes(&refused),
            Vec::from([DeclarationOutcome::Refused(
                LoweringRefusal::ShadowedBuiltin {
                    span: at,
                    name: SurfaceName::from("list"),
                }
            )]),
            "and refuses its declaration under the reject policy"
        );
    }
}

#[test]
fn user_shadowing_is_the_only_observable_delta()
{
    let every_path = || {
        table()
            .entries()
            .iter()
            .map(|seed| seed.path.clone())
            .collect::<Vec<NamePath>>()
    };
    let pristine = seeded(ShadowPolicy::WarnAndAllow);
    let resolved = |recognition: &Recognition| {
        every_path()
            .iter()
            .map(|seeded_path| recognition.resolve_path(seeded_path))
            .collect::<Vec<PathResolution>>()
    };

    let unrelated = lowered(
        SourceText::from("def other = 1 ;"),
        seeded(ShadowPolicy::WarnAndAllow),
    );
    assert_eq!(
        resolved(unrelated.recognition()),
        resolved(&pristine),
        "a declaration over no builtin leaves every seeded path resolving as before"
    );
    assert!(
        unrelated.recognition().shadowed().is_empty(),
        "and reports nothing"
    );

    let shadowing = lowered(
        SourceText::from("def prim = 1 ;"),
        seeded(ShadowPolicy::WarnAndAllow),
    );
    assert_eq!(
        shadowing.recognition().shadowed().len(),
        1_usize,
        "the declaration over `prim` is reported"
    );
    let changed: Vec<NamePath> = every_path()
        .into_iter()
        .filter(|seeded_path| {
            shadowing.recognition().resolve_path(seeded_path) != pristine.resolve_path(seeded_path)
        })
        .collect();
    assert_eq!(
        changed,
        Vec::from([path("prim"), path("prim.id")]),
        "and `prim`'s own subtree is the only change"
    );
    assert_eq!(
        (
            shadowing.recognition().resolve_path(&path("prim")),
            shadowing.recognition().resolve_path(&path("prim.id")),
        ),
        (
            PathResolution::Complete(Recognized::Definition),
            PathResolution::Ungoverned,
        ),
        "`prim` is the user's definition and `prim.id` an ordinary projection on it"
    );
}
