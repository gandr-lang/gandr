//! Recognition as scoped resolution: the outermost scope seeded from ordered
//! tables, and the shadow policy that settles a source name over a builtin.
//! The lowering's own cases are in the integration target of
//! `gandr-surface-lowering`.
//!
//! The seed table here is a test table: the rows a prelude, a host or a
//! session will contribute are not part of the mechanism.
//!
//! The recognition cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use anodized::spec;
use gandr_surface_lowering_base::namespace::Binding;
use gandr_surface_lowering_base::namespace::Declines;
use gandr_surface_lowering_base::namespace::DottedName;
use gandr_surface_lowering_base::namespace::NamePath;
use gandr_surface_lowering_base::namespace::PathResolution;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_lowering_base::namespace::RecognitionSite;
use gandr_surface_lowering_base::namespace::Recognized;
use gandr_surface_lowering_base::namespace::SeedEntry;
use gandr_surface_lowering_base::namespace::SeedKind;
use gandr_surface_lowering_base::namespace::SeedPosition;
use gandr_surface_lowering_base::namespace::SeedTable;
use gandr_surface_lowering_base::namespace::Segment;
use gandr_surface_lowering_base::namespace::SegmentCount;
use gandr_surface_lowering_base::namespace::ShadowPolicy;
use gandr_surface_lowering_base::namespace::ShadowedBuiltin;
use gandr_surface_lowering_base::namespace::Trie;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
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
/// - witness: `tests::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
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
/// - hypothesis: L3 — namespace and member seeds govern different path
///   continuations; reordering or changing kinds changes the observed
///   resolution.
/// - witness: `tests::recognition::a_path_is_governed_by_its_deepest_resolved_prefix`
/// - witness: `tests::recognition::a_declaration_displaces_the_whole_builtin_subtree`
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

/// A one-binding namespace for a source declaration written at `at`.
///
/// # Specification
/// - requires: the span is interpreted as fixture metadata, not an ownership
///   certificate.
/// - ensures: exactly one root binding, recognized as a source definition at
///   the supplied span.
/// - provides: a declaration subtree for shadow-policy witnesses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — source definitions displace builtin subtrees while
///   retaining the source site used by the selected shadow policy.
/// - witness: `tests::recognition::a_declaration_displaces_the_whole_builtin_subtree`
/// - witness: `tests::recognition::shadowing_a_builtin_warns_by_default_and_rejects_under_policy`
#[spec(
        ensures: |ret| {
            usize::from(ret.binding_count()) == 1
                && matches!(ret.get(&NamePath::root()), Maybe::Present(binding) if binding.data == Recognized::Definition && binding.tag == RecognitionSite::Source(at))
        },
    )]
fn declaration(at: ByteSpan) -> Trie<Recognized, RecognitionSite>
{
    let mut namespace = Trie::empty();
    let _fresh = namespace.insert(
        &NamePath::root(),
        Binding::new(Recognized::Definition, RecognitionSite::Source(at)),
    );
    namespace
}

#[test]
fn shadow_policy_uses_site_tags_independently_of_recognized_kinds()
{
    let at = site(4_usize, 8_usize);
    let mut scope = Recognition::new(&[], ShadowPolicy::Reject);
    scope.declare_resumed(
        Segment::from("source"),
        core::iter::once((
            NamePath::root(),
            Binding::new(
                Recognized::BuiltinMember(SeedPosition {
                    table: 0_usize,
                    entry: 0_usize,
                }),
                RecognitionSite::Source(at),
            ),
        ))
        .collect(),
    );
    let root = scope
        .note_binder(Segment::from("source"), at)
        .expect("a source site is not a builtin shadow, regardless of recognized kind");
    assert_eq!(
        root,
        Maybe::Present(RecognitionSite::Source(at)),
        "and the note gives the source site the root holds"
    );
    assert!(scope.shadowed().is_empty());
    scope.declare_resumed(
        Segment::from("builtin"),
        core::iter::once((
            NamePath::root(),
            Binding::new(Recognized::Definition, RecognitionSite::Builtin),
        ))
        .collect(),
    );
    let refused = scope
        .note_binder(Segment::from("builtin"), at)
        .expect_err("the site tag marks a builtin, regardless of recognized kind");
    assert_eq!(refused.path(), &path("builtin"));
    assert_eq!(
        scope.resolve(&path("builtin")),
        Maybe::Present(&Recognized::Definition)
    );
    assert_eq!(
        scope.resolve(&path("source")),
        Maybe::Present(&Recognized::BuiltinMember(SeedPosition {
            table: 0_usize,
            entry: 0_usize
        }))
    );
    assert!(scope.shadowed().is_empty());
}

#[test]
fn root_seeds_do_not_bridge_an_unbound_namespace_prefix()
{
    let seeds = SeedTable::from(Vec::from([
        SeedEntry {
            path: NamePath::root(),
            kind: SeedKind::Namespace,
        },
        SeedEntry {
            path: path("missing.member"),
            kind: SeedKind::Member,
        },
    ]));
    let scope = Recognition::new(&[seeds], ShadowPolicy::WarnAndAllow);
    assert_eq!(
        scope.resolve(&NamePath::root()),
        Maybe::Present(&Recognized::BuiltinNamespace(SeedPosition {
            table: 0_usize,
            entry: 0_usize
        }))
    );
    assert_eq!(
        scope.resolve(&path("missing.member")),
        Maybe::Present(&Recognized::BuiltinMember(SeedPosition {
            table: 0_usize,
            entry: 1_usize
        }))
    );
    assert_eq!(
        scope.resolve_path(&NamePath::root()),
        PathResolution::Ungoverned
    );
    assert_eq!(
        scope.resolve_path(&path("missing.member")),
        PathResolution::Ungoverned
    );
}
#[test]
fn only_governed_namespaces_decline_an_unknown_member()
{
    let position = SeedPosition {
        table: 0_usize,
        entry: 0_usize,
    };
    for kind in [
        Recognized::BuiltinNamespace(position),
        Recognized::ModuleNamespace,
        Recognized::Functor,
    ] {
        assert_eq!(
            kind.declines_unknown_member(),
            Declines(true),
            "a namespace governs its members and declines an unknown one, and a functor \
                 has none to read"
        );
    }
    for kind in [
        Recognized::BuiltinMember(position),
        Recognized::ModuleComponent,
        Recognized::ModuleType,
        Recognized::Definition,
    ] {
        assert_eq!(
            kind.declines_unknown_member(),
            Declines(false),
            "a member, a component or a definition falls through to the ordinary projection"
        );
    }
}

#[test]
fn a_path_is_governed_by_its_deepest_resolved_prefix()
{
    let at = site(0_usize, 8_usize);
    let mut recognition = Recognition::default();
    let mut namespace = Trie::empty();
    for (text, recognized) in [
        ("", Recognized::ModuleNamespace),
        ("cfg", Recognized::ModuleComponent),
        ("inner", Recognized::ModuleNamespace),
        ("inner.answer", Recognized::ModuleComponent),
    ] {
        let _fresh = namespace.insert(
            &path(text),
            Binding::new(recognized, RecognitionSite::Source(at)),
        );
    }
    recognition
        .declare(Segment::from("M"), namespace, at)
        .expect("declaring `M` shadows nothing");

    assert_eq!(
        recognition.resolve_path(&path("M.inner.answer")),
        PathResolution::Complete(Recognized::ModuleComponent),
        "a fully bound nested path resolves completely"
    );
    assert_eq!(
        recognition.resolve_path(&path("M.inner")),
        PathResolution::Complete(Recognized::ModuleNamespace),
        "a nested module is itself a complete resolution"
    );
    assert_eq!(
        recognition.resolve_path(&path("M.nope")),
        PathResolution::UnknownMember {
            depth: SegmentCount::from(1_usize),
            namespace: Recognized::ModuleNamespace,
        },
        "an absent component under a module is governed and declines"
    );
    assert_eq!(
        recognition.resolve_path(&path("M.inner.nope")),
        PathResolution::UnknownMember {
            depth: SegmentCount::from(2_usize),
            namespace: Recognized::ModuleNamespace,
        },
        "the decline follows nesting to the depth that governs"
    );
    assert_eq!(
        recognition.resolve_path(&path("M.cfg.port")),
        PathResolution::Ungoverned,
        "a value component's own fields belong to the record carrier"
    );
    assert_eq!(
        recognition.resolve_path(&path("stranger.nope")),
        PathResolution::Ungoverned,
        "an unbound root is ungoverned, which is what a record projection is"
    );
}

#[test]
fn a_declaration_displaces_the_whole_builtin_subtree()
{
    let mut recognition = seeded(ShadowPolicy::WarnAndAllow);
    assert!(
        matches!(recognition.resolve(&path("list.each")), Maybe::Present(_)),
        "the table seeds `list.each` before the declaration"
    );
    recognition
        .declare(
            Segment::from("list"),
            declaration(site(0_usize, 7_usize)),
            site(0_usize, 7_usize),
        )
        .expect("warn-and-allow accepts the shadow");
    assert!(
        matches!(
            recognition.resolve(&path("list")),
            Maybe::Present(&Recognized::Definition)
        ),
        "the declaration takes the name"
    );
    assert!(
        matches!(recognition.resolve(&path("list.each")), Maybe::Absent(_)),
        "the whole displaced subtree goes with it, so no member is left behind"
    );
    assert!(
        matches!(recognition.resolve(&path("prim.id")), Maybe::Present(_)),
        "an unrelated namespace is untouched"
    );
}

#[test]
fn shadowing_a_builtin_warns_by_default_and_rejects_under_policy()
{
    let at = site(4_usize, 10_usize);
    let mut warning = Recognition::new(&[table()], ShadowPolicy::default());
    warning
        .declare(Segment::from("record"), declaration(at), at)
        .expect("warn-and-allow accepts");
    assert_eq!(
        warning.shadowed(),
        [ShadowedBuiltin {
            path: path("record"),
            span: at,
        }]
        .as_slice(),
        "warn-and-allow is the default and records exactly one event, at the declaration"
    );

    let mut rejecting = seeded(ShadowPolicy::Reject);
    let refused = rejecting
        .declare(Segment::from("record"), declaration(at), at)
        .expect_err("the reject policy refuses");
    assert_eq!(
        refused.path(),
        &path("record"),
        "the refusal names the path"
    );
    assert!(
        matches!(rejecting.resolve(&path("record.get")), Maybe::Present(_)),
        "a refused declaration leaves the scope as it was"
    );
}

#[test]
fn redeclaring_a_source_name_is_not_a_shadow_event()
{
    let mut recognition = seeded(ShadowPolicy::Reject);
    recognition
        .declare(
            Segment::from("mine"),
            declaration(site(0_usize, 4_usize)),
            site(0_usize, 4_usize),
        )
        .expect("a fresh name shadows nothing");
    recognition
        .declare(
            Segment::from("mine"),
            declaration(site(9_usize, 13_usize)),
            site(9_usize, 13_usize),
        )
        .expect("one source declaration over another is ordinary rebinding");
    assert!(
        recognition.shadowed().is_empty(),
        "neither declaration displaced a builtin"
    );
}

#[test]
fn resuming_carries_the_names_and_drops_the_events()
{
    let mut first = seeded(ShadowPolicy::WarnAndAllow);
    first
        .declare(
            Segment::from("string"),
            declaration(site(0_usize, 6_usize)),
            site(0_usize, 6_usize),
        )
        .expect("warn-and-allow accepts");
    assert_eq!(
        first.shadowed().len(),
        1_usize,
        "the first run recorded its event"
    );

    let resumed = Recognition::resumed(&first, ShadowPolicy::WarnAndAllow);
    assert!(
        matches!(
            resumed.resolve(&path("string")),
            Maybe::Present(&Recognized::Definition)
        ),
        "the declaration is still in scope on the next submission"
    );
    assert!(
        matches!(resumed.resolve(&path("string.escape")), Maybe::Absent(_)),
        "and so is the displacement it performed"
    );
    assert!(
        resumed.shadowed().is_empty(),
        "each submission reports only its own events"
    );
}

#[test]
fn a_resumed_declaration_binds_without_reporting()
{
    let mut recognition = seeded(ShadowPolicy::Reject);
    recognition.declare_resumed(Segment::from("prim"), declaration(site(0_usize, 4_usize)));
    assert!(
        matches!(
            recognition.resolve(&path("prim")),
            Maybe::Present(&Recognized::Definition)
        ),
        "the carried declaration binds, over a builtin, under the reject policy"
    );
    assert!(
        recognition.shadowed().is_empty(),
        "an earlier submission's shadowing is not this submission's event"
    );
}

#[test]
fn a_binder_over_a_builtin_reports_without_shadowing()
{
    let mut recognition = seeded(ShadowPolicy::WarnAndAllow);
    let root = recognition
        .note_binder(Segment::from("env"), site(7_usize, 10_usize))
        .expect("warn-and-allow accepts a binder collision");
    assert_eq!(
        root,
        Maybe::Present(RecognitionSite::Builtin),
        "the note gives the builtin the binder hides"
    );
    assert_eq!(
        recognition.shadowed(),
        [ShadowedBuiltin {
            path: path("env"),
            span: site(7_usize, 10_usize),
        }]
        .as_slice(),
        "the binder collision is reported at the binder"
    );
    assert!(
        matches!(
            recognition.resolve(&path("env")),
            Maybe::Present(&Recognized::BuiltinNamespace(_))
        ),
        "the binder changes no resolution: `env` still names the builtin namespace"
    );
    assert!(
        matches!(recognition.resolve(&path("env.get")), Maybe::Present(_)),
        "and its members are still reachable"
    );

    let mut quiet = seeded(ShadowPolicy::Reject);
    let root = quiet
        .note_binder(Segment::from("not_a_builtin"), site(0_usize, 3_usize))
        .expect("a binder over nothing is not an event");
    assert!(
        matches!(root, Maybe::Absent(_)),
        "the note gives no root for a name nothing binds"
    );
    assert!(quiet.shadowed().is_empty(), "and reports nothing");
    let refused = quiet.note_binder(Segment::from("env"), site(0_usize, 3_usize));
    assert!(
        refused.is_err(),
        "the reject policy refuses a binder collision too"
    );
}
