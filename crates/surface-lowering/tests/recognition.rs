//! Recognition as scoped resolution: the outermost scope seeded from ordered
//! tables, the shadow policy that settles a source name over a builtin, and
//! the lowering that declares every name and reports every binder against it.
//!
//! The seed table here is a test table: the rows a prelude, a host or a
//! session will contribute are not part of the mechanism.

/// The recognition cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod recognition
{
    use gandr_core_term::CoreArena;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::DeclarationOutcome;
    use gandr_surface_lowering::LoweredDeclaration;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Binding;
    use gandr_surface_lowering::namespace::Declines;
    use gandr_surface_lowering::namespace::DottedName;
    use gandr_surface_lowering::namespace::NamePath;
    use gandr_surface_lowering::namespace::PathResolution;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_lowering::namespace::RecognitionSite;
    use gandr_surface_lowering::namespace::Recognized;
    use gandr_surface_lowering::namespace::SeedEntry;
    use gandr_surface_lowering::namespace::SeedKind;
    use gandr_surface_lowering::namespace::SeedPosition;
    use gandr_surface_lowering::namespace::SeedTable;
    use gandr_surface_lowering::namespace::Segment;
    use gandr_surface_lowering::namespace::SegmentCount;
    use gandr_surface_lowering::namespace::ShadowPolicy;
    use gandr_surface_lowering::namespace::ShadowedBuiltin;
    use gandr_surface_lowering::namespace::Trie;
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
    fn declaration(at: ByteSpan) -> Trie<Recognized, RecognitionSite>
    {
        let mut namespace = Trie::empty();
        let _fresh = namespace.insert(
            &NamePath::root(),
            Binding::new(Recognized::Definition, RecognitionSite::Source(at)),
        );
        namespace
    }

    /// `source` parsed under the built-in grammar and lowered against
    /// `outermost`, which must not refuse the module.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
    fn outcomes<'source>(module: &LoweredModule<'source>) -> Vec<DeclarationOutcome<'source>>
    {
        module
            .declarations()
            .iter()
            .map(LoweredDeclaration::outcome)
            .collect()
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
        ] {
            assert_eq!(
                kind.declines_unknown_member(),
                Declines(true),
                "a namespace governs its members and declines an unknown one"
            );
        }
        for kind in [
            Recognized::BuiltinMember(position),
            Recognized::ModuleComponent,
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
        recognition
            .note_binder(Segment::from("env"), site(7_usize, 10_usize))
            .expect("warn-and-allow accepts a binder collision");
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
        quiet
            .note_binder(Segment::from("not_a_builtin"), site(0_usize, 3_usize))
            .expect("a binder over nothing is not an event");
        assert!(quiet.shadowed().is_empty(), "and reports nothing");
        let refused = quiet.note_binder(Segment::from("env"), site(0_usize, 3_usize));
        assert!(
            refused.is_err(),
            "the reject policy refuses a binder collision too"
        );
    }

    #[test]
    fn a_shadowed_builtin_is_reported_as_a_warning()
    {
        let source = "def list = 1 ;\ndef used = list ;";
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
    }

    #[test]
    fn a_binder_shadowing_a_builtin_is_rejected_under_policy()
    {
        for (written, at) in [
            (
                "def x = thunk { fn (list) { ret list } } ;",
                site(20_usize, 24_usize),
            ),
            (
                "def f(list: Integer) -> F Integer { ret list }",
                site(6_usize, 10_usize),
            ),
            (
                "def x = thunk { run list <- ret 1 ; ret list } ;",
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
                "a lambda, parameter or `run` binder over a builtin is reported at the binder"
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
                shadowing.recognition().resolve_path(seeded_path)
                    != pristine.resolve_path(seeded_path)
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
}
