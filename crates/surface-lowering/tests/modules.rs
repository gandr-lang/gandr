// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]
//! Module declarations and nested modules, lowered: every member flattened to
//! one declaration in source order under its structured name, every path
//! governed by the module that binds it, inline signatures matched coercively
//! against the body, and the refusals a module, a member and a component
//! earn, each asserted through the declarations the lowering hands a checker
//! and through the checker's verdicts over them.

/// The module cases, in a `cfg(test)` module so the crate's lint wall reads
/// them as test code rather than as shipping code.
#[cfg(test)]
mod modules
{
    use core::fmt::Write as _;

    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::ModuleReport;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::body;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::Value as KernelValue;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::AscriptionForm;
    use gandr_surface_lowering::Coerced;
    use gandr_surface_lowering::DeclarationOutcome;
    use gandr_surface_lowering::FormFault;
    use gandr_surface_lowering::FormName;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::FragmentSort;
    use gandr_surface_lowering::LoweredDeclaration;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::LoweredStructure;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Repair;
    use gandr_surface_lowering::Role;
    use gandr_surface_lowering::SurfaceName;
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
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    /// A source lowered over its own arena.
    struct Lowered<'source>
    {
        /// The lowered module.
        module: LoweredModule<'source>,
        /// The arena its core nodes were minted into.
        arena: CoreArena,
    }

    /// What one declaration amounts to, as these tests compare it.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Amounts<'source>
    {
        /// A signature and a definition, both lowered.
        Completed,
        /// A signature alone: the obligation the module owes.
        Uncompleted,
        /// A definition alone.
        Bodied,
        /// The lowering's refusal.
        Refused(LoweringRefusal<'source>),
    }

    /// What the checker said about one declaration, as these tests compare it.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Judgement
    {
        /// The body checked against the declared type.
        Checked,
        /// The unsigned body synthesised its type.
        Synthesised,
        /// The body is a hole, owed.
        Owed,
        /// The body's type does not convert to the declared one.
        Mismatched,
        /// Any other refusal.
        Refused,
    }

    /// One module's stratum item, as these tests compare it.
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
        /// trivial.
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
        /// trivial.
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
        /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
    fn rows<'source>(lowered: &Lowered<'source>) -> Vec<(String, Role, Amounts<'source>)>
    {
        lowered
            .module
            .declarations()
            .iter()
            .map(|declaration| {
                let amounts = match declaration.outcome() {
                    | DeclarationOutcome::Completed { .. } => Amounts::Completed,
                    | DeclarationOutcome::Uncompleted { .. } => Amounts::Uncompleted,
                    | DeclarationOutcome::Bodied { .. } => Amounts::Bodied,
                    | DeclarationOutcome::Refused(refusal) => Amounts::Refused(refusal),
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
    /// trivial.
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
    /// trivial.
    fn body_of<Path>(
        lowered: &Lowered<'_>,
        path: Path,
    ) -> ValueId
    where
        Path: AsRef<str>,
    {
        let path = path.as_ref();
        match declaration(lowered, path, Role::Declared).outcome() {
            | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => {
                body
            },
            | outcome @ (DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Refused(_)) => {
                panic!("`{path}` has a body, not {outcome:?}")
            },
        }
    }

    /// The constant the body of the declared name at `path` is.
    ///
    /// # Specification
    /// trivial.
    fn constant_read_by<Path>(
        lowered: &Lowered<'_>,
        path: Path,
    ) -> ConstantIndex
    where
        Path: AsRef<str>,
    {
        let path = path.as_ref();
        match lowered.arena.value(body_of(lowered, path)) {
            | Some(&Value::Constant(constant)) => constant,
            | other => panic!("`{path}` is a constant, not {other:?}"),
        }
    }

    /// The declared type of the declaration at `path` in `role`.
    ///
    /// # Specification
    /// trivial.
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
            | DeclarationOutcome::Completed { declared_type, .. }
            | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
            | outcome @ (DeclarationOutcome::Bodied { .. } | DeclarationOutcome::Refused(_)) => {
                panic!("`{path}` has a declared type, not {outcome:?}")
            },
        }
    }

    /// The bytes the origin of the type `declared` covers.
    ///
    /// # Specification
    /// trivial.
    fn origin_of(
        lowered: &Lowered<'_>,
        declared: ValueTypeId,
    ) -> ByteSpan
    {
        match lowered.module.origins().value_type(declared) {
            | Maybe::Present(origin) => origin.span(),
            | Maybe::Absent(absent) => panic!("every minted type has an origin, not {absent:?}"),
        }
    }

    /// Every module's stratum item, in pre-order.
    ///
    /// # Specification
    /// trivial.
    fn strata(lowered: &Lowered<'_>) -> Vec<Stratum>
    {
        lowered
            .module
            .structures()
            .iter()
            .map(|structure| Stratum {
                path: structure
                    .path()
                    .iter()
                    .map(|segment| String::from(segment.as_ref()))
                    .collect::<Vec<String>>()
                    .join("."),
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

    /// The checker's report over every declaration `lowered` did not refuse.
    ///
    /// # Specification
    /// trivial.
    fn report(lowered: &mut Lowered<'_>) -> ModuleReport
    {
        let declarations: Vec<Declaration> = lowered
            .module
            .declarations()
            .iter()
            .filter_map(|declaration| {
                let (declared, defined) = match declaration.outcome() {
                    | DeclarationOutcome::Completed {
                        declared_type,
                        body,
                    } => (Maybe::Present(declared_type), Maybe::Present(body)),
                    | DeclarationOutcome::Uncompleted { declared_type } => (
                        Maybe::Present(declared_type),
                        Maybe::Absent(body::Absent::Hole),
                    ),
                    | DeclarationOutcome::Bodied { body } => (
                        Maybe::Absent(signature::Absent::Unsigned),
                        Maybe::Present(body),
                    ),
                    | DeclarationOutcome::Refused(_) => return None,
                };
                Some(Declaration::new(
                    declaration.constant(),
                    declared,
                    defined,
                    OriginToken::from(usize::from(declaration.origin())),
                ))
            })
            .collect();
        check_module(
            &mut CheckingContext::new(&mut lowered.arena, CheckBudget::DEFAULT),
            &declarations,
        )
    }

    /// The checker's judgement of every declaration `lowered` did not refuse,
    /// by admission position.
    ///
    /// # Specification
    /// trivial.
    fn verdicts(lowered: &mut Lowered<'_>) -> Vec<(ConstantIndex, Judgement)>
    {
        report(lowered)
            .judged()
            .iter()
            .map(|judged| {
                let judgement = match judged.verdict() {
                    | Verdict::Checked { .. } => Judgement::Checked,
                    | Verdict::Synthesised { .. } => Judgement::Synthesised,
                    | Verdict::Owed(_) => Judgement::Owed,
                    | Verdict::Refused(CheckRefusal::TypeMismatch(_)) => Judgement::Mismatched,
                    | Verdict::Refused(_) => Judgement::Refused,
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
    /// trivial.
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
    /// trivial.
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
                    | DeclarationContent::Def { body, .. } => artifact.arena().value(body).cloned(),
                    | DeclarationContent::Axiom { .. }
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
                row(
                    "free_field",
                    Role::Declared,
                    Amounts::Refused(LoweringRefusal::OutOfFragment {
                        span: span_of(source, "free.field", 0_usize),
                        form: FormName::from(NamedKind("projection_expression")),
                        sort: FragmentSort::Value,
                        boundary: FragmentBoundary::Unadmitted,
                    })
                ),
            ],
            "the module selection resolves; a selection no module governs is a record \
             projection, which waits for the record former and is not a module refusal"
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
            ],
            "and checks"
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
            | [ref manifest] if manifest.name == name("T") => manifest.defined,
            | ref other => panic!("one manifest component `T`, not {other:?}"),
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
    fn a_kinded_type_component_is_declined_by_name_and_a_manifest_one_is_not()
    {
        let kinded = "module M : #{ type Hom : Integer -> Integer } { }";
        assert_eq!(
            rows(&lower(kinded)),
            [row(
                "M.Hom",
                Role::Held,
                Amounts::Refused(LoweringRefusal::UnreadAscription {
                    span: span_of(kinded, "Hom", 0_usize),
                    name: name("Hom"),
                    form: AscriptionForm::Kinded,
                })
            )],
            "the kinded component is declined by its name"
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
    fn a_bare_type_component_declines_and_keeps_its_siblings()
    {
        let source = "module M : #{ type T, value: Integer } { def value = 1; }";
        let mut lowered = lower(source);
        assert_eq!(
            rows(&lowered),
            [
                row("M.value", Role::Declared, Amounts::Completed),
                row(
                    "M.T",
                    Role::Held,
                    Amounts::Refused(LoweringRefusal::UnreadAscription {
                        span: span_of(source, "T", 0_usize),
                        name: name("T"),
                        form: AscriptionForm::Abstract,
                    })
                ),
            ],
            "the bare component is declined by its name and its sibling is matched"
        );
        assert_eq!(
            verdicts(&mut lowered),
            [judged(0_usize, Judgement::Checked)],
            "and the sibling checks"
        );
    }

    #[test]
    fn an_abstract_component_under_transparent_ascription_points_at_seal()
    {
        let source = "module Bad : #{ type T, value: Integer } { def value = 1; }";
        let lowered = lower(source);
        let refusal = match declaration(&lowered, "Bad.T", Role::Held).outcome() {
            | DeclarationOutcome::Refused(refusal) => refusal,
            | other => panic!("the abstract component is refused, not {other:?}"),
        };
        assert_eq!(
            refusal.to_string(),
            "`T` at 21..22 is an abstract type component, given its meaning only by opaque \
             ascription `:>`; the fragment does not read it yet",
            "the refusal names opaque ascription as the form that gives the component meaning"
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
    fn member_signature_attaches_and_wins_over_derived_function_type()
    {
        let source = "module M { def f : +U (Integer -> -F Integer); def f(x : Integer) -> -F \
                      Integer { ret x } }";
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
                      Integer);\ndef f(x : Integer) -> -F Integer { ret x }";
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
        let member = "module M { def x : -F Integer; def x = ret 1; }";
        let top = "def x : -F Integer;\ndef x = ret 1;";
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
                | Maybe::Present(origin) => origin.span(),
                | Maybe::Absent(absent) => panic!("the declaration has an origin, not {absent:?}"),
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
    fn opaque_module_ascription_is_declined_not_read_as_transparent()
    {
        let source = "module M :> #{ visible: Integer } { def visible = 2; }";
        let lowered = lower(source);
        assert_eq!(
            rows(&lowered),
            [row(
                "M",
                Role::Held,
                Amounts::Refused(LoweringRefusal::UnreadAscription {
                    span: span_of(source, ":>", 0_usize),
                    name: name("M"),
                    form: AscriptionForm::Opaque,
                })
            )],
            "the module is declined at its opaque ascription"
        );
        assert_eq!(
            strata(&lowered),
            [],
            "and nothing of it is read as a transparent module"
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
                        fault: FormFault::Repaired(Repair::Grout(_)),
                        ..
                    })),
                    (member, Role::Declared, Amounts::Bodied),
                    (top, Role::Declared, Amounts::Bodied),
                ] if bad == "M.bad" && *refused == FormName::from(NamedKind("def_value"))
                    && member == "M.good"
                    && top == "good"
            ),
            "the repair stays inside the member it repairs; the module keeps its other \
             member and the declaration after it, got {found:?}"
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
        let source = "module M : #{\n  val x : Integer\n} {\n  def x = 1;\n}\n\ndef after = 1;\n";
        let lowered = repaired(source);
        let found = rows(&lowered);
        assert!(
            matches!(
                found.as_slice(),
                [(module, Role::Held, Amounts::Refused(LoweringRefusal::MalformedForm {
                    span,
                    form: FormName::MODULE,
                    fault: FormFault::MisplacedTile,
                }))] if module == "M" && span.start() == span_of(source, "val", 0_usize).start()
            ),
            "the module is refused where its signature stops being read, got {found:?}"
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
        let source = "module M {\n  type Hom = Type;\n}\n\ndef after = 1;\n";
        let lowered = repaired(source);
        assert_eq!(
            rows(&lowered),
            [row(
                "M",
                Role::Held,
                Amounts::Refused(LoweringRefusal::MalformedForm {
                    span: span_of(source, "type", 0_usize),
                    form: FormName::MODULE,
                    fault: FormFault::MisplacedTile,
                })
            )],
            "the report is at the member's own tile rather than over the whole declaration"
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
                 T) }} {{ def zero = 0; def add(x : Integer, y : Integer) -> -F Integer {{ ret \
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
                let lowered = repaired(source.as_str());
                let whole =
                    ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(source.len()))
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
}
