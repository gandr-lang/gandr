//! Type operators, lowered and checked: the relative-monad witness written
//! with every universe spelled out and with the defaults left off, each
//! lowered, judged by the checker and readmitted to the kernel, the two
//! compared by the kernel's content digest of everything they export; and the
//! witness's sort errors, refused naming both universes.

extern crate alloc;

/// The static-operator cases, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod static_operators
{
    use alloc::collections::BTreeMap;

    use anodized::spec;
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
    use gandr_core_term::Sort;
    use gandr_core_term::ValueType;
    use gandr_kernel_core::content_digest;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::decode;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::DeclarationOutcome;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    /// The witness with every universe written at its sort and level.
    ///
    /// # Specification
    /// - requires: interpreted by the built-in grammar and current core
    ///   fragment.
    /// - ensures: the fully explicit relative-monad signature and its two
    ///   instances exercise static abstraction, application, universes and the
    ///   value-function alias.
    /// - provides: the explicit spelling in the semantic comparison.
    /// - fails: none for this accepted source fixture.
    /// - panics: none as a string value.
    /// - executable: none — constant items do not accept the specification
    ///   attribute; semantic meaning is observed by the full elaboration
    ///   witness.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on this fixture — the operator checks, its two
    ///   instances are owed, and the instantiated and explicitly expanded types
    ///   export equal content digests.
    /// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
    const EXPLICIT: &str = "\
        def raw_rel_monad : (Type[+, 0] -> Type[-, 0]) -> Type[+, 0] -> Type[+, 0] -> Type[+, 0] ;
        def raw_rel_monad = \\T. \\A. \\B. +U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;
        def unit_and_bind : raw_rel_monad(\\X. -F (X * X), Integer, Integer) ;
        def unit_and_bind_spelled :
          (Integer => Integer * Integer)
          * ((+U (-F (Integer * Integer)), Integer => Integer * Integer) => Integer * Integer) ;
    ";

    /// The same witness with the sort and level defaults left off.
    ///
    /// # Specification
    /// - requires: interpreted by the same grammar and core fragment as the
    ///   explicit fixture.
    /// - ensures: omitting the permitted sort and level defaults preserves the
    ///   explicit fixture’s verdicts and exported content.
    /// - provides: the elided spelling in the semantic comparison.
    /// - fails: none for this accepted source fixture.
    /// - panics: none as a string value.
    /// - executable: none — constant items do not accept the specification
    ///   attribute; equivalence is observed after parsing, checking and export.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the paired fixtures only — explicit and elided
    ///   spellings have identical normalized verdict and exported-digest views.
    /// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
    const ELIDED: &str = "\
        def raw_rel_monad : (Type -> Type[-]) -> Type -> Type -> Type ;
        def raw_rel_monad = \\T. \\A. \\B. +U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;
        def unit_and_bind : raw_rel_monad(\\X. -F (X * X), Integer, Integer) ;
        def unit_and_bind_spelled :
          (Integer => Integer * Integer)
          * ((+U (-F (Integer * Integer)), Integer => Integer * Integer) => Integer * Integer) ;
    ";

    /// The witness's two sort errors: the carrier `T(A)`, a computation type,
    /// standing bare in an eager product and under a returner, where a value
    /// type is read.
    ///
    /// # Specification
    /// - requires: interpreted by the built-in grammar and current core
    ///   fragment.
    /// - ensures: the negative carrier is refused in both a positive product
    ///   position and a returner’s positive argument position.
    /// - provides: the two sort-boundary counterexamples.
    /// - fails: checking reports the computation universe where the value
    ///   universe is required, both at level zero.
    /// - panics: none as a string value.
    /// - executable: none — constant items do not accept the specification
    ///   attribute; the checker witness observes both exact universe pairs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the product and returner contexts independently
    ///   expose the expected and synthesized sorts and levels, not just any
    ///   refusal.
    /// - witness: `static_operators::static_operators::a_negative_carrier_where_a_value_type_is_read_names_both_universes`
    const SORT_ERRORS: &str = "\
        def in_a_product : (Type -> Type[-]) -> Type -> Type ;
        def in_a_product = \\T. \\A. T(A) * A ;
        def under_a_returner : (Type -> Type[-]) -> Type -> Type[-] ;
        def under_a_returner = \\T. \\A. -F (T(A)) ;
    ";

    /// What one spelling elaborates to: the checker's verdict on each
    /// declaration, and each exported declaration's name with the content
    /// digests of its type and of its body when it has one.
    ///
    /// # Specification
    /// - requires: interpreted as the stage artifact of a fully signed fixture.
    /// - ensures: verdict order is separate from export order, and an absent
    ///   body digest denotes a non-definition export.
    /// - provides: a comparison free of arena-local identifiers.
    /// - fails: it cannot certify typing or digest provenance without the
    ///   erased arenas and reports.
    /// - panics: none as a data value.
    /// - executable: none — the intermediate checker report and decoded
    ///   artifact are not retained; `elaborate` checks its observable category
    ///   and export bound.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the named fixtures — normalized verdicts, exported
    ///   names and type digests are compared with their expected semantic roles
    ///   and with the independent explicit normal form.
    /// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
    #[derive(Debug, Eq, PartialEq)]
    struct Elaborated
    {
        /// Whether each declaration checked, was owed, or was refused.
        verdicts: Vec<&'static str>,
        /// The exported declarations, in export order.
        exported: Vec<(Vec<String>, String, Option<String>)>,
    }

    /// `source` parsed, lowered and judged in `arena`: the checker's report,
    /// and each declaration's structured name.
    ///
    /// # Specification
    /// - requires: clean top-level fixtures whose declarations all lower within
    ///   the default budgets.
    /// - ensures: checking preserves admission coordinates and every judged
    ///   declaration has its structured name in the returned map.
    /// - provides: the real parse, lower and check pipeline rather than a
    ///   mocked verdict.
    /// - fails: checking refusals remain in the report.
    /// - panics: on parsing, repair, engine refusal or a declaration-local
    ///   lowering refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the explicit and elided operator fixtures, with L3
    ///   negative product and returner positions — reports preserve the named
    ///   declarations and expose the exact expected and synthesized universes.
    /// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
    /// - witness: `static_operators::static_operators::a_negative_carrier_where_a_value_type_is_read_names_both_universes`
    #[spec(
        ensures: |ret| {
            ret.0
                .judged()
                .iter()
                .map(gandr_core_checker::Judged::constant)
                .eq(ret.1.keys().copied())
        },
    )]
    fn judge(
        source: SourceText<'_>,
        arena: &mut CoreArena,
    ) -> (ModuleReport, BTreeMap<ConstantIndex, StructuredName>)
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let parsed = parse(&pbg, source).expect("the parser reads the source");
        assert!(
            bool::from(parsed.is_clean()),
            "the parser reads the source without repair: {source}"
        );
        let tree = parsed.into_tree();
        let module = lower_module(
            &pbg,
            &tree,
            arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        let declarations: Vec<Declaration> = module
            .declarations()
            .iter()
            .map(|declaration| {
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
                    | DeclarationOutcome::Refused(refusal) => {
                        panic!("every declaration lowers: {refusal:?}")
                    },
                };
                Declaration::new(
                    declaration.constant(),
                    declared,
                    defined,
                    OriginToken::from(usize::from(declaration.origin())),
                )
            })
            .collect();
        let report = check_module(
            &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
            &declarations,
        );
        (report, module.structured_names())
    }

    /// `source` parsed, lowered, judged and readmitted.
    ///
    /// # Specification
    /// - requires: clean, fully signed top-level fixtures accepted by lowering
    ///   and readable by the export decoder.
    /// - ensures: verdict classes stay in admission order and exported names
    ///   and type/body digests stay in export order; checked operators not
    ///   representable in the artifact may remain unexported.
    /// - provides: a semantic stage artifact for comparing the two spellings
    ///   and their independently written normal forms.
    /// - fails: checking and readmission may omit declarations from the export.
    /// - panics: on a parser or lowering refusal, or an undecodable exported
    ///   image.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on these two relative-monad spellings only — one
    ///   checked operator stays local, two owed instances cross, and the
    ///   instantiated type’s digest equals the independently spelled normal
    ///   form.
    /// - witness: `static_operators::static_operators::the_relative_monad_witness_elaborates_identically_in_both_spellings`
    #[spec(
        ensures: |ret| {
            ret.verdicts
                .iter()
                .all(|&verdict| matches!(verdict, "checked" | "owed" | "refused"))
                && ret.exported.len()
                    <= ret
                        .verdicts
                        .iter()
                        .filter(|&&verdict| matches!(verdict, "checked" | "owed"))
                        .count()
        },
    )]
    fn elaborate(source: SourceText<'_>) -> Elaborated
    {
        let mut arena = CoreArena::new();
        let (report, names) = judge(source, &mut arena);
        let verdicts = report
            .judged()
            .iter()
            .map(|judged| match judged.verdict() {
                | Verdict::Checked { .. } => "checked",
                | Verdict::Owed(_) => "owed",
                | _ => "refused",
            })
            .collect();
        let readmission = bridge::readmit(&mut arena, &report);
        let artifact = decode(readmission.export(names).as_image()).expect("the export decodes");
        let digest = |node| format!("{:?}", content_digest(artifact.arena(), node));
        let exported = artifact
            .declarations()
            .iter()
            .map(|marked| {
                let declaration = marked.declaration();
                let segments = declaration
                    .name()
                    .segments()
                    .iter()
                    .map(|segment| String::from(segment.as_ref()))
                    .collect();
                let (declared, defined) = match *declaration.content() {
                    | DeclarationContent::Def { declared, body } => {
                        (declared, Some(digest(AnyNode::Value(body))))
                    },
                    | DeclarationContent::Axiom { declared } => (declared, None),
                    | DeclarationContent::AbstractType { kind } => (kind, None),
                };
                (segments, digest(AnyNode::ValueType(declared)), defined)
            })
            .collect();

        Elaborated { verdicts, exported }
    }

    #[test]
    fn the_relative_monad_witness_elaborates_identically_in_both_spellings()
    {
        let explicit = elaborate(SourceText::from(EXPLICIT));
        let elided = elaborate(SourceText::from(ELIDED));

        assert_eq!(
            explicit.verdicts,
            ["checked", "owed", "owed"],
            "the operator checks against its static Pi, and both instances are owed"
        );
        assert_eq!(
            explicit
                .exported
                .iter()
                .map(|entry| entry.0.join("."))
                .collect::<Vec<String>>(),
            ["unit_and_bind", "unit_and_bind_spelled"],
            "the operator stays on the checker's side and both instances cross"
        );
        let [ref instance, ref spelled] = *explicit.exported
        else {
            panic!("two exported declarations");
        };
        assert_eq!(
            instance.1, spelled.1,
            "the instance crosses as the very type its normal form spells through `=>`"
        );
        assert_eq!(
            explicit, elided,
            "the explicit and the elided spellings export equal content"
        );
    }

    #[test]
    fn a_negative_carrier_where_a_value_type_is_read_names_both_universes()
    {
        let mut arena = CoreArena::new();
        let (report, _) = judge(SourceText::from(SORT_ERRORS), &mut arena);
        let universe = |id| match arena.value_type(id) {
            | Some(&ValueType::Universe { sort, ref level }) => (sort, level.clone()),
            | other => panic!("a sort mismatch names universes, not {other:?}"),
        };
        let refused: Vec<_> = report
            .judged()
            .iter()
            .map(|judged| match judged.verdict() {
                | Verdict::Refused(CheckRefusal::SortMismatch {
                    synthesised,
                    expected,
                    ..
                }) => (universe(synthesised), universe(expected)),
                | other => panic!("each carrier is refused as a sort mismatch, not {other:?}"),
            })
            .collect();

        let negative = (Sort::Ground(GroundSort::Computation), Level::zero());
        let positive = (Sort::Ground(GroundSort::Value), Level::zero());
        assert_eq!(
            refused,
            [(negative.clone(), positive.clone()), (negative, positive)],
            "each refusal names the carrier's universe and the one its position reads, sort and \
             level both"
        );
    }
}
