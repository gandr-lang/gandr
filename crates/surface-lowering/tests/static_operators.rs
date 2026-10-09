//! Type operators, lowered and checked: the relative-monad witness written
//! with every universe spelled out and with the defaults left off, each
//! lowered, judged by the checker and readmitted to the kernel, the two
//! compared by the kernel's content digest of everything they export.

/// The static-operator cases, in a `cfg(test)` module so the crate's lint
/// wall reads them as test code rather than as shipping code.
#[cfg(test)]
mod static_operators
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::Verdict;
    use gandr_core_checker::body;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_kernel_core::content_digest;
    use gandr_kernel_term::AnyNode;
    use gandr_kernel_term::DeclarationContent;
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
    const EXPLICIT: &str = "\
        def raw_rel_monad : (Type[+, 0] -> Type[-, 0]) -> Type[+, 0] -> Type[+, 0] -> Type[+, 0] ;
        def raw_rel_monad = \\T. \\A. \\B. +U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;
        def unit_and_bind : raw_rel_monad(\\X. -F (X * X), Integer, Integer) ;
        def unit_and_bind_spelled :
          (Integer => Integer * Integer)
          * ((+U (-F (Integer * Integer)), Integer => Integer * Integer) => Integer * Integer) ;
    ";

    /// The same witness with the sort and level defaults left off.
    const ELIDED: &str = "\
        def raw_rel_monad : (Type -> Type[-]) -> Type -> Type -> Type ;
        def raw_rel_monad = \\T. \\A. \\B. +U (A -> T(A)) * +U (+U (T(A)) -> +U (A -> T(B)) -> T(B)) ;
        def unit_and_bind : raw_rel_monad(\\X. -F (X * X), Integer, Integer) ;
        def unit_and_bind_spelled :
          (Integer => Integer * Integer)
          * ((+U (-F (Integer * Integer)), Integer => Integer * Integer) => Integer * Integer) ;
    ";

    /// What one spelling elaborates to: the checker's verdict on each
    /// declaration, and each exported declaration's name with the content
    /// digests of its type and of its body when it has one.
    #[derive(Debug, Eq, PartialEq)]
    struct Elaborated
    {
        /// Whether each declaration checked, was owed, or was refused.
        verdicts: Vec<&'static str>,
        /// The exported declarations, in export order.
        exported: Vec<(Vec<String>, String, Option<String>)>,
    }

    /// `source` parsed, lowered, judged and readmitted.
    ///
    /// # Specification
    /// trivial.
    fn elaborate(source: SourceText<'_>) -> Elaborated
    {
        let pbg = built_in().expect("the built-in grammar builds");
        let parsed = parse(&pbg, source).expect("the parser reads the source");
        assert!(
            bool::from(parsed.is_clean()),
            "the parser reads the source without repair: {source}"
        );
        let tree = parsed.into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &pbg,
            &tree,
            &mut arena,
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
        let names = module.structured_names();
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &declarations,
        );
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
}
