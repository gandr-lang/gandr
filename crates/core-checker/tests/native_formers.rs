//! Nominal and record judgments, including independent kernel readmission.

extern crate alloc;

#[cfg(test)]
mod native_formers
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
    use gandr_core_checker::bridge;
    use gandr_core_checker::bridge::Outcome;
    use gandr_core_checker::check_module;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DataSignature;
    use gandr_core_term::Sort;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::GroundSort;
    use quenchant_shape::shape::Maybe;

    /// A definition at its source position.
    ///
    /// # Specification
    /// trivial.
    fn definition(
        constant: ConstantIndex,
        declared: ValueTypeId,
        body: ValueId,
    ) -> Declaration
    {
        Declaration::new(
            constant,
            Maybe::Present(declared),
            Maybe::Present(body),
            OriginToken::from(usize::from(constant)),
        )
    }

    /// Run the producer and its independent kernel boundary.
    ///
    /// # Specification
    /// - requires: declaration ids refer to `arena`.
    /// - ensures: each source position has a producer verdict and a boundary
    ///   outcome.
    /// - panics: only if a called judgment violates its contract.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses inspect exact positive and negative
    ///   outcomes, including native identities after admission renumbering.
    /// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
    #[spec(ensures: |ret| ret.0.judged().len() == declarations.len() && ret.1.readmitted().len() == declarations.len())]
    fn run(
        arena: &mut CoreArena,
        declarations: &[Declaration],
    ) -> (ModuleReport, bridge::Readmission)
    {
        let report = check_module(
            &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
            declarations,
        );
        let crossed = bridge::readmit(arena, &report);
        (report, crossed)
    }

    #[test]
    fn data_declarations_and_refusals_agree_with_kernel()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bad_kind =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let bad = Declaration::data(
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![], bad_kind).into(),
            OriginToken::from(0_usize),
        );
        let first = ConstantIndex::from(1_usize);
        let second = ConstantIndex::from(2_usize);
        let one = Declaration::data(
            first,
            DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
            OriginToken::from(1_usize),
        );
        let two = Declaration::data(
            second,
            DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
            OriginToken::from(2_usize),
        );
        let datatype = arena.value_type_data(first, vec![]);
        let other = arena.value_type_data(second, vec![]);
        let good = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
        let bad_tag = arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![unit]);
        let bad_fields = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
        let bad_arguments = arena.value_type_data(first, vec![unit]);
        let bad_application =
            arena.value_constructor(bad_arguments, ConstructorTag::from(0_usize), vec![unit]);
        let declarations = vec![
            bad,
            one,
            two,
            definition(ConstantIndex::from(3_usize), datatype, good),
            definition(ConstantIndex::from(4_usize), datatype, bad_tag),
            definition(ConstantIndex::from(5_usize), datatype, bad_fields),
            definition(ConstantIndex::from(6_usize), bad_arguments, bad_application),
            definition(ConstantIndex::from(7_usize), other, good),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        assert_eq!(
            report.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::DataKindNotUniverse(bad_kind))
        );
        assert_eq!(report.judged()[1].verdict(), Verdict::Data);
        assert_eq!(report.judged()[2].verdict(), Verdict::Data);
        assert!(matches!(
            report.judged()[3].verdict(),
            Verdict::Checked { .. }
        ));
        assert_eq!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::UnknownConstructor {
                at: bad_tag,
                tag: ConstructorTag::from(1_usize)
            })
        );
        assert_eq!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::ConstructorArity(bad_fields))
        );
        assert_eq!(
            report.judged()[6].verdict(),
            Verdict::Refused(CheckRefusal::DataArgumentArity(bad_arguments))
        );
        assert!(matches!(
            report.judged()[7].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ));
        for position in [0_usize, 4, 5, 6, 7] {
            let Verdict::Refused(reason) = report.judged()[position].verdict()
            else {
                panic!("malformed declaration must be refused");
            };
            assert_eq!(
                reason.classify(),
                gandr_core_term::FailureClass::MalformedSource
            );
        }
        assert!(
            matches!(crossed.readmitted()[1].outcome(),Outcome::Data { admitted,.. } if admitted.position() == ConstantIndex::from(0_usize))
        );
        assert!(
            matches!(crossed.readmitted()[2].outcome(),Outcome::Data { admitted,.. } if admitted.position() == ConstantIndex::from(1_usize))
        );
        assert!(
            matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
            "{:?}",
            crossed.readmitted()[3].outcome()
        );
        assert!(crossed.audit().axioms().is_empty());
        let family = gandr_kernel_term::StructuredName::from(vec![
            gandr_kernel_term::NameSegment::from_text(String::from("Unit1")).unwrap(),
        ]);
        let artifact = gandr_kernel_term::decode(
            crossed
                .export(BTreeMap::from([(first, family.clone())]))
                .as_image(),
        )
        .unwrap();
        assert_eq!(
            artifact.declarations()[0].declaration().name(),
            &family,
            "a nominal declaration crosses under its own name"
        );
        let gandr_kernel_term::DeclarationContent::Def { body, .. } =
            *artifact.declarations()[2].declaration().content()
        else {
            panic!("a native constructor definition");
        };
        let Some(matched_native_node) = artifact.arena().value(body)
        else {
            panic!("native constructor, not a pair encoding");
        };
        let gandr_kernel_term::Value::Constructor { ref datatype, .. } = *matched_native_node
        else {
            panic!("native constructor, not a pair encoding");
        };
        assert!(
            matches!(artifact.arena().value_type(*datatype),Some(gandr_kernel_term::ValueType::Data { declaration,.. }) if *declaration == ConstantIndex::from(0_usize))
        );
    }

    /// The circle's word over `base` (tag 0), spelled by `letters` outermost
    /// first: tag 1 a `Loop`, tag 2 an `Unloop`.
    ///
    /// # Specification
    /// trivial.
    fn word(
        arena: &mut CoreArena,
        letters: &[ConstructorTag],
    ) -> ValueId
    {
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let mut built = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
        for &letter in letters.iter().rev() {
            built = arena.value_constructor(own, letter, vec![built]);
        }
        built
    }

    /// The circle at position zero, presented by `rules`.
    ///
    /// # Specification
    /// trivial.
    fn circle(
        arena: &mut CoreArena,
        rules: Vec<gandr_kernel_term::PresentedRule>,
    ) -> Declaration
    {
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        Declaration::data(
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![vec![], vec![own], vec![own]], kind)
                .presented(gandr_kernel_term::Presentation::new(rules))
                .into(),
            OriginToken::from(0_usize),
        )
    }

    /// The circle's cancellations `Loop(Unloop(x)) ~> x` and
    /// `Unloop(Loop(x)) ~> x`.
    ///
    /// # Specification
    /// trivial.
    fn cancellations() -> Vec<gandr_kernel_term::PresentedRule>
    {
        use gandr_kernel_term::RuleNode;
        let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
        let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
        vec![
            gandr_kernel_term::PresentedRule::new([c(1), c(2), x].into(), [x].into()),
            gandr_kernel_term::PresentedRule::new([c(2), c(1), x].into(), [x].into()),
        ]
    }

    #[test]
    fn a_presented_word_meets_its_reduced_word_in_both_checkers()
    {
        let looped = ConstructorTag::from(1_usize);
        let unlooped = ConstructorTag::from(2_usize);
        for (rules, admitted) in [(cancellations(), true), (vec![], false)] {
            let mut arena = CoreArena::new();
            let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
            let written = word(&mut arena, &[looped, unlooped, looped]);
            let reduced = word(&mut arena, &[looped]);
            let declared = arena.value_type_path(own, written, reduced);
            let point = word(&mut arena, &[looped]);
            let reflexivity = arena.value_here(point);
            let declarations = vec![
                circle(&mut arena, rules),
                definition(ConstantIndex::from(1_usize), declared, reflexivity),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            assert_eq!(report.judged()[0].verdict(), Verdict::Data);
            if admitted {
                assert!(
                    matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                    "`here(Loop(Base))` meets `Loop(Unloop(Loop(Base)))` under the rules: {:?}",
                    report.judged()[1].verdict()
                );
                assert!(
                    matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                    "the kernel admits the reflexivity by the same normal forms: {:?}",
                    crossed.readmitted()[1].outcome()
                );
            }
            else {
                assert!(
                    matches!(
                        report.judged()[1].verdict(),
                        Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
                    ),
                    "over a free circle the two words are two terms: {:?}",
                    report.judged()[1].verdict()
                );
            }
        }
    }

    #[test]
    fn a_misplaced_rule_is_refused_in_both_checkers()
    {
        use gandr_kernel_term::RuleNode;
        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        // `Mark(Empty) ~> Empty`, with `Mark`'s field an integer: no term of
        // the family stands there.
        let misplaced = gandr_kernel_term::PresentedRule::new(
            [
                RuleNode::Constructor(ConstructorTag::from(1_usize)),
                RuleNode::Constructor(ConstructorTag::from(0_usize)),
            ]
            .into(),
            [RuleNode::Constructor(ConstructorTag::from(0_usize))].into(),
        );
        let presentation = gandr_kernel_term::Presentation::new(vec![misplaced]);
        let tally = Declaration::data(
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![vec![], vec![integer]], kind)
                .presented(presentation.clone())
                .into(),
            OriginToken::from(0_usize),
        );
        let refusal = gandr_kernel_term::RuleRefusal {
            rule: gandr_kernel_term::RuleIndex::from(0_usize),
            fault: gandr_kernel_term::RuleFault::NotOwnPosition,
        };
        let (report, _crossed) = run(&mut arena, &[tally]);
        assert_eq!(
            report.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::RuleNotPresentable { kind, refusal }),
            "the checker names the rule and its fault"
        );
        let mut environment = gandr_kernel_core::Environment::new();
        let mut staging = environment.stage();
        let kernel_kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let kernel_integer = staging
            .arena()
            .value_type_base(gandr_kernel_term::BaseType::Integer);
        let staged = staging
            .data(
                gandr_kernel_term::LevelSignature::monomorphic(),
                vec![],
                vec![vec![], vec![kernel_integer]],
                kernel_kind,
            )
            .presented(presentation);
        assert_eq!(
            environment.add_decl(staged).map(|_admitted| ()),
            Err(gandr_kernel_core::KernelError::RuleNotPresentable(refusal)),
            "the kernel refuses the same rule for the same fault"
        );
    }

    /// `fix f. λy. case y { Base ⇒ return (); Loop(x) ⇒ f(x); Unloop(x) ⇒
    /// f(x) }` at `Circle → F Unit`, its descent claimed, and the case at its
    /// root.
    ///
    /// # Specification
    /// trivial.
    fn unwinding(arena: &mut CoreArena) -> (ValueId, ValueTypeId, gandr_core_term::ComputationId)
    {
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let motive = arena.comp_type_returner(unit_type);
        let returned = arena.computation_return(unit);
        // Under the self binder, the argument and the field: `f` is two out.
        let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(recursive);
        let called = arena.computation_application(forced, field);
        let recursing = arena.computation_lambda(called);
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case =
            arena.computation_data_case(argument, motive, vec![returned, recursing, recursing]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let arrow = arena.comp_type_arrow(own, motive);
        (
            arena.value_thunk(fixpoint),
            arena.value_type_thunk(arrow),
            case,
        )
    }

    #[test]
    fn a_case_respects_its_type_s_rules_or_is_refused_by_the_rule()
    {
        let looped = ConstructorTag::from(1_usize);
        let unlooped = ConstructorTag::from(2_usize);
        for (rules, presented) in [(cancellations(), true), (vec![], false)] {
            let mut arena = CoreArena::new();
            // `Loop(Unloop(Base))`, which the rules identify with `Base`.
            let scrutinee = word(&mut arena, &[looped, unlooped]);
            let unit_type = arena.value_type_unit();
            let unit = arena.value_unit();
            let motive = arena.comp_type_returner(unit_type);
            let returned = arena.computation_return(unit);
            let lettered = arena.computation_lambda(returned);
            // A bare case: its arms return at once, so at `Loop(Unloop(x))`
            // it returns while at `x` it is stuck on the variable.
            let case =
                arena.computation_data_case(scrutinee, motive, vec![returned, lettered, lettered]);
            let body = arena.value_thunk(case);
            let declared = arena.value_type_thunk(motive);
            let (unwound, unwinding_type, _root) = unwinding(&mut arena);
            let declarations = vec![
                circle(&mut arena, rules),
                definition(ConstantIndex::from(1_usize), declared, body),
                definition(ConstantIndex::from(2_usize), unwinding_type, unwound),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            assert_eq!(report.judged()[0].verdict(), Verdict::Data);
            assert!(
                matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
                "a fixpoint recursing through both letters meets itself at the cancelled word: \
                 {:?}",
                report.judged()[2].verdict()
            );
            assert!(
                matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
                "and the kernel re-derives the respect: {:?}",
                crossed.readmitted()[2].outcome()
            );
            if presented {
                let Verdict::Refused(CheckRefusal::RuleNotRespected {
                    at,
                    rule,
                    left,
                    right,
                }) = report.judged()[1].verdict()
                else {
                    panic!(
                        "a bare case over the circle is refused: {:?}",
                        report.judged()[1].verdict()
                    );
                };
                assert_eq!(
                    (at, rule),
                    (case, gandr_kernel_term::RuleIndex::from(0_usize)),
                    "at the first rule"
                );
                assert!(
                    matches!(
                        arena.value(left),
                        Some(gandr_core_term::Value::Constructor { tag, .. }) if *tag == looped
                    ),
                    "naming its left side, `Loop(Unloop(x))`"
                );
                assert!(
                    matches!(
                        arena.value(right),
                        Some(gandr_core_term::Value::Variable { .. })
                    ),
                    "and its right side, `x`"
                );
            }
            else {
                assert!(
                    matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                    "the same case over a free circle checks and readmits: {:?}",
                    crossed.readmitted()[1].outcome()
                );
            }
        }
    }

    #[test]
    fn a_fold_nesting_its_call_is_judged_on_the_bind_it_elaborates_to()
    {
        let (looped, unlooped) = (ConstructorTag::from(1_usize), ConstructorTag::from(2_usize));
        // `fix f. λy. case y { Base ⇒ return Base; Loop(x) ⇒ return
        // Loop^n(f(x)); Unloop(x) ⇒ return Unloop(Unloop(f(x))) }`, the call
        // written where a value is read: doubling at `n = 2`, and at `n = 1` a
        // fold that tells `Loop(Unloop(x))` apart from `x`.
        for (loops, respected) in [(2_usize, true), (1_usize, false)] {
            let mut arena = CoreArena::new();
            let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
            let motive = arena.comp_type_returner(own);
            let base = word(&mut arena, &[]);
            let returned = arena.computation_return(base);
            let mut arm = |letter: ConstructorTag, count: usize| {
                let recursive =
                    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
                let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let forced = arena.computation_force(recursive);
                let called = arena.computation_application(forced, field);
                let mut built = arena.value_nested(called);
                for _ in 0_usize .. count {
                    built = arena.value_constructor(own, letter, vec![built]);
                }
                let result = arena.computation_return(built);
                arena.computation_lambda(result)
            };
            let (lettered, inverted) = (arm(looped, loops), arm(unlooped, 2_usize));
            let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let case =
                arena.computation_data_case(argument, motive, vec![returned, lettered, inverted]);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(
                lambda,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            );
            let fold = arena.value_thunk(fixpoint);
            let arrow = arena.comp_type_arrow(own, motive);
            let fold_type = arena.value_type_thunk(arrow);
            let declarations = vec![
                circle(&mut arena, cancellations()),
                definition(ConstantIndex::from(1_usize), fold_type, fold),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            if respected {
                assert!(
                    matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                    "the doubling fold's call, bound ahead of its arm, unfolds at the cancelled \
                     word: {:?}",
                    report.judged()[1].verdict()
                );
                assert!(
                    matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                    "and the kernel re-derives the respect: {:?}",
                    crossed.readmitted()[1].outcome()
                );
            }
            else {
                assert!(
                    matches!(
                        report.judged()[1].verdict(),
                        Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. })
                            if rule == gandr_kernel_term::RuleIndex::from(0_usize)
                    ),
                    "a fold the first rule tells apart is refused there: {:?}",
                    report.judged()[1].verdict()
                );
            }
        }
    }

    #[test]
    fn a_loop_is_a_word_at_its_path_in_both_checkers()
    {
        use gandr_kernel_term::FreeCell;
        use gandr_kernel_term::FreeCells;
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::RuleNode;

        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let (sort, words) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
        let carrier = arena.value_type_data(sort, vec![]);
        let own = arena.value_type_data(words, vec![]);
        let point = arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![]);
        let path = arena.value_type_path(carrier, point, point);
        let base =
            || -> Box<[RuleNode]> { [RuleNode::Constructor(ConstructorTag::from(0_usize))].into() };
        let cells = FreeCells::new(sort, vec![FreeCell::new(base(), base())]);
        let table = || vec![vec![], vec![own], vec![own]];
        // The one-point sort, and the words of one loop at its point.
        let one_point = Declaration::data(
            sort,
            DataSignature::new(vec![], vec![vec![]], kind).into(),
            OriginToken::from(0_usize),
        );
        let loops = Declaration::data(
            words,
            DataSignature::new(vec![], table(), kind)
                .presented(Presentation::words(cells.clone()))
                .into(),
            OriginToken::from(1_usize),
        );
        // `loop : Path(S, base, base)`, the word of its one letter.
        let empty = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
        let letter = arena.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
        // Read back at the words' own type.
        let named = arena.value_constant(ConstantIndex::from(2_usize));
        // `fix f. λp. case p { here ⇒ return here; g ∷ q ⇒ r ← f(q); return
        // g ∷ r; … }` at `Path(S, base, base) → F Path(S, base, base)`.
        let motive = arena.comp_type_returner(path);
        let nil = arena.computation_return(empty);
        let mut arm = |tag: usize| {
            let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let folded = arena.computation_application(forced, field);
            let result = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let rebuilt = arena.value_constructor(own, ConstructorTag::from(tag), vec![result]);
            let returned = arena.computation_return(rebuilt);
            let sequenced = arena.computation_bind(folded, returned);
            arena.computation_lambda(sequenced)
        };
        let (lettered, inverted) = (arm(1), arm(2));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(argument, motive, vec![nil, lettered, inverted]);
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let fold = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(path, motive);
        let fold_type = arena.value_type_thunk(arrow);
        // The same words with their cancellations dropped.
        let tampered = Declaration::data(
            ConstantIndex::from(5_usize),
            DataSignature::new(vec![], table(), kind)
                .presented(Presentation::new(vec![]).carrying(cells))
                .into(),
            OriginToken::from(5_usize),
        );
        let declarations = vec![
            one_point,
            loops,
            definition(ConstantIndex::from(2_usize), path, letter),
            definition(ConstantIndex::from(3_usize), own, named),
            definition(ConstantIndex::from(4_usize), fold_type, fold),
            tampered,
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, what) in [
            (2, "a word checks at the path of its point"),
            (3, "a path at the looped point converts with its words"),
            (
                4,
                "a fold over a path splits its words and respects both cancellations",
            ),
        ] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{what}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "and the kernel agrees: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert!(
            matches!(crossed.readmitted()[1].outcome(), Outcome::Data { .. }),
            "the words admit as their cells mint them: {:?}",
            crossed.readmitted()[1].outcome()
        );
        assert_eq!(
            crossed.readmitted()[5].outcome(),
            &Outcome::Rejected(gandr_kernel_core::KernelError::WordsRefused(
                gandr_kernel_term::CellFault::NotMinted
            )),
            "the kernel re-mints the words and refuses a twin whose cancellations were dropped"
        );
    }

    /// The parts of the one-loop circle the loop witnesses build on.
    struct OneLoop
    {
        /// The sort, `S`.
        carrier: ValueTypeId,
        /// Its point, `Base`.
        point: ValueId,
        /// The words' empty word, reflexivity at the point.
        empty: ValueId,
        /// The word of the loop's inverse letter.
        inverse: ValueId,
        /// The constant `loop`, whose body is the word of its letter.
        named: ValueId,
    }

    /// The one-point sort at constant 0, the words of one loop at its point at
    /// constant 1, and `loop` at constant 2, the word of its one letter at
    /// `Path(S, Base, Base)`.
    ///
    /// # Specification
    /// trivial.
    fn one_loop(arena: &mut CoreArena) -> (Vec<Declaration>, OneLoop)
    {
        use gandr_kernel_term::FreeCell;
        use gandr_kernel_term::FreeCells;
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::RuleNode;

        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let (sort, words) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
        let carrier = arena.value_type_data(sort, vec![]);
        let own = arena.value_type_data(words, vec![]);
        let point = arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![]);
        let path = arena.value_type_path(carrier, point, point);
        let base =
            || -> Box<[RuleNode]> { [RuleNode::Constructor(ConstructorTag::from(0_usize))].into() };
        let cells = FreeCells::new(sort, vec![FreeCell::new(base(), base())]);
        let empty = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
        let letter = arena.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
        let inverse = arena.value_constructor(own, ConstructorTag::from(2_usize), vec![empty]);
        let named = arena.value_constant(ConstantIndex::from(2_usize));
        let declarations = vec![
            Declaration::data(
                sort,
                DataSignature::new(vec![], vec![vec![]], kind).into(),
                OriginToken::from(0_usize),
            ),
            Declaration::data(
                words,
                DataSignature::new(vec![], vec![vec![], vec![own], vec![own]], kind)
                    .presented(Presentation::words(cells))
                    .into(),
                OriginToken::from(1_usize),
            ),
            definition(ConstantIndex::from(2_usize), path, letter),
        ];
        (declarations, OneLoop {
            carrier,
            point,
            empty,
            inverse,
            named,
        })
    }

    /// `thunk (λx. case x { Base ⇒ return answer; loop ⇒ arm… })` at
    /// `motive`, the case's motive and the function's codomain alike.
    ///
    /// # Specification
    /// trivial.
    fn case_over(
        arena: &mut CoreArena,
        (carrier, motive): (ValueTypeId, gandr_core_term::CompTypeId),
        answer: ValueId,
        arms: &[ValueId],
    ) -> (ValueTypeId, ValueId)
    {
        let mut branches = vec![arena.computation_return(answer)];
        branches.extend(arms.iter().map(|&arm| arena.computation_return(arm)));
        let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(scrutinee, motive, branches);
        let lambda = arena.computation_lambda(case);
        let pi = arena.comp_type_pi(carrier, motive);
        (arena.value_type_thunk(pi), arena.value_thunk(lambda))
    }

    #[test]
    fn a_case_over_the_circle_owes_its_loop()
    {
        let mut arena = CoreArena::new();
        let (mut declarations, circle) = one_loop(&mut arena);
        let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let joined = arena.value_type_path(circle.carrier, circle.point, x);
        let joined = arena.comp_type_returner(joined);
        let looped = arena.value_type_path(circle.carrier, x, x);
        let looped = arena.comp_type_returner(looped);
        let kept = arena.comp_type_returner(circle.carrier);
        // Reflexivity joining the point to every point, which the loop carries
        // to the loop; reflexivity and the loop at every point, each of which
        // conjugation by the loop fixes; and the map collapsing the circle,
        // whose constant family owes nothing.
        for (position, (motive, answer)) in [
            (joined, circle.empty),
            (looped, circle.empty),
            (looped, circle.named),
            (kept, circle.point),
        ]
        .into_iter()
        .enumerate()
        {
            let (declared, body) = case_over(&mut arena, (circle.carrier, motive), answer, &[]);
            let constant = ConstantIndex::from(position.saturating_add(3));
            declarations.push(definition(constant, declared, body));
        }
        let (report, crossed) = run(&mut arena, &declarations);
        assert!(
            matches!(
                report.judged()[3].verdict(),
                Verdict::Refused(CheckRefusal::LoopNotRespected { cell, .. })
                    if cell == gandr_kernel_term::CellIndex::from(0_usize)
            ),
            "the circle is not contractible: carried along the loop, reflexivity at the \
             point is the loop: {:?}",
            report.judged()[3].verdict()
        );
        for (position, what) in [
            (4, "reflexivity at every point respects the loop"),
            (
                5,
                "the loop at every point respects the loop, read as its word",
            ),
            (6, "a non-dependent case owes no loop"),
        ] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{what}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "and the kernel re-derives it: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
    }

    #[test]
    fn a_loop_arm_checks_at_the_path_over_its_loop()
    {
        let mut arena = CoreArena::new();
        let (mut declarations, circle) = one_loop(&mut arena);
        let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let joined = arena.value_type_path(circle.carrier, circle.point, x);
        let joined = arena.comp_type_returner(joined);
        let looped = arena.value_type_path(circle.carrier, x, x);
        let looped = arena.comp_type_returner(looped);
        let kept = arena.comp_type_returner(circle.carrier);
        let stays = arena.value_here(circle.empty);
        // The flip: the loop's image is its inverse, a loop at the point's
        // image. Reflexivity at every point, its arm the path from its
        // conjugate to itself. Reflexivity joining the point to every point,
        // whose arm owes a path from the loop to reflexivity and offers
        // reflexivity at reflexivity.
        for (position, (motive, answer, arm)) in [
            (kept, circle.point, circle.inverse),
            (looped, circle.empty, stays),
            (joined, circle.empty, stays),
        ]
        .into_iter()
        .enumerate()
        {
            let (declared, body) = case_over(&mut arena, (circle.carrier, motive), answer, &[arm]);
            let constant = ConstantIndex::from(position.saturating_add(3));
            declarations.push(definition(constant, declared, body));
        }
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, what) in [
            (3, "a non-dependent loop arm chooses the loop's image"),
            (4, "a dependent loop arm checks at the path over the loop"),
        ] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{what}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "and the kernel re-derives it: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert!(
            matches!(
                report.judged()[5].verdict(),
                Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
            ),
            "a dependent loop arm at the wrong endpoints is refused: {:?}",
            report.judged()[5].verdict()
        );
    }

    #[test]
    fn a_composite_along_a_returned_path_cancels_in_both_checkers()
    {
        let mut arena = CoreArena::new();
        let (mut declarations, circle) = one_loop(&mut arena);
        // `loop then back(loop)`: the composite runs along the inverse's
        // returned transport, which only computes once that path has run.
        let inverse =
            gandr_core_term::identity::back(&mut arena, circle.carrier, circle.point, circle.named);
        let inverse = arena.value_returned(inverse);
        let composite = gandr_core_term::identity::then(
            &mut arena,
            circle.carrier,
            circle.point,
            circle.named,
            inverse,
        );
        let composite = arena.value_returned(composite);
        let at_point = arena.value_type_path(circle.carrier, circle.point, circle.point);
        let cancelled = arena.value_type_path(at_point, composite, circle.empty);
        let reflexivity = arena.value_here(circle.empty);
        declarations.push(definition(
            ConstantIndex::from(3_usize),
            cancelled,
            reflexivity,
        ));
        // The same composite is not the loop.
        let apart = arena.value_type_path(at_point, composite, circle.named);
        let wrong = arena.value_here(circle.named);
        declarations.push(definition(ConstantIndex::from(4_usize), apart, wrong));
        let (report, crossed) = run(&mut arena, &declarations);
        assert!(
            matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
            "the composite cancels to the empty word: {:?}",
            report.judged()[3].verdict()
        );
        assert!(
            matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
            "and the kernel runs the returned path before transporting along it: {:?}",
            crossed.readmitted()[3].outcome()
        );
        assert!(
            matches!(
                report.judged()[4].verdict(),
                Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
            ),
            "the composite is not the loop: {:?}",
            report.judged()[4].verdict()
        );
    }

    #[test]
    fn a_word_written_as_a_transport_path_is_that_path_in_both_checkers()
    {
        let mut arena = CoreArena::new();
        let (mut declarations, circle) = one_loop(&mut arena);
        let at_point = arena.value_type_path(circle.carrier, circle.point, circle.point);
        // `loop then ε`: the loop transported along the empty word, written
        // as a constructor of the words, whose type is the words' own.
        let joined = gandr_core_term::identity::then(
            &mut arena,
            circle.carrier,
            circle.point,
            circle.named,
            circle.empty,
        );
        let joined = arena.value_returned(joined);
        let composed = arena.value_type_path(at_point, joined, circle.named);
        let looped = arena.value_here(circle.named);
        declarations.push(definition(ConstantIndex::from(3_usize), composed, looped));
        // `back(ℓ⁻¹ ∷ ε)`: the inverse letter's word, inverted, is the loop.
        let inverted = gandr_core_term::identity::back(
            &mut arena,
            circle.carrier,
            circle.point,
            circle.inverse,
        );
        let inverted = arena.value_returned(inverted);
        let reverted = arena.value_type_path(at_point, inverted, circle.named);
        declarations.push(definition(ConstantIndex::from(4_usize), reverted, looped));
        // The composite is not reflexivity.
        let reflexive = arena.value_type_path(at_point, joined, circle.empty);
        let stays = arena.value_here(circle.empty);
        declarations.push(definition(ConstantIndex::from(5_usize), reflexive, stays));
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, what) in [
            (3, "the loop composed with the empty word is the loop"),
            (4, "the inverse letter's word inverted is the loop"),
        ] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{what}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "and the kernel follows the word as the same path: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert!(
            matches!(
                report.judged()[5].verdict(),
                Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
            ),
            "the composite is not reflexivity: {:?}",
            report.judged()[5].verdict()
        );
    }

    #[test]
    fn an_absurd_case_rests_on_apart_endpoints_in_both_checkers()
    {
        let looped = ConstructorTag::from(1_usize);
        let unlooped = ConstructorTag::from(2_usize);
        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let empty = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
        let base = word(&mut arena, &[]);
        // `λe. case e {}` at `Path(Circle, left, right) → F Empty`, its type,
        // its lambda and its case.
        let absurd = |arena: &mut CoreArena, left: ValueId, right: ValueId| {
            let path = arena.value_type_path(own, left, right);
            let motive = arena.comp_type_returner(empty);
            let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let case = arena.computation_data_case(scrutinee, motive, vec![]);
            let lambda = arena.computation_lambda(case);
            let arrow = arena.comp_type_arrow(path, motive);
            (lambda, arrow, case)
        };
        let thunked = |arena: &mut CoreArena,
                       (lambda, arrow, case): (
            gandr_core_term::ComputationId,
            gandr_core_term::CompTypeId,
            gandr_core_term::ComputationId,
        )| {
            (
                arena.value_thunk(lambda),
                arena.value_type_thunk(arrow),
                case,
            )
        };
        let once = word(&mut arena, &[looped]);
        let formed = absurd(&mut arena, once, base);
        let (apart, apart_type, _) = thunked(&mut arena, formed);
        let named = arena.value_constant(ConstantIndex::from(3_usize));
        let formed = absurd(&mut arena, named, base);
        let (by_name, by_name_type, _) = thunked(&mut arena, formed);
        let cancelled = word(&mut arena, &[looped, unlooped]);
        let formed = absurd(&mut arena, cancelled, base);
        let (agree, agree_type, agree_case) = thunked(&mut arena, formed);
        // `λx. λe. case e {}` at `(x : Circle) → Path(Circle, Loop(x), Base)
        // → F Empty`: an endpoint holds a variable of the circle.
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let open_word = arena.value_constructor(own, looped, vec![variable]);
        let (inner, arrow, open_case) = absurd(&mut arena, open_word, base);
        let outer = arena.computation_lambda(inner);
        let open = arena.value_thunk(outer);
        let pi = arena.comp_type_pi(own, arrow);
        let open_type = arena.value_type_thunk(pi);
        let declarations = vec![
            circle(&mut arena, cancellations()),
            Declaration::data(
                ConstantIndex::from(1_usize),
                DataSignature::new(vec![], vec![], kind).into(),
                OriginToken::from(1_usize),
            ),
            definition(ConstantIndex::from(2_usize), apart_type, apart),
            definition(ConstantIndex::from(3_usize), own, once),
            definition(ConstantIndex::from(4_usize), by_name_type, by_name),
            definition(ConstantIndex::from(5_usize), agree_type, agree),
            definition(ConstantIndex::from(6_usize), open_type, open),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        for (position, what) in [
            (2, "`Loop(Base)` and `Base` are apart"),
            (4, "a definition of `Loop(Base)` is read as its body"),
        ] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{what}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "and the kernel decides alike: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert_eq!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::NotApart {
                at: agree_case,
                reason: gandr_kernel_term::Apartness::Agree,
            }),
            "`Loop(Unloop(Base))` is `Base`"
        );
        assert_eq!(
            report.judged()[6].verdict(),
            Verdict::Refused(CheckRefusal::NotApart {
                at: open_case,
                reason: gandr_kernel_term::Apartness::Open,
            }),
            "`Loop(x)` is `Base` once `x` is `Unloop(Base)`"
        );
    }

    #[test]
    fn a_fold_rests_on_the_laws_of_the_rules_it_computes_apart()
    {
        let (turn, unturn) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
        let (turn_unturn, unturn_turn) =
            (ConstantIndex::from(3_usize), ConstantIndex::from(4_usize));
        let wind = ConstantIndex::from(5_usize);
        let first = gandr_kernel_term::RuleIndex::from(0_usize);
        for (laws, admitted) in [
            (vec![turn_unturn, unturn_turn], true),
            (vec![], false),
            (vec![unturn_turn, turn_unturn], false),
        ] {
            let mut arena = CoreArena::new();
            let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let returner = arena.comp_type_returner(integer);
            // The integers' successor and predecessor, holes conversion
            // cannot see through.
            let step = arena.comp_type_arrow(integer, returner);
            let step = arena.value_type_thunk(step);
            let call = |arena: &mut CoreArena, operation, argument| {
                let operation = arena.value_constant(operation);
                let forced = arena.computation_force(operation);
                arena.computation_application(forced, argument)
            };
            // `Π n. turn(unturn(n)) = n`, the law of `Loop(Unloop(x)) ~> x`,
            // and its mirror.
            let mut law = |first_operation, second_operation| {
                let n = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let inner = call(&mut arena, second_operation, n);
                let inner = arena.value_returned(inner);
                let outer = call(&mut arena, first_operation, inner);
                let outer = arena.value_returned(outer);
                let path = arena.value_type_path(integer, outer, n);
                let returner = arena.comp_type_returner(path);
                let pi = arena.comp_type_pi(integer, returner);
                arena.value_type_thunk(pi)
            };
            let first_law = law(turn, unturn);
            let second_law = law(unturn, turn);
            // `fix f. λy. case y { Base ⇒ return 0; Loop(x) ⇒ turn(f(x));
            // Unloop(x) ⇒ unturn(f(x)) }`, each recursive run written where
            // a value is read: at `Loop(Unloop(x))` it computes
            // `turn(unturn(f(x)))`, which meets `f(x)` only by the first law.
            let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                gandr_kernel_term::IntegerLiteral::new(
                    gandr_kernel_term::Sign::NonNegative,
                    gandr_kernel_term::Magnitude::zero(),
                ),
            ));
            let base = arena.computation_return(zero);
            let mut arm = |operation| {
                let recursive =
                    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
                let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let forced = arena.computation_force(recursive);
                let folded = arena.computation_application(forced, field);
                let folded = arena.value_returned(folded);
                let applied = call(&mut arena, operation, folded);
                arena.computation_lambda(applied)
            };
            let looping = arm(turn);
            let unlooping = arm(unturn);
            let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let case =
                arena.computation_data_case(argument, returner, vec![base, looping, unlooping]);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(
                lambda,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            );
            let body = arena.value_thunk(fixpoint);
            let arrow = arena.comp_type_arrow(own, returner);
            let declared = arena.value_type_thunk(arrow);
            let hole = |constant: ConstantIndex, stated| {
                Declaration::new(
                    constant,
                    Maybe::Present(stated),
                    Maybe::Absent(gandr_core_checker::body::Absent::Hole),
                    OriginToken::from(usize::from(constant)),
                )
            };
            let declarations = vec![
                circle(&mut arena, cancellations()),
                hole(turn, step),
                hole(unturn, step),
                hole(turn_unturn, first_law),
                hole(unturn_turn, second_law),
                definition(wind, declared, body).lawful(laws),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            let verdict = report.judged()[5].verdict();
            if admitted {
                assert!(
                    matches!(verdict, Verdict::Checked { .. }),
                    "each rule's law relates the fold's two sides of it: {verdict:?}"
                );
                let assumed: Vec<_> = crossed.readmitted()[1 .. 5]
                    .iter()
                    .map(|entry| match *entry.outcome() {
                        Outcome::Assumed { admitted, .. } => admitted.position(),
                        ref other @ (Outcome::Data { .. }
                        | Outcome::Defined { .. }
                        | Outcome::Marked(_)
                        | Outcome::Static
                        | Outcome::Refused(_)
                        | Outcome::Rejected(_)) => {
                            panic!("each hole crosses as an axiom: {other:?}")
                        },
                    })
                    .collect();
                let Outcome::Defined { ref audit, .. } = *crossed.readmitted()[5].outcome()
                else {
                    panic!(
                        "and the kernel re-derives the fold from its laws: {:?}",
                        crossed.readmitted()[5].outcome()
                    );
                };
                assert_eq!(
                    audit.axioms(),
                    assumed.as_slice(),
                    "the fold rests on its laws as on the operations it calls"
                );
            }
            else {
                assert!(
                    matches!(
                        verdict,
                        Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. }) if rule == first
                    ),
                    "without the first rule's law the fold is refused by that rule: {verdict:?}"
                );
                assert!(
                    matches!(crossed.readmitted()[5].outcome(), Outcome::Marked(_)),
                    "and the kernel is offered nothing: {:?}",
                    crossed.readmitted()[5].outcome()
                );
            }
        }
    }

    #[test]
    fn a_fold_into_the_paths_of_a_set_respects_its_rules()
    {
        let first = gandr_kernel_term::RuleIndex::from(0_usize);
        let (lemma, fold) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
        // The presented integers are a set: no cells, no loop at them. The
        // native integers are no data type, so nothing reads them as one.
        for set in [true, false] {
            let mut arena = CoreArena::new();
            let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
            let (carrier, point) = if set {
                (own, word(&mut arena, &[]))
            }
            else {
                let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
                let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                    gandr_kernel_term::IntegerLiteral::new(
                        gandr_kernel_term::Sign::NonNegative,
                        gandr_kernel_term::Magnitude::zero(),
                    ),
                ));
                (integer, zero)
            };
            let path = arena.value_type_path(carrier, point, point);
            let returner = arena.comp_type_returner(path);
            // A lemma conversion cannot see through, from a loop at the point
            // to a loop at the point.
            let step = arena.comp_type_arrow(path, returner);
            let step = arena.value_type_thunk(step);
            // `fix f. λy. case y { Base ⇒ return here(p); Loop(x) ⇒
            // lemma(f(x)); Unloop(x) ⇒ lemma(f(x)) }`: at `Loop(Unloop(x))`
            // it computes `lemma(lemma(f(x)))`, which conversion never meets
            // with `f(x)`; both are loops at `p`.
            let reflexivity = arena.value_here(point);
            let base = arena.computation_return(reflexivity);
            let mut arm = || {
                let recursive =
                    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
                let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let forced = arena.computation_force(recursive);
                let folded = arena.computation_application(forced, field);
                let folded = arena.value_returned(folded);
                let operation = arena.value_constant(lemma);
                let operation = arena.computation_force(operation);
                let applied = arena.computation_application(operation, folded);
                arena.computation_lambda(applied)
            };
            let looping = arm();
            let unlooping = arm();
            let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let case =
                arena.computation_data_case(argument, returner, vec![base, looping, unlooping]);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(
                lambda,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            );
            let body = arena.value_thunk(fixpoint);
            let arrow = arena.comp_type_arrow(own, returner);
            let declared = arena.value_type_thunk(arrow);
            let declarations = vec![
                circle(&mut arena, cancellations()),
                Declaration::new(
                    lemma,
                    Maybe::Present(step),
                    Maybe::Absent(gandr_core_checker::body::Absent::Hole),
                    OriginToken::from(usize::from(lemma)),
                ),
                definition(fold, declared, body),
            ];
            let (report, crossed) = run(&mut arena, &declarations);
            let verdict = report.judged()[2].verdict();
            if set {
                assert!(
                    matches!(verdict, Verdict::Checked { .. }),
                    "two loops at one point of a set are one loop: {verdict:?}"
                );
                assert!(
                    matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
                    "and the kernel re-derives the fold: {:?}",
                    crossed.readmitted()[2].outcome()
                );
            }
            else {
                assert!(
                    matches!(
                        verdict,
                        Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. }) if rule == first
                    ),
                    "loops in a type not read as a set are compared as written: {verdict:?}"
                );
            }
        }
    }

    #[test]
    fn dependent_data_parameters_and_case_motives()
    {
        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(parameter, Level::zero());
        let family = ConstantIndex::from(0_usize);
        let indexed = ConstantIndex::from(1_usize);
        let declaration = Declaration::data(
            family,
            DataSignature::new(vec![kind], vec![vec![element]], kind).into(),
            OriginToken::from(0_usize),
        );
        let unit_type = arena.value_type_unit();
        let unit_code = arena.value_quote(unit_type);
        let unit = arena.value_unit();
        let datatype = arena.value_type_data(family, vec![unit_code]);
        let index_declaration = Declaration::data(
            indexed,
            DataSignature::new(vec![datatype], vec![vec![]], kind).into(),
            OriginToken::from(1_usize),
        );
        let scrutinee =
            arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let motive_type = arena.value_type_data(indexed, vec![bound]);
        let motive = arena.comp_type_returner(motive_type);
        let branch_index =
            arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![bound]);
        let branch_type = arena.value_type_data(indexed, vec![branch_index]);
        let branch_value =
            arena.value_constructor(branch_type, ConstructorTag::from(0_usize), vec![]);
        let returned = arena.computation_return(branch_value);
        let branch = arena.computation_lambda(returned);
        let case = arena.computation_data_case(scrutinee, motive, vec![branch]);
        let body = arena.value_thunk(case);
        let expected_type = arena.value_type_data(indexed, vec![scrutinee]);
        let expected = arena.comp_type_returner(expected_type);
        let expected = arena.value_type_thunk(expected);
        let missing = arena.computation_data_case(scrutinee, motive, vec![]);
        let missing_body = arena.value_thunk(missing);
        let declarations = [
            declaration,
            index_declaration,
            definition(ConstantIndex::from(2_usize), expected, body),
            definition(ConstantIndex::from(3_usize), expected, missing_body),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        assert!(
            matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
            "{:?}",
            report.judged()[2].verdict()
        );
        assert!(
            matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
            "{:?}",
            crossed.readmitted()[2].outcome()
        );
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::NonExhaustiveDataCase(missing))
        );
        assert!(crossed.audit().axioms().is_empty());
    }

    #[test]
    fn record_width_depth_and_projection()
    {
        let mut arena = CoreArena::new();
        let x = FieldLabel::from(String::from("x"));
        let y = FieldLabel::from(String::from("y"));
        let nested = FieldLabel::from(String::from("nested"));
        let missing = FieldLabel::from(String::from("missing"));
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let inner_wide = arena.value_type_record(BTreeMap::from([
            (x.clone(), unit_type),
            (y.clone(), unit_type),
        ]));
        let inner_narrow = arena.value_type_record(BTreeMap::from([(x.clone(), unit_type)]));
        let wide = arena.value_type_record(BTreeMap::from([
            (nested.clone(), inner_wide),
            (x.clone(), unit_type),
        ]));
        let narrow = arena.value_type_record(BTreeMap::from([(nested.clone(), inner_narrow)]));
        let empty = arena.value_type_record(BTreeMap::new());
        let inner = arena.value_record(BTreeMap::from([(x.clone(), unit), (y, unit)]));
        let record = arena.value_record(BTreeMap::from([(nested.clone(), inner), (x, unit)]));
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returned);
        let function = arena.value_thunk(lambda);
        let result = arena.comp_type_returner(narrow);
        let arrow = arena.comp_type_arrow(wide, result);
        let arrow = arena.value_type_thunk(arrow);
        let reverse_result = arena.comp_type_returner(wide);
        let reverse = arena.comp_type_arrow(narrow, reverse_result);
        let reverse = arena.value_type_thunk(reverse);
        let projection = arena.computation_record_projection(record, nested);
        let projected = arena.value_thunk(projection);
        let projected_type = arena.comp_type_returner(inner_wide);
        let projected_type = arena.value_type_thunk(projected_type);
        let absent = arena.computation_record_projection(record, missing.clone());
        let absent_body = arena.value_thunk(absent);
        let missing_type = arena.value_type_record(BTreeMap::from([(missing, unit_type)]));
        let wrong_depth = arena.value_type_record(BTreeMap::from([(
            FieldLabel::from(String::from("nested")),
            unit_type,
        )]));
        let empty_record = arena.value_record(BTreeMap::new());
        let declarations = [
            definition(ConstantIndex::from(0_usize), narrow, record),
            definition(ConstantIndex::from(1_usize), arrow, function),
            definition(ConstantIndex::from(2_usize), projected_type, projected),
            definition(ConstantIndex::from(3_usize), empty, record),
            definition(ConstantIndex::from(4_usize), projected_type, absent_body),
            definition(ConstantIndex::from(5_usize), missing_type, record),
            definition(ConstantIndex::from(6_usize), wrong_depth, record),
            definition(ConstantIndex::from(7_usize), reverse, function),
            Declaration::new(
                ConstantIndex::from(8_usize),
                Maybe::Absent(gandr_core_checker::signature::Absent::Unsigned),
                Maybe::Present(record),
                OriginToken::from(8_usize),
            ),
            Declaration::new(
                ConstantIndex::from(9_usize),
                Maybe::Absent(gandr_core_checker::signature::Absent::Unsigned),
                Maybe::Present(empty_record),
                OriginToken::from(9_usize),
            ),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        for position in 0 .. 4_usize {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{position}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "{position}: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert_eq!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::AbsentRecordField(absent))
        );
        assert_eq!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::MissingRecordField {
                at: record,
                expected: missing_type
            })
        );
        assert!(matches!(
            report.judged()[6].verdict(),
            Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
        ));
        assert!(matches!(
            report.judged()[7].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ));
        let Verdict::Synthesised { synthesised, .. } = report.judged()[8].verdict()
        else {
            panic!("an unsigned record infers its fields");
        };
        let Some(matched_native_node) = arena.value_type(synthesised.produced().id())
        else {
            panic!("record classifier");
        };
        let ValueType::Record(ref fields) = *matched_native_node
        else {
            panic!("record classifier");
        };
        assert!(
            fields
                .keys()
                .map(core::convert::AsRef::as_ref)
                .eq(["nested", "x"])
        );
        for (label, &field) in fields {
            if label.as_ref() == "x" {
                assert!(arena.value_type(field).is_some_and(
                    |held| matches!(*held, ValueType::Product(ref parts) if parts.is_empty())
                ));
            }
            else {
                let Some(matched_native_node) = arena.value_type(field)
                else {
                    panic!("nested record classifier");
                };
                let ValueType::Record(ref inner) = *matched_native_node
                else {
                    panic!("nested record classifier");
                };
                assert!(
                    inner
                        .keys()
                        .map(core::convert::AsRef::as_ref)
                        .eq(["x", "y"])
                );
                assert!(inner.values().all(|&ty| arena.value_type(ty).is_some_and(
                    |held| matches!(*held, ValueType::Product(ref parts) if parts.is_empty())
                )));
            }
        }
        let Verdict::Synthesised { synthesised, .. } = report.judged()[9].verdict()
        else {
            panic!("the empty record has an exact empty classifier");
        };
        assert_eq!(
            arena.value_type(synthesised.produced().id()),
            arena.value_type(empty)
        );
        for position in [8_usize, 9] {
            assert!(matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ));
        }
        assert!(crossed.audit().axioms().is_empty());
    }

    #[test]
    fn term_indices_are_structural_in_both_checkers()
    {
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let returns_unit = arena.comp_type_returner(unit_type);
        let function = arena.comp_type_arrow(unit_type, returns_unit);
        let function = arena.value_type_thunk(function);
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let data = ConstantIndex::from(1_usize);
        let declaration = Declaration::data(
            data,
            DataSignature::new(vec![function], vec![vec![]], kind).into(),
            OriginToken::from(1_usize),
        );
        let returned = arena.computation_return(unit);
        let normal = arena.computation_lambda(returned);
        let normal = arena.value_thunk(normal);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let identity = arena.computation_return(variable);
        let identity = arena.computation_lambda(identity);
        let identity = arena.value_thunk(identity);
        let identity_definition = definition(ConstantIndex::from(0_usize), function, identity);
        let identity_reference = arena.value_constant(ConstantIndex::from(0_usize));
        let identity = arena.computation_force(identity_reference);
        let redex = arena.computation_application(identity, unit);
        let redex = arena.computation_lambda(redex);
        let redex = arena.value_thunk(redex);
        let copied_unit = arena.value_unit();
        let copied = arena.computation_return(copied_unit);
        let copied = arena.computation_lambda(copied);
        let copied = arena.value_thunk(copied);
        let reference = arena.value_constant(ConstantIndex::from(2_usize));
        let reference_copy = arena.value_constant(ConstantIndex::from(2_usize));
        let declared = arena.value_type_data(data, vec![normal]);
        let copied_type = arena.value_type_data(data, vec![copied]);
        let redex_type = arena.value_type_data(data, vec![redex]);
        let named_type = arena.value_type_data(data, vec![reference]);
        let named_copy_type = arena.value_type_data(data, vec![reference_copy]);
        let tag = ConstructorTag::from(0_usize);
        let copied_value = arena.value_constructor(copied_type, tag, vec![]);
        let redex_value = arena.value_constructor(redex_type, tag, vec![]);
        let named_value = arena.value_constructor(named_type, tag, vec![]);
        let named_copy_value = arena.value_constructor(named_copy_type, tag, vec![]);
        let (report, crossed) = run(&mut arena, &[
            identity_definition,
            declaration,
            definition(ConstantIndex::from(2_usize), function, normal),
            definition(ConstantIndex::from(3_usize), declared, copied_value),
            definition(ConstantIndex::from(4_usize), declared, redex_value),
            definition(ConstantIndex::from(5_usize), declared, named_value),
            definition(ConstantIndex::from(6_usize), named_type, named_copy_value),
        ]);
        for position in [0, 2, 3, 6] {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "{:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert_eq!(report.judged()[1].verdict(), Verdict::Data);
        for position in [4, 5] {
            assert!(matches!(
                report.judged()[position].verdict(),
                Verdict::Refused(CheckRefusal::TypeMismatch(_))
            ));
            assert!(matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Marked(CheckRefusal::TypeMismatch(_))
            ));
        }
    }

    #[test]
    fn empty_data_elimination_preserves_the_ambient_scope()
    {
        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let constant = ConstantIndex::from(0_usize);
        let declaration = Declaration::data(
            constant,
            DataSignature::new(vec![], vec![], kind).into(),
            OriginToken::from(0_usize),
        );
        let datatype = arena.value_type_data(constant, vec![]);
        let unit_type = arena.value_type_unit();
        let motive = arena.comp_type_returner(unit_type);
        let impossible = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(impossible, motive, vec![]);
        let lambda = arena.computation_lambda(case);
        let body = arena.value_thunk(lambda);
        let arrow = arena.comp_type_pi(datatype, motive);
        let declared = arena.value_type_thunk(arrow);
        let (report, crossed) = run(&mut arena, &[
            declaration,
            definition(ConstantIndex::from(1_usize), declared, body),
        ]);
        assert!(
            matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
            "{:?}",
            report.judged()[1].verdict()
        );
        assert!(
            matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
            "{:?}",
            crossed.readmitted()[1].outcome()
        );
        assert!(crossed.audit().axioms().is_empty());
    }

    #[test]
    fn native_signature_support_and_adoption()
    {
        use alloc::sync::Arc;

        use gandr_core_checker::DeclarationContent;
        use gandr_core_checker::check_declaration;
        use gandr_core_checker::check_declaration_supported;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let constant = ConstantIndex::from(0_usize);
        let declaration = Declaration::data(
            constant,
            DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
            OriginToken::from(0_usize),
        );
        let datatype = arena.value_type_data(constant, vec![]);
        let unit = arena.value_unit();
        let constructor =
            arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
        let use_site = definition(ConstantIndex::from(1_usize), datatype, constructor);
        let fresh = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            assert_eq!(check_declaration(&mut context, &declaration), Verdict::Data);
            check_declaration_supported(&mut context, &use_site)
        };
        let DeclarationContent::Data(ref signature) = *(declaration.content())
        else {
            panic!("native signature");
        };
        let adopted = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.adopt_data(constant, Arc::clone(signature)).unwrap();
            check_declaration_supported(&mut context, &use_site)
        };
        assert!(matches!(adopted.verdict(), Verdict::Checked { .. }));
        assert_eq!(fresh.verdict(), adopted.verdict());
        assert_eq!(fresh.support(), adopted.support());
        let [ref answer] = *(fresh.support().data_consulted())
        else {
            panic!("one nominal consultation despite repeated formation and introduction");
        };
        assert_eq!(answer.constant(), constant);
        assert_eq!(answer.signature(), Some(signature.as_ref()));

        let changed_declaration = Declaration::data(
            constant,
            DataSignature::new(vec![], vec![vec![]], kind).into(),
            OriginToken::from(0_usize),
        );
        let changed = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            assert_eq!(
                check_declaration(&mut context, &changed_declaration),
                Verdict::Data
            );
            check_declaration_supported(&mut context, &use_site)
        };
        assert_eq!(
            changed.verdict(),
            Verdict::Refused(CheckRefusal::ConstructorArity(constructor))
        );
        assert_ne!(
            fresh.support().data_consulted(),
            changed.support().data_consulted(),
            "an unchanged kind does not hide a changed constructor table"
        );
        let missing = check_declaration_supported(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &use_site,
        );
        assert_eq!(
            missing.verdict(),
            Verdict::Refused(CheckRefusal::NotADataType(constant))
        );
        let [ref absent] = *(missing.support().data_consulted())
        else {
            panic!("the missing nominal declaration was consulted");
        };
        assert_eq!(absent.constant(), constant);
        assert!(absent.signature().is_none());
    }

    #[test]
    fn tuple_projection_reads_each_component()
    {
        use gandr_core_term::Component;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let empty_type = arena.value_type_record(BTreeMap::new());
        let pair_type = arena.value_type_product(&[unit_type, unit_type]);
        let unit = arena.value_unit();
        let empty = arena.value_record(BTreeMap::new());
        let pair = arena.value_tuple(&[unit, unit]);
        let tuple = arena.value_tuple(&[unit, empty, pair]);
        let mut declarations = Vec::new();
        for (position, classifier) in [unit_type, empty_type, pair_type].into_iter().enumerate() {
            let projection = arena.computation_tuple_projection(tuple, Component::from(position));
            let body = arena.value_thunk(projection);
            let returner = arena.comp_type_returner(classifier);
            let declared = arena.value_type_thunk(returner);
            declarations.push(definition(ConstantIndex::from(position), declared, body));
        }
        let returner = arena.comp_type_returner(unit_type);
        let declared = arena.value_type_thunk(returner);
        let absent = arena.computation_tuple_projection(tuple, Component::from(3_usize));
        let absent_body = arena.value_thunk(absent);
        declarations.push(definition(
            ConstantIndex::from(3_usize),
            declared,
            absent_body,
        ));
        let second = arena.computation_tuple_projection(tuple, Component::from(1_usize));
        let second_body = arena.value_thunk(second);
        declarations.push(definition(
            ConstantIndex::from(4_usize),
            declared,
            second_body,
        ));
        let record = arena.value_record(BTreeMap::from([(
            FieldLabel::from(String::from("a")),
            unit,
        )]));
        let of_record = arena.computation_tuple_projection(record, Component::from(0_usize));
        let of_record_body = arena.value_thunk(of_record);
        declarations.push(definition(
            ConstantIndex::from(5_usize),
            declared,
            of_record_body,
        ));
        let (report, crossed) = run(&mut arena, &declarations);
        for position in 0 .. 3_usize {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{position}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "{position}: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert_eq!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::AbsentTupleComponent(absent))
        );
        assert!(matches!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ));
        assert!(matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
        ));
        assert!(crossed.audit().axioms().is_empty());
    }

    /// A split crosses as the projection binds the kernel judges: reading the
    /// last of a variable pair's components, which a wrong shift would read
    /// from the first and the kernel would refuse; reading a closed triple's
    /// last component; and splitting the unit into its body.
    #[test]
    fn a_split_crosses_as_its_projection_binds()
    {
        use gandr_core_term::ComponentCount;
        let mut arena = CoreArena::new();
        let unit_type = arena.value_type_unit();
        let pair_type = arena.value_type_product(&[unit_type, unit_type]);
        let nested_type = arena.value_type_product(&[unit_type, pair_type]);
        let unit = arena.value_unit();
        let empty = arena.value_record(BTreeMap::new());
        let pair = arena.value_tuple(&[unit, unit]);
        let tuple = arena.value_tuple(&[unit, empty, pair]);
        let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returns_last = arena.computation_return(innermost);
        let split_argument =
            arena.computation_split(innermost, ComponentCount::from(2_usize), returns_last);
        let lambda = arena.computation_lambda(split_argument);
        let returns_pair = arena.comp_type_returner(pair_type);
        let arrow = arena.comp_type_arrow(nested_type, returns_pair);
        let function_type = arena.value_type_thunk(arrow);
        let function = arena.value_thunk(lambda);
        let split_tuple =
            arena.computation_split(tuple, ComponentCount::from(3_usize), returns_last);
        let returns_unit = arena.computation_return(unit);
        let split_unit = arena.computation_split(unit, ComponentCount::default(), returns_unit);
        let declared_pair = arena.value_type_thunk(returns_pair);
        let returns_unit_type = arena.comp_type_returner(unit_type);
        let declared_unit = arena.value_type_thunk(returns_unit_type);
        let tuple_body = arena.value_thunk(split_tuple);
        let unit_body = arena.value_thunk(split_unit);
        let declarations = [
            definition(ConstantIndex::from(0_usize), function_type, function),
            definition(ConstantIndex::from(1_usize), declared_pair, tuple_body),
            definition(ConstantIndex::from(2_usize), declared_unit, unit_body),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        for position in 0 .. 3_usize {
            assert!(
                matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
                "{position}: {:?}",
                report.judged()[position].verdict()
            );
            assert!(
                matches!(
                    crossed.readmitted()[position].outcome(),
                    Outcome::Defined { .. }
                ),
                "{position}: {:?}",
                crossed.readmitted()[position].outcome()
            );
        }
        assert!(crossed.audit().axioms().is_empty());
    }
}
