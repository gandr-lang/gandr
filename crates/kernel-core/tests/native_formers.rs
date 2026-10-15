//! Native nominal declarations, dependent cases and structural records through
//! admission.

extern crate alloc;

#[cfg(test)]
mod native_formers
{
    use alloc::collections::BTreeMap;

    use anodized::spec;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_core::CheckedId;
    use gandr_kernel_core::CompTypeHead;
    use gandr_kernel_core::EngineClaim;
    use gandr_kernel_core::Environment;
    use gandr_kernel_core::ExpectedComputationShape;
    use gandr_kernel_core::KernelError;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayBudget;
    use gandr_kernel_core::ReplayNode;
    use gandr_kernel_core::ReplaySides;
    use gandr_kernel_core::Unfoldable;
    use gandr_kernel_core::Unfoldings;
    use gandr_kernel_core::replay;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::CellIndex;
    use gandr_kernel_term::CompTypeId;
    use gandr_kernel_term::Component;
    use gandr_kernel_term::ComputationId;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::FreeCell;
    use gandr_kernel_term::FreeCells;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::ValueTypeId;
    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;

    /// Admit a fresh nominal identity with one unit field.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned position names a checked, monomorphic data
    ///   declaration.
    /// - panics: if the well-formed fixture is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal carrier tables do not identify independently
    ///   admitted heads.
    /// - witness: `native_formers::native_formers::nominal_identity_and_constructor_refusals`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position && position.checked_add(1) == Some(environment.entries().len()))]
    fn mono(environment: &mut Environment) -> CheckedId
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit = arena.value_type_unit();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![unit]],
            kind,
        );
        environment
            .add_decl(declaration)
            .expect("well-formed native data")
    }

    #[test]
    fn nominal_identity_and_constructor_refusals()
    {
        let mut environment = Environment::new();
        let first = mono(&mut environment).position();
        let second = mono(&mut environment).position();
        for (tag, field_count, expected) in [
            (
                ConstructorTag::from(1),
                1,
                KernelError::UnknownConstructor {
                    tag: ConstructorTag::from(1),
                },
            ),
            (ConstructorTag::from(0), 0, KernelError::ConstructorArity),
            (ConstructorTag::from(0), 2, KernelError::ConstructorArity),
        ] {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(first, vec![]);
            let unit = arena.value_unit();
            let constructor = arena.value_constructor(datatype, tag, vec![unit; field_count]);
            let declaration = staging.def(LevelSignature::monomorphic(), datatype, constructor);
            assert_eq!(environment.add_decl(declaration), Err(expected));
        }
        let mut staging = environment.stage();
        let arena = staging.arena();
        let first_type = arena.value_type_data(first, vec![]);
        let second_type = arena.value_type_data(second, vec![]);
        let unit = arena.value_unit();
        let constructor = arena.value_constructor(first_type, ConstructorTag::from(0), vec![unit]);
        let declaration = staging.def(LevelSignature::monomorphic(), second_type, constructor);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ValueTypeMismatch(_))
        ));

        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(first, vec![]);
        let unit = arena.value_unit();
        let constructor = arena.value_constructor(datatype, ConstructorTag::from(0), vec![unit]);
        let declaration = staging.def(LevelSignature::monomorphic(), datatype, constructor);
        let admitted = environment
            .add_decl(declaration)
            .expect("matching nominal constructor");
        assert!(environment.audit(admitted).axioms().is_empty());

        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(first, vec![]);
        let unit = arena.value_unit();
        let constructor = arena.value_constructor(datatype, ConstructorTag::from(0), vec![unit]);
        let declaration =
            staging.sealed_def(LevelSignature::monomorphic(), datatype, constructor, vec![
                first,
            ]);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::SealingProvenanceNotProjected { atom: first })
        );
    }

    #[test]
    fn data_signature_formation_checks_fields_and_parameters()
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let unit = staging.arena().value_type_unit();
        let declaration = staging.data(LevelSignature::monomorphic(), vec![], vec![], unit);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::DataKindNotUniverse)
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let variable = arena.value_variable(DeBruijnIndex::from(0));
        let escaped = arena.value_type_element(variable, Level::zero());
        let declaration = staging.data(LevelSignature::monomorphic(), vec![escaped], vec![], kind);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::UnboundVariable {
                index: DeBruijnIndex::from(0)
            })
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![kind]],
            kind,
        );
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::UniverseViolation(_))
        ));

        let nominal = mono(&mut environment).position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit = arena.value_unit();
        let datatype = arena.value_type_data(nominal, vec![unit]);
        let declaration = staging.axiom(LevelSignature::monomorphic(), datatype);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::DataArgumentArity)
        );

        let missing = ConstantIndex::from(environment.entries().len());
        let mut staging = environment.stage();
        let datatype = staging.arena().value_type_data(missing, vec![]);
        let declaration = staging.axiom(LevelSignature::monomorphic(), datatype);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::NotADataType { index: missing })
        );
    }

    #[test]
    fn data_parameters_preserve_open_indices()
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let zero = arena.value_variable(DeBruijnIndex::from(0));
        let one = arena.value_variable(DeBruijnIndex::from(1));
        let parameter_type = arena.value_type_element(zero, Level::zero());
        let field_type = arena.value_type_element(one, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![universe, parameter_type],
            vec![vec![field_type]],
            universe,
        );
        let nominal = environment
            .add_decl(declaration)
            .expect("dependent parameter telescope")
            .position();

        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(nominal, vec![one, zero]);
        let constructor = arena.value_constructor(datatype, ConstructorTag::from(0), vec![zero]);
        let result = arena.computation_return(constructor);
        let inner = arena.computation_lambda(result);
        let outer = arena.computation_lambda(inner);
        let result_type = arena.comp_type_returner(datatype);
        let inner_type = arena.comp_type_pi(parameter_type, result_type);
        let outer_type = arena.comp_type_pi(universe, inner_type);
        let declared = arena.value_type_thunk(outer_type);
        let body = arena.value_thunk(outer);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        let admitted = environment
            .add_decl(declaration)
            .expect("ambient type and term arguments retain their scopes");
        assert!(environment.audit(admitted).axioms().is_empty());
    }

    #[test]
    fn data_case_checks_coverage_and_motive()
    {
        let mut environment = Environment::new();
        let nominal = mono(&mut environment).position();
        for count in [0, 2] {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(nominal, vec![]);
            let unit_type = arena.value_type_unit();
            let unit = arena.value_unit();
            let constructor =
                arena.value_constructor(datatype, ConstructorTag::from(0), vec![unit]);
            let motive = arena.comp_type_returner(unit_type);
            let body = arena.computation_return(unit);
            let branch = arena.computation_lambda(body);
            let case = arena.computation_data_case(constructor, motive, vec![branch; count]);
            let body = arena.value_thunk(case);
            let declared = arena.value_type_thunk(motive);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            assert_eq!(
                environment.add_decl(declaration),
                Err(KernelError::NonExhaustiveDataCase)
            );
        }
        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(nominal, vec![]);
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let constructor = arena.value_constructor(datatype, ConstructorTag::from(0), vec![unit]);
        let motive = arena.comp_type_returner(unit_type);
        let parameter = arena.value_variable(DeBruijnIndex::from(0));
        let body = arena.computation_return(parameter);
        let branch = arena.computation_lambda(body);
        let case = arena.computation_data_case(constructor, motive, vec![branch]);
        let result = arena.computation_return(unit);
        let body = arena.value_thunk(case);
        let declared = arena.value_type_thunk(motive);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        environment
            .add_decl(declaration)
            .expect("constructor-directed branch type");
        let mut arena = environment.arena().clone();
        let trace = [ConversionDecision::ComparedShared {
            left: ReplayNode::Other,
            right: ReplayNode::Other,
        }];
        assert_eq!(
            replay(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(case, result),
                EngineClaim::Convertible,
                trace,
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let wrong_motive = arena.comp_type_returner(datatype);
        let bad_case = arena.computation_data_case(constructor, wrong_motive, vec![branch]);
        let body = arena.value_thunk(bad_case);
        let declared = arena.value_type_thunk(wrong_motive);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ValueTypeMismatch(_))
        ));
    }

    #[test]
    fn a_case_respects_its_type_s_rules_or_is_refused_by_the_rule()
    {
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::PresentedRule;
        use gandr_kernel_term::RuleNode;
        let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
        let succ = RuleNode::Constructor(ConstructorTag::from(1_usize));
        // `Succ(Succ(x)) ~> x`: the naturals modulo two, where a case could
        // tell `Succ(Succ(Zero))` from `Zero`.
        let modulo =
            Presentation::new(vec![PresentedRule::new([succ, succ, x].into(), [x].into())]);
        for (presentation, presented) in [(Presentation::default(), false), (modulo, true)] {
            let mut environment = Environment::new();
            let mut staging = environment.stage();
            let arena = staging.arena();
            let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let naturals = staging
                .data(
                    LevelSignature::monomorphic(),
                    vec![],
                    vec![vec![], vec![own]],
                    kind,
                )
                .presented(presentation);
            let nominal = environment
                .add_decl(naturals)
                .expect("the naturals admit, presented or free")
                .position();
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(nominal, vec![]);
            let zero = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
            let unit_type = arena.value_type_unit();
            let unit = arena.value_unit();
            let motive = arena.comp_type_returner(unit_type);
            let returned = arena.computation_return(unit);
            let successor = arena.computation_lambda(returned);
            // A bare case: at `Succ(Succ(x))` it returns, at `x` it is stuck.
            let case = arena.computation_data_case(zero, motive, vec![returned, successor]);
            let body = arena.value_thunk(case);
            let declared = arena.value_type_thunk(motive);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            let admitted = environment.add_decl(declaration).map(|_admitted| ());
            if presented {
                assert_eq!(
                    admitted,
                    Err(KernelError::RuleNotRespected(
                        gandr_kernel_term::RuleIndex::from(0_usize)
                    )),
                    "a bare case over the presented naturals is refused at their rule"
                );
            }
            else {
                assert_eq!(
                    admitted,
                    Ok(()),
                    "the same case over the free naturals admits"
                );
            }
            // `fix f. λy. case y { Zero ⇒ return (); Succ(x) ⇒ f(x) }`: at
            // `Succ(Succ(x))` it descends twice to the call stuck at `x`.
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(nominal, vec![]);
            let unit_type = arena.value_type_unit();
            let unit = arena.value_unit();
            let motive = arena.comp_type_returner(unit_type);
            let returned = arena.computation_return(unit);
            let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let called = arena.computation_application(forced, field);
            let descending = arena.computation_lambda(called);
            let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
            let case = arena.computation_data_case(argument, motive, vec![returned, descending]);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(
                lambda,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            );
            let body = arena.value_thunk(fixpoint);
            let arrow = arena.comp_type_arrow(datatype, motive);
            let declared = arena.value_type_thunk(arrow);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            assert_eq!(
                environment.add_decl(declaration).map(|_admitted| ()),
                Ok(()),
                "a fixpoint meeting itself at both sides admits, presented or free"
            );
        }
    }

    /// Admit `declared` as an axiom.
    ///
    /// # Specification
    /// - requires: `declared` forms in the environment.
    /// - ensures: the returned position names an axiom of that type.
    /// - panics: if the axiom is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the fold's witness, which names these axioms.
    /// - witness: `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
    #[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
    fn assume(
        environment: &mut Environment,
        declared: impl FnOnce(&mut gandr_kernel_term::TermArena) -> ValueTypeId,
    ) -> ConstantIndex
    {
        let mut staging = environment.stage();
        let declared = declared(staging.arena());
        let axiom = staging.axiom(LevelSignature::monomorphic(), declared);
        environment
            .add_decl(axiom)
            .expect("the axiom admits")
            .position()
    }

    #[test]
    fn a_fold_rests_on_the_law_of_each_rule_it_computes_apart()
    {
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::PresentedRule;
        use gandr_kernel_term::RuleNode;
        let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
        let around = RuleNode::Constructor(ConstructorTag::from(1_usize));
        let back = RuleNode::Constructor(ConstructorTag::from(2_usize));
        // The circle: a point, a loop and its inverse, the two cancellations
        // its rules.
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let circle = staging
            .data(
                LevelSignature::monomorphic(),
                vec![],
                vec![vec![], vec![own], vec![own]],
                kind,
            )
            .presented(Presentation::new(vec![
                PresentedRule::new([around, back, x].into(), [x].into()),
                PresentedRule::new([back, around, x].into(), [x].into()),
            ]));
        let circle = environment
            .add_decl(circle)
            .expect("the circle admits")
            .position();
        // The integers' successor and predecessor, opaque to conversion, and
        // the two laws a model of the circle owes: `turn(unturn(n)) = n` and
        // `unturn(turn(n)) = n`, each assumed.
        let step = |arena: &mut gandr_kernel_term::TermArena| {
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let returner = arena.comp_type_returner(integer);
            let arrow = arena.comp_type_arrow(integer, returner);
            arena.value_type_thunk(arrow)
        };
        let turn = assume(&mut environment, step);
        let unturn = assume(&mut environment, step);
        let call = |arena: &mut gandr_kernel_term::TermArena, operation, argument| {
            let operation = arena.value_constant(operation);
            let forced = arena.computation_force(operation);
            let applied = arena.computation_application(forced, argument);
            arena.value_returned(applied)
        };
        let law = |first, second| {
            move |arena: &mut gandr_kernel_term::TermArena| {
                let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
                let n = arena.value_variable(DeBruijnIndex::from(0_u32));
                let inner = call(arena, second, n);
                let outer = call(arena, first, inner);
                let path = arena.value_type_path(integer, outer, n);
                let returner = arena.comp_type_returner(path);
                let pi = arena.comp_type_pi(integer, returner);
                arena.value_type_thunk(pi)
            }
        };
        let turn_unturn = assume(&mut environment, law(turn, unturn));
        let unturn_turn = assume(&mut environment, law(unturn, turn));
        // `fix f. λy. case y { Base ⇒ return 0; Loop(x) ⇒ r ← f(x); turn(r);
        // Unloop(x) ⇒ r ← f(x); unturn(r) }`, its runs elaborated into binds
        // as the bridge delivers them: at `Loop(Unloop(x))` it computes
        // `turn(unturn(f(x)))`, which meets `f(x)` only by the first law.
        let wind = |environment: &mut Environment, laws: Vec<ConstantIndex>| {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(circle, vec![]);
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let motive = arena.comp_type_returner(integer);
            let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                gandr_kernel_term::IntegerLiteral::new(
                    gandr_kernel_term::Sign::NonNegative,
                    gandr_kernel_term::Magnitude::zero(),
                ),
            ));
            let base = arena.computation_return(zero);
            let mut arm = |operation| {
                let recursive = arena.value_variable(DeBruijnIndex::from(2_u32));
                let field = arena.value_variable(DeBruijnIndex::from(0_u32));
                let forced = arena.computation_force(recursive);
                let folded = arena.computation_application(forced, field);
                let result = arena.value_variable(DeBruijnIndex::from(0_u32));
                let operation = arena.value_constant(operation);
                let operation = arena.computation_force(operation);
                let applied = arena.computation_application(operation, result);
                let sequenced = arena.computation_bind(folded, applied);
                arena.computation_lambda(sequenced)
            };
            let looped = arm(turn);
            let unlooped = arm(unturn);
            let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
            let case = arena.computation_data_case(argument, motive, vec![base, looped, unlooped]);
            let lambda = arena.computation_lambda(case);
            let fixpoint = arena.computation_fixpoint(
                lambda,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            );
            let body = arena.value_thunk(fixpoint);
            let arrow = arena.comp_type_arrow(datatype, motive);
            let declared = arena.value_type_thunk(arrow);
            let declaration = staging
                .def(LevelSignature::monomorphic(), declared, body)
                .lawful(laws);
            environment.add_decl(declaration)
        };
        let first = Err(KernelError::RuleNotRespected(
            gandr_kernel_term::RuleIndex::from(0_usize),
        ));
        assert_eq!(
            wind(&mut environment, vec![]).map(|_admitted| ()),
            first,
            "with no law the fold computes the first rule's sides apart"
        );
        assert_eq!(
            wind(&mut environment, vec![unturn_turn, turn_unturn]).map(|_admitted| ()),
            first,
            "the second law does not state the first rule"
        );
        let admitted = wind(&mut environment, vec![turn_unturn, unturn_turn])
            .expect("each rule's law relates the fold's two sides of it");
        assert_eq!(
            environment.audit(admitted).axioms(),
            [turn, unturn, turn_unturn, unturn_turn],
            "the fold rests on its laws as on the operations it calls"
        );
    }

    #[test]
    fn empty_nominal_case_eliminates_only_an_empty_declaration()
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let universe = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(LevelSignature::monomorphic(), vec![], vec![], universe);
        let empty = environment
            .add_decl(declaration)
            .expect("empty data signature")
            .position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(empty, vec![]);
        let variable = arena.value_variable(DeBruijnIndex::from(0));
        let unit = arena.value_type_unit();
        let motive = arena.comp_type_returner(unit);
        let case = arena.computation_data_case(variable, motive, vec![]);
        let lambda = arena.computation_lambda(case);
        let body = arena.value_thunk(lambda);
        let arrow = arena.comp_type_pi(datatype, motive);
        let declared = arena.value_type_thunk(arrow);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        let admitted = environment
            .add_decl(declaration)
            .expect("empty case checks under its impossible argument");
        assert!(environment.audit(admitted).axioms().is_empty());
    }

    #[test]
    fn an_absurd_case_rests_on_apart_endpoints()
    {
        use gandr_kernel_term::Apartness;
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::PresentedRule;
        use gandr_kernel_term::RuleNode;
        let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
        let succ = RuleNode::Constructor(ConstructorTag::from(1_usize));
        // The naturals modulo two: `Succ(Zero)` and `Zero` are normal and
        // differ at their heads, and `Succ(Succ(Zero))` is `Zero`.
        let modulo =
            Presentation::new(vec![PresentedRule::new([succ, succ, x].into(), [x].into())]);
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let naturals = staging
            .data(
                LevelSignature::monomorphic(),
                vec![],
                vec![vec![], vec![own]],
                kind,
            )
            .presented(modulo);
        let nominal = environment
            .add_decl(naturals)
            .expect("the naturals modulo two admit")
            .position();
        for (successors, expected, why) in [
            (1_usize, Ok(()), "`Succ(Zero)` is apart from `Zero`"),
            (
                2,
                Err(KernelError::NotApart(Apartness::Agree)),
                "`Succ(Succ(Zero))` is `Zero`, so the path is reflexivity",
            ),
        ] {
            // `λe. case e {}` at `Path(N, Succ^n(Zero), Zero) → F unit`.
            let mut staging = environment.stage();
            let arena = staging.arena();
            let datatype = arena.value_type_data(nominal, vec![]);
            let zero = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
            let mut left = zero;
            for _ in 0 .. successors {
                left = arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![left]);
            }
            let path = arena.value_type_path(datatype, left, zero);
            let unit = arena.value_type_unit();
            let motive = arena.comp_type_returner(unit);
            let variable = arena.value_variable(DeBruijnIndex::from(0));
            let case = arena.computation_data_case(variable, motive, vec![]);
            let lambda = arena.computation_lambda(case);
            let body = arena.value_thunk(lambda);
            let arrow = arena.comp_type_pi(path, motive);
            let declared = arena.value_type_thunk(arrow);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            assert_eq!(
                environment.add_decl(declaration).map(|_admitted| ()),
                expected,
                "{why}"
            );
        }
    }

    #[test]
    fn record_width_depth_projection_and_absent_fields()
    {
        let mut environment = Environment::new();
        let a = FieldLabel::from(String::from("a"));
        let b = FieldLabel::from(String::from("b"));
        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let narrow = arena.value_type_record(BTreeMap::from([(a.clone(), unit_type)]));
        let wide = arena.value_record(BTreeMap::from([(a.clone(), unit), (b.clone(), unit)]));
        let declared = arena.value_type_record(BTreeMap::from([(a.clone(), narrow)]));
        let body = arena.value_record(BTreeMap::from([(a.clone(), wide), (b.clone(), unit)]));
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        environment
            .add_decl(declaration)
            .expect("width and nested record checking");

        let mut staging = environment.stage();
        let arena = staging.arena();
        let inner_wide = arena.value_type_record(BTreeMap::from([
            (a.clone(), unit_type),
            (b.clone(), unit_type),
        ]));
        let wide_type =
            arena.value_type_record(BTreeMap::from([(a.clone(), inner_wide), (b, unit_type)]));
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returned);
        let function = arena.value_thunk(lambda);
        let result = arena.comp_type_returner(declared);
        let arrow = arena.comp_type_arrow(wide_type, result);
        let function_type = arena.value_type_thunk(arrow);
        let declaration = staging.def(LevelSignature::monomorphic(), function_type, function);
        environment
            .add_decl(declaration)
            .expect("a record variable supports width and depth inclusion");

        let mut staging = environment.stage();
        let arena = staging.arena();
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let bad_inner = arena.value_type_record(BTreeMap::from([(a.clone(), integer)]));
        let bad_result = arena.value_type_record(BTreeMap::from([(a.clone(), bad_inner)]));
        let bad_result = arena.comp_type_returner(bad_result);
        let bad_arrow = arena.comp_type_arrow(wide_type, bad_result);
        let bad_type = arena.value_type_thunk(bad_arrow);
        let declaration = staging.def(LevelSignature::monomorphic(), bad_type, function);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ValueTypeMismatch(_))
        ));

        let mut staging = environment.stage();
        let arena = staging.arena();
        let projection = arena.computation_record_projection(wide, a);
        let result = arena.computation_return(unit);
        let returner = arena.comp_type_returner(unit_type);
        let declared = arena.value_type_thunk(returner);
        let body = arena.value_thunk(projection);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        environment
            .add_decl(declaration)
            .expect("projection synthesizes the selected field type");
        let mut arena = environment.arena().clone();
        let trace = [ConversionDecision::ComparedShared {
            left: ReplayNode::Other,
            right: ReplayNode::Other,
        }];
        assert_eq!(
            replay(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(projection, result),
                EngineClaim::Convertible,
                trace,
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );

        let absent = FieldLabel::from(String::from("absent"));
        let mut staging = environment.stage();
        let arena = staging.arena();
        let projection = arena.computation_record_projection(wide, absent.clone());
        let body = arena.value_thunk(projection);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::AbsentRecordField { label: absent })
        );
    }

    #[test]
    fn native_declarations_and_eliminators_survive_canonical_decode()
    {
        let mut environment = Environment::new();
        let mut declarations = Vec::new();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit_type = arena.value_type_unit();
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let declaration = staging.data(
            LevelSignature::monomorphic(),
            vec![],
            vec![vec![unit_type]],
            universe,
        );
        declarations.push(MarkedDeclaration::new(
            AdmissionMark::Checked,
            declaration.declaration().clone(),
        ));
        let nominal = environment
            .add_decl(declaration)
            .expect("data signature")
            .position();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let datatype = arena.value_type_data(nominal, vec![]);
        let unit = arena.value_unit();
        let constructor = arena.value_constructor(datatype, ConstructorTag::from(0), vec![unit]);
        let motive = arena.comp_type_returner(unit_type);
        let body = arena.computation_return(unit);
        let branch = arena.computation_lambda(body);
        let case = arena.computation_data_case(constructor, motive, vec![branch]);
        let label = FieldLabel::from(String::from("é"));
        let record = arena.value_record(BTreeMap::from([(label.clone(), unit)]));
        let record_type = arena.value_type_record(BTreeMap::from([(label.clone(), unit_type)]));
        let projection = arena.computation_record_projection(record, label);
        let quoted = arena.value_quote(record_type);
        let first = arena.value_thunk(case);
        let second = arena.value_thunk(projection);
        let pair = arena.value_tuple(&[first, second]);
        let body = arena.value_tuple(&[quoted, pair]);
        let thunk_type = arena.value_type_thunk(motive);
        let pair_type = arena.value_type_product(&[thunk_type, thunk_type]);
        let declared = arena.value_type_product(&[universe, pair_type]);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        declarations.push(MarkedDeclaration::new(
            AdmissionMark::Checked,
            declaration.declaration().clone(),
        ));
        environment
            .add_decl(declaration)
            .expect("all native nodes are reachable and typed");
        let bytes = encode(environment.arena(), &declarations);
        let decoded = decode(bytes.as_image()).expect("native canonical reader");
        assert_eq!(encode(decoded.arena(), decoded.declarations()), bytes);
        let DeclarationContent::Data {
            ref parameters,
            ref constructors,
            ref kind,
        } = *(decoded.declarations()[0].declaration().content())
        else {
            panic!("nominal signature was not decoded");
        };
        assert!(parameters.is_empty());
        assert_eq!(constructors.len(), 1);
        assert_eq!(
            decoded.arena().value_type(constructors[0][0]),
            Some(&ValueType::unit())
        );
        assert!(matches!(
            decoded.arena().value_type(*kind),
            Some(ValueType::Universe {
                sort: GroundSort::Value,
                ..
            })
        ));
    }

    /// Each component of a three-component tuple projects at its own type and
    /// replays to the component returned; a component past the last and a
    /// record operand refuse; a projection survives canonical decode.
    #[test]
    fn tuple_projection_reads_each_component()
    {
        /// The tuple `(0, unit, (unit, unit))` and its three components'
        /// classifiers, minted in one staging arena.
        fn fixture(
            arena: &mut gandr_kernel_term::TermArena
        ) -> (ValueId, [(ValueId, ValueTypeId); 3])
        {
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let unit_type = arena.value_type_unit();
            let pair_type = arena.value_type_product(&[unit_type, unit_type]);
            let unit = arena.value_unit();
            let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                gandr_kernel_term::IntegerLiteral::new(
                    gandr_kernel_term::Sign::NonNegative,
                    gandr_kernel_term::Magnitude::zero(),
                ),
            ));
            let pair = arena.value_tuple(&[unit, unit]);
            let tuple = arena.value_tuple(&[zero, unit, pair]);
            (tuple, [
                (zero, integer),
                (unit, unit_type),
                (pair, pair_type),
            ])
        }

        let mut environment = Environment::new();
        let mut declarations = Vec::new();
        for position in 0 .. 3_usize {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let (tuple, components) = fixture(arena);
            let (component, classifier) = components[position];
            let projection = arena.computation_tuple_projection(tuple, Component::from(position));
            let returned = arena.computation_return(component);
            let returner = arena.comp_type_returner(classifier);
            let declared = arena.value_type_thunk(returner);
            let body = arena.value_thunk(projection);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            declarations.push(MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.declaration().clone(),
            ));
            environment
                .add_decl(declaration)
                .expect("a projection synthesizes its component's returner");
            let mut arena = environment.arena().clone();
            assert_eq!(
                replay(
                    &mut arena,
                    &Unfoldings::default(),
                    ReplaySides::Computations(projection, returned),
                    EngineClaim::Convertible,
                    [ConversionDecision::ComparedShared {
                        left: ReplayNode::Other,
                        right: ReplayNode::Other,
                    }],
                    ReplayBudget::default()
                ),
                KernelVerdict::Convertible
            );
        }

        let mut staging = environment.stage();
        let arena = staging.arena();
        let (tuple, [_, (_, unit_type), _]) = fixture(arena);
        let first = arena.computation_tuple_projection(tuple, Component::from(0_usize));
        let returner = arena.comp_type_returner(unit_type);
        let declared = arena.value_type_thunk(returner);
        let body = arena.value_thunk(first);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(
            environment.add_decl(declaration).is_err(),
            "the first component is an integer, not the unit"
        );

        let past = Component::from(3_usize);
        let mut staging = environment.stage();
        let arena = staging.arena();
        let (tuple, [_, (_, unit_type), _]) = fixture(arena);
        let projection = arena.computation_tuple_projection(tuple, past);
        let returner = arena.comp_type_returner(unit_type);
        let declared = arena.value_type_thunk(returner);
        let body = arena.value_thunk(projection);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert_eq!(
            environment.add_decl(declaration),
            Err(KernelError::AbsentTupleComponent { component: past })
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let label = FieldLabel::from(String::from("a"));
        let record = arena.value_record(BTreeMap::from([(label, unit)]));
        let projection = arena.computation_tuple_projection(record, Component::from(0_usize));
        let returner = arena.comp_type_returner(unit_type);
        let declared = arena.value_type_thunk(returner);
        let body = arena.value_thunk(projection);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ValueShapeMismatch { .. })
        ));

        let bytes = encode(environment.arena(), &declarations);
        let decoded = decode(bytes.as_image()).expect("tuple projection canonical reader");
        assert_eq!(encode(decoded.arena(), decoded.declarations()), bytes);
    }

    /// A lazy pairing checks against its lazy product; each projection of the
    /// admitted pairing synthesizes its own side and replays, through the
    /// pairing's unfolding, to that side's returner; a projection of a pairing
    /// replays with no decision; a pairing at a returner, a projection of a
    /// returner and a projection read at the other side's type refuse by name;
    /// the declarations survive canonical decode.
    #[test]
    fn lazy_product_pairs_projects_and_survives_decode()
    {
        /// The pairing `⟨return unit, return 0⟩`, its two components, and the
        /// two sides' returner types, minted in one staging arena.
        fn fixture(
            arena: &mut gandr_kernel_term::TermArena
        ) -> (ComputationId, [(ComputationId, CompTypeId); 2])
        {
            let unit_type = arena.value_type_unit();
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let unit = arena.value_unit();
            let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                gandr_kernel_term::IntegerLiteral::new(
                    gandr_kernel_term::Sign::NonNegative,
                    gandr_kernel_term::Magnitude::zero(),
                ),
            ));
            let left = arena.computation_return(unit);
            let right = arena.computation_return(zero);
            let unit_returner = arena.comp_type_returner(unit_type);
            let integer_returner = arena.comp_type_returner(integer);
            (arena.computation_with(left, right), [
                (left, unit_returner),
                (right, integer_returner),
            ])
        }

        let mut environment = Environment::new();
        let mut declarations = Vec::new();
        let mut staging = environment.stage();
        let arena = staging.arena();
        let (pairing, [(_, left_type), (_, right_type)]) = fixture(arena);
        let lazy = arena.comp_type_with(left_type, right_type);
        let declared = arena.value_type_thunk(lazy);
        let record_body = arena.value_thunk(pairing);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, record_body);
        declarations.push(MarkedDeclaration::new(
            AdmissionMark::Checked,
            declaration.declaration().clone(),
        ));
        let record = environment
            .add_decl(declaration)
            .expect("a pairing checks against its lazy product")
            .position();
        let unfoldings = Unfoldings::new(vec![Unfoldable::Body(record_body)]);

        for side in [Side::Left, Side::Right] {
            let mut staging = environment.stage();
            let arena = staging.arena();
            let (_, components) = fixture(arena);
            let (component, classifier) = match side {
                | Side::Left => components[0],
                | Side::Right => components[1],
            };
            let named = arena.value_constant(record);
            let forced = arena.computation_force(named);
            let projection = arena.computation_project(side, forced);
            let declared = arena.value_type_thunk(classifier);
            let body = arena.value_thunk(projection);
            let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
            declarations.push(MarkedDeclaration::new(
                AdmissionMark::Checked,
                declaration.declaration().clone(),
            ));
            environment
                .add_decl(declaration)
                .expect("a projection synthesizes its side of the lazy product");
            let mut arena = environment.arena().clone();
            let unfold = [
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(record),
                },
                ConversionDecision::ReduceLeft {
                    redex: ReplayNode::Constant(record),
                },
            ];
            assert_eq!(
                replay(
                    &mut arena,
                    &unfoldings,
                    ReplaySides::Computations(projection, component),
                    EngineClaim::Convertible,
                    unfold,
                    ReplayBudget::default()
                ),
                KernelVerdict::Convertible
            );
        }

        let mut staging = environment.stage();
        let arena = staging.arena();
        let (pairing, [(left, left_type), _]) = fixture(arena);
        let reduction = arena.computation_project(Side::Left, pairing);
        let declared = arena.value_type_thunk(left_type);
        let body = arena.value_thunk(reduction);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        declarations.push(MarkedDeclaration::new(
            AdmissionMark::Checked,
            declaration.declaration().clone(),
        ));
        environment
            .add_decl(declaration)
            .expect("a projection of a pairing synthesizes its side");
        let mut arena = environment.arena().clone();
        assert_eq!(
            replay(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(reduction, left),
                EngineClaim::Convertible,
                [],
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let (pairing, [(_, left_type), _]) = fixture(arena);
        let wrong_side = arena.computation_project(Side::Right, pairing);
        let declared = arena.value_type_thunk(left_type);
        let body = arena.value_thunk(wrong_side);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(
            matches!(
                environment.add_decl(declaration),
                Err(KernelError::ComputationTypeMismatch(_))
            ),
            "the right side is an integer returner, not the unit's"
        );

        let mut staging = environment.stage();
        let arena = staging.arena();
        let (_, [(left, left_type), _]) = fixture(arena);
        let not_a_pairing = arena.computation_project(Side::Left, left);
        let declared = arena.value_type_thunk(left_type);
        let body = arena.value_thunk(not_a_pairing);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ComputationShapeMismatch {
                expected: ExpectedComputationShape::With,
                actual,
            }) if actual.head() == CompTypeHead::Returner
        ));

        let mut staging = environment.stage();
        let arena = staging.arena();
        let (pairing, [(_, left_type), _]) = fixture(arena);
        let declared = arena.value_type_thunk(left_type);
        let body = arena.value_thunk(pairing);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        assert!(matches!(
            environment.add_decl(declaration),
            Err(KernelError::ComputationShapeMismatch {
                expected: ExpectedComputationShape::With,
                actual,
            }) if actual.head() == CompTypeHead::Returner
        ));

        let bytes = encode(environment.arena(), &declarations);
        let decoded = decode(bytes.as_image()).expect("lazy product canonical reader");
        assert_eq!(encode(decoded.arena(), decoded.declarations()), bytes);
    }

    /// The one-point sort `S`, at constant 0.
    const SORT: usize = 0;
    /// The words of the loop at `S`'s point, at constant 1.
    const WORDS: usize = 1;
    /// `loop`, the word of the loop's letter, at constant 2.
    const LOOP: usize = 2;

    /// A value a loop witness's case answers or arms with.
    #[derive(Clone, Copy, Debug)]
    enum Built
    {
        /// The point, `Base`.
        Point,
        /// The empty word: reflexivity at the point.
        Empty,
        /// The constant `loop`, whose body is the word of its letter.
        Named,
        /// The word of the loop's inverse letter.
        Inverse,
        /// Reflexivity at the empty word.
        Stays,
    }

    /// `built` in `arena`.
    ///
    /// # Specification
    /// trivial.
    fn build(
        arena: &mut TermArena,
        built: Built,
    ) -> ValueId
    {
        let carrier = arena.value_type_data(ConstantIndex::from(SORT), vec![]);
        let words = arena.value_type_data(ConstantIndex::from(WORDS), vec![]);
        let empty = arena.value_constructor(words, ConstructorTag::from(0_usize), vec![]);
        match built {
            | Built::Point => {
                arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![])
            },
            | Built::Empty => empty,
            | Built::Named => arena.value_constant(ConstantIndex::from(LOOP)),
            | Built::Inverse => {
                arena.value_constructor(words, ConstructorTag::from(2_usize), vec![empty])
            },
            | Built::Stays => arena.value_here(empty),
        }
    }

    /// The one-point sort, the words of one loop at its point, and `loop`, the
    /// word of its one letter at `Path(S, Base, Base)`, admitted in that order.
    ///
    /// # Specification
    /// trivial.
    fn one_loop() -> Environment
    {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let staged = staging.data(LevelSignature::monomorphic(), vec![], vec![vec![]], kind);
        let _sort = environment
            .add_decl(staged)
            .expect("the one-point sort admits");
        let mut staging = environment.stage();
        let arena = staging.arena();
        let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
        let own = arena.value_type_data(ConstantIndex::from(WORDS), vec![]);
        let base =
            || -> Box<[RuleNode]> { [RuleNode::Constructor(ConstructorTag::from(0_usize))].into() };
        let cells = FreeCells::new(ConstantIndex::from(SORT), vec![FreeCell::new(
            base(),
            base(),
        )]);
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                vec![],
                vec![vec![], vec![own], vec![own]],
                kind,
            )
            .presented(Presentation::words(cells));
        let _words = environment
            .add_decl(staged)
            .expect("the loop's words admit");
        let mut staging = environment.stage();
        let arena = staging.arena();
        let point = build(arena, Built::Point);
        let carrier = arena.value_type_data(ConstantIndex::from(SORT), vec![]);
        let path = arena.value_type_path(carrier, point, point);
        let words = arena.value_type_data(ConstantIndex::from(WORDS), vec![]);
        let empty = build(arena, Built::Empty);
        let letter = arena.value_constructor(words, ConstructorTag::from(1_usize), vec![empty]);
        let staged = staging.def(LevelSignature::monomorphic(), path, letter);
        let _loop = environment
            .add_decl(staged)
            .expect("the loop's word checks at its path");
        environment
    }

    /// The family a loop witness's case answers in, read under the case's
    /// one binder `x`.
    #[derive(Clone, Copy, Debug)]
    enum Family
    {
        /// `Path(S, Base, x)`.
        Joined,
        /// `Path(S, x, x)`.
        Looped,
        /// `S`.
        Kept,
        /// `Path(S, ⟨f x⟩, Base)`.
        Collapsed(ConstantIndex),
        /// `Path(S, ⟨f x⟩, x)`.
        Mapped(ConstantIndex),
        /// `Path(S, ⟨f ⟨f x⟩⟩, x)`.
        Twice(ConstantIndex),
    }

    /// `family`'s returner in `arena`.
    ///
    /// # Specification
    /// trivial.
    fn motive(
        arena: &mut TermArena,
        family: Family,
    ) -> CompTypeId
    {
        let carrier = arena.value_type_data(ConstantIndex::from(SORT), vec![]);
        let point = build(arena, Built::Point);
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let call = |arena: &mut TermArena, function: ConstantIndex, argument: ValueId| {
            let function = arena.value_constant(function);
            let forced = arena.computation_force(function);
            let applied = arena.computation_application(forced, argument);
            arena.value_returned(applied)
        };
        let fibre = match family {
            | Family::Joined => arena.value_type_path(carrier, point, x),
            | Family::Looped => arena.value_type_path(carrier, x, x),
            | Family::Kept => carrier,
            | Family::Collapsed(function) => {
                let image = call(arena, function, x);
                arena.value_type_path(carrier, image, point)
            },
            | Family::Mapped(function) => {
                let image = call(arena, function, x);
                arena.value_type_path(carrier, image, x)
            },
            | Family::Twice(function) => {
                let inner = call(arena, function, x);
                let image = call(arena, function, inner);
                arena.value_type_path(carrier, image, x)
            },
        };
        arena.comp_type_returner(fibre)
    }

    /// Stage `thunk (λx. case x { Base ⇒ return answer; loop ⇒ return arm… })`
    /// at `(x : S) → family`, the case's motive and the function's codomain
    /// alike, and admit it at its position.
    ///
    /// # Specification
    /// trivial.
    fn case_over(
        environment: &mut Environment,
        family: Family,
        answer: Built,
        arms: &[Built],
    ) -> Result<ConstantIndex, KernelError>
    {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let carrier = arena.value_type_data(ConstantIndex::from(SORT), vec![]);
        let motive = motive(arena, family);
        let answer = build(arena, answer);
        let mut branches = vec![arena.computation_return(answer)];
        for &arm in arms {
            let arm = build(arena, arm);
            branches.push(arena.computation_return(arm));
        }
        let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(scrutinee, motive, branches);
        let lambda = arena.computation_lambda(case);
        let pi = arena.comp_type_pi(carrier, motive);
        let declared = arena.value_type_thunk(pi);
        let body = arena.value_thunk(lambda);
        let staged = staging.def(LevelSignature::monomorphic(), declared, body);
        environment
            .add_decl(staged)
            .map(gandr_kernel_core::CheckedId::position)
    }

    #[test]
    fn a_case_over_the_circle_owes_its_loop()
    {
        let mut environment = one_loop();
        assert_eq!(
            case_over(&mut environment, Family::Joined, Built::Empty, &[]),
            Err(KernelError::LoopNotRespected(CellIndex::from(0_usize))),
            "the circle is not contractible: carried along the loop, reflexivity at the point \
             is the loop"
        );
        for (family, answer, what) in [
            (
                Family::Looped,
                Built::Empty,
                "reflexivity at every point respects the loop",
            ),
            (
                Family::Looped,
                Built::Named,
                "the loop at every point respects the loop, read as its word",
            ),
            (
                Family::Kept,
                Built::Point,
                "a non-dependent case owes no loop",
            ),
        ] {
            assert!(
                case_over(&mut environment, family, answer, &[]).is_ok(),
                "{what}"
            );
        }
    }

    #[test]
    fn a_loop_arm_checks_at_the_path_over_its_loop()
    {
        let mut environment = one_loop();
        let flip = case_over(&mut environment, Family::Kept, Built::Point, &[
            Built::Inverse,
        ])
        .expect("a non-dependent loop arm chooses the loop's image");
        let collapse = case_over(&mut environment, Family::Kept, Built::Point, &[])
            .expect("a non-dependent case with no loop arm sends the loop to reflexivity");
        assert!(
            case_over(&mut environment, Family::Looped, Built::Empty, &[
                Built::Stays
            ])
            .is_ok(),
            "a dependent loop arm checks at the path over the loop"
        );
        assert!(
            matches!(
                case_over(&mut environment, Family::Joined, Built::Empty, &[
                    Built::Stays
                ]),
                Err(KernelError::Identity(
                    gandr_kernel_core::IdentityError::EndpointsDiffer {
                        side: gandr_kernel_core::EndpointSide::Left,
                        ..
                    }
                ))
            ),
            "a dependent loop arm at the wrong endpoints is refused: the path over the loop \
             starts at the loop, not at reflexivity"
        );
        assert!(
            case_over(&mut environment, Family::Twice(flip), Built::Empty, &[]).is_ok(),
            "the flip twice follows the point round the loop, read through its loop arm"
        );
        assert!(
            case_over(
                &mut environment,
                Family::Collapsed(collapse),
                Built::Empty,
                &[]
            )
            .is_ok(),
            "the collapse's image of the loop is reflexivity"
        );
        assert_eq!(
            case_over(&mut environment, Family::Mapped(flip), Built::Empty, &[]),
            Err(KernelError::LoopNotRespected(CellIndex::from(0_usize))),
            "the flip once is no identity: reflexivity is carried to the loop twice"
        );
    }
}
