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
            DataSignature::new(vec![], vec![], bad_kind),
            OriginToken::from(0_usize),
        );
        let first = ConstantIndex::from(1_usize);
        let second = ConstantIndex::from(2_usize);
        let one = Declaration::data(
            first,
            DataSignature::new(vec![], vec![vec![unit_type]], kind),
            OriginToken::from(1_usize),
        );
        let two = Declaration::data(
            second,
            DataSignature::new(vec![], vec![vec![unit_type]], kind),
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
        let artifact =
            gandr_kernel_term::decode(crossed.export(BTreeMap::new()).as_image()).unwrap();
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
            DataSignature::new(vec![kind], vec![vec![element]], kind),
            OriginToken::from(0_usize),
        );
        let unit_type = arena.value_type_unit();
        let unit_code = arena.value_quote(unit_type);
        let unit = arena.value_unit();
        let datatype = arena.value_type_data(family, vec![unit_code]);
        let index_declaration = Declaration::data(
            indexed,
            DataSignature::new(vec![datatype], vec![vec![]], kind),
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
                assert!(matches!(arena.value_type(field), Some(ValueType::Unit)));
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
                assert!(
                    inner
                        .values()
                        .all(|&ty| matches!(arena.value_type(ty), Some(ValueType::Unit)))
                );
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
            DataSignature::new(vec![function], vec![vec![]], kind),
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
            DataSignature::new(vec![], vec![], kind),
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
            DataSignature::new(vec![], vec![vec![unit_type]], kind),
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
            DataSignature::new(vec![], vec![vec![]], kind),
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
}
