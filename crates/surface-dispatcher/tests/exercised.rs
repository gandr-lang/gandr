//! The rows a composition's settled declarations carry: each composition
//! names the run stage's engine, so these tests stand in the `tests` target
//! (#7048).

use anodized::spec;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Exercised;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Row;
use gandr_surface_dispatcher::compose;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;

/// The rows `source`'s settled declarations carry under the fixture root.
///
/// # Specification
/// - requires: the built-in grammar builds and `source` composes without an
///   engine fault or whole-module refusal under the fixture root.
/// - ensures: the returned rows belong to the composed source; an empty source
///   contributes zero to every row.
/// - panics: if the fixture violates the composition premise.
///
/// # Adequacy
/// - hypothesis: L3 — real empty, accepted and refused source declarations have
///   independent exact row expectations, not a second composition.
/// - witness: `tests::exercised::a_module_carries_exactly_its_rows`
#[spec(ensures: |ref ret| !source.as_ref().is_empty()
        || Row::ALL.into_iter().all(|row| usize::from(ret.count(row)) == 0_usize))]
fn rows_of(source: SourceText<'_>) -> Exercised
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    match compose::<Evaluator>(&grammar, CorpusRoot::Fixture, source, &mut lowerings) {
        Ok(Composed::Settled { exercised, .. }) => exercised,
        Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
        Err(fault) => panic!("faulted: {fault}"),
    }
}

#[test]
fn a_module_carries_exactly_its_rows()
{
    let table: &[(&str, &[(Row, usize)])] = &[
        (
            include_str!("exercised/fixtures/a-module-carries-exactly-its-rows-table.gandr"),
            &[
                (Row::LambdaChecks, 2_usize),
                (Row::ReturnChecks, 2_usize),
                (Row::ForceSynthesises, 1_usize),
                (Row::ApplicationSynthesises, 1_usize),
                (Row::SubsumptionBridge, 4_usize),
            ],
        ),
        // A synthesised literal converts nothing, so crosses no bridge.
        ("def answer = 42 ;", &[]),
        (r#"@[ refuses("UnresolvedName") ] def a = missing ;"#, &[(
            Row::UndefinedTermName,
            1_usize,
        )]),
        (
            r#"@[ refuses("UnresolvedTypeHead") ] def a : Natural ;"#,
            &[(Row::UndefinedTypeHead, 1_usize)],
        ),
        (
            r#"@[ refuses("ShapeMismatch") ] def a : +U (Integer -> -F Integer) ; def a = thunk { return 3 } ;"#,
            &[(Row::ShapeRefusal, 1_usize)],
        ),
        (
            r#"@[ refuses("NotSynthesisable") ] def a : +U (-F Integer) ; def a = thunk { become (fun (x) { return x }) 3 } ;"#,
            &[(Row::NonSynthesisableHead, 1_usize)],
        ),
        (
            r#"@[ refuses("NotSynthesisable") ] def a = thunk { return 3 } ;"#,
            &[(Row::NonSynthesisableDefinition, 1_usize)],
        ),
        (
            include_str!("exercised/fixtures/a-module-carries-exactly-its-rows.gandr"),
            &[(Row::ReservedForm, 1_usize)],
        ),
        (r#"@[ owes(1) ] def a : Integer ;"#, &[(
            Row::AddressableObligation,
            1_usize,
        )]),
    ];
    for &(source, rows) in table {
        let carried = rows_of(SourceText::from(source));
        for row in Row::ALL {
            let expected = rows
                .iter()
                .find(|&&(candidate, _)| candidate == row)
                .map_or(0_usize, |&(_, count)| count);
            assert_eq!(usize::from(carried.count(row)), expected, "{source}: {row}");
        }
        assert!(
            carried.missing().into_iter().eq(Row::ALL
                .into_iter()
                .filter(|row| !rows.iter().any(|&(carried, _)| carried == *row))),
            "{source} misses every other row"
        );
    }
    assert_eq!(
        rows_of(SourceText::from("")).missing().as_slice(),
        &Row::ALL,
        "an empty source misses every row"
    );
}

#[test]
fn an_unsettled_declaration_carries_no_row()
{
    let rows = rows_of(SourceText::from(include_str!(
        "exercised/fixtures/an-unsettled-declaration-carries-no-row-rows.gandr"
    )));
    assert_eq!(
        rows,
        Exercised::default(),
        "no unsettled declaration counts"
    );
}

#[test]
fn a_near_miss_carries_no_refusal_row()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let source = SourceText::from(include_str!(
        "exercised/fixtures/a-near-miss-carries-no-refusal-row.gandr"
    ));
    let mut lowerings = LoweringCount::default();
    let Composed::Settled {
        report, exercised, ..
    } = compose::<Evaluator>(&grammar, CorpusRoot::Fixture, source, &mut lowerings)
        .expect("the near misses compose")
    else {
        panic!("the near misses lower")
    };
    assert_eq!(report.declarations().len(), 3_usize);
    assert!(
        report.declarations().iter().all(
            |declaration| declaration.settlement() == gandr_surface_corpus::Settlement::Settled
        )
    );
    assert_eq!(
        exercised,
        Exercised::default(),
        "settled near misses carry no refusal row"
    );
}
