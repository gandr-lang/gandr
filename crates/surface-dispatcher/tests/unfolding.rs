//! The unfolding probe over a composition and a walk, each run by the run
//! stage's engine, so the area stands in the `tests` target (#7048).

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::PathBuf;

use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::observe_unfoldings;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;

#[test]
fn a_type_alias_is_not_a_global_body_read()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let observed = observe_unfoldings(|| {
        let mut lowerings = LoweringCount::default();
        compose::<Evaluator>(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"def A : Type ;
def A = Integer ;
def b : A ;
def b = 1 ;"#,
            ),
            &mut lowerings,
        )
    });
    assert!(
        matches!(observed.output(), Ok(Composed::Settled { .. })),
        "the type alias source settles"
    );
    assert_eq!(
        observed.reports(),
        &[],
        "the alias is a type value, not a global body read"
    );
}

#[test]
fn a_flow_body_read_is_reported()
{
    let paths = vec![
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/identity/flow-list-each.gandr"),
    ];
    let observed = observe_unfoldings(|| {
        Walk::new(paths).visit::<Evaluator, _, _>(&Pool::new(Width::SERIAL), |_| {
            ControlFlow::<Infallible>::Continue(())
        })
    });
    assert!(
        matches!(observed.output(), ControlFlow::Continue(_)),
        "the flow source is walked"
    );
    let rows: Vec<(&str, usize, usize)> = observed
        .reports()
        .iter()
        .map(|report| {
            (
                report.subject(),
                usize::from(report.pairs()),
                usize::from(report.events()),
            )
        })
        .collect();
    assert_eq!(
        rows,
        vec![
            ("Cells.everyone", 3_usize, 17_usize),
            ("Cells.renamed", 1_usize, 3_usize),
            ("EqInteger.refl", 1_usize, 1_usize),
            ("EqInteger.sym", 1_usize, 2_usize),
            ("EqString.refl", 1_usize, 1_usize),
            ("EqString.sym", 1_usize, 2_usize),
            ("PartialEqFloat.sym", 1_usize, 2_usize),
        ],
        "the flow source keeps each subject's pairs and events"
    );
}
