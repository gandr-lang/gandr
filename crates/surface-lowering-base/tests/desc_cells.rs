//! The cell gate, run by the production lowering route of
//! `gandr-surface-lowering`: a refusal of the gate reaches the lowered module,
//! and the declarations after it lower.

use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering_base::desc_cells::CellFault;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_theory_cell_complexes::CellCount;
use gandr_theory_cell_complexes::ContinuationCount;
use gandr_theory_computads::ElaborateError;

#[test]
fn ordinary_lowering_executes_the_cell_gate_and_preserves_later_values()
{
    let source = "data Flag : Type where { | Off : Flag | On : Flag oper split : (x : Flag) --> (a : Flag, b : Flag); rule : split Off ==> On; } def later = 7;";
    let grammar = grammar();
    let tree = parse(&grammar, source.into()).unwrap().into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let [ref rule] = *module.cells().diagnostics.as_slice()
    else {
        panic!("the cell refusal reached ordinary lowering")
    };
    assert_eq!(
        rule.fault,
        CellFault::Rule(ElaborateError::ResultArity {
            outputs: ContinuationCount::from(2_usize),
            results: ContinuationCount::ONE,
        })
    );
    assert_eq!(
        module.cells().declarations[0].store.len(),
        CellCount::from(2_usize)
    );
    let declarations: Vec<_> = module.declarations().iter().collect();
    assert_eq!(declarations.len(), 3);
    for (declaration, expected) in declarations.iter().zip(["Flag", "Flag", "later"]) {
        assert_eq!(declaration.name().as_ref(), expected);
    }
    assert!(matches!(
        declarations[0].outcome(),
        DeclarationOutcome::Data(_)
    ));
    assert_eq!(declarations[1].span(), rule.span);
    assert!(matches!(
        declarations[1].outcome(),
        DeclarationOutcome::Refused(_)
    ));
}
