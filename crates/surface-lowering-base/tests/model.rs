//! The theory handle a lowered module hands back, read through the
//! production lowering route of `gandr-surface-lowering`.

use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering_base::fixture::grammar;
use gandr_surface_lowering_base::fixture::parsed;
use gandr_surface_lowering_base::namespace::Recognition;
use gandr_surface_syntax::SourceText;

/// A module declaring `CatShape` beside a data family hands back one theory:
/// its name, its two sorts and two operations, and the model its instances
/// check against.
#[test]
fn a_lowered_theory_reads_its_description_and_its_model()
{
    let text = alloc::format!(
        "{}\ndata Flag : Type where {{ | On : Flag | Off : Flag }}\n",
        include_str!("../src/model/tests/unformatted/cat-shape.gandr")
    );
    let grammar = grammar();
    let tree = parsed(&grammar, SourceText::from(text.as_str()));
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let theories: Vec<_> = module.theories().collect();
    let [ref theory] = *theories.as_slice()
    else {
        panic!("the theory alone presents a model signature: {theories:?}")
    };
    assert_eq!(
        text.get(usize::from(theory.named.span.start()) .. usize::from(theory.named.span.end())),
        Some("CatShape")
    );
    let sorts: Vec<&str> = theory
        .description
        .sorts
        .iter()
        .map(|sort| sort.name.as_ref())
        .collect();
    let operations: Vec<&str> = theory
        .description
        .opers
        .iter()
        .map(|operation| operation.name.as_ref())
        .collect();
    assert_eq!((sorts, operations), (vec!["Ob", "Hom"], vec!["id", "comp"]));
    let model = theory.model().unwrap();
    let components: Vec<&str> = model
        .components
        .iter()
        .map(|component| component.name.as_ref())
        .collect();
    assert_eq!(components, [
        "Ob", "Hom", "id", "comp", "unitL", "unitR", "assoc"
    ]);
}
