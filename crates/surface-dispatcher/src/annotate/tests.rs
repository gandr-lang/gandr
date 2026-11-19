use alloc::vec::Vec;

use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_checker::Typings;
use gandr_core_checker::type_module;
use gandr_core_term::Computation;
use gandr_core_term::Value;
use gandr_kernel_term::FieldPosition;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::typed;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::ModuleSettings;
use crate::compose::Opening;
use crate::compose::adapt;
use crate::compose::checking_context;
use crate::schedule::bound_run;

/// The join reads each cell of `#[1, 2] : List Integer` at its own typing:
/// the head at the element type, and the tail at the cell's list type. The
/// binder of `let m = n + n` holds the result type of its head, the same
/// `Integer` as the list's elements (#8161).
#[test]
fn the_join_reads_each_field_and_binder_at_its_occurrence_8161()
{
    let listed =
        crate::fixture::Listed::hosted(include_str!("tests/fixtures/a-list-and-a-bind-8161.gandr"));
    let grammar = built_in().expect("the built-in grammar");
    let lowering = crate::lower_unit_source(
        &grammar,
        SourceText::from(listed.text.as_str()),
        &listed.unit,
        &mut LoweringCount::default(),
    )
    .expect("the source lowers");
    let Lowered::Module { module, mut arena } = lowering.into_lowered()
    else {
        panic!("the source is a module");
    };
    let declarations = adapt(&module, &arena);
    let mut context =
        checking_context(&mut arena, Opening::UNBOUNDED, &ModuleSettings::of(&module));
    let module_typed = type_module(&mut context, &declarations);
    let declared = context.data_signatures().clone();
    let core = &arena;
    let table = typed(core, &module_typed, declared);
    let mut heads = Vec::new();
    let mut binders = Vec::new();
    for typing in module_typed.typings().values().flat_map(Typings::typings) {
        match (typing.term, typing.ty) {
            (TermNode::Value(cell), TypeNode::Value(list))
                if matches!(core.value(cell), Some(&Value::ListCons(..))) =>
            {
                assert_eq!(
                    Maybe::Present(list),
                    table.field(cell, FieldPosition::from(1_usize)),
                    "a cell's tail holds the cell's own list type"
                );
                let Maybe::Present(head) = table.field(cell, FieldPosition::from(0_usize))
                else {
                    panic!("a cell's head holds a type");
                };
                heads.push(head);
            },
            (TermNode::Computation(bind), _) => {
                let Some(&Computation::Bind(head, _)) = core.computation(bind)
                else {
                    continue;
                };
                let Maybe::Present(binder) = table.binder(bound_run(core, head))
                else {
                    panic!("a bind's binder holds a type");
                };
                binders.push(binder);
            },
            _ => {},
        }
    }
    assert_eq!(2, heads.len(), "the two cells of the list");
    assert!(!binders.is_empty(), "the bind of `m`");
    let element = core.value_type(heads[0]);
    assert!(element.is_some(), "the element type resolves");
    for &held in heads.iter().chain(binders.iter()) {
        assert_eq!(
            element,
            core.value_type(held),
            "each head and each binder hold the integer type"
        );
    }
}
