use alloc::collections::BTreeSet;

use gandr_core_checker::Site;
use gandr_core_checker::Verdict;
use gandr_core_checker::check_module;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::Value;
use gandr_core_term::ValueTypeId;
use gandr_core_term::equal_type_syntax;
use gandr_kernel_term::BaseType;
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

/// The join reads each cell of `#[1, 2] : List Integer` at its own check: the
/// head at the element type, and the tail at the list type. The binder of
/// `let m = n + n` holds `Integer`. So does the binder of `let k = same n`:
/// the judgement gives its type with the omitted implicit of `same`, and the
/// run reads that type with the implicit's solution (#8161).
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
    let report = check_module(&mut context, &declarations);
    let declared = context.data_signatures().clone();
    let integer = context.arena_mut().value_type_base(BaseType::Integer);
    let core = &arena;
    let Some(Verdict::Checked { declared: list, .. }) = report
        .judged()
        .first()
        .map(gandr_core_checker::Judged::verdict)
    else {
        panic!("`xs` checks at its ascribed list type");
    };
    let list = list.id();
    let table = typed(core, report.annotations(), declared);
    let equal = |left: ValueTypeId, right: ValueTypeId| {
        equal_type_syntax(core, left, right) == CertificateEquality::Equal
    };
    let cells: BTreeSet<_> = report
        .annotations()
        .iter()
        .filter_map(|annotation| match annotation.site {
            Site::Field(cell, _) if matches!(core.value(cell), Some(&Value::ListCons(..))) => {
                Some(cell)
            },
            Site::Field(..) | Site::Binder(_) => None,
        })
        .collect();
    assert_eq!(2, cells.len(), "the two cells of the list");
    for &cell in &cells {
        let (Maybe::Present(head), Maybe::Present(tail)) = (
            table.field(cell, FieldPosition::from(0_usize)),
            table.field(cell, FieldPosition::from(1_usize)),
        )
        else {
            panic!("a cell's head and tail hold a type");
        };
        assert!(equal(head, integer), "a cell's head holds the element type");
        assert!(equal(tail, list), "a cell's tail holds the list type");
    }
    // Each run of a body gives the binder at the head of its own bind: the
    // bind as written, and the bind that the elaboration rebuilds over the
    // call.
    let binders: BTreeSet<_> = report
        .annotations()
        .iter()
        .filter_map(|annotation| match annotation.site {
            Site::Binder(head) => Some(head),
            Site::Field(..) => None,
        })
        .collect();
    assert!(
        binders
            .iter()
            .any(|&head| matches!(core.computation(head), Some(&Computation::Primitive { .. }))),
        "the rebuilt bind of `m` runs `n + n`"
    );
    assert!(
        binders
            .iter()
            .any(|&head| matches!(core.computation(head), Some(&Computation::Application(..)))),
        "the rebuilt bind of `k` runs `same n`"
    );
    for &head in &binders {
        let Maybe::Present(binder) = table.binder(head)
        else {
            panic!("each binder holds a type");
        };
        assert!(equal(binder, integer), "each binder holds the integer type");
    }
}
