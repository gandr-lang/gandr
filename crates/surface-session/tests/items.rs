//! The item source: a lowered revision offered as the incremental checker's
//! items.

use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemSource as _;
use gandr_core_term::FailureClass;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::adapt;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_session::Revision;
use gandr_surface_session::RevisionFault;
use gandr_surface_session::SurfaceItems;
use gandr_surface_session::program;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::grammar;

#[test]
fn each_unrefused_declaration_is_one_item_keyed_by_its_name()
{
    let grammar = &*crate::common::GRAMMAR;
    let mut lowerings = LoweringCount::default();
    let lowering = lower_source(
        grammar,
        SourceText::from(
            "def first : Integer ; def first = 1 ; def broken = missing ; def owed : String ; def last = first ;",
        ),
        &mut lowerings,
    )
    .expect("lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the module is read");
    };
    let program = program(&module, arena).expect("positions ascend");
    let keys: Vec<&ItemKey> = program
        .items()
        .iter()
        .map(gandr_core_incremental::Item::key)
        .collect();
    assert_eq!(
        keys,
        vec![
            &ItemKey::from("first"),
            &ItemKey::from("owed"),
            &ItemKey::from("last")
        ],
        "one item per unrefused declaration, keyed by its name, in admission order"
    );
    let declarations: Vec<_> = program
        .items()
        .iter()
        .map(|item| *item.declaration())
        .collect();
    assert_eq!(
        declarations,
        adapt(&module),
        "each item carries exactly the declaration the checker is given"
    );
}

#[test]
fn the_item_source_offers_a_revision_or_names_its_fault()
{
    let items = SurfaceItems::new(grammar());
    let program = items
        .items(&Revision::from("def a = 1 ; def b = a ;"))
        .expect("a module the lowering reads is offered");
    assert_eq!(
        program.items().len(),
        2_usize,
        "both declarations are items"
    );
    let refused = items.items(&Revision::from(String::from("def a = 1 ;\nret a")));
    let Err(RevisionFault::Refused { class, span }) = refused
    else {
        panic!("a root that is no list of declarations is refused whole: {refused:?}");
    };
    assert_eq!(
        class,
        FailureClass::Unrepresentable,
        "the fragment cannot represent a top-level expression"
    );
    assert!(
        matches!(span, Maybe::Present(_)),
        "the refusal names the bytes it covers"
    );
}
