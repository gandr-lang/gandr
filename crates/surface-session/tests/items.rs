//! The item source: a lowered revision offered as the incremental checker's
//! items.

use core::fmt;
use core::fmt::Write as _;

use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::ItemSource as _;
use gandr_core_incremental::ProgramError;
use gandr_core_term::FailureClass;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_session::Revision;
use gandr_surface_session::RevisionFault;
use gandr_surface_session::SurfaceItems;
use gandr_surface_session::fault_span;
use gandr_surface_session::program;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::RefusingWriter;
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
    let Maybe::Present(span) = span
    else {
        panic!("the refusal names its source extent")
    };
    assert_eq!(usize::from(span.start()), "def a = 1 ;\n".len());
    assert_eq!(usize::from(span.end()), "def a = 1 ;\nret a".len());
    assert_eq!(program.items()[0].key().as_ref(), b"a");
    assert_eq!(program.items()[1].key().as_ref(), b"b");
    let next = items
        .items(&Revision::from("def fresh = 9 ;"))
        .expect("the next revision lowers");
    assert_eq!(next.items()[0].key().as_ref(), b"fresh");
}
#[test]
fn revision_faults_retain_fields_and_sink_refusals()
{
    let span = ByteSpan::new(ByteOffset::from(17_usize), ByteOffset::from(31_usize))
        .expect("ordered span");
    let spanned = RevisionFault::Refused {
        class: FailureClass::Unrepresentable,
        span: Maybe::Present(span),
    };
    let unspanned = RevisionFault::Refused {
        class: FailureClass::EngineFault,
        span: Maybe::Absent(fault_span::Absent::Run),
    };
    let unordered = RevisionFault::Unordered(ProgramError::PositionOrder {
        ordinal: ItemOrdinal::from(113_usize),
        position: ConstantIndex::from(257_usize),
        previous: ConstantIndex::from(509_usize),
    });
    let rendered = spanned.to_string();
    assert!(rendered.contains(&FailureClass::Unrepresentable.to_string()));
    assert!(rendered.contains("17"));
    assert!(rendered.contains("31"));
    assert!(
        unspanned
            .to_string()
            .contains(&FailureClass::EngineFault.to_string())
    );
    let positions = unordered.to_string();
    for field in ["113", "257", "509"] {
        assert!(positions.contains(field));
    }
    for fault in [spanned, unspanned, unordered] {
        assert_eq!(write!(&mut RefusingWriter, "{fault}"), Err(fmt::Error));
    }
}
