//! Schema maps and the pull-back of a store along one.

use gandr_storage_schema::ElementKind;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::MapError;
use gandr_storage_schema::Ordinal;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Presentation;
use gandr_storage_schema::Schema;
use gandr_storage_schema::SchemaError;
use gandr_storage_schema::SchemaMap;
use gandr_storage_schema::StoreError;
use gandr_storage_schema::keyed;

use crate::common::Keyed;
use crate::common::Name;
use crate::common::ThreePath;
use crate::common::arrow;
use crate::common::attribute;
use crate::common::graph;
use crate::common::object;

/// A view of the keyed schema: moves under their tasks, and namings that
/// agree with them.
///
/// # Specification
/// trivial.
fn view() -> Schema
{
    let presentation = Presentation::new()
        .object("Made")
        .object("Work")
        .object("Named")
        .attribute_type("Bytes")
        .attribute_type("Text")
        .arrow("made_work", "Made", "Work", Indexing::Indexed)
        .arrow("named_made", "Named", "Made", Indexing::Indexed)
        .arrow("named_work", "Named", "Work", Indexing::Indexed)
        .attribute("made_receipt", "Made", "Bytes", Indexing::Unindexed)
        .attribute("work_name", "Work", "Text", Indexing::Indexed)
        .equation("named_agrees", "Named", ["named_work"], [
            "named_made",
            "made_work",
        ]);
    Schema::present(&presentation).expect("the view presents")
}

/// The view's map into the keyed schema, before it is checked.
///
/// # Specification
/// trivial.
fn view_map() -> gandr_storage_schema::MapBuilder
{
    let identity: [&str; 0] = [];
    SchemaMap::builder(view(), keyed::schema().expect("the keyed schema presents"))
        .object("Made", "Move")
        .object("Work", "Task")
        .object("Named", "Naming")
        .arrow("made_work", ["move_attempt", "attempt_task"])
        .arrow("named_made", ["naming_move"])
        .arrow("named_work", ["naming_task"])
        .attribute("made_receipt", identity, "move_receipt")
        .attribute("work_name", identity, "task_name")
}

#[test]
fn a_pulled_back_store_satisfies_its_equations_by_construction()
{
    let Keyed {
        store,
        tasks: [alpha, beta],
        moves,
        namings,
        ..
    } = Keyed::new();
    let map = view_map()
        .build()
        .expect("the view's equation holds by the keyed equation");
    let pulled = store.pull_back(&map).expect("a keyed store pulls back");

    let made = object(&pulled, &Name("Made"));
    let named = object(&pulled, &Name("Named"));
    let made_work = arrow(&pulled, &Name("made_work"));
    let named_work = arrow(&pulled, &Name("named_work"));
    let made_receipt = attribute(&pulled, &Name("made_receipt"));
    let move_attempt = arrow(&store, &Name("move_attempt"));
    let attempt_task = arrow(&store, &Name("attempt_task"));
    let move_receipt = attribute(&store, &Name("move_receipt"));

    let keys: Vec<PartKey> = pulled.parts(made).expect("a table").collect();
    assert_eq!(keys, moves, "the moves under their own keys");
    for part in moves {
        let attempt = store.target(move_attempt, part).expect("an attempt");
        assert_eq!(
            pulled.target(made_work, part),
            store.target(attempt_task, attempt),
            "the followed path"
        );
        assert_eq!(
            pulled.value(made_receipt, part),
            store.value(move_receipt, part),
            "the receipt"
        );
    }
    let keys: Vec<PartKey> = pulled.parts(named).expect("a table").collect();
    assert_eq!(keys, namings, "the namings under their own keys");
    assert_eq!(
        pulled.preimage(made_work, alpha).map(<[PartKey]>::len),
        Ok(3),
        "alpha's moves"
    );
    assert_eq!(
        pulled.preimage(named_work, beta).map(<[PartKey]>::len),
        Ok(1),
        "beta's naming"
    );
    assert_eq!(
        pulled.audit(),
        Ok(()),
        "no check ran, and every equation holds"
    );

    let mut pulled = pulled;
    let mut edit = pulled.edit();
    let next = edit.add_part(made).expect("a key is minted");
    edit.abandon();
    assert_eq!(
        next,
        PartKey::from(4_u64),
        "the counter came with the table"
    );

    let ThreePath { store: other, .. } = ThreePath::new();
    assert_eq!(
        other.pull_back(&map).err(),
        Some(StoreError::SchemaMismatch {
            expected: map.target().identity(),
            found: other.schema().identity(),
        }),
        "a store of another schema"
    );
}

#[test]
fn a_map_that_breaks_an_equation_is_refused()
{
    let presentation = Presentation::new()
        .object("Node")
        .object("Link")
        .arrow("from", "Link", "Node", Indexing::Unindexed)
        .arrow("to", "Link", "Node", Indexing::Unindexed)
        .equation("loops", "Link", ["from"], ["to"]);
    let loops = Schema::present(&presentation).expect("the loops schema presents");
    let refusal = SchemaMap::builder(loops, graph())
        .object("Node", "V")
        .object("Link", "E")
        .arrow("from", ["src"])
        .arrow("to", ["tgt"])
        .build()
        .expect_err("not every graph edge is a loop");
    assert_eq!(refusal, MapError::EquationNotPreserved {
        equation: "loops".into()
    });
}

#[test]
fn a_map_that_does_not_compose_is_refused_by_name()
{
    let refusal = view_map()
        .arrow("made_work", ["attempt_task"])
        .build()
        .expect_err("`attempt_task` does not leave `Move`");
    assert_eq!(refusal, MapError::NotComposable {
        element: "made_work".into(),
        arrow: "attempt_task".into(),
        at: "Move".into(),
    });

    let refusal = view_map()
        .arrow("made_work", ["move_attempt"])
        .build()
        .expect_err("a move's attempt is not a task");
    assert_eq!(refusal, MapError::WrongEnd {
        element: "made_work".into(),
        expected: "Task".into(),
        found: "Attempt".into(),
    });

    let presentation = Presentation::new().object("Lone");
    let lone = Schema::present(&presentation).expect("one object presents");
    let refusal = SchemaMap::builder(lone, graph())
        .build()
        .expect_err("`Lone` has no image");
    assert_eq!(refusal, MapError::Unmapped {
        kind: ElementKind::Object,
        name: "Lone".into(),
    });
}

#[test]
fn a_map_onto_another_attribute_type_is_refused()
{
    let identity: [&str; 0] = [];
    let refusal = view_map()
        .attribute("made_receipt", identity, "move_seq")
        .build()
        .expect_err("a receipt is bytes, a sequence number a number");
    assert_eq!(refusal, MapError::AttributeType {
        attribute: "made_receipt".into(),
        expected: "Bytes".into(),
        found: "Number".into(),
    });
    assert_eq!(
        refusal.to_string(),
        "schema map: `made_receipt` has type `Bytes` but its image has type `Number`"
    );
}

#[test]
fn a_map_names_what_it_leaves_unmapped_and_refuses_a_foreign_ordinal()
{
    let identity: [&str; 0] = [];
    let objects = || {
        SchemaMap::builder(view(), keyed::schema().expect("the keyed schema presents"))
            .object("Made", "Move")
            .object("Work", "Task")
            .object("Named", "Naming")
    };
    let refusal = objects()
        .arrow("made_work", ["move_attempt", "attempt_task"])
        .arrow("named_made", ["naming_move"])
        .build()
        .expect_err("`named_work` has no image");
    assert_eq!(refusal, MapError::Unmapped {
        kind: ElementKind::Arrow,
        name: "named_work".into(),
    });
    let refusal = objects()
        .arrow("made_work", ["move_attempt", "attempt_task"])
        .arrow("named_made", ["naming_move"])
        .arrow("named_work", ["naming_task"])
        .attribute("made_receipt", identity, "move_receipt")
        .build()
        .expect_err("`work_name` has no image");
    assert_eq!(refusal, MapError::Unmapped {
        kind: ElementKind::Attribute,
        name: "work_name".into(),
    });

    let source = view();
    let target = keyed::schema().expect("the keyed schema presents");
    let map = view_map().build().expect("the view maps");
    assert_eq!(
        map.arrow(source.arrow("named_made").expect("a view arrow"))
            .map(|path| path.arrows().to_vec()),
        Ok(vec![target.arrow("naming_move").expect("a keyed arrow")])
    );
    let foreign_arrow = target
        .arrows()
        .find(|&arrow| usize::from(arrow) >= source.arrows().len())
        .expect("the keyed schema has more arrows than the view");
    assert_eq!(
        map.arrow(foreign_arrow),
        Err(SchemaError::UnknownOrdinal {
            kind: ElementKind::Arrow,
            ordinal: Ordinal(usize::from(foreign_arrow)),
        })
    );
    let foreign_attribute = target
        .attributes()
        .find(|&attribute| usize::from(attribute) >= source.attributes().len())
        .expect("the keyed schema has more attributes than the view");
    assert_eq!(
        map.attribute(foreign_attribute),
        Err(SchemaError::UnknownOrdinal {
            kind: ElementKind::Attribute,
            ordinal: Ordinal(usize::from(foreign_attribute)),
        })
    );
}

/// A target where `f = g` holds at `X`, reached from `W` through `p`, beside
/// an arrow `k` the equation says nothing of.
///
/// # Specification
/// trivial.
fn parallel() -> Schema
{
    let presentation = Presentation::new()
        .object("W")
        .object("X")
        .object("Y")
        .arrow("p", "W", "X", Indexing::Unindexed)
        .arrow("f", "X", "Y", Indexing::Unindexed)
        .arrow("g", "X", "Y", Indexing::Unindexed)
        .arrow("k", "X", "Y", Indexing::Unindexed)
        .equation("fg", "X", ["f"], ["g"]);
    Schema::present(&presentation).expect("the parallel schema presents")
}

#[test]
fn an_equation_holds_of_images_one_step_apart_in_context()
{
    let presentation = Presentation::new()
        .object("A")
        .object("B")
        .arrow("a1", "A", "B", Indexing::Unindexed)
        .arrow("a2", "A", "B", Indexing::Unindexed)
        .equation("same", "A", ["a1"], ["a2"]);
    let pair = || Schema::present(&presentation).expect("the pair schema presents");
    let map = |first: [&str; 2], second: [&str; 2]| {
        SchemaMap::builder(pair(), parallel())
            .object("A", "W")
            .object("B", "Y")
            .arrow("a1", first)
            .arrow("a2", second)
            .build()
    };

    assert!(map(["p", "f"], ["p", "f"]).is_ok(), "equal images");
    assert!(
        map(["p", "g"], ["p", "f"]).is_ok(),
        "one step after `p`, by the equation read right to left"
    );
    assert!(
        map(["p", "f"], ["p", "g"]).is_ok(),
        "one step after `p`, by the equation read left to right"
    );
    assert_eq!(
        map(["p", "f"], ["p", "k"]),
        Err(MapError::EquationNotPreserved {
            equation: "same".into(),
        }),
        "`f` rewrites to `g`, never to `k`"
    );
}
