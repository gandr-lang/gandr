//! The dangling reference: a delete that would leave a live part referring to
//! a dead one is refused by name, and so is every edit that would make one.

use gandr_storage_schema::AttributeValue;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::Liveness;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Presentation;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::Row;
use gandr_storage_schema::Schema;
use gandr_storage_schema::Store;

use crate::common::Name;
use crate::common::ThreePath;
use crate::common::arrow;
use crate::common::attribute;
use crate::common::object;
use crate::common::params;

#[test]
fn deleting_the_middle_vertex_refuses_by_name()
{
    let ThreePath {
        mut store,
        vertices: [one, two, three],
        edges: [first, second],
    } = ThreePath::new();
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));

    let refusal = store
        .delete_part(vertex, one)
        .expect_err("vertex 1 is the source of 1 → 2");
    assert_eq!(refusal, Refusal::Referenced {
        object: "V".into(),
        part: one,
        arrow: "src".into(),
        by: first,
    });
    assert_eq!(
        refusal.to_string(),
        "`V` part 0 is referred to by `src` of part 0, so it is not deleted"
    );

    let refusal = store
        .delete_part(vertex, two)
        .expect_err("vertex 2 is the source of 2 → 3");
    assert_eq!(refusal, Refusal::Referenced {
        object: "V".into(),
        part: two,
        arrow: "src".into(),
        by: second,
    });
    assert_eq!(
        store.liveness(vertex, two),
        Ok(Liveness::Live),
        "the refused delete left vertex 2"
    );
    assert_eq!(
        u64::from(store.live_count(vertex).expect("V is a table")),
        3,
        "three vertices"
    );

    store
        .delete_part(edge, first)
        .expect("an edge nothing refers to is deleted");
    assert_eq!(
        store.liveness(edge, first),
        Ok(Liveness::Dead),
        "the edge is dead"
    );
    assert_eq!(
        store.liveness(edge, second),
        Ok(Liveness::Live),
        "its neighbour is not"
    );
    let src = arrow(&store, &Name("src"));
    assert_eq!(
        store.target(src, first),
        Err(Refusal::NotLive {
            object: "E".into(),
            part: first,
        }),
        "a dead edge has no source to read"
    );

    store
        .delete_part(vertex, one)
        .expect("vertex 1 is no longer referred to");
    assert_eq!(
        u64::from(store.live_count(vertex).expect("V is a table")),
        2,
        "two vertices"
    );
    assert_eq!(
        store.liveness(vertex, three),
        Ok(Liveness::Live),
        "vertex 3 stands"
    );
}

#[test]
fn an_unindexed_arrow_still_refuses_the_delete()
{
    let ThreePath {
        mut store,
        vertices: [_, _, three],
        edges: [_, second],
    } = ThreePath::new();
    let vertex = object(&store, &Name("V"));
    let tgt = arrow(&store, &Name("tgt"));

    assert_eq!(
        store.preimage(tgt, three),
        Err(Refusal::NotIndexed {
            field: "tgt".into()
        }),
        "`tgt` keeps no inverse"
    );
    assert_eq!(
        store.delete_part(vertex, three),
        Err(Refusal::Referenced {
            object: "V".into(),
            part: three,
            arrow: "tgt".into(),
            by: second,
        }),
        "the scan finds the edge 2 → 3"
    );
    assert_eq!(store.liveness(vertex, three), Ok(Liveness::Live));
}

#[test]
fn a_row_must_be_complete_and_its_own()
{
    let ThreePath {
        mut store,
        vertices: [one, two, _],
        ..
    } = ThreePath::new();
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let label = attribute(&store, &Name("label"));

    let refusal = store
        .add_part(edge, &Row::new().arrow(src, one))
        .expect_err("an edge without a target is incomplete");
    assert_eq!(refusal, Refusal::Unset {
        field: "tgt".into(),
        object: "E".into(),
        part: PartKey::from(2_u64),
    });

    let refusal = store
        .add_part(
            edge,
            &Row::new()
                .arrow(src, one)
                .arrow(tgt, two)
                .value(label, AttributeValue::from(&b"edge"[..])),
        )
        .expect_err("`label` is a vertex column");
    assert_eq!(refusal, Refusal::ForeignField {
        field: "label".into(),
        object: "E".into(),
    });
    assert_eq!(
        u64::from(store.live_count(edge).expect("E is a table")),
        2,
        "neither edge was added"
    );

    let added = store
        .add_part(edge, &Row::new().arrow(src, one).arrow(tgt, two))
        .expect("a complete edge is added");
    assert_eq!(
        added,
        PartKey::from(4_u64),
        "the refused rows' keys stay minted"
    );
    assert_eq!(store.target(src, added), Ok(one));
    assert_eq!(store.target(tgt, added), Ok(two));

    let vertex = object(&store, &Name("V"));
    let refusal = store
        .add_part(vertex, &Row::new())
        .expect_err("a vertex without its label is incomplete");
    assert_eq!(refusal, Refusal::Unset {
        field: "label".into(),
        object: "V".into(),
        part: PartKey::from(3_u64),
    });
}

#[test]
fn a_reference_to_a_dead_part_is_refused_by_name()
{
    let ThreePath {
        mut store,
        vertices: [one, two, three],
        edges: [first, _],
    } = ThreePath::new();
    let vertex = object(&store, &Name("V"));
    let tgt = arrow(&store, &Name("tgt"));
    let label = attribute(&store, &Name("label"));

    let spare = store
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"spare"[..])),
        )
        .expect("a fourth vertex");
    store
        .delete_part(vertex, spare)
        .expect("nothing refers to it");

    let refusal = store
        .set_arrow(tgt, first, spare)
        .expect_err("the vertex is dead");
    assert_eq!(refusal, Refusal::NotLive {
        object: "V".into(),
        part: spare,
    });
    assert_eq!(refusal.to_string(), "`V` part 3 is not live");
    assert_eq!(store.target(tgt, first), Ok(two), "the arrow is unchanged");

    store
        .set_arrow(tgt, first, three)
        .expect("a live vertex is a target");
    assert_eq!(store.target(tgt, first), Ok(three));
    assert_eq!(store.liveness(vertex, one), Ok(Liveness::Live));
}

#[test]
fn a_part_deleted_before_its_label_is_set_owes_none()
{
    let ThreePath { mut store, .. } = ThreePath::new();
    let vertex = object(&store, &Name("V"));

    let mut edit = store.edit();
    let fresh = edit.add_part(vertex).expect("a vertex is minted");
    edit.delete_part(vertex, fresh)
        .expect("nothing refers to it yet");
    assert_eq!(edit.finish(), Ok(()), "a dead part owes no label");
    assert_eq!(store.liveness(vertex, fresh), Ok(Liveness::Dead));

    let edge = object(&store, &Name("E"));
    let mut edit = store.edit();
    let unset_vertex = edit.add_part(vertex).expect("a vertex is minted");
    let unset_edge = edit.add_part(edge).expect("an edge is minted");
    edit.delete_part(edge, unset_edge)
        .expect("nothing refers to the edge");
    edit.delete_part(vertex, unset_vertex)
        .expect("the deleted edge no longer refers to anything");
    let dangling = edit.add_part(edge).expect("another edge is minted");
    assert!(
        matches!(edit.finish(), Err(Refusal::Unset { part, .. }) if part == dangling),
        "the edge left live has no ends"
    );
    for (table, part) in [(vertex, unset_vertex), (edge, unset_edge), (edge, dangling)] {
        assert_eq!(
            store.liveness(table, part),
            Ok(Liveness::Dead),
            "the refused edit's parts are gone, deleted or not"
        );
    }
}

#[test]
fn a_refused_edit_restores_a_deleted_part_with_its_values()
{
    let ThreePath { mut store, .. } = ThreePath::new();
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let label = attribute(&store, &Name("label"));
    let four = AttributeValue::from(&b"four"[..]);
    let lone = store
        .add_part(vertex, &Row::new().value(label, four.clone()))
        .expect("a labelled vertex is complete");

    let mut edit = store.edit();
    let dangling = edit.add_part(edge).expect("an edge is minted");
    edit.delete_part(vertex, lone)
        .expect("no edge refers to the lone vertex, the unset one included");
    assert!(
        matches!(edit.finish(), Err(Refusal::Unset { part, .. }) if part == dangling),
        "an edge with no ends is refused"
    );

    assert_eq!(store.liveness(vertex, lone), Ok(Liveness::Live));
    assert_eq!(store.value(label, lone), Ok(&four));
}

#[test]
fn an_abandoned_delete_rejoins_the_inverse_it_shared()
{
    let presentation = Presentation::new()
        .object("V")
        .attribute_type("Text")
        .attribute("tag", "V", "Text", Indexing::Indexed);
    let schema = Schema::present(&presentation).expect("the tagged schema presents");
    let mut store = Store::new(schema, params()).expect("the parameters are supported");
    let vertex = object(&store, &Name("V"));
    let tag = attribute(&store, &Name("tag"));
    let shared = AttributeValue::from(&b"shared"[..]);
    let [first, second] = [(); 2].map(|()| {
        store
            .add_part(vertex, &Row::new().value(tag, shared.clone()))
            .expect("a tagged vertex is complete")
    });

    let mut edit = store.edit();
    edit.delete_part(vertex, first)
        .expect("nothing refers to a vertex");
    edit.abandon();

    assert_eq!(store.liveness(vertex, first), Ok(Liveness::Live));
    assert_eq!(
        store.value_preimage(tag, &shared),
        Ok(&[first, second][..]),
        "the restored vertex rejoins the list in key order"
    );
}
