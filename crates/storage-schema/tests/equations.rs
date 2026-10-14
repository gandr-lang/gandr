//! Path equations, checked on every edit at the parts the edit can reach.

use gandr_storage_schema::Indexing;
use gandr_storage_schema::Liveness;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::Row;
use gandr_storage_schema::Store;

use crate::common::Name;
use crate::common::ThreePath;
use crate::common::arrow;
use crate::common::object;
use crate::common::params;
use crate::common::reflexive;
use crate::common::scan;

/// A reflexive graph holding two vertices, each with its own loop.
///
/// # Specification
/// trivial.
fn two_loops(refl: Indexing) -> (Store, [PartKey; 2], [PartKey; 2])
{
    let mut store = Store::new(reflexive(refl), params()).expect("the parameters are supported");
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let loop_of = arrow(&store, &Name("refl"));

    let mut vertices = [PartKey::FIRST; 2];
    let mut loops = [PartKey::FIRST; 2];
    let mut edit = store.edit();
    for (vertex_slot, loop_slot) in vertices.iter_mut().zip(loops.iter_mut()) {
        let at = edit.add_part(vertex).expect("a vertex is minted");
        let around = edit.add_part(edge).expect("a loop is minted");
        edit.set_arrow(src, around, at)
            .expect("the loop leaves its vertex");
        edit.set_arrow(tgt, around, at)
            .expect("the loop returns to it");
        edit.set_arrow(loop_of, at, around)
            .expect("the vertex names its loop");
        *vertex_slot = at;
        *loop_slot = around;
    }
    edit.finish().expect("each loop is at its vertex");
    (store, vertices, loops)
}

#[test]
fn a_loop_that_leaves_its_vertex_is_refused_by_equation()
{
    let mut store =
        Store::new(reflexive(Indexing::Indexed), params()).expect("the parameters are supported");
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let loop_of = arrow(&store, &Name("refl"));

    let mut edit = store.edit();
    let one = edit.add_part(vertex).expect("vertex one");
    let two = edit.add_part(vertex).expect("vertex two");
    let around = edit.add_part(edge).expect("a loop at one");
    edit.set_arrow(src, around, one).expect("src");
    edit.set_arrow(tgt, around, one).expect("tgt");
    edit.set_arrow(loop_of, one, around).expect("one's loop");
    edit.set_arrow(loop_of, two, around)
        .expect("two borrows one's loop");
    let refusal = edit.finish().expect_err("two's loop leaves two");
    assert_eq!(refusal, Refusal::EquationViolated {
        equation: "refl_src".into(),
        object: "V".into(),
        part: two,
        left: one,
        right: two,
    });
    assert_eq!(
        refusal.to_string(),
        "equation `refl_src` fails at `V` part 1: the left side reaches 0, the right 1"
    );
    assert_eq!(
        store.liveness(vertex, one),
        Ok(Liveness::Dead),
        "the refused edit added nothing"
    );

    let (store, [first, second], [first_loop, second_loop]) = two_loops(Indexing::Indexed);
    assert_eq!(store.target(loop_of, first), Ok(first_loop));
    assert_eq!(store.target(loop_of, second), Ok(second_loop));
    assert_eq!(
        store.audit(),
        Ok(()),
        "the admitted store satisfies every equation"
    );
}

#[test]
fn retargeting_an_arrow_rechecks_every_part_whose_path_crosses_it()
{
    for indexing in [Indexing::Indexed, Indexing::Unindexed] {
        let (mut store, [first, second], [first_loop, _]) = two_loops(indexing);
        let edge = object(&store, &Name("E"));
        let src = arrow(&store, &Name("src"));
        let tgt = arrow(&store, &Name("tgt"));

        assert_eq!(
            store.set_arrow(src, first_loop, second),
            Err(Refusal::EquationViolated {
                equation: "refl_src".into(),
                object: "V".into(),
                part: first,
                left: second,
                right: first,
            }),
            "the vertex whose loop moved is found through `refl`, kept or scanned"
        );
        assert_eq!(
            store.target(src, first_loop),
            Ok(first),
            "the refused edit is undone"
        );

        let free = store
            .add_part(edge, &Row::new().arrow(src, first).arrow(tgt, second))
            .expect("an edge no vertex names as its loop");
        store
            .set_arrow(src, free, second)
            .expect("no equation crosses a free edge");
        assert_eq!(store.target(src, free), Ok(second));
        assert_eq!(
            store.audit(),
            Ok(()),
            "every equation holds after the accepted edits"
        );
    }
}

#[test]
fn every_inverse_agrees_with_a_scan_after_every_edit()
{
    let ThreePath {
        mut store,
        vertices: [one, two, three],
        edges: [first, second],
    } = ThreePath::new();
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));

    let agree = |store: &Store, step: &str| {
        for target in store.parts(vertex).expect("V is a table") {
            assert_eq!(
                store
                    .preimage(src, target)
                    .expect("`src` keeps its inverse"),
                scan(store, src, target).as_slice(),
                "the inverse of `src` at {target} after {step}"
            );
        }
    };

    agree(&store, "building");
    let third = store
        .add_part(edge, &Row::new().arrow(src, one).arrow(tgt, three))
        .expect("an edge 1 → 3");
    agree(&store, "adding an edge");
    store
        .set_arrow(src, second, one)
        .expect("2 → 3 becomes 1 → 3");
    agree(&store, "retargeting a source");
    store.delete_part(edge, first).expect("1 → 2 goes");
    agree(&store, "deleting an edge");
    store.delete_part(vertex, two).expect("vertex 2 is free");
    agree(&store, "deleting a vertex");
    assert_eq!(
        store.preimage(src, one),
        Ok(&[second, third][..]),
        "both edges leave vertex 1"
    );
    assert_eq!(
        store.preimage(src, two),
        Err(Refusal::NotLive {
            object: "V".into(),
            part: two,
        }),
        "a dead vertex has no preimage"
    );
}

#[test]
fn an_abandoned_edit_leaves_no_part_and_no_reused_key()
{
    let ThreePath { mut store, .. } = ThreePath::new();
    let vertex = object(&store, &Name("V"));

    let mut edit = store.edit();
    let abandoned = edit.add_part(vertex).expect("a vertex is minted");
    edit.abandon();
    assert_eq!(
        store.liveness(vertex, abandoned),
        Ok(Liveness::Dead),
        "abandoned"
    );

    let mut edit = store.edit();
    let dropped = edit.add_part(vertex).expect("a vertex is minted");
    drop(edit);
    assert_eq!(
        store.liveness(vertex, dropped),
        Ok(Liveness::Dead),
        "dropped unfinished"
    );

    let mut edit = store.edit();
    let next = edit.add_part(vertex).expect("a vertex is minted");
    assert_eq!(
        u64::from(dropped),
        u64::from(abandoned).saturating_add(1),
        "keys advance"
    );
    assert_eq!(
        u64::from(next),
        u64::from(dropped).saturating_add(1),
        "and are never reused"
    );
    edit.abandon();
    assert_eq!(
        u64::from(store.live_count(vertex).expect("V is a table")),
        3,
        "the path's vertices"
    );
}

#[test]
fn a_refused_close_restores_the_store()
{
    let (mut store, [first, second], [first_loop, second_loop]) = two_loops(Indexing::Indexed);
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let loop_of = arrow(&store, &Name("refl"));
    let before: Vec<(PartKey, PartKey, PartKey)> = store
        .parts(edge)
        .expect("E is a table")
        .map(|part| {
            (
                part,
                store.target(src, part).expect("src"),
                store.target(tgt, part).expect("tgt"),
            )
        })
        .collect();

    let mut edit = store.edit();
    let extra = edit.add_part(edge).expect("an extra edge");
    edit.set_arrow(src, extra, first).expect("src");
    edit.set_arrow(tgt, extra, second).expect("tgt");
    edit.set_arrow(loop_of, first, extra)
        .expect("first's loop becomes the extra edge");
    edit.set_arrow(tgt, second_loop, first)
        .expect("second's loop is bent");
    edit.delete_part(edge, first_loop)
        .expect("first's old loop is now free");
    assert!(edit.finish().is_err(), "the extra edge is not a loop");

    let after: Vec<(PartKey, PartKey, PartKey)> = store
        .parts(edge)
        .expect("E is a table")
        .map(|part| {
            (
                part,
                store.target(src, part).expect("src"),
                store.target(tgt, part).expect("tgt"),
            )
        })
        .collect();
    assert_eq!(after, before, "every edge and cell is restored");
    assert_eq!(
        store.target(loop_of, first),
        Ok(first_loop),
        "the loop arrow is restored"
    );
    assert_eq!(
        store.preimage(loop_of, first_loop),
        Ok(&[first][..]),
        "and its inverse"
    );
    assert_eq!(
        store.preimage(src, first),
        Ok(&[first_loop][..]),
        "and the source inverse"
    );
    assert_eq!(
        store.liveness(edge, extra),
        Ok(Liveness::Dead),
        "the extra edge is gone"
    );
    assert_eq!(store.liveness(vertex, second), Ok(Liveness::Live));
    assert_eq!(store.audit(), Ok(()));
}
