//! Gluing: two writers' stores join by a union of their regions, and no key
//! is renumbered.

use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_schema::AttributeValue;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::Row;
use gandr_storage_schema::Store;
use gandr_storage_schema::StoreError;
use gandr_storage_schema::StoreManifest;
use gandr_storage_schema::Writer;
use gandr_storage_schema::keyed;

use crate::common::Name;
use crate::common::ThreePath;
use crate::common::arrow;
use crate::common::attribute;
use crate::common::graph;
use crate::common::object;
use crate::common::params;

/// A graph store that `writer` fills with a path: one vertex for each label,
/// and an edge from each vertex to the next.
///
/// # Specification
/// trivial.
fn path(
    writer: Writer,
    labels: &[AttributeValue],
) -> Store
{
    let mut store = Store::new(graph(), params(), writer).expect("the parameters are supported");
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let label = attribute(&store, &Name("label"));
    let vertices: Vec<PartKey> = labels
        .iter()
        .map(|text| {
            store
                .add_part(vertex, &Row::new().value(label, text.clone()))
                .expect("a labelled vertex")
        })
        .collect();
    for pair in vertices.windows(2) {
        if let [from, to] = *pair {
            store
                .add_part(edge, &Row::new().arrow(src, from).arrow(tgt, to))
                .expect("an edge");
        }
    }
    store
}

/// The path `1 → 2 → 3` committed as writer zero, with the block store that
/// holds it.
#[derive(Debug)]
struct Base
{
    /// The committed manifest.
    manifest: StoreManifest,
    /// The blocks of every table.
    blocks: InMemoryBlockStore,
    /// The vertices, in path order.
    vertices: [PartKey; 3],
    /// The edges `1 → 2` and `2 → 3`.
    edges: [PartKey; 2],
}

impl Base
{
    /// Commits the path.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        let ThreePath {
            mut store,
            vertices,
            edges,
        } = ThreePath::new();
        let mut blocks = InMemoryBlockStore::new();
        store.commit(&mut blocks).expect("the base commits");
        Self {
            manifest: store.manifest().clone(),
            blocks,
            vertices,
            edges,
        }
    }

    /// The base reopened as `writer`.
    ///
    /// # Specification
    /// trivial.
    fn open(
        &self,
        writer: Writer,
    ) -> Store
    {
        Store::open(graph(), params(), writer, &self.manifest, &self.blocks)
            .expect("the base reopens")
    }
}

#[test]
fn two_writers_glue_to_the_union_of_their_parts()
{
    let value_of = |text: &[u8]| AttributeValue::from(text);
    let left = path(Writer::from(1_u16), &[value_of(b"a"), value_of(b"b")]);
    let right = path(Writer::from(2_u16), &[
        value_of(b"x"),
        value_of(b"y"),
        value_of(b"z"),
    ]);
    let vertex = object(&left, &Name("V"));
    let edge = object(&left, &Name("E"));
    let src = arrow(&left, &Name("src"));
    let tgt = arrow(&left, &Name("tgt"));
    let label = attribute(&left, &Name("label"));

    let mut glued = left.clone();
    glued.glue(&right).expect("two writers' regions glue");
    let mut flipped = right.clone();
    flipped.glue(&left).expect("in either order");

    for table in [vertex, edge] {
        let union: Vec<PartKey> = left
            .parts(table)
            .expect("a table")
            .chain(right.parts(table).expect("a table"))
            .collect();
        let keys: Vec<PartKey> = glued.parts(table).expect("a table").collect();
        assert_eq!(
            keys, union,
            "every part under its own key, writer by writer"
        );
        let keys: Vec<PartKey> = flipped.parts(table).expect("a table").collect();
        assert_eq!(keys, union, "the same union from the other side");
    }
    for source in [&left, &right] {
        for part in source.parts(edge).expect("a table") {
            for column in [src, tgt] {
                assert_eq!(
                    glued.target(column, part),
                    source.target(column, part),
                    "every arrow cell"
                );
            }
        }
        for part in source.parts(vertex).expect("a table") {
            assert_eq!(
                glued.value(label, part),
                source.value(label, part),
                "every attribute cell"
            );
            assert_eq!(
                glued.preimage(src, part),
                source.preimage(src, part),
                "every inverse"
            );
        }
    }
    assert_eq!(glued.audit(), Ok(()), "every equation holds");

    let root = glued
        .commit(&mut InMemoryBlockStore::new())
        .expect("the glued store commits");
    let again = flipped
        .commit(&mut InMemoryBlockStore::new())
        .expect("the flipped store commits");
    assert_eq!(root, again, "either order commits to one root");

    let next = glued
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"c"[..])),
        )
        .expect("the glued store mints");
    assert_eq!(
        (next.writer(), u64::from(next.offset())),
        (Writer::from(1_u16), 2),
        "past its own writer's counter"
    );
}

#[test]
fn two_writers_that_share_a_base_glue_over_it()
{
    let base = Base::new();
    let [one, two, three] = base.vertices;
    let [first, second] = base.edges;
    let mut left = base.open(Writer::from(1_u16));
    let mut right = base.open(Writer::from(2_u16));
    let vertex = object(&left, &Name("V"));
    let edge = object(&left, &Name("E"));
    let src = arrow(&left, &Name("src"));
    let tgt = arrow(&left, &Name("tgt"));
    let label = attribute(&left, &Name("label"));

    let back = left
        .add_part(edge, &Row::new().arrow(src, three).arrow(tgt, one))
        .expect("the left writer closes the cycle");
    let four = right
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"four"[..])),
        )
        .expect("the right writer adds a vertex");
    let onward = right
        .add_part(edge, &Row::new().arrow(src, three).arrow(tgt, four))
        .expect("and an edge to it");

    left.glue(&right)
        .expect("the stores agree on the base, so they glue");
    let vertices: Vec<PartKey> = left.parts(vertex).expect("a table").collect();
    assert_eq!(vertices, [one, two, three, four], "the base's parts once");
    let edges: Vec<PartKey> = left.parts(edge).expect("a table").collect();
    assert_eq!(edges, [first, second, back, onward]);
    assert_eq!(
        left.preimage(src, three),
        Ok(&[back, onward][..]),
        "both writers' edges leave the shared vertex"
    );
    assert_eq!(left.target(tgt, onward), Ok(four));
    assert_eq!(left.audit(), Ok(()), "every equation holds");

    let once = left.clone();
    left.glue(&right)
        .expect("the glued store agrees with the right");
    assert_eq!(left, once, "a second glue adds nothing");
}

#[test]
fn two_stores_that_disagree_on_a_shared_region_do_not_glue()
{
    let base = Base::new();
    let [_, two, _] = base.vertices;
    let [_, second] = base.edges;
    let mut left = base.open(Writer::from(1_u16));
    let vertex = object(&left, &Name("V"));
    let edge = object(&left, &Name("E"));
    let label = attribute(&left, &Name("label"));
    left.add_part(
        vertex,
        &Row::new().value(label, AttributeValue::from(&b"left"[..])),
    )
    .expect("the left writer adds a vertex");
    let before = left.clone();

    let mut relabelled = base.open(Writer::from(2_u16));
    relabelled
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"right"[..])),
        )
        .expect("the right writer adds a vertex");
    relabelled
        .set_value(label, two, AttributeValue::from(&b"deux"[..]))
        .expect("the right writer relabels a vertex of the base");
    let refusal = left.glue(&relabelled).err();
    assert_eq!(
        refusal,
        Some(StoreError::Refused(Refusal::Disagreed {
            object: "V".into(),
            writer: Writer::from(0_u16),
        })),
        "a cell of the base that differs"
    );
    assert_eq!(
        refusal.map(|error| error.to_string()).as_deref(),
        Some("the two stores hold writer 0's region of `V` apart, so they do not glue")
    );
    assert_eq!(left, before, "a refused glue changes nothing");

    let mut pruned = base.open(Writer::from(2_u16));
    pruned
        .delete_part(edge, second)
        .expect("nothing refers to an edge");
    assert_eq!(
        left.glue(&pruned).err(),
        Some(StoreError::Refused(Refusal::Disagreed {
            object: "E".into(),
            writer: Writer::from(0_u16),
        })),
        "a part of the base that one store deleted"
    );
    assert_eq!(left, before, "a refused glue changes nothing");

    let schema = keyed::schema().expect("the keyed schema presents");
    let foreign = Store::new(schema, params(), Writer::from(2_u16)).expect("a keyed store");
    assert!(
        matches!(left.glue(&foreign), Err(StoreError::SchemaMismatch { .. })),
        "a store of another schema"
    );
}
