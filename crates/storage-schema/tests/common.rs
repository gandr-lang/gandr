//! Schemas and stores the area suites share.

use gandr_storage_records::TreeParams;
use gandr_storage_schema::ArrowId;
use gandr_storage_schema::AttributeId;
use gandr_storage_schema::AttributeValue;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::ObjectId;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Presentation;
use gandr_storage_schema::Row;
use gandr_storage_schema::Schema;
use gandr_storage_schema::Store;
use gandr_storage_schema::keyed;

/// The graph schema's presentation: vertices with a text label, edges with
/// an indexed source and an unindexed target.
///
/// # Specification
/// trivial.
pub fn graph_presentation() -> Presentation
{
    Presentation::new()
        .object("V")
        .object("E")
        .attribute_type("Text")
        .arrow("src", "E", "V", Indexing::Indexed)
        .arrow("tgt", "E", "V", Indexing::Unindexed)
        .attribute("label", "V", "Text", Indexing::Unindexed)
}

/// The graph schema.
///
/// # Specification
/// trivial.
pub fn graph() -> Schema
{
    Schema::present(&graph_presentation()).expect("the graph schema presents")
}

/// The reflexive-graph schema: every vertex has a loop, `refl`, whose two
/// ends are the vertex.
///
/// # Specification
/// trivial.
pub fn reflexive(refl: Indexing) -> Schema
{
    let identity: [&str; 0] = [];
    let presentation = Presentation::new()
        .object("V")
        .object("E")
        .arrow("src", "E", "V", Indexing::Indexed)
        .arrow("tgt", "E", "V", Indexing::Indexed)
        .arrow("refl", "V", "E", refl)
        .equation("refl_src", "V", ["refl", "src"], identity)
        .equation("refl_tgt", "V", ["refl", "tgt"], identity);
    Schema::present(&presentation).expect("the reflexive-graph schema presents")
}

/// The record plane's parameters every suite builds under.
///
/// # Specification
/// trivial.
pub fn params() -> TreeParams
{
    TreeParams::default()
}

/// A store's object by name.
///
/// # Specification
/// trivial.
pub fn object(
    store: &Store,
    name: &Name,
) -> ObjectId
{
    store
        .schema()
        .object(name.0)
        .expect("the object is in the schema")
}

/// A store's arrow by name.
///
/// # Specification
/// trivial.
pub fn arrow(
    store: &Store,
    name: &Name,
) -> ArrowId
{
    store
        .schema()
        .arrow(name.0)
        .expect("the arrow is in the schema")
}

/// A store's attribute by name.
///
/// # Specification
/// trivial.
pub fn attribute(
    store: &Store,
    name: &Name,
) -> AttributeId
{
    store
        .schema()
        .attribute(name.0)
        .expect("the attribute is in the schema")
}

/// An element name as the suites spell it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Name(pub &'static str);

/// The path `1 → 2 → 3`: three labelled vertices and the two edges between
/// them.
#[derive(Debug)]
pub struct ThreePath
{
    /// The store.
    pub store: Store,
    /// The vertices, in path order.
    pub vertices: [PartKey; 3],
    /// The edges `1 → 2` and `2 → 3`.
    pub edges: [PartKey; 2],
}

impl ThreePath
{
    /// Builds the path in a fresh graph store.
    ///
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        let mut store = Store::new(graph(), params()).expect("the parameters are supported");
        let vertex = object(&store, &Name("V"));
        let edge = object(&store, &Name("E"));
        let src = arrow(&store, &Name("src"));
        let tgt = arrow(&store, &Name("tgt"));
        let label = attribute(&store, &Name("label"));

        let mut vertices = [PartKey::FIRST; 3];
        for (slot, text) in vertices.iter_mut().zip(["one", "two", "three"]) {
            *slot = store
                .add_part(
                    vertex,
                    &Row::new().value(label, AttributeValue::from(text.as_bytes())),
                )
                .expect("a labelled vertex is complete");
        }
        let [one, two, three] = vertices;
        let first = store
            .add_part(edge, &Row::new().arrow(src, one).arrow(tgt, two))
            .expect("the edge 1 → 2 is complete");
        let second = store
            .add_part(edge, &Row::new().arrow(src, two).arrow(tgt, three))
            .expect("the edge 2 → 3 is complete");
        Self {
            store,
            vertices,
            edges: [first, second],
        }
    }
}

/// Every live source an arrow takes to a target, by scanning the source
/// table: the reference a kept inverse must agree with.
///
/// # Specification
/// trivial.
pub fn scan(
    store: &Store,
    arrow: ArrowId,
    target: PartKey,
) -> Vec<PartKey>
{
    let source = store
        .schema()
        .arrow_at(arrow)
        .expect("the arrow is in the schema")
        .source();
    store
        .parts(source)
        .expect("the source is in the schema")
        .filter(|&part| store.target(arrow, part) == Ok(target))
        .collect()
}

/// A store of the keyed-index schema shaped like a factory's indexes: two
/// tasks, three attempts, four moves, a refusal, two subjects of different
/// widths and three namings.
#[derive(Debug)]
pub struct Keyed
{
    /// The store.
    pub store: Store,
    /// `alpha` (open) and `beta` (closed).
    pub tasks: [PartKey; 2],
    /// `alpha` #1, `alpha` #2 and `beta` #1.
    pub attempts: [PartKey; 3],
    /// Sequence 0 and 1 of `alpha` #1, 0 of `alpha` #2, 0 of `beta` #1.
    pub moves: [PartKey; 4],
    /// One refusal of `beta`.
    pub refusal: PartKey,
    /// A 32-byte digest and a 20-byte revision.
    pub subjects: [PartKey; 2],
    /// The first move names the digest, the second the revision, the fourth
    /// the digest again.
    pub namings: [PartKey; 3],
}

impl Keyed
{
    /// The 32-byte digest subject's value.
    pub const DIGEST: [u8; 32] = [0xd1; 32];
    /// The 20-byte revision subject's value.
    pub const REVISION: [u8; 20] = [0xd1; 20];
    /// The open standing's tag.
    pub const OPEN: [u8; 1] = [0x01];
    /// The closed standing's tag.
    pub const CLOSED: [u8; 1] = [0x02];

    /// Builds the fixture.
    ///
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        let schema = keyed::schema().expect("the keyed schema presents");
        let mut store = Store::new(schema, params()).expect("the parameters are supported");
        let table = |store: &Store, name| object(store, &Name(name));
        let to = |store: &Store, name| arrow(store, &Name(name));
        let field = |store: &Store, name| attribute(store, &Name(name));
        let number = |value: u64| AttributeValue::from(value.to_le_bytes().to_vec());
        let bytes = |value: &[u8]| AttributeValue::from(value);

        let mut tasks = [PartKey::FIRST; 2];
        for (slot, (name, standing)) in tasks
            .iter_mut()
            .zip([("alpha", Self::OPEN), ("beta", Self::CLOSED)])
        {
            let row = Row::new()
                .value(field(&store, "task_name"), bytes(name.as_bytes()))
                .value(field(&store, "task_standing"), bytes(&standing))
                .value(field(&store, "task_heads"), bytes(name.as_bytes()));
            *slot = store.add_part(table(&store, "Task"), &row).expect("a task");
        }
        let [alpha, beta] = tasks;

        let mut attempts = [PartKey::FIRST; 3];
        for (slot, (task, ordinal)) in attempts.iter_mut().zip([(alpha, 1), (alpha, 2), (beta, 1)])
        {
            let row = Row::new()
                .arrow(to(&store, "attempt_task"), task)
                .value(field(&store, "attempt_number"), number(ordinal));
            *slot = store
                .add_part(table(&store, "Attempt"), &row)
                .expect("an attempt");
        }
        let [first, second, third] = attempts;

        let mut moves = [PartKey::FIRST; 4];
        let made = [
            (first, 0, "receipt a1/0"),
            (first, 1, "receipt a1/1"),
            (second, 0, "receipt a2/0"),
            (third, 0, "receipt b1/0"),
        ];
        for (slot, (attempt, seq, receipt)) in moves.iter_mut().zip(made) {
            let row = Row::new()
                .arrow(to(&store, "move_attempt"), attempt)
                .value(field(&store, "move_seq"), number(seq))
                .value(field(&store, "move_receipt"), bytes(receipt.as_bytes()));
            *slot = store.add_part(table(&store, "Move"), &row).expect("a move");
        }

        let row = Row::new()
            .arrow(to(&store, "refusal_task"), beta)
            .value(field(&store, "refusal_commit"), bytes(&[0xc0; 32]))
            .value(
                field(&store, "refusal_reason"),
                bytes(b"the rubric declined"),
            );
        let refusal = store
            .add_part(table(&store, "Refusal"), &row)
            .expect("a refusal");

        let mut subjects = [PartKey::FIRST; 2];
        for (slot, digest) in subjects
            .iter_mut()
            .zip([&Self::DIGEST[..], &Self::REVISION[..]])
        {
            let row = Row::new().value(field(&store, "subject_digest"), bytes(digest));
            *slot = store
                .add_part(table(&store, "Subject"), &row)
                .expect("a subject");
        }

        let [digest, revision] = subjects;
        let [m0, m1, _, m3] = moves;
        let mut namings = [PartKey::FIRST; 3];
        let named = [
            (m0, digest, alpha, 0x01_u8),
            (m1, revision, alpha, 0x02_u8),
            (m3, digest, beta, 0x01_u8),
        ];
        for (slot, (by, subject, task, role)) in namings.iter_mut().zip(named) {
            let row = Row::new()
                .arrow(to(&store, "naming_move"), by)
                .arrow(to(&store, "naming_subject"), subject)
                .arrow(to(&store, "naming_task"), task)
                .value(field(&store, "naming_role"), bytes(&[role]));
            *slot = store
                .add_part(table(&store, "Naming"), &row)
                .expect("a naming");
        }

        Self {
            store,
            tasks,
            attempts,
            moves,
            refusal,
            subjects,
            namings,
        }
    }
}
