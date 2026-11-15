//! One root per store, and proofs of what it holds against that root.

use gandr_storage_records::BoundaryParams;
use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::Record;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_schema::Answer;
use gandr_storage_schema::AttributeValue;
use gandr_storage_schema::Liveness;
use gandr_storage_schema::ManifestFault;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Proof;
use gandr_storage_schema::ProofFault;
use gandr_storage_schema::ProofImage;
use gandr_storage_schema::Question;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::Row;
use gandr_storage_schema::Store;
use gandr_storage_schema::StoreError;
use gandr_storage_schema::keyed;

use crate::common::Keyed;
use crate::common::Name;
use crate::common::ThreePath;
use crate::common::arrow;
use crate::common::attribute;
use crate::common::graph;
use crate::common::object;
use crate::common::params;

/// The keyed fixture with its refusal deleted, committed.
///
/// # Specification
/// trivial.
fn committed() -> Keyed
{
    let mut fixture = Keyed::new();
    let table = object(&fixture.store, &Name("Refusal"));
    fixture
        .store
        .delete_part(table, fixture.refusal)
        .expect("nothing refers to a refusal");
    fixture
        .store
        .commit(&mut InMemoryBlockStore::new())
        .expect("the fixture commits");
    fixture
}

/// Proves a question and verifies the proof against the store's root.
///
/// # Specification
/// trivial.
fn answer(
    store: &Store,
    question: &Question,
) -> Result<Answer, StoreError>
{
    let proof = store.prove(question)?;
    proof.verify(store.root(), store.schema(), params(), question)
}

#[test]
fn an_empty_store_has_a_root_that_names_its_schema()
{
    let first = Store::new(graph(), params()).expect("a graph store");
    let second = Store::new(graph(), params()).expect("another graph store");
    let schema = keyed::schema().expect("the keyed schema presents");
    let other = Store::new(schema.clone(), params()).expect("a keyed store");
    assert_eq!(first.root(), second.root(), "one schema, one empty root");
    assert_ne!(first.root(), other.root(), "another schema, another root");
    assert_eq!(
        other.manifest().schema(),
        schema.identity(),
        "the manifest names the schema"
    );
    let vertex = object(&first, &Name("V"));
    assert_eq!(
        first.parts(vertex).expect("V is a table").count(),
        0,
        "no part"
    );
}

#[test]
fn every_kind_of_proof_verifies_against_the_root()
{
    let Keyed {
        store,
        tasks: [_, beta],
        attempts: [first, ..],
        moves: [m0, m1, ..],
        refusal,
        subjects: [digest, _],
        ..
    } = committed();
    let task = object(&store, &Name("Task"));
    let refusals = object(&store, &Name("Refusal"));
    let move_attempt = arrow(&store, &Name("move_attempt"));
    let receipt = attribute(&store, &Name("move_receipt"));
    let subject_digest = attribute(&store, &Name("subject_digest"));

    assert_eq!(
        answer(&store, &Question::Part {
            object: task,
            part: beta
        }),
        Ok(Answer::Liveness(Liveness::Live)),
        "a live part"
    );
    assert_eq!(
        answer(&store, &Question::Part {
            object: refusals,
            part: refusal,
        }),
        Ok(Answer::Liveness(Liveness::Dead)),
        "a deleted part"
    );
    assert_eq!(
        answer(&store, &Question::Arrow {
            arrow: move_attempt,
            part: m1,
        }),
        Ok(Answer::Target(first)),
        "an arrow's value"
    );
    assert_eq!(
        answer(&store, &Question::Value {
            attribute: receipt,
            part: m0,
        }),
        Ok(Answer::Value(AttributeValue::from(&b"receipt a1/0"[..]))),
        "an attribute's value"
    );
    assert_eq!(
        answer(&store, &Question::Preimage {
            arrow: move_attempt,
            target: first,
        }),
        Ok(Answer::Preimage(Box::from([m0, m1]))),
        "a complete preimage"
    );
    assert_eq!(
        answer(&store, &Question::ValuePreimage {
            attribute: subject_digest,
            value: AttributeValue::from(&Keyed::DIGEST[..]),
        }),
        Ok(Answer::Preimage(Box::from([digest]))),
        "a complete value preimage"
    );
    assert_eq!(
        store.prove(&Question::Arrow {
            arrow: arrow(&store, &Name("refusal_task")),
            part: refusal,
        }),
        Err(StoreError::Refused(Refusal::NotLive {
            object: "Refusal".into(),
            part: refusal,
        })),
        "a deleted part has no arrow to prove"
    );
}

#[test]
fn a_proof_against_another_root_is_refused()
{
    let Keyed {
        mut store,
        tasks: [alpha, beta],
        ..
    } = committed();
    let task = object(&store, &Name("Task"));
    let question = Question::Part {
        object: task,
        part: alpha,
    };
    let proof = store.prove(&question).expect("a proof");
    let old = store.root();

    store
        .set_value(
            attribute(&store, &Name("task_heads")),
            beta,
            AttributeValue::from(&b"moved"[..]),
        )
        .expect("beta's heads move");
    let new = store
        .commit(&mut InMemoryBlockStore::new())
        .expect("the edit commits");
    assert_ne!(new, old, "the edit changed the root");

    let refusal = proof
        .verify(new, store.schema(), params(), &question)
        .expect_err("the proof is for the old root");
    assert_eq!(refusal, StoreError::RootMismatch {
        expected: new,
        found: old
    });
    assert_eq!(
        refusal.to_string(),
        format!("the proof's manifest hashes to {old}, not {new}")
    );
    assert_eq!(old.to_string().len(), 64, "a root renders in full");
    assert_eq!(
        proof.verify(old, store.schema(), params(), &question),
        Ok(Answer::Liveness(Liveness::Live)),
        "against its own root it still verifies"
    );
}

#[test]
fn a_proof_under_another_schema_is_refused()
{
    let Keyed {
        store,
        tasks: [alpha, beta],
        ..
    } = committed();
    let task = object(&store, &Name("Task"));
    let question = Question::Part {
        object: task,
        part: alpha,
    };
    let proof = store.prove(&question).expect("a proof");
    let other = graph();

    assert_eq!(
        proof.verify(store.root(), &other, params(), &question),
        Err(StoreError::SchemaMismatch {
            expected: other.identity(),
            found: store.schema().identity(),
        }),
        "a reader of another schema"
    );
    let current = params();
    let capped = TreeParams::new(
        current.kind(),
        current.encoding_version(),
        current.hash_algorithm(),
        current.separator_convention(),
        BoundaryParams::new(
            current.boundary().profile(),
            current.boundary().mask_bits(),
            BoundaryRecordCap::try_from(65_u32).expect("sixty-five records is an admissible cap"),
        ),
    );
    assert_eq!(
        proof.verify(store.root(), store.schema(), capped, &question),
        Err(StoreError::ProfileMismatch),
        "a reader of other boundary parameters"
    );
    assert_eq!(
        proof.verify(store.root(), store.schema(), params(), &Question::Part {
            object: task,
            part: beta
        }),
        Err(StoreError::WrongQuestion),
        "another question"
    );
}

#[test]
fn an_unindexed_preimage_is_not_proved()
{
    let ThreePath {
        mut store,
        vertices: [_, two, _],
        ..
    } = ThreePath::new();
    store
        .commit(&mut InMemoryBlockStore::new())
        .expect("the path commits");
    let tgt = arrow(&store, &Name("tgt"));
    assert_eq!(
        store.prove(&Question::Preimage {
            arrow: tgt,
            target: two
        }),
        Err(StoreError::Refused(Refusal::NotIndexed {
            field: "tgt".into()
        }))
    );
    let label = attribute(&store, &Name("label"));
    assert_eq!(
        store.prove(&Question::ValuePreimage {
            attribute: label,
            value: AttributeValue::from(&b"two"[..]),
        }),
        Err(StoreError::Refused(Refusal::NotIndexed {
            field: "label".into()
        }))
    );
}

#[test]
fn a_value_preimage_excludes_a_value_it_prefixes()
{
    let mut fixture = Keyed::new();
    let subjects = object(&fixture.store, &Name("Subject"));
    let digest = attribute(&fixture.store, &Name("subject_digest"));
    let longer: Vec<u8> = Keyed::DIGEST.iter().copied().chain([0x00]).collect();
    let extended = fixture
        .store
        .add_part(
            subjects,
            &Row::new().value(digest, AttributeValue::from(longer.clone())),
        )
        .expect("a subject whose digest extends another");
    fixture
        .store
        .commit(&mut InMemoryBlockStore::new())
        .expect("the fixture commits");

    let [short, revision] = fixture.subjects;
    for (value, expected) in [
        (Vec::from(Keyed::DIGEST), short),
        (longer, extended),
        (Vec::from(Keyed::REVISION), revision),
    ] {
        assert_eq!(
            answer(&fixture.store, &Question::ValuePreimage {
                attribute: digest,
                value: AttributeValue::from(value),
            }),
            Ok(Answer::Preimage(Box::from([expected]))),
            "each digest's own subject only"
        );
    }

    let move_attempt = arrow(&fixture.store, &Name("move_attempt"));
    let [m0, m1, m2, _] = fixture.moves;
    let [first, second, _] = fixture.attempts;
    assert_eq!(
        answer(&fixture.store, &Question::Preimage {
            arrow: move_attempt,
            target: first,
        }),
        Ok(Answer::Preimage(Box::from([m0, m1]))),
        "a target's run stops before the next target's"
    );
    assert_eq!(
        answer(&fixture.store, &Question::Preimage {
            arrow: move_attempt,
            target: second,
        }),
        Ok(Answer::Preimage(Box::from([m2]))),
    );
}

#[test]
fn a_table_lies_on_the_record_plane_as_documented()
{
    let mut store = Store::new(graph(), params()).expect("a graph store");
    let vertex = object(&store, &Name("V"));
    let edge = object(&store, &Name("E"));
    let src = arrow(&store, &Name("src"));
    let tgt = arrow(&store, &Name("tgt"));
    let label = attribute(&store, &Name("label"));
    let one = store
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"a"[..])),
        )
        .expect("a vertex");
    let two = store
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"b"[..])),
        )
        .expect("a vertex");
    let joined = store
        .add_part(edge, &Row::new().arrow(src, one).arrow(tgt, two))
        .expect("an edge");
    store
        .commit(&mut InMemoryBlockStore::new())
        .expect("the graph commits");
    assert_eq!(usize::from(src), 0, "`src` sorts first");
    assert_eq!(usize::from(tgt), 1);
    assert_eq!(u64::from(joined), 0);

    // The edge table, written out by hand: the part, both cells, and the
    // inverse entry of the indexed `src`.
    let records = [
        Record::new(vec![0x00, 0, 0, 0, 0, 0, 0, 0, 0], Vec::new()),
        Record::new(vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], vec![
            0, 0, 0, 0, 0, 0, 0, 0,
        ]),
        Record::new(vec![0x01, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], vec![
            1, 0, 0, 0, 0, 0, 0, 0,
        ]),
        Record::new(
            vec![
                0x03, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            Vec::new(),
        ),
    ];
    let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
    let expected = RecordTree::build(&refs, params()).expect("the hand-written records build");
    let table = store
        .manifest()
        .tables()
        .get(usize::from(edge))
        .expect("the edge table");
    assert_eq!(
        table.root_node(),
        expected.root_node_hash(),
        "the edge table's tree"
    );
    assert_eq!(table.records(), expected.root().record_count());
    assert_eq!(table.next(), PartKey::from(1_u64), "the edge counter");

    // The vertex table: two parts and two label cells, no inverse.
    let records = [
        Record::new(vec![0x00, 0, 0, 0, 0, 0, 0, 0, 0], Vec::new()),
        Record::new(vec![0x00, 0, 0, 0, 0, 0, 0, 0, 1], Vec::new()),
        Record::new(
            vec![0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            b"a".to_vec(),
        ),
        Record::new(
            vec![0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
            b"b".to_vec(),
        ),
    ];
    let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
    let expected = RecordTree::build(&refs, params()).expect("the hand-written records build");
    let table = store
        .manifest()
        .tables()
        .get(usize::from(vertex))
        .expect("the vertex table");
    assert_eq!(
        table.root_node(),
        expected.root_node_hash(),
        "the vertex table's tree"
    );
}

#[test]
fn the_root_is_a_function_of_the_contents_and_counters()
{
    let build = || {
        let ThreePath { mut store, .. } = ThreePath::new();
        store
            .commit(&mut InMemoryBlockStore::new())
            .expect("the path commits");
        store
    };
    let mut first = build();
    let second = build();
    assert_eq!(first.root(), second.root(), "the same edits, the same root");

    let vertex = object(&first, &Name("V"));
    let label = attribute(&first, &Name("label"));
    let spare = first
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"spare"[..])),
        )
        .expect("a spare vertex");
    first.delete_part(vertex, spare).expect("and it goes");
    first
        .commit(&mut InMemoryBlockStore::new())
        .expect("the round trip commits");
    assert_ne!(
        first.root(),
        second.root(),
        "the same parts, a later counter"
    );

    let mut third = build();
    let spare = third
        .add_part(
            vertex,
            &Row::new().value(label, AttributeValue::from(&b"other"[..])),
        )
        .expect("another spare vertex");
    third.delete_part(vertex, spare).expect("and it goes");
    third
        .commit(&mut InMemoryBlockStore::new())
        .expect("the round trip commits");
    assert_eq!(
        third.root(),
        first.root(),
        "a dead part's cells are not committed"
    );
}

/// The evidence tag a proof's image carries after its manifest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Tag(u8);

/// Every kind of question against the committed keyed fixture, with the
/// evidence tag its proof's image carries.
///
/// # Specification
/// trivial.
fn questions(fixture: &Keyed) -> [(Question, Tag); 6]
{
    let store = &fixture.store;
    let [_, beta] = fixture.tasks;
    let [first, ..] = fixture.attempts;
    let [m0, m1, ..] = fixture.moves;
    [
        (
            Question::Part {
                object: object(store, &Name("Task")),
                part: beta,
            },
            Tag(0x01),
        ),
        (
            Question::Part {
                object: object(store, &Name("Refusal")),
                part: fixture.refusal,
            },
            Tag(0x02),
        ),
        (
            Question::Arrow {
                arrow: arrow(store, &Name("move_attempt")),
                part: m1,
            },
            Tag(0x01),
        ),
        (
            Question::Value {
                attribute: attribute(store, &Name("move_receipt")),
                part: m0,
            },
            Tag(0x01),
        ),
        (
            Question::Preimage {
                arrow: arrow(store, &Name("move_attempt")),
                target: first,
            },
            Tag(0x03),
        ),
        (
            Question::ValuePreimage {
                attribute: attribute(store, &Name("subject_digest")),
                value: AttributeValue::from(&Keyed::DIGEST[..]),
            },
            Tag(0x03),
        ),
    ]
}

#[test]
fn every_kind_of_proof_round_trips_through_its_image()
{
    let fixture = committed();
    let store = &fixture.store;
    let manifest = store.manifest().encode();
    let manifest: &[u8] = manifest.as_ref();
    let length = u64::try_from(manifest.len()).expect("a manifest fits sixty-four bits");
    for (question, tag) in questions(&fixture) {
        let proof = store.prove(&question).expect("a proof");
        let image = proof.encode();
        let bytes: &[u8] = image.as_ref();
        assert_eq!(
            bytes.get(.. 8),
            Some(&length.to_le_bytes()[..]),
            "the manifest's length opens the image: {question:?}"
        );
        assert_eq!(
            bytes.get(8 .. 8 + manifest.len()),
            Some(manifest),
            "then the manifest: {question:?}"
        );
        assert_eq!(
            bytes.get(8 + manifest.len()),
            Some(&tag.0),
            "then the evidence tag: {question:?}"
        );
        let decoded = Proof::decode(ProofImage::from(bytes), store.schema(), params(), &question)
            .expect("the image decodes");
        assert_eq!(decoded, proof, "the proof the store made: {question:?}");
        assert_eq!(
            decoded.verify(store.root(), store.schema(), params(), &question),
            proof.verify(store.root(), store.schema(), params(), &question),
            "and it verifies to the same answer: {question:?}"
        );
    }
}

#[test]
fn a_malformed_proof_image_is_refused_by_part()
{
    let fixture = committed();
    let store = &fixture.store;
    let decode = |bytes: &[u8], question: &Question| {
        Proof::decode(ProofImage::from(bytes), store.schema(), params(), question)
    };
    let refused = |fault| Err(StoreError::Proof { fault });
    let [_, (dead, _), _, (value, _), (preimage, _), _] = questions(&fixture);
    let image = store.prove(&dead).expect("a dead part's proof").encode();
    let bytes: &[u8] = image.as_ref();
    let tag = 8 + store.manifest().encode().as_ref().len();

    for end in 0 .. bytes.len() {
        assert_eq!(
            decode(bytes.get(.. end).expect("a prefix"), &dead),
            refused(ProofFault::Truncated),
            "a prefix of {end} bytes"
        );
    }
    let mut trailing = bytes.to_vec();
    trailing.push(0x00);
    assert_eq!(
        decode(&trailing, &dead),
        refused(ProofFault::Trailing),
        "a byte past the last node"
    );
    let mut evidence = bytes.to_vec();
    *evidence.get_mut(tag).expect("the evidence tag") = 0x09;
    assert_eq!(
        decode(&evidence, &dead),
        refused(ProofFault::Tag),
        "an unknown evidence tag"
    );
    let mut neighbour = bytes.to_vec();
    *neighbour.get_mut(tag + 1).expect("the predecessor's tag") = 0x07;
    assert_eq!(
        decode(&neighbour, &dead),
        refused(ProofFault::Tag),
        "an unknown neighbour tag"
    );
    let mut domain = bytes.to_vec();
    *domain.get_mut(8).expect("the manifest's first byte") ^= 0x01;
    assert_eq!(
        decode(&domain, &dead),
        Err(StoreError::Manifest {
            fault: ManifestFault::Domain
        }),
        "a foreign manifest"
    );
    assert_eq!(
        Proof::decode(ProofImage::from(bytes), &graph(), params(), &dead),
        Err(StoreError::SchemaMismatch {
            expected: graph().identity(),
            found: store.schema().identity(),
        }),
        "a reader of another schema"
    );

    let run = store.prove(&preimage).expect("a preimage's proof").encode();
    assert_eq!(
        decode(run.as_ref(), &value),
        Err(StoreError::WrongQuestion),
        "a run offered for one cell"
    );

    let cell = store.prove(&value).expect("a value's proof").encode();
    let mut forged = cell.as_ref().to_vec();
    *forged.get_mut(tag + 9).expect("the value's first byte") ^= 0x01;
    let forged = decode(&forged, &value).expect("a forged value still decodes");
    assert!(
        matches!(
            forged.verify(store.root(), store.schema(), params(), &value),
            Err(StoreError::Records(_))
        ),
        "and is refused by verification"
    );

    let rendered: Vec<String> = [ProofFault::Truncated, ProofFault::Tag, ProofFault::Trailing]
        .into_iter()
        .map(|fault| StoreError::Proof { fault }.to_string())
        .collect();
    assert_eq!(rendered, [
        "malformed proof image: the proof image ends inside a part",
        "malformed proof image: the proof image carries an unknown tag",
        "malformed proof image: bytes follow the last node",
    ]);
}
