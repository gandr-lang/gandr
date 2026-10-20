//! The keyed-index schema: a factory's dialogue, project and provenance
//! indexes as one schema, round-tripped through the block store.

use gandr_storage_records::BlockStore as _;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::DecodedNode;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::decode_node;
use gandr_storage_schema::AttributeValue;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::LayoutFault;
use gandr_storage_schema::ManifestImage;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::Row;
use gandr_storage_schema::Store;
use gandr_storage_schema::StoreError;
use gandr_storage_schema::StoreManifest;
use gandr_storage_schema::keyed;

use crate::common::Keyed;
use crate::common::Name;
use crate::common::arrow;
use crate::common::attribute;
use crate::common::object;
use crate::common::params;

/// Every record a committed table holds, loaded from the block store.
///
/// # Specification
/// trivial.
fn records_of(
    blocks: &InMemoryBlockStore,
    root: NodeHash,
) -> Vec<Record>
{
    let stored = blocks.load(root).expect("the root is stored");
    let node = decode_node(stored.bytes(), &mut DecodeWork::new()).expect("the root decodes");
    match node {
        DecodedNode::Leaf(leaf) => leaf.records().to_vec(),
        DecodedNode::Internal(internal) => internal
            .children()
            .iter()
            .flat_map(|child| {
                let stored = blocks.load(child.identity()).expect("the child is stored");
                let node =
                    decode_node(stored.bytes(), &mut DecodeWork::new()).expect("the child decodes");
                node.as_leaf()
                    .expect("children are leaves")
                    .records()
                    .to_vec()
            })
            .collect(),
    }
}

/// A manifest naming `records` as the table at `table`, its tree written to
/// the block store; everything else is the original manifest.
///
/// # Specification
/// trivial.
fn doctored(
    manifest: &StoreManifest,
    table: Table,
    records: &mut [Record],
    blocks: &mut InMemoryBlockStore,
) -> StoreManifest
{
    records.sort();
    let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
    let tree = RecordTree::build(&refs, params()).expect("the doctored records build");
    tree.write_to(blocks).expect("the doctored tree is written");

    let mut image = manifest.encode().as_ref().to_vec();
    let entry = entry_of(manifest, table).0;
    let count = u64::from(tree.root().record_count()).to_le_bytes();
    image
        .get_mut(entry.saturating_add(8) ..)
        .and_then(|rest| rest.get_mut(.. 8))
        .expect("the record count")
        .copy_from_slice(&count);
    image
        .get_mut(entry.saturating_add(16) ..)
        .and_then(|rest| rest.get_mut(.. 32))
        .expect("the root node")
        .copy_from_slice(tree.root_node_hash().as_ref());
    StoreManifest::decode(ManifestImage::from(image.as_slice()))
        .expect("the doctored manifest decodes")
}

/// Where a table's 48-byte entry starts in a manifest image: the entries
/// close the image, in table order.
///
/// # Specification
/// trivial.
fn entry_of(
    manifest: &StoreManifest,
    table: Table,
) -> Offset
{
    let length = manifest.encode().as_ref().len();
    manifest
        .tables()
        .len()
        .checked_sub(table.0)
        .and_then(|after| after.checked_mul(48))
        .and_then(|tail| length.checked_sub(tail))
        .map(Offset)
        .expect("the table has an entry")
}

/// A byte offset into a manifest image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Offset(usize);

/// A table's position in the manifest, or a column's ordinal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Table(usize);

#[test]
fn the_keyed_schema_identity_is_pinned()
{
    let schema = keyed::schema().expect("the keyed schema presents");
    assert_eq!(schema.objects().len(), 6, "six tables");
    assert_eq!(schema.arrows().len(), 6, "six arrows");
    assert_eq!(schema.attributes().len(), 10, "ten attributes");
    assert_eq!(schema.equations().len(), 1, "one equation");
    assert_eq!(
        schema.identity().to_string(),
        "c41fca723d8f72d631faab68a9b243250a8a428cf8a3a0151a4e72e92a9ff5c5",
        "the identity a consumer pins"
    );
}

#[test]
fn a_naming_whose_task_disagrees_is_refused_by_equation()
{
    let Keyed {
        mut store,
        tasks: [alpha, beta],
        attempts: [first, ..],
        moves: [m0, ..],
        subjects: [digest, _],
        namings: [n0, n1, _],
        ..
    } = Keyed::new();
    let naming_task = arrow(&store, &Name("naming_task"));
    let attempt_task = arrow(&store, &Name("attempt_task"));
    let agrees = |part, left, right| Refusal::EquationViolated {
        equation: "naming_task_agrees".into(),
        object: "Naming".into(),
        part,
        left,
        right,
    };

    assert_eq!(
        store.set_arrow(naming_task, n0, beta),
        Err(agrees(n0, beta, alpha)),
        "a naming retargeted to another task"
    );
    assert_eq!(
        store.set_arrow(attempt_task, first, beta),
        Err(agrees(n0, alpha, beta)),
        "an attempt moved under the namings of its moves"
    );
    let row = Row::new()
        .arrow(arrow(&store, &Name("naming_move")), m0)
        .arrow(arrow(&store, &Name("naming_subject")), digest)
        .arrow(naming_task, beta)
        .value(
            attribute(&store, &Name("naming_role")),
            AttributeValue::from(&[0x01_u8][..]),
        );
    let refusal = store
        .add_part(object(&store, &Name("Naming")), &row)
        .expect_err("a new naming of the wrong task");
    assert!(
        matches!(refusal, Refusal::EquationViolated { ref equation, .. } if *equation == "naming_task_agrees".into()),
        "refused by the equation"
    );
    assert_eq!(store.target(naming_task, n1), Ok(alpha), "nothing moved");
    assert_eq!(store.audit(), Ok(()));
}

#[test]
fn the_fixture_round_trips_through_the_block_store()
{
    let Keyed {
        mut store,
        tasks: [alpha, beta],
        attempts: [first, ..],
        moves: [m0, m1, _, m3],
        refusal,
        subjects: [digest, _],
        namings: [n0, _, n2],
    } = Keyed::new();
    let mut blocks = InMemoryBlockStore::new();
    let root = store.commit(&mut blocks).expect("the fixture commits");
    let image = store.manifest().encode();
    let manifest = StoreManifest::decode(ManifestImage::from(image.as_ref()))
        .expect("the manifest round-trips");
    let schema = keyed::schema().expect("the keyed schema presents");
    let mut reopened =
        Store::open(schema.clone(), params(), &manifest, &blocks).expect("the fixture reopens");
    assert_eq!(reopened.root(), root, "one root");

    for table in schema.objects() {
        let parts = store.parts(table).expect("a table");
        let again = reopened.parts(table).expect("a table");
        assert!(parts.eq(again), "every table's parts: {table:?}");
    }
    for column in schema.arrows() {
        let spec = schema.arrow_at(column).expect("an arrow");
        for part in store.parts(spec.source()).expect("a table") {
            assert_eq!(
                reopened.target(column, part),
                store.target(column, part),
                "every arrow cell"
            );
        }
        for target in store.parts(spec.target()).expect("a table") {
            assert_eq!(
                reopened.preimage(column, target),
                store.preimage(column, target),
                "every inverse"
            );
        }
    }
    for column in schema.attributes() {
        let spec = schema.attribute_at(column).expect("an attribute");
        for part in store.parts(spec.object()).expect("a table") {
            let value = store.value(column, part).expect("a value");
            assert_eq!(
                reopened.value(column, part),
                Ok(value),
                "every attribute cell"
            );
            if spec.indexing() == Indexing::Indexed {
                assert_eq!(
                    reopened.value_preimage(column, value),
                    store.value_preimage(column, value),
                    "every value inverse"
                );
            }
        }
    }

    // The dialogue index: an attempt's moves, by sequence number.
    let move_attempt = arrow(&reopened, &Name("move_attempt"));
    let move_seq = attribute(&reopened, &Name("move_seq"));
    let receipt = attribute(&reopened, &Name("move_receipt"));
    let mut dialogue: Vec<(AttributeValue, AttributeValue)> = reopened
        .preimage(move_attempt, first)
        .expect("moves are indexed by attempt")
        .iter()
        .map(|&made| {
            (
                reopened
                    .value(move_seq, made)
                    .expect("a sequence number")
                    .clone(),
                reopened.value(receipt, made).expect("a receipt").clone(),
            )
        })
        .collect();
    dialogue.sort();
    let receipts: Vec<&[u8]> = dialogue.iter().map(|row| row.1.as_ref()).collect();
    assert_eq!(
        receipts,
        [&b"receipt a1/0"[..], &b"receipt a1/1"[..]],
        "the dialogue of alpha #1"
    );
    assert_eq!(reopened.preimage(move_attempt, first), Ok(&[m0, m1][..]));

    // The project index: a task by name, its standing and its refusals.
    let task_name = attribute(&reopened, &Name("task_name"));
    let task_standing = attribute(&reopened, &Name("task_standing"));
    let refusal_task = arrow(&reopened, &Name("refusal_task"));
    assert_eq!(
        reopened.value_preimage(task_name, &AttributeValue::from(&b"beta"[..])),
        Ok(&[beta][..])
    );
    assert_eq!(
        reopened.value(task_standing, beta).map(AsRef::as_ref),
        Ok(&Keyed::CLOSED[..]),
        "beta is closed"
    );
    assert_eq!(
        reopened.preimage(refusal_task, beta),
        Ok(&[refusal][..]),
        "beta's refusal"
    );
    assert_eq!(
        reopened.preimage(refusal_task, alpha),
        Ok(&[][..]),
        "alpha has none"
    );

    // The provenance index: who named a digest, in which task, attempt and role.
    let subject_digest = attribute(&reopened, &Name("subject_digest"));
    let naming_subject = arrow(&reopened, &Name("naming_subject"));
    let naming_move = arrow(&reopened, &Name("naming_move"));
    let naming_task = arrow(&reopened, &Name("naming_task"));
    assert_eq!(
        reopened.value_preimage(subject_digest, &AttributeValue::from(&Keyed::DIGEST[..])),
        Ok(&[digest][..])
    );
    assert_eq!(reopened.preimage(naming_subject, digest), Ok(&[n0, n2][..]));
    let provenance: Vec<(PartKey, PartKey, PartKey)> = [n0, n2]
        .iter()
        .map(|&naming| {
            let made = reopened.target(naming_move, naming).expect("a move");
            (
                reopened.target(naming_task, naming).expect("a task"),
                reopened.target(move_attempt, made).expect("an attempt"),
                made,
            )
        })
        .collect();
    assert_eq!(provenance.first().map(|row| row.2), Some(m0));
    assert_eq!(provenance.last().map(|row| row.2), Some(m3));
    assert_eq!(provenance.first().map(|row| row.0), Some(alpha));
    assert_eq!(provenance.last().map(|row| row.0), Some(beta));

    // The reopened counter continues, and an unchanged store recommits to its root.
    let again = reopened
        .commit(&mut blocks)
        .expect("an unchanged store recommits");
    assert_eq!(again, root, "the root is a function of the store");
    let task = object(&reopened, &Name("Task"));
    let mut edit = reopened.edit();
    let next = edit.add_part(task).expect("a task is minted");
    edit.abandon();
    assert_eq!(
        next,
        PartKey::from(2_u64),
        "the third task's key, never a reused one"
    );
}

#[test]
fn a_doctored_table_is_refused_on_reopening()
{
    let Keyed {
        mut store,
        tasks: [_, beta],
        namings: [n0, ..],
        ..
    } = Keyed::new();
    let mut blocks = InMemoryBlockStore::new();
    store.commit(&mut blocks).expect("the fixture commits");
    let manifest = store.manifest().clone();
    let schema = keyed::schema().expect("the keyed schema presents");
    let naming = object(&store, &Name("Naming"));
    let table = Table(usize::from(naming));
    let original = records_of(
        &blocks,
        manifest
            .tables()
            .get(table.0)
            .expect("the Naming table")
            .root_node(),
    );
    let reopen = |manifest: &StoreManifest, blocks: &InMemoryBlockStore| {
        Store::open(schema.clone(), params(), manifest, blocks).err()
    };
    let be4 = |value: Table| {
        let mut bytes = u32::try_from(value.0).expect("fits a u32").to_le_bytes();
        bytes.reverse();
        bytes
    };
    let be8 = |part: PartKey| {
        let mut bytes = u64::from(part).to_le_bytes();
        bytes.reverse();
        bytes
    };

    // An arrow cell and its inverse entry, rewritten together so the table
    // stays canonical.
    let retarget = |records: &mut Vec<Record>, column: Table, from: PartKey, to: PartKey| {
        let cell: Vec<u8> = [&[0x01_u8][..], &be4(column), &be8(n0)].concat();
        let entry: Vec<u8> = [&[0x03_u8][..], &be4(column), &be8(from), &be8(n0)].concat();
        records.retain(|record| {
            record.key().as_ref() != cell.as_slice() && record.key().as_ref() != entry.as_slice()
        });
        records.push(Record::new(cell, Vec::from(u64::from(to).to_le_bytes())));
        records.push(Record::new(
            [&[0x03_u8][..], &be4(column), &be8(to), &be8(n0)].concat(),
            Vec::new(),
        ));
    };

    let naming_task = Table(usize::from(arrow(&store, &Name("naming_task"))));
    let alpha = store
        .target(arrow(&store, &Name("naming_task")), n0)
        .expect("n0's task");
    let mut records = original.clone();
    retarget(&mut records, naming_task, alpha, beta);
    let bent = doctored(&manifest, table, &mut records, &mut blocks);
    assert!(
        matches!(
            reopen(&bent, &blocks),
            Some(StoreError::Refused(Refusal::EquationViolated { ref equation, part, .. }))
                if *equation == "naming_task_agrees".into() && part == n0
        ),
        "a naming of the wrong task"
    );

    let naming_subject = Table(usize::from(arrow(&store, &Name("naming_subject"))));
    let subject = store
        .target(arrow(&store, &Name("naming_subject")), n0)
        .expect("n0's subject");
    let ghost = PartKey::from(9_u64);
    let mut records = original.clone();
    retarget(&mut records, naming_subject, subject, ghost);
    let dangling = doctored(&manifest, table, &mut records, &mut blocks);
    assert_eq!(
        reopen(&dangling, &blocks),
        Some(StoreError::Refused(Refusal::NotLive {
            object: "Subject".into(),
            part: ghost,
        })),
        "a naming of a subject that is not live"
    );

    let mut records = original.clone();
    records.push(Record::new(vec![0x09_u8], Vec::new()));
    let foreign = doctored(&manifest, table, &mut records, &mut blocks);
    let refusal = reopen(&foreign, &blocks);
    assert_eq!(
        refusal,
        Some(StoreError::Layout {
            object: "Naming".into(),
            fault: LayoutFault::Family,
        }),
        "a record of no family"
    );
    assert_eq!(
        refusal.map(|error| error.to_string()).as_deref(),
        Some("table `Naming`: a key opens with no family of the layout")
    );

    let role = Table(usize::from(attribute(&store, &Name("naming_role"))));
    let cell: Vec<u8> = [&[0x02_u8][..], &be4(role), &be8(n0)].concat();
    let mut records = original.clone();
    records.retain(|record| record.key().as_ref() != cell.as_slice());
    let incomplete = doctored(&manifest, table, &mut records, &mut blocks);
    assert_eq!(
        reopen(&incomplete, &blocks),
        Some(StoreError::Layout {
            object: "Naming".into(),
            fault: LayoutFault::NotCanonical,
        }),
        "a naming without its role"
    );

    let mut records = original;
    let recounted = doctored(&manifest, table, &mut records, &mut blocks);
    let mut image = recounted.encode().as_ref().to_vec();
    let at = entry_of(&recounted, table).0.saturating_add(8);
    if let Some(byte) = image.get_mut(at) {
        *byte = byte.wrapping_add(1);
    }
    let miscounted = StoreManifest::decode(ManifestImage::from(image.as_slice()))
        .expect("a miscounted manifest decodes");
    assert_eq!(
        reopen(&miscounted, &blocks),
        Some(StoreError::Layout {
            object: "Naming".into(),
            fault: LayoutFault::Root,
        }),
        "a record count the tree does not have"
    );

    assert!(
        matches!(
            reopen(&manifest, &InMemoryBlockStore::new()),
            Some(StoreError::Records(_))
        ),
        "a block store that holds no table"
    );
    assert!(
        reopen(&manifest, &blocks).is_none(),
        "the honest manifest still reopens"
    );
}

#[test]
fn a_standing_moves_between_inverses()
{
    let Keyed {
        mut store,
        tasks: [alpha, beta],
        ..
    } = Keyed::new();
    let standing = attribute(&store, &Name("task_standing"));
    let heads = attribute(&store, &Name("task_heads"));
    let open = AttributeValue::from(&Keyed::OPEN[..]);
    let closed = AttributeValue::from(&Keyed::CLOSED[..]);

    assert_eq!(store.value_preimage(standing, &open), Ok(&[alpha][..]));
    assert_eq!(store.value_preimage(standing, &closed), Ok(&[beta][..]));
    store
        .set_value(standing, alpha, closed.clone())
        .expect("alpha closes");
    assert_eq!(
        store.value_preimage(standing, &open),
        Ok(&[][..]),
        "no task is open"
    );
    assert_eq!(
        store.value_preimage(standing, &closed),
        Ok(&[alpha, beta][..]),
        "both are closed"
    );
    assert_eq!(
        store.value_preimage(heads, &open),
        Err(Refusal::NotIndexed {
            field: "task_heads".into(),
        }),
        "heads keep no inverse"
    );
}
