//! Version-one cross-implementation vectors for the record plane.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the test reads JSON primitives at the external vector boundary"
    )
)]

use core::fmt::Write as _;

use gandr_storage_records::BoundaryMaskBits;
use gandr_storage_records::BoundaryParams;
use gandr_storage_records::BoundaryProfile;
use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::DecodedNode;
use gandr_storage_records::Record;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use serde_json::Value as JsonValue;
use serde_json::json;

/// # Specification
///
/// trivial.
fn document() -> JsonValue
{
    serde_json::from_str(include_str!("vectors/v1.json")).expect("the v1 record vectors parse")
}

/// # Specification
///
/// trivial.
fn field<'value>(
    value: &'value JsonValue,
    name: &str,
) -> &'value JsonValue
{
    value
        .get(name)
        .unwrap_or_else(|| panic!("the vector has {name}"))
}
/// # Specification
///
/// trivial.
fn array<'value>(
    value: &'value JsonValue,
    name: &str,
) -> &'value [JsonValue]
{
    field(value, name)
        .as_array()
        .unwrap_or_else(|| panic!("the vector field {name} is an array"))
}

/// # Specification
///
/// trivial.
fn number(
    value: &JsonValue,
    name: &str,
) -> u64
{
    field(value, name)
        .as_u64()
        .unwrap_or_else(|| panic!("the vector field {name} is an unsigned number"))
}

/// # Specification
///
/// trivial.
fn text<'value>(
    value: &'value JsonValue,
    name: &str,
) -> &'value str
{
    field(value, name)
        .as_str()
        .unwrap_or_else(|| panic!("the vector field {name} is text"))
}

/// # Specification
///
/// trivial.
fn hex(bytes: &[u8]) -> String
{
    let capacity = bytes
        .len()
        .checked_mul(2_usize)
        .expect("the hex output capacity fits");
    let mut text = String::with_capacity(capacity);
    for byte in bytes {
        write!(&mut text, "{byte:02x}").expect("writing into a string succeeds");
    }
    text
}

/// # Specification
///
/// trivial.
fn byte(nibble: u8) -> u8
{
    match nibble {
        b'0' => 0_u8,
        b'1' => 1_u8,
        b'2' => 2_u8,
        b'3' => 3_u8,
        b'4' => 4_u8,
        b'5' => 5_u8,
        b'6' => 6_u8,
        b'7' => 7_u8,
        b'8' => 8_u8,
        b'9' => 9_u8,
        b'a' | b'A' => 10_u8,
        b'b' | b'B' => 11_u8,
        b'c' | b'C' => 12_u8,
        b'd' | b'D' => 13_u8,
        b'e' | b'E' => 14_u8,
        b'f' | b'F' => 15_u8,
        _ => panic!("the vector byte is hexadecimal"),
    }
}

/// # Specification
///
/// trivial.
fn bytes(text: &str) -> Vec<u8>
{
    let (pairs, rest) = text.as_bytes().as_chunks::<2_usize>();
    assert!(rest.is_empty(), "the vector hex has byte pairs");
    pairs
        .iter()
        .map(|pair| {
            let [high, low] = *pair;
            (byte(high) << 4_u8) | byte(low)
        })
        .collect()
}

/// # Specification
///
/// trivial.
fn generated_records(
    seed: u64,
    count: usize,
) -> Vec<Record>
{
    let mut state = seed;

    (0_usize .. count)
        .map(|index| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005_u64)
                .wrapping_add(1_u64);
            Record::new(
                format!("key-{index:08}").into_bytes(),
                format!("value-{state:016x}").into_bytes(),
            )
        })
        .collect()
}

/// # Specification
///
/// trivial.
fn records(vector: &JsonValue) -> Vec<Record>
{
    let input = field(vector, "input");
    match text(input, "kind") {
        "literal-v1" => array(input, "records")
            .iter()
            .map(|record| Record::new(bytes(text(record, "key")), bytes(text(record, "value"))))
            .collect(),
        "counter-v1" => generated_records(
            number(input, "seed"),
            usize::try_from(number(input, "count")).expect("the count fits in usize"),
        ),
        kind => panic!("the v1 record vector kind {kind} is unknown"),
    }
}

/// # Specification
///
/// trivial.
fn profile(vector: &JsonValue) -> TreeParams
{
    let description = field(vector, "profile");
    let mask_bits = u8::try_from(number(description, "mask_bits")).expect("the mask fits in u8");
    let kappa = 1_u64
        .checked_shl(u32::from(mask_bits))
        .expect("the mask gives a kappa");
    assert_eq!(
        number(description, "kappa"),
        kappa,
        "the vector kappa matches its mask"
    );
    let cap = u32::try_from(number(description, "cap")).expect("the cap fits in u32");
    let current = TreeParams::current();

    TreeParams::new(
        current.kind(),
        current.encoding_version(),
        current.hash_algorithm(),
        current.separator_convention(),
        BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::try_from(mask_bits).expect("the mask is supported"),
            BoundaryRecordCap::try_from(cap).expect("the cap is nonzero"),
        ),
    )
}

/// # Specification
///
/// trivial.
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "each JSON vector entry owns its digest text"
    )
)]
fn observe(vector: &JsonValue) -> JsonValue
{
    let records = records(vector);
    let input: Vec<_> = records.iter().map(Record::as_record_ref).collect();
    let profile = profile(vector);
    let tree = RecordTree::build(input.as_slice(), profile).expect("the vector records build");
    let mut end = 0_usize;
    let mut cuts = Vec::new();
    let nodes: Vec<JsonValue> = tree
        .nodes()
        .iter()
        .map(|node| {
            let bytes: &[u8] = node.bytes().into();
            if let DecodedNode::Leaf(leaf) =
                gandr_storage_records::decode_node(node.bytes(), &mut DecodeWork::new())
                    .expect("the vector node decodes")
            {
                end = end
                    .checked_add(leaf.records().len())
                    .expect("the vector cut index fits");
                cuts.push(end);
            }
            json!({
                "digest": node.identity().to_string(),
                "bytes": hex(bytes),
            })
        })
        .collect();
    let _final = cuts.pop();

    json!({
        "name": text(vector, "name"),
        "input": field(vector, "input"),
        "profile": {
            "mask_bits": u8::from(profile.boundary().mask_bits()),
            "kappa": 1_u64 << u8::from(profile.boundary().mask_bits()),
            "cap": u32::from(profile.boundary().record_cap()),
        },
        "cuts": cuts,
        "nodes": nodes,
        "root": {
            "node": tree.root_node_hash().to_string(),
            "manifest": tree.root().identity().to_string(),
            "records": u64::from(tree.root().record_count()),
        },
    })
}

/// #3168 keeps the record vectors as an external storage contract.
#[test]
fn v1_storage_vectors_3168_are_reproduced()
{
    let expected = document();
    let vectors = array(&expected, "vectors");
    let actual = json!({
        "version": 1_u8,
        "vectors": vectors.iter().map(observe).collect::<Vec<_>>(),
    });

    assert_eq!(
        actual, expected,
        "the v1 record vectors are reproduced exactly"
    );
}
