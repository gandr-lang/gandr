//! Version-one cross-implementation vectors for the value plane.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the test reads JSON primitives at the external vector boundary"
    )
)]

use core::fmt::Write as _;

use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::BoundaryClassification;
use gandr_storage_values::BoundaryTags;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use gandr_storage_values::encode_flat;
use serde_json::Value as JsonValue;
use serde_json::json;

use crate::common::Depth;
use crate::common::Scanned;
use crate::common::Script;
use crate::common::Seed;
use crate::common::Step;
use crate::common::balanced;
use crate::common::scan;
use crate::reference::Ledger;
use crate::reference::RecordIndex;
use crate::reference::reference_cuts;

/// # Specification
///
/// trivial.
fn document() -> JsonValue
{
    serde_json::from_str(include_str!("vectors/v1.json")).expect("the v1 value vectors parse")
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
fn pointer(pointer: ContentPtr) -> JsonValue
{
    json!({
        "digest": pointer.digest().to_string(),
        "offset": u32::from(pointer.offset()),
    })
}

/// # Specification
///
/// trivial.
fn profile(vector: &JsonValue) -> ValueProfile
{
    let description = field(vector, "profile");
    let tags = array(description, "boundary_tags")
        .iter()
        .fold(BoundaryTags::EMPTY, |tags, tag| {
            tags.with(ConstructorTag::from(
                u8::try_from(tag.as_u64().expect("a boundary tag is an unsigned number"))
                    .expect("a boundary tag fits in one byte"),
            ))
        });
    let params = TypedChunkerParams::new(
        Kappa::try_from(number(description, "kappa")).expect("kappa is nonzero"),
        TokenCap::try_from(number(description, "cap")).expect("the cap is nonzero"),
    );
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));

    ValueProfile::new(params, codec, ChildIndexBase::Absolute)
        .classified(BoundaryClassification::Tagged(tags))
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
fn observe_value<Value>(
    vector: &JsonValue,
    value: &Value,
) -> JsonValue
where
    Value: gandr_storage_values::CanonicalValue,
{
    let profile = profile(vector);
    let flat = encode_flat(value).expect("the vector value encodes flat");
    let mut store = Ledger::default();
    let manifest = cam_commit(&mut store, &profile, value).expect("the vector value commits");
    let cuts: Vec<usize> = reference_cuts(
        flat.as_body(),
        &profile.params(),
        profile.boundary_classification(),
    )
    .into_iter()
    .map(|RecordIndex(index)| index)
    .collect();
    let chunks: Vec<JsonValue> = store
        .held()
        .iter()
        .map(|digest| {
            let chunk = store.load(*digest).expect("the committed chunk is held");
            let image: &[u8] = chunk.image().into();
            json!({
                "digest": digest.to_string(),
                "bytes": hex(image),
            })
        })
        .collect();
    let mut pointers = vec![manifest.root()];
    for digest in store.held() {
        let chunk = store.load(*digest).expect("the committed chunk is held");
        pointers.extend(
            scan(chunk.body())
                .into_iter()
                .filter_map(|record| match record {
                    Scanned::Child(pointer) => Some(pointer),
                    Scanned::Open | Scanned::Other => None,
                }),
        );
    }
    pointers.sort();
    pointers.dedup();

    json!({
        "name": text(vector, "name"),
        "input": field(vector, "input"),
        "profile": {
            "kappa": u64::from(profile.params().kappa()),
            "cap": u64::from(profile.params().cap()),
            "boundary_tags": array(field(vector, "profile"), "boundary_tags"),
        },
        "tokens": hex(flat.as_body().as_ref()),
        "cuts": cuts,
        "chunks": chunks,
        "pointers": pointers.into_iter().map(pointer).collect::<Vec<_>>(),
        "manifest": {
            "bytes": hex(manifest.encode().as_ref()),
            "digest": manifest.identity().to_string(),
            "root": pointer(manifest.root()),
            "tokens": u64::from(manifest.token_count()),
        },
    })
}

/// # Specification
///
/// trivial.
fn observe(vector: &JsonValue) -> JsonValue
{
    match text(field(vector, "input"), "kind") {
        "leaf-zero-v1" => observe_value(vector, &Script(vec![Step::Open, Step::Word, Step::Close])),
        "balanced-v1" => observe_value(
            vector,
            &balanced(
                Depth(
                    u32::try_from(number(field(vector, "input"), "depth"))
                        .expect("the depth fits in u32"),
                ),
                Seed(number(field(vector, "input"), "seed")),
            ),
        ),
        kind => panic!("the v1 value vector kind {kind} is unknown"),
    }
}

/// #3168 keeps the value vectors as an external storage contract.
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
        "the v1 value vectors are reproduced exactly"
    );
}
