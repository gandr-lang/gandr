//! Every refusal renders what it carries, and no two render alike.

use core::fmt::Display;
use core::fmt::Write as _;

use gandr_storage_records::NodeHash;
use gandr_storage_records::RecordTreeError;
use gandr_storage_schema::ElementKind;
use gandr_storage_schema::ImageFault;
use gandr_storage_schema::LayoutFault;
use gandr_storage_schema::ManifestFault;
use gandr_storage_schema::MapError;
use gandr_storage_schema::Name;
use gandr_storage_schema::Ordinal;
use gandr_storage_schema::PartKey;
use gandr_storage_schema::Refusal;
use gandr_storage_schema::SchemaError;
use gandr_storage_schema::SchemaIdentity;
use gandr_storage_schema::StoreError;
use gandr_storage_schema::StoreRoot;

/// Asserts that no two renderings are equal.
///
/// # Specification
/// trivial.
fn assert_distinct(rendered: &[&dyn Display])
{
    let mut sorted: Vec<String> = rendered.iter().map(ToString::to_string).collect();
    let count = sorted.len();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), count, "{sorted:?}");
}

/// Asserts that the rendering of `refusal` carries the rendering of every
/// one of `parts`.
///
/// # Specification
/// trivial.
fn assert_names(
    refusal: &dyn Display,
    parts: &[&dyn Display],
)
{
    let rendered = refusal.to_string();
    let mut part = String::new();
    for each in parts {
        part.clear();
        write!(part, "{each}").expect("a string takes the rendering");
        assert!(
            rendered.contains(part.as_str()),
            "`{rendered}` does not name `{part}`"
        );
    }
}

#[test]
fn every_schema_refusal_names_its_elements()
{
    let kinds = [
        ElementKind::Object,
        ElementKind::AttributeType,
        ElementKind::Arrow,
        ElementKind::Attribute,
        ElementKind::Equation,
    ];
    assert_distinct(&kinds.each_ref().map(|kind| -> &dyn Display { kind }));
    for kind in kinds {
        let unknown = SchemaError::Unknown {
            kind,
            name: Name::from("ghost"),
        };
        assert_names(&unknown, &[&kind, &"ghost"]);
    }

    let empty = SchemaError::EmptyName;
    let twice = SchemaError::DuplicateName {
        name: Name::from("twice"),
    };
    let unknown = SchemaError::Unknown {
        kind: ElementKind::Arrow,
        name: Name::from("ghost"),
    };
    let ordinal = SchemaError::UnknownOrdinal {
        kind: ElementKind::Object,
        ordinal: Ordinal(7),
    };
    let not_composable = SchemaError::NotComposable {
        equation: Name::from("square"),
        arrow: Name::from("src"),
        at: Name::from("Vertex"),
    };
    let apart = SchemaError::EndpointsDiffer {
        equation: Name::from("square"),
        left: Name::from("Edge"),
        right: Name::from("Vertex"),
    };
    let too_large = SchemaError::TooLarge {
        kind: ElementKind::Attribute,
    };
    let image = SchemaError::Image {
        fault: ImageFault::Trailing,
    };
    assert_names(&twice, &[&"twice"]);
    assert_names(&ordinal, &[&ElementKind::Object, &7_usize]);
    assert_names(&not_composable, &[&"square", &"src", &"Vertex"]);
    assert_names(&apart, &[&"square", &"Edge", &"Vertex"]);
    assert_names(&too_large, &[&ElementKind::Attribute]);
    assert_names(&image, &[&ImageFault::Trailing]);
    assert_distinct(&[
        &empty,
        &twice,
        &unknown,
        &ordinal,
        &not_composable,
        &apart,
        &too_large,
        &image,
    ]);
}

#[test]
fn every_map_refusal_names_its_elements()
{
    let lookup = SchemaError::DuplicateName {
        name: Name::from("twice"),
    };
    let carried = MapError::from(lookup.clone());
    assert_eq!(MapError::Schema(lookup.clone()), carried);
    assert_names(&carried, &[&lookup]);

    let unmapped = MapError::Unmapped {
        kind: ElementKind::Equation,
        name: Name::from("square"),
    };
    let not_composable = MapError::NotComposable {
        element: Name::from("edge"),
        arrow: Name::from("tgt"),
        at: Name::from("Vertex"),
    };
    let wrong_end = MapError::WrongEnd {
        element: Name::from("edge"),
        expected: Name::from("Vertex"),
        found: Name::from("Edge"),
    };
    let attribute_type = MapError::AttributeType {
        attribute: Name::from("label"),
        expected: Name::from("Text"),
        found: Name::from("Bytes"),
    };
    let not_preserved = MapError::EquationNotPreserved {
        equation: Name::from("square"),
    };
    assert_names(&unmapped, &[&ElementKind::Equation, &"square"]);
    assert_names(&not_composable, &[&"edge", &"tgt", &"Vertex"]);
    assert_names(&wrong_end, &[&"edge", &"Vertex", &"Edge"]);
    assert_names(&attribute_type, &[&"label", &"Text", &"Bytes"]);
    assert_names(&not_preserved, &[&"square"]);
    assert_distinct(&[
        &carried,
        &unmapped,
        &not_composable,
        &wrong_end,
        &attribute_type,
        &not_preserved,
    ]);
}

#[test]
fn every_edit_refusal_names_its_parts()
{
    let lookup = SchemaError::Unknown {
        kind: ElementKind::Object,
        name: Name::from("ghost"),
    };
    let carried = Refusal::from(lookup.clone());
    assert_eq!(Refusal::Schema(lookup.clone()), carried);
    assert_eq!(lookup.to_string(), carried.to_string());

    let [eleven, twenty_three, thirty_seven] = [11_u64, 23_u64, 37_u64].map(PartKey::from);
    let not_live = Refusal::NotLive {
        object: Name::from("Vertex"),
        part: eleven,
    };
    let referenced = Refusal::Referenced {
        object: Name::from("Vertex"),
        part: eleven,
        arrow: Name::from("src"),
        by: twenty_three,
    };
    let unset = Refusal::Unset {
        field: Name::from("label"),
        object: Name::from("Vertex"),
        part: eleven,
    };
    let violated = Refusal::EquationViolated {
        equation: Name::from("square"),
        object: Name::from("Edge"),
        part: eleven,
        left: twenty_three,
        right: thirty_seven,
    };
    let not_indexed = Refusal::NotIndexed {
        field: Name::from("tgt"),
    };
    let foreign = Refusal::ForeignField {
        field: Name::from("tgt"),
        object: Name::from("Vertex"),
    };
    let exhausted = Refusal::Exhausted {
        object: Name::from("Edge"),
    };
    assert_names(&not_live, &[&"Vertex", &eleven]);
    assert_names(&referenced, &[&"Vertex", &eleven, &"src", &twenty_three]);
    assert_names(&unset, &[&"label", &"Vertex", &eleven]);
    assert_names(&violated, &[
        &"square",
        &"Edge",
        &eleven,
        &twenty_three,
        &thirty_seven,
    ]);
    assert_names(&not_indexed, &[&"tgt"]);
    assert_names(&foreign, &[&"tgt", &"Vertex"]);
    assert_names(&exhausted, &[&"Edge"]);
    assert_distinct(&[
        &carried,
        &not_live,
        &referenced,
        &unset,
        &violated,
        &not_indexed,
        &foreign,
        &exhausted,
    ]);
}

#[test]
fn every_store_refusal_names_what_it_compared()
{
    let layout = [
        LayoutFault::Family,
        LayoutFault::Width,
        LayoutFault::Column,
        LayoutFault::Counter,
        LayoutFault::Root,
        LayoutFault::NotCanonical,
    ];
    assert_distinct(&layout.each_ref().map(|fault| -> &dyn Display { fault }));
    let manifest = [
        ManifestFault::Domain,
        ManifestFault::Version,
        ManifestFault::Truncated,
        ManifestFault::Trailing,
    ];
    assert_distinct(&manifest.each_ref().map(|fault| -> &dyn Display { fault }));

    let records = RecordTreeError::UnknownNode {
        hash: NodeHash::from([0x5a_u8; 32]),
    };
    let refusal = Refusal::Exhausted {
        object: Name::from("Edge"),
    };
    let lookup = SchemaError::EmptyName;
    assert_eq!(
        StoreError::Records(records.clone()),
        StoreError::from(records.clone())
    );
    assert_eq!(
        StoreError::Refused(refusal.clone()),
        StoreError::from(refusal.clone())
    );
    assert_eq!(
        StoreError::Refused(Refusal::Schema(lookup.clone())),
        StoreError::from(lookup)
    );

    let held = SchemaIdentity::from([0xab_u8; 32]);
    let committed = SchemaIdentity::from([0xcd_u8; 32]);
    let verifier = StoreRoot::from([0x12_u8; 32]);
    let hashed = StoreRoot::from([0x34_u8; 32]);
    let carried_records = StoreError::Records(records.clone());
    let carried_refusal = StoreError::Refused(refusal.clone());
    let schema_mismatch = StoreError::SchemaMismatch {
        expected: held,
        found: committed,
    };
    let profile_mismatch = StoreError::ProfileMismatch;
    let table_count = StoreError::TableCount;
    let malformed = StoreError::Manifest {
        fault: ManifestFault::Truncated,
    };
    let root_mismatch = StoreError::RootMismatch {
        expected: verifier,
        found: hashed,
    };
    let doctored = StoreError::Layout {
        object: Name::from("Vertex"),
        fault: LayoutFault::Counter,
    };
    let wrong_question = StoreError::WrongQuestion;
    assert_eq!(records.to_string(), carried_records.to_string());
    assert_eq!(refusal.to_string(), carried_refusal.to_string());
    assert_names(&schema_mismatch, &[&held, &committed]);
    assert_names(&malformed, &[&ManifestFault::Truncated]);
    assert_names(&root_mismatch, &[&verifier, &hashed]);
    assert_names(&doctored, &[&"Vertex", &LayoutFault::Counter]);
    assert_distinct(&[
        &carried_records,
        &carried_refusal,
        &schema_mismatch,
        &profile_mismatch,
        &table_count,
        &malformed,
        &root_mismatch,
        &doctored,
        &wrong_question,
    ]);
}
