//! Schemas as values: canonical images, identities and named refusals.

use gandr_storage_schema::ElementKind;
use gandr_storage_schema::ImageFault;
use gandr_storage_schema::Indexing;
use gandr_storage_schema::Ordinal;
use gandr_storage_schema::Presentation;
use gandr_storage_schema::SCHEMA_DOMAIN;
use gandr_storage_schema::Schema;
use gandr_storage_schema::SchemaError;
use gandr_storage_schema::SchemaImage;
use gandr_storage_schema::keyed;

use crate::common::graph;
use crate::common::graph_presentation;
use crate::common::reflexive;

/// The golden schema: two objects, both indexings, an attribute and an
/// equation.
///
/// # Specification
/// trivial.
fn golden_presentation() -> Presentation
{
    Presentation::new()
        .object("V")
        .object("E")
        .attribute_type("Text")
        .arrow("tgt", "E", "V", Indexing::Unindexed)
        .arrow("src", "E", "V", Indexing::Indexed)
        .attribute("label", "V", "Text", Indexing::Unindexed)
        .equation("loop", "E", ["src"], ["tgt"])
}

/// The golden schema's image, written out field by field.
///
/// # Specification
/// trivial.
fn golden_image() -> Golden
{
    let mut image = Vec::from(SCHEMA_DOMAIN);
    // Objects, sorted: E = 0, V = 1.
    image.extend_from_slice(&[2, 0, 0, 0]);
    image.extend_from_slice(&[1, 0, 0, 0, b'E']);
    image.extend_from_slice(&[1, 0, 0, 0, b'V']);
    // Attribute types.
    image.extend_from_slice(&[1, 0, 0, 0]);
    image.extend_from_slice(&[4, 0, 0, 0, b'T', b'e', b'x', b't']);
    // Arrows, sorted: src = 0, tgt = 1.
    image.extend_from_slice(&[2, 0, 0, 0]);
    image.extend_from_slice(&[3, 0, 0, 0, b's', b'r', b'c', 0, 0, 0, 0, 1, 0, 0, 0, 0x01]);
    image.extend_from_slice(&[3, 0, 0, 0, b't', b'g', b't', 0, 0, 0, 0, 1, 0, 0, 0, 0x00]);
    // Attributes.
    image.extend_from_slice(&[1, 0, 0, 0]);
    image.extend_from_slice(&[
        5, 0, 0, 0, b'l', b'a', b'b', b'e', b'l', 1, 0, 0, 0, 0, 0, 0, 0, 0x00,
    ]);
    // Equations.
    image.extend_from_slice(&[1, 0, 0, 0]);
    image.extend_from_slice(&[4, 0, 0, 0, b'l', b'o', b'o', b'p', 0, 0, 0, 0]);
    image.extend_from_slice(&[1, 0, 0, 0, 0, 0, 0, 0]);
    image.extend_from_slice(&[1, 0, 0, 0, 1, 0, 0, 0]);
    Golden(image)
}

/// The golden schema image's bytes.
#[repr(transparent)]
struct Golden(Vec<u8>);

#[test]
fn presentation_order_does_not_change_the_identity()
{
    let reversed = Presentation::new()
        .attribute("label", "V", "Text", Indexing::Unindexed)
        .arrow("tgt", "E", "V", Indexing::Unindexed)
        .arrow("src", "E", "V", Indexing::Indexed)
        .attribute_type("Text")
        .object("E")
        .object("V");
    let forward = graph();
    let backward = Schema::present(&reversed).expect("the reversed presentation presents");
    assert_eq!(forward.encode(), backward.encode(), "one image");
    assert_eq!(forward.identity(), backward.identity(), "one identity");

    let reindexed = graph_presentation().arrow("other", "E", "V", Indexing::Indexed);
    let other = Schema::present(&reindexed).expect("a third arrow presents");
    assert_ne!(
        other.identity(),
        forward.identity(),
        "another arrow is another schema"
    );
}

#[test]
fn a_duplicate_name_is_refused()
{
    let clash = graph_presentation().object("src");
    assert_eq!(
        Schema::present(&clash),
        Err(SchemaError::DuplicateName { name: "src".into() }),
        "an object may not share an arrow's name"
    );
    let empty = graph_presentation().object("");
    assert_eq!(
        Schema::present(&empty),
        Err(SchemaError::EmptyName),
        "the empty name"
    );
}

#[test]
fn an_unknown_object_is_refused_by_name()
{
    let dangling = graph_presentation().arrow("out", "E", "W", Indexing::Unindexed);
    let refusal = Schema::present(&dangling).expect_err("`W` is not an object");
    assert_eq!(refusal, SchemaError::Unknown {
        kind: ElementKind::Object,
        name: "W".into(),
    });
    assert_eq!(refusal.to_string(), "no object is named `W`");
}

#[test]
fn a_path_that_does_not_compose_is_refused_by_name()
{
    let identity: [&str; 0] = [];
    let bad = graph_presentation().equation("bad", "V", ["tgt"], identity);
    let refusal = Schema::present(&bad).expect_err("`tgt` does not leave `V`");
    assert_eq!(refusal, SchemaError::NotComposable {
        equation: "bad".into(),
        arrow: "tgt".into(),
        at: "V".into(),
    });
    assert_eq!(
        refusal.to_string(),
        "equation `bad`: arrow `tgt` does not leave `V`, where its path is"
    );

    let bad_right = graph_presentation().equation("bad_right", "V", identity, ["src"]);
    assert_eq!(
        Schema::present(&bad_right),
        Err(SchemaError::NotComposable {
            equation: "bad_right".into(),
            arrow: "src".into(),
            at: "V".into(),
        }),
        "the right side is resolved as the left is"
    );
}

#[test]
fn equation_sides_must_meet()
{
    let identity: [&str; 0] = [];
    let apart = graph_presentation().equation("apart", "E", ["src"], identity);
    assert_eq!(
        Schema::present(&apart),
        Err(SchemaError::EndpointsDiffer {
            equation: "apart".into(),
            left: "V".into(),
            right: "E".into(),
        })
    );
}

#[test]
fn the_image_is_golden()
{
    let schema = Schema::present(&golden_presentation()).expect("the golden presents");
    let image = golden_image().0;
    assert_eq!(
        schema.encode().as_ref(),
        image.as_slice(),
        "the layout is the golden"
    );
    assert_eq!(
        schema.identity().as_ref(),
        blake3::hash(&image).as_bytes(),
        "the identity is BLAKE3 of the image"
    );
}

#[test]
fn an_image_round_trips_and_malformed_ones_are_refused()
{
    let schema = Schema::present(&golden_presentation()).expect("the golden presents");
    let image = golden_image().0;
    let decode = |bytes: &[u8]| Schema::decode(SchemaImage::from(bytes));
    let fault = |fault| Err(SchemaError::Image { fault });

    assert_eq!(decode(&image), Ok(schema), "the golden round-trips");

    let mut domain = image.clone();
    let last = SCHEMA_DOMAIN.len().saturating_sub(1);
    if let Some(byte) = domain.get_mut(last) {
        *byte = b'2';
    }
    assert_eq!(decode(&domain), fault(ImageFault::Domain), "the domain");

    for length in SCHEMA_DOMAIN.len() .. image.len() {
        assert_eq!(
            decode(image.get(.. length).expect("a prefix")),
            fault(ImageFault::Truncated),
            "the prefix of {length} bytes"
        );
    }

    let mut trailing = image.clone();
    trailing.push(0);
    assert_eq!(
        decode(&trailing),
        fault(ImageFault::Trailing),
        "a trailing byte"
    );

    // The object name `E` sits after the domain, the count and its length.
    let name_at = SCHEMA_DOMAIN.len().saturating_add(8);
    let mut utf8 = image.clone();
    if let Some(byte) = utf8.get_mut(name_at) {
        *byte = 0xff;
    }
    assert_eq!(
        decode(&utf8),
        fault(ImageFault::NotUtf8),
        "a name that is not UTF-8"
    );

    let src_at = image
        .windows(3)
        .position(|window| window == b"src")
        .expect("the arrow `src`");
    let mut tag = image.clone();
    if let Some(byte) = tag.get_mut(src_at.saturating_add(11)) {
        *byte = 0x02;
    }
    assert_eq!(
        decode(&tag),
        fault(ImageFault::IndexingTag),
        "an indexing byte of 0x02"
    );

    let mut ordinal = image.clone();
    if let Some(byte) = ordinal.get_mut(src_at.saturating_add(7)) {
        *byte = 2;
    }
    assert_eq!(
        decode(&ordinal),
        fault(ImageFault::Ordinal),
        "object ordinal two of two"
    );

    let mut reordered = image;
    if let (Some(&first), Some(&second)) = (
        reordered.get(name_at),
        reordered.get(name_at.saturating_add(5)),
    ) {
        if let Some(byte) = reordered.get_mut(name_at) {
            *byte = second;
        }
        if let Some(byte) = reordered.get_mut(name_at.saturating_add(5)) {
            *byte = first;
        }
    }
    assert_eq!(
        decode(&reordered),
        fault(ImageFault::NotCanonical),
        "a reordered section"
    );

    let faults = [
        ImageFault::Domain,
        ImageFault::Truncated,
        ImageFault::NotUtf8,
        ImageFault::IndexingTag,
        ImageFault::Ordinal,
        ImageFault::Trailing,
        ImageFault::NotCanonical,
    ];
    let rendered: Vec<String> = faults.iter().map(ToString::to_string).collect();
    for (index, phrase) in rendered.iter().enumerate() {
        assert!(
            rendered
                .iter()
                .skip(index.saturating_add(1))
                .all(|other| other != phrase),
            "`{phrase}` renders apart"
        );
    }
}

#[test]
fn a_lookup_of_the_wrong_kind_is_refused()
{
    let schema = graph();
    let unknown = |kind, name: &str| {
        Some(SchemaError::Unknown {
            kind,
            name: name.into(),
        })
    };
    let vertex = schema.object("V").expect("an object resolves");
    assert_eq!(
        schema.object_name(vertex).map(AsRef::as_ref),
        Ok("V"),
        "the resolved object's name reads back as its text"
    );
    assert_eq!(
        schema.object("src").err(),
        unknown(ElementKind::Object, "src"),
        "an arrow as an object"
    );
    assert!(schema.arrow("src").is_ok(), "an arrow resolves");
    assert_eq!(
        schema.arrow("V").err(),
        unknown(ElementKind::Arrow, "V"),
        "an object as an arrow"
    );
    assert!(schema.attribute("label").is_ok(), "an attribute resolves");
    assert_eq!(
        schema.attribute("tgt").err(),
        unknown(ElementKind::Attribute, "tgt"),
        "an arrow as an attribute"
    );
    let loops = reflexive(Indexing::Indexed);
    assert!(loops.equation("refl_src").is_ok(), "an equation resolves");
    assert_eq!(
        loops.equation("refl").err(),
        unknown(ElementKind::Equation, "refl"),
        "an arrow as an equation"
    );
}

#[test]
fn an_ordinal_out_of_range_is_refused()
{
    let small = graph();
    let large = keyed::schema().expect("the keyed schema presents");
    let arrow = large.arrows().last().expect("the keyed schema has arrows");
    let attribute = large
        .attributes()
        .last()
        .expect("the keyed schema has attributes");
    let equation = large
        .equations()
        .last()
        .expect("the keyed schema has an equation");
    let unknown = |kind, ordinal| SchemaError::UnknownOrdinal {
        kind,
        ordinal: Ordinal(ordinal),
    };
    assert_eq!(
        small.arrow_at(arrow).err(),
        Some(unknown(ElementKind::Arrow, usize::from(arrow))),
        "an arrow past the last"
    );
    assert_eq!(
        small.attribute_at(attribute).err(),
        Some(unknown(ElementKind::Attribute, usize::from(attribute))),
        "an attribute past the last"
    );
    assert_eq!(
        small.equation_at(equation).err(),
        Some(unknown(ElementKind::Equation, usize::from(equation))),
        "an equation past the last"
    );
}

#[test]
fn an_attribute_type_is_found_by_name()
{
    let schema = keyed::schema().expect("the keyed schema presents");
    let declared = |name: &str| {
        schema
            .attribute_at(schema.attribute(name).expect("a keyed attribute"))
            .expect("the attribute is the schema's")
            .ty()
    };
    assert_eq!(schema.attribute_type("Text"), Ok(declared("task_name")));
    assert_eq!(schema.attribute_type("Bytes"), Ok(declared("move_receipt")));
    assert_ne!(declared("task_name"), declared("move_receipt"));
    assert_eq!(
        schema.attribute_type("Float"),
        Err(SchemaError::Unknown {
            kind: ElementKind::AttributeType,
            name: "Float".into(),
        })
    );
}
