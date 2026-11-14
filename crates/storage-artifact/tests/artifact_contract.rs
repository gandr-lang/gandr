//! The artifact layer's specification suite: the record round trip, the
//! identity's determinism, sensitivity and history-independence, the stored
//! read back through the kernel's decoder, and each refusal of that read.
//!
//! The artifact contract suite.

use core::fmt::Write as _;
use core::num::NonZeroU64;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::FORMAT_VERSION;
use gandr_kernel_term::FormatVersion;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MalformedSite;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;
use gandr_storage_artifact::ARTIFACT_IDENTITY_LEN;
use gandr_storage_artifact::ArtifactError;
use gandr_storage_artifact::ArtifactManifest;
use gandr_storage_artifact::ArtifactManifestVersion;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::ContentName;
use gandr_storage_artifact::HEADER_KEY;
use gandr_storage_artifact::MANIFEST_DOMAIN;
use gandr_storage_artifact::Naming;
use gandr_storage_artifact::ORDER_KEY;
use gandr_storage_artifact::RECORD_KEY_LEN;
use gandr_storage_artifact::RecordKey;
use gandr_storage_artifact::SegmentBytes;
use gandr_storage_artifact::build;
use gandr_storage_artifact::unnamed;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_records::BlockStore as _;
use gandr_storage_records::BoundaryMaskBits;
use gandr_storage_records::BoundaryParams;
use gandr_storage_records::BoundaryProfile;
use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::EncodingVersion;
use gandr_storage_records::HashAlgorithm;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::NodeHash;
use gandr_storage_records::NodeKind;
use gandr_storage_records::RecordCount;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::SeparatorConvention;
use gandr_storage_records::StoredNode;
use gandr_storage_records::TreeKind;
use gandr_storage_records::TreeParams;
use gandr_storage_records::decode_node;
use gandr_storage_records::encode_leaf;
use gandr_storage_records::hash_node;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::EditDepth;
use gandr_storage_values::EmissionFault;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::measure_edit;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

/// One declaration a generated environment holds.
#[derive(Clone, Copy, Debug)]
enum Kind
{
    /// `def : unit := ()`.
    UnitDefinition,
    /// `axiom : unit`.
    UnitAxiom,
    /// `axiom : Type 0`, a universe the level oracle mints.
    UniverseAxiom,
    /// `def : unit := c0`, naming the first declaration, so a later
    /// segment reaches into an earlier one; the first declaration falls
    /// back to a unit definition.
    ReferenceToFirst,
}

/// A count of declarations.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Count(usize);

/// The artifact of the declarations `kinds` names, in order, each admitted
/// by bypass, since storage reads no typing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an encoded artifact with one declaration per kind; a reference at
///   position zero becomes a unit definition.
/// - provides: four declaration shapes and cross-declaration references.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 in 64 generated environments of zero to 47 declarations
///   observes reassembly and stored-read agreement; a 300-declaration cycle
///   exercises an internal root. The predicate checks count when decoding
///   succeeds, while consumer reads distinguish invalid images. The witnesses
///   do not independently classify every generated declaration's term shape.
/// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
#[spec(ensures: |ret| decode(ret.as_image()).map_or(true, |decoded|
            decoded.declarations().len() == kinds.len()))]
fn artifact_of(kinds: &[Kind]) -> EncodedArtifact
{
    let mut arena = TermArena::new();
    let mut declarations = Vec::with_capacity(kinds.len());
    for (position, &kind) in kinds.iter().enumerate() {
        let declaration = match (kind, position) {
            (Kind::UnitDefinition, _) | (Kind::ReferenceToFirst, 0) => {
                let declared = arena.value_type_unit();
                let body = arena.value_unit();
                DeclarationBuilder::new(&mut arena).def(
                    LevelSignature::monomorphic(),
                    declared,
                    body,
                )
            },
            (Kind::UnitAxiom, _) => {
                let declared = arena.value_type_unit();
                DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), declared)
            },
            (Kind::UniverseAxiom, _) => {
                let declared = arena.value_type_universe(GroundSort::Value, Level::zero());
                DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), declared)
            },
            (Kind::ReferenceToFirst, _) => {
                let declared = arena.value_type_unit();
                let body = arena.value_constant(ConstantIndex::from(0_usize));
                DeclarationBuilder::new(&mut arena).def(
                    LevelSignature::monomorphic(),
                    declared,
                    body,
                )
            },
        };
        declarations.push(MarkedDeclaration::new(
            AdmissionMark::UncheckedBypass,
            declaration,
        ));
    }

    encode(&arena, &declarations)
}

/// An artifact sharing subterms within and across declarations: a unit
/// definition, a definition naming it, a universe axiom and a unit axiom.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a structurally decodable four-declaration artifact in the
///   documented order, with the second declaration referring to the first.
/// - provides: the small shared-subterm consumer fixture.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 for this fixed four-declaration artifact observes every
///   reassembled byte and a stored read equal to its kernel decode. It
///   distinguishes lost declarations or damaged images, not an alternative
///   well-formed four-declaration fixture; the predicate checks count and
///   structural decodability rather than full term-shape equivalence.
/// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
#[spec(ensures: |ret| decode(ret.as_image())
        .is_ok_and(|decoded| decoded.declarations().len() == 4))]
fn shared_artifact() -> EncodedArtifact
{
    artifact_of(&[
        Kind::UnitDefinition,
        Kind::ReferenceToFirst,
        Kind::UniverseAxiom,
        Kind::UnitAxiom,
    ])
}

/// An artifact of `count` declarations cycling through every kind.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an encoded artifact with exactly count declarations, cycling
///   through the four fixture kinds.
/// - provides: a multi-leaf artifact under the current boundary profile.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 at 300 declarations observes exact stored-read agreement
///   with the kernel decode and an internal record-tree root. It distinguishes
///   truncated cycles and malformed output within decoder budgets, not every
///   permutation of the four declaration kinds.
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
#[spec(ensures: |ret| decode(ret.as_image()).map_or(true, |decoded|
            decoded.declarations().len() == count.0))]
fn long_artifact(count: Count) -> EncodedArtifact
{
    let cycle = [
        Kind::UnitDefinition,
        Kind::ReferenceToFirst,
        Kind::UniverseAxiom,
        Kind::UnitAxiom,
    ];
    let kinds: Vec<Kind> = cycle.iter().copied().cycle().take(count.0).collect();

    artifact_of(&kinds)
}

/// The record set `artifact` cuts into.
///
/// # Specification
/// - requires: the encoded fixture lies within the kernel decoder's budgets.
/// - ensures: the returned header and ordered segments concatenate to artifact.
/// - provides: the record set consumed by the integration scenarios.
/// - fails: never.
/// - panics: if the fixture violates the decoder's admission conditions.
///
/// # Panics
/// Panics if the fixture does not decode within the kernel's budgets.
///
/// # Adequacy
/// - hypothesis: L2 on the fixed four-declaration fixture and 64 generated
///   environments with at most 47 declarations observes exact byte equality,
///   distinguishing lost headers, changed segment order and dropped bytes.
///   Refused images are not the domain of this asserting helper.
/// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
/// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
#[spec(ensures: |ret| {
        let mut offset = ret.header().as_ref().len();
        artifact.as_ref().starts_with(ret.header().as_ref())
            && ret.segments().all(|segment| {
                let end = offset.saturating_add(segment.as_ref().len());
                let agrees = artifact.as_ref().get(offset .. end) == Some(segment.as_ref());
                offset = end;
                agrees
            }) && offset == artifact.as_ref().len()
    })]
fn records_of(artifact: &EncodedArtifact) -> ArtifactRecordSet
{
    ArtifactRecordSet::from_artifact(artifact.as_image()).expect("the artifact decodes")
}

/// `set` committed into a fresh store under the current parameters.
///
/// # Specification
/// - requires: set is within the record plane's current admission limits.
/// - ensures: the manifest names the set's header and declarations and the
///   returned store holds its root; invalid kernel bytes remain unvalidated.
/// - provides: an isolated committed artifact for each consumer scenario.
/// - fails: never.
/// - panics: if the record plane refuses the fixture.
///
/// # Panics
/// Panics when the fixture cannot be built or written under current
/// parameters.
///
/// # Adequacy
/// - hypothesis: L2 on one- and 300-declaration fixtures observes the complete
///   decoded artifact after store traversal, detecting missing roots or
///   children and mismatched counts. L3 stores a corrupt kernel header and
///   observes a kernel refusal rather than storage validation. Arbitrary
///   record-plane limits and failing stores are outside this helper's domain.
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
/// - witness: `tests::artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`
#[spec(ensures: |ret| ret.0.kernel_format() == FORMAT_VERSION
        && usize::try_from(u64::from(ret.0.record_count())).ok()
            == Some(set.records().len().saturating_add(2))
        && ret.1.load(ret.0.root_node()).is_ok())]
fn committed(set: &ArtifactRecordSet) -> (ArtifactManifest, InMemoryBlockStore)
{
    let mut store = InMemoryBlockStore::new();
    let manifest = build(set, TreeParams::current(), &mut store).expect("the set commits");

    (manifest, store)
}

/// `records` written as an index tree under the current parameters into
/// `store`, and the manifest naming that tree exactly.
///
/// # Specification
/// - requires: records are strictly ascending and within current record-plane
///   limits.
/// - ensures: the manifest counts exactly records and its root is present in
///   the returned store, beside what `store` held; the artifact layer has not
///   admitted their keys.
/// - provides: authenticated but potentially misplaced records for refusal
///   probes, over a store that holds an honest set's value leaves or none.
/// - fails: never.
/// - panics: if the record plane refuses the supplied fixture.
///
/// # Panics
/// Panics when the records cannot be built or stored under current
/// parameters.
///
/// # Adequacy
/// - hypothesis: L3 on forged indexes observes exact misplaced-key positions
///   after authentication. It distinguishes losing the stored root from the
///   intended key refusal; arbitrary record-plane refusal paths are outside
///   this helper's domain.
/// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
#[spec(
        requires: records.iter().zip(records.iter().skip(1))
            .all(|(previous, next)| previous.key() < next.key()),
        ensures: |ret| ret.0.kernel_format() == FORMAT_VERSION
            && usize::try_from(u64::from(ret.0.record_count())).ok() == Some(records.len())
            && ret.1.load(ret.0.root_node()).is_ok(),
    )]
fn stored_as_named(
    records: &[RecordRef<'_>],
    mut store: InMemoryBlockStore,
) -> (ArtifactManifest, InMemoryBlockStore)
{
    let params = TreeParams::current();
    let tree = RecordTree::build(records, params).expect("the records build a tree");
    tree.write_to(&mut store).expect("the tree writes");
    let manifest = ArtifactManifest::new(
        FORMAT_VERSION,
        params.boundary_commitment(),
        tree.root().record_count(),
        tree.root_node_hash(),
        Naming::Bytes,
    );

    (manifest, store)
}

/// A record count of `count`.
///
/// # Specification
/// - requires: nothing; supported targets' declaration counts fit u64.
/// - ensures: the record count is numerically equal to count.
/// - provides: a lossless count observer across the usize/u64 boundary.
/// - fails: never.
/// - panics: none on supported targets.
///
/// # Adequacy
/// - hypothesis: L2 observes the manifest's count against the explicit five
///   records of the shared fixture and against generated lengths plus one. This
///   distinguishes omitted headers and off-by-one counts within zero to 47
///   generated declarations, not the full integer domain.
/// - witness: `tests::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
/// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
#[spec(ensures: |ret| usize::try_from(u64::from(ret)).ok() == Some(count.0))]
fn record_count(count: Count) -> RecordCount
{
    RecordCount(u64::try_from(count.0).expect("a count fits sixty-four bits"))
}

#[test]
fn unsupported_build_parameters_do_not_write_nodes()
{
    let set = records_of(&shared_artifact());
    let current = TreeParams::current();
    let stale = TreeParams::new(
        current.kind(),
        EncodingVersion::V1,
        current.hash_algorithm(),
        current.separator_convention(),
        current.boundary(),
    );
    let mut store = InMemoryBlockStore::new();
    assert_eq!(
        Err(ArtifactError::Records {
            refusal: RecordTreeError::UnsupportedVersion {
                version: EncodingVersion::V1.number(),
            }
        }),
        build(&set, stale, &mut store),
    );
    assert_eq!(
        gandr_storage_records::StoredNodeCount::from(0_usize),
        store.len()
    );
}

#[test]
fn records_round_trip_to_a_byte_identical_artifact()
{
    let artifact = shared_artifact();
    let set = records_of(&artifact);
    assert_eq!(
        artifact.as_ref(),
        set.reassemble().as_ref(),
        "the header and the segment at each place are the artifact, byte for byte"
    );
    assert_eq!(4, set.places().len(), "one place per declaration");
    assert_eq!(4, set.records().len(), "one record per distinct segment");

    let (manifest, _store) = committed(&set);
    assert_eq!(
        record_count(Count(6)),
        manifest.record_count(),
        "the manifest counts the header, the order and the four distinct segments"
    );
}

/// #776: the set cut by a decode resumed after a kept prefix is the set cut
/// whole, at every split of an artifact, and for an artifact that does not
/// lead with the prefix.
#[test]
fn a_set_cut_after_a_kept_prefix_is_the_whole_cut_776()
{
    let artifact = long_artifact(Count(9));
    let whole = records_of(&artifact);
    let other = shared_artifact();
    for split in 0 ..= 9_usize {
        let (kept, prefix) = ArtifactRecordSet::from_artifact_keeping(
            artifact.as_image(),
            ConstantIndex::from(split),
        )
        .expect("the artifact decodes");
        assert_eq!(kept, whole, "the keeping cut is the whole one");
        let Maybe::Present(prefix) = prefix
        else {
            panic!("the first {split} declarations are kept");
        };
        assert_eq!(
            ArtifactRecordSet::from_artifact_after(&prefix, artifact.as_image())
                .expect("the artifact decodes"),
            whole,
            "resumed after {split}"
        );
        assert_eq!(
            ArtifactRecordSet::from_artifact_after(&prefix, other.as_image())
                .expect("the other artifact decodes"),
            records_of(&other),
            "another artifact, after {split}"
        );
    }
}

#[test]
fn the_same_artifact_mints_the_same_identity()
{
    let set = records_of(&shared_artifact());
    let (first, _first_store) = committed(&set);
    let (second, _second_store) = committed(&records_of(&shared_artifact()));
    assert_eq!(
        first.identity(),
        second.identity(),
        "one artifact mints one identity"
    );
    assert_eq!(
        first.root_node(),
        second.root_node(),
        "one artifact has one root node"
    );
}

#[test]
fn a_manifest_names_its_version_and_spells_its_identity_bytes()
{
    let (manifest, _store) = committed(&records_of(&shared_artifact()));
    assert_eq!(ArtifactManifestVersion::V2, manifest.manifest_version());
    let identity = manifest.identity();
    assert_eq!(ARTIFACT_IDENTITY_LEN, identity.as_ref().len());
    let mut spelled = String::new();
    for byte in identity.as_ref() {
        write!(spelled, "{byte:02x}").expect("a string takes any text");
    }
    assert_eq!(
        spelled,
        identity.to_string(),
        "the identity spells its bytes"
    );
    let image = manifest.encode();
    assert!(
        image.as_image().as_ref().starts_with(MANIFEST_DOMAIN),
        "the image opens with its domain"
    );
}

#[test]
fn any_perturbation_changes_the_identity()
{
    let header = SegmentBytes::from(b"header".as_slice());
    let set_of = |header: SegmentBytes<'_>, segments: [&[u8]; 2]| {
        ArtifactRecordSet::from_segments(header, segments.map(SegmentBytes::from))
    };
    let (base, _base_store) = committed(&set_of(header, [b"alpha", b"beta"]));
    let (segment, _segment_store) = committed(&set_of(header, [b"alpha", b"BETA!"]));
    let (headed, _headed_store) = committed(&set_of(SegmentBytes::from(b"HEADER".as_slice()), [
        b"alpha", b"beta",
    ]));
    let (swapped, _swapped_store) = committed(&set_of(header, [b"beta", b"alpha"]));
    let named_with = |second: u8| {
        set_of(header, [b"alpha", b"beta"])
            .named(&[
                Maybe::Present(ContentName::from([1; 32])),
                Maybe::Present(ContentName::from([second; 32])),
            ])
            .expect("one name per place")
    };
    let (named, _named_store) = committed(&named_with(2));
    let (renamed, _renamed_store) = committed(&named_with(3));
    assert_ne!(
        base.identity(),
        swapped.identity(),
        "two places swapped move the identity, though the records are the same"
    );
    assert_ne!(
        base.identity(),
        named.identity(),
        "names beside the places move the identity"
    );
    assert_ne!(
        named.identity(),
        renamed.identity(),
        "a changed name moves the identity"
    );
    assert_ne!(
        base.identity(),
        segment.identity(),
        "a changed segment moves the identity"
    );
    assert_ne!(
        base.identity(),
        headed.identity(),
        "a changed header moves the identity"
    );
}

/// An insertion of a declaration whose bytes the artifact already holds
/// leaves every record as it was: the order alone takes the new place.
#[test]
fn an_insertion_leaves_every_record_it_does_not_rewrite_7340()
{
    let cycle = [
        Kind::UnitDefinition,
        Kind::ReferenceToFirst,
        Kind::UniverseAxiom,
        Kind::UnitAxiom,
    ];
    let kinds: Vec<Kind> = cycle.iter().copied().cycle().take(40).collect();
    let mut inserted = kinds.clone();
    inserted.insert(20, Kind::UnitAxiom);
    let base = records_of(&artifact_of(&kinds));
    let edited = records_of(&artifact_of(&inserted));
    assert_eq!(
        base.records(),
        edited.records(),
        "each record past the insertion keeps its key and its bytes"
    );
    assert_eq!(base.places().len().saturating_add(1), edited.places().len());
    assert_eq!(
        base.places().get(.. 20),
        edited.places().get(.. 20),
        "the places before the insertion stay"
    );
    assert_eq!(
        base.places().get(20 ..),
        edited.places().get(21 ..),
        "the places past the insertion move one place on, each naming its record"
    );
}

/// A set named by its writer stores and reads back with each name at its
/// place, under a manifest that says it is named. A manifest that says the
/// other form is refused, and so are one name too few and an absent name.
#[test]
fn a_named_set_reads_back_with_its_names_7340()
{
    let honest = records_of(&shared_artifact());
    let names: Vec<Maybe<ContentName, unnamed::Absent>> = (0_u8 .. 4)
        .map(|index| Maybe::Present(ContentName::from([index; 32])))
        .collect();
    let named = honest.clone().named(&names).expect("one name per place");
    let (manifest, store) = committed(&named);
    assert_eq!(Naming::Named, manifest.naming());
    let order = named.order_image();
    let refs = named.record_refs(&order);
    let tree = RecordTree::build(&refs, TreeParams::current()).expect("the records build a tree");
    let back =
        ArtifactRecordSet::from_stored(tree.records(), &store).expect("the stored set reads back");
    assert_eq!(back, named, "each name reads back at its place");
    assert!(
        manifest.read_under(&store, TreeParams::current()).is_ok(),
        "a named set reads back through the kernel's decoder"
    );
    let unnamed_claim = ArtifactManifest::new(
        FORMAT_VERSION,
        manifest.commitment().clone(),
        manifest.record_count(),
        manifest.root_node(),
        Naming::Bytes,
    );
    assert_eq!(
        Err(ArtifactError::NamingMismatch {
            manifest: Naming::Bytes,
        }),
        unnamed_claim.read_under(&store, TreeParams::current()),
        "a manifest that says the other form is refused"
    );
    assert_eq!(
        Err(ArtifactError::Misnamed {
            place: RecordIndex::from(3_usize)
        }),
        honest.clone().named(names.get(.. 3).expect("three names")),
        "one name too few is refused at the place without one"
    );
    let mut unkeyed = names;
    if let Some(name) = unkeyed.get_mut(2) {
        *name = Maybe::Absent(unnamed::Absent::Unkeyed);
    }
    assert_eq!(
        Err(ArtifactError::Misnamed {
            place: RecordIndex::from(2_usize)
        }),
        honest.named(&unkeyed),
        "a place the kernel gives no key is refused at that place"
    );
}

#[test]
fn tree_nodes_store_and_reopen()
{
    // The index holds two records. Under the current rule they share one leaf;
    // a rule that caps a leaf at one record puts each in a leaf of its own,
    // under an internal root. So these fixtures witness both root shapes.
    let current = TreeParams::current();
    let one_per_leaf = TreeParams::new(
        TreeKind::CURRENT,
        EncodingVersion::CURRENT,
        HashAlgorithm::CURRENT,
        SeparatorConvention::CURRENT,
        BoundaryParams::new(
            BoundaryProfile::CURRENT,
            current.boundary().mask_bits(),
            BoundaryRecordCap::try_from(1_u32).expect("a record cap"),
        ),
    );
    for (artifact, params, root_kind) in [
        (
            artifact_of(&[Kind::UnitDefinition]),
            current,
            NodeKind::Leaf,
        ),
        (long_artifact(Count(300)), one_per_leaf, NodeKind::Internal),
    ] {
        let mut store = InMemoryBlockStore::new();
        let manifest = build(&records_of(&artifact), params, &mut store).expect("the set commits");
        let root = store
            .load(manifest.root_node())
            .expect("the root is stored");
        assert_eq!(
            root_kind,
            decode_node(root.bytes(), &mut DecodeWork::new())
                .expect("the root decodes")
                .kind()
        );
        let expected = decode(artifact.as_image()).expect("the artifact decodes");
        assert_eq!(
            Ok(expected.clone()),
            manifest.read_under(&store, params),
            "the stored artifact reads back as the decode of its own image"
        );
        let reread = ArtifactManifest::decode(manifest.encode().as_image())
            .expect("the manifest's image decodes");
        assert_eq!(
            Ok(expected),
            reread.read_under(&store, params),
            "a manifest read from its bytes reads the same artifact"
        );
        assert_eq!(
            Err(ArtifactError::Records {
                refusal: RecordTreeError::UnknownNode {
                    hash: manifest.root_node(),
                },
            }),
            manifest.read_under(&InMemoryBlockStore::new(), params),
            "a store without the root refuses it by name"
        );
    }
}

#[test]
fn a_foreign_profile_or_format_is_refused_before_any_load()
{
    let set = records_of(&shared_artifact());
    let (manifest, _store) = committed(&set);
    let empty = InMemoryBlockStore::new();

    let foreign_format = ArtifactManifest::new(
        FormatVersion(1),
        manifest.commitment().clone(),
        manifest.record_count(),
        manifest.root_node(),
        manifest.naming(),
    );
    assert_eq!(
        Err(ArtifactError::UnsupportedKernelFormat {
            found: FormatVersion(1),
        }),
        foreign_format.read_under(&empty, TreeParams::current()),
        "a kernel format this build does not decode is refused with nothing loaded"
    );

    let foreign = TreeParams::new(
        TreeKind::CURRENT,
        EncodingVersion::CURRENT,
        HashAlgorithm::CURRENT,
        SeparatorConvention::CURRENT,
        BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::try_from(2_u8).expect("a mask width"),
            BoundaryRecordCap::try_from(64_u32).expect("a record cap"),
        ),
    );
    let mut foreign_store = InMemoryBlockStore::new();
    let cut_otherwise = build(&set, foreign, &mut foreign_store).expect("the set commits");
    assert_eq!(
        Err(ArtifactError::IncompatibleProfile),
        cut_otherwise.read_under(&empty, TreeParams::current()),
        "a tree cut under another boundary rule is refused with nothing loaded"
    );
    assert!(
        cut_otherwise.read_under(&foreign_store, foreign).is_ok(),
        "the reader sharing the rule reads it"
    );
}

#[test]
fn a_manifest_naming_another_record_count_is_refused()
{
    let set = records_of(&shared_artifact());
    let (manifest, store) = committed(&set);
    let miscounted = ArtifactManifest::new(
        FORMAT_VERSION,
        manifest.commitment().clone(),
        RecordCount(u64::from(manifest.record_count()).saturating_add(1)),
        manifest.root_node(),
        manifest.naming(),
    );
    assert_eq!(
        Err(ArtifactError::TreeMismatch),
        miscounted.read_under(&store, TreeParams::current()),
        "the stored records do not rebuild the tree a miscounted manifest names"
    );
}

#[test]
fn a_matching_identity_over_bytes_the_kernel_refuses_is_refused()
{
    // The header's magic is one byte off. Storage cannot tell: the tree
    // binds the bytes, the manifest names the tree, and the identity a
    // reader holds matches the one it was handed.
    let honest = records_of(&shared_artifact());
    let mut header = honest.header().as_ref().to_vec();
    let first = header.first_mut().expect("the header is not empty");
    *first = b'X';
    let forged =
        ArtifactRecordSet::from_segments(SegmentBytes::from(header.as_slice()), honest.segments());
    let (manifest, store) = committed(&forged);
    let held = manifest.identity();
    let handed = ArtifactManifest::decode(manifest.encode().as_image())
        .expect("the manifest's image decodes");
    assert_eq!(held, handed.identity(), "the identity matches");
    assert_eq!(
        Err(ArtifactError::Kernel {
            refusal: DecodeError::Malformed {
                site: MalformedSite::Header,
            },
        }),
        handed.read_under(&store, TreeParams::current()),
        "the kernel refuses the bytes, and so the read is refused"
    );
}

#[test]
fn a_stored_tree_with_misplaced_keys_is_refused()
{
    let honest = records_of(&shared_artifact());
    let (_honest_manifest, leaves) = committed(&honest);
    let order = honest.order_image();
    let refs = honest.record_refs(&order);
    let place_count = honest.places().len();
    let record_count = honest.records().len();
    let refused = |records: &[RecordRef<'_>], store: &InMemoryBlockStore| {
        let (manifest, store) = stored_as_named(records, store.clone());
        manifest.read_under(&store, TreeParams::current())
    };
    let header_bytes = honest.header();
    let header = RecordRef::new(HEADER_KEY, header_bytes.as_ref());
    let first = honest
        .records()
        .first()
        .expect("the artifact has a declaration");
    let segment = first.segment();
    let key = RecordKey::of(segment);
    // The order's keys start past its form and its count, and its places
    // past its keys.
    let keys_at = 5_usize;
    let places_at = keys_at.saturating_add(record_count.saturating_mul(RECORD_KEY_LEN));
    let short = order
        .as_ref()
        .get(.. order.as_ref().len().saturating_sub(1))
        .expect("a prefix");
    let second_key_at = keys_at.saturating_add(RECORD_KEY_LEN);
    let first_key = order
        .as_ref()
        .get(keys_at .. second_key_at)
        .expect("a first key")
        .to_vec();
    let mut repeated = order.as_ref().to_vec();
    repeated
        .get_mut(second_key_at .. second_key_at.saturating_add(RECORD_KEY_LEN))
        .expect("a second key")
        .copy_from_slice(&first_key);
    let mut early = order.as_ref().to_vec();
    early
        .get_mut(places_at .. places_at.saturating_add(4))
        .expect("a first place")
        .copy_from_slice(&1_u32.to_le_bytes());
    let past_keys = u32::try_from(record_count)
        .expect("a count fits four bytes")
        .to_le_bytes();
    let mut past = order.as_ref().to_vec();
    past.get_mut(places_at .. places_at.saturating_add(4))
        .expect("a first place")
        .copy_from_slice(&past_keys);
    let mut unplaced = order.as_ref().get(.. 1).expect("the form").to_vec();
    unplaced.extend_from_slice(
        &u32::try_from(record_count.saturating_add(1))
            .expect("a count fits four bytes")
            .to_le_bytes(),
    );
    unplaced.extend_from_slice(order.as_ref().get(keys_at .. places_at).expect("the keys"));
    unplaced.extend_from_slice(&[0xff; RECORD_KEY_LEN]);
    unplaced.extend_from_slice(order.as_ref().get(places_at ..).expect("the places"));
    for (records, expected, what) in [
        (
            vec![header, RecordRef::new(key.as_ref(), segment.as_ref())],
            ArtifactError::MisplacedRecord {
                position: RecordIndex::from(1_usize),
            },
            "a tree without the order is refused at its second record",
        ),
        (
            vec![
                RecordRef::new(ORDER_KEY, order.as_ref()),
                RecordRef::new(key.as_ref(), segment.as_ref()),
            ],
            ArtifactError::MisplacedRecord {
                position: RecordIndex::ZERO,
            },
            "a tree without a header record is refused at its first record",
        ),
        (
            vec![
                header,
                RecordRef::new(ORDER_KEY, order.as_ref()),
                RecordRef::new(key.as_ref(), segment.as_ref()),
            ],
            ArtifactError::TreeMismatch,
            "an index of three records is refused: the manifest names an index of two",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, &[0x07])],
            ArtifactError::MalformedOrder {
                place: RecordIndex::ZERO,
            },
            "an order that opens with no form is refused at place zero",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, short)],
            ArtifactError::MalformedOrder {
                place: RecordIndex::from(place_count.saturating_sub(1)),
            },
            "an order one byte short is refused at its last place",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, repeated.as_slice())],
            ArtifactError::MisplacedRecord {
                position: RecordIndex::from(3_usize),
            },
            "a key the order lists twice is refused at its second listing",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, early.as_slice())],
            ArtifactError::MisplacedRecord {
                position: RecordIndex::from(3_usize),
            },
            "a place that names a key before its turn is refused at that key",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, past.as_slice())],
            ArtifactError::UnheldRecord {
                place: RecordIndex::ZERO,
            },
            "a slot past the keys is refused at its place",
        ),
        (
            vec![header, RecordRef::new(ORDER_KEY, unplaced.as_slice())],
            ArtifactError::UnplacedRecord {
                position: RecordIndex::from(record_count.saturating_add(2)),
            },
            "a key no place names is refused at that key",
        ),
    ] {
        assert_eq!(Err(expected), refused(&records, &leaves), "{what}");
    }
    let three = [
        header,
        RecordRef::new(ORDER_KEY, order.as_ref()),
        RecordRef::new(key.as_ref(), segment.as_ref()),
    ];
    let three = RecordTree::build(&three, TreeParams::current()).expect("the records build a tree");
    assert_eq!(
        Err(ArtifactError::MisplacedRecord {
            position: RecordIndex::from(2_usize),
        }),
        ArtifactRecordSet::from_stored(three.records(), &leaves).map(|set| set.records().len()),
        "a record past the order is refused at its position: no record stores its key beside \
         its bytes"
    );
    assert_eq!(
        Err(ArtifactError::Records {
            refusal: RecordTreeError::UnknownNode {
                hash: NodeHash::from(first.key()),
            },
        }),
        refused(&refs, &InMemoryBlockStore::new()),
        "an index whose value leaves the store lacks is refused at the first key"
    );
    let foreign = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
    let foreign_hash = hash_node(foreign.as_borrowed());
    let mut holding = InMemoryBlockStore::new();
    holding
        .insert(StoredNode::new(foreign_hash, foreign.as_borrowed()))
        .expect("the leaf stores");
    let mut lone = vec![u8::from(Naming::Bytes)];
    lone.extend_from_slice(&1_u32.to_le_bytes());
    lone.extend_from_slice(foreign_hash.as_ref());
    lone.extend_from_slice(&0_u32.to_le_bytes());
    assert!(
        matches!(
            refused(
                &[header, RecordRef::new(ORDER_KEY, lone.as_slice())],
                &holding
            ),
            Err(ArtifactError::Records {
                refusal: RecordTreeError::MalformedNode { .. }
            })
        ),
        "a key that names a node other than a value leaf is refused"
    );
    assert_eq!(
        order.as_ref().len(),
        record_count
            .saturating_mul(RECORD_KEY_LEN)
            .saturating_add(place_count.saturating_mul(4))
            .saturating_add(5),
        "an order of bytes alone holds its form, its count, each key once and four bytes per place"
    );
}

#[test]
fn records_cut_off_a_segment_boundary_are_refused()
{
    let artifact = shared_artifact();
    let honest = records_of(&artifact);
    let (manifest, store) = committed(&honest);
    assert!(
        manifest.read_under(&store, TreeParams::current()).is_ok(),
        "the decoder's own cuts read back"
    );

    let bytes = artifact.as_ref();
    let header_end = honest.header().as_ref().len();
    let ends: Vec<usize> = honest
        .segments()
        .scan(header_end, |end, segment| {
            *end = end.saturating_add(segment.as_ref().len());
            Some(*end)
        })
        .collect();
    let cut_at = |header: usize, cuts: &[usize]| {
        let mut segments = Vec::new();
        let mut start = header;
        for &end in cuts {
            segments.push(SegmentBytes::from(
                bytes.get(start .. end).expect("a run of the artifact"),
            ));
            start = end;
        }
        ArtifactRecordSet::from_segments(
            SegmentBytes::from(bytes.get(.. header).expect("a prefix of the artifact")),
            segments,
        )
    };

    // The header carries the first declaration's first byte.
    let late_header = cut_at(header_end.saturating_add(1), &ends);
    // The first declaration carries the second's first byte.
    let mut straddling_ends = ends;
    let straddled = straddling_ends
        .first_mut()
        .expect("the artifact has a declaration");
    *straddled = straddled.saturating_add(1);
    let straddling = cut_at(header_end, &straddling_ends);

    for (set, position, what) in [
        (late_header, RecordIndex::ZERO, "a header past its segment"),
        (
            straddling,
            RecordIndex::from(1_usize),
            "a declaration straddling the next",
        ),
    ] {
        assert_eq!(
            artifact.as_ref(),
            set.reassemble().as_ref(),
            "{what} reassembles to the same bytes"
        );
        let (cut, cut_store) = committed(&set);
        assert_eq!(
            Err(ArtifactError::SegmentBoundary { position }),
            cut.read_under(&cut_store, TreeParams::current()),
            "{what} is refused at its record"
        );
    }
}

#[test]
fn a_set_is_held_to_the_layout_s_segment_count()
{
    let artifact = shared_artifact();
    let honest = records_of(&artifact);
    assert!(
        honest
            .records()
            .iter()
            .all(|record| record.key() == RecordKey::of(record.segment())),
        "each record sits under the identity of its bytes' value leaf"
    );
    let decoded = decode(artifact.as_image()).expect("the artifact decodes");
    let layout = decoded.segments();
    assert_eq!(Ok(()), honest.ensure_cut_at(layout));

    let count = honest.places().len();
    let padded = ArtifactRecordSet::from_segments(
        honest.header(),
        honest
            .segments()
            .chain(core::iter::once(SegmentBytes::from(b"".as_slice()))),
    );
    assert_eq!(
        Err(ArtifactError::SegmentBoundary {
            position: RecordIndex::from(count.saturating_add(1)),
        }),
        padded.ensure_cut_at(layout),
        "a record past the last segment is refused at that record"
    );

    let short = ArtifactRecordSet::from_segments(
        honest.header(),
        honest.segments().take(count.saturating_sub(1)),
    );
    assert_eq!(
        Err(ArtifactError::SegmentBoundary {
            position: RecordIndex::from(count),
        }),
        short.ensure_cut_at(layout),
        "a set one segment short is refused past its last record"
    );

    assert_eq!(
        Err(ArtifactError::MisplacedRecord {
            position: RecordIndex::ZERO,
        }),
        ArtifactRecordSet::from_stored(&[], &InMemoryBlockStore::new())
            .map(|set| set.records().len()),
        "an empty tree has no header"
    );
}

/// One generated declaration kind.
///
/// # Specification
/// - requires: nothing.
/// - ensures: generated values are drawn from the four declaration kinds.
/// - provides: the declaration domain of the generated storage laws.
/// - fails: never.
/// - panics: none.
/// - executable: none — the returned opaque strategy does not expose its
///   support; enumerating all generated and shrunk values requires a runner.
///
/// # Adequacy
/// - hypothesis: L2 runs 64 environments of zero to 47 generated kinds,
///   observing complete byte reconstruction and stored-read agreement. It
///   detects storage failures reached by those samples, not absent generator
///   alternatives, a distribution promise or all shrink paths.
/// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
fn kind() -> impl Strategy<Value = Kind>
{
    prop_oneof![
        proptest::strategy::Just(Kind::UnitDefinition),
        proptest::strategy::Just(Kind::UnitAxiom),
        proptest::strategy::Just(Kind::UniverseAxiom),
        proptest::strategy::Just(Kind::ReferenceToFirst),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Over generated environments the records reassemble to the artifact,
    /// one place per declaration and one record per distinct segment beside
    /// the header and the order, the identity is deterministic, and the
    /// stored artifact reads back as its decode.
    #[test]
    fn round_trip_over_generated_environments(
        kinds in proptest::collection::vec(kind(), 0 .. 48_usize)
    )
    {
        let artifact = artifact_of(&kinds);
        let set = records_of(&artifact);
        let reassembled = set.reassemble();
        prop_assert_eq!(artifact.as_ref(), reassembled.as_ref());
        prop_assert_eq!(kinds.len(), set.places().len());
        let distinct: alloc::collections::BTreeSet<Vec<u8>> =
            set.segments().map(|segment| segment.as_ref().to_vec()).collect();
        prop_assert_eq!(distinct.len(), set.records().len());

        let (first, store) = committed(&set);
        let (second, _second_store) = committed(&set);
        prop_assert_eq!(first.identity(), second.identity());
        prop_assert_eq!(record_count(Count(distinct.len().saturating_add(2))), first.record_count());
        prop_assert_eq!(
            decode(artifact.as_image()).map_err(ArtifactError::from),
            first.read_under(&store, TreeParams::current())
        );
    }
}

/// The cuts the value-plane witnesses commit under: every record a chunk of
/// its own, the store's pair, and no cut but the cap's.
///
/// # Specification
/// trivial.
fn cuts() -> [TypedChunkerParams; 3]
{
    let params = |kappa: NonZeroU64, cap: NonZeroU64| {
        TypedChunkerParams::new(Kappa::from(kappa), TokenCap::from(cap))
    };
    [
        params(NonZeroU64::MIN, NonZeroU64::MAX),
        params(
            NonZeroU64::MIN.saturating_add(3_u64),
            NonZeroU64::MIN.saturating_add(63_u64),
        ),
        params(NonZeroU64::MAX, NonZeroU64::MAX),
    ]
}

/// An artifact's value-plane profile under `params`.
///
/// # Specification
/// trivial.
fn value_profile(params: TypedChunkerParams) -> ValueProfile
{
    ValueProfile::new(
        params,
        CodecIdentity::new(CodecId::from(0x01_u16), CodecVersion::from(1_u16)),
        ChildIndexBase::Absolute,
    )
}

#[test]
fn an_artifact_commits_and_reads_back_to_the_image_the_kernel_decodes()
{
    for artifact in [shared_artifact(), long_artifact(Count(40))] {
        let set = records_of(&artifact);
        for params in cuts() {
            let mut store = InMemoryChunkStore::new();
            let manifest =
                cam_commit(&mut store, &value_profile(params), &set).expect("the set commits");
            let back: ArtifactRecordSet =
                cam_deref(&store, manifest.root()).expect("the set reads back");
            assert_eq!(back, set, "under {params:?}, the set reads back whole");
            let image = back.reassemble();
            assert_eq!(
                image.as_ref(),
                artifact.as_ref(),
                "under {params:?}, the set read back reassembles to the artifact"
            );
            assert!(
                decode(image.as_image()).is_ok(),
                "under {params:?}, the kernel decodes the image read back"
            );
        }
    }
}

/// A named set reads back off the value plane whole, and so does an empty
/// named set, whose form no place carries. Each is written again as the
/// stream it was read from.
#[test]
fn a_named_set_reads_back_off_the_value_plane_7340()
{
    let honest = records_of(&shared_artifact());
    let named = honest
        .named(&[
            Maybe::Present(ContentName::from([0xA5; 32])),
            Maybe::Present(ContentName::from([0x5A; 32])),
            Maybe::Present(ContentName::from([0xA5; 32])),
            Maybe::Present(ContentName::from(core::array::from_fn(|index| {
                u8::try_from(index).unwrap_or(u8::MAX)
            }))),
        ])
        .expect("one name per place");
    let empty = ArtifactRecordSet::from_segments(SegmentBytes::from(b"h".as_slice()), [])
        .named(&[])
        .expect("no place, no name");
    for (set, what) in [(named, "a named set"), (empty, "an empty named set")] {
        assert_eq!(Naming::Named, set.naming(), "{what} is named");
        for params in cuts() {
            let profile = value_profile(params);
            let mut store = InMemoryChunkStore::new();
            let manifest = cam_commit(&mut store, &profile, &set).expect("the set commits");
            let back: ArtifactRecordSet =
                cam_deref(&store, manifest.root()).expect("the set reads back");
            assert_eq!(
                back, set,
                "under {params:?}, {what} reads back with every name at its place"
            );
            assert_eq!(
                cam_commit(&mut store, &profile, &back)
                    .expect("the set commits again")
                    .root(),
                manifest.root(),
                "under {params:?}, {what} is written as the stream it was read from"
            );
        }
    }
}

/// One record of a hand-written token stream.
#[derive(Clone, Copy, Debug)]
enum Token
{
    /// A constructor opens.
    Open(ConstructorTag),
    /// A payload word.
    Word(CanonicalWord),
    /// A byte payload.
    Bytes(TokenBytes<'static>),
    /// The innermost constructor closes.
    Close,
}

/// A value whose emission is a hand-written stream, an artifact or not.
#[repr(transparent)]
struct Stream(Vec<Token>);

impl CanonicalValue for Stream
{
    /// Plays the stream into the sink.
    ///
    /// # Specification
    /// - requires: nothing; a stream no artifact emits is admitted.
    /// - ensures: the records in order, stopping at the sink's first refusal.
    /// - fails: the sink's first refusal.
    /// - panics: none.
    /// - executable: none — the records go to an opaque sink, whose record is
    ///   the committing store's.
    ///
    /// # Errors
    /// The sink's first refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 two balanced streams no artifact emits commit, so the
    ///   refusals the witness reads are the artifact decoder's.
    /// - witness: `tests::artifact_contract::a_stream_that_is_no_artifact_is_refused_off_the_value_plane`
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        for &token in &self.0 {
            match token {
                Token::Open(tag) => sink.open(tag)?,
                Token::Word(word) => sink.word(word)?,
                Token::Bytes(bytes) => sink.bytes(bytes)?,
                Token::Close => sink.close()?,
            }
        }
        Ok(())
    }

    /// Never decodes: a stream is only ever emitted.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens(_reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        Err(ValueError::MalformedEmission {
            fault: EmissionFault::EmptyValue,
        })
    }
}

#[test]
fn a_stream_that_is_no_artifact_is_refused_off_the_value_plane()
{
    let tag = |byte: u8| Token::Open(ConstructorTag::from(byte));
    let word = |value: u64| Token::Word(CanonicalWord::from(value));
    let bytes = Token::Bytes(TokenBytes::from(b"bytes".as_slice()));
    // A record's constructor where the artifact's stands.
    let headless = Stream(vec![tag(0x02), bytes, Token::Close]);
    // A place opening the retired hole tag.
    let retired = Stream(vec![
        tag(0x01),
        bytes,
        word(1),
        tag(0x03),
        bytes,
        Token::Close,
        Token::Close,
    ]);
    for (stream, expected) in [
        (headless, ValueError::UnexpectedConstructor {
            found: ConstructorTag::from(0x02_u8),
            position: TokenOffset::ZERO,
        }),
        (retired, ValueError::UnexpectedConstructor {
            found: ConstructorTag::from(0x03_u8),
            position: TokenOffset::from(3_u32),
        }),
    ] {
        let mut store = InMemoryChunkStore::new();
        let manifest = cam_commit(&mut store, &value_profile(cuts()[1]), &stream)
            .expect("the stream is balanced");
        assert_eq!(
            cam_deref::<ArtifactRecordSet>(&store, manifest.root()),
            Err(expected),
            "a stream no artifact emits is refused by name"
        );
    }
}

#[test]
fn an_edit_shares_every_chunk_before_it_on_the_value_plane()
{
    let set = records_of(&long_artifact(Count(40)));
    let edited = 30_usize;
    let segments: Vec<Vec<u8>> = set
        .segments()
        .enumerate()
        .map(|(index, segment)| {
            let mut segment = segment.as_ref().to_vec();
            if index == edited {
                segment.push(0xA5_u8);
            }
            segment
        })
        .collect();
    let changed = ArtifactRecordSet::from_segments(
        set.header(),
        segments
            .iter()
            .map(|segment| SegmentBytes::from(segment.as_slice())),
    );
    // Every record a chunk of its own: each chunk before the edit is shared,
    // and the edited record's, each after it and the root's are written anew.
    let profile = value_profile(cuts()[0]);
    let mut store = InMemoryChunkStore::new();
    let before = cam_commit(&mut store, &profile, &set)
        .expect("the set commits")
        .root();
    let after = cam_commit(&mut store, &profile, &changed)
        .expect("the edit commits")
        .root();
    let measured = measure_edit(&store, before, after, EditDepth::from(10_u64))
        .expect("both closures are in the store");
    assert_eq!(
        (
            usize::from(measured.chunks_shared),
            usize::from(measured.chunks_affected)
        ),
        (edited, 40_usize - edited + 1_usize),
        "the thirty records before the edit are shared; the ten from it on and the root are new"
    );
}
