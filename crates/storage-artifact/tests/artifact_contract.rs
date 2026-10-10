//! The artifact layer's specification suite: the record round trip, the
//! identity's determinism, sensitivity and history-independence, the stored
//! read back through the kernel's decoder, and each refusal of that read.

/// The artifact contract suite.
#[cfg(test)]
mod artifact_contract
{
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
    use gandr_storage_artifact::AdmissionKey;
    use gandr_storage_artifact::ArtifactError;
    use gandr_storage_artifact::ArtifactManifest;
    use gandr_storage_artifact::ArtifactRecord;
    use gandr_storage_artifact::ArtifactRecordSet;
    use gandr_storage_artifact::HEADER_KEY;
    use gandr_storage_artifact::SegmentBytes;
    use gandr_storage_artifact::build;
    use gandr_storage_records::BlockStore as _;
    use gandr_storage_records::BoundaryMaskBits;
    use gandr_storage_records::BoundaryParams;
    use gandr_storage_records::BoundaryProfile;
    use gandr_storage_records::BoundaryRecordCap;
    use gandr_storage_records::DecodeWork;
    use gandr_storage_records::EncodingVersion;
    use gandr_storage_records::HashAlgorithm;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_storage_records::NodeKind;
    use gandr_storage_records::RecordCount;
    use gandr_storage_records::RecordIndex;
    use gandr_storage_records::RecordRef;
    use gandr_storage_records::RecordTree;
    use gandr_storage_records::RecordTreeError;
    use gandr_storage_records::SeparatorConvention;
    use gandr_storage_records::TreeKind;
    use gandr_storage_records::TreeParams;
    use gandr_storage_records::decode_node;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::Strategy;
    use proptest::prop_assert_eq;
    use proptest::prop_oneof;
    use proptest::proptest;

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
    /// - ensures: an encoded artifact with one declaration per kind; a
    ///   reference at position zero becomes a unit definition.
    /// - provides: four declaration shapes and cross-declaration references.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 in 64 generated environments of zero to 47 declarations
    ///   observes reassembly and stored-read agreement; a 300-declaration cycle
    ///   exercises an internal root. The predicate checks count when decoding
    ///   succeeds, while consumer reads distinguish invalid images. The
    ///   witnesses do not independently classify every generated declaration's
    ///   term shape.
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    #[anodized::spec(ensures: |ret| decode(ret.as_image()).map_or(true, |decoded|
            decoded.declarations().len() == kinds.len()))]
    fn artifact_of(kinds: &[Kind]) -> EncodedArtifact
    {
        let mut arena = TermArena::new();
        let mut declarations = Vec::with_capacity(kinds.len());
        for (position, &kind) in kinds.iter().enumerate() {
            let declaration = match (kind, position) {
                | (Kind::UnitDefinition, _) | (Kind::ReferenceToFirst, 0) => {
                    let declared = arena.value_type_unit();
                    let body = arena.value_unit();
                    DeclarationBuilder::new(&mut arena).def(
                        LevelSignature::monomorphic(),
                        declared,
                        body,
                    )
                },
                | (Kind::UnitAxiom, _) => {
                    let declared = arena.value_type_unit();
                    DeclarationBuilder::new(&mut arena)
                        .axiom(LevelSignature::monomorphic(), declared)
                },
                | (Kind::UniverseAxiom, _) => {
                    let declared = arena.value_type_universe(GroundSort::Value, Level::zero());
                    DeclarationBuilder::new(&mut arena)
                        .axiom(LevelSignature::monomorphic(), declared)
                },
                | (Kind::ReferenceToFirst, _) => {
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
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    #[anodized::spec(ensures: |ret| decode(ret.as_image())
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
    /// - hypothesis: L2 at 300 declarations observes exact stored-read
    ///   agreement with the kernel decode and an internal record-tree root. It
    ///   distinguishes truncated cycles and malformed output within decoder
    ///   budgets, not every permutation of the four declaration kinds.
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    #[anodized::spec(ensures: |ret| decode(ret.as_image()).map_or(true, |decoded|
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
    /// - requires: the encoded fixture lies within the kernel decoder's
    ///   budgets.
    /// - ensures: the returned header and ordered segments concatenate to
    ///   artifact.
    /// - provides: the record set consumed by the integration scenarios.
    /// - fails: never.
    /// - panics: if the fixture violates the decoder's admission conditions.
    ///
    /// # Panics
    /// Panics if the fixture does not decode within the kernel's budgets.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the fixed four-declaration fixture and 64 generated
    ///   environments with at most 47 declarations observes exact byte
    ///   equality, distinguishing lost headers, changed segment order and
    ///   dropped bytes. Refused images are not the domain of this asserting
    ///   helper.
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    #[anodized::spec(ensures: |ret| {
        let mut offset = ret.header().as_ref().len();
        artifact.as_ref().starts_with(ret.header().as_ref())
            && ret.records().iter().all(|record| {
                let segment = record.segment();
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
    ///   returned store holds its root; invalid kernel bytes remain
    ///   unvalidated.
    /// - provides: an isolated committed artifact for each consumer scenario.
    /// - fails: never.
    /// - panics: if the record plane refuses the fixture.
    ///
    /// # Panics
    /// Panics when the fixture cannot be built or written under current
    /// parameters.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on one- and 300-declaration fixtures observes the
    ///   complete decoded artifact after store traversal, detecting missing
    ///   roots or children and mismatched counts. L3 stores a corrupt kernel
    ///   header and observes a kernel refusal rather than storage validation.
    ///   Arbitrary record-plane limits and failing stores are outside this
    ///   helper's domain.
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `artifact_contract::artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`
    #[anodized::spec(ensures: |ret| ret.0.kernel_format() == FORMAT_VERSION
        && usize::try_from(u64::from(ret.0.record_count())).ok()
            == Some(set.records().len().saturating_add(1))
        && ret.1.load(ret.0.root_node()).is_ok())]
    fn committed(set: &ArtifactRecordSet) -> (ArtifactManifest, InMemoryBlockStore)
    {
        let mut store = InMemoryBlockStore::new();
        let manifest = build(set, TreeParams::current(), &mut store).expect("the set commits");

        (manifest, store)
    }

    /// `records` written as a record tree under the current parameters, and
    /// the manifest naming that tree exactly.
    ///
    /// # Specification
    /// - requires: records are strictly ascending and within current
    ///   record-plane limits.
    /// - ensures: the manifest counts exactly records and its root is present
    ///   in the returned store; the artifact layer has not admitted their keys.
    /// - provides: authenticated but potentially misplaced records for refusal
    ///   probes.
    /// - fails: never.
    /// - panics: if the record plane refuses the supplied fixture.
    ///
    /// # Panics
    /// Panics when the records cannot be built or stored under current
    /// parameters.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a missing-header tree and a skipped-initial-index
    ///   tree observes exact misplaced-key positions after authentication. It
    ///   distinguishes losing the stored root from the intended key refusal;
    ///   arbitrary record-plane refusal paths are outside this helper's domain.
    /// - witness: `artifact_contract::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    #[anodized::spec(
        requires: records.iter().zip(records.iter().skip(1))
            .all(|(previous, next)| previous.key() < next.key()),
        ensures: |ret| ret.0.kernel_format() == FORMAT_VERSION
            && usize::try_from(u64::from(ret.0.record_count())).ok() == Some(records.len())
            && ret.1.load(ret.0.root_node()).is_ok(),
    )]
    fn stored_as_named(records: &[RecordRef<'_>]) -> (ArtifactManifest, InMemoryBlockStore)
    {
        let params = TreeParams::current();
        let tree = RecordTree::build(records, params).expect("the records build a tree");
        let mut store = InMemoryBlockStore::new();
        tree.write_to(&mut store).expect("the tree writes");
        let manifest = ArtifactManifest::new(
            FORMAT_VERSION,
            params.boundary_commitment(),
            tree.root().record_count(),
            tree.root_node_hash(),
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
    ///   records of the shared fixture and against generated lengths plus one.
    ///   This distinguishes omitted headers and off-by-one counts within zero
    ///   to 47 generated declarations, not the full integer domain.
    /// - witness: `artifact_contract::artifact_contract::records_round_trip_to_a_byte_identical_artifact`
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
    #[anodized::spec(ensures: |ret| usize::try_from(u64::from(ret)).ok() == Some(count.0))]
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
            "the header and the segments in key order are the artifact, byte for byte"
        );
        assert_eq!(4, set.records().len(), "one record per declaration");

        let (manifest, _store) = committed(&set);
        assert_eq!(
            record_count(Count(5)),
            manifest.record_count(),
            "the manifest counts the header and the four declarations"
        );
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
    fn any_perturbation_changes_the_identity()
    {
        let header = SegmentBytes::from(b"header".as_slice());
        let set_of = |header: SegmentBytes<'_>, second: &[u8]| {
            ArtifactRecordSet::from_records(header, vec![
                ArtifactRecord::new(
                    ConstantIndex::from(0_usize),
                    SegmentBytes::from(b"alpha".as_slice()),
                ),
                ArtifactRecord::new(ConstantIndex::from(1_usize), SegmentBytes::from(second)),
            ])
            .expect("the keys are unique")
        };
        let (base, _base_store) = committed(&set_of(header, b"beta"));
        let (segment, _segment_store) = committed(&set_of(header, b"BETA!"));
        let (headed, _headed_store) =
            committed(&set_of(SegmentBytes::from(b"HEADER".as_slice()), b"beta"));
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

    #[test]
    fn a_permuted_build_order_yields_the_same_identity()
    {
        let base = records_of(&shared_artifact());
        let reversed: Vec<ArtifactRecord> = base.records().iter().rev().cloned().collect();
        let permuted =
            ArtifactRecordSet::from_records(base.header(), reversed).expect("the keys are unique");
        let (base_manifest, _base_store) = committed(&base);
        let (permuted_manifest, _permuted_store) = committed(&permuted);
        assert_eq!(
            base_manifest.identity(),
            permuted_manifest.identity(),
            "the order records were gathered in does not reach the identity"
        );
        assert_eq!(
            base_manifest.root_node(),
            permuted_manifest.root_node(),
            "nor the root node"
        );
    }

    #[test]
    fn tree_nodes_store_and_reopen()
    {
        // These concrete fixtures witness both supported root shapes.
        for (artifact, root_kind) in [
            (artifact_of(&[Kind::UnitDefinition]), NodeKind::Leaf),
            (long_artifact(Count(300)), NodeKind::Internal),
        ] {
            let (manifest, store) = committed(&records_of(&artifact));
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
                manifest.read_under(&store, TreeParams::current()),
                "the stored artifact reads back as the decode of its own image"
            );
            let reread = ArtifactManifest::decode(manifest.encode().as_image())
                .expect("the manifest's image decodes");
            assert_eq!(
                Ok(expected),
                reread.read_under(&store, TreeParams::current()),
                "a manifest read from its bytes reads the same artifact"
            );
            assert_eq!(
                Err(ArtifactError::Records {
                    refusal: RecordTreeError::UnknownNode {
                        hash: manifest.root_node(),
                    },
                }),
                manifest.read_under(&InMemoryBlockStore::new(), TreeParams::current()),
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
    fn a_matching_identity_over_bytes_the_kernel_refuses_is_refused()
    {
        // The header's magic is one byte off. Storage cannot tell: the tree
        // binds the bytes, the manifest names the tree, and the identity a
        // reader holds matches the one it was handed.
        let honest = records_of(&shared_artifact());
        let mut header = honest.header().as_ref().to_vec();
        let first = header.first_mut().expect("the header is not empty");
        *first = b'X';
        let forged = ArtifactRecordSet::from_records(
            SegmentBytes::from(header.as_slice()),
            honest.records().to_vec(),
        )
        .expect("the keys are unique");
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
        let header = honest.header();
        let segment = honest
            .records()
            .first()
            .expect("the artifact has a declaration")
            .segment();

        let skipping = AdmissionKey::from(ConstantIndex::from(1_usize));
        let (manifest, store) = stored_as_named(&[
            RecordRef::new(HEADER_KEY, header.as_ref()),
            RecordRef::new(skipping.as_ref(), segment.as_ref()),
        ]);
        assert_eq!(
            Err(ArtifactError::MisplacedRecord {
                position: RecordIndex::from(1_usize),
            }),
            manifest.read_under(&store, TreeParams::current()),
            "the declaration keys start at admission index zero"
        );

        let first = AdmissionKey::from(ConstantIndex::from(0_usize));
        let (headless, headless_store) =
            stored_as_named(&[RecordRef::new(first.as_ref(), segment.as_ref())]);
        assert_eq!(
            Err(ArtifactError::MisplacedRecord {
                position: RecordIndex::ZERO,
            }),
            headless.read_under(&headless_store, TreeParams::current()),
            "a tree without a header record is refused at its first record"
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
            .records()
            .iter()
            .scan(header_end, |end, record| {
                *end = end.saturating_add(record.segment().as_ref().len());
                Some(*end)
            })
            .collect();
        let record = |index: usize, start: usize, end: usize| {
            ArtifactRecord::new(
                ConstantIndex::from(index),
                SegmentBytes::from(bytes.get(start .. end).expect("a run of the artifact")),
            )
        };
        let cut_at = |header: usize, cuts: &[usize]| {
            let mut records = Vec::new();
            let mut start = header;
            for (index, &end) in cuts.iter().enumerate() {
                records.push(record(index, start, end));
                start = end;
            }
            ArtifactRecordSet::from_records(
                SegmentBytes::from(bytes.get(.. header).expect("a prefix of the artifact")),
                records,
            )
            .expect("the keys are unique")
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

    /// One generated declaration kind.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: generated values are drawn from the four declaration kinds.
    /// - provides: the declaration domain of the generated storage laws.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the returned opaque strategy does not expose its
    ///   support; enumerating all generated and shrunk values requires a
    ///   runner.
    ///
    /// # Adequacy
    /// - hypothesis: L2 runs 64 environments of zero to 47 generated kinds,
    ///   observing complete byte reconstruction and stored-read agreement. It
    ///   detects storage failures reached by those samples, not absent
    ///   generator alternatives, a distribution promise or all shrink paths.
    /// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
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
        /// one record per declaration plus the header, the identity is
        /// deterministic, and the stored artifact reads back as its decode.
        #[test]
        fn round_trip_over_generated_environments(
            kinds in proptest::collection::vec(kind(), 0 .. 48_usize)
        )
        {
            let artifact = artifact_of(&kinds);
            let set = records_of(&artifact);
            let reassembled = set.reassemble();
            prop_assert_eq!(artifact.as_ref(), reassembled.as_ref());
            prop_assert_eq!(kinds.len(), set.records().len());

            let (first, store) = committed(&set);
            let (second, _second_store) = committed(&set);
            prop_assert_eq!(first.identity(), second.identity());
            prop_assert_eq!(record_count(Count(kinds.len().saturating_add(1))), first.record_count());
            prop_assert_eq!(
                decode(artifact.as_image()).map_err(ArtifactError::from),
                first.read_under(&store, TreeParams::current())
            );
        }
    }
}
