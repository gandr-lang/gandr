//! Adversarial-depth totality, observed as ownership rather than as survival.
//!
//! A decoder can build an arbitrarily deep graph from bytes, so the dangerous
//! moment is not decoding it but **dropping** it: under owned pointers a deep
//! uniquely-owned chain still recurses on destruction, and iterative decode
//! does not cover deallocation.
//!
//! A deep-graph test that merely has to finish is measuring the host stack, so
//! this one runs inside a thread with a deliberately small stack. A recursive
//! destructor over a chain this deep would need megabytes of frames and cannot
//! fit; flat vectors do not recurse along graph edges. A bounded walk checks
//! every thunk-over-returner link before the drop; entry counts alone cannot
//! distinguish a deep chain from a shallow graph. This witnesses one
//! adversarial shape and stack bound, not every possible graph or allocation
//! failure.

/// The adversarial-depth totality suite.
#[cfg(test)]
mod adversarial_depth
{
    use anodized::spec;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::ArtifactImage;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::TableEntryCount;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;

    /// The number of thunk-over-returner links in the chain; each contributes
    /// two distinct entries above the unit type at the bottom.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: fixes the number of two-entry links used to separate
    ///   recursive edge teardown from flat arena ownership.
    /// - provides: a fixed, repeatable boundary for the adversarial-depth
    ///   witness.
    /// - panics: none.
    /// - executable: none — a test-policy constant has no callable post-state;
    ///   the structural depth witness observes the resulting graph.
    ///
    /// # Adequacy
    /// - hypothesis: L3 decodes the artifact inside a 256 KiB stack thread,
    ///   walks exactly 100,000 thunk-over-returner links to the unit type,
    ///   observes the exact entry count and drops the sole graph owner there.
    ///   The bounded structural walk rules out a shallow graph with the same
    ///   count. Byte-identical re-encoding supplies agreement, while the
    ///   predicate independently projects the frozen tags and predecessor
    ///   ordinals; neither witness claims arbitrary graph totality or
    ///   allocation-failure behavior.
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
    const CHAIN_LINKS: usize = 100_000;

    /// A stack far too small for a per-node recursive destructor over the
    /// chain, and ample for an iterative decode whose worklists live on the
    /// heap.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: sets the stack size of the thread that owns and drops the
    ///   decoded graph.
    /// - provides: a fixed, repeatable boundary for the adversarial-depth
    ///   witness.
    /// - panics: none.
    /// - executable: none — a test-policy constant has no callable post-state;
    ///   successful construction and completion of the requested-size thread
    ///   supply the runtime observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 decodes the artifact inside a 256 KiB stack thread,
    ///   walks exactly 100,000 thunk-over-returner links to the unit type,
    ///   observes the exact entry count and drops the sole graph owner there.
    ///   The bounded structural walk rules out a shallow graph with the same
    ///   count. Byte-identical re-encoding supplies agreement, while the
    ///   predicate independently projects the frozen tags and predecessor
    ///   ordinals; neither witness claims arbitrary graph totality or
    ///   allocation-failure behavior.
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// A hand-held byte image.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: owns the canonical fixture image independently of the arena
    ///   that produced it.
    /// - provides: owned bytes that outlive the producing arena.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   producer predicate and decoder observations check its byte content.
    ///
    /// # Adequacy
    /// - hypothesis: L3 decodes the artifact inside a 256 KiB stack thread,
    ///   walks exactly 100,000 thunk-over-returner links to the unit type,
    ///   observes the exact entry count and drops the sole graph owner there.
    ///   The bounded structural walk rules out a shallow graph with the same
    ///   count. Byte-identical re-encoding supplies agreement, while the
    ///   predicate independently projects the frozen tags and predecessor
    ///   ordinals; neither witness claims arbitrary graph totality or
    ///   allocation-failure behavior.
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
    #[repr(transparent)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Bytes(Vec<u8>);

    impl AsRef<[u8]> for Bytes
    {
        /// Borrow the image's bytes.
        ///
        /// # Specification
        /// trivial.
        fn as_ref(&self) -> &[u8]
        {
            self.0.as_slice()
        }
    }

    /// Build a chain-deep artifact's canonical bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the canonical bytes of an artifact whose single
    ///   axiom's declared type is a chain of [`CHAIN_LINKS`]
    ///   thunk-over-returner links above the unit type.
    /// - provides: the adversarial input the teardown claim is made over, and
    ///   the first half of that claim: the producing arena is dropped here, on
    ///   an ordinary stack and with no ordering care taken.
    /// - panics: panics only through the arena and builder calls it makes, none
    ///   of which is fallible.
    ///
    /// # Adequacy
    /// - hypothesis: L3 decodes the artifact inside a 256 KiB stack thread,
    ///   walks exactly 100,000 thunk-over-returner links to the unit type,
    ///   observes the exact entry count and drops the sole graph owner there.
    ///   The bounded structural walk rules out a shallow graph with the same
    ///   count. Byte-identical re-encoding supplies agreement, while the
    ///   predicate independently projects the frozen tags and predecessor
    ///   ordinals; neither witness claims arbitrary graph totality or
    ///   allocation-failure behavior.
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_artifact_round_trips_byte_identically`
    #[spec(
        ensures: |ret| { let entries = CHAIN_LINKS.saturating_mul(2).saturating_add(1);
            let count_word = u64::try_from(entries).unwrap_or(u64::MAX);
            let first = 13_usize.saturating_add(usize::try_from(64_u32.saturating_sub((count_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
            ret.0.starts_with(&[b'G', b'K', b'X', b'1', 2, 0, 0, 1, 0, 1, 0, 0, 0])
                && ({ let scalar = count_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(13_usize .. (13_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.get(first) == Some(&1)
                && (1 .. entries).try_fold(first.saturating_add(1),
            |position, index| { let previous = u64::try_from(index.saturating_sub(1)).unwrap_or(u64::MAX);
            let tag = if index.rem_euclid(2) == 1 { 0x07 }
            else { 0x05 };
            (ret.0.get(position) == Some(&tag)
                && ({ let scalar = previous;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position.saturating_add(1)) .. (position.saturating_add(1)).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })).then_some(position.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub((previous).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }).is_some_and(|position| { let root_word = u64::try_from(entries.saturating_sub(1)).unwrap_or(u64::MAX);
            ({ let scalar = root_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.len() == position.saturating_add(usize::try_from(64_u32.saturating_sub((root_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) }) },
    )]
    fn deep_artifact_bytes() -> Bytes
    {
        let mut arena = TermArena::new();
        let mut declared = arena.value_type_unit();
        let mut remaining = CHAIN_LINKS;
        while remaining > 0 {
            let returner = arena.comp_type_returner(declared);
            declared = arena.value_type_thunk(returner);
            remaining = remaining.saturating_sub(1);
        }
        let builder = DeclarationBuilder::new(&mut arena);
        let declaration = builder.axiom(LevelSignature::monomorphic(), declared);
        let declarations = vec![MarkedDeclaration::new(AdmissionMark::Checked, declaration)];
        let bytes = Bytes(Vec::from(encode(&arena, &declarations)));
        // The producing arena is dropped here, on the caller's ordinary stack and
        // with no ordering care taken, which is the first half of the claim.
        bytes
    }

    #[test]
    fn a_deep_decoded_graph_tears_down_inside_a_small_stack_thread()
    {
        let bytes = deep_artifact_bytes();
        let expected = TableEntryCount::from(CHAIN_LINKS.saturating_mul(2).saturating_add(1));

        let worker = std::thread::Builder::new()
            .stack_size(SMALL_STACK_BYTES)
            .spawn(move || {
                let artifact = decode(ArtifactImage::from(bytes.as_ref()))
                    .expect("the deep artifact is within every budget and decodes");
                let entries = artifact.metrics().table_entries();
                let mut node = artifact
                    .declarations()
                    .first()
                    .expect("the axiom exists")
                    .declaration()
                    .declared_id();
                for _ in 0 .. CHAIN_LINKS {
                    let Some(&gandr_kernel_term::ValueType::Thunk(returner)) =
                        artifact.arena().value_type(node)
                    else {
                        panic!("each chain link starts with a thunk");
                    };
                    let Some(&gandr_kernel_term::CompType::Returner(inner)) =
                        artifact.arena().comp_type(returner)
                    else {
                        panic!("each thunk returns the next value type");
                    };
                    node = inner;
                }
                assert_eq!(
                    artifact.arena().value_type(node),
                    Some(&gandr_kernel_term::ValueType::Unit),
                    "the exact chain ends at unit"
                );
                // Nothing but this binding owns the decoded graph, so dropping it
                // here is the whole teardown rather than a partial one.
                drop(artifact);
                entries
            })
            .expect("the small-stack worker starts");

        let entries = worker.join().expect("the small-stack worker finishes");
        assert_eq!(
            expected, entries,
            "the graph contains exactly the declared chain entries"
        );
    }

    #[test]
    fn a_deep_artifact_round_trips_byte_identically()
    {
        let bytes = deep_artifact_bytes();
        let artifact =
            decode(ArtifactImage::from(bytes.as_ref())).expect("the deep artifact decodes");
        assert_eq!(
            bytes.0,
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "a decoded deep artifact re-encodes to the bytes it came from"
        );
    }
}
