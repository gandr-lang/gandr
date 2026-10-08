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
//! fit; a flat vector drop needs none. The depth is asserted through the decode
//! metrics before the drop, so the case cannot silently degenerate into a
//! shallow graph and keep passing.

/// The adversarial-depth totality suite.
#[cfg(test)]
mod adversarial_depth
{
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
    const CHAIN_LINKS: usize = 100_000;

    /// A stack far too small for a per-node recursive destructor over the
    /// chain, and ample for an iterative decode whose worklists live on the
    /// heap.
    const SMALL_STACK_BYTES: usize = 256 * 1024;

    /// A hand-held byte image.
    #[repr(transparent)]
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Bytes(Vec<u8>);

    impl AsRef<[u8]> for Bytes
    {
        fn as_ref(&self) -> &[u8]
        {
            self.0.as_slice()
        }
    }

    /// Build a chain-deep artifact's canonical bytes.
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
                // Nothing but this binding owns the decoded graph, so dropping it
                // here is the whole teardown rather than a partial one.
                drop(artifact);
                entries
            })
            .expect("the small-stack worker starts");

        let entries = worker.join().expect("the small-stack worker finishes");
        assert_eq!(
            expected, entries,
            "the graph really is chain-deep, so the teardown claim is not vacuous"
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
