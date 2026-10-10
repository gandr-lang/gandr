//! The format's real contract is its rejection suite.
//!
//! Every case here is either a property the format promises — sharing survives
//! a round trip, two differently shared spellings of one abstract environment
//! write identically — or a named refusal, asserted at its exact variant on an
//! artifact built to trigger exactly it. The boundary goldens derive their
//! shapes from the budget constants rather than from hand-written numbers, so
//! retuning a constant to another power of two needs no edit here.

/// The sharing-format conformance and rejection suite.
#[cfg(test)]
mod sharing_format
{
    use anodized::spec;
    use gandr_kernel_term::AdmissionMark;
    use gandr_kernel_term::ArtifactImage;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ByteOffset;
    use gandr_kernel_term::CompType;
    use gandr_kernel_term::Computation;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::DeclarationBuilder;
    use gandr_kernel_term::DeclarationContent;
    use gandr_kernel_term::DecodeError;
    use gandr_kernel_term::DecodedArtifact;
    use gandr_kernel_term::EncodedArtifact;
    use gandr_kernel_term::ExpandedWork;
    use gandr_kernel_term::FORMAT_VERSION;
    use gandr_kernel_term::FormatVersion;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::MAX_ARTIFACT_EXPANDED_WORK;
    use gandr_kernel_term::MAX_DECODED_LEVEL_OFFSET;
    use gandr_kernel_term::MAX_EXPANDED_TERM_WORK;
    use gandr_kernel_term::MAX_TABLE_ENTRIES;
    use gandr_kernel_term::MalformedSite;
    use gandr_kernel_term::MarkedDeclaration;
    use gandr_kernel_term::NameSegment;
    use gandr_kernel_term::ReservedKind;
    use gandr_kernel_term::ReservedSlot;
    use gandr_kernel_term::SHARING_BLOCK_FIRST;
    use gandr_kernel_term::SHARING_BLOCK_LAST;
    use gandr_kernel_term::StructuredName;
    use gandr_kernel_term::TableEntryCount;
    use gandr_kernel_term::TagSite;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueId;
    use gandr_kernel_term::ValueType;
    use gandr_kernel_term::ValueTypeId;
    use gandr_kernel_term::WireTag;
    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;
    use proptest::prelude::Just;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::Strategy;
    use proptest::prelude::any;
    use proptest::prop_assert_eq;
    use proptest::prop_oneof;
    use proptest::proptest;

    // ---------------------------------------------------------------------------
    // The suite's own nominal vocabulary
    // ---------------------------------------------------------------------------

    /// A hand-built byte image.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: the exact bytes of a hand-built image, including malformed
    ///   framing.
    /// - provides: nominal separation for a raw image distinct from a decoded
    ///   artifact.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Debug, Default, Eq, PartialEq)]
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

    /// One literal byte written into a hand-built image.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: one unvalidated literal byte, kept distinct from a
    ///   variable-length integer.
    /// - provides: nominal separation for one unvalidated literal byte, kept
    ///   distinct from a variable-length integer.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct RawByte(u8);

    /// One wire integer, written as a minimal unsigned LEB128 varint.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: an unsigned scalar to be written with minimal variable-length
    ///   framing.
    /// - provides: nominal separation for an unsigned scalar to be written with
    ///   minimal variable-length framing.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct WireValue(u64);

    /// A subterm-table index, as a hand-built artifact spells one.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: an unvalidated global table ordinal, not a declaration-local
    ///   offset.
    /// - provides: nominal separation for an unvalidated global table ordinal,
    ///   not a declaration-local offset.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TableIndex(u32);

    /// A declared format version, as a hand-built header spells one.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: an unvalidated little-endian format-version word.
    /// - provides: nominal separation for an unvalidated little-endian
    ///   format-version word.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Version(u16);

    /// A position in a decoded declaration sequence, or in a byte image.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: a host-sized sequence or byte position; callers choose which
    ///   domain they address.
    /// - provides: nominal separation for a host-sized sequence or byte
    ///   position; callers choose which domain they address.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Position(usize);

    /// A repeated-diamond depth.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: the number of repeated pair layers, distinct from its
    ///   expanded tree size.
    /// - provides: nominal separation for the number of repeated pair layers,
    ///   distinct from its expanded tree size.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Depth(u32);

    impl Depth
    {
        /// The depth one above this one.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the depth one greater, or this depth at the
        ///   representable ceiling.
        /// - provides: a total increment for depth-boundary fixtures;
        ///   saturation alone does not establish termination of a search.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L2 compares powers and expanded-tree sizes with
        ///   widened arithmetic, and finds admissible depths by enumerating the
        ///   finite mathematical candidates. L3 includes the exact u64
        ///   tree-size boundary, its neighbors, the u32 exponent ceiling and
        ///   the largest u64 cap, distinguishing premature saturation and a
        ///   nonterminating saturated search.
        /// - witness: `sharing_format::sharing_format::diamond_arithmetic_saturates_at_the_tree_size_boundary`
        #[spec(
            ensures: |ret| u64::from(ret.0) == u64::from(self.0).saturating_add(1).min(u64::from(u32::MAX)),
        )]
        fn next(self) -> Self
        {
            Self(self.0.saturating_add(1))
        }
    }

    /// A count of links in a value-type chain.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: the number of thunk-over-returner steps, each contributing
    ///   two entries.
    /// - provides: nominal separation for the number of thunk-over-returner
    ///   steps, each contributing two entries.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct LinkCount(usize);

    impl Bytes
    {
        /// An empty image.
        ///
        /// # Specification
        /// trivial.
        fn new() -> Self
        {
            Self::default()
        }

        /// Append one literal byte.
        ///
        /// # Specification
        /// trivial.
        fn byte(
            &mut self,
            byte: RawByte,
        )
        {
            self.0.push(byte.0);
        }

        /// Append the minimal unsigned LEB128 encoding of `value`.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: appends the little-endian base-128 groups of `value` with
        ///   no continuation byte past the highest set group.
        /// - provides: the suite's own varint writer, written independently of
        ///   the crate's, so a fixture's bytes do not inherit the encoder's
        ///   idea of minimality.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        #[spec(
            captures: start = self.0.len(),
            ensures: |ret| self.0.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((value.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))
                    && ({ let scalar = value.0;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                self.0.as_slice().get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }),
        )]
        fn varint(
            &mut self,
            value: WireValue,
        )
        {
            let mut remaining = value.0;
            loop {
                let low = u8::try_from(remaining & 0x7f).unwrap_or(0_u8);
                remaining = remaining.wrapping_shr(7);
                if remaining == 0_u64 {
                    self.0.push(low);
                    return;
                }
                self.0.push(low | 0x80);
            }
        }

        /// Append another image verbatim.
        ///
        /// # Specification
        /// trivial.
        fn append(
            &mut self,
            other: &Self,
        )
        {
            self.0.extend_from_slice(&other.0);
        }

        /// Append the four-byte artifact magic.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: appends the four bytes `GKX1`.
        /// - provides: the header magic spelled out here rather than read from
        ///   the crate, so a change to the constant shows up as a refused
        ///   fixture instead of silently agreeing with itself.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::a_foreign_magic_is_refused_at_the_header`
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        #[spec(
            captures: start = self.0.len(),
            ensures: |ret| self.0.len() == start.saturating_add(4)
                    && self.0.get(start ..) == Some(b"GKX1".as_slice()),
        )]
        fn magic(&mut self)
        {
            self.0.extend_from_slice(b"GKX1");
        }

        /// Append a little-endian format version.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: appends exactly two bytes, the version's little-endian
        ///   image.
        /// - provides: the header's version field, written at the fixed width
        ///   the format gives it.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        #[spec(
            captures: start = self.0.len(),
            ensures: |ret| self.0.len() == start.saturating_add(2)
                    && self.0.get(start ..) == Some(version.0.to_le_bytes().as_slice()),
        )]
        fn version(
            &mut self,
            version: Version,
        )
        {
            self.0.extend_from_slice(&version.0.to_le_bytes());
        }

        /// Append everything from `offset` onward in `other`, which the caller
        /// keeps within `other`'s length.
        ///
        /// # Specification
        /// - requires: `offset` is within `other`'s length.
        /// - ensures: appends every byte of `other` from `offset` onward.
        /// - provides: the splice that rebuilds an artifact with a new header
        ///   over an unchanged tail, so a header-only variant shares the rest
        ///   of the bytes with the artifact it came from.
        /// - panics: panics when `offset` is past `other`'s length.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::a_minted_atom_table_with_a_repeat_is_refused`
        /// - witness: `sharing_format::sharing_format::a_minted_atom_table_omitting_an_atom_is_refused`
        /// - witness: `sharing_format::sharing_format::a_minted_atom_table_naming_a_definition_is_refused`
        #[spec(
            requires: offset.0 <= other.0.len(), captures: start = self.0.len(),
            ensures: |ret| self.0.get(start ..) == other.0.get(offset.0 ..),
        )]
        fn append_tail(
            &mut self,
            other: &Self,
            offset: Position,
        )
        {
            let tail = other
                .0
                .get(offset.0 ..)
                .expect("the image is at least as long as the offset");
            self.0.extend_from_slice(tail);
        }
    }

    // ---------------------------------------------------------------------------
    // Raw artifact construction, for the cases a well-formed encoder cannot produce
    // ---------------------------------------------------------------------------

    /// A hand-built declaration segment.
    ///
    /// # Specification
    /// - requires: nothing; fields may deliberately describe invalid input.
    /// - ensures: raw declaration fields whose consistency is deliberately not
    ///   enforced by the fixture type.
    /// - provides: nominal separation for raw declaration framing.
    /// - panics: none.
    /// - executable: none — data declaration, not a callable boundary; the
    ///   fixture writers and decoder refusals observe its represented fields.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    struct RawDeclaration
    {
        /// The admission mark byte.
        mark: RawByte,
        /// The declaration kind byte.
        kind: RawByte,
        /// The structured name's segments, each as the raw bytes its text
        /// field carries.
        name: Vec<Bytes>,
        /// The entries this segment introduces, already encoded.
        entries: Vec<Bytes>,
        /// The declared-type root's global index.
        root_declared: TableIndex,
        /// The body root's global index, for a definition.
        root_body: Option<TableIndex>,
        /// The erasure annotation slot, which must be zero to be accepted.
        erasure: WireValue,
    }

    impl RawDeclaration
    {
        /// A definition segment with every reserved slot empty.
        ///
        /// # Specification
        /// - requires: nothing; entries and global roots may be deliberately
        ///   inconsistent for refusal fixtures.
        /// - ensures: retains supplied entries and roots, with a checked mark,
        ///   definition kind and present body. The name and reserved fields
        ///   start empty.
        /// - provides: a raw baseline whose roots address the cross-segment
        ///   global index space, not necessarily this segment’s own entries. No
        ///   validation is performed.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        #[spec(
            captures: entry = (entries.len(), entries.iter().fold(0_usize,
                |total, bytes| total.saturating_add(bytes.0.len()))),
            ensures: |ret| ret.mark.0 == 0
                    && ret.kind.0 == 0
                    && ret.name.is_empty()
                    && ret.root_declared == root_declared
                    && ret.root_body == Some(root_body)
                    && ret.erasure.0 == 0
                    && ret.entries.len() == entry.0
                    && ret.entries.iter().fold(0_usize,
                |total, bytes| total.saturating_add(bytes.0.len())) == entry.1,
        )]
        fn definition(
            entries: Vec<Bytes>,
            root_declared: TableIndex,
            root_body: TableIndex,
        ) -> Self
        {
            Self {
                mark: RawByte(0),
                kind: RawByte(0),
                name: Vec::new(),
                entries,
                root_declared,
                root_body: Some(root_body),
                erasure: WireValue(0),
            }
        }

        /// An axiom segment, which carries a declared root and no body.
        ///
        /// # Specification
        /// - requires: nothing; entries and global roots may be deliberately
        ///   inconsistent for refusal fixtures.
        /// - ensures: retains supplied entries and roots, with a checked mark,
        ///   axiom kind and no body. The name and reserved fields start empty.
        /// - provides: a raw baseline whose roots address the cross-segment
        ///   global index space, not necessarily this segment’s own entries. No
        ///   validation is performed.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        #[spec(
            captures: entry = (entries.len(), entries.iter().fold(0_usize,
                |total, bytes| total.saturating_add(bytes.0.len()))),
            ensures: |ret| ret.mark.0 == 0
                    && ret.kind.0 == 1
                    && ret.name.is_empty()
                    && ret.root_declared == root_declared
                    && ret.root_body.is_none()
                    && ret.erasure.0 == 0
                    && ret.entries.len() == entry.0
                    && ret.entries.iter().fold(0_usize,
                |total, bytes| total.saturating_add(bytes.0.len())) == entry.1,
        )]
        fn axiom(
            entries: Vec<Bytes>,
            root_declared: TableIndex,
        ) -> Self
        {
            Self {
                mark: RawByte(0),
                kind: RawByte(1),
                name: Vec::new(),
                entries,
                root_declared,
                root_body: None,
                erasure: WireValue(0),
            }
        }

        /// This segment's bytes.
        ///
        /// # Specification
        /// - requires: nothing; fields may deliberately disagree.
        /// - ensures: returns the mark, kind, counted names, zero level counts,
        ///   counted raw entries and declared root. A present body field adds
        ///   its root, erasure count and three empty slots, regardless of the
        ///   kind byte.
        /// - provides: independent raw field framing for both valid and
        ///   deliberately inconsistent records. Presence of the optional body,
        ///   not validation of the kind, controls the trailing fields.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 accepted and malformed artifacts use this
        ///   independent fixture writer to isolate header, field-order,
        ///   reference and canonical-form decisions. Literal encoder and
        ///   decoder fixtures separately pin the frozen bytes; shared round
        ///   trips alone are not an independent oracle. The refusal witnesses
        ///   vary one field while retaining the surrounding record.
        /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
        /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
        /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
        /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
        /// - witness: `sharing_format::sharing_format::a_reserved_declaration_kind_is_refused_distinctly`
        /// - witness: `sharing_format::sharing_format::an_occupied_reserved_slot_is_refused_by_name`
        #[spec(
            ensures: |ret| ret.0.get(0 .. 2).and_then(|header| { let segment_start = 0_usize;
                 let names_count = u64::try_from(self.name.len()).unwrap_or(u64::MAX);
                if header != [self.mark.0, self.kind.0].as_slice() || !({ let scalar = names_count;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((segment_start.saturating_add(2)) .. (segment_start.saturating_add(2)).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) { return None;
                } let names_end = self.name.iter().try_fold(segment_start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((names_count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
                |position, name| { let length = u64::try_from(name.0.len()).unwrap_or(u64::MAX);
                let payload = position.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
                let end = payload.saturating_add(name.0.len());
                (({ let scalar = length;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                    && ret.0.as_slice().get(payload .. end) == Some(name.0.as_slice())).then_some(end) })?;
                let entries_count = u64::try_from(self.entries.len()).unwrap_or(u64::MAX);
                let count_start = names_end.saturating_add(2);
                if ret.0.as_slice().get(names_end .. count_start) != Some([0_u8, 0].as_slice()) || !({ let scalar = entries_count;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((count_start) .. (count_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) { return None;
                } let roots_start = self.entries.iter().try_fold(count_start.saturating_add(usize::try_from(64_u32.saturating_sub((entries_count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
                |position, entry| { let end = position.saturating_add(entry.0.len());
                (ret.0.as_slice().get(position .. end) == Some(entry.0.as_slice())).then_some(end) })?;
                let declared = u64::from(self.root_declared.0);
                let body_start = roots_start.saturating_add(usize::try_from(64_u32.saturating_sub((declared).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
                let valid_root = { let scalar = declared;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((roots_start) .. (roots_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) };
                if valid_root { self.root_body.map_or(Some(body_start),
                |body| { let body_word = u64::from(body.0);
                let erasure_start = body_start.saturating_add(usize::try_from(64_u32.saturating_sub((body_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
                let empty_start = erasure_start.saturating_add(usize::try_from(64_u32.saturating_sub((self.erasure.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
                let end = empty_start.saturating_add(3);
                (({ let scalar = body_word;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((body_start) .. (body_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                    && ({ let scalar = self.erasure.0;
                let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
                ret.0.as_slice().get((erasure_start) .. (erasure_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
                u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                    && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                    && ret.0.as_slice().get(empty_start .. end) == Some([0_u8, 0, 0].as_slice())).then_some(end) }) }
                else { None } }) == Some(ret.0.len()),
        )]
        fn bytes(&self) -> Bytes
        {
            let mut out = Bytes::new();
            out.byte(self.mark);
            out.byte(self.kind);
            out.varint(WireValue(
                u64::try_from(self.name.len()).unwrap_or(u64::MAX),
            ));
            for segment in &self.name {
                out.varint(WireValue(
                    u64::try_from(segment.0.len()).unwrap_or(u64::MAX),
                ));
                out.append(segment);
            }
            out.varint(WireValue(0)); // the level parameter count
            out.varint(WireValue(0)); // the landmark constraint count
            out.varint(WireValue(
                u64::try_from(self.entries.len()).unwrap_or(u64::MAX),
            ));
            for entry in &self.entries {
                out.append(entry);
            }
            out.varint(WireValue(u64::from(self.root_declared.0)));
            if let Some(root_body) = self.root_body {
                out.varint(WireValue(u64::from(root_body.0)));
                out.varint(self.erasure);
                out.varint(WireValue(0)); // modes and grades
                out.varint(WireValue(0)); // sealing provenance
                out.varint(WireValue(0)); // directedness and variance
            }
            out
        }
    }

    /// A hand-built artifact: a header naming `atoms`, then the segments.
    ///
    /// # Specification
    /// - requires: nothing; every field may be inconsistent with the segments,
    ///   which is what the refusal fixtures rely on.
    /// - ensures: returns the magic, the declared version, the atom count and
    ///   the atoms, then the declaration count and the segments' bytes.
    /// - provides: the hand-built artifact for shapes a well-formed encoder
    ///   cannot produce, so a refusal can be provoked without weakening the
    ///   encoder.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
    /// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[spec(
        ensures: |ret| ret.0.starts_with(b"GKX1")
                && ret.0.get(4 .. 6) == Some(version.0.to_le_bytes().as_slice())
                && { let count = u64::try_from(atoms.len()).unwrap_or(u64::MAX);
            let valid_count = { let scalar = count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(6_usize .. (6_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) };
            if valid_count { atoms.iter().try_fold((6_usize).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |position, atom| { ({ let scalar = atom.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }).then_some(position.saturating_add(usize::try_from(64_u32.saturating_sub((atom.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }) }
            else { None } }.and_then(|position| { let count = u64::try_from(declarations.len()).unwrap_or(u64::MAX);
            let valid_count = { let scalar = count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) };
            if valid_count { declarations.iter().try_fold(position.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |offset, declaration| { let segment_start = offset;
            let header = ret.0.as_slice().get(segment_start .. segment_start.saturating_add(2))?;
            let names_count = u64::try_from(declaration.name.len()).unwrap_or(u64::MAX);
            if header != [declaration.mark.0, declaration.kind.0].as_slice() || !({ let scalar = names_count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((segment_start.saturating_add(2)) .. (segment_start.saturating_add(2)).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) { return None;
            } let names_end = declaration.name.iter().try_fold(segment_start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((names_count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |position, name| { let length = u64::try_from(name.0.len()).unwrap_or(u64::MAX);
            let payload = position.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
            let end = payload.saturating_add(name.0.len());
            (({ let scalar = length;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.as_slice().get(payload .. end) == Some(name.0.as_slice())).then_some(end) })?;
            let entries_count = u64::try_from(declaration.entries.len()).unwrap_or(u64::MAX);
            let count_start = names_end.saturating_add(2);
            if ret.0.as_slice().get(names_end .. count_start) != Some([0_u8, 0].as_slice()) || !({ let scalar = entries_count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((count_start) .. (count_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) { return None;
            } let roots_start = declaration.entries.iter().try_fold(count_start.saturating_add(usize::try_from(64_u32.saturating_sub((entries_count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |position, entry| { let end = position.saturating_add(entry.0.len());
            (ret.0.as_slice().get(position .. end) == Some(entry.0.as_slice())).then_some(end) })?;
            let declared = u64::from(declaration.root_declared.0);
            let body_start = roots_start.saturating_add(usize::try_from(64_u32.saturating_sub((declared).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
            let valid_root = { let scalar = declared;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((roots_start) .. (roots_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) };
            if valid_root { declaration.root_body.map_or(Some(body_start),
            |body| { let body_word = u64::from(body.0);
            let erasure_start = body_start.saturating_add(usize::try_from(64_u32.saturating_sub((body_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
            let empty_start = erasure_start.saturating_add(usize::try_from(64_u32.saturating_sub((declaration.erasure.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
            let end = empty_start.saturating_add(3);
            (({ let scalar = body_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((body_start) .. (body_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ({ let scalar = declaration.erasure.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((erasure_start) .. (erasure_start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.as_slice().get(empty_start .. end) == Some([0_u8, 0, 0].as_slice())).then_some(end) }) }
            else { None } }) }
            else { None } }) == Some(ret.0.len()),
    )]
    fn raw_artifact(
        version: Version,
        atoms: &[WireValue],
        declarations: &[RawDeclaration],
    ) -> Bytes
    {
        let mut out = Bytes::new();
        out.magic();
        out.version(version);
        out.varint(WireValue(u64::try_from(atoms.len()).unwrap_or(u64::MAX)));
        for &atom in atoms {
            out.varint(atom);
        }
        out.varint(WireValue(
            u64::try_from(declarations.len()).unwrap_or(u64::MAX),
        ));
        for declaration in declarations {
            out.append(&declaration.bytes());
        }
        out
    }

    /// The version every accepted artifact declares.
    ///
    /// # Specification
    /// trivial.
    fn current_version() -> Version
    {
        Version(u16::from(FORMAT_VERSION))
    }

    /// The value-type unit entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the single tag byte of the unit value type, with no
    ///   payload.
    /// - provides: the smallest accepted entry, used wherever a fixture needs
    ///   one well-formed value type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
    #[spec(
        ensures: |ret| ret.0.as_slice() == [0x01_u8].as_slice(),
    )]
    fn entry_unit_type() -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x01));
        out
    }

    /// The universe entry at a constant level with no variable atoms.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the universe tag, the constant part, and a zero atom
    ///   count.
    /// - provides: the universe entry at a closed level, which is what an
    ///   abstract type's kind needs.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_universe_artifact_round_trips_byte_identically`
    #[spec(
        ensures: |ret| ret.0.starts_with(&[0x02_u8])
                && ({ let scalar = constant.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(1_usize .. (1_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.get(1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((constant.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) ..) == Some([0_u8].as_slice()),
    )]
    fn entry_universe(constant: WireValue) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x02));
        out.varint(constant);
        out.varint(WireValue(0));
        out
    }

    /// The universe entry at one variable atom with the given offset.
    ///
    /// # Specification
    /// - requires: nothing; the variable index and offset may be arbitrary.
    /// - ensures: returns the universe tag, a zero constant part, an atom count
    ///   of one, then the variable index and its offset.
    /// - provides: the universe entry carrying one variable atom, which is
    ///   where the level plane's offset cap is exercised.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
    #[spec(
        ensures: |ret| ret.0.starts_with(&[0x02_u8, 0, 1])
                && ({ let scalar = variable.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(3_usize .. (3_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ({ let scalar = offset.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((3_usize .saturating_add(usize::try_from(64_u32.saturating_sub((variable.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (3_usize .saturating_add(usize::try_from(64_u32.saturating_sub((variable.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.len() == 3_usize .saturating_add(usize::try_from(64_u32.saturating_sub((variable.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) .saturating_add(usize::try_from(64_u32.saturating_sub((offset.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
    )]
    fn entry_universe_atom(
        variable: WireValue,
        offset: WireValue,
    ) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x02));
        out.varint(WireValue(0));
        out.varint(WireValue(1));
        out.varint(variable);
        out.varint(offset);
        out
    }

    /// A universe entry whose atom list names one variable twice.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a universe entry whose atom list names variable zero
    ///   twice, at offsets one and one.
    /// - provides: the entry no canonical level encodes, so the level plane's
    ///   refusal of a repeated atom is reachable from bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_non_canonical_inline_level_is_refused`
    #[spec(
        ensures: |ret| ret.0.as_slice() == [0x02_u8, 0, 2, 0, 1, 0, 1].as_slice(),
    )]
    fn entry_universe_repeated_atom() -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x02));
        out.varint(WireValue(0));
        out.varint(WireValue(2));
        out.varint(WireValue(0));
        out.varint(WireValue(1));
        out.varint(WireValue(0));
        out.varint(WireValue(1));
        out
    }

    /// A universe entry whose inline constant is written as an overlong varint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a universe entry whose constant part is written as a
    ///   continuation byte followed by a zero group — a second image of zero.
    /// - provides: the overlong varint the writer cannot produce, so the
    ///   reader's minimality refusal is reachable from bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::an_overlong_varint_inside_an_entry_is_refused`
    #[spec(
        ensures: |ret| ret.0.as_slice() == [0x02_u8, 0x80, 0, 0].as_slice(),
    )]
    fn entry_universe_overlong_constant() -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x02));
        out.byte(RawByte(0x80));
        out.byte(RawByte(0x00));
        out.byte(RawByte(0x00));
        out
    }

    /// The unit value entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the single tag byte of the unit value, with no
    ///   payload.
    /// - provides: the smallest accepted value entry, used as a leaf wherever a
    ///   fixture needs one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[spec(
        ensures: |ret| ret.0.as_slice() == [0x0b_u8].as_slice(),
    )]
    fn entry_unit() -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x0B));
        out
    }

    /// A pair value entry over two global indices.
    ///
    /// # Specification
    /// - requires: nothing; either index may name no entry or a later one,
    ///   which is what the child-order fixtures rely on.
    /// - ensures: returns the pair tag followed by the two indices in that
    ///   order.
    /// - provides: the two-child entry the sharing and child-order cases are
    ///   built from.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
    #[spec(
        ensures: |ret| ret.0.starts_with(&[0x0d_u8])
                && ({ let scalar = u64::from(first.0);
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(1_usize .. (1_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ({ let scalar = u64::from(second.0);
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(first.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(first.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.len() == 1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(first.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(second.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
    )]
    fn entry_pair(
        first: TableIndex,
        second: TableIndex,
    ) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x0D));
        out.varint(WireValue(u64::from(first.0)));
        out.varint(WireValue(u64::from(second.0)));
        out
    }

    /// A bound-variable value entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the variable tag followed by the de Bruijn index.
    /// - provides: the leaf entry with an inline payload, distinguishing a
    ///   payload from a child reference in the entry shape.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_mis_ordered_table_is_refused_as_non_canonical`
    #[spec(
        ensures: |ret| ret.0.starts_with(&[0x09_u8])
                && ({ let scalar = index.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(1_usize .. (1_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.len() == 1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((index.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
    )]
    fn entry_variable(index: WireValue) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x09));
        out.varint(index);
        out
    }

    /// An entry whose tag byte lies above the frozen block.
    ///
    /// # Specification
    /// - requires: `tag` is a byte the format assigns to no former.
    /// - ensures: returns that single byte as an entry.
    /// - provides: the unassigned-tag entry, so the node alphabet's refusal is
    ///   reachable at a byte of the caller's choosing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::an_unassigned_node_tag_is_refused_by_name`
    #[spec(
        requires: tag.0 >= 0x20,
        ensures: |ret| ret.0.as_slice() == [tag.0].as_slice(),
    )]
    fn entry_unassigned_tag(tag: RawByte) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(tag);
        out
    }

    /// A dependent-arrow entry over a value-type domain and a computation-type
    /// codomain.
    ///
    /// # Specification
    /// - requires: nothing; either index may name an entry of the wrong family,
    ///   which is what the polarity fixtures rely on.
    /// - ensures: returns the dependent-arrow tag followed by the domain and
    ///   codomain indices in that order.
    /// - provides: the entry whose two children are of different families,
    ///   which is where the child-polarity check is exercised.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_dependent_arrow_refuses_a_mis_polarized_codomain`
    #[spec(
        ensures: |ret| ret.0.starts_with(&[0x18_u8])
                && ({ let scalar = u64::from(domain.0);
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(1_usize .. (1_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ({ let scalar = u64::from(codomain.0);
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(domain.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(domain.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && ret.0.len() == 1_usize .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(domain.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) .saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(codomain.0)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
    )]
    fn entry_pi(
        domain: TableIndex,
        codomain: TableIndex,
    ) -> Bytes
    {
        let mut out = Bytes::new();
        out.byte(RawByte(0x18));
        out.varint(WireValue(u64::from(domain.0)));
        out.varint(WireValue(u64::from(codomain.0)));
        out
    }

    // ---------------------------------------------------------------------------
    // Shapes built through the public constructors
    // ---------------------------------------------------------------------------

    /// Two to the power of `exponent`, saturating rather than overflowing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns two raised to `exponent`, or the `u64` ceiling once
    ///   the power is not representable.
    /// - provides: the expanded-size arithmetic the diamond fixtures are sized
    ///   by, saturating so a large exponent bounds the search instead of
    ///   wrapping.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares powers and expanded-tree sizes with widened
    ///   arithmetic, and finds admissible depths by enumerating the finite
    ///   mathematical candidates. L3 includes the exact u64 tree-size boundary,
    ///   its neighbors, the u32 exponent ceiling and the largest u64 cap,
    ///   distinguishing premature saturation and a nonterminating saturated
    ///   search.
    /// - witness: `sharing_format::sharing_format::diamond_arithmetic_saturates_at_the_tree_size_boundary`
    #[spec(
        ensures: |ret| u64::from(ret) == u64::try_from(1_u128.checked_shl(exponent.0).unwrap_or(u128::MAX)).unwrap_or(u64::MAX),
    )]
    fn power_of_two(exponent: Depth) -> ExpandedWork
    {
        ExpandedWork::from(1_u64.checked_shl(exponent.0).unwrap_or(u64::MAX))
    }

    /// The largest diamond depth whose expanded size, plus the one node a
    /// declared type costs beside it, still fits `cap`.
    ///
    /// # Specification
    /// - requires: cap is at least two, so a unit diamond and its declared type
    ///   fit.
    /// - ensures: returns the greatest depth whose mathematical expanded size
    ///   plus one is at most cap, including when cap is the u64 ceiling.
    /// - provides: a constant-time boundary calculation; it does not compare a
    ///   saturated power against the ceiling and enter a nonterminating search.
    /// - panics: none within the stated domain.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares powers and expanded-tree sizes with widened
    ///   arithmetic, and finds admissible depths by enumerating the finite
    ///   mathematical candidates. L3 includes the exact u64 tree-size boundary,
    ///   its neighbors, the u32 exponent ceiling and the largest u64 cap,
    ///   distinguishing premature saturation and a nonterminating saturated
    ///   search.
    /// - witness: `sharing_format::sharing_format::diamond_arithmetic_saturates_at_the_tree_size_boundary`
    #[spec(
        requires: u64::from(cap) >= 2,
        ensures: |ret| 1_u128.checked_shl(ret.0.saturating_add(1)).is_some_and(|size| size <= u128::from(u64::from(cap))
                && size.saturating_mul(2) > u128::from(u64::from(cap))),
    )]
    fn diamond_depth_within(cap: ExpandedWork) -> Depth
    {
        Depth(
            u64::BITS
                .saturating_sub(u64::from(cap).leading_zeros())
                .saturating_sub(2),
        )
    }

    /// A repeated-diamond value of the given depth: each level pairs the level
    /// below it with itself, so the expanded size doubles while the node
    /// count grows by one.
    ///
    /// # Specification
    /// - requires: `arena` is the arena the fixture's declaration will address.
    /// - ensures: mints `depth` pair nodes above one unit value, each pairing
    ///   the level below it with itself, and returns the topmost id.
    /// - provides: the shape whose expanded size doubles per level while its
    ///   node count grows by one, which is what makes the expanded-work budget
    ///   different from a node count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes shared child identity, independent
    ///   declarations with equal content, exact chain entry counts and both
    ///   sides of the work and table caps. The predicates walk the constructed
    ///   shapes without encoding or allocating a comparison arena; bounded
    ///   walks distinguish a repeated edge from a different child and stop on a
    ///   wrong former.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
    #[spec(
        ensures: |ret| { let mut node = ret;
            let mut remaining = depth.0;
            let mut valid = true;
            while remaining > 0 { match arena.value(node) { Some(&Value::Pair(left, right)) if left == right => node = left, _ => { valid = false;
            break;
            } } remaining = remaining.saturating_sub(1);
            } valid
                && arena.value(node) == Some(&Value::Unit) },
    )]
    fn diamond(
        arena: &mut TermArena,
        depth: Depth,
    ) -> ValueId
    {
        let mut node = arena.value_unit();
        let mut remaining = depth.0;
        while remaining > 0 {
            node = arena.value_pair(node, node);
            remaining = remaining.saturating_sub(1);
        }
        node
    }

    /// The expanded size of a diamond of the given depth.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns 2 raised to depth plus one, minus one, saturating
    ///   only the final mathematical tree size at the u64 ceiling.
    /// - provides: an expected expanded size independent of the decoder’s
    ///   memoized graph scan; depth 63 yields the exact u64 ceiling rather than
    ///   one less.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares powers and expanded-tree sizes with widened
    ///   arithmetic, and finds admissible depths by enumerating the finite
    ///   mathematical candidates. L3 includes the exact u64 tree-size boundary,
    ///   its neighbors, the u32 exponent ceiling and the largest u64 cap,
    ///   distinguishing premature saturation and a nonterminating saturated
    ///   search.
    /// - witness: `sharing_format::sharing_format::diamond_arithmetic_saturates_at_the_tree_size_boundary`
    #[spec(
        ensures: |ret| u64::from(ret) == u64::try_from(depth.0.checked_add(1).and_then(|shift| 1_u128.checked_shl(shift)).map_or(u128::MAX,
            |power| power.saturating_sub(1))).unwrap_or(u64::MAX),
    )]
    fn diamond_expanded(depth: Depth) -> ExpandedWork
    {
        ExpandedWork::from(
            u64::from(power_of_two(depth))
                .saturating_sub(1)
                .saturating_mul(2)
                .saturating_add(1),
        )
    }

    /// A value-type chain of `links` thunk-over-returner steps above the unit
    /// type, which contributes one entry for the unit and two per link,
    /// with an expanded size equal to that entry count.
    ///
    /// # Specification
    /// - requires: `arena` is the arena the fixture's declaration will address.
    /// - ensures: mints `links` thunk-over-returner steps above the unit type
    ///   and returns the topmost id.
    /// - provides: the shape whose entry count and expanded size are equal, so
    ///   a table-entry cap and a work cap can be exercised apart.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes shared child identity, independent
    ///   declarations with equal content, exact chain entry counts and both
    ///   sides of the work and table caps. The predicates walk the constructed
    ///   shapes without encoding or allocating a comparison arena; bounded
    ///   walks distinguish a repeated edge from a different child and stop on a
    ///   wrong former.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
    #[spec(
        ensures: |ret| { let mut node = ret;
            let mut remaining = links.0;
            let mut valid = true;
            while remaining > 0 { if let Some(&ValueType::Thunk(returner)) = arena.value_type(node)
                && let Some(&CompType::Returner(inner)) = arena.comp_type(returner) { node = inner;
            }
            else { valid = false;
            break;
            } remaining = remaining.saturating_sub(1);
            } valid
                && arena.value_type(node) == Some(&ValueType::Unit) },
    )]
    fn type_chain(
        arena: &mut TermArena,
        links: LinkCount,
    ) -> ValueTypeId
    {
        let mut node = arena.value_type_unit();
        let mut remaining = links.0;
        while remaining > 0 {
            let returner = arena.comp_type_returner(node);
            node = arena.value_type_thunk(returner);
            remaining = remaining.saturating_sub(1);
        }
        node
    }

    /// One checked definition over the given roots.
    ///
    /// # Specification
    /// - requires: `declared` and `body` were minted in `arena`.
    /// - ensures: returns a checked-mark definition over the two roots.
    /// - provides: the one declaration wrapper the encoder-driven fixtures use,
    ///   so the mark and the level signature are stated once.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes shared child identity, independent
    ///   declarations with equal content, exact chain entry counts and both
    ///   sides of the work and table caps. The predicates walk the constructed
    ///   shapes without encoding or allocating a comparison arena; bounded
    ///   walks distinguish a repeated edge from a different child and stop on a
    ///   wrong former.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
    #[spec(
        requires: arena.value_type(declared).is_some()
                && arena.value(body).is_some(), captures: before = arena.watermark(),
        ensures: |ret| ret.mark() == AdmissionMark::Checked
                && u32::from(ret.declaration().levels().params()) == 0
                && ret.declaration().levels().constraints().is_empty()
                && ret.declaration().name().segments().is_empty()
                && ret.declaration().provenance().is_empty()
                && ret.declaration().content() == &DeclarationContent::Def { declared, body }
                && arena.watermark() == before,
    )]
    fn definition_over(
        arena: &mut TermArena,
        declared: ValueTypeId,
        body: ValueId,
    ) -> MarkedDeclaration
    {
        let builder = DeclarationBuilder::new(arena);
        let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
        MarkedDeclaration::new(AdmissionMark::Checked, declaration)
    }

    /// The decoded body root of the definition at `position`, or `None` when no
    /// declaration decoded there or the one that did is not a definition.
    ///
    /// # Specification
    /// - requires: nothing; `position` may name no declaration.
    /// - ensures: returns the body root of the definition at `position`, and
    ///   `None` both when no declaration decoded there and when the one that
    ///   did is not a definition.
    /// - provides: the projection the round-trip assertions read, keeping the
    ///   two absences from being confused with a decoded root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes shared child identity, independent
    ///   declarations with equal content, exact chain entry counts and both
    ///   sides of the work and table caps. The predicates walk the constructed
    ///   shapes without encoding or allocating a comparison arena; bounded
    ///   walks distinguish a repeated edge from a different child and stop on a
    ///   wrong former.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
    #[spec(
        ensures: |ret| ret == artifact.declarations().get(position.0).and_then(|marked| match *marked.declaration().content() { DeclarationContent::Def { body, .. } => Some(body), DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => None }),
    )]
    fn decoded_body(
        artifact: &DecodedArtifact,
        position: Position,
    ) -> Option<ValueId>
    {
        let declaration = artifact.declarations().get(position.0)?;
        match *declaration.declaration().content() {
            | DeclarationContent::Def { body, .. } => Some(body),
            | DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => None,
        }
    }

    /// The declared-type root of the declaration at `position`, or `None` when
    /// no declaration decoded there.
    ///
    /// # Specification
    /// - requires: nothing; `position` may name no declaration.
    /// - ensures: returns the declared-type root of the declaration at
    ///   `position`, and `None` when no declaration decoded there.
    /// - provides: the projection that reads the root every declaration kind
    ///   carries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes shared child identity, independent
    ///   declarations with equal content, exact chain entry counts and both
    ///   sides of the work and table caps. The predicates walk the constructed
    ///   shapes without encoding or allocating a comparison arena; bounded
    ///   walks distinguish a repeated edge from a different child and stop on a
    ///   wrong former.
    /// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `sharing_format::sharing_format::the_declaration_work_boundary_accepts_under_and_refuses_over`
    /// - witness: `sharing_format::sharing_format::the_table_entry_boundary_accepts_under_and_refuses_over`
    #[spec(
        ensures: |ret| ret == artifact.declarations().get(position.0).map(|marked| marked.declaration().declared_id()),
    )]
    fn decoded_declared(
        artifact: &DecodedArtifact,
        position: Position,
    ) -> Option<ValueTypeId>
    {
        let declaration = artifact.declarations().get(position.0)?;
        Some(declaration.declaration().declared_id())
    }

    // ---------------------------------------------------------------------------
    // Sharing: the round trip and the determinism
    // ---------------------------------------------------------------------------

    #[test]
    fn diamond_arithmetic_saturates_at_the_tree_size_boundary()
    {
        for depth in [0_u32, 1, 7, 31, 62, 63, 64, 127, 128, u32::MAX] {
            let power = 1_u128.checked_shl(depth).unwrap_or(u128::MAX);
            assert_eq!(
                u64::from(power_of_two(Depth(depth))),
                u64::try_from(power).unwrap_or(u64::MAX)
            );
            let tree = depth
                .checked_add(1)
                .and_then(|shift| 1_u128.checked_shl(shift))
                .map_or(u128::MAX, |power| power.saturating_sub(1));
            assert_eq!(
                u64::from(diamond_expanded(Depth(depth))),
                u64::try_from(tree).unwrap_or(u64::MAX)
            );
            assert_eq!(
                Depth(depth).next().0,
                u32::try_from(u64::from(depth).saturating_add(1)).unwrap_or(u32::MAX)
            );
        }
        for cap in [2_u64, 3, 4, 7, 8, u64::MAX.saturating_sub(1), u64::MAX] {
            let expected = (0_u32 .. 64)
                .filter(|&depth| {
                    1_u128
                        .checked_shl(depth.saturating_add(1))
                        .is_some_and(|size| size <= u128::from(cap))
                })
                .max()
                .expect("a unit diamond plus its declared type fits");
            assert_eq!(
                diamond_depth_within(ExpandedWork::from(cap)),
                Depth(expected)
            );
        }
    }

    #[test]
    fn sharing_round_trips_with_sharing_at_the_shared_nodes()
    {
        let mut arena = TermArena::new();

        // The first declaration's body shares one unit value with itself.
        let first_declared = arena.value_type_unit();
        let shared = arena.value_unit();
        let first_body = arena.value_pair(shared, shared);
        let first = definition_over(&mut arena, first_declared, first_body);

        // The second declaration mints its own structurally equal nodes, so any
        // sharing the artifact shows between the two is the format's rather than a
        // consequence of how this arena happened to be built.
        let second_declared = arena.value_type_unit();
        let second_body = arena.value_unit();
        let second = definition_over(&mut arena, second_declared, second_body);

        let declarations = vec![first, second];
        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("a well-formed artifact decodes");

        let re_encoded = encode(artifact.arena(), artifact.declarations());
        assert_eq!(
            Vec::from(bytes),
            Vec::from(re_encoded),
            "the decoded artifact re-encodes to the bytes it came from"
        );

        let first_body =
            decoded_body(&artifact, Position(0)).expect("the first definition decodes");
        let second_body =
            decoded_body(&artifact, Position(1)).expect("the second definition decodes");
        match artifact.arena().value(first_body) {
            | Some(&Value::Pair(left, right)) => {
                assert_eq!(
                    left, right,
                    "the shared pair children decode to one arena id"
                );
                assert_eq!(
                    left, second_body,
                    "the second declaration's unit is the first's very node"
                );
            },
            | other => panic!("the first body decodes to a pair, not {other:?}"),
        }

        assert_eq!(
            decoded_declared(&artifact, Position(0)).expect("the first declaration decodes"),
            decoded_declared(&artifact, Position(1)).expect("the second declaration decodes"),
            "the two declared types share one entry across declaration segments"
        );
        assert_eq!(
            TableEntryCount::from(3),
            artifact.metrics().table_entries(),
            "the unit type, the unit value and the pair are the whole table"
        );
    }

    #[test]
    fn differently_shared_equal_inputs_write_identical_bytes()
    {
        let shared_bytes = {
            let mut arena = TermArena::new();
            let declared = arena.value_type_unit();
            let unit = arena.value_unit();
            let body = arena.value_pair(unit, unit);
            let declarations = vec![definition_over(&mut arena, declared, body)];
            Vec::from(encode(&arena, &declarations))
        };
        let unshared_bytes = {
            let mut arena = TermArena::new();
            let declared = arena.value_type_unit();
            let left = arena.value_unit();
            let right = arena.value_unit();
            let body = arena.value_pair(left, right);
            let declarations = vec![definition_over(&mut arena, declared, body)];
            Vec::from(encode(&arena, &declarations))
        };
        assert_eq!(
            shared_bytes, unshared_bytes,
            "the bytes are a function of the abstract environment, not of how it shares in memory"
        );
    }

    /// The dependent arrow round-trips, and it does **not** collapse onto the
    /// non-dependent arrow over the same two children.
    ///
    /// The deduplication key is an entry's own bytes, so the two formers stay
    /// two entries exactly because they carry two tags. A shared tag would
    /// have merged the ambient-context codomain with the under-a-binder
    /// one, which is the collapse the settled numbering exists to prevent.
    #[test]
    fn a_dependent_arrow_round_trips_and_stays_distinct_from_the_arrow()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit_type);
        let dependent = arena.comp_type_pi(unit_type, returner);
        let plain = arena.comp_type_arrow(unit_type, returner);
        let dependent_declared = arena.value_type_thunk(dependent);
        let plain_declared = arena.value_type_thunk(plain);
        let body = arena.value_unit();
        let declarations = vec![
            definition_over(&mut arena, dependent_declared, body),
            definition_over(&mut arena, plain_declared, body),
        ];

        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("the dependent artifact decodes");
        let re_encoded = encode(artifact.arena(), artifact.declarations());
        assert_eq!(
            Vec::from(bytes),
            Vec::from(re_encoded),
            "the decoded dependent arrow re-encodes to the bytes it came from"
        );

        let decoded_dependent =
            decoded_declared(&artifact, Position(0)).expect("the dependent declaration decodes");
        let decoded_plain =
            decoded_declared(&artifact, Position(1)).expect("the plain declaration decodes");
        assert_ne!(
            decoded_dependent, decoded_plain,
            "the two arrows over the same children are two entries, so their thunks are two nodes"
        );
        let (Some(&ValueType::Thunk(dependent)), Some(&ValueType::Thunk(plain))) = (
            artifact.arena().value_type(decoded_dependent),
            artifact.arena().value_type(decoded_plain),
        )
        else {
            panic!("both declared types decode to thunks");
        };
        match (
            artifact.arena().comp_type(dependent),
            artifact.arena().comp_type(plain),
        ) {
            | (
                Some(&CompType::Pi { domain, codomain }),
                Some(&CompType::Arrow {
                    domain: plain_domain,
                    codomain: plain_codomain,
                }),
            ) => {
                assert_eq!(
                    domain, plain_domain,
                    "the domain is one shared entry across the two formers"
                );
                assert_eq!(
                    codomain, plain_codomain,
                    "and so is the codomain: only the tag separates them"
                );
            },
            | other => {
                panic!("the two formers decode to a dependent and a plain arrow, not {other:?}")
            },
        }
    }

    /// The dependent arrow's children carry the arrow's polarities: a
    /// value-type domain and a computation-type codomain. Offering the
    /// codomain a value type is refused at the polarity site rather than
    /// minted.
    #[test]
    fn a_dependent_arrow_refuses_a_mis_polarized_codomain()
    {
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            vec![
                entry_unit_type(),
                entry_pi(TableIndex(0), TableIndex(0)),
                entry_unit_type(),
            ],
            TableIndex(2),
        )]);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::Polarity,
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "a value type offered as a dependent codomain is a polarity refusal"
        );
    }

    /// A type that mentions a bound variable through a code round-trips,
    /// sharing the code with the term that produced it.
    ///
    /// This is the edge that leaves the type language: the declared type
    /// reaches a *value*, so the subterm table's single index space is
    /// carrying a type-to-term reference rather than only type-to-type
    /// ones.
    #[test]
    fn a_type_mentioning_a_code_round_trips()
    {
        let mut arena = TermArena::new();
        let level = gandr_kernel_strata::Level::zero();
        let universe = arena.value_type_universe(GroundSort::Value, level.clone());
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(code, level);
        let returner = arena.comp_type_returner(element);
        let dependent = arena.comp_type_pi(universe, returner);
        let declared = arena.value_type_thunk(dependent);
        let body_value = arena.value_variable(DeBruijnIndex::from(0_u32));
        let inner = arena.computation_return(body_value);
        let lambda = arena.computation_lambda(inner);
        let body = arena.value_thunk(lambda);
        let declarations = vec![definition_over(&mut arena, declared, body)];

        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("the code-carrying artifact decodes");
        assert_eq!(
            Vec::from(bytes),
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "the decoded artifact re-encodes to the bytes it came from"
        );

        let decoded_declared =
            decoded_declared(&artifact, Position(0)).expect("the declaration decodes");
        let Some(&ValueType::Thunk(decoded_pi)) = artifact.arena().value_type(decoded_declared)
        else {
            panic!("the declared type decodes to a thunk");
        };
        let Some(&CompType::Pi { codomain, .. }) = artifact.arena().comp_type(decoded_pi)
        else {
            panic!("over a dependent arrow");
        };
        let Some(&CompType::Returner(result)) = artifact.arena().comp_type(codomain)
        else {
            panic!("whose codomain returns");
        };
        let Some(&ValueType::Element { code, .. }) = artifact.arena().value_type(result)
        else {
            panic!("a type read off a code");
        };
        assert_eq!(
            Some(&Value::Variable(DeBruijnIndex::from(0_u32))),
            artifact.arena().value(code),
            "the code is the bound variable the type was written against"
        );

        // And it is the *same entry* as the variable the body returns: the subterm
        // table's single index space shares across the type-to-term boundary, which
        // is the payoff of one table over four.
        let decoded_body = decoded_body(&artifact, Position(0)).expect("the definition decodes");
        let Some(&Value::Thunk(decoded_lambda)) = artifact.arena().value(decoded_body)
        else {
            panic!("the body decodes to a thunk");
        };
        let Some(&Computation::Lambda(decoded_inner)) =
            artifact.arena().computation(decoded_lambda)
        else {
            panic!("holding a lambda");
        };
        let Some(&Computation::Return(returned)) = artifact.arena().computation(decoded_inner)
        else {
            panic!("whose body returns");
        };
        assert_eq!(
            code, returned,
            "the code and the returned variable are one entry"
        );
    }

    /// The static formers read their two children back in wire order: a
    /// static Pi's domain before its codomain, a static application's head
    /// before its argument. Each pair is chosen distinct, so a decoder that
    /// swapped them would re-encode the same bytes and still fail the shape
    /// check below.
    #[test]
    fn a_static_family_round_trips_in_wire_order()
    {
        let mut arena = TermArena::new();
        let level = gandr_kernel_strata::Level::zero();
        let values = arena.value_type_universe(GroundSort::Value, level.clone());
        let computations = arena.value_type_universe(GroundSort::Computation, level.clone());
        let family = arena.value_type_static_pi(values, computations);
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let integer = arena.value_type_base(BaseType::Integer);
        let argument = arena.value_quote(integer);
        let instance = arena.value_static_application(head, argument);
        let decoded_instance = arena.comp_type_element(instance, level);
        let declared = arena.value_type_thunk(decoded_instance);
        let declarations = vec![
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), family),
            ),
            MarkedDeclaration::new(
                AdmissionMark::Checked,
                DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), declared),
            ),
        ];

        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("the static family decodes");
        assert_eq!(
            Vec::from(bytes),
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "the decoded artifact re-encodes to the bytes it came from"
        );
        let decoded = artifact.arena();
        let family = decoded_declared(&artifact, Position(0)).expect("the family decodes");
        let Some(&ValueType::StaticPi { domain, codomain }) = decoded.value_type(family)
        else {
            panic!("the family's classifier decodes to a static Pi");
        };
        assert_eq!(
            (
                Some(&ValueType::Universe {
                    sort: GroundSort::Value,
                    level: gandr_kernel_strata::Level::zero(),
                }),
                Some(&ValueType::Universe {
                    sort: GroundSort::Computation,
                    level: gandr_kernel_strata::Level::zero(),
                }),
            ),
            (decoded.value_type(domain), decoded.value_type(codomain)),
            "the domain reads back before the codomain"
        );
        let declared = decoded_declared(&artifact, Position(1)).expect("the instance decodes");
        let Some(&ValueType::Thunk(element)) = decoded.value_type(declared)
        else {
            panic!("the instance's type decodes to a thunk");
        };
        let Some(&CompType::Element { code, .. }) = decoded.comp_type(element)
        else {
            panic!("over a decode");
        };
        let Some(&Value::StaticApplication(head, argument)) = decoded.value(code)
        else {
            panic!("whose code is a static application");
        };
        assert_eq!(
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            decoded.value(head),
            "the head reads back before the argument"
        );
        assert!(
            matches!(decoded.value(argument), Some(&Value::Quote(_))),
            "and the argument is the quoted code"
        );
    }

    #[test]
    fn the_empty_sequence_encodes_to_a_bare_header()
    {
        let arena = TermArena::new();
        let bytes = encode(&arena, &[]);
        // Hand check of the version field: the version is 2, which as a
        // little-endian sixteen-bit field is the low byte 0x02 first and the
        // high byte 0x00 after. The header is the four-byte magic, that
        // two-byte field, the empty atom table as one varint zero and the
        // declaration count as one varint zero.
        assert_eq!(
            vec![b'G', b'K', b'X', b'1', 0x02, 0x00, 0x00, 0x00],
            Vec::from(bytes.clone()),
            "the empty artifact is the magic, the version, an empty atom table and a zero count"
        );
        let artifact = decode(bytes.as_image()).expect("the empty artifact decodes");
        assert!(
            artifact.declarations().is_empty(),
            "the empty artifact decodes to no declarations"
        );
        assert_eq!(
            TableEntryCount::from(0),
            artifact.metrics().table_entries(),
            "the empty artifact has an empty table"
        );
    }

    /// The decoder reports each segment's end where the hand-built bytes put
    /// it: the header's after the declaration count, and each declaration's
    /// after its last slot, sharing across the segments notwithstanding.
    #[test]
    fn each_segment_ends_where_its_bytes_end()
    {
        let header = raw_artifact(current_version(), &[], &[]);
        let empty = decode(ArtifactImage::from(header.as_ref())).expect("the bare header decodes");
        assert_eq!(
            ByteOffset::from(header.0.len()),
            empty.segments().header_end(),
            "a bare header ends at the image's end"
        );
        assert!(
            empty.segments().declaration_ends().is_empty(),
            "a bare header has no declaration segment"
        );

        // The axiom's declared type is the definition's entry zero, so its own
        // segment introduces no entry and its bytes still delimit it.
        let definition = RawDeclaration::definition(
            vec![entry_unit_type(), entry_unit()],
            TableIndex(0),
            TableIndex(1),
        );
        let axiom = RawDeclaration::axiom(Vec::new(), TableIndex(0));
        let first_end = header.0.len().saturating_add(definition.bytes().0.len());
        let second_end = first_end.saturating_add(axiom.bytes().0.len());
        let bytes = raw_artifact(current_version(), &[], &[definition, axiom]);
        let artifact =
            decode(ArtifactImage::from(bytes.as_ref())).expect("the two segments decode");
        assert_eq!(
            ByteOffset::from(header.0.len()),
            artifact.segments().header_end(),
            "the header ends after the declaration count"
        );
        assert_eq!(
            [ByteOffset::from(first_end), ByteOffset::from(second_end)].as_slice(),
            artifact.segments().declaration_ends(),
            "each declaration ends after its own last slot"
        );
        assert_eq!(
            bytes.0.len(),
            second_end,
            "the last segment ends at the image's end"
        );
    }

    #[test]
    fn a_bypass_admission_mark_survives_the_round_trip()
    {
        let mut arena = TermArena::new();
        let declared = arena.value_type_unit();
        let body = arena.value_unit();
        let builder = DeclarationBuilder::new(&mut arena);
        let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
        let declarations = vec![MarkedDeclaration::new(
            AdmissionMark::UncheckedBypass,
            declaration,
        )];
        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("the bypass artifact decodes");
        assert_eq!(
            AdmissionMark::UncheckedBypass,
            artifact
                .declarations()
                .first()
                .expect("the declaration decodes")
                .mark(),
            "the bypass mark rides in the bytes rather than being re-derived"
        );
    }

    // ---------------------------------------------------------------------------
    // The four canonical-form refusals
    // ---------------------------------------------------------------------------

    /// The refusal a non-canonical artifact takes.
    ///
    /// # Specification
    /// trivial.
    fn non_canonical() -> DecodeError
    {
        DecodeError::Malformed {
            site: MalformedSite::NonCanonical,
        }
    }

    #[test]
    fn a_duplicate_entry_is_refused_as_non_canonical()
    {
        let entries = vec![
            entry_unit_type(),
            entry_unit(),
            entry_unit(),
            entry_pair(TableIndex(1), TableIndex(2)),
        ];
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::definition(
            entries,
            TableIndex(0),
            TableIndex(3),
        )]);
        assert_eq!(
            Err(non_canonical()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "two structurally equal entries are not maximal sharing"
        );
    }

    #[test]
    fn a_mis_ordered_table_is_refused_as_non_canonical()
    {
        // Every child reference is still strictly earlier, so this is a genuine
        // ordering violation rather than a child-order one.
        let entries = vec![
            entry_unit(),
            entry_unit_type(),
            entry_pair(TableIndex(0), TableIndex(0)),
        ];
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::definition(
            entries,
            TableIndex(1),
            TableIndex(2),
        )]);
        assert_eq!(
            Err(non_canonical()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "any permutation of the table re-encodes to a different index assignment"
        );
    }

    #[test]
    fn a_dead_entry_is_refused_as_non_canonical()
    {
        let entries = vec![
            entry_unit_type(),
            entry_unit(),
            entry_pair(TableIndex(1), TableIndex(1)),
            entry_variable(WireValue(7)),
        ];
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::definition(
            entries,
            TableIndex(0),
            TableIndex(2),
        )]);
        assert_eq!(
            Err(non_canonical()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "an entry no declaration root reaches re-encodes away"
        );
    }

    /// The decoding rule fires on the wire too: a table that writes a decode
    /// over a quote reads back as the quoted type, so its re-encoding drops
    /// both entries and the artifact is not canonical. The redex is no more
    /// representable in bytes than in an arena.
    #[test]
    fn a_decode_of_a_quote_is_refused_as_non_canonical()
    {
        let mut quote = Bytes::new();
        quote.byte(RawByte(0x1C));
        quote.varint(WireValue(0));
        let mut element = Bytes::new();
        element.byte(RawByte(0x19));
        element.varint(WireValue(0));
        element.varint(WireValue(0));
        element.varint(WireValue(1));
        let entries = vec![entry_unit_type(), quote, element];
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            entries,
            TableIndex(2),
        )]);
        assert_eq!(
            Err(non_canonical()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "a decoded quote is the quoted type, which the table wrote twice over"
        );
    }

    #[test]
    fn a_self_or_forward_child_reference_is_refused()
    {
        let child_order = DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        };
        let self_reference = raw_artifact(current_version(), &[], &[RawDeclaration::definition(
            vec![entry_pair(TableIndex(0), TableIndex(0))],
            TableIndex(0),
            TableIndex(0),
        )]);
        assert_eq!(
            Err(child_order),
            decode(ArtifactImage::from(self_reference.as_ref())),
            "an entry naming itself is not strictly earlier than itself"
        );

        let forward_reference =
            raw_artifact(current_version(), &[], &[RawDeclaration::definition(
                vec![entry_pair(TableIndex(1), TableIndex(1)), entry_unit()],
                TableIndex(0),
                TableIndex(0),
            )]);
        assert_eq!(
            Err(child_order),
            decode(ArtifactImage::from(forward_reference.as_ref())),
            "an entry naming a later entry breaks topological order"
        );
    }

    // ---------------------------------------------------------------------------
    // The amplification goldens
    // ---------------------------------------------------------------------------

    #[test]
    fn a_repeated_diamond_is_refused_before_any_consumer()
    {
        let depth = diamond_depth_within(MAX_EXPANDED_TERM_WORK).next();
        let mut arena = TermArena::new();
        let declared = arena.value_type_unit();
        let body = diamond(&mut arena, depth);
        let declarations = vec![definition_over(&mut arena, declared, body)];
        let bytes = encode(&arena, &declarations);

        assert!(
            Vec::from(bytes.clone()).len() < 200,
            "the artifact is a few dozen bytes: the amplification is in its expansion, not its size"
        );
        assert!(
            diamond_expanded(depth) > MAX_EXPANDED_TERM_WORK,
            "the golden really does exceed the per-declaration budget"
        );
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::ExpandedWork,
            }),
            decode(bytes.as_image()),
            "an over-budget declaration yields no artifact at all, so nothing downstream sees it"
        );
    }

    #[test]
    fn many_cheap_segments_sharing_one_root_are_refused()
    {
        let depth = diamond_depth_within(MAX_EXPANDED_TERM_WORK);
        let per_declaration = u64::from(diamond_expanded(depth)).saturating_add(1);
        let accepted = u64::from(MAX_ARTIFACT_EXPANDED_WORK)
            .checked_div(per_declaration)
            .expect("the per-declaration cost is nonzero");

        let build = |count: u64| {
            let mut arena = TermArena::new();
            let declared = arena.value_type_unit();
            let body = diamond(&mut arena, depth);
            let mut declarations: Vec<MarkedDeclaration> = Vec::new();
            let mut remaining = count;
            while remaining > 0 {
                declarations.push(definition_over(&mut arena, declared, body));
                remaining = remaining.saturating_sub(1);
            }
            Vec::from(encode(&arena, &declarations))
        };

        let under = build(accepted);
        let artifact = decode(ArtifactImage::from(under.as_slice()))
            .expect("the artifact-total budget accepts its own boundary");
        assert_eq!(
            MAX_ARTIFACT_EXPANDED_WORK,
            artifact.metrics().artifact_expanded_work(),
            "the accepted boundary sits exactly at the artifact cap"
        );

        let over = build(accepted.saturating_add(1));
        assert!(
            over.len() < 400,
            "each extra segment costs a handful of bytes while forcing a whole budget's work"
        );
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::ArtifactExpandedWork,
            }),
            decode(ArtifactImage::from(over.as_slice())),
            "the artifact total closes the hole no per-declaration bound can see"
        );
    }

    // ---------------------------------------------------------------------------
    // The boundary goldens, derived from the constants
    // ---------------------------------------------------------------------------

    #[test]
    fn the_declaration_work_boundary_accepts_under_and_refuses_over()
    {
        let under = diamond_depth_within(MAX_EXPANDED_TERM_WORK);
        let over = under.next();

        let build = |depth: Depth| {
            let mut arena = TermArena::new();
            let declared = arena.value_type_unit();
            let body = diamond(&mut arena, depth);
            let declarations = vec![definition_over(&mut arena, declared, body)];
            Vec::from(encode(&arena, &declarations))
        };

        let accepted = build(under);
        let artifact = decode(ArtifactImage::from(accepted.as_slice()))
            .expect("the largest in-budget declaration is accepted");
        assert_eq!(
            diamond_expanded(under),
            artifact.metrics().max_declaration_expanded_work(),
            "the metric reports the expanded size the shape actually has"
        );

        let refused = build(over);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::ExpandedWork,
            }),
            decode(ArtifactImage::from(refused.as_slice())),
            "one level deeper crosses the per-declaration cap"
        );
    }

    #[test]
    fn the_table_entry_boundary_accepts_under_and_refuses_over()
    {
        let cap = usize::from(MAX_TABLE_ENTRIES);
        // A chain of `links` steps contributes `1 + 2 * links` entries; the body
        // contributes the rest, so the entry count lands exactly on the cap.
        let links = LinkCount(
            cap.saturating_sub(2)
                .checked_div(2)
                .expect("a chain step contributes two entries"),
        );

        let build = |body_is_a_pair: bool| {
            let mut arena = TermArena::new();
            let declared = type_chain(&mut arena, links);
            let unit = arena.value_unit();
            let body = if body_is_a_pair {
                arena.value_pair(unit, unit)
            }
            else {
                unit
            };
            let declarations = vec![definition_over(&mut arena, declared, body)];
            Vec::from(encode(&arena, &declarations))
        };

        let accepted = build(false);
        let artifact = decode(ArtifactImage::from(accepted.as_slice()))
            .expect("a table exactly at the entry cap is accepted");
        assert_eq!(
            MAX_TABLE_ENTRIES,
            artifact.metrics().table_entries(),
            "the accepted boundary sits exactly at the entry cap"
        );

        let refused = build(true);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::TableSize,
            }),
            decode(ArtifactImage::from(refused.as_slice())),
            "one entry past the cap is refused as the entries accrue"
        );
    }

    #[test]
    fn the_level_offset_boundary_accepts_under_and_refuses_over()
    {
        let cap = u64::from(MAX_DECODED_LEVEL_OFFSET);

        let mut level = gandr_kernel_strata::Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0),
        ));
        let mut remaining = cap.saturating_sub(1);
        while remaining > 0 {
            level = level
                .succ()
                .expect("a level offset below the cap is representable");
            remaining = remaining.saturating_sub(1);
        }
        let mut arena = TermArena::new();
        let declared = arena.value_type_universe(GroundSort::Value, level);
        let builder = DeclarationBuilder::new(&mut arena);
        let declaration = builder.axiom(LevelSignature::monomorphic(), declared);
        let declarations = vec![MarkedDeclaration::new(AdmissionMark::Checked, declaration)];
        let accepted = encode(&arena, &declarations);
        let artifact =
            decode(accepted.as_image()).expect("an atom offset just under the cap is accepted");
        assert_eq!(
            1,
            artifact.declarations().len(),
            "the accepted level artifact carries its one declaration"
        );

        let refused = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            vec![entry_universe_atom(WireValue(0), WireValue(cap))],
            TableIndex(0),
        )]);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::LevelOffset,
            }),
            decode(ArtifactImage::from(refused.as_ref())),
            "an atom offset at the cap demands unbounded reconstruction and is refused"
        );
    }

    // ---------------------------------------------------------------------------
    // The version refusal and the totality properties
    // ---------------------------------------------------------------------------

    #[test]
    fn a_predecessor_version_is_refused_by_name()
    {
        let bytes = raw_artifact(Version(1), &[], &[]);
        assert_eq!(
            Err(DecodeError::UnsupportedVersion {
                found: FormatVersion::from(1),
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "a predecessor version is named rather than guessed at"
        );

        let future = raw_artifact(Version(3), &[], &[]);
        assert_eq!(
            Err(DecodeError::UnsupportedVersion {
                found: FormatVersion::from(3),
            }),
            decode(ArtifactImage::from(future.as_ref())),
            "a later version is refused with the version it declared"
        );
    }

    #[test]
    fn a_foreign_magic_is_refused_at_the_header()
    {
        let bytes = vec![b'N', b'O', b'P', b'E', 0x02, 0x00, 0x00, 0x00];
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::Header,
            }),
            decode(ArtifactImage::from(bytes.as_slice())),
            "bytes that are not a gandr kernel export are refused at the magic"
        );
    }

    #[test]
    fn truncation_at_every_prefix_is_refused_without_panicking()
    {
        let mut arena = TermArena::new();
        let declared = arena.value_type_unit();
        let unit = arena.value_unit();
        let body = arena.value_pair(unit, unit);
        let declarations = vec![definition_over(&mut arena, declared, body)];
        let bytes = Vec::from(encode(&arena, &declarations));

        let mut length = 0_usize;
        while length < bytes.len() {
            let prefix = bytes.get(.. length).expect("a prefix of the artifact");
            assert!(
                decode(ArtifactImage::from(prefix)).is_err(),
                "the artifact truncated to {length} bytes is refused rather than accepted"
            );
            length = length.saturating_add(1);
        }
        assert!(
            decode(ArtifactImage::from(bytes.as_slice())).is_ok(),
            "the whole artifact is accepted, so the truncation sweep is not vacuous"
        );
    }

    #[test]
    fn arbitrary_bytes_never_panic()
    {
        // A deterministic sweep: every one-byte and two-byte image, then a
        // scattering of longer ones that begin with the magic, built from a linear
        // congruential sequence so the case is reproducible.
        let mut first = 0_u16;
        while first < 256 {
            let byte = u8::try_from(first).unwrap_or(0);
            let _ignored = decode(ArtifactImage::from([byte].as_slice()));
            let _ignored = decode(ArtifactImage::from([byte, byte].as_slice()));
            first = first.saturating_add(1);
        }

        let mut state = 0x2545_f491_4f6c_dd1d_u64;
        let mut trial = 0_u32;
        while trial < 512 {
            let mut bytes: Vec<u8> = b"GKX1".to_vec();
            let mut remaining = 24_u32;
            while remaining > 0 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                bytes.push(u8::try_from(state.wrapping_shr(33) & 0xff).unwrap_or(0));
                remaining = remaining.saturating_sub(1);
            }
            let _ignored = decode(ArtifactImage::from(bytes.as_slice()));
            trial = trial.saturating_add(1);
        }
    }

    #[test]
    fn trailing_bytes_are_refused()
    {
        let arena = TermArena::new();
        let mut bytes = Vec::from(encode(&arena, &[]));
        bytes.push(0x00);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::TrailingBytes,
            }),
            decode(ArtifactImage::from(bytes.as_slice())),
            "an artifact is the whole image, not a prefix of it"
        );
    }

    // ---------------------------------------------------------------------------
    // The closed vocabulary: unknown tags, reserved kinds, reserved slots
    // ---------------------------------------------------------------------------

    #[test]
    fn an_unassigned_node_tag_is_refused_by_name()
    {
        // Both ends of the reserved sharing block, and the first byte above
        // it, where the frozen block resumes now that the growth room is spent.
        // The settled numbering assigns the block but this crate emits no entry
        // carrying one, so a reader meeting one refuses it exactly as it
        // refuses any other unassigned byte — the reservation is a numbering
        // claim, never a parse.
        let unassigned = [
            RawByte(u8::from(SHARING_BLOCK_FIRST)),
            RawByte(u8::from(SHARING_BLOCK_LAST)),
            RawByte(
                u8::from(SHARING_BLOCK_LAST)
                    .checked_add(1)
                    .expect("the block ends below the byte ceiling"),
            ),
        ];
        for tag in unassigned {
            let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
                vec![entry_unassigned_tag(tag)],
                TableIndex(0),
            )]);
            assert_eq!(
                Err(DecodeError::UnknownTag {
                    site: TagSite::Node,
                    tag: WireTag::from(tag.0),
                }),
                decode(ArtifactImage::from(bytes.as_ref())),
                "the space above the frozen block is a named refusal, never a mis-parse"
            );
        }
    }

    #[test]
    fn a_reserved_declaration_kind_is_refused_distinctly()
    {
        let reserved = [
            (RawByte(3), ReservedKind::ModuleSig),
            (RawByte(4), ReservedKind::ModuleDef),
            (RawByte(5), ReservedKind::FunctorDef),
        ];
        for (byte, kind) in reserved {
            let mut declaration = RawDeclaration::axiom(vec![entry_unit_type()], TableIndex(0));
            declaration.kind = byte;
            let bytes = raw_artifact(current_version(), &[], &[declaration]);
            assert_eq!(
                Err(DecodeError::ReservedDeclarationKind { kind }),
                decode(ArtifactImage::from(bytes.as_ref())),
                "a reserved kind is refused as reserved rather than as unknown"
            );
        }

        let mut unknown = RawDeclaration::axiom(vec![entry_unit_type()], TableIndex(0));
        unknown.kind = RawByte(9);
        let bytes = raw_artifact(current_version(), &[], &[unknown]);
        assert_eq!(
            Err(DecodeError::UnknownTag {
                site: TagSite::DeclarationKind,
                tag: WireTag::from(9),
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "a kind byte outside the reserved block is an unknown tag"
        );
    }

    #[test]
    fn an_unknown_admission_mark_is_refused()
    {
        let mut declaration = RawDeclaration::axiom(vec![entry_unit_type()], TableIndex(0));
        declaration.mark = RawByte(7);
        let bytes = raw_artifact(current_version(), &[], &[declaration]);
        assert_eq!(
            Err(DecodeError::UnknownTag {
                site: TagSite::Admission,
                tag: WireTag::from(7),
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "the admission bit is one of exactly two bytes"
        );
    }

    /// Segment text, the empty text among it: any characters but the
    /// separator, from an alphabet narrow enough that generated names collide.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the returned strategy generates zero to three Unicode scalar
    ///   values excluding the ASCII name separator; empty text and repeated
    ///   segments are permitted.
    /// - provides: short, collision-prone segment inputs while retaining the
    ///   full Unicode scalar alphabet as a choice.
    /// - panics: none during construction.
    /// - executable: none — the returned opaque strategy has no pure observer
    ///   for all future generated or shrunk values; running a value tree
    ///   requires a mutable random runner. The property consumes the strategy
    ///   and checks its semantic consequences instead of sampling inside a
    ///   postcondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 varies Unicode segment lists, including empty segments
    ///   and collisions, while comparing names as lists and each declaration’s
    ///   content, mark, levels and provenance with the unnamed baseline.
    ///   Structural predicates separately pin the baseline’s cycling kinds and
    ///   the predecessor reference in each later definition; the round trip is
    ///   an agreement check, not independent evidence for every wire byte.
    /// - witness: `sharing_format::sharing_format::a_structured_name_round_trips_as_segments`
    fn segment_text() -> impl Strategy<Value = String>
    {
        proptest::collection::vec(
            prop_oneof![Just('a'), Just('b'), Just('ß'), any::<char>()]
                .prop_filter("a segment holds no separator", |character| {
                    *character != NameSegment::SEPARATOR
                }),
            0 ..= 3,
        )
        .prop_map(|characters| characters.into_iter().collect())
    }

    /// A count-driven sequence over one arena, cycling through a definition,
    /// an axiom and an abstract type; later definitions read their predecessor.
    ///
    /// # Specification
    /// - requires: successful allocation within the arena’s index capacity.
    ///   Count may be zero.
    /// - ensures: returns count unnamed, monomorphic, checked-mark declarations
    ///   in definition, axiom, abstract-type order, each declared at the unit
    ///   type. The first definition has a unit body; each later definition
    ///   refers to the immediately preceding admission position.
    /// - provides: a name-independent baseline containing predecessor
    ///   references. Axioms and abstract types themselves do not reference
    ///   their predecessors; the generator is not a well-typed admission proof.
    /// - panics: if the arena exhausts its representable index space.
    ///
    /// # Adequacy
    /// - hypothesis: L3 varies Unicode segment lists, including empty segments
    ///   and collisions, while comparing names as lists and each declaration’s
    ///   content, mark, levels and provenance with the unnamed baseline.
    ///   Structural predicates separately pin the baseline’s cycling kinds and
    ///   the predecessor reference in each later definition; the round trip is
    ///   an agreement check, not independent evidence for every wire byte.
    /// - witness: `sharing_format::sharing_format::a_structured_name_round_trips_as_segments`
    #[spec(
        ensures: |ret| ret.len() == count.0
                && ret.iter().enumerate().all(|(position, marked)| marked.mark() == AdmissionMark::Checked
                && u32::from(marked.declaration().levels().params()) == 0
                && marked.declaration().levels().constraints().is_empty()
                && marked.declaration().name().segments().is_empty()
                && marked.declaration().provenance().is_empty()
                && arena.value_type(marked.declaration().declared_id()) == Some(&ValueType::Unit)
                && match *marked.declaration().content() { DeclarationContent::Def { body, .. } => position.rem_euclid(3) == 0
                && arena.value(body).is_some_and(|value| position.checked_sub(1).map_or(value == &Value::Unit,
            |previous| value == &Value::Constant(ConstantIndex::from(previous)))), DeclarationContent::Axiom { .. } => position.rem_euclid(3) == 1, DeclarationContent::AbstractType { .. } => position.rem_euclid(3) == 2 }),
    )]
    fn referencing_sequence(
        arena: &mut TermArena,
        count: Position,
    ) -> Vec<MarkedDeclaration>
    {
        let mut declarations = Vec::new();
        for position in 0 .. count.0 {
            let previous = position.checked_sub(1).map(ConstantIndex::from);
            let mut builder = DeclarationBuilder::new(arena);
            let reference = match previous {
                | Some(previous) => builder.arena().value_constant(previous),
                | None => builder.arena().value_unit(),
            };
            let declared = builder.arena().value_type_unit();
            let declaration = match position % 3 {
                | 0 => builder.def(LevelSignature::monomorphic(), declared, reference),
                | 1 => builder.axiom(LevelSignature::monomorphic(), declared),
                | _ => builder.abstract_type(LevelSignature::monomorphic(), declared),
            };
            declarations.push(MarkedDeclaration::new(AdmissionMark::Checked, declaration));
        }
        declarations
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// Generated segment lists survive the round trip as lists, and naming
        /// a sequence changes nothing its declarations hold: the decoded arena
        /// and every content root are the unnamed sequence's, so a reference
        /// reads the admission position whatever the names are.
        #[test]
        fn a_structured_name_round_trips_as_segments(
            names in proptest::collection::vec(
                proptest::collection::vec(segment_text(), 0 ..= 4),
                1 ..= 6,
            )
        ) {
            let mut arena = TermArena::new();
            let unnamed = referencing_sequence(&mut arena, Position(names.len()));
            let named: Vec<MarkedDeclaration> = unnamed
                .iter()
                .zip(&names)
                .map(|(marked, segments)| {
                    let name = StructuredName::from(
                        segments
                            .iter()
                            .map(|text| NameSegment::from_text(text.clone()))
                            .collect::<Option<Vec<NameSegment>>>()
                            .expect("generated text holds no separator"),
                    );
                    MarkedDeclaration::new(marked.mark(), marked.declaration().clone().named(name))
                })
                .collect();

            let named_bytes = encode(&arena, &named);
            let decoded_named = decode(named_bytes.as_image()).expect("a named artifact decodes");
            let decoded_unnamed =
                decode(encode(&arena, &unnamed).as_image()).expect("an unnamed artifact decodes");

            let decoded_names: Vec<Vec<&str>> = decoded_named
                .declarations()
                .iter()
                .map(|marked| {
                    marked.declaration().name().segments().iter().map(AsRef::as_ref).collect()
                })
                .collect();
            let written_names: Vec<Vec<&str>> = names
                .iter()
                .map(|segments| segments.iter().map(String::as_str).collect())
                .collect();
            prop_assert_eq!(written_names, decoded_names);
            prop_assert_eq!(decoded_unnamed.arena(), decoded_named.arena());
            for (named, unnamed) in decoded_named.declarations().iter().zip(decoded_unnamed.declarations()) {
                prop_assert_eq!(named.mark(), unnamed.mark());
                prop_assert_eq!(named.declaration().levels(), unnamed.declaration().levels());
                prop_assert_eq!(named.declaration().content(), unnamed.declaration().content());
                prop_assert_eq!(named.declaration().provenance(), unnamed.declaration().provenance());
            }
            prop_assert_eq!(named_bytes, encode(decoded_named.arena(), decoded_named.declarations()));
        }
    }

    #[test]
    fn a_segment_holding_a_separator_is_refused()
    {
        // At encode: the only constructor refuses the separator, so the
        // encoder's input cannot carry one.
        for dotted in [".lead", "mid.dle", "trail.", "."] {
            assert_eq!(
                None,
                NameSegment::from_text(String::from(dotted)),
                "`{dotted}` holds the separator and is no segment"
            );
        }
        let bare = NameSegment::from_text(String::from("middle"))
            .expect("the bare spelling one character away is a segment");
        assert_eq!("middle", bare.as_ref());

        // At decode: the same spelling written by hand into the name record.
        let named = |segment: &[u8]| {
            let mut declaration = RawDeclaration::axiom(vec![entry_unit_type()], TableIndex(0));
            declaration.name = vec![Bytes(segment.to_vec())];
            raw_artifact(current_version(), &[], &[declaration])
        };
        let refused = Err(DecodeError::Malformed {
            site: MalformedSite::NameSegment,
        });
        assert_eq!(
            refused,
            decode(ArtifactImage::from(named(b"mid.dle").as_ref())),
            "a dotted segment on the wire is refused at the name-segment site"
        );
        assert_eq!(
            refused,
            decode(ArtifactImage::from(named(&[0xff]).as_ref())),
            "a segment that is not UTF-8 is refused at the same site"
        );
        let decoded = decode(ArtifactImage::from(named(b"middle").as_ref()))
            .expect("the bare segment decodes");
        let segments: Vec<&str> = decoded
            .declarations()
            .first()
            .expect("the declaration decodes")
            .declaration()
            .name()
            .segments()
            .iter()
            .map(AsRef::as_ref)
            .collect();
        assert_eq!(vec!["middle"], segments);
    }

    #[test]
    fn an_occupied_reserved_slot_is_refused_by_name()
    {
        let mut erased = RawDeclaration::definition(
            vec![entry_unit_type(), entry_unit()],
            TableIndex(0),
            TableIndex(1),
        );
        erased.erasure = WireValue(1);
        let bytes = raw_artifact(current_version(), &[], &[erased]);
        assert_eq!(
            Err(DecodeError::ReservedSlotOccupied {
                slot: ReservedSlot::ErasureAnnotation,
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "an occupied erasure slot is refused at the slot that carried it"
        );
    }

    #[test]
    fn a_child_of_the_wrong_polarity_is_refused()
    {
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::definition(
            vec![entry_unit_type(), entry_pair(TableIndex(0), TableIndex(0))],
            TableIndex(0),
            TableIndex(1),
        )]);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::Polarity,
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "polarity is recoverable from the tag alone, so a value slot refuses a type"
        );
    }

    // ---------------------------------------------------------------------------
    // The minted-atom table is refuted rather than believed
    // ---------------------------------------------------------------------------

    /// A sealed artifact: an abstract type at position zero, a definition after
    /// it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the fixed canonical artifact with an abstract type at
    ///   position zero and a checked definition after it, with one minted-atom
    ///   position.
    /// - provides: a baseline with a nonempty atom table, pinned by literal
    ///   bytes rather than a second encoder invocation.
    /// - panics: none under successful allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_sealed_artifact_round_trips_with_its_atom_table`
    #[spec(
        ensures: |ret| ret.as_image().as_ref() == [b'G', b'K', b'X', b'1', 2, 0, 1, 0, 2, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0x0b, 1, 2, 0, 0, 0, 0].as_slice(),
    )]
    fn sealed_artifact() -> EncodedArtifact
    {
        let mut arena = TermArena::new();
        let kind = arena.value_type_universe(GroundSort::Value, gandr_kernel_strata::Level::zero());
        let builder = DeclarationBuilder::new(&mut arena);
        let atom = builder.abstract_type(LevelSignature::monomorphic(), kind);
        let declared = arena.value_type_unit();
        let body = arena.value_unit();
        let definition = definition_over(&mut arena, declared, body);
        let declarations = vec![
            MarkedDeclaration::new(AdmissionMark::Checked, atom),
            definition,
        ];
        encode(&arena, &declarations)
    }

    /// The sealed artifact's bytes with its declared atom table replaced.
    ///
    /// The header the sealed artifact writes is the magic, the version, a
    /// one-byte table count and one one-byte position, so its tail begins
    /// at the eighth byte.
    ///
    /// # Specification
    /// - requires: nothing; `atoms` may disagree with the artifact's own
    ///   declarations, which is the point.
    /// - ensures: returns the sealed artifact's bytes with the magic, the
    ///   current version, and `atoms` in place of the original header, and the
    ///   original tail from the eighth byte onward.
    /// - provides: the artifact whose declared table is false while every other
    ///   byte is unchanged, so a refusal isolates the table rather than the
    ///   surrounding shape.
    /// - panics: panics when the sealed artifact is shorter than eight bytes,
    ///   which its own header precludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 accepted and malformed artifacts use this independent
    ///   fixture writer to isolate header, field-order, reference and
    ///   canonical-form decisions. Literal encoder and decoder fixtures
    ///   separately pin the frozen bytes; shared round trips alone are not an
    ///   independent oracle. The refusal witnesses vary one field while
    ///   retaining the surrounding record.
    /// - witness: `sharing_format::sharing_format::a_minted_atom_table_with_a_repeat_is_refused`
    /// - witness: `sharing_format::sharing_format::a_minted_atom_table_omitting_an_atom_is_refused`
    /// - witness: `sharing_format::sharing_format::a_minted_atom_table_naming_a_definition_is_refused`
    #[spec(
        ensures: |ret| ret.0.starts_with(b"GKX1")
                && ret.0.get(4 .. 6) == Some([2_u8, 0].as_slice())
                && { let count = u64::try_from(atoms.len()).unwrap_or(u64::MAX);
            let valid_count = { let scalar = count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get(6_usize .. (6_usize).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) };
            if valid_count { atoms.iter().try_fold((6_usize).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |position, atom| { ({ let scalar = atom.0;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            ret.0.as_slice().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }).then_some(position.saturating_add(usize::try_from(64_u32.saturating_sub((atom.0).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }) }
            else { None } }.is_some_and(|position| ret.0.get(position ..) == Some([2_u8, 0, 2, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0x0b, 1, 2, 0, 0, 0, 0].as_slice())),
    )]
    fn sealed_with_atom_table(atoms: &[WireValue]) -> Bytes
    {
        let original = Bytes(Vec::from(sealed_artifact()));
        let mut bytes = Bytes::new();
        bytes.magic();
        bytes.version(current_version());
        bytes.varint(WireValue(u64::try_from(atoms.len()).unwrap_or(u64::MAX)));
        for &atom in atoms {
            bytes.varint(atom);
        }
        bytes.append_tail(&original, Position(8));
        bytes
    }

    /// The refusal a refuted atom table takes.
    ///
    /// # Specification
    /// trivial.
    fn refuted_atom_table() -> DecodeError
    {
        DecodeError::ReservedSlotOccupied {
            slot: ReservedSlot::MintedAtomTable,
        }
    }

    #[test]
    fn a_sealed_artifact_round_trips_with_its_atom_table()
    {
        let bytes = sealed_artifact();
        let artifact = decode(bytes.as_image()).expect("a sealed artifact decodes");
        let first = artifact
            .declarations()
            .first()
            .expect("the atom declaration decodes");
        assert!(
            matches!(
                *first.declaration().content(),
                DeclarationContent::AbstractType { .. }
            ),
            "an atom decodes as an atom rather than as an axiom"
        );
        assert_eq!(
            Vec::from(bytes),
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "the sealed artifact re-encodes to the bytes it came from"
        );
    }

    #[test]
    fn a_minted_atom_table_with_a_repeat_is_refused()
    {
        let bytes = sealed_with_atom_table(&[WireValue(0), WireValue(0)]);
        assert_eq!(
            Err(refuted_atom_table()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "two atoms cannot occupy one admission position"
        );
    }

    #[test]
    fn a_minted_atom_table_omitting_an_atom_is_refused()
    {
        let bytes = sealed_with_atom_table(&[]);
        assert_eq!(
            Err(refuted_atom_table()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "an atom cannot be smuggled past the table"
        );
    }

    #[test]
    fn a_minted_atom_table_naming_a_definition_is_refused()
    {
        let bytes = sealed_with_atom_table(&[WireValue(1)]);
        assert_eq!(
            Err(refuted_atom_table()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "the table cannot conjure an atom the declarations do not contain"
        );
    }

    // ---------------------------------------------------------------------------
    // Universes and levels ride the same canonical discipline
    // ---------------------------------------------------------------------------

    #[test]
    fn a_non_canonical_inline_level_is_refused()
    {
        // The atom list names one variable twice. The level oracle's canonical form
        // keeps one atom per variable, so re-encoding writes one atom where the
        // artifact carried two.
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            vec![entry_universe_repeated_atom()],
            TableIndex(0),
        )]);
        assert_eq!(
            Err(non_canonical()),
            decode(ArtifactImage::from(bytes.as_ref())),
            "a level is rebuilt through its smart constructors, so a redundant atom re-encodes away"
        );
    }

    #[test]
    fn an_overlong_varint_inside_an_entry_is_refused()
    {
        let bytes = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            vec![entry_universe_overlong_constant()],
            TableIndex(0),
        )]);
        assert_eq!(
            Err(DecodeError::Malformed {
                site: MalformedSite::Varint,
            }),
            decode(ArtifactImage::from(bytes.as_ref())),
            "an overlong varint would be a second byte image of one value"
        );
    }

    #[test]
    fn a_universe_artifact_round_trips_byte_identically()
    {
        let mut arena = TermArena::new();
        let declared =
            arena.value_type_universe(GroundSort::Value, gandr_kernel_strata::Level::zero());
        let builder = DeclarationBuilder::new(&mut arena);
        let declaration = builder.axiom(LevelSignature::monomorphic(), declared);
        let declarations = vec![MarkedDeclaration::new(AdmissionMark::Checked, declaration)];
        let bytes = encode(&arena, &declarations);
        let artifact = decode(bytes.as_image()).expect("the universe artifact decodes");
        assert_eq!(
            Vec::from(bytes),
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "a decoded universe re-encodes identically"
        );
        // The entry shape the raw builders use must agree with what the encoder
        // writes, or every hand-built golden above would be testing a format the
        // encoder does not produce.
        let expected = raw_artifact(current_version(), &[], &[RawDeclaration::axiom(
            vec![entry_universe(WireValue(0))],
            TableIndex(0),
        )]);
        assert_eq!(
            expected.0,
            Vec::from(encode(artifact.arena(), artifact.declarations())),
            "the hand-built segment shape is the shape the encoder produces"
        );
    }
}
