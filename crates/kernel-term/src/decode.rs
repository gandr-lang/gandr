//! Structural and canonical-wire validation into a shared arena.
//!
//! # Table rows and arena identity
//!
//! Each complete wire entry appends one global row. A row resolves to a
//! family-specific arena id; it is not that id's numeric ordinal. Repeated
//! references reuse the same id. Element normalization can reuse a quoted
//! type's existing id instead of allocating another node; the final comparison
//! then rejects the reducible spelling.
//!
//! Entry decoding checks the frozen tag, strictly earlier child references,
//! slot polarity and table cap before committing its row. A failed entry leaves
//! the table unchanged, but a failed segment can retain earlier completed rows.
//! No partially decoded artifact is returned to the caller.
//!
//! # Acceptance and its limits
//!
//! A forward scan computes saturating expanded sizes from the wire edges and
//! checks both structural-work caps. The header's claimed atom positions are
//! compared with the decoded declaration kinds. Finally, the shared encoder
//! must reproduce the input bytes exactly: minimal integers, normalized
//! payloads, maximal sharing, first-completion order and absence of dead rows.
//!
//! This comparison is an implementation-level acceptance criterion, not an
//! independent proof of the format; literal fixtures constrain the shared
//! codec. It does not validate typing, parameter coverage, admission claims or
//! provenance truth. Structural expansion bounds are not bounds on evaluation
//! or all inline-payload work. Graph handling is iterative, while normalization
//! and ordered-map operations contribute their own costs.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::ConstraintRelation;
use gandr_kernel_strata::LandmarkConstraint;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::TermArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::BaseType;
use crate::base::FractionDigits;
use crate::base::IntegerLiteral;
use crate::base::Literal;
use crate::base::Magnitude;
use crate::base::NumericLiteral;
use crate::base::Sign;
use crate::base::StringLiteral;
use crate::budget::DecodeMetrics;
use crate::budget::ExpandedWork;
use crate::budget::GlobalIndex;
use crate::budget::LevelAtomOffset;
use crate::budget::MAX_ARTIFACT_EXPANDED_WORK;
use crate::budget::MAX_DECODED_LEVEL_OFFSET;
use crate::budget::MAX_EXPANDED_TERM_WORK;
use crate::budget::MAX_TABLE_ENTRIES;
use crate::budget::TableEntryCount;
use crate::decl::AdmissionMark;
use crate::decl::DeclarationBuilder;
use crate::decl::DeclarationContent;
use crate::decl::LevelParamCount;
use crate::decl::LevelSignature;
use crate::decl::MarkedDeclaration;
use crate::decl::MintedAtom;
use crate::decl::NameSegment;
use crate::decl::StructuredName;
use crate::encode::encode;
use crate::encode::minted_atoms;
use crate::error::DecodeError;
use crate::error::MalformedSite;
use crate::error::ReservedKind;
use crate::error::ReservedSlot;
use crate::error::TagSite;
use crate::tags;
use crate::term::ConstantIndex;
use crate::term::DeBruijnIndex;
use crate::term::Side;
use crate::types::GroundSort;
use crate::wire::ArtifactImage;
use crate::wire::ByteCount;
use crate::wire::ByteOffset;
use crate::wire::FormatVersion;
use crate::wire::WireByte;
use crate::wire::WireTag;
use crate::wire::WireU32;
use crate::wire::WireU64;
use crate::wire::WireUsize;

/// The polarity family of a decoded entry, read from its tag alone.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Family
{
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
    /// A value.
    Value,
    /// A computation.
    Computation,
}

/// A decoded entry's arena id, tagged by family.
///
/// # Specification
/// - requires: nothing; ids alone do not certify arena membership.
/// - ensures: distinguishes the four id families without implying that a global
///   table index is an arena ordinal.
/// - provides: family-tagged resolution results used by child and root checks.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[derive(Clone, Copy, Debug)]
enum DecodedNode
{
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
}

/// The running decode state for the global subterm table: the arena entries
/// mint into, and per-entry parallel vectors indexed by global index.
///
/// # Specification
/// - requires: decoding operations keep the parallel vectors aligned; child
///   indices describe the wire graph and are strictly earlier than their row.
/// - ensures: retains global-to-arena resolution, recorded families and ordered
///   wire children; normalized element rows may resolve to an existing arena
///   id.
/// - provides: the state shared by segment decoding, reference checks and the
///   expanded-work scan.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
struct Table
{
    /// The arena every entry mints into, sharing retained.
    arena: TermArena,
    /// Each entry's arena id.
    nodes: Vec<DecodedNode>,
    /// Each entry's polarity family, for the child-polarity check.
    families: Vec<Family>,
    /// Each entry's child global indices, for the expanded-size scan.
    children: Vec<Vec<GlobalIndex>>,
}

impl Table
{
    /// A fresh empty table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a table with an empty arena and no entries, so the
    ///   next global index is zero.
    /// - provides: the accumulator one artifact's entries fill; no state from
    ///   an earlier decode is reachable from it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 distinguishes all four reference families, exact
    ///   ordered child appends, self and forward references, polarity refusals
    ///   and complete former payloads against literal entries. It observes
    ///   sharing through resolved ids rather than assuming global indices equal
    ///   arena ordinals.
    /// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
    /// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
    #[spec(
        ensures: |ret| ret.nodes.is_empty()
                && ret.families.is_empty()
                && ret.children.is_empty()
                && ret.arena.watermark() == crate::arena::ArenaWatermark::default(),
    )]
    #[inline]
    fn new() -> Self
    {
        Self {
            arena: TermArena::new(),
            nodes: Vec::new(),
            families: Vec::new(),
            children: Vec::new(),
        }
    }

    /// The number of entries decoded so far, as the next global index.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the index the next entry will take, or the `u32`
    ///   ceiling on a table longer than the index space.
    /// - provides: the total, panic-free index for the entry about to be
    ///   decoded; the saturated index cannot alias entry zero, and the entry
    ///   cap is reached long before it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 distinguishes all four reference families, exact
    ///   ordered child appends, self and forward references, polarity refusals
    ///   and complete former payloads against literal entries. It observes
    ///   sharing through resolved ids rather than assuming global indices equal
    ///   arena ordinals. The entry cap prevents a decoded table from reaching
    ///   ordinal saturation; the scalar conversion boundary is separately
    ///   modeled in the arena witness.
    /// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
    /// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
    /// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
    #[spec(
        ensures: |ret| u32::from(ret) == u32::try_from(self.nodes.len()).unwrap_or(u32::MAX),
    )]
    #[inline]
    fn next_index(&self) -> GlobalIndex
    {
        GlobalIndex::from(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX))
    }
}

/// Which live declaration kind a decoded segment carried.
///
/// A missing body root does not distinguish them: an axiom and an abstract
/// type both decode to a single root and no body, and conflating the two would
/// silently turn every atom back into a hole on replay — inverting exactly the
/// distinction sealing exists to draw.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclKind
{
    /// A typed definition.
    Def,
    /// A tracked typed hole.
    Axiom,
    /// A sealed abstract type.
    AbstractType,
}

/// Per-declaration metadata gathered during decode, resolved to declarations
/// once the arena is built.
///
/// # Specification
/// - requires: nothing; this carrier alone does not validate roots or producer
///   claims.
/// - ensures: holds the decoded kind, mark, name, level interface, roots and
///   provenance until assembly. Individual consumers establish their own root
///   requirements.
/// - provides: declaration metadata kept separate from table construction and
///   final root resolution.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 literal artifact fixtures and named malformed-input
///   boundaries observe header and segment framing, sharing, producer claims
///   and refusal precedence. Generated round trips show codec agreement, not an
///   independent proof of the format or arbitrary-input totality; small-stack
///   depth witnesses cover iterative graph handling.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `sharing_format::sharing_format::each_segment_ends_where_its_bytes_end`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
/// - witness: `decode::tests::declaration_assembly_preserves_claims_and_consumes_names`
struct DeclMeta
{
    /// The admission mark.
    mark: AdmissionMark,
    /// Which live kind the segment carried.
    kind: DeclKind,
    /// The structured name the segment's name record carried.
    name: StructuredName,
    /// The prenex level signature.
    levels: LevelSignature,
    /// The declared value type's global index, which is an abstract type's
    /// kind.
    root_declared: GlobalIndex,
    /// The body value's global index, for a definition only.
    root_body: Option<GlobalIndex>,
    /// The sealing-provenance slot's atoms, for a definition only.
    provenance: Vec<ConstantIndex>,
}

/// Where the decoder found an artifact's segments, as offsets into the image it
/// read: the end of the header and the end of each declaration segment.
///
/// The header is the magic, the version, the minted-atom table and the
/// declaration count; segment `i` runs from the end before it — the header's
/// for the first — to its own end. The offsets are the reader's: a consumer
/// that stores the segments apart takes their boundaries from a decode, never
/// from the writer that handed it the bytes.
///
/// # Specification
/// - requires: nothing; a default layout has no source image.
/// - ensures: a decode-produced layout records the header and strictly
///   increasing declaration ends in its source image; the default is zero with
///   no declaration ends.
/// - provides: reader-derived segment boundaries, not an independently
///   authenticated image association.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 literal artifact fixtures and named malformed-input
///   boundaries observe header and segment framing, sharing, producer claims
///   and refusal precedence. Generated round trips show codec agreement, not an
///   independent proof of the format or arbitrary-input totality; small-stack
///   depth witnesses cover iterative graph handling.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `sharing_format::sharing_format::each_segment_ends_where_its_bytes_end`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SegmentLayout
{
    /// The offset one past the header's last byte.
    header_end: ByteOffset,
    /// The offset one past each declaration segment's last byte, in admission
    /// order.
    declaration_ends: Vec<ByteOffset>,
}

impl SegmentLayout
{
    /// The offset one past the header's last byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn header_end(&self) -> ByteOffset
    {
        self.header_end
    }

    /// The offset one past each declaration segment's last byte, in admission
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declaration_ends(&self) -> &[ByteOffset]
    {
        &self.declaration_ends
    }
}

/// A fully decoded artifact.
///
/// It holds the arena its declarations' content lives in, the
/// admission-ordered declaration sequence addressing it, the deterministic
/// budget metrics computed en route, and where each segment sat in the bytes.
///
/// # Specification
/// - requires: nothing; Default constructs empty state rather than evidence
///   that input bytes were accepted.
/// - ensures: decode-produced values hold the checked structural graph,
///   declaration claims, metrics and source boundaries; producer typing and
///   admission claims remain unverified.
/// - provides: the decoder result container; successful decode, not this type
///   alone, establishes acceptance.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 literal artifact fixtures and named malformed-input
///   boundaries observe header and segment framing, sharing, producer claims
///   and refusal precedence. Generated round trips show codec agreement, not an
///   independent proof of the format or arbitrary-input totality; small-stack
///   depth witnesses cover iterative graph handling.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `sharing_format::sharing_format::each_segment_ends_where_its_bytes_end`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DecodedArtifact
{
    /// The arena every decoded declaration's content lives in.
    arena: TermArena,
    /// The decoded declarations, in admission order.
    declarations: Vec<MarkedDeclaration>,
    /// The deterministic decode-budget metrics.
    metrics: DecodeMetrics,
    /// Where the header and each declaration segment ended.
    segments: SegmentLayout,
}

impl DecodedArtifact
{
    /// The arena the declarations' content was decoded into.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &TermArena
    {
        &self.arena
    }

    /// The decoded declarations, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> &[MarkedDeclaration]
    {
        &self.declarations
    }

    /// The deterministic decode-budget metrics.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn metrics(&self) -> DecodeMetrics
    {
        self.metrics
    }

    /// Where the header and each declaration segment ended in the decoded
    /// image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn segments(&self) -> &SegmentLayout
    {
        &self.segments
    }
}

/// Decode an artifact image into its declaration sequence and shared arena.
///
/// # Specification
/// - requires: nothing; image may be arbitrary or adversarial.
/// - ensures: success yields a complete structural parse with supported header,
///   live tags, earlier polarity-correct references, bounded table size and
///   expanded work, a refuted minted-atom table and bytes identical to
///   re-encoding the normalized graph. Sharing is retained. Segment ends are
///   strictly increasing, one per declaration, with the final end equal to the
///   input length.
/// - provides: structural and canonical-wire acceptance, not typing,
///   producer-admission evidence, provenance truth or an overall evaluator-work
///   bound. The predicate checks returned metrics and layout; literal fixtures
///   independently constrain the encoder shared by the final comparison.
/// - fails: a named `DecodeError` for the first observed header, field,
///   reference, structural-budget, atom-table or canonical-form refusal.
/// - panics: none for representable input storage under successful allocation.
/// - intension: term-table parsing and the expanded-work scan are iterative.
///   Inline-payload normalization and tree-map re-encoding have their own
///   payload-dependent costs; the whole operation is not linear in entry count
///   alone.
///
/// # Errors
/// Any [`DecodeError`].
///
/// # Adequacy
/// - hypothesis: L3 literal artifact fixtures and named malformed-input
///   boundaries observe header and segment framing, sharing, producer claims
///   and refusal precedence. Generated round trips show codec agreement, not an
///   independent proof of the format or arbitrary-input totality; small-stack
///   depth witnesses cover iterative graph handling.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `sharing_format::sharing_format::each_segment_ends_where_its_bytes_end`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
/// - witness: `decode::tests::budget_scan_matches_explicit_expansion_and_saturating_boundaries`
/// - witness: `sharing_format::sharing_format::a_repeated_diamond_is_refused_before_any_consumer`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
/// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
/// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_mis_ordered_table_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_dead_entry_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|artifact|
    artifact.metrics.table_entries() <= MAX_TABLE_ENTRIES
        && artifact.metrics.max_declaration_expanded_work() <= MAX_EXPANDED_TERM_WORK
        && artifact.metrics.artifact_expanded_work() <= MAX_ARTIFACT_EXPANDED_WORK
        && artifact.segments.declaration_ends.len() == artifact.declarations.len()
        && core::iter::once(artifact.segments.header_end)
            .chain(artifact.segments.declaration_ends.iter().copied())
            .zip(artifact.segments.declaration_ends.iter().copied())
            .all(|(start, end)| start < end)
        && artifact.segments.declaration_ends.last().copied()
            .unwrap_or(artifact.segments.header_end) == image.length()))]
pub fn decode(image: ArtifactImage<'_>) -> Result<DecodedArtifact, DecodeError>
{
    let mut reader = ByteReader::new(image);
    reader.expect_magic()?;
    reader.expect_version()?;
    let declared_atoms = reader.read_minted_atom_table()?;
    let count = reader.read_uvarint()?;
    let header_end = reader.position;
    let mut table = Table::new();
    let mut metas: Vec<DeclMeta> = Vec::new();
    let mut declaration_ends: Vec<ByteOffset> = Vec::new();
    let mut remaining = u64::from(count);
    while remaining > 0_u64 {
        let meta = decode_declaration(&mut reader, &mut table)?;
        metas.push(meta);
        declaration_ends.push(reader.position);
        remaining = remaining.wrapping_sub(1_u64);
    }
    if reader.position < image.length() {
        return Err(DecodeError::Malformed {
            site: MalformedSite::TrailingBytes,
        });
    }
    let metrics = budget_report(&table, &metas);
    check_budget(metrics)?;
    let declarations = build_declarations(&mut table, &mut metas);
    check_minted_atom_table(&declared_atoms, &declarations)?;
    if encode(&table.arena, &declarations).as_image() != image {
        return Err(DecodeError::Malformed {
            site: MalformedSite::NonCanonical,
        });
    }
    Ok(DecodedArtifact {
        arena: table.arena,
        declarations,
        metrics,
        segments: SegmentLayout {
            header_end,
            declaration_ends,
        },
    })
}

/// Compute the artifact's budget report in one forward scan of memoized
/// saturating expanded sizes.
///
/// # Specification
/// - requires: every entry's children are strictly earlier, which decode
///   checked as the entries accrued, so a forward scan resolves each child's
///   size before its parent's.
/// - ensures: the entry count, the maximum expanded size over every declaration
///   root, and the saturating sum of those root sizes — each a function of the
///   canonical bytes alone. An index that resolves to no entry contributes the
///   saturated ceiling, so a wiring defect refuses rather than under-reports.
/// - provides: the one scan both the acceptance gate and the telemetry read;
///   there is no second descent. The clauses check topological input order and
///   the exact entry count. Expanded sizes stay prose: the only available
///   derivation is this scan, whose memo vector would have to be allocated and
///   recomputed as a predicate.
/// - fails: never — a saturating scan is total.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 compares a small topological graph with explicit path
///   expansion rather than the memoized recurrence. L3 checks repeated roots,
///   missing roots, saturating diamonds and exact work-cap refusal precedence.
///   These observations concern structural wire expansion, not evaluator work
///   or inline-payload cost.
/// - witness: `decode::tests::budget_scan_matches_explicit_expansion_and_saturating_boundaries`
/// - witness: `sharing_format::sharing_format::a_repeated_diamond_is_refused_before_any_consumer`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
#[spec(
    requires: table.children.iter().enumerate().all(|(parent, children)|
        children.iter().all(|child| child.offset().0 < parent)),
    ensures: |ret| ret.table_entries() == TableEntryCount::from(table.nodes.len()),
)]
fn budget_report(
    table: &Table,
    metas: &[DeclMeta],
) -> DecodeMetrics
{
    let mut expanded: Vec<ExpandedWork> = Vec::with_capacity(table.children.len());
    for child_globals in &table.children {
        let mut size = ExpandedWork::ONE;
        for &child in child_globals {
            let child_size = expanded
                .get(child.offset().0)
                .copied()
                .unwrap_or_else(|| ExpandedWork::from(u64::MAX));
            size = size.saturating_add(child_size);
        }
        expanded.push(size);
    }
    let size_of = |global: GlobalIndex| -> ExpandedWork {
        expanded
            .get(global.offset().0)
            .copied()
            .unwrap_or_else(|| ExpandedWork::from(u64::MAX))
    };
    let mut largest = ExpandedWork::default();
    let mut total = ExpandedWork::default();
    for meta in metas {
        for root in core::iter::once(meta.root_declared).chain(meta.root_body) {
            let size = size_of(root);
            largest = largest.max(size);
            total = total.saturating_add(size);
        }
    }
    DecodeMetrics::new(TableEntryCount::from(table.nodes.len()), largest, total)
}

/// Refuse an artifact whose expanded work exceeds either work budget.
///
/// # Specification
/// - requires: nothing; metrics is the supplied report and this helper checks
///   its two work quantities only.
/// - ensures: accepts exactly when both work quantities are within their
///   respective caps, with per-root expanded work taking refusal precedence
///   over artifact-total work.
/// - provides: the structural-work comparison; table-entry limits are checked
///   separately as rows accrue.
/// - fails: `DecodeError::Malformed` at `MalformedSite::ExpandedWork` first,
///   then `MalformedSite::ArtifactExpandedWork`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 compares a small topological graph with explicit path
///   expansion rather than the memoized recurrence. L3 checks repeated roots,
///   missing roots, saturating diamonds and exact work-cap refusal precedence.
///   These observations concern structural wire expansion, not evaluator work
///   or inline-payload cost.
/// - witness: `decode::tests::budget_scan_matches_explicit_expansion_and_saturating_boundaries`
/// - witness: `sharing_format::sharing_format::a_repeated_diamond_is_refused_before_any_consumer`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
#[spec(
    ensures: |ret| if metrics.max_declaration_expanded_work() > MAX_EXPANDED_TERM_WORK { ret.as_ref() == Err(&DecodeError::Malformed { site: MalformedSite::ExpandedWork }) }
        else if metrics.artifact_expanded_work() > MAX_ARTIFACT_EXPANDED_WORK { ret.as_ref() == Err(&DecodeError::Malformed { site: MalformedSite::ArtifactExpandedWork }) }
        else { ret.is_ok() },
)]
fn check_budget(metrics: DecodeMetrics) -> Result<(), DecodeError>
{
    if metrics.max_declaration_expanded_work() > MAX_EXPANDED_TERM_WORK {
        return Err(DecodeError::Malformed {
            site: MalformedSite::ExpandedWork,
        });
    }
    if metrics.artifact_expanded_work() > MAX_ARTIFACT_EXPANDED_WORK {
        return Err(DecodeError::Malformed {
            site: MalformedSite::ArtifactExpandedWork,
        });
    }
    Ok(())
}

/// Refute the minted-atom table against the declarations decoded beside it.
///
/// The table is a claim the header makes about the segments, and this is where
/// that claim is checked rather than believed: the decoder re-derives the
/// ascending positions of the abstract-type declarations from the independently
/// decoded sequence and requires the table to be exactly that. One equality
/// decides three properties at once —
///
/// - **distinctness**, because the re-derived sequence is strictly ascending by
///   construction, so a table with a repeat cannot equal it and two atoms can
///   never share a position;
/// - **accounting**, because an abstract-type declaration missing from the
///   table makes the lengths differ, so no atom is smuggled past it;
/// - **no forgery**, because an entry naming a definition or an axiom, or
///   naming nothing at all, is not in the re-derived sequence.
///
/// What it does not establish, stated because the gap is easy to miss: this is
/// freshness *within one artifact*. Two independently produced artifacts can
/// both mint an atom at position zero, so cross-process uniqueness is a
/// different property that this table neither carries nor claims.
///
/// # Specification
/// - requires: `declarations` is the artifact's decoded sequence, in admission
///   order.
/// - ensures: acceptance exactly when `declared` equals the ascending positions
///   of the abstract-type declarations in `declarations`.
/// - provides: the freshness gate, decided from the bytes alone. Admission
///   history stays prose: positions encode sequence order, not an independently
///   observable admission event.
/// - fails: [`DecodeError::ReservedSlotOccupied`] at the minted-atom table on
///   any disagreement, so a wrong table is refused by name rather than by a
///   generic structural error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 uses literal record bytes with empty and nonempty names,
///   Unicode, out-of-order provenance, occupied reserved slots, invalid UTF-8
///   and maximal declared counts. It checks exact values, refusal sites and
///   cursor positions; it does not claim name normalization, atom truth or
///   typing. Separate sealed-artifact fixtures refute repeated, omitted and
///   non-minting positions against the decoded sequence, not against an assumed
///   admission history.
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
/// - witness: `sharing_format::sharing_format::a_sealed_artifact_round_trips_with_its_atom_table`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_with_a_repeat_is_refused`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_omitting_an_atom_is_refused`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_naming_a_definition_is_refused`
#[spec(ensures: |ret| ret.is_ok() == declared.iter().copied().eq(
    declarations.iter().enumerate().filter_map(|(position, declaration)|
        matches!(*declaration.declaration().content(),
            DeclarationContent::AbstractType { .. })
            .then_some(MintedAtom::from(position))),
))]
fn check_minted_atom_table(
    declared: &[MintedAtom],
    declarations: &[MarkedDeclaration],
) -> Result<(), DecodeError>
{
    if declared == minted_atoms(declarations).as_slice() {
        Ok(())
    }
    else {
        Err(DecodeError::ReservedSlotOccupied {
            slot: ReservedSlot::MintedAtomTable,
        })
    }
}

/// The value-type id at a global index, if the entry there is a value type.
///
/// # Specification
/// - requires: nothing; `global` may name no entry.
/// - ensures: returns the value-type id at that index, and `None` both when the
///   index names no entry and when the entry there is of another family.
/// - provides: the family-checked root resolution, so a declaration claiming a
///   value type cannot be handed a node of another polarity.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match nodes.get(global.offset().0) { Some(&DecodedNode::ValueType(id)) => Some(id), _ => None },
)]
#[inline]
fn value_type_id_at(
    nodes: &[DecodedNode],
    global: GlobalIndex,
) -> Option<ValueTypeId>
{
    match nodes.get(global.offset().0) {
        | Some(&DecodedNode::ValueType(id)) => Some(id),
        | _ => None,
    }
}

/// The value id at a global index, if the entry there is a value.
///
/// # Specification
/// - requires: nothing; `global` may name no entry.
/// - ensures: returns the value id at that index, and `None` both when the
///   index names no entry and when the entry there is of another family.
/// - provides: the family-checked root resolution for a definition's body.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match nodes.get(global.offset().0) { Some(&DecodedNode::Value(id)) => Some(id), _ => None },
)]
#[inline]
fn value_id_at(
    nodes: &[DecodedNode],
    global: GlobalIndex,
) -> Option<ValueId>
{
    match nodes.get(global.offset().0) {
        | Some(&DecodedNode::Value(id)) => Some(id),
        | _ => None,
    }
}

/// Resolve each declaration's roots to arena ids and build the sequence.
///
/// # Specification
/// - requires: declared roots resolve to live value types; exactly definitions
///   have a body root, and each such root resolves to a live value. The segment
///   decoder establishes these conditions.
/// - ensures: returns one declaration per metadata record in order, preserving
///   its mark, kind, roots and levels. Definition provenance is retained; other
///   forms have none. Names move to the declarations and leave empty source
///   names. The arena is unchanged.
/// - provides: assembly from already validated references, not recovery of
///   malformed root metadata or proof of producer claims.
/// - fails: never within the validated-root domain.
/// - panics: none within that domain.
///
/// # Adequacy
/// - hypothesis: L3 assembles all three declaration forms over distinguishable
///   shared prefix roots, preserving full level interfaces, marks and
///   definition provenance while moving empty and Unicode names out of the
///   metadata. A complete arena snapshot detects accidental reminting or prefix
///   mutation; this does not establish typing or producer-claim truth.
/// - witness: `decode::tests::declaration_assembly_preserves_claims_and_consumes_names`
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
#[spec(
    requires: metas.iter().all(|meta| value_type_id_at(&table.nodes, meta.root_declared).is_some_and(|id| table.arena.value_type(id).is_some())
            && match (meta.kind, meta.root_body) { (DeclKind::Def, Some(root)) => value_id_at(&table.nodes, root).is_some_and(|id| table.arena.value(id).is_some()), (DeclKind::Axiom | DeclKind::AbstractType, None) => true, _ => false }), captures: entry = (table.arena.watermark(), metas.iter().fold(0_usize,
        |total, meta| total.saturating_add(meta.name.segments().len()))),
    ensures: |ret| table.arena.watermark() == entry.0
            && ret.len() == metas.len()
            && metas.iter().all(|meta| meta.name.segments().is_empty())
            && ret.iter().fold(0_usize,
        |total, marked| total.saturating_add(marked.declaration().name().segments().len())) == entry.1
            && ret.iter().zip(metas.iter()).all(|(marked, meta)| marked.mark() == meta.mark
            && marked.declaration().levels() == &meta.levels
            && Some(marked.declaration().declared_id()) == value_type_id_at(&table.nodes, meta.root_declared)
            && match (*marked.declaration().content(), meta.kind, meta.root_body) { (DeclarationContent::Def { body, .. }, DeclKind::Def, Some(root)) => Some(body) == value_id_at(&table.nodes, root)
            && marked.declaration().provenance() == meta.provenance.as_slice(), (DeclarationContent::Axiom { .. }, DeclKind::Axiom, None) | (DeclarationContent::AbstractType { .. }, DeclKind::AbstractType, None) => marked.declaration().provenance().is_empty(), _ => false }),
)]
fn build_declarations(
    table: &mut Table,
    metas: &mut [DeclMeta],
) -> Vec<MarkedDeclaration>
{
    let mut declarations: Vec<MarkedDeclaration> = Vec::new();
    for meta in metas.iter_mut() {
        let declared_id = value_type_id_at(&table.nodes, meta.root_declared);
        let body_id = meta.root_body.map(|root| value_id_at(&table.nodes, root));
        let mut builder = DeclarationBuilder::new(&mut table.arena);
        let declared = declared_id.unwrap_or_else(|| builder.arena().value_type_unit());
        let declaration = match (meta.kind, body_id) {
            | (DeclKind::Def, Some(body_id)) => {
                let body = body_id.unwrap_or_else(|| builder.arena().value_unit());
                builder.sealed_def(meta.levels.clone(), declared, body, meta.provenance.clone())
            },
            | (DeclKind::AbstractType, _) => builder.abstract_type(meta.levels.clone(), declared),
            // A missing body reaches this arm only outside the validated
            // metadata domain. A present but unresolved id takes the unit
            // fallback above; enabled preconditions reject both states.
            | (DeclKind::Def | DeclKind::Axiom, _) => builder.axiom(meta.levels.clone(), declared),
        };
        declarations.push(MarkedDeclaration::new(
            meta.mark,
            declaration.named(core::mem::take(&mut meta.name)),
        ));
    }
    declarations
}

/// A forward byte cursor with bounds-checked reads: the decoder's totality
/// substrate, where an over-read surfaces as truncation rather than a panic.
///
/// # Specification
/// - requires: the private cursor stays within its borrowed image.
/// - ensures: retains one immutable image and a forward cursor; individual
///   reads specify whether failure consumes a prefix.
/// - provides: bounds-checked borrowed input and observable field-consumption
///   state.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; its
///   decoding, construction and lookup operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 compares cursor values, exact consumed offsets and borrowed
///   slice identity at empty, complete, truncated and overflowing ranges.
///   Header fixtures distinguish all-or-nothing magic reads from partial
///   version consumption. These finite boundaries do not prove every parser
///   composition.
/// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
pub struct ByteReader<'bytes>
{
    /// The artifact bytes.
    image: ArtifactImage<'bytes>,
    /// The next unread offset.
    position: ByteOffset,
}

impl<'bytes> ByteReader<'bytes>
{
    /// A cursor at the start of `image`.
    ///
    /// # Specification
    /// - requires: nothing; `image` may be arbitrary or adversarial.
    /// - ensures: returns a cursor whose next unread offset is zero.
    /// - provides: the one reading position over an image; every read advances
    ///   it, so no byte is read twice and none is skipped.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        ensures: |ret| ret.position.0 == 0
                && core::ptr::eq(&raw const *ret.image.as_ref(), &raw const *image.as_ref()),
    )]
    #[inline]
    pub(crate) fn new(image: ArtifactImage<'bytes>) -> Self
    {
        Self {
            image,
            position: ByteOffset::default(),
        }
    }

    /// Read one byte, or refuse as truncated at the end.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, returns the byte at the current offset and advances
    ///   the offset by one.
    /// - provides: the single-byte read every other read is built from; the
    ///   offset advances only on success, so a refusal leaves the cursor where
    ///   it was.
    /// - fails: [`DecodeError::Truncated`] at the end of the image, and on an
    ///   offset increment that would not be representable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        captures: start = self.position,
        ensures: |ret| match self.image.byte_at(start) { Some(byte) => ret.as_ref() == Ok(&byte)
                && self.position.0 == start.0.saturating_add(1), None => ret.as_ref() == Err(&DecodeError::Truncated)
                && self.position == start },
    )]
    #[inline]
    fn next_byte(&mut self) -> Result<WireByte, DecodeError>
    {
        let byte = self
            .image
            .byte_at(self.position)
            .ok_or(DecodeError::Truncated)?;
        let next = self
            .position
            .0
            .checked_add(1)
            .ok_or(DecodeError::Truncated)?;
        self.position = ByteOffset::from(next);
        Ok(byte)
    }

    /// Read one tag byte.
    ///
    /// # Specification
    /// - requires: the current position is a tagged position of the format.
    /// - ensures: on `Ok`, returns the byte at the current offset as a tag and
    ///   advances the offset by one.
    /// - provides: the read every tag alphabet is resolved from; the tag's
    ///   meaning is decided by the site the caller is at, never by the byte
    ///   alone.
    /// - fails: [`DecodeError::Truncated`] at the end of the image.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        captures: start = self.position,
        ensures: |ret| match self.image.byte_at(start) { Some(byte) => ret.as_ref() == Ok(&WireTag::from(byte))
                && self.position.0 == start.0.saturating_add(1), None => ret.as_ref() == Err(&DecodeError::Truncated)
                && self.position == start },
    )]
    #[inline]
    fn next_tag(&mut self) -> Result<WireTag, DecodeError>
    {
        let byte = self.next_byte()?;
        Ok(WireTag::from(byte))
    }

    /// Read `count` bytes as a borrowed image, or refuse as truncated.
    ///
    /// # Specification
    /// - requires: nothing; `count` may exceed the image.
    /// - ensures: on `Ok`, returns a borrow of exactly `count` bytes from the
    ///   current offset and advances the offset past them.
    /// - provides: the bounds-checked bulk read; the borrow is of the original
    ///   image, so no payload is copied to be inspected.
    /// - fails: [`DecodeError::Truncated`] when fewer than `count` bytes
    ///   remain, and on an offset sum that would not be representable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        captures: start = self.position,
        ensures: |ret| match start.0.checked_add(count.0).and_then(|end| self.image.as_ref().get(start.0 .. end)) { Some(bytes) => ret.as_ref().is_ok_and(|image| core::ptr::eq(&raw const *image.as_ref(), &raw const *bytes))
                && self.position.0 == start.0.saturating_add(count.0), None => ret.as_ref() == Err(&DecodeError::Truncated)
                && self.position == start },
    )]
    #[inline]
    fn take(
        &mut self,
        count: ByteCount,
    ) -> Result<ArtifactImage<'bytes>, DecodeError>
    {
        let end = self
            .position
            .0
            .checked_add(count.0)
            .ok_or(DecodeError::Truncated)?;
        let end = ByteOffset::from(end);
        let slice = self
            .image
            .span(self.position .. end)
            .ok_or(DecodeError::Truncated)?;
        self.position = end;
        Ok(slice)
    }

    /// Verify the four-byte magic.
    ///
    /// # Specification
    /// - requires: the cursor is at the start of the image.
    /// - ensures: on `Ok`, the four leading bytes were the format magic and the
    ///   offset is past them.
    /// - provides: the first refusal an unrelated byte string meets, so a
    ///   non-artifact is rejected before any length is believed.
    /// - fails: [`DecodeError::Truncated`] on fewer than four bytes;
    ///   [`DecodeError::Malformed`] at the header site when the bytes differ.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        requires: self.position.0 == 0, captures: start = self.position,
        ensures: |ret| match self.image.as_ref().get(start.0 .. start.0.saturating_add(tags::MAGIC.len())) { Some(bytes) => self.position.0 == start.0.saturating_add(tags::MAGIC.len())
                && if bytes == tags::MAGIC { ret.is_ok() }
            else { ret.as_ref() == Err(&DecodeError::Malformed { site: MalformedSite::Header }) }, None => self.position == start
                && ret.as_ref() == Err(&DecodeError::Truncated) },
    )]
    #[inline]
    fn expect_magic(&mut self) -> Result<(), DecodeError>
    {
        let head = self.take(ByteCount::from(tags::MAGIC.len()))?;
        if head.as_ref() == tags::MAGIC {
            Ok(())
        }
        else {
            Err(DecodeError::Malformed {
                site: MalformedSite::Header,
            })
        }
    }

    /// Verify the version, refusing any other by name.
    ///
    /// # Specification
    /// - requires: the cursor is positioned just past the magic.
    /// - ensures: on `Ok`, the two version bytes named the version this decoder
    ///   implements and the offset is past them.
    /// - provides: the version gate, which names the version it found rather
    ///   than reporting a generic malformation, so a future artifact is
    ///   distinguishable from a corrupt one.
    /// - fails: [`DecodeError::Truncated`] on fewer than two bytes;
    ///   [`DecodeError::UnsupportedVersion`] carrying the version found.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    #[spec(
        requires: self.position.0 == tags::MAGIC.len(), captures: start = self.position,
        ensures: |ret| match (self.image.byte_at(start), self.image.byte_at(ByteOffset::from(start.0.saturating_add(1)))) { (Some(low), Some(high)) => { let found = FormatVersion::from(u16::from_le_bytes([u8::from(low), u8::from(high)]));
            self.position.0 == start.0.saturating_add(2)
                && if found == tags::FORMAT_VERSION { ret.is_ok() }
            else { ret.as_ref() == Err(&DecodeError::UnsupportedVersion { found }) } }, (Some(_), None) => self.position.0 == start.0.saturating_add(1)
                && ret.as_ref() == Err(&DecodeError::Truncated), (None, _) => self.position == start
                && ret.as_ref() == Err(&DecodeError::Truncated) },
    )]
    #[inline]
    fn expect_version(&mut self) -> Result<(), DecodeError>
    {
        let low = self.next_byte()?;
        let high = self.next_byte()?;
        let found = FormatVersion::from(u16::from_le_bytes([u8::from(low), u8::from(high)]));
        if found == tags::FORMAT_VERSION {
            Ok(())
        }
        else {
            Err(DecodeError::UnsupportedVersion { found })
        }
    }

    /// Read the minted-atom table: a count followed by that many admission
    /// positions.
    ///
    /// Only the integers are read here; the table's truth is decided once the
    /// declarations have been decoded independently, because a claim checked
    /// against nothing is not checked. No capacity is reserved from the
    /// declared count. Allocation follows only positions actually decoded
    /// before a refusal.
    ///
    /// # Specification
    /// - requires: the cursor is positioned at the minted-atom table.
    /// - ensures: on `Ok`, returns exactly the declared number of admission
    ///   positions, in the order the bytes carry them, and advances past the
    ///   table.
    /// - provides: the declared table, read but not believed: its truth is
    ///   decided later against the decoded declarations, and no capacity is
    ///   reserved from the declared count; storage grows only after a position
    ///   has been decoded.
    /// - fails: [`DecodeError::Truncated`] when the bytes run out;
    ///   [`DecodeError::Malformed`] at the varint or index-range site.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 uses literal record bytes with empty and nonempty
    ///   names, Unicode, out-of-order provenance, occupied reserved slots,
    ///   invalid UTF-8 and maximal declared counts. It checks exact values,
    ///   refusal sites and cursor positions; it does not claim name
    ///   normalization, atom truth or typing.
    /// - witness: `decode::tests::counted_records_validate_content_and_consumption`
    #[spec(
        captures: start = self.position,
        ensures: |ret| self.position >= start
                && self.position <= self.image.length()
                && ret.as_ref().ok().is_none_or(|atoms| { let count = u64::try_from(atoms.len()).unwrap_or(u64::MAX);
            ({ let scalar = count;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && atoms.iter().try_fold((start.0).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
            |position, &atom| { let ordinal = u64::try_from(usize::from(atom)).unwrap_or(u64::MAX);
            ({ let scalar = ordinal;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }).then_some(position.saturating_add(usize::try_from(64_u32.saturating_sub((ordinal).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }) == Some(self.position.0) }),
    )]
    fn read_minted_atom_table(&mut self) -> Result<Vec<MintedAtom>, DecodeError>
    {
        let count = self.read_uvarint()?;
        let mut atoms: Vec<MintedAtom> = Vec::new();
        let mut remaining = u64::from(count);
        while remaining > 0_u64 {
            let atom = self.read_usize()?;
            atoms.push(MintedAtom::from(usize::from(atom)));
            remaining = remaining.wrapping_sub(1_u64);
        }
        Ok(atoms)
    }

    /// Read a minimal unsigned LEB128 varint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value of the unique minimal little-endian base-128
    ///   encoding of a 64-bit integer.
    /// - provides: the decoder's integer primitive, and half of the
    ///   one-image-per-value commitment the canonical-form comparison rests on.
    /// - fails: [`DecodeError::Truncated`] at the end;
    ///   [`DecodeError::Malformed`] at the varint site on an overlong encoding
    ///   — a redundant continuation, or more groups than 64 bits admit — since
    ///   an overlong encoding would be a second image of one value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares integer reads with an independent
    ///   division-based byte model at each seven-bit boundary; L3 pins
    ///   truncation, redundant groups, the tenth-bit limit and narrowing
    ///   refusal without losing consumed offsets. It does not infer
    ///   arbitrary-input totality from a round trip.
    /// - witness: `decode::tests::integer_fields_match_independent_boundary_bytes`
    /// - witness: `decode::tests::an_overlong_varint_is_refused`
    /// - witness: `decode::tests::a_truncated_varint_is_refused_as_truncation`
    #[spec(
        captures: entry_position = self.position,
        ensures: |ret| ret.as_ref().ok().is_none_or(|value|
            self.image.as_ref().get(entry_position.0 .. self.position.0)
                .is_some_and(|bytes| {
                    let value = u64::from(*value);
                    let groups = u64::BITS.saturating_sub(value.leading_zeros())
                        .saturating_add(6).checked_div(7).unwrap_or(0).max(1);
                    bytes.len() == usize::try_from(groups).unwrap_or(usize::MAX)
                        && bytes.iter().enumerate().all(|(position, byte)| {
                            let shift = u32::try_from(position).unwrap_or(u32::MAX)
                                .saturating_mul(7);
                            let payload = value.checked_shr(shift).unwrap_or(0) & 0x7f;
                            let continuation = if position.saturating_add(1) < bytes.len() {
                                0x80
                            } else {
                                0
                            };
                            u64::from(*byte) == payload | continuation
                        })
                })),
    )]
    pub(crate) fn read_uvarint(&mut self) -> Result<WireU64, DecodeError>
    {
        let overlong = DecodeError::Malformed {
            site: MalformedSite::Varint,
        };
        let mut result: u64 = 0;
        let mut shift: u32 = 0;
        let mut groups: u32 = 0;
        loop {
            let byte = self.next_byte()?;
            let byte = u8::from(byte);
            groups = groups.checked_add(1).ok_or(overlong)?;
            if groups > 10 {
                return Err(overlong);
            }
            let low = u64::from(byte & 0x7f);
            if shift == 63 && low > 1 {
                return Err(overlong);
            }
            let contribution = low.checked_shl(shift).ok_or(overlong)?;
            result |= contribution;
            if byte & 0x80 == 0 {
                if groups > 1 && byte == 0 {
                    return Err(overlong);
                }
                return Ok(WireU64::from(result));
            }
            shift = shift.checked_add(7).ok_or(overlong)?;
        }
    }

    /// Read a 32-bit value, refusing an out-of-range varint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, returns the varint's value when it fits a `u32`.
    /// - provides: the narrowing every table index and count is read through,
    ///   so an out-of-range value is a refusal rather than a truncated index.
    /// - fails: the varint read's own failures, and [`DecodeError::Malformed`]
    ///   at the index-range site when the value exceeds `u32::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares integer reads with an independent
    ///   division-based byte model at each seven-bit boundary; L3 pins
    ///   truncation, redundant groups, the tenth-bit limit and narrowing
    ///   refusal without losing consumed offsets. It does not infer
    ///   arbitrary-input totality from a round trip.
    /// - witness: `decode::tests::integer_fields_match_independent_boundary_bytes`
    /// - witness: `decode::tests::an_overlong_varint_is_refused`
    /// - witness: `decode::tests::a_truncated_varint_is_refused_as_truncation`
    #[spec(
        captures: start = self.position,
        ensures: |ret| self.position >= start
                && self.position <= self.image.length()
                && self.position.0 <= start.0.saturating_add(11)
                && ret.as_ref().ok().is_none_or(|value| { let value_word = u64::from(u32::from(*value));
            self.position.0 == start.0.saturating_add(usize::try_from(64_u32.saturating_sub((value_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))
                && ({ let scalar = value_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) }),
    )]
    #[inline]
    fn read_u32(&mut self) -> Result<WireU32, DecodeError>
    {
        let value = self.read_uvarint()?;
        u32::try_from(u64::from(value))
            .map(WireU32::from)
            .map_err(|_error| DecodeError::Malformed {
                site: MalformedSite::IndexRange,
            })
    }

    /// Read a host-sized value, refusing an out-of-range varint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on `Ok`, returns the varint's value when it fits a `usize`.
    /// - provides: the narrowing every length is read through, so a length
    ///   larger than the host can address is a refusal rather than a wrapped
    ///   count.
    /// - fails: the varint read's own failures, and [`DecodeError::Malformed`]
    ///   at the index-range site when the value exceeds `usize::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares integer reads with an independent
    ///   division-based byte model at each seven-bit boundary; L3 pins
    ///   truncation, redundant groups, the tenth-bit limit and narrowing
    ///   refusal without losing consumed offsets. It does not infer
    ///   arbitrary-input totality from a round trip.
    /// - witness: `decode::tests::integer_fields_match_independent_boundary_bytes`
    /// - witness: `decode::tests::an_overlong_varint_is_refused`
    /// - witness: `decode::tests::a_truncated_varint_is_refused_as_truncation`
    #[spec(
        captures: start = self.position,
        ensures: |ret| self.position >= start
                && self.position <= self.image.length()
                && self.position.0 <= start.0.saturating_add(11)
                && ret.as_ref().ok().is_none_or(|value| { let value_word = u64::try_from(usize::from(*value)).unwrap_or(u64::MAX);
            self.position.0 == start.0.saturating_add(usize::try_from(64_u32.saturating_sub((value_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))
                && ({ let scalar = value_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) }),
    )]
    #[inline]
    fn read_usize(&mut self) -> Result<WireUsize, DecodeError>
    {
        let value = self.read_uvarint()?;
        usize::try_from(u64::from(value))
            .map(WireUsize::from)
            .map_err(|_error| DecodeError::Malformed {
                site: MalformedSite::IndexRange,
            })
    }

    /// Read a global table index.
    ///
    /// # Specification
    /// - requires: the cursor is positioned at a table index.
    /// - ensures: on `Ok`, returns the index the bytes named; whether it names
    ///   an entry is decided by the caller.
    /// - provides: the typed read that keeps a table index from being crossed
    ///   with a count at a signature.
    /// - fails: the 32-bit read's own failures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares integer reads with an independent
    ///   division-based byte model at each seven-bit boundary; L3 pins
    ///   truncation, redundant groups, the tenth-bit limit and narrowing
    ///   refusal without losing consumed offsets. It does not infer
    ///   arbitrary-input totality from a round trip.
    /// - witness: `decode::tests::integer_fields_match_independent_boundary_bytes`
    /// - witness: `decode::tests::an_overlong_varint_is_refused`
    /// - witness: `decode::tests::a_truncated_varint_is_refused_as_truncation`
    #[spec(
        captures: start = self.position,
        ensures: |ret| self.position >= start
                && self.position <= self.image.length()
                && self.position.0 <= start.0.saturating_add(11)
                && ret.as_ref().ok().is_none_or(|value| { let value_word = u64::from(u32::from(*value));
            self.position.0 == start.0.saturating_add(usize::try_from(64_u32.saturating_sub((value_word).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))
                && ({ let scalar = value_word;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) }),
    )]
    #[inline]
    fn read_global(&mut self) -> Result<GlobalIndex, DecodeError>
    {
        let value = self.read_u32()?;
        Ok(GlobalIndex::from(u32::from(value)))
    }

    /// Read length-prefixed text through a validating UTF-8 conversion.
    ///
    /// # Specification
    /// - requires: the cursor is positioned at a length-prefixed text field.
    /// - ensures: on `Ok`, returns the field's bytes as owned text and advances
    ///   past them.
    /// - provides: the one validating conversion every text payload passes
    ///   through, so no invalid UTF-8 reaches a literal or a name.
    /// - fails: the length and bulk reads' own failures, and
    ///   [`DecodeError::Malformed`] at `site` on invalid UTF-8.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 compares cursor values, exact consumed offsets and
    ///   borrowed slice identity at empty, complete, truncated and overflowing
    ///   ranges. Header fixtures distinguish all-or-nothing magic reads from
    ///   partial version consumption. These finite boundaries do not prove
    ///   every parser composition. Counted-text fixtures also pin UTF-8
    ///   validation, caller-selected refusal sites and byte rather than
    ///   character lengths.
    /// - witness: `decode::tests::cursor_reads_preserve_borrows_and_refusal_positions`
    /// - witness: `decode::tests::counted_records_validate_content_and_consumption`
    #[spec(
        captures: start = self.position,
        ensures: |ret| self.position >= start
                && self.position <= self.image.length()
                && ret.as_ref().ok().is_none_or(|text| { let length = u64::try_from(text.len()).unwrap_or(u64::MAX);
            self.position.0 == start.0.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(text.len())
                && ({ let scalar = length;
            let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
            self.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
                && self.image.as_ref().get(self.position.0.saturating_sub(text.len()) .. self.position.0) == Some(text.as_bytes()) }),
    )]
    #[inline]
    fn read_text(
        &mut self,
        site: MalformedSite,
    ) -> Result<String, DecodeError>
    {
        let length = self.read_usize()?;
        let bytes = self.take(ByteCount::from(usize::from(length)))?;
        let text = core::str::from_utf8(bytes.as_ref())
            .map_err(|_error| DecodeError::Malformed { site })?;
        Ok(String::from(text))
    }
}

/// Decode one declaration segment: its header, its entries, and its roots.
///
/// # Specification
/// - requires: table is the running aligned state from earlier segments; input
///   bytes may be arbitrary.
/// - ensures: success appends this segment’s entries in wire order and returns
///   its mark, kind, name, level interface, family-correct live roots and
///   definition provenance. Exactly definitions have a body root.
/// - provides: segment parsing, not semantic validation of producer claims. On
///   failure the cursor and previously completed entries may have advanced;
///   this operation does not roll back an entire segment.
/// - fails: reserved or unknown kinds and marks, malformed names, occupied
///   reserved slots, and entry, level or root refusals.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 literal artifact fixtures and named malformed-input
///   boundaries observe header and segment framing, sharing, producer claims
///   and refusal precedence. Generated round trips show codec agreement, not an
///   independent proof of the format or arbitrary-input totality; small-stack
///   depth witnesses cover iterative graph handling. The declaration-assembly
///   witness separately observes metadata transfer, and the entry fixtures
///   prove local failure atomicity; a later segment failure can retain rows
///   from its earlier successful entries.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `sharing_format::sharing_format::each_segment_ends_where_its_bytes_end`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
/// - witness: `decode::tests::declaration_assembly_preserves_claims_and_consumes_names`
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|meta|
    meta.root_declared < table.next_index()
        && table.families.get(meta.root_declared.offset().0) == Some(&Family::ValueType)
        && match (meta.kind, meta.root_body) {
            (DeclKind::Def, Some(root)) => root < table.next_index()
                && table.families.get(root.offset().0) == Some(&Family::Value),
            (DeclKind::Axiom | DeclKind::AbstractType, None) => true,
            _ => false,
        }))]
fn decode_declaration(
    reader: &mut ByteReader<'_>,
    table: &mut Table,
) -> Result<DeclMeta, DecodeError>
{
    let mark = decode_admission(reader)?;
    let kind = reader.next_tag()?;
    let kind = declaration_kind(kind)?;
    let name = decode_structured_name(reader)?;
    let levels = decode_level_signature(reader)?;
    let entry_count = reader.read_uvarint()?;
    let mut remaining = u64::from(entry_count);
    while remaining > 0_u64 {
        decode_entry(reader, table)?;
        remaining = remaining.wrapping_sub(1_u64);
    }
    let root_declared = decode_root(reader, table, Family::ValueType)?;
    let mut provenance: Vec<ConstantIndex> = Vec::new();
    let root_body = match kind {
        | DeclKind::Def => {
            let body = decode_root(reader, table, Family::Value)?;
            provenance = decode_definition_slots(reader)?;
            Some(body)
        },
        // An abstract type carries a kind root and stops, exactly like an
        // axiom: no body, and therefore no per-definition annotation slots.
        | DeclKind::Axiom | DeclKind::AbstractType => None,
    };
    Ok(DeclMeta {
        mark,
        kind,
        name,
        levels,
        root_declared,
        root_body,
        provenance,
    })
}

/// Decode a declaration's root: a global index resolving to an already-decoded
/// entry of the required family.
///
/// # Specification
/// - requires: nothing — the index on the wire may be arbitrary.
/// - ensures: the returned index names an entry already in `table` whose family
///   is `required`, so every root a declaration is later built over resolves.
/// - provides: the root-reference check of one declaration segment.
/// - fails: [`DecodeError::Malformed`] at the child-order site when the index
///   names no already-decoded entry, and at the polarity site when the entry it
///   names is of another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|index|
    *index < table.next_index() && table.families.get(index.offset().0) == Some(&required)))]
fn decode_root(
    reader: &mut ByteReader<'_>,
    table: &Table,
    required: Family,
) -> Result<GlobalIndex, DecodeError>
{
    let index = reader.read_global()?;
    let family = family_at(table, index)?;
    if family == required {
        Ok(index)
    }
    else {
        Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        })
    }
}

/// The family of the entry at `index`, requiring it to name an already-decoded
/// entry; a forward or out-of-range reference is a child-order fault.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the recorded family of the entry at `index` when `index` is
///   strictly below the next free index and the family vector holds it.
/// - provides: the polarity lookup both the root check and the child check
///   decide against, so polarity is read from the table rather than threaded
///   through the parser.
/// - fails: [`DecodeError::Malformed`] at the child-order site on a forward,
///   self, or out-of-range index.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    ensures: |ret| match (index < table.next_index(), table.families.get(index.offset().0)) { (true, Some(family)) => ret.as_ref() == Ok(family), _ => ret.as_ref() == Err(&DecodeError::Malformed { site: MalformedSite::ChildOrder }) },
)]
#[inline]
fn family_at(
    table: &Table,
    index: GlobalIndex,
) -> Result<Family, DecodeError>
{
    if index >= table.next_index() {
        return Err(DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        });
    }
    table
        .families
        .get(index.offset().0)
        .copied()
        .ok_or(DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        })
}

/// Decode one subterm-table entry, minting it into the arena.
///
/// # Specification
/// - requires: the running table’s vectors are aligned; input bytes may be
///   arbitrary.
/// - ensures: success appends one global row with its correct family and
///   ordered earlier children, resolving to a live arena id. Element
///   normalization may reuse an existing id rather than allocate a fresh node.
///   Failure leaves the table and arena unchanged, though the byte cursor may
///   advance.
/// - provides: sharing-preserving entry construction and an atomic table
///   update. Predicates check the row frame and live family; literal fixtures
///   check payloads and ordered child fields.
/// - fails: table-size, child-order or polarity faults; an unknown node tag; or
///   any inline field’s named refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
///   Every proper entry prefix and every unassigned node byte also check that
///   refusal leaves the table and arena unchanged.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    captures: entry = (table.nodes.len(), table.families.len(), table.children.len(), table.next_index(), reader.image.byte_at(reader.position).map(WireTag::from), table.arena.watermark(), reader.position),
    ensures: |ret| reader.position >= entry.6
            && reader.position <= reader.image.length()
            && if ret.is_err() { table.nodes.len() == entry.0
            && table.families.len() == entry.1
            && table.children.len() == entry.2
            && table.arena.watermark() == entry.5 }
        else { TableEntryCount::from(table.nodes.len()) <= MAX_TABLE_ENTRIES
            && table.nodes.len() == entry.0.saturating_add(1)
            && table.families.len() == entry.1.saturating_add(1)
            && table.children.len() == entry.2.saturating_add(1)
            && entry.4.is_some_and(|tag| tags::NODE_TAG_TABLE.iter().any(|description| description.tag == tag))
            && table.children.last().is_some_and(|children| children.iter().all(|child| *child < entry.3))
            && match (table.nodes.last().copied(), table.families.last().copied()) { (Some(DecodedNode::ValueType(id)), Some(Family::ValueType)) => table.arena.value_type(id).is_some(), (Some(DecodedNode::CompType(id)), Some(Family::CompType)) => table.arena.comp_type(id).is_some(), (Some(DecodedNode::Value(id)), Some(Family::Value)) => table.arena.value(id).is_some(), (Some(DecodedNode::Computation(id)), Some(Family::Computation)) => table.arena.computation(id).is_some(), _ => false } },
)]
fn decode_entry(
    reader: &mut ByteReader<'_>,
    table: &mut Table,
) -> Result<(), DecodeError>
{
    if TableEntryCount::from(table.nodes.len()) >= MAX_TABLE_ENTRIES {
        return Err(DecodeError::Malformed {
            site: MalformedSite::TableSize,
        });
    }
    let this = table.next_index();
    let tag = reader.next_tag()?;
    let mut children: Vec<GlobalIndex> = Vec::new();
    let (node, family) = match tag {
        | tags::NODE_VT_BASE => {
            let base = decode_base_type(reader)?;
            let id = table.arena.value_type_base(base);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_UNIT => (
            DecodedNode::ValueType(table.arena.value_type_unit()),
            Family::ValueType,
        ),
        | tags::NODE_VT_UNIVERSE => {
            let level = decode_level(reader)?;
            let id = table.arena.value_type_universe(GroundSort::Value, level);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_COMPUTATION_UNIVERSE => {
            let level = decode_level(reader)?;
            let id = table
                .arena
                .value_type_universe(GroundSort::Computation, level);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_ABSTRACT => {
            // The payload is an admission position, not a table index: an atom
            // names a declaration, so resolving it is a choke point's job on
            // replay rather than the parser's. Decode only bounds the integer.
            let atom = reader.read_usize()?;
            let id = table
                .arena
                .value_type_abstract(ConstantIndex::from(usize::from(atom)));
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_PRODUCT => {
            let first = read_value_type(reader, table, this, &mut children)?;
            let second = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.value_type_product(first, second);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_SUM => {
            let first = read_value_type(reader, table, this, &mut children)?;
            let second = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.value_type_sum(first, second);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_THUNK => {
            let body = read_comp_type(reader, table, this, &mut children)?;
            let id = table.arena.value_type_thunk(body);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_LIFT => {
            let target = decode_level(reader)?;
            let inner = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.value_type_lift(inner, target);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_ELEMENT => {
            let target = decode_level(reader)?;
            let code = read_value(reader, table, this, &mut children)?;
            let id = table.arena.value_type_element(code, target);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_VT_STATIC_PI => {
            let domain = read_value_type(reader, table, this, &mut children)?;
            let codomain = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.value_type_static_pi(domain, codomain);
            (DecodedNode::ValueType(id), Family::ValueType)
        },
        | tags::NODE_CT_RETURNER => {
            let result = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.comp_type_returner(result);
            (DecodedNode::CompType(id), Family::CompType)
        },
        | tags::NODE_CT_ARROW => {
            let domain = read_value_type(reader, table, this, &mut children)?;
            let codomain = read_comp_type(reader, table, this, &mut children)?;
            let id = table.arena.comp_type_arrow(domain, codomain);
            (DecodedNode::CompType(id), Family::CompType)
        },
        | tags::NODE_CT_PI => {
            let domain = read_value_type(reader, table, this, &mut children)?;
            let codomain = read_comp_type(reader, table, this, &mut children)?;
            let id = table.arena.comp_type_pi(domain, codomain);
            (DecodedNode::CompType(id), Family::CompType)
        },
        | tags::NODE_CT_ELEMENT => {
            let target = decode_level(reader)?;
            let code = read_value(reader, table, this, &mut children)?;
            let id = table.arena.comp_type_element(code, target);
            (DecodedNode::CompType(id), Family::CompType)
        },
        | tags::NODE_V_VARIABLE => {
            let index = reader.read_u32()?;
            let id = table
                .arena
                .value_variable(DeBruijnIndex::from(u32::from(index)));
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_CONSTANT => {
            let index = reader.read_usize()?;
            let id = table
                .arena
                .value_constant(ConstantIndex::from(usize::from(index)));
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_UNIT => (DecodedNode::Value(table.arena.value_unit()), Family::Value),
        | tags::NODE_V_LITERAL => {
            let literal = decode_literal(reader)?;
            let id = table.arena.value_literal(literal);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_PAIR => {
            let first = read_value(reader, table, this, &mut children)?;
            let second = read_value(reader, table, this, &mut children)?;
            let id = table.arena.value_pair(first, second);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_INJECTION => {
            let side = decode_side(reader)?;
            let body = read_value(reader, table, this, &mut children)?;
            let id = table.arena.value_injection(side, body);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_THUNK => {
            let body = read_computation(reader, table, this, &mut children)?;
            let id = table.arena.value_thunk(body);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_LIFT => {
            let target = decode_level(reader)?;
            let body = read_value(reader, table, this, &mut children)?;
            let id = table.arena.value_lift(target, body);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_QUOTE => {
            let quoted = read_value_type(reader, table, this, &mut children)?;
            let id = table.arena.value_quote(quoted);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_QUOTE_COMPUTATION => {
            let quoted = read_comp_type(reader, table, this, &mut children)?;
            let id = table.arena.value_quote_computation(quoted);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_V_STATIC_APPLICATION => {
            let head = read_value(reader, table, this, &mut children)?;
            let argument = read_value(reader, table, this, &mut children)?;
            let id = table.arena.value_static_application(head, argument);
            (DecodedNode::Value(id), Family::Value)
        },
        | tags::NODE_C_LAMBDA => {
            let body = read_computation(reader, table, this, &mut children)?;
            let id = table.arena.computation_lambda(body);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | tags::NODE_C_APPLICATION => {
            let head = read_computation(reader, table, this, &mut children)?;
            let argument = read_value(reader, table, this, &mut children)?;
            let id = table.arena.computation_application(head, argument);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | tags::NODE_C_RETURN => {
            let value = read_value(reader, table, this, &mut children)?;
            let id = table.arena.computation_return(value);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | tags::NODE_C_BIND => {
            let bound = read_computation(reader, table, this, &mut children)?;
            let body = read_computation(reader, table, this, &mut children)?;
            let id = table.arena.computation_bind(bound, body);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | tags::NODE_C_FORCE => {
            let value = read_value(reader, table, this, &mut children)?;
            let id = table.arena.computation_force(value);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | tags::NODE_C_CASE => {
            let scrutinee = read_value(reader, table, this, &mut children)?;
            let on_left = read_computation(reader, table, this, &mut children)?;
            let on_right = read_computation(reader, table, this, &mut children)?;
            let id = table.arena.computation_case(scrutinee, on_left, on_right);
            (DecodedNode::Computation(id), Family::Computation)
        },
        | other => {
            return Err(DecodeError::UnknownTag {
                site: TagSite::Node,
                tag: other,
            });
        },
    };
    table.nodes.push(node);
    table.families.push(family);
    table.children.push(children);
    Ok(())
}

/// Read one child index, validating strictly-earlier order and the required
/// polarity, and return the entry it names.
///
/// # Specification
/// - requires: `this` is the global index the entry being decoded will take, so
///   "strictly earlier" is decided against the parent's own position.
/// - ensures: the read index is strictly below `this` and names an entry of
///   family `required`; the index is appended to `children` in wire order, and
///   the entry it names is returned. Acyclicity and topological order are both
///   consequences of the strictly-earlier check.
/// - provides: the one child-reference primitive every arity uses, so no arm
///   can forget either check. The clauses check the next index, appended
///   child's identity and polarity. Preservation of the earlier `children`
///   prefix stays prose: checking its entry contents would require an
///   allocating capture even without checks.
/// - fails: [`DecodeError::Malformed`] at the child-order site on a self,
///   forward, or out-of-range index, and at the polarity site when the named
///   entry belongs to another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[inline]
#[spec(
    requires: this == table.next_index(),
    captures: entry_children_count = children.len(),
    ensures: |ret| (ret.is_ok() || children.len() == entry_children_count) && ret.as_ref().ok().is_none_or(|node|
        children.len() == entry_children_count.saturating_add(1)
            && children.last().is_some_and(|index|
                *index < this && table.families.get(index.offset().0) == Some(&required)
                && match (*node, table.nodes.get(index.offset().0).copied()) {
                    (DecodedNode::ValueType(id), Some(DecodedNode::ValueType(found))) => id == found,
                    (DecodedNode::CompType(id), Some(DecodedNode::CompType(found))) => id == found,
                    (DecodedNode::Value(id), Some(DecodedNode::Value(found))) => id == found,
                    (DecodedNode::Computation(id), Some(DecodedNode::Computation(found))) => id == found,
                    _ => false,
                })),
)]
fn read_child(
    reader: &mut ByteReader<'_>,
    table: &Table,
    this: GlobalIndex,
    required: Family,
    children: &mut Vec<GlobalIndex>,
) -> Result<DecodedNode, DecodeError>
{
    let index = reader.read_global()?;
    if index >= this {
        return Err(DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        });
    }
    let family = table
        .families
        .get(index.offset().0)
        .copied()
        .ok_or(DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        })?;
    if family != required {
        return Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        });
    }
    let node = table
        .nodes
        .get(index.offset().0)
        .copied()
        .ok_or(DecodeError::Malformed {
            site: MalformedSite::ChildOrder,
        })?;
    children.push(index);
    Ok(node)
}

/// Read a value-type child.
///
/// # Specification
/// - requires: `this` is the index of the entry being decoded, and `children`
///   collects its child indices in wire order.
/// - ensures: on `Ok`, returns the child's value-type id and appends its index
///   to `children`.
/// - provides: the polarity-checked child read; a child of another family is
///   refused here rather than reaching a constructor.
/// - fails: the child read's own failures, and [`DecodeError::Malformed`] at
///   the polarity site when the entry is of another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    requires: this == table.next_index(), captures: start = (children.len(), reader.position),
    ensures: |ret| reader.position >= start.1
            && reader.position <= reader.image.length()
            && children.len() >= start.0
            && children.len() <= start.0.saturating_add(1)
            && ret.as_ref().ok().is_none_or(|id| children.len() == start.0.saturating_add(1)
            && children.last().is_some_and(|index| *index < this
            && table.families.get(index.offset().0) == Some(&Family::ValueType)
            && match table.nodes.get(index.offset().0) { Some(&DecodedNode::ValueType(found)) => *id == found, _ => false })),
)]
#[inline]
fn read_value_type(
    reader: &mut ByteReader<'_>,
    table: &Table,
    this: GlobalIndex,
    children: &mut Vec<GlobalIndex>,
) -> Result<ValueTypeId, DecodeError>
{
    let child = read_child(reader, table, this, Family::ValueType, children)?;
    match child {
        | DecodedNode::ValueType(id) => Ok(id),
        | _ => Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        }),
    }
}

/// Read a computation-type child.
///
/// # Specification
/// - requires: `this` is the index of the entry being decoded, and `children`
///   collects its child indices in wire order.
/// - ensures: on `Ok`, returns the child's computation-type id and appends its
///   index to `children`.
/// - provides: the polarity-checked child read for the negative type family.
/// - fails: the child read's own failures, and [`DecodeError::Malformed`] at
///   the polarity site when the entry is of another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    requires: this == table.next_index(), captures: start = (children.len(), reader.position),
    ensures: |ret| reader.position >= start.1
            && reader.position <= reader.image.length()
            && children.len() >= start.0
            && children.len() <= start.0.saturating_add(1)
            && ret.as_ref().ok().is_none_or(|id| children.len() == start.0.saturating_add(1)
            && children.last().is_some_and(|index| *index < this
            && table.families.get(index.offset().0) == Some(&Family::CompType)
            && match table.nodes.get(index.offset().0) { Some(&DecodedNode::CompType(found)) => *id == found, _ => false })),
)]
#[inline]
fn read_comp_type(
    reader: &mut ByteReader<'_>,
    table: &Table,
    this: GlobalIndex,
    children: &mut Vec<GlobalIndex>,
) -> Result<CompTypeId, DecodeError>
{
    let child = read_child(reader, table, this, Family::CompType, children)?;
    match child {
        | DecodedNode::CompType(id) => Ok(id),
        | _ => Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        }),
    }
}

/// Read a value child.
///
/// # Specification
/// - requires: `this` is the index of the entry being decoded, and `children`
///   collects its child indices in wire order.
/// - ensures: on `Ok`, returns the child's value id and appends its index to
///   `children`.
/// - provides: the polarity-checked child read for the positive term family.
/// - fails: the child read's own failures, and [`DecodeError::Malformed`] at
///   the polarity site when the entry is of another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    requires: this == table.next_index(), captures: start = (children.len(), reader.position),
    ensures: |ret| reader.position >= start.1
            && reader.position <= reader.image.length()
            && children.len() >= start.0
            && children.len() <= start.0.saturating_add(1)
            && ret.as_ref().ok().is_none_or(|id| children.len() == start.0.saturating_add(1)
            && children.last().is_some_and(|index| *index < this
            && table.families.get(index.offset().0) == Some(&Family::Value)
            && match table.nodes.get(index.offset().0) { Some(&DecodedNode::Value(found)) => *id == found, _ => false })),
)]
#[inline]
fn read_value(
    reader: &mut ByteReader<'_>,
    table: &Table,
    this: GlobalIndex,
    children: &mut Vec<GlobalIndex>,
) -> Result<ValueId, DecodeError>
{
    let child = read_child(reader, table, this, Family::Value, children)?;
    match child {
        | DecodedNode::Value(id) => Ok(id),
        | _ => Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        }),
    }
}

/// Read a computation child.
///
/// # Specification
/// - requires: `this` is the index of the entry being decoded, and `children`
///   collects its child indices in wire order.
/// - ensures: on `Ok`, returns the child's computation id and appends its index
///   to `children`.
/// - provides: the polarity-checked child read for the negative term family.
/// - fails: the child read's own failures, and [`DecodeError::Malformed`] at
///   the polarity site when the entry is of another family.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 distinguishes all four reference families, exact ordered
///   child appends, self and forward references, polarity refusals and complete
///   former payloads against literal entries. It observes sharing through
///   resolved ids rather than assuming global indices equal arena ordinals.
/// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
/// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
#[spec(
    requires: this == table.next_index(), captures: start = (children.len(), reader.position),
    ensures: |ret| reader.position >= start.1
            && reader.position <= reader.image.length()
            && children.len() >= start.0
            && children.len() <= start.0.saturating_add(1)
            && ret.as_ref().ok().is_none_or(|id| children.len() == start.0.saturating_add(1)
            && children.last().is_some_and(|index| *index < this
            && table.families.get(index.offset().0) == Some(&Family::Computation)
            && match table.nodes.get(index.offset().0) { Some(&DecodedNode::Computation(found)) => *id == found, _ => false })),
)]
#[inline]
fn read_computation(
    reader: &mut ByteReader<'_>,
    table: &Table,
    this: GlobalIndex,
    children: &mut Vec<GlobalIndex>,
) -> Result<ComputationId, DecodeError>
{
    let child = read_child(reader, table, this, Family::Computation, children)?;
    match child {
        | DecodedNode::Computation(id) => Ok(id),
        | _ => Err(DecodeError::Malformed {
            site: MalformedSite::Polarity,
        }),
    }
}

/// Decode a declaration's admission mark.
///
/// # Specification
/// - requires: the cursor is at a declaration’s admission-mark field.
/// - ensures: returns the mark named by the next byte and consumes that byte,
///   or reports its exact refusal.
/// - provides: the producer’s checked or bypass claim. Reading a checked mark
///   neither runs a checker nor proves that admission occurred.
/// - fails: `DecodeError::Truncated` at the end; `DecodeError::UnknownTag` at
///   the admission site for every unassigned byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| { let byte = reader.image.byte_at(start).map(u8::from);
        reader.position.0 == start.0.saturating_add(usize::from(byte.is_some()))
            && match byte { Some(0) => ret.as_ref() == Ok(&AdmissionMark::Checked), Some(1) => ret.as_ref() == Ok(&AdmissionMark::UncheckedBypass), Some(other) => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::Admission, tag: WireTag::from(other) }), None => ret.as_ref() == Err(&DecodeError::Truncated) } },
)]
#[inline]
fn decode_admission(reader: &mut ByteReader<'_>) -> Result<AdmissionMark, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::ADMISSION_CHECKED => Ok(AdmissionMark::Checked),
        | tags::ADMISSION_UNCHECKED => Ok(AdmissionMark::UncheckedBypass),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::Admission,
            tag: other,
        }),
    }
}

/// Resolve a declaration-kind byte, refusing a reserved kind distinctly from an
/// unknown one.
///
/// # Specification
/// - requires: `kind` is the byte read at a declaration-kind position.
/// - ensures: returns the live kind for a definition, an axiom, or a sealed
///   abstract type.
/// - provides: the one place a kind byte is interpreted, keeping a reserved
///   kind's refusal distinct from an unknown byte's, so a reader learns whether
///   the kind is unimplemented or unassigned.
/// - fails: [`DecodeError::ReservedDeclarationKind`] on one of the three
///   reserved kinds; [`DecodeError::UnknownTag`] at the declaration-kind site
///   on any other byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    ensures: |ret| match u8::from(kind) { 0 => ret.as_ref() == Ok(&DeclKind::Def), 1 => ret.as_ref() == Ok(&DeclKind::Axiom), 2 => ret.as_ref() == Ok(&DeclKind::AbstractType), 3 => ret.as_ref() == Err(&DecodeError::ReservedDeclarationKind { kind: ReservedKind::ModuleSig }), 4 => ret.as_ref() == Err(&DecodeError::ReservedDeclarationKind { kind: ReservedKind::ModuleDef }), 5 => ret.as_ref() == Err(&DecodeError::ReservedDeclarationKind { kind: ReservedKind::FunctorDef }), _ => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::DeclarationKind, tag: kind }) },
)]
#[inline]
fn declaration_kind(kind: WireTag) -> Result<DeclKind, DecodeError>
{
    match kind {
        | tags::KIND_DEF => Ok(DeclKind::Def),
        | tags::KIND_AXIOM => Ok(DeclKind::Axiom),
        // The abstract-type kind is deliberately live here: it was reserved with
        // the other three and sealing made it real, so it is decoded rather than
        // refused.
        | tags::KIND_ABSTRACT_TYPE => Ok(DeclKind::AbstractType),
        | tags::KIND_MODULE_SIG => Err(DecodeError::ReservedDeclarationKind {
            kind: ReservedKind::ModuleSig,
        }),
        | tags::KIND_MODULE_DEF => Err(DecodeError::ReservedDeclarationKind {
            kind: ReservedKind::ModuleDef,
        }),
        | tags::KIND_FUNCTOR_DEF => Err(DecodeError::ReservedDeclarationKind {
            kind: ReservedKind::FunctorDef,
        }),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::DeclarationKind,
            tag: other,
        }),
    }
}

/// Decode the structured-name record: a segment count, then each segment as
/// length-prefixed UTF-8.
///
/// No capacity is reserved from the declared count; storage grows only after a
/// complete segment has been decoded.
///
/// # Specification
/// - requires: the cursor is positioned at the structured-name record.
/// - ensures: on `Ok`, returns exactly the declared number of segments, in wire
///   order, each rebuilt through [`NameSegment::from_text`], and advances past
///   the record.
/// - provides: the name a decoded declaration carries; a segment holding the
///   separator is unrepresentable, so no dotted string becomes a name through
///   the wire.
/// - fails: the count and length reads' own failures, and
///   [`DecodeError::Malformed`] at the name-segment site on a segment that is
///   not UTF-8 or holds the separator.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 uses literal record bytes with empty and nonempty names,
///   Unicode, out-of-order provenance, occupied reserved slots, invalid UTF-8
///   and maximal declared counts. It checks exact values, refusal sites and
///   cursor positions; it does not claim name normalization, atom truth or
///   typing.
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
/// - witness: `sharing_format::sharing_format::a_segment_holding_a_separator_is_refused`
/// - witness: `sharing_format::sharing_format::a_structured_name_round_trips_as_segments`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|name| { let count = u64::try_from(name.segments().len()).unwrap_or(u64::MAX);
        ({ let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && name.segments().iter().try_fold(start.0.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
        |position, segment| { let text: &str = segment.as_ref();
        let length = u64::try_from(text.len()).unwrap_or(u64::MAX);
        let payload = position.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX));
        let end = payload.saturating_add(text.len());
        (({ let scalar = length;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && reader.image.as_ref().get(payload .. end) == Some(text.as_bytes())).then_some(end) }) == Some(reader.position.0) }),
)]
fn decode_structured_name(reader: &mut ByteReader<'_>) -> Result<StructuredName, DecodeError>
{
    let count = reader.read_uvarint()?;
    let mut segments: Vec<NameSegment> = Vec::new();
    let mut remaining = u64::from(count);
    while remaining > 0_u64 {
        let text = reader.read_text(MalformedSite::NameSegment)?;
        let Some(segment) = NameSegment::from_text(text)
        else {
            return Err(DecodeError::Malformed {
                site: MalformedSite::NameSegment,
            });
        };
        segments.push(segment);
        remaining = remaining.wrapping_sub(1_u64);
    }
    Ok(StructuredName::from(segments))
}

/// Decode the four per-definition annotation slots, yielding the
/// sealing-provenance atoms.
///
/// Three of the four stay reserved and are refused when occupied; the third is
/// live and carries the atoms this declaration's projection rebound. The atoms
/// are only *read* here — whether they ascend, and whether each occurs in the
/// declared type, are typing facts decided at a choke point, and this is the
/// format plane.
///
/// # Specification
/// - requires: the cursor is positioned at the first of the four per-definition
///   annotation slots.
/// - ensures: on `Ok`, the three reserved slots were empty and the returned
///   atoms are the sealing-provenance slot's, in wire order; the cursor is past
///   all four.
/// - provides: the whole slot block read in one place, so the live slot's
///   position among the reserved ones is stated once. Whether the atoms ascend,
///   and whether each occurs in the declared type, are typing facts decided at
///   a choke point.
/// - fails: the slot reads' own failures, and
///   [`DecodeError::ReservedSlotOccupied`] naming whichever reserved slot was
///   occupied.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 uses literal record bytes with empty and nonempty names,
///   Unicode, out-of-order provenance, occupied reserved slots, invalid UTF-8
///   and maximal declared counts. It checks exact values, refusal sites and
///   cursor positions; it does not claim name normalization, atom truth or
///   typing.
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|atoms| reader.image.as_ref().get(start.0 .. start.0.saturating_add(2)) == Some([0_u8, 0].as_slice())
            && reader.image.byte_at(ByteOffset::from(reader.position.0.saturating_sub(1))) == Some(WireByte::from(0_u8))
            && { let count = u64::try_from(atoms.len()).unwrap_or(u64::MAX);
        ({ let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0.saturating_add(2)) .. (start.0.saturating_add(2)).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && atoms.iter().try_fold((start.0.saturating_add(2)).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
        |position, &atom| { let ordinal = u64::try_from(usize::from(atom)).unwrap_or(u64::MAX);
        ({ let scalar = ordinal;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }).then_some(position.saturating_add(usize::try_from(64_u32.saturating_sub((ordinal).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }) == Some(reader.position.0.saturating_sub(1)) }),
)]
#[inline]
fn decode_definition_slots(reader: &mut ByteReader<'_>) -> Result<Vec<ConstantIndex>, DecodeError>
{
    expect_empty_slot(reader, ReservedSlot::ErasureAnnotation)?;
    expect_empty_slot(reader, ReservedSlot::ModeGradeAnnotation)?;
    let provenance = decode_sealing_provenance(reader)?;
    expect_empty_slot(reader, ReservedSlot::DirectednessVariance)?;
    Ok(provenance)
}

/// Require one still-reserved slot to be empty.
///
/// # Specification
/// - requires: the cursor is positioned at a reserved slot's count.
/// - ensures: on `Ok`, the count was zero and the cursor is past it.
/// - provides: the one refusal every still-reserved slot shares, so a slot made
///   live later changes one call site rather than a scattered check.
/// - fails: the count read's own failures, and
///   [`DecodeError::ReservedSlotOccupied`] naming `slot`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 uses literal record bytes with empty and nonempty names,
///   Unicode, out-of-order provenance, occupied reserved slots, invalid UTF-8
///   and maximal declared counts. It checks exact values, refusal sites and
///   cursor positions; it does not claim name normalization, atom truth or
///   typing.
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.is_ok() == (reader.image.byte_at(start) == Some(WireByte::from(0_u8)))
            && (ret.is_err() || reader.position.0 == start.0.saturating_add(1))
            && ret.as_ref().err().is_none_or(|error| match *error { DecodeError::ReservedSlotOccupied { slot: found } => found == slot, DecodeError::Truncated | DecodeError::Malformed { site: MalformedSite::Varint } => true, _ => false }),
)]
#[inline]
fn expect_empty_slot(
    reader: &mut ByteReader<'_>,
    slot: ReservedSlot,
) -> Result<(), DecodeError>
{
    let count = reader.read_uvarint()?;
    if u64::from(count) == 0_u64 {
        Ok(())
    }
    else {
        Err(DecodeError::ReservedSlotOccupied { slot })
    }
}

/// Decode the sealing-provenance slot: a count followed by admission positions.
///
/// No capacity is reserved from the declared count; storage grows only after a
/// position has been decoded.
///
/// # Specification
/// - requires: the cursor is positioned at the sealing-provenance slot.
/// - ensures: on `Ok`, returns exactly the declared number of admission
///   positions, in wire order, and advances past the slot.
/// - provides: the slot's atoms; no capacity is reserved from the declared
///   count; storage grows only after a position has been decoded.
/// - fails: the count and position reads' own failures.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 uses literal record bytes with empty and nonempty names,
///   Unicode, out-of-order provenance, occupied reserved slots, invalid UTF-8
///   and maximal declared counts. It checks exact values, refusal sites and
///   cursor positions; it does not claim name normalization, atom truth or
///   typing.
/// - witness: `decode::tests::counted_records_validate_content_and_consumption`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|atoms| { let count = u64::try_from(atoms.len()).unwrap_or(u64::MAX);
        ({ let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && atoms.iter().try_fold((start.0).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)),
        |position, &atom| { let ordinal = u64::try_from(usize::from(atom)).unwrap_or(u64::MAX);
        ({ let scalar = ordinal;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((position) .. (position).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }).then_some(position.saturating_add(usize::try_from(64_u32.saturating_sub((ordinal).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) }) == Some(reader.position.0) }),
)]
#[inline]
fn decode_sealing_provenance(reader: &mut ByteReader<'_>)
-> Result<Vec<ConstantIndex>, DecodeError>
{
    let count = reader.read_uvarint()?;
    let mut atoms: Vec<ConstantIndex> = Vec::new();
    let mut remaining = u64::from(count);
    while remaining > 0_u64 {
        let atom = reader.read_usize()?;
        atoms.push(ConstantIndex::from(usize::from(atom)));
        remaining = remaining.wrapping_sub(1_u64);
    }
    Ok(atoms)
}

/// Decode a prenex level signature, each constraint rebuilt through its smart
/// constructor.
///
/// # Specification
/// - requires: nothing; parameter and constraint counts may be adversarial.
/// - ensures: returns the parameter count and successfully rebuilt constraints
///   in wire order; the cursor follows the last constraint.
/// - provides: a decoded interface, not proof that its parameters cover every
///   referenced variable. Predicates check the two wire counts; normalization
///   and relation semantics are witnessed separately.
/// - fails: integer and level-read failures, unknown constraint relations, or
///   malformed non-variable-only constraint sides.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|signature| { let params = u64::from(u32::from(signature.params()));
        let count = u64::try_from(signature.constraints().len()).unwrap_or(u64::MAX);
        ({ let scalar = params;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0) .. (start.0).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && ({ let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (start.0.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && reader.position.0 >= start.0.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)) }),
)]
fn decode_level_signature(reader: &mut ByteReader<'_>) -> Result<LevelSignature, DecodeError>
{
    let params = reader.read_u32()?;
    let count = reader.read_uvarint()?;
    let mut constraints: Vec<LandmarkConstraint> = Vec::new();
    let mut remaining = u64::from(count);
    while remaining > 0_u64 {
        let relation = decode_relation(reader)?;
        let left = decode_level(reader)?;
        let right = decode_level(reader)?;
        let constraint = match relation {
            | ConstraintRelation::Leq => LandmarkConstraint::leq(left, right),
            | ConstraintRelation::Eq => LandmarkConstraint::equal(left, right),
        };
        let constraint = constraint.map_err(|_error| DecodeError::Malformed {
            site: MalformedSite::ConstraintForm,
        })?;
        constraints.push(constraint);
        remaining = remaining.wrapping_sub(1_u64);
    }
    Ok(LevelSignature::new(
        LevelParamCount::from(u32::from(params)),
        constraints,
    ))
}

/// Decode a landmark-constraint relation.
///
/// # Specification
/// - requires: the cursor is positioned at a constraint relation.
/// - ensures: on `Ok`, returns the relation the tag named and advances past it.
/// - provides: the relation alphabet's one interpretation site.
/// - fails: [`DecodeError::Truncated`] at the end of the image;
///   [`DecodeError::UnknownTag`] at the constraint-relation site on any other
///   byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| { let byte = reader.image.byte_at(start).map(u8::from);
        reader.position.0 == start.0.saturating_add(usize::from(byte.is_some()))
            && match byte { Some(0) => ret.as_ref() == Ok(&ConstraintRelation::Leq), Some(1) => ret.as_ref() == Ok(&ConstraintRelation::Eq), Some(other) => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::ConstraintRelation, tag: WireTag::from(other) }), None => ret.as_ref() == Err(&DecodeError::Truncated) } },
)]
#[inline]
fn decode_relation(reader: &mut ByteReader<'_>) -> Result<ConstraintRelation, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::RELATION_LEQ => Ok(ConstraintRelation::Leq),
        | tags::RELATION_EQ => Ok(ConstraintRelation::Eq),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::ConstraintRelation,
            tag: other,
        }),
    }
}

/// Decode a canonical level, rebuilt through the level oracle's smart
/// constructors so a non-canonical level is unrepresentable rather than merely
/// refused.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the normalized maximum of the supplied constant and
///   variable-offset atoms when every field decodes and every atom offset is
///   below the decode cap.
/// - provides: local level normalization, not acceptance of the original byte
///   spelling. Duplicate, dominated or reordered source atoms are rejected
///   later if re-encoding differs.
/// - fails: truncation, invalid integer encodings, out-of-range variable
///   indices, and an over-cap atom offset.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|level| reader.position.0 >= start.0.saturating_add(2)
            && level.atoms().all(|(_, amount)| LevelAtomOffset::from(u64::from(amount)) < MAX_DECODED_LEVEL_OFFSET)),
)]
fn decode_level(reader: &mut ByteReader<'_>) -> Result<Level, DecodeError>
{
    let constant = reader.read_uvarint()?;
    let atom_count = reader.read_uvarint()?;
    let mut level = Level::constant(LevelConstant::from(u64::from(constant)));
    let mut remaining = u64::from(atom_count);
    while remaining > 0_u64 {
        let variable = reader.read_u32()?;
        let offset = reader.read_uvarint()?;
        if LevelAtomOffset::from(u64::from(offset)) >= MAX_DECODED_LEVEL_OFFSET {
            return Err(DecodeError::Malformed {
                site: MalformedSite::LevelOffset,
            });
        }
        let atom = build_variable_atom(variable, offset)?;
        level = level.max(&atom);
        remaining = remaining.wrapping_sub(1_u64);
    }
    Ok(level)
}

/// Rebuild the level atom `variable + offset` through the oracle's variable and
/// successor constructors; the caller bounds the offset.
///
/// # Specification
/// - requires: `offset` is already below [`MAX_DECODED_LEVEL_OFFSET`], which
///   the caller checks — the loop below is one oracle call per unit of offset,
///   so an unbounded offset would be unbounded work.
/// - ensures: the canonical level `variable + offset`, built by `offset`-many
///   successor applications over the variable atom.
/// - provides: the level oracle's only route from a wire pair to an atom, so a
///   non-canonical atom is unrepresentable rather than merely refused. The
///   clauses check the offset bound and exact canonical atom. The number of
///   successor calls stays prose: `Level` exposes values, not a call trace.
/// - fails: [`DecodeError::Malformed`] at the level-offset site when a
///   successor application overflows.
/// - panics: none.
/// - intension: the reconstruction is an explicit loop over the offset, never
///   host recursion, so its depth is zero at every offset.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
#[inline]
#[spec(
    requires: LevelAtomOffset::from(u64::from(offset)) < MAX_DECODED_LEVEL_OFFSET,
    ensures: |ret| ret.as_ref().is_ok_and(|atom|
        u64::from(atom.constant_part()) == 0
            && atom.atoms().map(|(found, amount)|
                (u32::from(found.index()), u64::from(amount)))
                .eq(core::iter::once((u32::from(variable), u64::from(offset))))),
)]
fn build_variable_atom(
    variable: WireU32,
    offset: WireU64,
) -> Result<Level, DecodeError>
{
    let mut atom = Level::var(LevelVar::new(LevelVarIndex::from(u32::from(variable))));
    let mut remaining = u64::from(offset);
    while remaining > 0_u64 {
        atom = atom.succ().map_err(|_error| DecodeError::Malformed {
            site: MalformedSite::LevelOffset,
        })?;
        remaining = remaining.wrapping_sub(1_u64);
    }
    Ok(atom)
}

/// Decode a base-type atom.
///
/// # Specification
/// - requires: the cursor is positioned at a base-type atom.
/// - ensures: on `Ok`, returns the atom the tag named and advances past it.
/// - provides: the base-type alphabet's one interpretation site.
/// - fails: [`DecodeError::Truncated`] at the end of the image;
///   [`DecodeError::UnknownTag`] at the base-type site on any other byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| { let byte = reader.image.byte_at(start).map(u8::from);
        reader.position.0 == start.0.saturating_add(usize::from(byte.is_some()))
            && match byte { Some(0) => ret.as_ref() == Ok(&BaseType::Integer), Some(1) => ret.as_ref() == Ok(&BaseType::String), Some(2) => ret.as_ref() == Ok(&BaseType::Numeric), Some(other) => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::BaseType, tag: WireTag::from(other) }), None => ret.as_ref() == Err(&DecodeError::Truncated) } },
)]
#[inline]
fn decode_base_type(reader: &mut ByteReader<'_>) -> Result<BaseType, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::BASE_INTEGER => Ok(BaseType::Integer),
        | tags::BASE_STRING => Ok(BaseType::String),
        | tags::BASE_NUMERIC => Ok(BaseType::Numeric),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::BaseType,
            tag: other,
        }),
    }
}

/// Decode an injection side.
///
/// # Specification
/// - requires: the cursor is positioned at an injection side.
/// - ensures: on `Ok`, returns the side the tag named and advances past it.
/// - provides: the side alphabet's one interpretation site.
/// - fails: [`DecodeError::Truncated`] at the end of the image;
///   [`DecodeError::UnknownTag`] at the side site on any other byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| { let byte = reader.image.byte_at(start).map(u8::from);
        reader.position.0 == start.0.saturating_add(usize::from(byte.is_some()))
            && match byte { Some(0) => ret.as_ref() == Ok(&Side::Left), Some(1) => ret.as_ref() == Ok(&Side::Right), Some(other) => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::Side, tag: WireTag::from(other) }), None => ret.as_ref() == Err(&DecodeError::Truncated) } },
)]
#[inline]
fn decode_side(reader: &mut ByteReader<'_>) -> Result<Side, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::SIDE_LEFT => Ok(Side::Left),
        | tags::SIDE_RIGHT => Ok(Side::Right),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::Side,
            tag: other,
        }),
    }
}

/// Decode a literal, rebuilt through the base-type smart constructors.
///
/// # Specification
/// - requires: the cursor is positioned at a literal.
/// - ensures: on `Ok`, returns the literal the kind tag and payload named,
///   rebuilt through the canonicalizing constructors, and advances past it.
/// - provides: the only path from bytes to a literal, so a non-canonical
///   payload cannot enter the term language: the constructor canonicalizes and
///   the canonical-form comparison then refuses the original bytes.
/// - fails: the payload reads' own failures, and [`DecodeError::UnknownTag`] at
///   the literal-kind site on any other kind byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|literal| { let kind = reader.image.byte_at(start).map(u8::from);
        let sign = reader.image.byte_at(ByteOffset::from(start.0.saturating_add(1))).map(u8::from);
        match *literal { Literal::Integer(ref value) => kind == Some(0)
            && if value.magnitude().as_ref() == "0" { value.sign() == Sign::NonNegative }
        else { sign == Some(match value.sign() { Sign::NonNegative => 0, Sign::Negative => 1 }) }, Literal::Text(ref value) => { let text: &str = value.as_ref();
        let length = u64::try_from(text.len()).unwrap_or(u64::MAX);
        kind == Some(1)
            && reader.position.0 == start.0.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(text.len())
            && ({ let scalar = length;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        reader.image.as_ref().get((start.0.saturating_add(1)) .. (start.0.saturating_add(1)).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && reader.image.as_ref().get(reader.position.0.saturating_sub(text.len()) .. reader.position.0) == Some(text.as_bytes()) }, Literal::Numeric(ref value) => kind == Some(2)
            && if value.integer_part().as_ref() == "0"
            && value.fraction().as_ref().is_empty() { value.sign() == Sign::NonNegative }
        else { sign == Some(match value.sign() { Sign::NonNegative => 0, Sign::Negative => 1 }) } } }),
)]
fn decode_literal(reader: &mut ByteReader<'_>) -> Result<Literal, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::LITERAL_INTEGER => {
            let sign = decode_sign(reader)?;
            let magnitude = decode_magnitude(reader)?;
            Ok(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
        },
        | tags::LITERAL_TEXT => {
            let content = reader.read_text(MalformedSite::LiteralPayload)?;
            Ok(Literal::Text(StringLiteral::new(content)))
        },
        | tags::LITERAL_NUMERIC => {
            let sign = decode_sign(reader)?;
            let integer_part = decode_magnitude(reader)?;
            let fraction = decode_fraction(reader)?;
            Ok(Literal::Numeric(NumericLiteral::new(
                sign,
                integer_part,
                fraction,
            )))
        },
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::LiteralKind,
            tag: other,
        }),
    }
}

/// Decode a literal sign.
///
/// # Specification
/// - requires: the cursor is positioned at a literal sign.
/// - ensures: on `Ok`, returns the sign the tag named and advances past it.
/// - provides: the sign alphabet's one interpretation site.
/// - fails: [`DecodeError::Truncated`] at the end of the image;
///   [`DecodeError::UnknownTag`] at the sign site on any other byte.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 partitions every byte of each closed tag alphabet into its
///   exact value or named refusal, with empty-input truncation and
///   consumed-offset checks. Reserved declaration kinds remain distinct from
///   unassigned bytes. This proves the finite alphabets, not surrounding record
///   validity.
/// - witness: `decode::tests::tag_alphabets_partition_every_byte`
#[spec(
    captures: start = reader.position,
    ensures: |ret| { let byte = reader.image.byte_at(start).map(u8::from);
        reader.position.0 == start.0.saturating_add(usize::from(byte.is_some()))
            && match byte { Some(0) => ret.as_ref() == Ok(&Sign::NonNegative), Some(1) => ret.as_ref() == Ok(&Sign::Negative), Some(other) => ret.as_ref() == Err(&DecodeError::UnknownTag { site: TagSite::Sign, tag: WireTag::from(other) }), None => ret.as_ref() == Err(&DecodeError::Truncated) } },
)]
#[inline]
fn decode_sign(reader: &mut ByteReader<'_>) -> Result<Sign, DecodeError>
{
    let tag = reader.next_tag()?;
    match tag {
        | tags::SIGN_NON_NEGATIVE => Ok(Sign::NonNegative),
        | tags::SIGN_NEGATIVE => Ok(Sign::Negative),
        | other => Err(DecodeError::UnknownTag {
            site: TagSite::Sign,
            tag: other,
        }),
    }
}

/// Decode a canonical magnitude through its smart constructor.
///
/// # Specification
/// - requires: the cursor is at the magnitude’s length-prefixed digit text.
/// - ensures: returns nonempty ASCII decimal digits after removing leading
///   zeros; an all-zero input becomes the single zero.
/// - provides: local normalization. Padded digit spellings normalize here and
///   are rejected by the enclosing artifact comparison if re-encoding differs.
/// - fails: text and integer-read failures, or a malformed literal payload for
///   empty text or any non-decimal character.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|digits| reader.image.as_ref().get(start.0 .. reader.position.0).and_then(|bytes| { let prefix = bytes.iter().position(|byte| byte & 0x80 == 0)?.saturating_add(1);
        core::str::from_utf8(bytes.get(prefix ..)?).ok() }).is_some_and(|text| { let normalized = text.trim_start_matches('0');
        !text.is_empty() && digits.as_ref() == if normalized.is_empty() { "0" }
        else { normalized } })),
)]
#[inline]
fn decode_magnitude(reader: &mut ByteReader<'_>) -> Result<Magnitude, DecodeError>
{
    let digits = reader.read_text(MalformedSite::LiteralPayload)?;
    Magnitude::from_decimal_text(digits).ok_or(DecodeError::Malformed {
        site: MalformedSite::LiteralPayload,
    })
}

/// Decode a canonical fraction through its smart constructor.
///
/// # Specification
/// - requires: the cursor is at the fraction’s length-prefixed digit text.
/// - ensures: returns the decimal fraction after removing trailing zeros; empty
///   or all-zero input becomes the empty fraction.
/// - provides: local normalization. A noncanonical spelling is not refused
///   here; the enclosing artifact comparison rejects bytes that re-encode
///   differently.
/// - fails: text and integer-read failures, or a malformed literal payload when
///   the text contains a non-decimal character.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 contrasts local normalization with whole-artifact wire
///   acceptance: padded magnitudes, empty or trailing-zero fractions, negative
///   zero, repeated or dominated level atoms and reordered atoms normalize
///   locally but their noncanonical source bytes must not pass the final
///   re-encode comparison. Literal and interface fixtures also distinguish
///   malformed digits, invalid constraint sides and offset refusal.
/// - witness: `decode::tests::normalized_levels_and_literals_are_not_wire_acceptance`
#[spec(
    captures: start = reader.position,
    ensures: |ret| reader.position >= start
            && reader.position <= reader.image.length()
            && ret.as_ref().ok().is_none_or(|digits| reader.image.as_ref().get(start.0 .. reader.position.0).and_then(|bytes| { let prefix = bytes.iter().position(|byte| byte & 0x80 == 0)?.saturating_add(1);
        core::str::from_utf8(bytes.get(prefix ..)?).ok() }).is_some_and(|text| { let normalized = text.trim_end_matches('0');
        digits.as_ref() == normalized })),
)]
#[inline]
fn decode_fraction(reader: &mut ByteReader<'_>) -> Result<FractionDigits, DecodeError>
{
    let digits = reader.read_text(MalformedSite::LiteralPayload)?;
    FractionDigits::from_decimal_text(digits).ok_or(DecodeError::Malformed {
        site: MalformedSite::LiteralPayload,
    })
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use anodized::spec;

    use super::ByteReader;
    use crate::error::DecodeError;
    use crate::error::MalformedSite;
    use crate::wire::ArtifactImage;

    #[test]
    fn cursor_reads_preserve_borrows_and_refusal_positions()
    {
        let bytes = [0x10_u8, 0, 0xfe, 0x7f];
        for start in 0 ..= bytes.len() {
            for count in [0_usize, 1, 2, 4, 5, usize::MAX] {
                let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
                reader.position = super::ByteOffset::from(start);
                let result = reader.take(super::ByteCount::from(count));
                if count <= bytes.len().saturating_sub(start) {
                    let end = start.saturating_add(count);
                    let expected = bytes.get(start .. end).expect("bounded range");
                    let actual = result.expect("available bytes");
                    assert!(core::ptr::eq(
                        &raw const *actual.as_ref(),
                        &raw const *expected
                    ));
                    assert_eq!(reader.position, super::ByteOffset::from(end));
                }
                else {
                    assert_eq!(result, Err(DecodeError::Truncated));
                    assert_eq!(reader.position, super::ByteOffset::from(start));
                }
            }
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            reader.position = super::ByteOffset::from(start);
            let expected = bytes.get(start).copied().ok_or(DecodeError::Truncated);
            assert_eq!(reader.next_byte().map(u8::from), expected);
            assert_eq!(
                reader.position.0,
                start.saturating_add(usize::from(expected.is_ok()))
            );
        }
        let magic = *b"GKX1";
        for length in 0 ..= magic.len() {
            let prefix = magic.get(.. length).expect("bounded prefix");
            let mut reader = ByteReader::new(ArtifactImage::from(prefix));
            if length == 4 {
                assert_eq!(reader.expect_magic(), Ok(()));
                assert_eq!(reader.position.0, 4);
            }
            else {
                assert_eq!(reader.expect_magic(), Err(DecodeError::Truncated));
                assert_eq!(reader.position.0, 0);
            }
        }
        let mut foreign = ByteReader::new(ArtifactImage::from(b"BAD!tail".as_slice()));
        assert_eq!(
            foreign.expect_magic(),
            Err(DecodeError::Malformed {
                site: MalformedSite::Header
            })
        );
        assert_eq!(foreign.position.0, 4);
        for version in [0_u16, 1, 2, 3, 0x0200, u16::MAX] {
            let mut image = magic.to_vec();
            image.extend_from_slice(&version.to_le_bytes());
            let mut reader = ByteReader::new(ArtifactImage::from(image.as_slice()));
            reader.expect_magic().expect("valid header");
            let expected = if version == 2 {
                Ok(())
            }
            else {
                Err(DecodeError::UnsupportedVersion {
                    found: super::FormatVersion::from(version),
                })
            };
            assert_eq!(reader.expect_version(), expected);
            assert_eq!(reader.position.0, 6);
        }
        for suffix in [&[][..], &[2_u8][..]] {
            let mut image = magic.to_vec();
            image.extend_from_slice(suffix);
            let mut reader = ByteReader::new(ArtifactImage::from(image.as_slice()));
            reader.expect_magic().expect("valid header");
            assert_eq!(reader.expect_version(), Err(DecodeError::Truncated));
            assert_eq!(reader.position.0, 4_usize.saturating_add(suffix.len()));
        }
    }

    #[test]
    fn integer_fields_match_independent_boundary_bytes()
    {
        let reference = |mut value: u64| {
            let mut bytes = vec![];
            loop {
                let digit = u8::try_from(value.rem_euclid(128)).expect("seven-bit remainder");
                value = value.div_euclid(128);
                bytes.push(digit | if value == 0 { 0 } else { 0x80 });
                if value == 0 {
                    break;
                }
            }
            bytes
        };
        let mut values = vec![
            0_u64,
            1,
            u64::from(u32::MAX),
            u64::from(u32::MAX).saturating_add(1),
            u64::MAX,
        ];
        for shift in [7_u32, 14, 21, 28, 35, 42, 49, 56, 63] {
            let boundary = 1_u64.checked_shl(shift).expect("bounded shift");
            values.extend([
                boundary.saturating_sub(1),
                boundary,
                boundary.saturating_add(1),
            ]);
        }
        for value in values {
            let digits = reference(value);
            let mut bytes = vec![0xaa_u8];
            bytes.extend_from_slice(&digits);
            bytes.push(0x55);
            let end = 1_usize.saturating_add(digits.len());
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            reader.next_byte().expect("prefix");
            assert_eq!(reader.read_uvarint().map(u64::from), Ok(value));
            assert_eq!(reader.position.0, end);
            assert_eq!(reader.next_byte().map(u8::from), Ok(0x55));
            let narrow = u32::try_from(value).map_err(|_error| DecodeError::Malformed {
                site: MalformedSite::IndexRange,
            });
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            reader.next_byte().expect("prefix");
            assert_eq!(reader.read_u32().map(u32::from), narrow);
            assert_eq!(reader.position.0, end);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            reader.next_byte().expect("prefix");
            assert_eq!(reader.read_global().map(u32::from), narrow);
            assert_eq!(reader.position.0, end);
            let host = usize::try_from(value).map_err(|_error| DecodeError::Malformed {
                site: MalformedSite::IndexRange,
            });
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            reader.next_byte().expect("prefix");
            assert_eq!(reader.read_usize().map(usize::from), host);
            assert_eq!(reader.position.0, end);
        }
        for count in 0_usize ..= 10 {
            let bytes = vec![0x80_u8; count];
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            assert_eq!(reader.read_uvarint(), Err(DecodeError::Truncated));
            assert_eq!(reader.position.0, count);
        }
        for mut bytes in [vec![0x81_u8, 0], vec![0x80_u8; 11], vec![
            0x80_u8, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 2,
        ]] {
            let end = bytes.len();
            bytes.push(0x55);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            assert_eq!(
                reader.read_uvarint(),
                Err(DecodeError::Malformed {
                    site: MalformedSite::Varint
                })
            );
            assert_eq!(reader.position.0, end);
            assert_eq!(reader.next_byte().map(u8::from), Ok(0x55));
        }
    }

    #[test]
    fn tag_alphabets_partition_every_byte()
    {
        for byte in 0_u8 ..= u8::MAX {
            let bytes = [byte, 0x55];
            let unknown = |site| DecodeError::UnknownTag {
                site,
                tag: super::WireTag::from(byte),
            };
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let admission = match byte {
                | 0 => Ok(super::AdmissionMark::Checked),
                | 1 => Ok(super::AdmissionMark::UncheckedBypass),
                | _ => Err(unknown(super::TagSite::Admission)),
            };
            assert_eq!(super::decode_admission(&mut reader), admission);
            assert_eq!(reader.position.0, 1);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let relation = match byte {
                | 0 => Ok(super::ConstraintRelation::Leq),
                | 1 => Ok(super::ConstraintRelation::Eq),
                | _ => Err(unknown(super::TagSite::ConstraintRelation)),
            };
            assert_eq!(super::decode_relation(&mut reader), relation);
            assert_eq!(reader.position.0, 1);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let base = match byte {
                | 0 => Ok(super::BaseType::Integer),
                | 1 => Ok(super::BaseType::String),
                | 2 => Ok(super::BaseType::Numeric),
                | _ => Err(unknown(super::TagSite::BaseType)),
            };
            assert_eq!(super::decode_base_type(&mut reader), base);
            assert_eq!(reader.position.0, 1);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let side = match byte {
                | 0 => Ok(super::Side::Left),
                | 1 => Ok(super::Side::Right),
                | _ => Err(unknown(super::TagSite::Side)),
            };
            assert_eq!(super::decode_side(&mut reader), side);
            assert_eq!(reader.position.0, 1);
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let sign = match byte {
                | 0 => Ok(super::Sign::NonNegative),
                | 1 => Ok(super::Sign::Negative),
                | _ => Err(unknown(super::TagSite::Sign)),
            };
            assert_eq!(super::decode_sign(&mut reader), sign);
            assert_eq!(reader.position.0, 1);
            let kind = match byte {
                | 0 => Ok(super::DeclKind::Def),
                | 1 => Ok(super::DeclKind::Axiom),
                | 2 => Ok(super::DeclKind::AbstractType),
                | 3 => Err(DecodeError::ReservedDeclarationKind {
                    kind: super::ReservedKind::ModuleSig,
                }),
                | 4 => Err(DecodeError::ReservedDeclarationKind {
                    kind: super::ReservedKind::ModuleDef,
                }),
                | 5 => Err(DecodeError::ReservedDeclarationKind {
                    kind: super::ReservedKind::FunctorDef,
                }),
                | _ => Err(unknown(super::TagSite::DeclarationKind)),
            };
            assert_eq!(super::declaration_kind(super::WireTag::from(byte)), kind);
            if byte > 2 {
                let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
                assert_eq!(
                    super::decode_literal(&mut reader),
                    Err(unknown(super::TagSite::LiteralKind))
                );
                assert_eq!(reader.position.0, 1);
            }
        }
        let image = ArtifactImage::from([].as_slice());
        assert_eq!(
            super::decode_admission(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
        assert_eq!(
            super::decode_relation(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
        assert_eq!(
            super::decode_base_type(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
        assert_eq!(
            super::decode_side(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
        assert_eq!(
            super::decode_sign(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
        assert_eq!(
            super::decode_literal(&mut ByteReader::new(image)),
            Err(DecodeError::Truncated)
        );
    }

    #[test]
    fn counted_records_validate_content_and_consumption()
    {
        let positions = [3_u8, 0x81, 1, 0, 0x80, 1, 0x55];
        let mut reader = ByteReader::new(ArtifactImage::from(positions.as_slice()));
        let atoms = reader.read_minted_atom_table().expect("well-framed claims");
        assert!(atoms.into_iter().map(usize::from).eq([129_usize, 0, 128]));
        assert_eq!(reader.position.0, 6);
        let mut reader = ByteReader::new(ArtifactImage::from(positions.as_slice()));
        let atoms = super::decode_sealing_provenance(&mut reader).expect("well-framed claims");
        assert!(atoms.into_iter().map(usize::from).eq([129_usize, 0, 128]));
        assert_eq!(reader.position.0, 6);
        let names = [3_u8, 0, 2, 0xc3, 0xa9, 3, 0xef, 0xbc, 0x8e, 0x55];
        let mut reader = ByteReader::new(ArtifactImage::from(names.as_slice()));
        let name = super::decode_structured_name(&mut reader).expect("separator-free segments");
        assert!(
            name.segments()
                .iter()
                .map(AsRef::as_ref)
                .eq(["", "é", "．"])
        );
        assert_eq!(reader.position.0, 9);
        for bytes in [&[1_u8, 1, b'.'][..], &[1_u8, 1, 0xff][..]] {
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            assert_eq!(
                super::decode_structured_name(&mut reader),
                Err(DecodeError::Malformed {
                    site: MalformedSite::NameSegment
                })
            );
            assert_eq!(reader.position.0, 3);
        }
        for (bytes, end) in [
            (&[1_u8, 2, b'a'][..], 2_usize),
            (&[2_u8, 1, b'a'][..], 3_usize),
        ] {
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            assert_eq!(
                super::decode_structured_name(&mut reader),
                Err(DecodeError::Truncated)
            );
            assert_eq!(reader.position.0, end);
        }
        let text = [4_u8, 0xc3, 0xa9, 0, b'a', 0x55];
        let mut reader = ByteReader::new(ArtifactImage::from(text.as_slice()));
        assert_eq!(
            reader.read_text(MalformedSite::LiteralPayload).as_deref(),
            Ok("é\0a")
        );
        assert_eq!(reader.position.0, 5);
        for site in [MalformedSite::LiteralPayload, MalformedSite::NameSegment] {
            let invalid = [1_u8, 0xff];
            let mut reader = ByteReader::new(ArtifactImage::from(invalid.as_slice()));
            assert_eq!(reader.read_text(site), Err(DecodeError::Malformed { site }));
            assert_eq!(reader.position.0, 2);
            let short = [3_u8, b'a'];
            let mut reader = ByteReader::new(ArtifactImage::from(short.as_slice()));
            assert_eq!(reader.read_text(site), Err(DecodeError::Truncated));
            assert_eq!(reader.position.0, 1);
        }
        for slot in [
            super::ReservedSlot::ErasureAnnotation,
            super::ReservedSlot::ModeGradeAnnotation,
            super::ReservedSlot::DirectednessVariance,
            super::ReservedSlot::MintedAtomTable,
        ] {
            for (bytes, expected) in [
                (&[0_u8][..], Ok(())),
                (&[1_u8][..], Err(DecodeError::ReservedSlotOccupied { slot })),
                (
                    &[0x80_u8, 1][..],
                    Err(DecodeError::ReservedSlotOccupied { slot }),
                ),
                (
                    &[0x80_u8, 0][..],
                    Err(DecodeError::Malformed {
                        site: MalformedSite::Varint,
                    }),
                ),
                (&[0x80_u8][..], Err(DecodeError::Truncated)),
            ] {
                let mut reader = ByteReader::new(ArtifactImage::from(bytes));
                assert_eq!(super::expect_empty_slot(&mut reader, slot), expected);
                assert_eq!(reader.position.0, bytes.len());
            }
        }
        let slots = [0_u8, 0, 3, 0x81, 1, 0, 0x80, 1, 0, 0x55];
        let mut reader = ByteReader::new(ArtifactImage::from(slots.as_slice()));
        assert!(
            super::decode_definition_slots(&mut reader)
                .expect("empty reserved fields")
                .into_iter()
                .map(usize::from)
                .eq([129_usize, 0, 128])
        );
        assert_eq!(reader.position.0, 9);
        for (bytes, slot) in [
            (&[1_u8][..], super::ReservedSlot::ErasureAnnotation),
            (&[0_u8, 1][..], super::ReservedSlot::ModeGradeAnnotation),
            (
                &[0_u8, 0, 0, 1][..],
                super::ReservedSlot::DirectednessVariance,
            ),
        ] {
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            assert_eq!(
                super::decode_definition_slots(&mut reader),
                Err(DecodeError::ReservedSlotOccupied { slot })
            );
            assert_eq!(reader.position.0, bytes.len());
        }
        let maximal_count = [0xff_u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1];
        let image = ArtifactImage::from(maximal_count.as_slice());
        let mut reader = ByteReader::new(image);
        assert_eq!(reader.read_minted_atom_table(), Err(DecodeError::Truncated));
        assert_eq!(reader.position.0, 10);
        let mut reader = ByteReader::new(image);
        assert_eq!(
            super::decode_structured_name(&mut reader),
            Err(DecodeError::Truncated)
        );
        assert_eq!(reader.position.0, 10);
        let mut reader = ByteReader::new(image);
        assert_eq!(
            super::decode_sealing_provenance(&mut reader),
            Err(DecodeError::Truncated)
        );
        assert_eq!(reader.position.0, 10);
    }

    /// A fixed prefix with two distinguishable nodes of each family.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: globals zero through seven alternate value type, value,
    ///   computation type and computation, with distinct family-local ids.
    /// - provides: live earlier roots for polarity and ordered-edge witnesses.
    /// - panics: if the literal seed entries cease to decode.
    ///
    /// # Adequacy
    /// - hypothesis: L3 uses both same-family roots in ordered entry fixtures
    ///   and distinguishes every matching and mismatching reference family.
    /// - witness: `decode::tests::reference_families_preserve_order_and_failure_precedence`
    /// - witness: `decode::tests::decoded_entries_preserve_every_former_and_child_position`
    #[spec(ensures: |ret| ret.nodes.len() == 8
        && ret.children.len() == 8
        && ret.families.as_slice() == [super::Family::ValueType, super::Family::Value,
            super::Family::CompType, super::Family::Computation, super::Family::ValueType,
            super::Family::Value, super::Family::CompType, super::Family::Computation])]
    fn four_family_table() -> super::Table
    {
        let bytes = [1_u8, 0x0b, 7, 0, 0x13, 1, 0, 1, 9, 7, 7, 4, 0x15, 5];
        let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
        let mut table = super::Table::new();
        for _entry in 0_u8 .. 8 {
            super::decode_entry(&mut reader, &mut table).expect("literal earlier-child seed");
        }
        table
    }

    #[test]
    fn reference_families_preserve_order_and_failure_precedence()
    {
        let table = four_family_table();
        let families = [
            super::Family::ValueType,
            super::Family::Value,
            super::Family::CompType,
            super::Family::Computation,
        ];
        let nodes_equal =
            |first: super::DecodedNode, second: super::DecodedNode| match (first, second) {
                | (super::DecodedNode::ValueType(first), super::DecodedNode::ValueType(second)) => {
                    first == second
                },
                | (super::DecodedNode::Value(first), super::DecodedNode::Value(second)) => {
                    first == second
                },
                | (super::DecodedNode::CompType(first), super::DecodedNode::CompType(second)) => {
                    first == second
                },
                | (
                    super::DecodedNode::Computation(first),
                    super::DecodedNode::Computation(second),
                ) => first == second,
                | _ => false,
            };
        for index in 0_u8 ..= 9 {
            let global = super::GlobalIndex::from(u32::from(index));
            let bytes = [index];
            let family = families
                .get(usize::from(index).rem_euclid(4))
                .copied()
                .expect("four-way remainder");
            let expected_family = if index < 8 {
                Ok(family)
            }
            else {
                Err(DecodeError::Malformed {
                    site: MalformedSite::ChildOrder,
                })
            };
            assert_eq!(super::family_at(&table, global), expected_family);
            for required in families {
                let expected = if index >= 8 {
                    Err(DecodeError::Malformed {
                        site: MalformedSite::ChildOrder,
                    })
                }
                else if required != family {
                    Err(DecodeError::Malformed {
                        site: MalformedSite::Polarity,
                    })
                }
                else {
                    Ok(global)
                };
                let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
                assert_eq!(super::decode_root(&mut reader, &table, required), expected);
                assert_eq!(reader.position.0, 1);
                let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
                let prefix = [
                    super::GlobalIndex::from(6_u32),
                    super::GlobalIndex::from(4_u32),
                ];
                let mut children = prefix.to_vec();
                let next = table.next_index();
                let result = match required {
                    | super::Family::ValueType => {
                        super::read_value_type(&mut reader, &table, next, &mut children)
                            .map(super::DecodedNode::ValueType)
                    },
                    | super::Family::Value => {
                        super::read_value(&mut reader, &table, next, &mut children)
                            .map(super::DecodedNode::Value)
                    },
                    | super::Family::CompType => {
                        super::read_comp_type(&mut reader, &table, next, &mut children)
                            .map(super::DecodedNode::CompType)
                    },
                    | super::Family::Computation => {
                        super::read_computation(&mut reader, &table, next, &mut children)
                            .map(super::DecodedNode::Computation)
                    },
                };
                assert_eq!(reader.position.0, 1);
                match (result, expected) {
                    | (Ok(node), Ok(_)) => {
                        let stored = table
                            .nodes
                            .get(usize::from(index))
                            .copied()
                            .expect("live row");
                        assert!(nodes_equal(node, stored));
                        let mut expected_children = prefix.to_vec();
                        expected_children.push(global);
                        assert_eq!(children, expected_children);
                    },
                    | (Err(actual), Err(expected)) => {
                        assert_eq!(actual, expected);
                        assert_eq!(children, prefix);
                    },
                    | _ => panic!("reference family or refusal precedence changed"),
                }
            }
            let expected_type = match table.nodes.get(usize::from(index)).copied() {
                | Some(super::DecodedNode::ValueType(id)) => Some(id),
                | _ => None,
            };
            let expected_value = match table.nodes.get(usize::from(index)).copied() {
                | Some(super::DecodedNode::Value(id)) => Some(id),
                | _ => None,
            };
            assert_eq!(super::value_type_id_at(&table.nodes, global), expected_type);
            assert_eq!(super::value_id_at(&table.nodes, global), expected_value);
        }
        let mut reader = ByteReader::new(ArtifactImage::from([].as_slice()));
        let mut children = vec![super::GlobalIndex::from(4_u32)];
        assert!(matches!(
            super::read_child(
                &mut reader,
                &table,
                table.next_index(),
                super::Family::Value,
                &mut children
            ),
            Err(DecodeError::Truncated)
        ));
        assert_eq!(reader.position.0, 0);
        assert_eq!(children, [super::GlobalIndex::from(4_u32)]);
    }

    #[test]
    fn budget_scan_matches_explicit_expansion_and_saturating_boundaries()
    {
        let report = |edges: &[alloc::vec::Vec<usize>], roots: &[usize]| {
            let mut table = super::Table::new();
            for children in edges {
                let resolve = |index: usize| match table.nodes.get(index).copied() {
                    | Some(super::DecodedNode::ValueType(id)) => id,
                    | _ => panic!("fixture child must be an earlier value type"),
                };
                let first = children.first().copied().map(resolve);
                let second = children.get(1).copied().map(resolve);
                let id = match (first, second) {
                    | (None, _) => table.arena.value_type_unit(),
                    | (Some(first), None) => {
                        table.arena.value_type_lift(first, super::Level::zero())
                    },
                    | (Some(first), Some(second)) => table.arena.value_type_product(first, second),
                };
                table.nodes.push(super::DecodedNode::ValueType(id));
                table.families.push(super::Family::ValueType);
                table.children.push(
                    children
                        .iter()
                        .map(|&index| {
                            super::GlobalIndex::from(u32::try_from(index).expect("small fixture"))
                        })
                        .collect(),
                );
            }
            let metas: alloc::vec::Vec<_> = roots
                .iter()
                .map(|&root| super::DeclMeta {
                    mark: super::AdmissionMark::Checked,
                    kind: super::DeclKind::Axiom,
                    name: super::StructuredName::default(),
                    levels: super::LevelSignature::monomorphic(),
                    root_declared: super::GlobalIndex::from(
                        u32::try_from(root).expect("small fixture"),
                    ),
                    root_body: None,
                    provenance: vec![],
                })
                .collect();
            super::budget_report(&table, &metas)
        };
        let edges = [
            vec![],
            vec![0_usize],
            vec![0_usize, 0],
            vec![1_usize, 2],
            vec![2_usize, 3],
            vec![4_usize, 4],
        ];
        let roots = [5_usize, 3, 5];
        let mut maximum = 0_u128;
        let mut total = 0_u128;
        for root in roots {
            let mut pending = vec![root];
            let mut expanded = 0_u128;
            while let Some(index) = pending.pop() {
                expanded = expanded.checked_add(1).expect("small explicit expansion");
                pending.extend(
                    edges
                        .get(index)
                        .expect("earlier fixture child")
                        .iter()
                        .copied(),
                );
            }
            maximum = maximum.max(expanded);
            total = total
                .checked_add(expanded)
                .expect("small explicit expansion");
        }
        let metrics = report(&edges, &roots);
        assert_eq!(usize::from(metrics.table_entries()), edges.len());
        assert_eq!(
            u128::from(u64::from(metrics.max_declaration_expanded_work())),
            maximum
        );
        assert_eq!(
            u128::from(u64::from(metrics.artifact_expanded_work())),
            total
        );
        let empty = report(&edges, &[]);
        assert_eq!(usize::from(empty.table_entries()), edges.len());
        assert_eq!(u64::from(empty.max_declaration_expanded_work()), 0);
        assert_eq!(u64::from(empty.artifact_expanded_work()), 0);
        let missing = report(&edges, &[99_usize]);
        assert_eq!(u64::from(missing.max_declaration_expanded_work()), u64::MAX);
        assert_eq!(u64::from(missing.artifact_expanded_work()), u64::MAX);
        let mut diamonds = vec![vec![]];
        for index in 1_usize ..= 64 {
            let child = index.saturating_sub(1);
            diamonds.push(vec![child, child]);
        }
        for root in [0_usize, 1, 31, 62, 63, 64] {
            let shift = u32::try_from(root.saturating_add(1)).expect("small exponent");
            let expanded = 1_u128
                .checked_shl(shift)
                .expect("widened arithmetic")
                .saturating_sub(1);
            let expected = u64::try_from(expanded).unwrap_or(u64::MAX);
            let metrics = report(&diamonds, &[root, root]);
            assert_eq!(u64::from(metrics.max_declaration_expanded_work()), expected);
            assert_eq!(
                u64::from(metrics.artifact_expanded_work()),
                u64::try_from(expanded.saturating_mul(2)).unwrap_or(u64::MAX)
            );
        }
        let table = four_family_table();
        let meta = super::DeclMeta {
            mark: super::AdmissionMark::Checked,
            kind: super::DeclKind::Def,
            name: super::StructuredName::default(),
            levels: super::LevelSignature::monomorphic(),
            root_declared: super::GlobalIndex::from(0_u32),
            root_body: Some(super::GlobalIndex::from(5_u32)),
            provenance: vec![],
        };
        let metrics = super::budget_report(&table, &[meta]);
        assert_eq!(u64::from(metrics.max_declaration_expanded_work()), 1);
        assert_eq!(u64::from(metrics.artifact_expanded_work()), 2);
        let root_cap = u64::from(super::MAX_EXPANDED_TERM_WORK);
        let artifact_cap = u64::from(super::MAX_ARTIFACT_EXPANDED_WORK);
        for root in [
            root_cap.saturating_sub(1),
            root_cap,
            root_cap.saturating_add(1),
        ] {
            for total in [
                artifact_cap.saturating_sub(1),
                artifact_cap,
                artifact_cap.saturating_add(1),
            ] {
                let metrics = super::DecodeMetrics::new(
                    super::TableEntryCount::from(0_usize),
                    super::ExpandedWork::from(root),
                    super::ExpandedWork::from(total),
                );
                let expected = if root > root_cap {
                    Err(DecodeError::Malformed {
                        site: MalformedSite::ExpandedWork,
                    })
                }
                else if total > artifact_cap {
                    Err(DecodeError::Malformed {
                        site: MalformedSite::ArtifactExpandedWork,
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(super::check_budget(metrics), expected);
            }
        }
    }

    #[test]
    fn normalized_levels_and_literals_are_not_wire_acceptance()
    {
        let literal_artifact = |base: u8, literal: &[u8]| {
            let mut bytes = vec![
                b'G', b'K', b'X', b'1', 2, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, base, 0x0c,
            ];
            bytes.extend_from_slice(literal);
            bytes.extend_from_slice(&[0, 1, 0, 0, 0, 0]);
            bytes
        };
        let integer_cases: &[(&[u8], &[u8], super::Sign, &str)] = &[
            (
                &[0, 1, 1, b'0'],
                &[0, 0, 1, b'0'],
                super::Sign::NonNegative,
                "0",
            ),
            (
                &[0, 0, 3, b'0', b'0', b'7'],
                &[0, 0, 1, b'7'],
                super::Sign::NonNegative,
                "7",
            ),
            (
                &[0, 1, 3, b'0', b'0', b'7'],
                &[0, 1, 1, b'7'],
                super::Sign::Negative,
                "7",
            ),
        ];
        for &(raw, canonical, sign, digits) in integer_cases {
            let mut reader = ByteReader::new(ArtifactImage::from(raw));
            let super::Literal::Integer(value) =
                super::decode_literal(&mut reader).expect("decimal payload")
            else {
                panic!("integer kind");
            };
            assert_eq!(value.sign(), sign);
            assert_eq!(value.magnitude().as_ref(), digits);
            assert_eq!(reader.position.0, raw.len());
            let raw = literal_artifact(0, raw);
            assert_eq!(
                super::decode(ArtifactImage::from(raw.as_slice())),
                Err(DecodeError::Malformed {
                    site: MalformedSite::NonCanonical
                })
            );
            let canonical = literal_artifact(0, canonical);
            let decoded = super::decode(ArtifactImage::from(canonical.as_slice()))
                .expect("canonical partner");
            assert_eq!(decoded.declarations().len(), 1);
            assert_eq!(
                decoded.metrics().table_entries(),
                super::TableEntryCount::from(2_usize)
            );
        }
        let numeric_cases = [
            (
                &[2_u8, 1, 3, b'0', b'0', b'7', 4, b'1', b'2', b'0', b'0'][..],
                &[2_u8, 1, 1, b'7', 2, b'1', b'2'][..],
                super::Sign::Negative,
                "7",
                "12",
            ),
            (
                &[2_u8, 1, 1, b'0', 2, b'0', b'0'][..],
                &[2_u8, 0, 1, b'0', 0][..],
                super::Sign::NonNegative,
                "0",
                "",
            ),
        ];
        for (raw, canonical, sign, integer, fraction) in numeric_cases {
            let mut reader = ByteReader::new(ArtifactImage::from(raw));
            let super::Literal::Numeric(value) =
                super::decode_literal(&mut reader).expect("decimal payload")
            else {
                panic!("numeric kind");
            };
            assert_eq!(value.sign(), sign);
            assert_eq!(value.integer_part().as_ref(), integer);
            assert_eq!(value.fraction().as_ref(), fraction);
            assert_eq!(reader.position.0, raw.len());
            let raw = literal_artifact(2, raw);
            assert_eq!(
                super::decode(ArtifactImage::from(raw.as_slice())),
                Err(DecodeError::Malformed {
                    site: MalformedSite::NonCanonical
                })
            );
            let canonical = literal_artifact(2, canonical);
            let decoded = super::decode(ArtifactImage::from(canonical.as_slice()))
                .expect("canonical partner");
            assert_eq!(
                decoded.metrics().table_entries(),
                super::TableEntryCount::from(2_usize)
            );
        }
        let text = [1_u8, 4, 0xc3, 0xa9, 0, b'a'];
        let mut reader = ByteReader::new(ArtifactImage::from(text.as_slice()));
        let super::Literal::Text(value) = super::decode_literal(&mut reader).expect("UTF-8 text")
        else {
            panic!("text kind");
        };
        assert_eq!(value.as_ref(), "é\0a");
        assert_eq!(reader.position.0, text.len());
        for text in [
            &[0_u8][..],
            &[1_u8, b'+'][..],
            &[3_u8, 0xef, 0xbc, 0x97][..],
        ] {
            let mut reader = ByteReader::new(ArtifactImage::from(text));
            assert_eq!(
                super::decode_magnitude(&mut reader),
                Err(DecodeError::Malformed {
                    site: MalformedSite::LiteralPayload
                })
            );
            assert_eq!(reader.position.0, text.len());
        }
        let empty_fraction = [0_u8];
        let mut reader = ByteReader::new(ArtifactImage::from(empty_fraction.as_slice()));
        assert_eq!(
            super::decode_fraction(&mut reader)
                .expect("empty fraction")
                .as_ref(),
            ""
        );
        let bad_fraction = [1_u8, b'-'];
        let mut reader = ByteReader::new(ArtifactImage::from(bad_fraction.as_slice()));
        assert_eq!(
            super::decode_fraction(&mut reader),
            Err(DecodeError::Malformed {
                site: MalformedSite::LiteralPayload
            })
        );
        let level_artifact = |level: &[u8]| {
            let mut bytes = vec![b'G', b'K', b'X', b'1', 2, 0, 0, 1, 0, 1, 0, 3, 0, 1, 2];
            bytes.extend_from_slice(level);
            bytes.push(0);
            bytes
        };
        let level_cases = [
            (
                &[0_u8, 2, 0, 0, 0, 0][..],
                &[0_u8, 1, 0, 0][..],
                &[(0_u32, 0_u64)][..],
            ),
            (
                &[0_u8, 2, 0, 1, 0, 0][..],
                &[0_u8, 1, 0, 1][..],
                &[(0_u32, 1_u64)][..],
            ),
            (
                &[0_u8, 2, 2, 0, 0, 1][..],
                &[0_u8, 2, 0, 1, 2, 0][..],
                &[(0_u32, 1_u64), (2_u32, 0_u64)][..],
            ),
        ];
        for (raw, canonical, atoms) in level_cases {
            let mut reader = ByteReader::new(ArtifactImage::from(raw));
            let level = super::decode_level(&mut reader).expect("normalizable level");
            assert_eq!(u64::from(level.constant_part()), 0);
            assert!(
                level
                    .atoms()
                    .map(|(variable, amount)| (u32::from(variable.index()), u64::from(amount)))
                    .eq(atoms.iter().copied())
            );
            assert_eq!(reader.position.0, raw.len());
            let raw = level_artifact(raw);
            assert_eq!(
                super::decode(ArtifactImage::from(raw.as_slice())),
                Err(DecodeError::Malformed {
                    site: MalformedSite::NonCanonical
                })
            );
            let canonical = level_artifact(canonical);
            let decoded = super::decode(ArtifactImage::from(canonical.as_slice()))
                .expect("canonical level partner");
            assert_eq!(
                decoded.metrics().table_entries(),
                super::TableEntryCount::from(1_usize)
            );
        }
        let cap = u64::from(super::MAX_DECODED_LEVEL_OFFSET);
        for variable in [0_u32, 1, u32::MAX] {
            for offset in [0_u64, 1, cap.saturating_sub(1)] {
                let atom = super::build_variable_atom(
                    super::WireU32::from(variable),
                    super::WireU64::from(offset),
                )
                .expect("offset below cap");
                assert_eq!(u64::from(atom.constant_part()), 0);
                assert!(
                    atom.atoms()
                        .map(|(found, amount)| (u32::from(found.index()), u64::from(amount)))
                        .eq([(variable, offset)])
                );
            }
        }
        let x = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(0_u32)));
        let y = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(1_u32)));
        for relation in [0_u8, 1] {
            let bytes = [2_u8, 1, relation, 0, 1, 0, 0, 0, 1, 1, 0];
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            let signature =
                super::decode_level_signature(&mut reader).expect("variable-only constraint");
            let expected = if relation == 0 {
                super::LandmarkConstraint::leq(x.clone(), y.clone())
            }
            else {
                super::LandmarkConstraint::equal(x.clone(), y.clone())
            }
            .expect("valid sides");
            assert_eq!(u32::from(signature.params()), 2);
            assert_eq!(signature.constraints(), [expected]);
            assert_eq!(reader.position.0, bytes.len());
        }
        let invalid_side = [0_u8, 1, 0, 1, 0, 0, 1, 0, 0];
        let mut reader = ByteReader::new(ArtifactImage::from(invalid_side.as_slice()));
        assert_eq!(
            super::decode_level_signature(&mut reader),
            Err(DecodeError::Malformed {
                site: MalformedSite::ConstraintForm
            })
        );
        assert_eq!(reader.position.0, invalid_side.len());
        let unknown_relation = [0_u8, 1, 3];
        let mut reader = ByteReader::new(ArtifactImage::from(unknown_relation.as_slice()));
        assert_eq!(
            super::decode_level_signature(&mut reader),
            Err(DecodeError::UnknownTag {
                site: super::TagSite::ConstraintRelation,
                tag: super::WireTag::from(3_u8)
            })
        );
        assert_eq!(reader.position.0, 3);
        let maximal_count = [
            0_u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1,
        ];
        let mut reader = ByteReader::new(ArtifactImage::from(maximal_count.as_slice()));
        assert_eq!(
            super::decode_level_signature(&mut reader),
            Err(DecodeError::Truncated)
        );
        assert_eq!(reader.position.0, maximal_count.len());
    }

    #[test]
    fn decoded_entries_preserve_every_former_and_child_position()
    {
        let mut table = four_family_table();
        let &[
            super::DecodedNode::ValueType(vt0),
            super::DecodedNode::Value(v0),
            super::DecodedNode::CompType(ct0),
            super::DecodedNode::Computation(c0),
            super::DecodedNode::ValueType(vt1),
            super::DecodedNode::Value(v1),
            super::DecodedNode::CompType(ct1),
            super::DecodedNode::Computation(c1),
        ] = table.nodes.as_slice()
        else {
            panic!("four-family seed");
        };
        let level = super::Level::constant(super::LevelConstant::from(7_u64));
        let value_types: &[(&[u8], crate::types::ValueType, &[u32])] = &[
            (
                &[0, 0],
                crate::types::ValueType::Base(super::BaseType::Integer),
                &[],
            ),
            (
                &[0, 1],
                crate::types::ValueType::Base(super::BaseType::String),
                &[],
            ),
            (
                &[0, 2],
                crate::types::ValueType::Base(super::BaseType::Numeric),
                &[],
            ),
            (&[1], crate::types::ValueType::Unit, &[]),
            (
                &[2, 7, 0],
                crate::types::ValueType::Universe {
                    sort: super::GroundSort::Value,
                    level: level.clone(),
                },
                &[],
            ),
            (&[3, 4, 0], crate::types::ValueType::Product(vt1, vt0), &[
                4, 0,
            ]),
            (&[4, 0, 4], crate::types::ValueType::Sum(vt0, vt1), &[0, 4]),
            (&[5, 6], crate::types::ValueType::Thunk(ct1), &[6]),
            (
                &[6, 7, 0, 4],
                crate::types::ValueType::Lift {
                    inner: vt1,
                    target: level.clone(),
                },
                &[4],
            ),
            (
                &[0x17, 0x81, 1],
                crate::types::ValueType::Abstract(super::ConstantIndex::from(129_usize)),
                &[],
            ),
            (
                &[0x19, 7, 0, 5],
                crate::types::ValueType::Element {
                    code: v1,
                    target: level.clone(),
                },
                &[5],
            ),
            (
                &[0x1a, 7, 0],
                crate::types::ValueType::Universe {
                    sort: super::GroundSort::Computation,
                    level: level.clone(),
                },
                &[],
            ),
            (
                &[0x1e, 4, 0],
                crate::types::ValueType::StaticPi {
                    domain: vt1,
                    codomain: vt0,
                },
                &[4, 0],
            ),
        ];
        for &(bytes, ref expected, children) in value_types {
            let before = table.arena.watermark();
            let count = table.nodes.len();
            for end in 0 .. bytes.len() {
                let prefix = bytes.get(.. end).expect("proper prefix");
                let mut reader = ByteReader::new(ArtifactImage::from(prefix));
                assert_eq!(
                    super::decode_entry(&mut reader, &mut table),
                    Err(DecodeError::Truncated)
                );
                assert_eq!(table.arena.watermark(), before);
                assert_eq!(table.nodes.len(), count);
                assert_eq!(table.families.len(), count);
                assert_eq!(table.children.len(), count);
            }
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            super::decode_entry(&mut reader, &mut table).expect("literal complete entry");
            assert_eq!(reader.position.0, bytes.len());
            assert_eq!(table.nodes.len(), count.saturating_add(1));
            assert_eq!(table.families.last(), Some(&super::Family::ValueType));
            let super::DecodedNode::ValueType(id) =
                table.nodes.last().copied().expect("appended row")
            else {
                panic!("wrong node family");
            };
            assert_eq!(table.arena.value_type(id), Some(expected));
            assert!(
                table
                    .children
                    .last()
                    .expect("ordered edges")
                    .iter()
                    .copied()
                    .map(u32::from)
                    .eq(children.iter().copied())
            );
        }
        let comp_types: &[(&[u8], crate::types::CompType, &[u32])] = &[
            (&[7, 4], crate::types::CompType::Returner(vt1), &[4]),
            (
                &[8, 4, 2],
                crate::types::CompType::Arrow {
                    domain: vt1,
                    codomain: ct0,
                },
                &[4, 2],
            ),
            (
                &[0x18, 0, 6],
                crate::types::CompType::Pi {
                    domain: vt0,
                    codomain: ct1,
                },
                &[0, 6],
            ),
            (
                &[0x1b, 7, 0, 5],
                crate::types::CompType::Element {
                    code: v1,
                    target: level.clone(),
                },
                &[5],
            ),
        ];
        for &(bytes, ref expected, children) in comp_types {
            let before = table.arena.watermark();
            let count = table.nodes.len();
            for end in 0 .. bytes.len() {
                let prefix = bytes.get(.. end).expect("proper prefix");
                let mut reader = ByteReader::new(ArtifactImage::from(prefix));
                assert_eq!(
                    super::decode_entry(&mut reader, &mut table),
                    Err(DecodeError::Truncated)
                );
                assert_eq!(table.arena.watermark(), before);
                assert_eq!(table.nodes.len(), count);
                assert_eq!(table.families.len(), count);
                assert_eq!(table.children.len(), count);
            }
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            super::decode_entry(&mut reader, &mut table).expect("literal complete entry");
            assert_eq!(reader.position.0, bytes.len());
            assert_eq!(table.nodes.len(), count.saturating_add(1));
            assert_eq!(table.families.last(), Some(&super::Family::CompType));
            let super::DecodedNode::CompType(id) =
                table.nodes.last().copied().expect("appended row")
            else {
                panic!("wrong node family");
            };
            assert_eq!(table.arena.comp_type(id), Some(expected));
            assert!(
                table
                    .children
                    .last()
                    .expect("ordered edges")
                    .iter()
                    .copied()
                    .map(u32::from)
                    .eq(children.iter().copied())
            );
        }
        let values: &[(&[u8], crate::term::Value, &[u32])] = &[
            (
                &[9, 0x81, 1],
                crate::term::Value::Variable(super::DeBruijnIndex::from(129_u32)),
                &[],
            ),
            (
                &[0x0a, 0x81, 1],
                crate::term::Value::Constant(super::ConstantIndex::from(129_usize)),
                &[],
            ),
            (&[0x0b], crate::term::Value::Unit, &[]),
            (
                &[0x0c, 0, 1, 1, b'7'],
                crate::term::Value::Literal(super::Literal::Integer(super::IntegerLiteral::new(
                    super::Sign::Negative,
                    super::Magnitude::from_decimal_text(alloc::string::String::from("7"))
                        .expect("decimal fixture"),
                ))),
                &[],
            ),
            (&[0x0d, 5, 1], crate::term::Value::Pair(v1, v0), &[5, 1]),
            (
                &[0x0e, 0, 1],
                crate::term::Value::Injection(super::Side::Left, v0),
                &[1],
            ),
            (
                &[0x0e, 1, 5],
                crate::term::Value::Injection(super::Side::Right, v1),
                &[5],
            ),
            (&[0x0f, 7], crate::term::Value::Thunk(c1), &[7]),
            (
                &[0x10, 7, 0, 5],
                crate::term::Value::Lift {
                    target: level,
                    body: v1,
                },
                &[5],
            ),
            (&[0x1c, 4], crate::term::Value::Quote(vt1), &[4]),
            (&[0x1d, 6], crate::term::Value::QuoteComputation(ct1), &[6]),
            (
                &[0x1f, 5, 1],
                crate::term::Value::StaticApplication(v1, v0),
                &[5, 1],
            ),
        ];
        for &(bytes, ref expected, children) in values {
            let before = table.arena.watermark();
            let count = table.nodes.len();
            for end in 0 .. bytes.len() {
                let prefix = bytes.get(.. end).expect("proper prefix");
                let mut reader = ByteReader::new(ArtifactImage::from(prefix));
                assert_eq!(
                    super::decode_entry(&mut reader, &mut table),
                    Err(DecodeError::Truncated)
                );
                assert_eq!(table.arena.watermark(), before);
                assert_eq!(table.nodes.len(), count);
                assert_eq!(table.families.len(), count);
                assert_eq!(table.children.len(), count);
            }
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            super::decode_entry(&mut reader, &mut table).expect("literal complete entry");
            assert_eq!(reader.position.0, bytes.len());
            assert_eq!(table.nodes.len(), count.saturating_add(1));
            assert_eq!(table.families.last(), Some(&super::Family::Value));
            let super::DecodedNode::Value(id) = table.nodes.last().copied().expect("appended row")
            else {
                panic!("wrong node family");
            };
            assert_eq!(table.arena.value(id), Some(expected));
            assert!(
                table
                    .children
                    .last()
                    .expect("ordered edges")
                    .iter()
                    .copied()
                    .map(u32::from)
                    .eq(children.iter().copied())
            );
        }
        let computations: &[(&[u8], crate::term::Computation, &[u32])] = &[
            (&[0x11, 7], crate::term::Computation::Lambda(c1), &[7]),
            (
                &[0x12, 7, 5],
                crate::term::Computation::Application(c1, v1),
                &[7, 5],
            ),
            (&[0x13, 5], crate::term::Computation::Return(v1), &[5]),
            (&[0x14, 7, 3], crate::term::Computation::Bind(c1, c0), &[
                7, 3,
            ]),
            (&[0x15, 5], crate::term::Computation::Force(v1), &[5]),
            (
                &[0x16, 5, 7, 3],
                crate::term::Computation::Case {
                    scrutinee: v1,
                    on_left: c1,
                    on_right: c0,
                },
                &[5, 7, 3],
            ),
        ];
        for &(bytes, ref expected, children) in computations {
            let before = table.arena.watermark();
            let count = table.nodes.len();
            for end in 0 .. bytes.len() {
                let prefix = bytes.get(.. end).expect("proper prefix");
                let mut reader = ByteReader::new(ArtifactImage::from(prefix));
                assert_eq!(
                    super::decode_entry(&mut reader, &mut table),
                    Err(DecodeError::Truncated)
                );
                assert_eq!(table.arena.watermark(), before);
                assert_eq!(table.nodes.len(), count);
                assert_eq!(table.families.len(), count);
                assert_eq!(table.children.len(), count);
            }
            let mut reader = ByteReader::new(ArtifactImage::from(bytes));
            super::decode_entry(&mut reader, &mut table).expect("literal complete entry");
            assert_eq!(reader.position.0, bytes.len());
            assert_eq!(table.nodes.len(), count.saturating_add(1));
            assert_eq!(table.families.last(), Some(&super::Family::Computation));
            let super::DecodedNode::Computation(id) =
                table.nodes.last().copied().expect("appended row")
            else {
                panic!("wrong node family");
            };
            assert_eq!(table.arena.computation(id), Some(expected));
            assert!(
                table
                    .children
                    .last()
                    .expect("ordered edges")
                    .iter()
                    .copied()
                    .map(u32::from)
                    .eq(children.iter().copied())
            );
        }
        let count = table.nodes.len();
        let watermark = table.arena.watermark();
        for tag in 0x20_u8 ..= u8::MAX {
            let bytes = [tag];
            let mut reader = ByteReader::new(ArtifactImage::from(bytes.as_slice()));
            assert_eq!(
                super::decode_entry(&mut reader, &mut table),
                Err(DecodeError::UnknownTag {
                    site: super::TagSite::Node,
                    tag: super::WireTag::from(tag)
                })
            );
            assert_eq!(reader.position.0, 1);
            assert_eq!(table.nodes.len(), count);
            assert_eq!(table.arena.watermark(), watermark);
        }
        assert_eq!(
            table.arena.value_type(vt0),
            Some(&crate::types::ValueType::Unit)
        );
        assert_eq!(
            table.arena.value_type(vt1),
            Some(&crate::types::ValueType::Base(super::BaseType::String))
        );
        assert_eq!(table.arena.value(v0), Some(&crate::term::Value::Unit));
        assert_eq!(
            table.arena.value(v1),
            Some(&crate::term::Value::Variable(super::DeBruijnIndex::from(
                7_u32
            )))
        );
        assert_eq!(
            table.arena.comp_type(ct0),
            Some(&crate::types::CompType::Returner(vt0))
        );
        assert_eq!(
            table.arena.comp_type(ct1),
            Some(&crate::types::CompType::Returner(vt1))
        );
        assert_eq!(
            table.arena.computation(c0),
            Some(&crate::term::Computation::Return(v0))
        );
        assert_eq!(
            table.arena.computation(c1),
            Some(&crate::term::Computation::Force(v1))
        );
    }

    #[test]
    fn declaration_assembly_preserves_claims_and_consumes_names()
    {
        let mut table = four_family_table();
        let declared = super::value_type_id_at(&table.nodes, super::GlobalIndex::from(4_u32))
            .expect("string type");
        let unit = super::value_type_id_at(&table.nodes, super::GlobalIndex::from(0_u32))
            .expect("unit type");
        let body = super::value_id_at(&table.nodes, super::GlobalIndex::from(5_u32))
            .expect("variable body");
        let name = |parts: &[&str]| {
            super::StructuredName::from(
                parts
                    .iter()
                    .map(|&part| {
                        super::NameSegment::from_text(alloc::string::String::from(part))
                            .expect("separator-free fixture")
                    })
                    .collect::<alloc::vec::Vec<_>>(),
            )
        };
        let variable =
            |index| super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(index)));
        let levels = super::LevelSignature::new(super::LevelParamCount::from(2_u32), vec![
            super::LandmarkConstraint::leq(variable(0_u32), variable(1_u32))
                .expect("variable-only sides"),
        ]);
        let mut metas = [
            super::DeclMeta {
                mark: super::AdmissionMark::UncheckedBypass,
                kind: super::DeclKind::Def,
                name: name(&["definition", "é"]),
                levels,
                root_declared: super::GlobalIndex::from(4_u32),
                root_body: Some(super::GlobalIndex::from(5_u32)),
                provenance: vec![
                    super::ConstantIndex::from(129_usize),
                    super::ConstantIndex::from(0_usize),
                    super::ConstantIndex::from(128_usize),
                ],
            },
            super::DeclMeta {
                mark: super::AdmissionMark::Checked,
                kind: super::DeclKind::Axiom,
                name: name(&[""]),
                levels: super::LevelSignature::monomorphic(),
                root_declared: super::GlobalIndex::from(0_u32),
                root_body: None,
                provenance: vec![],
            },
            super::DeclMeta {
                mark: super::AdmissionMark::Checked,
                kind: super::DeclKind::AbstractType,
                name: name(&[]),
                levels: super::LevelSignature::new(super::LevelParamCount::from(1_u32), vec![]),
                root_declared: super::GlobalIndex::from(4_u32),
                root_body: None,
                provenance: vec![],
            },
        ];
        let arena_before = table.arena.clone();
        let declarations = super::build_declarations(&mut table, &mut metas);
        assert_eq!(table.arena, arena_before);
        let expected = [
            super::DeclarationContent::Def { declared, body },
            super::DeclarationContent::Axiom { declared: unit },
            super::DeclarationContent::AbstractType { kind: declared },
        ];
        let names: &[&[&str]] = &[&["definition", "é"], &[""], &[]];
        assert_eq!(declarations.len(), 3);
        for (((marked, meta), content), &parts) in declarations
            .iter()
            .zip(metas.iter())
            .zip(expected)
            .zip(names)
        {
            assert_eq!(marked.mark(), meta.mark);
            assert_eq!(marked.declaration().content(), &content);
            assert_eq!(marked.declaration().levels(), &meta.levels);
            assert_eq!(marked.declaration().provenance(), meta.provenance);
            assert!(
                marked
                    .declaration()
                    .name()
                    .segments()
                    .iter()
                    .map(AsRef::as_ref)
                    .eq(parts.iter().copied())
            );
            assert!(meta.name.segments().is_empty());
        }
        let empty = super::build_declarations(&mut table, &mut []);
        assert_eq!(empty, []);
        assert_eq!(table.arena, arena_before);
    }

    #[test]
    fn an_overlong_varint_is_refused()
    {
        let overlong = MalformedSite::Varint;
        // A redundant trailing zero group: a second image of the value one.
        let redundant = vec![0x81_u8, 0x00];
        let mut reader = ByteReader::new(ArtifactImage::from(redundant.as_slice()));
        assert_eq!(
            Err(DecodeError::Malformed { site: overlong }),
            reader.read_uvarint(),
            "a redundant continuation group is a second image of one value"
        );

        // Eleven groups: more than sixty-four bits admit.
        let too_many = vec![0x80_u8; 11];
        let mut reader = ByteReader::new(ArtifactImage::from(too_many.as_slice()));
        assert_eq!(
            Err(DecodeError::Malformed { site: overlong }),
            reader.read_uvarint(),
            "an encoding longer than the integer width is refused"
        );

        // A tenth group carrying more than the single remaining bit.
        let over_range = vec![
            0x80_u8, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02,
        ];
        let mut reader = ByteReader::new(ArtifactImage::from(over_range.as_slice()));
        assert_eq!(
            Err(DecodeError::Malformed { site: overlong }),
            reader.read_uvarint(),
            "a value beyond the integer range is refused"
        );
    }

    #[test]
    fn a_truncated_varint_is_refused_as_truncation()
    {
        let dangling = vec![0x80_u8];
        let mut reader = ByteReader::new(ArtifactImage::from(dangling.as_slice()));
        assert_eq!(
            Err(DecodeError::Truncated),
            reader.read_uvarint(),
            "a continuation with no successor ends mid-field"
        );
    }
}
