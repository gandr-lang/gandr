//! The validating decoder: canonical bytes back to a shared arena and an
//! admission-ordered declaration sequence.
//!
//! # Decode is arena construction
//!
//! Each subterm-table entry is validated as it accrues and minted **once** into
//! the arena, and post-order completion is allocation order — so **decode
//! retains sharing**: a table index referenced twice reuses one arena id and
//! never expands. That is the whole reason the representation and the format
//! stop being two designs; a table entry *is* an arena id.
//!
//! # What every entry is checked for, before anything downstream sees it
//!
//! - a tag inside the frozen block, otherwise a named refusal at a named site;
//! - each child index **strictly earlier** than the entry's own global index,
//!   which is acyclicity and topological order at once;
//! - each child of the polarity its parent's slot requires, decided by a table
//!   lookup rather than by an expectation threaded through the parser;
//! - the entry cap, enforced as entries accrue so a refusal truncates early.
//!
//! Then one forward scan computes every entry's memoized expanded size and the
//! two work budgets refuse an over-budget artifact **before any consumer sees
//! it**, and the whole-artifact re-encode-compare refuses a non-canonical one.
//!
//! # Canonical form is enforced by re-encoding, not by inspection
//!
//! An artifact is canonical exactly when: every variable-length integer is
//! minimal, every inline level canonical, every literal canonical; the table is
//! maximally shared, since otherwise re-encoding merges two entries and the
//! byte count differs; entries are in post-order first-completion order, since
//! any permutation re-encodes to a different index assignment; there are no
//! dead entries, since an unreferenced entry re-encodes away; and every child
//! index is strictly less than its own, which is checked structurally here
//! before re-encoding.
//!
//! The mechanism needed no separate implementation, because **the maximal-
//! sharing encoder is the re-encoder** — and that encoder is itself
//! sharing-aware, which is the sharpening not to miss: a re-encoder walking the
//! graph as a tree would turn the canonical check into an amplification vector.
//! The work budget runs first and bounds it, and the encoder is graph-aware on
//! its own terms besides.

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
    #[inline]
    fn next_index(&self) -> GlobalIndex
    {
        GlobalIndex::from(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX))
    }
}

/// Which live declaration kind a decoded segment carried.
///
/// A missing body root no longer distinguishes them: an axiom and an abstract
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
struct DeclMeta
{
    /// The admission mark.
    mark: AdmissionMark,
    /// Which live kind the segment carried.
    kind: DeclKind,
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

/// A fully decoded artifact: the arena its declarations' content lives in, the
/// admission-ordered declaration sequence addressing it, and the deterministic
/// budget metrics computed en route.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DecodedArtifact
{
    /// The arena every decoded declaration's content lives in.
    arena: TermArena,
    /// The decoded declarations, in admission order.
    declarations: Vec<MarkedDeclaration>,
    /// The deterministic decode-budget metrics.
    metrics: DecodeMetrics,
}

impl DecodedArtifact
{
    /// The arena the declarations' content was decoded into.
    #[inline]
    #[must_use]
    pub const fn arena(&self) -> &TermArena
    {
        &self.arena
    }

    /// The decoded declarations, in admission order.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> &[MarkedDeclaration]
    {
        &self.declarations
    }

    /// The deterministic decode-budget metrics.
    #[inline]
    #[must_use]
    pub const fn metrics(&self) -> DecodeMetrics
    {
        self.metrics
    }
}

/// Decode an artifact image into its declaration sequence and shared arena.
///
/// # Specification
/// - requires: nothing — `image` may be arbitrary or adversarial.
/// - ensures: an artifact is returned exactly when the bytes are the canonical
///   encoding of a sequence whose every entry validates — a tag inside the
///   frozen block, strictly-earlier and polarity-correct children, the entry
///   cap respected, both expanded-work budgets respected — and whose levels,
///   constraints and literals rebuild through their constructors. The returned
///   arena retains the format's sharing, so a table index referenced twice
///   resolves to one id; the metrics are functions of the canonical bytes
///   alone.
/// - provides: the re-checkable decode: a total parser over a closed vocabulary
///   whose acceptance is a bounded-work guarantee for everything downstream.
///   The clause checks the returned work bounds. Full canonical acceptance,
///   sharing and metric derivation stay prose: replaying decode would recurse,
///   and re-encoding would allocate another image rather than independently
///   validate the graph-to-bytes relation.
/// - fails: [`DecodeError`] — the rejection triple, a reserved declaration
///   kind, a reserved slot or a refuted minted-atom table, or an unsupported
///   version. It never panics and never loops unboundedly.
/// - panics: none.
/// - intension: the whole decode is iterative over the flat entry list and the
///   budget scan is a single forward pass, so the cost is linear in the entry
///   count and the recursion depth is zero at every input depth.
///
/// # Errors
/// Any [`DecodeError`].
///
/// # Adequacy
/// - hypothesis: L2 — the round-trip differential pins acceptance of every
///   genuine artifact with its sharing, and the totality property pins that
///   truncation at every prefix and arbitrary bytes return rather than panic;
///   the L3 residues are each named refusal — the version, the four
///   canonical-form violations, both work budgets, the entry cap and the level
///   offset — pinned by goldens whose shape is derived from the constants.
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::truncation_at_every_prefix_is_refused_without_panicking`
/// - witness: `sharing_format::sharing_format::arbitrary_bytes_never_panic`
/// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
/// - witness: `sharing_format::sharing_format::a_duplicate_entry_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_mis_ordered_table_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_dead_entry_is_refused_as_non_canonical`
/// - witness: `sharing_format::sharing_format::a_self_or_forward_child_reference_is_refused`
/// - witness: `sharing_format::sharing_format::a_repeated_diamond_is_refused_before_any_consumer`
/// - witness: `sharing_format::sharing_format::many_cheap_segments_sharing_one_root_are_refused`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|artifact|
    artifact.metrics.table_entries() <= MAX_TABLE_ENTRIES
        && artifact.metrics.max_declaration_expanded_work() <= MAX_EXPANDED_TERM_WORK
        && artifact.metrics.artifact_expanded_work() <= MAX_ARTIFACT_EXPANDED_WORK))]
pub fn decode(image: ArtifactImage<'_>) -> Result<DecodedArtifact, DecodeError>
{
    let mut reader = ByteReader::new(image);
    reader.expect_magic()?;
    reader.expect_version()?;
    let declared_atoms = reader.read_minted_atom_table()?;
    let count = reader.read_uvarint()?;
    let mut table = Table::new();
    let mut metas: Vec<DeclMeta> = Vec::new();
    let mut remaining = u64::from(count);
    while remaining > 0_u64 {
        let meta = decode_declaration(&mut reader, &mut table)?;
        metas.push(meta);
        remaining = remaining.wrapping_sub(1_u64);
    }
    if reader.position < image.length() {
        return Err(DecodeError::Malformed {
            site: MalformedSite::TrailingBytes,
        });
    }
    let metrics = budget_report(&table, &metas);
    check_budget(metrics)?;
    let declarations = build_declarations(&mut table, &metas);
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
/// - requires: `metrics` is the budget report of the decoded table.
/// - ensures: acceptance exactly when the maximum per-declaration-root expanded
///   size is within the per-declaration cap and the artifact-total expanded
///   size is within the artifact cap.
/// - provides: the checker-time bound, enforced structurally on the table and
///   before any consumer is handed the artifact.
/// - fails: [`DecodeError::Malformed`] at the per-declaration site first, which
///   is the tighter and more specific refusal, then at the artifact-total site.
/// - panics: none.
#[spec(ensures: |ret| ret.is_ok()
    == (metrics.max_declaration_expanded_work() <= MAX_EXPANDED_TERM_WORK
        && metrics.artifact_expanded_work() <= MAX_ARTIFACT_EXPANDED_WORK))]
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
/// - hypothesis: L2 — a well-formed sealed artifact round-trips; the L3
///   residues are the three refutations, pinned by hand-mutated tables.
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
/// - requires: each meta's roots resolved to an entry of the correct family at
///   decode, and `table.arena` holds the built nodes.
/// - ensures: one marked declaration per meta, its content roots addressing
///   `table.arena`, in admission order.
/// - provides: the decoded sequence, which is also the re-encode input the
///   canonical-form comparison runs over.
/// - fails: never — a family mismatch cannot survive decode's checks, and a
///   fresh unit leaf is the fail-safe fallback rather than a panic.
/// - panics: none.
#[spec(
    requires: metas.iter().all(|meta|
        value_type_id_at(&table.nodes, meta.root_declared)
            .is_some_and(|id| table.arena.value_type(id).is_some())
        && meta.root_body.is_none_or(|root|
            value_id_at(&table.nodes, root)
                .is_some_and(|id| table.arena.value(id).is_some()))),
    ensures: |ret| ret.len() == metas.len()
        && ret.iter().zip(metas).all(|(marked, meta)|
            marked.mark() == meta.mark
            && Some(marked.declaration().declared_id())
                == value_type_id_at(&table.nodes, meta.root_declared)
            && match (*marked.declaration().content(), meta.kind, meta.root_body) {
                (DeclarationContent::Def { body, .. }, DeclKind::Def, Some(root)) =>
                    Some(body) == value_id_at(&table.nodes, root),
                (DeclarationContent::Axiom { .. }, DeclKind::Axiom, _)
                | (DeclarationContent::Axiom { .. }, DeclKind::Def, None)
                | (DeclarationContent::AbstractType { .. }, DeclKind::AbstractType, _) => true,
                _ => false,
            }),
)]
fn build_declarations(
    table: &mut Table,
    metas: &[DeclMeta],
) -> Vec<MarkedDeclaration>
{
    let mut declarations: Vec<MarkedDeclaration> = Vec::new();
    for meta in metas {
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
            // A definition whose body root failed to resolve degrades to an
            // axiom rather than fabricating a body — the same fail-safe the unit
            // fallbacks above take, and unreachable after decode's checks.
            | (DeclKind::Def | DeclKind::Axiom, _) => builder.axiom(meta.levels.clone(), declared),
        };
        declarations.push(MarkedDeclaration::new(meta.mark, declaration));
    }
    declarations
}

/// A forward byte cursor with bounds-checked reads: the decoder's totality
/// substrate, where an over-read surfaces as truncation rather than a panic.
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
    #[inline]
    pub(crate) fn new(image: ArtifactImage<'bytes>) -> Self
    {
        Self {
            image,
            position: ByteOffset::default(),
        }
    }

    /// Read one byte, or refuse as truncated at the end.
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
    #[inline]
    fn next_tag(&mut self) -> Result<WireTag, DecodeError>
    {
        let byte = self.next_byte()?;
        Ok(WireTag::from(byte))
    }

    /// Read `count` bytes as a borrowed image, or refuse as truncated.
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
    /// declared count, so an adversarial count costs one truncation rather
    /// than an allocation.
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
    /// - hypothesis: L2 — the round-trip differential over the encoder pins
    ///   every accepted value; the L3 residues are the group boundary, the
    ///   overlong trailing zero group, and the beyond-64-bit encoding.
    /// - witness: `wire::tests::uvarint_round_trips_through_the_reader`
    /// - witness: `decode::tests::an_overlong_varint_is_refused`
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
    #[inline]
    fn read_global(&mut self) -> Result<GlobalIndex, DecodeError>
    {
        let value = self.read_u32()?;
        Ok(GlobalIndex::from(u32::from(value)))
    }

    /// Read length-prefixed text through a validating UTF-8 conversion.
    #[inline]
    fn read_text(&mut self) -> Result<String, DecodeError>
    {
        let length = self.read_usize()?;
        let bytes = self.take(ByteCount::from(usize::from(length)))?;
        let text =
            core::str::from_utf8(bytes.as_ref()).map_err(|_error| DecodeError::Malformed {
                site: MalformedSite::LiteralPayload,
            })?;
        Ok(String::from(text))
    }
}

/// Decode one declaration segment: its header, its entries, and its roots.
///
/// # Specification
/// - requires: nothing — the bytes may be adversarial; `table` holds every
///   entry the earlier segments introduced, since the table's index space runs
///   across segments.
/// - ensures: the segment's entries are appended to `table` in wire order, and
///   the returned metadata carries the admission mark, the live kind, the level
///   signature, the roots resolved to already-decoded entries of the required
///   family, and the sealing-provenance atoms a definition carried.
/// - provides: the per-segment step of the artifact decode. The clause checks
///   the returned roots' table membership and polarity. Wire-order appends and
///   metadata fidelity stay prose: the parser exposes no independent segment
///   view, and replaying it would mint a second graph.
/// - fails: [`DecodeError::ReservedDeclarationKind`] on a reserved kind;
///   [`DecodeError::ReservedSlotOccupied`] on an occupied reserved slot;
///   [`DecodeError::UnknownTag`] at the admission or declaration-kind site; and
///   whatever the entry and root decoders refuse.
/// - panics: none.
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
    decode_empty_name(reader)?;
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
#[inline]
#[spec(ensures: |ret| match (index < table.next_index(), table.families.get(index.offset().0)) {
    (true, Some(family)) => ret.as_ref() == Ok(family),
    _ => ret.is_err(),
})]
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
/// - requires: nothing — the bytes may be adversarial.
/// - ensures: the entry cap holds, the tag lies in the frozen block, every
///   child index is strictly earlier and of the required polarity, and the node
///   is minted once into the arena with its family and children recorded.
/// - provides: the arena-construction step that makes decode retain sharing.
///   The clause checks the cap, frozen tag, single append and earlier children.
///   Slot-specific polarity is checked by `read_child`; payload fidelity and
///   arena-node identity stay prose because the parser exposes no independent
///   decoded-entry view to compare without minting again.
/// - fails: [`DecodeError::Malformed`] at the table-size, child-order or
///   polarity site; [`DecodeError::UnknownTag`] at the node site; and whatever
///   the inline payload decoders refuse.
/// - panics: none.
#[spec(
    captures: [
        entry_count = table.nodes.len(),
        entry_family_count = table.families.len(),
        entry_children_count = table.children.len(),
        entry_index = table.next_index(),
        entry_tag = reader.image.byte_at(reader.position).map(WireTag::from),
    ],
    ensures: |ret| ret.is_err()
        || (TableEntryCount::from(table.nodes.len()) <= MAX_TABLE_ENTRIES
            && table.nodes.len() == entry_count.saturating_add(1)
            && table.families.len() == entry_family_count.saturating_add(1)
            && table.children.len() == entry_children_count.saturating_add(1)
            && entry_tag.is_some_and(|tag|
                tags::NODE_TAG_TABLE.iter().any(|description| description.tag == tag))
            && table.children.last().is_some_and(|children|
                children.iter().all(|child| *child < entry_index))),
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
            let id = table.arena.value_type_universe(level);
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
#[inline]
#[spec(
    requires: this == table.next_index(),
    captures: entry_children_count = children.len(),
    ensures: |ret| ret.as_ref().ok().is_none_or(|node|
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

/// Decode the structured-name record, requiring it empty.
#[inline]
fn decode_empty_name(reader: &mut ByteReader<'_>) -> Result<(), DecodeError>
{
    expect_empty_slot(reader, ReservedSlot::StructuredName)
}

/// Decode the four per-definition annotation slots, yielding the
/// sealing-provenance atoms.
///
/// Three of the four stay reserved and are refused when occupied; the third is
/// live and carries the atoms this declaration's projection rebound. The atoms
/// are only *read* here — whether they ascend, and whether each occurs in the
/// declared type, are typing facts decided at a choke point, and this is the
/// format plane.
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
/// No capacity is reserved from the declared count, so an adversarial count
/// costs one truncation rather than an allocation.
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
/// - requires: nothing — the declared parameter count and constraint count may
///   be adversarial; no capacity is reserved from either.
/// - ensures: the parameter count and the declared constraints in wire order,
///   every constraint rebuilt through [`LandmarkConstraint`]'s constructors so
///   a non-variable-only side is unrepresentable rather than merely refused.
/// - provides: the level interface of one declaration segment. The
///   wire-to-constraint relation stays prose: the result contains normalized
///   constraints, not their source encodings, and checking it would replay the
///   allocating level parser. Constructor-enforced shape adds no predicate.
/// - fails: [`DecodeError::Truncated`]; [`DecodeError::UnknownTag`] at the
///   constraint-relation site; [`DecodeError::Malformed`] at the
///   constraint-form site when a side is not variable-only, and at the sites
///   the level decoder names.
/// - panics: none.
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
/// - ensures: an always-canonical level, when the constant, the atom count and
///   each variable-and-offset pair decode and no offset meets the decode cap.
/// - provides: the level decoder for universes, lifts and constraint sides.
///   Canonicality is enforced by `Level`'s private representation and smart
///   constructors. Wire acceptance stays prose: checking it would replay this
///   allocating parser; a type-invariant-only clause would add no observation.
/// - fails: [`DecodeError::Truncated`]; [`DecodeError::Malformed`] at the
///   level-offset site on an over-cap offset or an overflow, and at the
///   index-range site on an out-of-range variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the round-trip differential pins every level an artifact
///   carries; the L3 residue is the offset cap, asserted just under and just
///   over with the exact refusal.
/// - witness: `sharing_format::sharing_format::the_level_offset_boundary_accepts_under_and_refuses_over`
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
#[inline]
#[spec(
    requires: LevelAtomOffset::from(u64::from(offset)) < MAX_DECODED_LEVEL_OFFSET,
    ensures: |ret| ret.as_ref().ok().is_none_or(|atom|
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
            let content = reader.read_text()?;
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
#[inline]
fn decode_magnitude(reader: &mut ByteReader<'_>) -> Result<Magnitude, DecodeError>
{
    let digits = reader.read_text()?;
    Magnitude::from_decimal_text(digits).ok_or(DecodeError::Malformed {
        site: MalformedSite::LiteralPayload,
    })
}

/// Decode a canonical fraction through its smart constructor.
#[inline]
fn decode_fraction(reader: &mut ByteReader<'_>) -> Result<FractionDigits, DecodeError>
{
    let digits = reader.read_text()?;
    FractionDigits::from_decimal_text(digits).ok_or(DecodeError::Malformed {
        site: MalformedSite::LiteralPayload,
    })
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::ByteReader;
    use crate::error::DecodeError;
    use crate::error::MalformedSite;
    use crate::wire::ArtifactImage;

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
