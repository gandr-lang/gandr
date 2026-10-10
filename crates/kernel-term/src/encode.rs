//! The deterministic encoder: an admission-ordered declaration sequence over
//! one arena, written as canonical bytes.
//!
//! # The subterm table, and what makes it canonical
//!
//! Each declaration segment carries a **subterm table** rather than an expanded
//! tree. Nodes are interned bottom-up, children before parents, with
//! **content-keyed deduplication**: a node's key is its own encoded entry bytes
//! — the node tag, its children's already-assigned global indices, and its
//! canonical inline payload — so two structurally equal nodes collapse to one
//! global index whether they were shared within a declaration, shared across
//! declarations, or merely coincident. Because children are already indices the
//! key does not recursively embed child entries. Tree-map lookups still have
//! logarithmic cost, and key comparisons and serialization depend on payload
//! byte lengths as well as the number of nodes.
//!
//! Deduplication is content-keyed and **never id-keyed**, and the reason is a
//! canonicality property rather than a performance one: an id-keyed
//! deduplication would make the bytes depend on decode history, and the bytes
//! must be a function of the abstract environment alone.
//!
//! The first completion of a node assigns the next free global index and
//! appends its entry to the *current* declaration's segment; a later occurrence
//! reuses the index without appending. That is **post-order first-completion
//! order**. The fixed child traversal selects one topological order; other
//! child-before-parent orders exist but are not this encoder’s canonical
//! order. Earlier-child indices make the table streaming-decodable.
//!
//! # The walk is sharing-aware, and that is load-bearing twice
//!
//! An arena node is visited once, memoized by id, so re-encoding a decoded DAG
//! avoids walking the expanded tree. That matters for
//! the encoder's own cost, and it matters more for the decoder, which uses this
//! encoder as its canonical-form oracle: **a re-encoder that walked the graph
//! as a tree would itself be an amplification vector**, turning the defence
//! into the vulnerability.
//!
//! # The encoder is untrusted
//!
//! It feeds no typing judgement and is not an admission fast path. The
//! decoder validates framing and budgets, then compares the input with this
//! encoder’s output. That checks agreement with this implementation, not an
//! independent proof of the wire format; shared encoder/decoder mistakes need
//! independent wire fixtures to expose them.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::ConstraintRelation;
use gandr_kernel_strata::Level;

use crate::arena::AnyNode;
use crate::arena::TermArena;
use crate::base::BaseType;
use crate::base::Literal;
use crate::base::Sign;
use crate::budget::GlobalIndex;
use crate::decl::AdmissionMark;
use crate::decl::DeclarationContent;
use crate::decl::LevelSignature;
use crate::decl::MarkedDeclaration;
use crate::decl::MintedAtom;
use crate::decl::StructuredName;
use crate::tags;
use crate::term::Computation;
use crate::term::ConstantIndex;
use crate::term::Side;
use crate::term::Value;
use crate::types::CompType;
use crate::types::GroundSort;
use crate::types::ValueType;
use crate::wire::ArtifactImage;
use crate::wire::ArtifactText;
use crate::wire::EncodedArtifact;
use crate::wire::WireTag;
use crate::wire::WireU64;
use crate::wire::WireUsize;

/// The canonical bytes of one encoded subterm-table entry, which are also its
/// deduplication key.
///
/// # Specification
/// - requires: the encoder supplies the state described by the consuming
///   operations.
/// - ensures: retains candidate entry bytes as a shallow lexicographic content
///   key; this wrapper does not validate entry completeness.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; new and
///   interning or entry-encoding operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EncodedEntry(EncodedArtifact);

/// The content-keyed subterm interner, carrying the global index counter and
/// both memos across declaration segments.
///
/// # Specification
/// - requires: the encoder supplies the state described by the consuming
///   operations.
/// - ensures: retains node memoization and byte-content deduplication across
///   segments with a saturating global counter; it belongs to one unchanged
///   arena.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; new and
///   interning or entry-encoding operations carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 observes exact segment entries, assigned indices and memo
///   state across repeated ids, distinct equal nodes, a new parent, a second
///   segment and reversed children. This separates id-keyed deduplication, memo
///   loss, redundant entries and incorrect post-order assignment. Deep and
///   differently shared integration fixtures supplement these bounded
///   transitions; a shared encode/decode round trip is not an independent
///   format oracle.
/// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
/// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
struct Interner
{
    /// Arena node to its assigned global index: the sharing-aware memo, so an
    /// in-arena shared node is walked once.
    by_node: BTreeMap<AnyNode, GlobalIndex>,
    /// Encoded entry bytes to their global index: the content deduplication, so
    /// structurally equal nodes collapse.
    by_content: BTreeMap<EncodedEntry, GlobalIndex>,
    /// The next free global index.
    next: GlobalIndex,
}

impl Interner
{
    /// A fresh interner over an empty index space.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns an interner holding no node and no content, with the
    ///   next free global index at zero.
    /// - provides: the empty index space one artifact's encoding fills, so no
    ///   index from an earlier encoding can be reused.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes exact segment entries, assigned indices and
    ///   memo state across repeated ids, distinct equal nodes, a new parent, a
    ///   second segment and reversed children. This separates id-keyed
    ///   deduplication, memo loss, redundant entries and incorrect post-order
    ///   assignment. Deep and differently shared integration fixtures
    ///   supplement these bounded transitions; a shared encode/decode round
    ///   trip is not an independent format oracle.
    /// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
    /// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    #[spec(
        ensures: |ret| ret.by_node.is_empty()
                && ret.by_content.is_empty()
                && u32::from(ret.next) == 0,
    )]
    #[inline]
    fn new() -> Self
    {
        Self {
            by_node: BTreeMap::new(),
            by_content: BTreeMap::new(),
            next: GlobalIndex::default(),
        }
    }
}

/// Encode an admission-ordered declaration sequence over `arena` into canonical
/// bytes.
///
/// # Specification
/// - requires: every reachable id resolves in arena; the graph is acyclic,
///   respects the arena’s truncation discipline and fits the global-index
///   space. The supplied declaration order defines admission positions.
/// - ensures: writes the magic, version, derived atom positions and declaration
///   count, then content-deduplicated segments in first-completion order. Equal
///   abstract input graphs produce equal bytes regardless of in-memory sharing.
/// - provides: a deterministic wire candidate, not admission or typing
///   evidence. Live roots are checked directly and each visited node is checked
///   before entry encoding. Missing negative-family nodes have no unit
///   substitute, so stale ids are a domain violation rather than a promised
///   recovery.
/// - fails: never within the live, acyclic input domain; decode budgets and
///   producer-metadata truth are not checked here.
/// - panics: none within that domain. Enabled specification checks reject a
///   missing root or visited node.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement. The enforced
///   stale-root witness checks the live-ID boundary, not recovery of an invalid
///   arena.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `encode::tests::stale_roots_violate_the_encoding_domain`
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
#[inline]
#[must_use]
#[spec(requires: declarations.iter().all(|marked| { let declaration = marked.declaration(); arena.value_type(declaration.declared_id()).is_some() && match *declaration.content() { DeclarationContent::Def { body, .. } => arena.value(body).is_some(), DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => true } }),
ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice())
    && ret
        .as_image()
        .as_ref()
        .get(tags::MAGIC.len() ..)
        .is_some_and(|rest| rest.starts_with(&u16::from(tags::FORMAT_VERSION).to_le_bytes())))]
pub fn encode(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
) -> EncodedArtifact
{
    let mut out = EncodedArtifact::new();
    out.put_image(ArtifactImage::from(tags::MAGIC.as_slice()));
    out.put_version(tags::FORMAT_VERSION);
    encode_minted_atom_table(&mut out, declarations);
    out.put_uvarint(WireU64::from(WireUsize::from(declarations.len())));
    let mut interner = Interner::new();
    for declaration in declarations {
        encode_declaration(&mut out, arena, &mut interner, declaration);
    }
    out
}

/// The admission positions of the abstract-type declarations in a sequence,
/// ascending: the canonical content of the minted-atom table.
///
/// # Specification
/// - requires: `declarations` is in admission order.
/// - ensures: the strictly ascending positions of exactly the abstract-type
///   declarations.
/// - provides: the table the encoder writes and the decoder independently
///   re-derives, which is what makes the table refutable rather than believed.
///   Admission order stays prose: a position is the sequence index itself, so
///   the order is definitional rather than an observation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[must_use]
#[spec(ensures: |ret| ret.iter().copied().eq(declarations.iter().enumerate().filter_map(
    |(position, declaration)| matches!(
        *declaration.declaration().content(),
        DeclarationContent::AbstractType { .. }
    )
    .then_some(MintedAtom::from(position)),
)))]
pub fn minted_atoms(declarations: &[MarkedDeclaration]) -> Vec<MintedAtom>
{
    declarations
        .iter()
        .enumerate()
        .filter_map(|(position, declaration)| {
            matches!(
                *declaration.declaration().content(),
                DeclarationContent::AbstractType { .. }
            )
            .then_some(MintedAtom::from(position))
        })
        .collect()
}

/// Write the minted-atom table: a count followed by ascending admission
/// positions.
///
/// The table is deliberately derivable from the declarations that follow it.
/// That is not redundancy for its own sake: a table the decoder can recompute
/// is a table the decoder can *refute*, and refutability is the whole
/// difference between freshness as a checked property and freshness as
/// something the producer asserts.
///
/// # Specification
/// - requires: `declarations` are in admission order.
/// - ensures: appends the number of minted atoms and then their admission
///   positions in ascending order.
/// - provides: the table a decoder recomputes and compares, which is what makes
///   freshness a checked property rather than a producer's assertion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let (count, fields) = declarations.iter().enumerate().filter(|&(_, declaration)| matches!(*declaration.declaration().content(), DeclarationContent::AbstractType { .. })).fold((0_usize, 0_usize),
        |(count, fields), (position, _)| (count.saturating_add(1), fields.saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from(position).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))));
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && ({ let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) },
)]
fn encode_minted_atom_table(
    out: &mut EncodedArtifact,
    declarations: &[MarkedDeclaration],
)
{
    let atoms = minted_atoms(declarations);
    out.put_uvarint(WireU64::from(WireUsize::from(atoms.len())));
    for atom in atoms {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
    }
}

/// Write one declaration segment: its admission mark, kind, name record, level
/// signature, the entries it introduces, and its root references.
///
/// # Specification
/// - requires: the interner carries assignments from earlier segments of this
///   unchanged acyclic arena; assignments fit its index space. Dangling value
///   and value-type roots are admitted.
/// - ensures: writes the mark, kind, name and level interface, then only newly
///   completed entries, in first-completion order. Definitions write
///   declared/body roots and four annotation slots; the other kinds write one
///   root and no slots.
/// - provides: one segment with cross-declaration sharing. The predicate checks
///   the mark/kind bytes, root memo presence and global-counter transition;
///   literal segment fixtures observe field order and slot framing.
/// - fails: never.
/// - panics: none within the acyclic domain.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[spec(
    captures: entry = (out.as_image().as_ref().len(), interner.by_content.len(), interner.next),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        bytes.get(entry.0).copied() == Some(u8::from(match marked.mark() { AdmissionMark::Checked => tags::ADMISSION_CHECKED, AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED }))
            && bytes.get(entry.0.saturating_add(1)).copied() == Some(u8::from(match *marked.declaration().content() { DeclarationContent::Def { .. } => tags::KIND_DEF, DeclarationContent::Axiom { .. } => tags::KIND_AXIOM, DeclarationContent::AbstractType { .. } => tags::KIND_ABSTRACT_TYPE }))
            && interner.by_node.contains_key(&AnyNode::ValueType(marked.declaration().declared_id()))
            && match *marked.declaration().content() { DeclarationContent::Def { body, .. } => interner.by_node.contains_key(&AnyNode::Value(body)), _ => true }
            && interner.by_content.len() >= entry.1
            && u32::from(interner.next) == u32::from(entry.2).saturating_add(u32::try_from(interner.by_content.len().saturating_sub(entry.1)).unwrap_or(u32::MAX)) },
)]
fn encode_declaration(
    out: &mut EncodedArtifact,
    arena: &TermArena,
    interner: &mut Interner,
    marked: &MarkedDeclaration,
)
{
    out.put_tag(match marked.mark() {
        | AdmissionMark::Checked => tags::ADMISSION_CHECKED,
        | AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED,
    });
    let declaration = marked.declaration();
    let content = declaration.content();
    out.put_tag(match *content {
        | DeclarationContent::Def { .. } => tags::KIND_DEF,
        | DeclarationContent::Axiom { .. } => tags::KIND_AXIOM,
        | DeclarationContent::AbstractType { .. } => tags::KIND_ABSTRACT_TYPE,
    });
    encode_structured_name(out, declaration.name());
    encode_level_signature(out, declaration.levels());

    let mut segment: Vec<EncodedEntry> = Vec::new();
    let roots = match *content {
        | DeclarationContent::Def { declared, body } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            let body = intern(arena, interner, &mut segment, AnyNode::Value(body));
            (declared, Some(body))
        },
        // An abstract type writes exactly like an axiom: one root, its kind,
        // and no body. That is the shape of "an atom with no unfolding rule" on
        // the wire — there is no representation field to omit, so none can leak.
        | DeclarationContent::Axiom { declared }
        | DeclarationContent::AbstractType { kind: declared } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            (declared, None)
        },
    };
    out.put_uvarint(WireU64::from(WireUsize::from(segment.len())));
    for entry in &segment {
        out.put_image(entry.0.as_image());
    }
    let (root_declared, root_body) = roots;
    out.put_uvarint(WireU64::from(u64::from(u32::from(root_declared))));
    if let Some(root_body) = root_body {
        out.put_uvarint(WireU64::from(u64::from(u32::from(root_body))));
        // The four per-definition annotation slots. Erasure, modes and grades,
        // and directedness and variance stay reserved and empty; the third is
        // the sealing-provenance slot, and it carries the atoms this
        // declaration's projection rebound. A choke point re-derives them from
        // the declared type rather than believing them.
        out.put_uvarint(WireU64::from(0_u64));
        out.put_uvarint(WireU64::from(0_u64));
        encode_sealing_provenance(out, declaration.provenance());
        out.put_uvarint(WireU64::from(0_u64));
    }
}

/// Write the structured-name record: a segment count, then each segment as
/// length-prefixed UTF-8.
///
/// An unnamed declaration writes a zero count and nothing else, so its segment
/// is the same bytes whatever names its neighbours carry.
///
/// # Specification
/// - requires: nothing — a segment's constructor already refused the separator.
/// - ensures: appends the segment count and then each segment's byte length and
///   bytes, outermost segment first.
/// - provides: the record a reader rebuilds the name from, segment by segment,
///   so no dotted string is ever the wire form of a name.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
/// - witness: `decl::tests::names_classify_the_separator_without_normalizing_unicode`
/// - witness: `sharing_format::sharing_format::a_structured_name_round_trips_as_segments`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let count = u64::try_from(name.segments().len()).unwrap_or(u64::MAX);
        let fields = name.segments().iter().fold(0_usize,
        |total, segment| total.saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((segment.as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((segment.as_ref()).len())));
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }
            && name.segments().last().is_none_or(|segment| bytes.ends_with(segment.as_ref().as_bytes())) },
)]
fn encode_structured_name(
    out: &mut EncodedArtifact,
    name: &StructuredName,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(name.segments().len())));
    for segment in name.segments() {
        encode_text(out, ArtifactText::from(segment.as_ref()));
    }
}

/// Write the sealing-provenance slot: a count followed by admission positions.
///
/// A declaration no projection touched writes a zero count, which is
/// byte-identical to what the slot carried while it was reserved — so filling
/// the slot moved no other field and invalidated no artifact.
///
/// # Specification
/// - requires: `provenance` holds the admission positions the declaration's
///   projection rebound, in the order the artifact carries them.
/// - ensures: appends the count and then those positions in that order; a
///   declaration no projection touched writes a zero count and nothing else.
/// - provides: the slot's filling, byte-identical to the reserved form on the
///   empty case, so filling it moved no other field.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares a mixed abstract-type, definition and axiom
///   sequence with a literal whole-artifact fixture, including names, admission
///   marks, shared globals, root order and reserved slots. A separate position
///   model and a nonempty provenance fixture distinguish declaration positions
///   from table indices and preserve claimed order. Existing refusal and
///   differently shared fixtures cover table disagreements and canonical
///   deduplication. The finite examples do not prove typing, provenance truth
///   or independent correctness through round-trip self-agreement.
/// - witness: `encode::tests::declaration_sequences_match_literal_segment_fixtures`
/// - witness: `encode::tests::atom_positions_and_provenance_preserve_sequence_identity`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let count = u64::try_from(provenance.len()).unwrap_or(u64::MAX);
        let fields = provenance.iter().fold(0_usize,
        |total, &atom| total.saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from(usize::from(atom)).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)));
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_sealing_provenance(
    out: &mut EncodedArtifact,
    provenance: &[ConstantIndex],
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(provenance.len())));
    for &atom in provenance {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
    }
}

/// Intern a root's sub-DAG, appending each first-completed entry to `segment`,
/// and return the root's global index.
///
/// # Specification
/// - requires: all reachable ids resolve in this acyclic arena; the memo
///   belongs to earlier roots of this unchanged arena and global assignments
///   fit the index space.
/// - ensures: assigns reachable nodes globals, appends newly completed content
///   in post-order first-completion order and returns the root’s memoized
///   index; an already memoized root changes neither segment nor memo.
/// - provides: content-keyed sharing across segments, with captured counts
///   checking reuse and one appended entry per new content key without cloning
///   either map.
/// - fails: never within the live, acyclic domain.
/// - panics: none within that domain.
/// - intension: uses a resumable heap stack rather than host recursion.
///   Tree-map lookups and byte-key comparisons add logarithmic and
///   payload-dependent costs; shared subgraphs are not expanded.
///
/// # Adequacy
/// - hypothesis: L3 observes exact segment entries, assigned indices and memo
///   state across repeated ids, distinct equal nodes, a new parent, a second
///   segment and reversed children. This separates id-keyed deduplication, memo
///   loss, redundant entries and incorrect post-order assignment. Deep and
///   differently shared integration fixtures supplement these bounded
///   transitions; a shared encode/decode round trip is not an independent
///   format oracle.
/// - witness: `encode::tests::interning_reuses_content_across_segments_without_losing_order`
/// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `adversarial_depth::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[spec(requires: match root { AnyNode::ValueType(id) => arena.value_type(id).is_some(), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },

    captures: entry = (interner.by_node.get(&root).copied(), interner.by_node.len(), interner.by_content.len(), segment.len(), interner.next),
    ensures: |ret| interner.by_node.get(&root) == Some(&ret)
            && interner.by_node.len() >= entry.1
            && interner.by_content.len() >= entry.2
            && segment.len() == entry.3.saturating_add(interner.by_content.len().saturating_sub(entry.2))
            && u32::from(interner.next) == u32::from(entry.4).saturating_add(u32::try_from(interner.by_content.len().saturating_sub(entry.2)).unwrap_or(u32::MAX))
            && entry.0.is_none_or(|prior| ret == prior
            && interner.by_node.len() == entry.1
            && interner.by_content.len() == entry.2
            && segment.len() == entry.3),
)]
fn intern(
    arena: &TermArena,
    interner: &mut Interner,
    segment: &mut Vec<EncodedEntry>,
    root: AnyNode,
) -> GlobalIndex
{
    let mut stack: Vec<(AnyNode, usize)> = Vec::new();
    stack.push((root, 0_usize));
    while let Some((node, cursor)) = stack.pop() {
        if interner.by_node.contains_key(&node) {
            continue;
        }
        let children = arena.children_of(node);
        let mut next = cursor;
        let mut descended = false;
        while let Some(&child) = children.get(next) {
            if interner.by_node.contains_key(&child) {
                next = next.saturating_add(1);
            }
            else {
                stack.push((node, next.saturating_add(1)));
                stack.push((child, 0_usize));
                descended = true;
                break;
            }
        }
        if descended {
            continue;
        }
        let child_globals: Vec<GlobalIndex> = children
            .iter()
            .map(|child| {
                interner
                    .by_node
                    .get(child)
                    .copied()
                    .unwrap_or_else(GlobalIndex::default)
            })
            .collect();
        let encoded = encode_entry(arena, node, &child_globals);
        let deduplicated = interner.by_content.get(&encoded).copied();
        let global = if let Some(global) = deduplicated {
            global
        }
        else {
            let assigned = interner.next;
            interner.next = interner.next.next();
            let _prior = interner.by_content.insert(encoded.clone(), assigned);
            segment.push(encoded);
            assigned
        };
        let _prior = interner.by_node.insert(node, global);
    }
    interner
        .by_node
        .get(&root)
        .copied()
        .unwrap_or_else(GlobalIndex::default)
}

/// Write one subterm-table entry: its node tag, its inline payload, then its
/// children's global indices.
///
/// Negative families have no nullary unit. An absent id is outside the encoding
/// domain, not a request to invent a substitute node or emit a partial entry.
///
/// # Specification
/// - requires: node resolves in arena, and the supplied globals name its
///   children in wire-field order.
/// - ensures: writes that live node’s exact frozen tag, canonical inline
///   payload and supplied child indices.
/// - provides: a byte-content deduplication key. The predicate checks liveness
///   and the tag; literal fixtures check payloads and distinguishable ordered
///   child fields.
/// - fails: never within the live-node domain.
/// - panics: none within that domain; enabled checks reject a missing id.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation; a separate enforced boundary witness rejects stale ids in every
///   family.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::stale_roots_violate_the_encoding_domain`
#[spec(requires: match node { AnyNode::ValueType(id) => arena.value_type(id).is_some(), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },
ensures: |ret| ret.0.as_image().as_ref().first().copied()
    == Some(u8::from(match node {
        AnyNode::ValueType(id) => match arena.value_type(id) {
            Some(&ValueType::PathUniverse(..)) => tags::NODE_VT_PATH_UNIVERSE,
            None | Some(&ValueType::Unit) => tags::NODE_VT_UNIT,
            Some(&ValueType::Empty) => tags::NODE_VT_EMPTY,
            Some(&ValueType::Base(_)) => tags::NODE_VT_BASE,
            Some(&ValueType::Universe { sort: GroundSort::Value, .. }) => tags::NODE_VT_UNIVERSE,
            Some(&ValueType::Universe { sort: GroundSort::Computation, .. }) => {
                tags::NODE_VT_COMPUTATION_UNIVERSE
            },
            Some(&ValueType::Abstract(_)) => tags::NODE_VT_ABSTRACT,
            Some(&ValueType::Product(..)) => tags::NODE_VT_PRODUCT,
            Some(&ValueType::Sum(..)) => tags::NODE_VT_SUM,
            Some(&ValueType::List(_)) => tags::NODE_VT_LIST,
            Some(&ValueType::Thunk(_)) => tags::NODE_VT_THUNK,
            Some(&ValueType::Lift { .. }) => tags::NODE_VT_LIFT,
            Some(&ValueType::Element { .. }) => tags::NODE_VT_ELEMENT,
            Some(&ValueType::StaticPi { .. }) => tags::NODE_VT_STATIC_PI,
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            None | Some(&CompType::Returner(_)) => tags::NODE_CT_RETURNER,
            Some(&CompType::Arrow { .. }) => tags::NODE_CT_ARROW,
            Some(&CompType::Pi { .. }) => tags::NODE_CT_PI,
            Some(&CompType::Element { .. }) => tags::NODE_CT_ELEMENT,
        },
        AnyNode::Value(id) => match arena.value(id) {
            Some(&Value::PathRefl(_)) => tags::NODE_V_PATH_REFL,
            Some(&Value::PathProduct(..)) => tags::NODE_V_PATH_PRODUCT,
            Some(&Value::PathEquiv { .. }) => tags::NODE_V_PATH_EQUIV,
            None | Some(&Value::Unit) => tags::NODE_V_UNIT,
            Some(&Value::Variable(_)) => tags::NODE_V_VARIABLE,
            Some(&Value::Constant(_)) => tags::NODE_V_CONSTANT,
            Some(&Value::Literal(_)) => tags::NODE_V_LITERAL,
            Some(&Value::Pair(..)) => tags::NODE_V_PAIR,
            Some(&Value::Injection(..)) => tags::NODE_V_INJECTION,
            Some(&Value::Thunk(_)) => tags::NODE_V_THUNK,
            Some(&Value::Lift { .. }) => tags::NODE_V_LIFT,
            Some(&Value::Quote(_)) => tags::NODE_V_QUOTE,
            Some(&Value::QuoteComputation(_)) => tags::NODE_V_QUOTE_COMPUTATION,
            Some(&Value::StaticApplication(..)) => tags::NODE_V_STATIC_APPLICATION,
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::Transport(..)) => tags::NODE_C_TRANSPORT,
            None | Some(&Computation::Return(_)) => tags::NODE_C_RETURN,
            Some(&Computation::Lambda(_)) => tags::NODE_C_LAMBDA,
            Some(&Computation::Application(..)) => tags::NODE_C_APPLICATION,
            Some(&Computation::Bind(..)) => tags::NODE_C_BIND,
            Some(&Computation::Force(_)) => tags::NODE_C_FORCE,
            Some(&Computation::Case { .. }) => tags::NODE_C_CASE,
            Some(&Computation::Absurd(_)) => tags::NODE_C_ABSURD,
        },
    })))]
fn encode_entry(
    arena: &TermArena,
    node: AnyNode,
    child_globals: &[GlobalIndex],
) -> EncodedEntry
{
    let mut out = EncodedArtifact::new();
    match node {
        | AnyNode::ValueType(id) => match arena.value_type(id) {
            | None => out.put_tag(tags::NODE_VT_UNIT),
            | Some(value_type) => match *value_type {
                | ValueType::Base(base) => {
                    out.put_tag(tags::NODE_VT_BASE);
                    out.put_tag(base_type_tag(base));
                },
                | ValueType::PathUniverse(..) => out.put_tag(tags::NODE_VT_PATH_UNIVERSE),
                | ValueType::Unit => out.put_tag(tags::NODE_VT_UNIT),
                | ValueType::Empty => out.put_tag(tags::NODE_VT_EMPTY),
                | ValueType::Universe {
                    sort: GroundSort::Value,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_UNIVERSE);
                    encode_level(&mut out, level);
                },
                | ValueType::Universe {
                    sort: GroundSort::Computation,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_COMPUTATION_UNIVERSE);
                    encode_level(&mut out, level);
                },
                | ValueType::Abstract(atom) => {
                    out.put_tag(tags::NODE_VT_ABSTRACT);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
                },
                | ValueType::Product(..) => out.put_tag(tags::NODE_VT_PRODUCT),
                | ValueType::Sum(..) => out.put_tag(tags::NODE_VT_SUM),
                | ValueType::List(_) => out.put_tag(tags::NODE_VT_LIST),
                | ValueType::Thunk(_) => out.put_tag(tags::NODE_VT_THUNK),
                | ValueType::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_LIFT);
                    encode_level(&mut out, target);
                },
                | ValueType::Element { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_ELEMENT);
                    encode_level(&mut out, target);
                },
                | ValueType::StaticPi { .. } => out.put_tag(tags::NODE_VT_STATIC_PI),
            },
        },
        | AnyNode::CompType(id) => match arena.comp_type(id) {
            | Some(&CompType::Returner(_)) | None => out.put_tag(tags::NODE_CT_RETURNER),
            | Some(&CompType::Arrow { .. }) => out.put_tag(tags::NODE_CT_ARROW),
            | Some(&CompType::Pi { .. }) => out.put_tag(tags::NODE_CT_PI),
            | Some(&CompType::Element { ref target, .. }) => {
                out.put_tag(tags::NODE_CT_ELEMENT);
                encode_level(&mut out, target);
            },
        },
        | AnyNode::Value(id) => match arena.value(id) {
            | None => out.put_tag(tags::NODE_V_UNIT),
            | Some(value) => match *value {
                | Value::Variable(index) => {
                    out.put_tag(tags::NODE_V_VARIABLE);
                    out.put_uvarint(WireU64::from(u64::from(u32::from(index))));
                },
                | Value::Constant(index) => {
                    out.put_tag(tags::NODE_V_CONSTANT);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(index))));
                },
                | Value::PathRefl(_) => out.put_tag(tags::NODE_V_PATH_REFL),
                | Value::PathProduct(..) => out.put_tag(tags::NODE_V_PATH_PRODUCT),
                | Value::PathEquiv { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_PATH_EQUIV);
                    for word in evidence.words() {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                | Value::Unit => out.put_tag(tags::NODE_V_UNIT),
                | Value::Literal(ref literal) => {
                    out.put_tag(tags::NODE_V_LITERAL);
                    encode_literal(&mut out, literal);
                },
                | Value::Pair(..) => out.put_tag(tags::NODE_V_PAIR),
                | Value::Injection(side, _) => {
                    out.put_tag(tags::NODE_V_INJECTION);
                    out.put_tag(side_tag(side));
                },
                | Value::Thunk(_) => out.put_tag(tags::NODE_V_THUNK),
                | Value::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_V_LIFT);
                    encode_level(&mut out, target);
                },
                | Value::Quote(_) => out.put_tag(tags::NODE_V_QUOTE),
                | Value::QuoteComputation(_) => out.put_tag(tags::NODE_V_QUOTE_COMPUTATION),
                | Value::StaticApplication(..) => out.put_tag(tags::NODE_V_STATIC_APPLICATION),
            },
        },
        | AnyNode::Computation(id) => match arena.computation(id) {
            | Some(&Computation::Transport(..)) => out.put_tag(tags::NODE_C_TRANSPORT),
            | Some(&Computation::Lambda(_)) => out.put_tag(tags::NODE_C_LAMBDA),
            | Some(&Computation::Application(..)) => out.put_tag(tags::NODE_C_APPLICATION),
            | Some(&Computation::Return(_)) | None => out.put_tag(tags::NODE_C_RETURN),
            | Some(&Computation::Bind(..)) => out.put_tag(tags::NODE_C_BIND),
            | Some(&Computation::Force(_)) => out.put_tag(tags::NODE_C_FORCE),
            | Some(&Computation::Case { .. }) => out.put_tag(tags::NODE_C_CASE),
            | Some(&Computation::Absurd(_)) => out.put_tag(tags::NODE_C_ABSURD),
        },
    }
    for &child in child_globals {
        out.put_uvarint(WireU64::from(u64::from(u32::from(child))));
    }
    EncodedEntry(out)
}

/// Write a declaration's prenex level signature.
///
/// # Specification
/// - requires: `signature`'s constraints are in declaration order.
/// - ensures: appends the parameter count, the constraint count, and then each
///   constraint as its relation tag followed by its two levels.
/// - provides: the prenex interface's byte image, in the one order a decoder
///   reads it back in.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let params = u64::from(u32::from(signature.params()));
        ({ let scalar = params;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) })
            && ({ let scalar = u64::try_from(signature.constraints().len()).unwrap_or(u64::MAX);
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (start.saturating_add(usize::try_from(64_u32.saturating_sub((params).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }) },
)]
fn encode_level_signature(
    out: &mut EncodedArtifact,
    signature: &LevelSignature,
)
{
    out.put_uvarint(WireU64::from(u64::from(u32::from(signature.params()))));
    let constraints = signature.constraints();
    out.put_uvarint(WireU64::from(WireUsize::from(constraints.len())));
    for constraint in constraints {
        out.put_tag(match constraint.relation() {
            | ConstraintRelation::Leq => tags::RELATION_LEQ,
            | ConstraintRelation::Eq => tags::RELATION_EQ,
        });
        encode_level(out, constraint.left());
        encode_level(out, constraint.right());
    }
}

/// Write a canonical level: its constant part, then its variable atoms in
/// ascending variable order, which is the order the level's own canonical form
/// keeps them in.
///
/// # Specification
/// - requires: `level` is canonical, which is what puts its atoms in ascending
///   variable order.
/// - ensures: appends the constant part, the atom count, and then each atom as
///   its variable index followed by its successor offset.
/// - provides: the level's byte image. The atom order is the level's own
///   canonical order rather than one chosen here, so two canonical levels agree
///   on bytes exactly when they are equal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let constant = u64::from(level.constant_part());
        let (count, fields) = level.atoms().fold((0_usize, 0_usize),
        |(count, fields), (variable, offset)| (count.saturating_add(1), fields.saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(u32::from(variable.index()))).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(usize::try_from(64_u32.saturating_sub((u64::from(offset)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))));
        let count = u64::try_from(count).unwrap_or(u64::MAX);
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(usize::try_from(64_u32.saturating_sub((count).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(fields)
            && { let scalar = constant;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) }
            && { let scalar = count;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))) .. (start.saturating_add(usize::try_from(64_u32.saturating_sub((constant).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX))).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_level(
    out: &mut EncodedArtifact,
    level: &Level,
)
{
    out.put_uvarint(WireU64::from(u64::from(level.constant_part())));
    let atoms: Vec<_> = level.atoms().collect();
    out.put_uvarint(WireU64::from(WireUsize::from(atoms.len())));
    for (variable, offset) in atoms {
        out.put_uvarint(WireU64::from(u64::from(u32::from(variable.index()))));
        out.put_uvarint(WireU64::from(u64::from(offset)));
    }
}

/// Write a literal: its kind, then its canonical payload.
///
/// # Specification
/// - requires: `literal` is canonical, which its constructors are the only way
///   to obtain.
/// - ensures: appends the kind tag, then the payload each kind owes — a sign
///   tag and digits for an integer, text for a string, and a sign tag with
///   integral and fractional digits for a numeric.
/// - provides: the literal's byte image; since the payload is canonical, two
///   literals agree on bytes exactly when they denote the same value.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        match *literal { Literal::Integer(ref integer) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_INTEGER))
            && bytes.get(start.saturating_add(1)).copied() == Some(u8::from(sign_tag(integer.sign())))
            && bytes.len() == start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((integer.magnitude().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((integer.magnitude().as_ref()).len()))
            && bytes.ends_with(integer.magnitude().as_ref().as_bytes()), Literal::Text(ref text) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_TEXT))
            && bytes.len() == start.saturating_add(1).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((text.as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((text.as_ref()).len()))
            && bytes.ends_with(text.as_ref().as_bytes()), Literal::Numeric(ref numeric) => bytes.get(start).copied() == Some(u8::from(tags::LITERAL_NUMERIC))
            && bytes.get(start.saturating_add(1)).copied() == Some(u8::from(sign_tag(numeric.sign())))
            && bytes.len() == start.saturating_add(2).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((numeric.integer_part().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((numeric.integer_part().as_ref()).len())).saturating_add(usize::try_from(64_u32.saturating_sub((u64::try_from((numeric.fraction().as_ref()).len()).unwrap_or(u64::MAX)).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX).saturating_add((numeric.fraction().as_ref()).len()))
            && bytes.ends_with(numeric.fraction().as_ref().as_bytes()) } },
)]
fn encode_literal(
    out: &mut EncodedArtifact,
    literal: &Literal,
)
{
    match *literal {
        | Literal::Integer(ref integer) => {
            out.put_tag(tags::LITERAL_INTEGER);
            out.put_tag(sign_tag(integer.sign()));
            let digits = integer.magnitude().to_digits();
            encode_text(out, ArtifactText::from(digits.as_str()));
        },
        | Literal::Text(ref text) => {
            out.put_tag(tags::LITERAL_TEXT);
            let content = text.to_content();
            encode_text(out, ArtifactText::from(content.as_str()));
        },
        | Literal::Numeric(ref numeric) => {
            out.put_tag(tags::LITERAL_NUMERIC);
            out.put_tag(sign_tag(numeric.sign()));
            let integer = numeric.integer_part().to_digits();
            encode_text(out, ArtifactText::from(integer.as_str()));
            let fraction = numeric.fraction().to_digits();
            encode_text(out, ArtifactText::from(fraction.as_str()));
        },
    }
}

/// Write length-prefixed UTF-8 text.
///
/// # Specification
/// - requires: nothing.
/// - ensures: appends the byte length of the UTF-8 encoding and then those
///   bytes verbatim.
/// - provides: the framing every text field shares, so a payload carrying no
///   normalization of its own is still unambiguously delimited.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 compares complete appended bytes, including a nonempty
///   prefix, with literal wire fixtures. Text covers NUL, multibyte UTF-8 and
///   the 127/128 and 16383/16384 length boundaries; literals cover every kind
///   and sign plus canonical zero. Levels cover empty, constant, ordered
///   multi-atom and u64-ceiling forms, and signatures distinguish both
///   relations and parameter widths. These separate byte-versus-character
///   lengths, field permutation, prefix damage and lost high bits. Arbitrary
///   payload sizes and allocation failure are outside the fixture domain.
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    captures: start = out.as_image().as_ref().len(),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        let length = u64::try_from(text.0.len()).unwrap_or(u64::MAX);
        bytes.len() == start.saturating_add(usize::try_from(64_u32.saturating_sub((length).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX)).saturating_add(text.0.len())
            && bytes.ends_with(text.0.as_bytes())
            && { let scalar = length;
        let width = usize::try_from(64_u32.saturating_sub((scalar).leading_zeros()).max(1).div_ceil(7)).unwrap_or(usize::MAX);
        bytes.get((start) .. (start).saturating_add(width)).is_some_and(|digits| digits.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
        u64::from(byte & 0x7f) == (scalar.checked_shr(shift).unwrap_or(0) & 0x7f)
            && (byte & 0x80 != 0) == (index.saturating_add(1) < width) })) } },
)]
fn encode_text(
    out: &mut EncodedArtifact,
    text: ArtifactText<'_>,
)
{
    let bytes = text.0.as_bytes();
    out.put_uvarint(WireU64::from(WireUsize::from(bytes.len())));
    out.put_image(ArtifactImage::from(bytes));
}

/// The wire tag of a base-type atom.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each of the three base-type atoms to its frozen tag.
/// - provides: the total atom-to-tag map, so a base type's byte is decided in
///   one place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain. L3 compares
///   complete appended bytes, including a nonempty prefix, with literal wire
///   fixtures. Text covers NUL, multibyte UTF-8 and the 127/128 and 16383/16384
///   length boundaries; literals cover every kind and sign plus canonical zero.
///   Levels cover empty, constant, ordered multi-atom and u64-ceiling forms,
///   and signatures distinguish both relations and parameter widths. These
///   separate byte-versus-character lengths, field permutation, prefix damage
///   and lost high bits. Arbitrary payload sizes and allocation failure are
///   outside the fixture domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match base { BaseType::Integer => tags::BASE_INTEGER, BaseType::String => tags::BASE_STRING, BaseType::Numeric => tags::BASE_NUMERIC },
)]
#[inline]
fn base_type_tag(base: BaseType) -> WireTag
{
    match base {
        | BaseType::Integer => tags::BASE_INTEGER,
        | BaseType::String => tags::BASE_STRING,
        | BaseType::Numeric => tags::BASE_NUMERIC,
    }
}

/// The wire tag of a literal sign.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each sign to its frozen tag.
/// - provides: the total sign-to-tag map, so a sign's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain. L3 compares
///   complete appended bytes, including a nonempty prefix, with literal wire
///   fixtures. Text covers NUL, multibyte UTF-8 and the 127/128 and 16383/16384
///   length boundaries; literals cover every kind and sign plus canonical zero.
///   Levels cover empty, constant, ordered multi-atom and u64-ceiling forms,
///   and signatures distinguish both relations and parameter widths. These
///   separate byte-versus-character lengths, field permutation, prefix damage
///   and lost high bits. Arbitrary payload sizes and allocation failure are
///   outside the fixture domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match sign { Sign::NonNegative => tags::SIGN_NON_NEGATIVE, Sign::Negative => tags::SIGN_NEGATIVE },
)]
#[inline]
fn sign_tag(sign: Sign) -> WireTag
{
    match sign {
        | Sign::NonNegative => tags::SIGN_NON_NEGATIVE,
        | Sign::Negative => tags::SIGN_NEGATIVE,
    }
}

/// The wire tag of an injection side.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each injection side to its frozen tag.
/// - provides: the total side-to-tag map, so a side's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes literal entry bytes for every frozen former, every
///   base atom, both injection sides, nonzero inline levels and distinguishable
///   one-, two- and three-child index sequences crossing varint boundaries.
///   This separates tag reassignment, child permutation, missing payloads and
///   lost high bits. It covers live nodes and supplied global assignments, not
///   formation or inputs outside the live, acyclic graph domain. L3 compares
///   complete appended bytes, including a nonempty prefix, with literal wire
///   fixtures. Text covers NUL, multibyte UTF-8 and the 127/128 and 16383/16384
///   length boundaries; literals cover every kind and sign plus canonical zero.
///   Levels cover empty, constant, ordered multi-atom and u64-ceiling forms,
///   and signatures distinguish both relations and parameter widths. These
///   separate byte-versus-character lengths, field permutation, prefix damage
///   and lost high bits. Arbitrary payload sizes and allocation failure are
///   outside the fixture domain.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
/// - witness: `encode::tests::text_and_literals_match_literal_wire_fixtures`
/// - witness: `encode::tests::levels_and_interfaces_match_literal_wire_fixtures`
#[spec(
    ensures: |ret| ret == match side { Side::Left => tags::SIDE_LEFT, Side::Right => tags::SIDE_RIGHT },
)]
#[inline]
fn side_tag(side: Side) -> WireTag
{
    match side {
        | Side::Left => tags::SIDE_LEFT,
        | Side::Right => tags::SIDE_RIGHT,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use super::AnyNode;
    use super::ArtifactImage;
    use super::ArtifactText;
    use super::EncodedArtifact;
    use super::GlobalIndex;
    use super::Level;
    use super::TermArena;
    use crate::base::BaseType;
    use crate::base::FractionDigits;
    use crate::base::IntegerLiteral;
    use crate::base::Literal;
    use crate::base::Magnitude;
    use crate::base::NumericLiteral;
    use crate::base::Sign;
    use crate::base::StringLiteral;
    use crate::decl::AdmissionMark;
    use crate::decl::DeclarationBuilder;
    use crate::decl::LevelParamCount;
    use crate::decl::LevelSignature;
    use crate::decl::MarkedDeclaration;
    use crate::decl::NameSegment;
    use crate::decl::StructuredName;
    use crate::term::ConstantIndex;
    use crate::term::DeBruijnIndex;
    use crate::term::Side;
    use crate::types::GroundSort;

    #[cfg(anodized_panic)]
    #[test]
    fn stale_roots_violate_the_encoding_domain()
    {
        extern crate std;

        let mut arena = TermArena::new();
        let empty = arena.watermark();
        let declared = arena.value_type_unit();
        let value = arena.value_unit();
        let negative_type = arena.comp_type_returner(declared);
        let computation = arena.computation_return(value);
        let declaration =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), declared, value);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, declaration)];
        arena.truncate_to(empty);
        for node in [
            AnyNode::ValueType(declared),
            AnyNode::Value(value),
            AnyNode::CompType(negative_type),
            AnyNode::Computation(computation),
        ] {
            assert!(std::panic::catch_unwind(|| super::encode_entry(&arena, node, &[])).is_err());
        }
        assert!(std::panic::catch_unwind(|| super::encode(&arena, &declarations)).is_err());
    }

    #[test]
    fn text_and_literals_match_literal_wire_fixtures()
    {
        let cases: &[(String, &[u8])] = &[
            (String::new(), &[0]),
            (String::from("A\0é"), &[4]),
            ("x".repeat(127), &[0x7f]),
            ("x".repeat(128), &[0x80, 1]),
            ("x".repeat(0x3fff), &[0xff, 0x7f]),
            ("x".repeat(0x4000), &[0x80, 0x80, 1]),
        ];
        for &(ref text, length) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_text(&mut out, ArtifactText::from(text.as_str()));
            let mut expected = alloc::vec![0xde_u8, 0xad];
            expected.extend_from_slice(length);
            expected.extend_from_slice(text.as_bytes());
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
        let cases: &[(Literal, &[u8])] = &[
            (
                Literal::Integer(IntegerLiteral::new(Sign::Negative, Magnitude::zero())),
                &[0, 0, 1, b'0'],
            ),
            (
                Literal::Integer(IntegerLiteral::new(
                    Sign::NonNegative,
                    Magnitude::from_decimal_text(String::from("00123")).expect("digits"),
                )),
                &[0, 0, 3, b'1', b'2', b'3'],
            ),
            (
                Literal::Integer(IntegerLiteral::new(
                    Sign::Negative,
                    Magnitude::from_decimal_text(String::from("00123")).expect("digits"),
                )),
                &[0, 1, 3, b'1', b'2', b'3'],
            ),
            (Literal::Text(StringLiteral::new(String::from("A\0é"))), &[
                1, 4, b'A', 0, 0xc3, 0xa9,
            ]),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::Negative,
                    Magnitude::from_decimal_text(String::from("0012")).expect("digits"),
                    FractionDigits::from_decimal_text(String::from("0300")).expect("fraction"),
                )),
                &[2, 1, 2, b'1', b'2', 2, b'0', b'3'],
            ),
            (
                Literal::Numeric(NumericLiteral::new(
                    Sign::Negative,
                    Magnitude::zero(),
                    FractionDigits::none(),
                )),
                &[2, 0, 1, b'0', 0],
            ),
        ];
        for &(ref literal, bytes) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_literal(&mut out, literal);
            let mut expected = alloc::vec![0xde_u8, 0xad];
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
    }

    #[test]
    fn levels_and_interfaces_match_literal_wire_fixtures()
    {
        let x = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0_u32),
        ));
        let y = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(1_u32),
        ));
        let second = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(2_u32),
        ))
        .succ()
        .expect("small offset");
        let later = Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(129_u32),
        ));
        let mixed = Level::constant(gandr_kernel_strata::LevelConstant::from(7_u64))
            .max(&later)
            .max(&second);
        let levels: &[(Level, &[u8])] = &[
            (Level::zero(), &[0, 0]),
            (
                Level::constant(gandr_kernel_strata::LevelConstant::from(128_u64)),
                &[0x80, 1, 0],
            ),
            (
                Level::constant(gandr_kernel_strata::LevelConstant::from(u64::MAX)),
                &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 1, 0],
            ),
            (x.clone(), &[0, 1, 0, 0]),
            (mixed, &[7, 2, 2, 1, 0x81, 1, 0]),
        ];
        for &(ref level, bytes) in levels {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level(&mut out, level);
            let mut expected = alloc::vec![0xde_u8, 0xad];
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
        let signature = LevelSignature::new(LevelParamCount::from(2_u32), alloc::vec![
            gandr_kernel_strata::LandmarkConstraint::leq(x.clone(), y.clone())
                .expect("variable-only sides"),
            gandr_kernel_strata::LandmarkConstraint::equal(y, x).expect("variable-only sides"),
        ]);
        let signatures: &[(LevelSignature, &[u8])] = &[
            (LevelSignature::monomorphic(), &[0, 0]),
            (
                LevelSignature::new(LevelParamCount::from(u32::MAX), Vec::new()),
                &[0xff, 0xff, 0xff, 0xff, 0x0f, 0],
            ),
            (signature, &[
                2, 2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0,
            ]),
        ];
        for &(ref signature, bytes) in signatures {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level_signature(&mut out, signature);
            let mut expected = alloc::vec![0xde_u8, 0xad];
            expected.extend_from_slice(bytes);
            assert_eq!(out.as_image().as_ref(), expected.as_slice());
        }
    }

    #[test]
    fn entry_goldens_pin_every_former_and_child_position()
    {
        let mut arena = TermArena::new();
        let t0 = arena.value_type_unit();
        let t1 = arena.value_type_base(BaseType::Integer);
        let v0 = arena.value_variable(DeBruijnIndex::from(0_u32));
        let v1 = arena.value_variable(DeBruijnIndex::from(1_u32));
        let c0 = arena.computation_return(v0);
        let c1 = arena.computation_return(v1);
        let k0 = arena.comp_type_returner(t0);
        let k1 = arena.comp_type_returner(t1);
        let level = Level::constant(gandr_kernel_strata::LevelConstant::from(7_u64));
        let first = GlobalIndex::from(3_u32);
        let second = GlobalIndex::from(129_u32);
        let third = GlobalIndex::from(0x4000_u32);
        let cases: &[(AnyNode, &[GlobalIndex], &[u8])] = &[
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::Integer)),
                &[],
                &[0x00, 0],
            ),
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::String)),
                &[],
                &[0x00, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_base(BaseType::Numeric)),
                &[],
                &[0x00, 2],
            ),
            (AnyNode::ValueType(arena.value_type_unit()), &[], &[0x01]),
            (
                AnyNode::ValueType(arena.value_type_universe(GroundSort::Value, level.clone())),
                &[],
                &[0x02, 7, 0],
            ),
            (
                AnyNode::ValueType(arena.value_type_product(t0, t1)),
                &[first, second],
                &[0x03, 3, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_sum(t0, t1)),
                &[first, second],
                &[0x04, 3, 0x81, 1],
            ),
            (AnyNode::ValueType(arena.value_type_thunk(k0)), &[first], &[
                0x05, 3,
            ]),
            (
                AnyNode::ValueType(arena.value_type_lift(t0, level.clone())),
                &[first],
                &[0x06, 7, 0, 3],
            ),
            (
                AnyNode::CompType(arena.comp_type_returner(t0)),
                &[first],
                &[0x07, 3],
            ),
            (
                AnyNode::CompType(arena.comp_type_arrow(t0, k1)),
                &[first, second],
                &[0x08, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_variable(DeBruijnIndex::from(0x4000_u32))),
                &[],
                &[0x09, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Value(arena.value_constant(ConstantIndex::from(129_usize))),
                &[],
                &[0x0a, 0x81, 1],
            ),
            (AnyNode::Value(arena.value_unit()), &[], &[0x0b]),
            (
                AnyNode::Value(
                    arena.value_literal(Literal::Text(StringLiteral::new(String::from("é")))),
                ),
                &[],
                &[0x0c, 1, 2, 0xc3, 0xa9],
            ),
            (
                AnyNode::Value(arena.value_pair(v0, v1)),
                &[first, second],
                &[0x0d, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_injection(Side::Left, v0)),
                &[first],
                &[0x0e, 0, 3],
            ),
            (
                AnyNode::Value(arena.value_injection(Side::Right, v0)),
                &[first],
                &[0x0e, 1, 3],
            ),
            (AnyNode::Value(arena.value_thunk(c0)), &[first], &[0x0f, 3]),
            (
                AnyNode::Value(arena.value_lift(level.clone(), v0)),
                &[first],
                &[0x10, 7, 0, 3],
            ),
            (
                AnyNode::Computation(arena.computation_lambda(c0)),
                &[first],
                &[0x11, 3],
            ),
            (
                AnyNode::Computation(arena.computation_application(c0, v0)),
                &[first, second],
                &[0x12, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_return(v0)),
                &[first],
                &[0x13, 3],
            ),
            (
                AnyNode::Computation(arena.computation_bind(c0, c1)),
                &[first, second],
                &[0x14, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_force(v0)),
                &[first],
                &[0x15, 3],
            ),
            (
                AnyNode::Computation(arena.computation_case(v0, c0, c1)),
                &[first, second, third],
                &[0x16, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_abstract(ConstantIndex::from(129_usize))),
                &[],
                &[0x17, 0x81, 1],
            ),
            (
                AnyNode::CompType(arena.comp_type_pi(t0, k1)),
                &[first, second],
                &[0x18, 3, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_element(v0, level.clone())),
                &[first],
                &[0x19, 7, 0, 3],
            ),
            (
                AnyNode::ValueType(
                    arena.value_type_universe(GroundSort::Computation, level.clone()),
                ),
                &[],
                &[0x1a, 7, 0],
            ),
            (
                AnyNode::CompType(arena.comp_type_element(v0, level)),
                &[first],
                &[0x1b, 7, 0, 3],
            ),
            (AnyNode::Value(arena.value_quote(t0)), &[first], &[0x1c, 3]),
            (
                AnyNode::Value(arena.value_quote_computation(k0)),
                &[first],
                &[0x1d, 3],
            ),
            (
                AnyNode::ValueType(arena.value_type_static_pi(t0, t1)),
                &[first, second],
                &[0x1e, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_static_application(v0, v1)),
                &[first, second],
                &[0x1f, 3, 0x81, 1],
            ),
        ];
        for &(node, children, expected) in cases {
            assert_eq!(
                super::encode_entry(&arena, node, children)
                    .0
                    .as_image()
                    .as_ref(),
                expected,
                "{node:?}"
            );
        }
    }

    #[test]
    fn interning_reuses_content_across_segments_without_losing_order()
    {
        let mut arena = TermArena::new();
        let first_unit = arena.value_unit();
        let second_unit = arena.value_unit();
        let variable = arena.value_variable(DeBruijnIndex::from(0x4000_u32));
        let first_pair = arena.value_pair(first_unit, variable);
        let equal_pair = arena.value_pair(second_unit, variable);
        let reversed = arena.value_pair(variable, first_unit);
        let mut interner = super::Interner::new();
        let mut first_segment = Vec::new();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(first_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        let prefix = first_segment.clone();
        let first_memo = interner.by_node.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(first_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        assert_eq!(interner.by_node, first_memo);
        assert_eq!(first_segment, prefix);
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut first_segment,
                AnyNode::Value(second_unit)
            ),
            GlobalIndex::from(0_u32)
        );
        assert_eq!(first_segment, prefix);
        assert_eq!(
            interner.by_node.get(&AnyNode::Value(second_unit)),
            Some(&GlobalIndex::from(0_u32))
        );
        let mut second_segment = Vec::new();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(first_pair)
            ),
            GlobalIndex::from(2_u32)
        );
        let expected: &[&[u8]] = &[&[0x09, 0x80, 0x80, 1], &[0x0d, 0, 1]];
        assert_eq!(second_segment.len(), expected.len());
        for (entry, &bytes) in second_segment.iter().zip(expected) {
            assert_eq!(entry.0.as_image().as_ref(), bytes);
        }
        let before_alias = second_segment.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(equal_pair)
            ),
            GlobalIndex::from(2_u32)
        );
        assert_eq!(second_segment, before_alias);
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut second_segment,
                AnyNode::Value(reversed)
            ),
            GlobalIndex::from(3_u32)
        );
        assert_eq!(
            second_segment
                .last()
                .expect("reversed entry")
                .0
                .as_image()
                .as_ref(),
            [0x0d, 1, 0]
        );
        assert_eq!(interner.next, GlobalIndex::from(4_u32));
        assert_eq!(interner.by_content.len(), 4);
        assert_eq!(interner.by_node.len(), 6);
        assert_eq!(first_segment, prefix);
    }

    #[test]
    fn declaration_sequences_match_literal_segment_fixtures()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let atom = builder.abstract_type(LevelSignature::monomorphic(), universe);
        let mut builder = DeclarationBuilder::new(&mut arena);
        let abstract_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let quote = builder.arena().value_quote(abstract_type);
        let definition = builder
            .def(LevelSignature::monomorphic(), universe, quote)
            .named(StructuredName::from(alloc::vec![
                NameSegment::from_text(String::from("a")).expect("segment"),
                NameSegment::from_text(String::from("é")).expect("segment"),
            ]));
        let axiom =
            DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), abstract_type);
        let declarations = [
            MarkedDeclaration::new(AdmissionMark::Checked, atom),
            MarkedDeclaration::new(AdmissionMark::UncheckedBypass, definition),
            MarkedDeclaration::new(AdmissionMark::Checked, axiom),
        ];
        let expected = [
            b'G', b'K', b'X', b'1', 2, 0, 1, 0, 3, 0, 2, 0, 0, 0, 1, 0x02, 0, 0, 0, 1, 0, 2, 1,
            b'a', 2, 0xc3, 0xa9, 0, 0, 2, 0x17, 0, 0x1c, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        assert_eq!(decoded.declarations().len(), 3);
        assert_eq!(
            decoded.declarations().get(1).expect("definition").mark(),
            AdmissionMark::UncheckedBypass
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
    }

    #[test]
    fn atom_positions_and_provenance_preserve_sequence_identity()
    {
        for mask in 0_u8 .. 64 {
            let mut arena = TermArena::new();
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let declared = arena.value_type_unit();
            let body = arena.value_unit();
            let mut declarations = Vec::new();
            let mut expected = Vec::new();
            for position in 0_u8 .. 6 {
                let builder = DeclarationBuilder::new(&mut arena);
                let is_atom = mask.checked_shr(u32::from(position)).unwrap_or(0) & 1 != 0;
                let declaration = if is_atom {
                    expected.push(usize::from(position));
                    builder.abstract_type(LevelSignature::monomorphic(), kind)
                }
                else if position.rem_euclid(2) == 0 {
                    builder.axiom(LevelSignature::monomorphic(), declared)
                }
                else {
                    builder.def(LevelSignature::monomorphic(), declared, body)
                };
                let mark = if position.rem_euclid(2) == 0 {
                    AdmissionMark::Checked
                }
                else {
                    AdmissionMark::UncheckedBypass
                };
                declarations.push(MarkedDeclaration::new(mark, declaration));
            }
            assert_eq!(
                super::minted_atoms(&declarations)
                    .into_iter()
                    .map(usize::from)
                    .collect::<Vec<_>>(),
                expected
            );
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_minted_atom_table(&mut out, &declarations);
            let mut bytes = alloc::vec![
                0xde_u8,
                0xad,
                u8::try_from(expected.len()).expect("at most six atoms")
            ];
            bytes.extend(
                expected
                    .into_iter()
                    .map(|position| u8::try_from(position).expect("six positions")),
            );
            assert_eq!(out.as_image().as_ref(), bytes.as_slice());
        }
        for (provenance, expected) in [
            (Vec::new(), alloc::vec![0]),
            (
                alloc::vec![
                    ConstantIndex::from(129_usize),
                    ConstantIndex::from(0_usize),
                    ConstantIndex::from(128_usize)
                ],
                alloc::vec![3, 0x81, 1, 0, 0x80, 1],
            ),
        ] {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_sealing_provenance(&mut out, &provenance);
            let mut bytes = alloc::vec![0xde_u8, 0xad];
            bytes.extend(expected);
            assert_eq!(out.as_image().as_ref(), bytes.as_slice());
        }
    }
}
