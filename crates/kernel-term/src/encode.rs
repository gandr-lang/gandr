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
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::ConstraintRelation;
use gandr_kernel_strata::Level;
use quenchant_shape::shape::Maybe;

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
use crate::decl::SealExtent;
use crate::decl::SealScope;
use crate::decl::StructuredName;
use crate::tags;
use crate::term::Computation;
use crate::term::ConstantIndex;
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

/// What an encoding of a sequence's leading declarations assigned, frozen for
/// every encoding that resumes after them.
///
/// # Specification
/// - requires: built from an interner that continued none, once its
///   declarations are written.
/// - ensures: holds that interner's node memo, its content deduplication and
///   its next free global index.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary;
///   [`encode_prefix`] builds it and [`Interner::after`] reads it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_after`].
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[derive(Debug)]
struct Assigned
{
    /// Arena node to its assigned global index.
    by_node: BTreeMap<AnyNode, GlobalIndex>,
    /// Encoded entry bytes to their global index.
    by_content: BTreeMap<EncodedEntry, GlobalIndex>,
    /// The next free global index.
    next: GlobalIndex,
}

/// The content-keyed subterm interner, carrying the global index counter and
/// both memos across declaration segments.
///
/// # Specification
/// - requires: the encoder supplies the state described by the consuming
///   operations.
/// - ensures: retains node memoization and byte-content deduplication across
///   segments with a saturating global counter; it belongs to one unchanged
///   arena. An interner that continues the frozen assignments of a leading run
///   answers from both, and records only what it assigns itself.
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
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[derive(Debug)]
struct Interner
{
    /// The frozen assignments of an encoding of the sequence's leading
    /// declarations, which this one continues; none for a whole encoding.
    base: Option<Arc<Assigned>>,
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
    /// - ensures: returns an interner holding no node and no content and
    ///   continuing none, with the next free global index at zero.
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
    /// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
    /// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
    #[spec(
        ensures: |ret| ret.base.is_none()
                && ret.by_node.is_empty()
                && ret.by_content.is_empty()
                && u32::from(ret.next) == 0,
    )]
    #[inline]
    fn new() -> Self
    {
        Self {
            base: None,
            by_node: BTreeMap::new(),
            by_content: BTreeMap::new(),
            next: GlobalIndex::default(),
        }
    }

    /// An interner continuing `base`, the frozen assignments of an encoding of
    /// the sequence's leading declarations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers every node and content `base` assigned as `base`
    ///   does, holds nothing of its own, and assigns from `base`'s next free
    ///   index.
    /// - provides: the resumed encoding's index space, shared rather than
    ///   copied, so resuming costs nothing in the prefix's size.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every split of mixed and shared sequences, resumed
    ///   after its prefix, writes the whole encoding's bytes.
    /// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
    #[spec(
        captures: [kept = Arc::as_ptr(&base), next = base.next],
        ensures: |ret| ret.by_node.is_empty()
                && ret.by_content.is_empty()
                && ret.base.as_ref().is_some_and(|held| Arc::as_ptr(held) == kept)
                && ret.next == next,
    )]
    #[inline]
    fn after(base: Arc<Assigned>) -> Self
    {
        Self {
            next: base.next,
            base: Some(base),
            by_node: BTreeMap::new(),
            by_content: BTreeMap::new(),
        }
    }

    /// The assignments this interner made, frozen for an encoding that
    /// resumes after them.
    ///
    /// # Specification
    /// - requires: the interner continues none.
    /// - ensures: its node memo, content deduplication and next free index,
    ///   moved rather than copied.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`encode_after`].
    /// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
    #[spec(
        requires: self.base.is_none(),
        captures: [nodes = self.by_node.len(), contents = self.by_content.len(), next = self.next],
        ensures: |ret| ret.by_node.len() == nodes
                && ret.by_content.len() == contents
                && ret.next == next,
    )]
    #[inline]
    fn freeze(self) -> Assigned
    {
        Assigned {
            by_node: self.by_node,
            by_content: self.by_content,
            next: self.next,
        }
    }

    /// The global index an earlier root assigned `node`, here or in the base.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node(
        &self,
        node: AnyNode,
    ) -> Option<GlobalIndex>
    {
        self.by_node
            .get(&node)
            .copied()
            .or_else(|| self.base.as_ref()?.by_node.get(&node).copied())
    }

    /// The global index the entry with `entry`'s bytes took, here or in the
    /// base.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn content(
        &self,
        entry: &EncodedEntry,
    ) -> Option<GlobalIndex>
    {
        self.by_content
            .get(entry)
            .copied()
            .or_else(|| self.base.as_ref()?.by_content.get(entry).copied())
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
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
#[inline]
#[must_use]
#[spec(requires: declarations.iter().all(|marked| { let declaration = marked.declaration(); arena.value_type(declaration.declared_id()).is_some() && match *declaration.content() { DeclarationContent::Def { body, .. } => arena.value(body).is_some(), DeclarationContent::Data { ref parameters, ref constructors, .. } => parameters.iter().chain(constructors.iter().flatten()).all(|id| arena.value_type(*id).is_some()), DeclarationContent::Codata { ref parameters, ref observations, .. } => parameters.iter().all(|id| arena.value_type(*id).is_some()) && observations.iter().all(|id| arena.comp_type(*id).is_some()), DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => true } }),
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
    for (position, declaration) in declarations.iter().enumerate() {
        let remaining = SealExtent::from(
            declarations
                .len()
                .saturating_sub(position)
                .saturating_sub(1),
        );
        encode_declaration(&mut out, arena, &mut interner, declaration, remaining);
    }
    out
}

/// The encoding of an admission-ordered sequence's leading declarations, which
/// an encoding of any sequence leading with them resumes.
///
/// # Specification
/// - requires: constructed by [`encode_prefix`].
/// - ensures: holds the leading declarations' segments as [`encode`] writes
///   them, the minted atoms among them, and the interner their encoding left,
///   frozen.
/// - panics: none.
/// - executable: none — the fields are private and set only by
///   [`encode_prefix`], whose specification states them.
///
/// # Adequacy
/// - hypothesis: L3 — as [`encode_after`].
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[derive(Clone, Debug)]
pub struct EncodedPrefix
{
    /// The leading declarations' segments, in admission order.
    segments: EncodedArtifact,
    /// The admission positions of the abstract types among them.
    atoms: Vec<MintedAtom>,
    /// How many declarations lead.
    count: usize,
    /// What their encoding assigned, shared by every encoding resumed after it.
    assigned: Arc<Assigned>,
}

impl EncodedPrefix
{
    /// The admission position the first declaration after the prefix takes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn end(&self) -> ConstantIndex
    {
        ConstantIndex::from(self.count)
    }
}

quenchant_shape::reason_enum! {
    /// Why a sequence's leading declarations have no encoding to resume.
    pub mod encoded_prefix {
        /// The reason no prefix is encoded.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// An abstract type among them is sealed to the end of the
            /// sequence, so its segment depends on what follows.
            OpenSeal,
        }
    }
}

/// The encoding of `declarations`, the leading declarations of a sequence over
/// `arena`, for [`encode_after`] to resume.
///
/// # Specification
/// - requires: as [`encode`].
/// - ensures: absent as [`encoded_prefix::Absent::OpenSeal`] when an abstract
///   type among `declarations` has an open seal; otherwise the segments
///   [`encode`] writes for `declarations` after its header, ending at
///   `declarations`' length, and the interner those segments left.
/// - provides: what an editor's admission encodes once for a document's import
///   closure, so that each revision of the document encodes its own
///   declarations alone.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Adequacy
/// - hypothesis: L3 — every split of mixed and shared sequences, resumed after
///   its prefix, writes the whole encoding's bytes; a prefix with an open seal
///   is refused.
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
/// - witness: `encode::tests::a_prefix_with_an_open_seal_is_not_encoded_776`
#[inline]
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref prefix) => usize::from(prefix.end()) == declarations.len()
        && prefix.atoms == minted_atoms(declarations),
    Maybe::Absent(encoded_prefix::Absent::OpenSeal) => declarations.iter().any(|marked| matches!(
        *marked.declaration().content(),
        DeclarationContent::AbstractType { scope: SealScope::Open, .. }
    )),
})]
pub fn encode_prefix(
    arena: &TermArena,
    declarations: &[MarkedDeclaration],
) -> Maybe<EncodedPrefix, encoded_prefix::Absent>
{
    if declarations.iter().any(|marked| {
        matches!(
            *marked.declaration().content(),
            DeclarationContent::AbstractType {
                scope: SealScope::Open,
                ..
            }
        )
    }) {
        return Maybe::Absent(encoded_prefix::Absent::OpenSeal);
    }
    let mut segments = EncodedArtifact::new();
    let mut interner = Interner::new();
    for declaration in declarations {
        // No seal is open, so no segment reads how many declarations follow.
        encode_declaration(
            &mut segments,
            arena,
            &mut interner,
            declaration,
            SealExtent::from(0_usize),
        );
    }
    Maybe::Present(EncodedPrefix {
        segments,
        atoms: minted_atoms(declarations),
        count: declarations.len(),
        assigned: Arc::new(interner.freeze()),
    })
}

/// [`encode`] of the sequence `prefix`'s declarations lead and `after`
/// follows, writing `prefix`'s segments as they were encoded and encoding
/// `after`'s alone.
///
/// # Specification
/// - requires: `prefix` was encoded by [`encode_prefix`] over an arena whose
///   nodes `arena` holds at the same ids, and `after` follows the declarations
///   it encoded; the sequence is in [`encode`]'s domain.
/// - ensures: [`encode`]'s bytes for the whole sequence: its header, then
///   `prefix`'s segments, then `after`'s.
/// - provides: an encoding whose cost is `after`'s, and a copy of `prefix`'s
///   bytes.
/// - fails: never within [`encode`]'s domain.
/// - panics: none within that domain.
///
/// # Adequacy
/// - hypothesis: L3 — every split of mixed and shared sequences, resumed after
///   its prefix, writes the whole encoding's bytes.
/// - witness: `encode::tests::an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice())
    && ret.as_image().as_ref().len() > prefix.segments.as_image().as_ref().len())]
pub fn encode_after(
    prefix: &EncodedPrefix,
    arena: &TermArena,
    after: &[MarkedDeclaration],
) -> EncodedArtifact
{
    let mut out = EncodedArtifact::new();
    out.put_image(ArtifactImage::from(tags::MAGIC.as_slice()));
    out.put_version(tags::FORMAT_VERSION);
    let minted = minted_atoms(after);
    out.put_uvarint(WireU64::from(WireUsize::from(
        prefix.atoms.len().saturating_add(minted.len()),
    )));
    for atom in &prefix.atoms {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(*atom))));
    }
    for atom in minted {
        out.put_uvarint(WireU64::from(WireUsize::from(
            prefix.count.saturating_add(usize::from(atom)),
        )));
    }
    out.put_uvarint(WireU64::from(WireUsize::from(
        prefix.count.saturating_add(after.len()),
    )));
    out.put_image(prefix.segments.as_image());
    let mut interner = Interner::after(Arc::clone(&prefix.assigned));
    for (position, declaration) in after.iter().enumerate() {
        let remaining = SealExtent::from(after.len().saturating_sub(position).saturating_sub(1));
        encode_declaration(&mut out, arena, &mut interner, declaration, remaining);
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
///   and value-type roots are admitted. `remaining` counts the declarations
///   after this one in the sequence.
/// - ensures: writes the mark, kind, name and level interface, then only newly
///   completed entries, in first-completion order. Definitions write
///   declared/body roots and four annotation slots, and a definition relating
///   endpoints writes [`tags::KIND_DEF_RELATING`] and closes with the pair
///   count and each pair's roots and dialogue; a definition resting on laws
///   writes [`tags::KIND_DEF_LAWFUL`] and closes with the pair block, its count
///   possibly zero, then the law count and each law's position; a definition
///   carrying an operation's rules writes [`tags::KIND_DEF_RULED`] and closes
///   with the pair block and the law block, both counts possibly zero, then the
///   rule count and each rule's two sides; a data declaration presenting rules
///   writes [`tags::KIND_DATA_PRESENTED`] and closes with the rule count and
///   each rule's two sides; a type of words writes [`tags::KIND_DATA_WORDS`]
///   and closes with the rule block, its count possibly zero, then the sort's
///   position, the cell count and each cell's two endpoints as rule sides; an
///   indexed data declaration writes [`tags::KIND_DATA_INDEXED`] and closes
///   with the index count, each index classifier's root and each constructor's
///   result roots, and no rules; a codata declaration writes
///   [`tags::KIND_CODATA`] and closes with its parameter count and roots, then
///   its observation count and roots; abstract types write their kind and
///   representation roots and the extent of their scope, an open scope as
///   `remaining`, and an interfaced one writes
///   [`tags::KIND_ABSTRACT_INTERFACED`] and closes with its relation's and its
///   reflexivity's roots, or, when its interface states a law,
///   [`tags::KIND_ABSTRACT_LAWFUL`] and the law's root after them; the other
///   kinds write one root and no slots.
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
/// - witness: `encode::tests::a_relating_definition_closes_its_segment_with_its_pairs`
/// - witness: `encode::tests::a_lawful_definition_closes_its_segment_with_its_laws`
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_type_of_words_closes_its_segment_with_its_cells`
/// - witness: `encode::tests::an_interfaced_atom_closes_its_segment_with_its_interface`
/// - witness: `encode::tests::an_indexed_data_declaration_closes_its_segment_with_its_indices`
/// - witness: `encode::tests::a_codata_declaration_closes_its_segment_with_its_observations`
#[spec(
    captures: entry = (out.as_image().as_ref().len(), interner.by_content.len(), interner.next),
    ensures: |ret| { let image = out.as_image();
        let bytes = image.as_ref();
        bytes.get(entry.0).copied() == Some(u8::from(match marked.mark() { AdmissionMark::Checked => tags::ADMISSION_CHECKED, AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED }))
            && bytes.get(entry.0.saturating_add(1)).copied() == Some(u8::from(match *marked.declaration().content() { DeclarationContent::Data { ref indices, .. } if !indices.is_empty() => tags::KIND_DATA_INDEXED, DeclarationContent::Data { .. } if marked.declaration().presentation().cells().is_some() => tags::KIND_DATA_WORDS, DeclarationContent::Data { .. } if marked.declaration().presentation().rules().is_empty() => tags::KIND_DATA, DeclarationContent::Data { .. } => tags::KIND_DATA_PRESENTED, DeclarationContent::Codata { .. } => tags::KIND_CODATA, DeclarationContent::Def { .. } if !marked.declaration().operation_rules().rules().is_empty() => tags::KIND_DEF_RULED, DeclarationContent::Def { .. } if !marked.declaration().laws().is_empty() => tags::KIND_DEF_LAWFUL, DeclarationContent::Def { .. } if marked.declaration().related().is_empty() => tags::KIND_DEF, DeclarationContent::Def { .. } => tags::KIND_DEF_RELATING, DeclarationContent::Axiom { .. } => tags::KIND_AXIOM, DeclarationContent::AbstractType { interface: Maybe::Present(ref interface), .. } if matches!(interface.law(), Maybe::Present(_)) => tags::KIND_ABSTRACT_LAWFUL, DeclarationContent::AbstractType { interface: Maybe::Present(_), .. } => tags::KIND_ABSTRACT_INTERFACED, DeclarationContent::AbstractType { .. } => tags::KIND_ABSTRACT_TYPE }))
            && interner.node(AnyNode::ValueType(marked.declaration().declared_id())).is_some()
            && match *marked.declaration().content() { DeclarationContent::Def { body, .. } => interner.node(AnyNode::Value(body)).is_some(), DeclarationContent::Codata { ref observations, .. } => observations.iter().all(|id| interner.node(AnyNode::CompType(*id)).is_some()), DeclarationContent::AbstractType { interface: Maybe::Present(interface), .. } => interner.node(AnyNode::Value(interface.relation())).is_some() && interner.node(AnyNode::Value(interface.reflexivity())).is_some() && match interface.law() { Maybe::Present(law) => interner.node(AnyNode::Value(law)).is_some(), Maybe::Absent(_) => true }, DeclarationContent::Data { .. } | DeclarationContent::Axiom { .. } | DeclarationContent::AbstractType { .. } => true }
            && marked.declaration().related().iter().all(|related| interner.node(AnyNode::Value(related.left)).is_some() && interner.node(AnyNode::Value(related.right)).is_some())
            && interner.by_content.len() >= entry.1
            && u32::from(interner.next) == u32::from(entry.2).saturating_add(u32::try_from(interner.by_content.len().saturating_sub(entry.1)).unwrap_or(u32::MAX)) },
)]
fn encode_declaration(
    out: &mut EncodedArtifact,
    arena: &TermArena,
    interner: &mut Interner,
    marked: &MarkedDeclaration,
    remaining: SealExtent,
)
{
    out.put_tag(match marked.mark() {
        AdmissionMark::Checked => tags::ADMISSION_CHECKED,
        AdmissionMark::UncheckedBypass => tags::ADMISSION_UNCHECKED,
    });
    let declaration = marked.declaration();
    let content = declaration.content();
    out.put_tag(match *content {
        DeclarationContent::Data { ref indices, .. } if !indices.is_empty() => {
            tags::KIND_DATA_INDEXED
        },
        DeclarationContent::Data { .. } if declaration.presentation().cells().is_some() => {
            tags::KIND_DATA_WORDS
        },
        DeclarationContent::Data { .. } if declaration.presentation().rules().is_empty() => {
            tags::KIND_DATA
        },
        DeclarationContent::Data { .. } => tags::KIND_DATA_PRESENTED,
        DeclarationContent::Codata { .. } => tags::KIND_CODATA,
        DeclarationContent::Def { .. } if !declaration.operation_rules().rules().is_empty() => {
            tags::KIND_DEF_RULED
        },
        DeclarationContent::Def { .. } if !declaration.laws().is_empty() => tags::KIND_DEF_LAWFUL,
        DeclarationContent::Def { .. } if declaration.related().is_empty() => tags::KIND_DEF,
        DeclarationContent::Def { .. } => tags::KIND_DEF_RELATING,
        DeclarationContent::Axiom { .. } => tags::KIND_AXIOM,
        DeclarationContent::AbstractType {
            interface: Maybe::Present(ref interface),
            ..
        } if matches!(interface.law(), Maybe::Present(_)) => tags::KIND_ABSTRACT_LAWFUL,
        DeclarationContent::AbstractType {
            interface: Maybe::Present(_),
            ..
        } => tags::KIND_ABSTRACT_INTERFACED,
        DeclarationContent::AbstractType { .. } => tags::KIND_ABSTRACT_TYPE,
    });
    encode_structured_name(out, declaration.name());
    encode_level_signature(out, declaration.levels());

    let mut segment: Vec<EncodedEntry> = Vec::new();
    let mut data_roots = Vec::new();
    let mut index_roots = Vec::new();
    let mut related_roots = Vec::new();
    let mut interface_roots = None;
    let mut observation_roots = Vec::new();
    let (root_declared, root_body, root_sealed) = match *content {
        DeclarationContent::Data {
            kind,
            ref parameters,
            ref indices,
            ref constructors,
            ref results,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            for group in core::iter::once(parameters).chain(constructors.iter()) {
                let roots = group
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id)))
                    .collect::<Vec<_>>();
                data_roots.push(roots);
            }
            // The indices after the constructors, so a family indexed by
            // nothing interns exactly what it did before the kind existed.
            index_roots.extend(
                indices
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id))),
            );
            for result in results.iter().flatten() {
                index_roots.push(intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(*result),
                ));
            }
            (declared, None, None)
        },
        // A codata declaration writes its kind as its declared root, then its
        // parameter roots in the data roots' first group and its observations'
        // computation-type roots after them.
        DeclarationContent::Codata {
            kind,
            ref parameters,
            ref observations,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            data_roots.push(
                parameters
                    .iter()
                    .map(|id| intern(arena, interner, &mut segment, AnyNode::ValueType(*id)))
                    .collect::<Vec<_>>(),
            );
            observation_roots = observations
                .iter()
                .map(|id| intern(arena, interner, &mut segment, AnyNode::CompType(*id)))
                .collect();
            (declared, None, None)
        },
        DeclarationContent::Def { declared, body } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            let body = intern(arena, interner, &mut segment, AnyNode::Value(body));
            // The related endpoints after the body, so a definition relating
            // none interns exactly what it did before the kind existed.
            for related in declaration.related() {
                let left = intern(arena, interner, &mut segment, AnyNode::Value(related.left));
                let right = intern(arena, interner, &mut segment, AnyNode::Value(related.right));
                related_roots.push((left, right));
            }
            (declared, Some(body), None)
        },
        DeclarationContent::Axiom { declared } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(declared));
            (declared, None, None)
        },
        // An abstract type writes its kind as its declared root, its
        // representation as a second value-type root, and its scope's extent.
        // The representation is on the wire because the kernel re-reads it
        // inside the minting admission when it replays the artifact; outside
        // that admission no rule reads it. An interface's two roots come after
        // the representation, so an atom with none interns exactly what it
        // did before the kind existed.
        DeclarationContent::AbstractType {
            kind,
            representation,
            scope,
            interface,
        } => {
            let declared = intern(arena, interner, &mut segment, AnyNode::ValueType(kind));
            let representation = intern(
                arena,
                interner,
                &mut segment,
                AnyNode::ValueType(representation),
            );
            if let Maybe::Present(interface) = interface {
                let relation = intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(interface.relation()),
                );
                let reflexivity = intern(
                    arena,
                    interner,
                    &mut segment,
                    AnyNode::Value(interface.reflexivity()),
                );
                let law = match interface.law() {
                    Maybe::Present(law) => {
                        Some(intern(arena, interner, &mut segment, AnyNode::Value(law)))
                    },
                    Maybe::Absent(_) => None,
                };
                interface_roots = Some((relation, reflexivity, law));
            }
            let extent = match scope {
                SealScope::Open => remaining,
                SealScope::Closed(extent) => extent,
            };
            (declared, None, Some((representation, extent)))
        },
    };
    out.put_uvarint(WireU64::from(WireUsize::from(segment.len())));
    for entry in &segment {
        out.put_image(entry.0.as_image());
    }
    out.put_uvarint(WireU64::from(u64::from(u32::from(root_declared))));
    if let Some((representation, extent)) = root_sealed {
        out.put_uvarint(WireU64::from(u64::from(u32::from(representation))));
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(extent))));
    }
    if let Some((relation, reflexivity, law)) = interface_roots {
        out.put_uvarint(WireU64::from(u64::from(u32::from(relation))));
        out.put_uvarint(WireU64::from(u64::from(u32::from(reflexivity))));
        if let Some(law) = law {
            out.put_uvarint(WireU64::from(u64::from(u32::from(law))));
        }
    }
    if let DeclarationContent::Data {
        ref indices,
        ref constructors,
        ..
    } = *(content)
    {
        for (index, group) in data_roots.iter().enumerate() {
            if index == 1 {
                out.put_uvarint(WireU64::from(WireUsize::from(constructors.len())));
            }
            out.put_uvarint(WireU64::from(WireUsize::from(group.len())));
            for root in group {
                out.put_uvarint(WireU64::from(u64::from(u32::from(*root))));
            }
        }
        if constructors.is_empty() {
            out.put_uvarint(WireU64::from(0_u64));
        }
        if !indices.is_empty() {
            out.put_uvarint(WireU64::from(WireUsize::from(indices.len())));
            for root in &index_roots {
                out.put_uvarint(WireU64::from(u64::from(u32::from(*root))));
            }
        }
    }
    if let DeclarationContent::Codata { .. } = *content {
        for group in [
            data_roots.first().map_or(&[][..], Vec::as_slice),
            &observation_roots,
        ] {
            out.put_uvarint(WireU64::from(WireUsize::from(group.len())));
            for root in group {
                out.put_uvarint(WireU64::from(u64::from(u32::from(*root))));
            }
        }
    }
    if let Some(root_body) = root_body {
        out.put_uvarint(WireU64::from(u64::from(u32::from(root_body))));
        // The four per-definition annotation slots. The first, erasure, carries
        // the stages the signature quantifies over; modes and grades, and
        // directedness and variance stay reserved and empty; the third is the
        // sealing-provenance slot, and it carries the atoms this declaration's
        // projection rebound. A choke point re-derives them from the declared
        // type rather than believing them.
        encode_stage_signature(out, declaration.stages());
        out.put_uvarint(WireU64::from(0_u64));
        encode_sealing_provenance(out, declaration.provenance());
        out.put_uvarint(WireU64::from(0_u64));
    }
    // The relating block closes a definition's segment: a pair count of at
    // least one, since a definition relating none wrote the plain kind, then
    // each pair's roots and its dialogue. A lawful definition writes the block
    // whatever its count, and its laws after it: a count of at least one and
    // each law's position. A ruled definition writes both blocks whatever
    // their counts, then its rules: a count of at least one and each rule's
    // two sides.
    let laws = declaration.laws();
    let operation_rules = declaration.operation_rules().rules();
    if !related_roots.is_empty() || !laws.is_empty() || !operation_rules.is_empty() {
        out.put_uvarint(WireU64::from(WireUsize::from(related_roots.len())));
        for (&(left, right), related) in related_roots.iter().zip(declaration.related()) {
            out.put_uvarint(WireU64::from(u64::from(u32::from(left))));
            out.put_uvarint(WireU64::from(u64::from(u32::from(right))));
            out.put_uvarint(WireU64::from(WireUsize::from(related.dialogue.len())));
            for &decision in &related.dialogue {
                out.put_uvarint(WireU64::from(crate::term::decision_word(decision).0));
            }
        }
    }
    if !laws.is_empty() || !operation_rules.is_empty() {
        out.put_uvarint(WireU64::from(WireUsize::from(laws.len())));
        for &law in laws {
            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(law))));
        }
    }
    if !operation_rules.is_empty() {
        out.put_uvarint(WireU64::from(WireUsize::from(operation_rules.len())));
        for rule in operation_rules {
            encode_operation_side(out, rule.left());
            encode_operation_side(out, rule.right());
        }
    }
    // The rule block closes a presented data declaration's segment: a rule
    // count of at least one, since a free type wrote the plain kind, then each
    // rule's left and right sides, a node count and the nodes in pre-order. A
    // type of words writes the block whatever its count, then its sort's
    // position and its cells, each endpoint a side as a rule's are. An indexed
    // type presents no rules, which admission refuses, and writes none.
    let presentation = declaration.presentation();
    let rules = presentation.rules();
    let cells = presentation.cells();
    let indexed =
        matches!(*content, DeclarationContent::Data { ref indices, .. } if !indices.is_empty());
    if indexed {
        return;
    }
    if !rules.is_empty() || cells.is_some() {
        out.put_uvarint(WireU64::from(WireUsize::from(rules.len())));
        for rule in rules {
            encode_rule_side(out, rule.left());
            encode_rule_side(out, rule.right());
        }
    }
    if let Some(cells) = cells {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(cells.sort()))));
        out.put_uvarint(WireU64::from(WireUsize::from(cells.cells().len())));
        for cell in cells.cells() {
            encode_rule_side(out, cell.source());
            encode_rule_side(out, cell.target());
        }
    }
}

/// Write a definition's stage signature into its erasure slot: the binder
/// count, zero for a signature binding none; then each binder's bound, zero
/// for none and one past the earlier binder's ordinal otherwise; then the
/// mark count and each mark's binder, reach — zero at the binder, the depth
/// below it — path length and steps.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a signature binding no stage writes the one byte an empty slot
///   writes, so a definition quantified over none crosses as it did before the
///   slot was live.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a signature with a bound binder and two marks writes its
///   literal bytes and decodes to itself; an empty one writes zero.
/// - witness: `encode::tests::a_stage_signature_fills_the_erasure_slot`
#[spec(
    captures: entry = out.as_image().as_ref().len(),
    ensures: !stages.bounds().is_empty() || out.as_image().as_ref().get(entry ..) == Some(&[0_u8][..]),
)]
fn encode_stage_signature(
    out: &mut EncodedArtifact,
    stages: &crate::stage_signature::StageSignature,
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(stages.bounds().len())));
    if stages.bounds().is_empty() {
        return;
    }
    for &bound in stages.bounds() {
        out.put_uvarint(WireU64::from(WireUsize::from(match bound {
            crate::stage_signature::StageBound::Unbounded => 0_usize,
            crate::stage_signature::StageBound::Below(binder) => {
                usize::from(binder).saturating_add(1)
            },
        })));
    }
    out.put_uvarint(WireU64::from(WireUsize::from(stages.marks().len())));
    for mark in stages.marks() {
        out.put_uvarint(WireU64::from(WireUsize::from(usize::from(mark.binder()))));
        out.put_uvarint(WireU64::from(match mark.reach() {
            crate::stage_signature::StageReach::At => 0_u64,
            crate::stage_signature::StageReach::Below(depth) => u64::from(u32::from(depth)),
        }));
        out.put_uvarint(WireU64::from(WireUsize::from(mark.path().len())));
        for &step in mark.path() {
            out.put_uvarint(WireU64::from(WireUsize::from(usize::from(step))));
        }
    }
}

/// Write one rule side: its node count, then each node's tag and ordinal in
/// pre-order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the count and every node are written, in order, and nothing else.
/// - provides: the one spelling of a side, a rule's and a cell's endpoint
///   alike, that `decode_rule_side` reads back.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a presented declaration and a type of words round-trip
///   every side.
/// - witness: `encode::tests::a_presented_data_declaration_closes_its_segment_with_its_rules`
/// - witness: `encode::tests::a_type_of_words_closes_its_segment_with_its_cells`
#[spec(captures: before = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > before)]
fn encode_rule_side(
    out: &mut EncodedArtifact,
    side: &[crate::presented::RuleNode],
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(side.len())));
    for &node in side {
        let (tag, ordinal) = match node {
            crate::presented::RuleNode::Constructor(tag) => (
                tags::RULE_CONSTRUCTOR,
                WireU64::from(WireUsize::from(usize::from(tag))),
            ),
            crate::presented::RuleNode::Variable(variable) => (
                tags::RULE_VARIABLE,
                WireU64::from(u64::from(u32::from(variable))),
            ),
        };
        out.put_tag(tag);
        out.put_uvarint(ordinal);
    }
}

/// Write one side of an operation's rule: its node count, then each node's
/// tag and payload in pre-order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the count and every node are written, in order, and nothing else:
///   an operation as its position and arity, a constructor as its data
///   declaration's position and its ordinal, a results tuple as its count, a
///   variable as its ordinal.
/// - provides: the one spelling of an operation's side, which
///   `decode_operation_side` reads back.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a ruled definition round-trips every side.
/// - witness: `encode::tests::a_ruled_definition_closes_its_segment_with_its_rules`
#[spec(captures: before = out.as_image().as_ref().len(), ensures: out.as_image().as_ref().len() > before)]
fn encode_operation_side(
    out: &mut EncodedArtifact,
    side: &[crate::operation_rules::OperationNode],
)
{
    out.put_uvarint(WireU64::from(WireUsize::from(side.len())));
    for &node in side {
        match node {
            crate::operation_rules::OperationNode::Operation { constant, arity } => {
                out.put_tag(tags::RULE_OPERATION);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(constant))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(arity))));
            },
            crate::operation_rules::OperationNode::Constructor { family, tag } => {
                out.put_tag(tags::RULE_CONSTRUCTOR);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(family))));
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(tag))));
            },
            crate::operation_rules::OperationNode::Results(count) => {
                out.put_tag(tags::RULE_RESULTS);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(count))));
            },
            crate::operation_rules::OperationNode::Variable(variable) => {
                out.put_tag(tags::RULE_VARIABLE);
                out.put_uvarint(WireU64::from(u64::from(u32::from(variable))));
            },
        }
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
/// - witness: `tests::sharing_format::a_structured_name_round_trips_as_segments`
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
///   index; an already memoized root changes neither segment nor memo; a staged
///   value type takes its base's index and appends nothing.
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
/// - witness: `encode::tests::a_staged_type_is_written_as_its_base`
/// - witness: `tests::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `tests::adversarial_depth::a_deep_decoded_graph_tears_down_inside_a_small_stack_thread`
#[spec(requires: match root { AnyNode::ValueType(id) => arena.value_type(id).is_some(), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },

    captures: entry = (interner.node(root), interner.by_node.len(), interner.by_content.len(), segment.len(), interner.next),
    ensures: |ret| interner.node(root) == Some(ret)
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
    // The children's indices of the node being written, refilled per node.
    let mut child_globals: Vec<GlobalIndex> = Vec::new();
    while let Some((node, cursor)) = stack.pop() {
        if interner.node(node).is_some() {
            continue;
        }
        let children = arena.children_of(node);
        let mut next = cursor;
        let mut descended = false;
        while let Some(&child) = children.get(next) {
            if interner.node(child).is_some() {
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
        // A stage is admission's alone: the wire holds the type it refines, so
        // a staged node takes its base's index and writes no entry.
        if let AnyNode::ValueType(id) = node
            && let Some(&ValueType::Staged { base, .. }) = arena.value_type(id)
        {
            let global = interner.node(AnyNode::ValueType(base)).unwrap_or_default();
            let _prior = interner.by_node.insert(node, global);
            continue;
        }
        child_globals.clear();
        child_globals.extend(
            children
                .iter()
                .map(|&child| interner.node(child).unwrap_or_default()),
        );
        let encoded = encode_entry(arena, node, &child_globals);
        let deduplicated = interner.content(&encoded);
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
    interner.node(root).unwrap_or_default()
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
#[spec(requires: match node { AnyNode::ValueType(id) => arena.value_type(id).is_some_and(|value_type| !matches!(value_type, ValueType::Staged { .. })), AnyNode::CompType(id) => arena.comp_type(id).is_some(), AnyNode::Value(id) => arena.value(id).is_some(), AnyNode::Computation(id) => arena.computation(id).is_some() },
ensures: |ret| ret.0.as_image().as_ref().first().copied()
    == Some(u8::from(match node {
        AnyNode::ValueType(id) => match arena.value_type(id) {
            Some(&ValueType::Data { .. }) => tags::NODE_VT_DATA,
            Some(&ValueType::Record(_)) => tags::NODE_VT_RECORD,
            Some(&ValueType::PathUniverse(..)) => tags::NODE_VT_PATH_UNIVERSE,
            Some(&ValueType::FlowUniverse(..)) => tags::NODE_VT_FLOW_UNIVERSE,
            Some(&ValueType::Path { .. }) => tags::NODE_VT_PATH,
            Some(&ValueType::Flow { .. }) => tags::NODE_VT_FLOW,
            Some(&ValueType::Bridge { .. }) => tags::NODE_VT_BRIDGE,
            Some(&ValueType::Base(_)) => tags::NODE_VT_BASE,
            Some(&ValueType::Universe { sort: GroundSort::Value, .. }) => tags::NODE_VT_UNIVERSE,
            Some(&ValueType::Universe { sort: GroundSort::Computation, .. }) => {
                tags::NODE_VT_COMPUTATION_UNIVERSE
            },
            Some(&ValueType::Abstract(_)) => tags::NODE_VT_ABSTRACT,
            None | Some(&ValueType::Product(_) | &ValueType::Staged { .. }) => tags::NODE_VT_PRODUCT,
            Some(&ValueType::Sigma { .. }) => tags::NODE_VT_SIGMA,
            Some(&ValueType::Sum(..)) => tags::NODE_VT_SUM,
            Some(&ValueType::Session { .. }) => tags::NODE_VT_SESSION,
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
            Some(&CompType::With(..)) => tags::NODE_CT_WITH,
            Some(&CompType::Codata { .. }) => tags::NODE_CT_CODATA,
        },
        AnyNode::Value(id) => match arena.value(id) {
            Some(&Value::Constructor { .. }) => tags::NODE_V_CONSTRUCTOR,
            Some(&Value::Record(_)) => tags::NODE_V_RECORD,
            Some(&Value::SessionPath { .. }) => tags::NODE_V_SESSION_PATH,
            Some(&Value::SessionFlow { .. }) => tags::NODE_V_SESSION_FLOW,
            Some(&Value::Stay { .. }) => tags::NODE_V_STAY,
            Some(&Value::ForwardFlow { .. }) => tags::NODE_V_FORWARD_FLOW,
            Some(&Value::FunctionFlow { .. }) => tags::NODE_V_FUNCTION_FLOW,
            Some(&Value::Then { .. }) => tags::NODE_V_THEN,
            Some(&Value::FlowProduct(..)) => tags::NODE_V_FLOW_PRODUCT,
            Some(&Value::PathRefl(_)) => tags::NODE_V_PATH_REFL,
            Some(&Value::PathProduct(..)) => tags::NODE_V_PATH_PRODUCT,
            Some(&Value::PathEquiv { .. }) => tags::NODE_V_PATH_EQUIV,
            Some(&Value::Univalence { .. }) => tags::NODE_V_UNIVALENCE,
            Some(&Value::Here { .. }) => tags::NODE_V_HERE,
            Some(&Value::Returned(_)) => tags::NODE_V_RETURNED,
            Some(&Value::Higher { .. }) => tags::NODE_V_HIGHER,
            Some(&Value::HigherEvaluation { .. }) => tags::NODE_V_HIGHER_EVALUATION,
            Some(&Value::QuantifiedEvaluation { .. }) => tags::NODE_V_QUANTIFIED_EVALUATION,
            Some(&Value::Variable(_)) => tags::NODE_V_VARIABLE,
            Some(&Value::Constant(_)) => tags::NODE_V_CONSTANT,
            Some(&Value::Literal(_)) => tags::NODE_V_LITERAL,
            None | Some(&Value::Tuple(_)) => tags::NODE_V_TUPLE,
            Some(&Value::Injection(..)) => tags::NODE_V_INJECTION,
            Some(&Value::ListNil) => tags::NODE_V_LIST_NIL,
            Some(&Value::ListCons(..)) => tags::NODE_V_LIST_CONS,
            Some(&Value::Thunk(_)) => tags::NODE_V_THUNK,
            Some(&Value::Lift { .. }) => tags::NODE_V_LIFT,
            Some(&Value::Quote(_)) => tags::NODE_V_QUOTE,
            Some(&Value::QuoteComputation(_)) => tags::NODE_V_QUOTE_COMPUTATION,
            Some(&Value::StaticApplication(..)) => tags::NODE_V_STATIC_APPLICATION,
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::DataCase { equations, .. }) => {
                if equations == crate::EquationCount::NONE {
                    tags::NODE_C_DATA_CASE
                }
                else {
                    tags::NODE_C_INDEXED_DATA_CASE
                }
            },
            Some(&Computation::SigmaSplit { .. }) => tags::NODE_C_SIGMA_SPLIT,
            Some(&Computation::RecordProjection(..)) => tags::NODE_C_RECORD_PROJECTION,
            Some(&Computation::TupleProjection(..)) => tags::NODE_C_TUPLE_PROJECTION,
            Some(&Computation::Transport(..)) => tags::NODE_C_TRANSPORT,
            Some(&Computation::PathTransport { .. }) => tags::NODE_C_PATH_TRANSPORT,
            Some(&Computation::TelescopeTransport { .. }) => tags::NODE_C_TELESCOPE_TRANSPORT,
            Some(&Computation::Ride { .. }) => tags::NODE_C_RIDE,
            Some(&Computation::TelescopeRide { .. }) => tags::NODE_C_TELESCOPE_RIDE,
            Some(&Computation::RelatedApplication { .. }) => tags::NODE_C_RELATED_APPLICATION,
            None | Some(&Computation::Return(_)) => tags::NODE_C_RETURN,
            Some(&Computation::Lambda(_)) => tags::NODE_C_LAMBDA,
            Some(&Computation::Fixpoint { .. }) => tags::NODE_C_FIXPOINT,
            Some(&Computation::Application(..)) => tags::NODE_C_APPLICATION,
            Some(&Computation::Bind(..)) => tags::NODE_C_BIND,
            Some(&Computation::Force(_)) => tags::NODE_C_FORCE,
            Some(&Computation::Case { .. }) => tags::NODE_C_CASE,
            Some(&Computation::ListFold { .. }) => tags::NODE_C_LIST_FOLD,
            Some(&Computation::ListCase { .. }) => tags::NODE_C_LIST_CASE,
            Some(&Computation::With(..)) => tags::NODE_C_WITH,
            Some(&Computation::Project(..)) => tags::NODE_C_PROJECT,
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
        AnyNode::ValueType(id) => match arena.value_type(id) {
            None => {
                out.put_tag(tags::NODE_VT_PRODUCT);
                out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
            },
            Some(value_type) => match *value_type {
                ValueType::Data {
                    declaration,
                    ref arguments,
                } => {
                    out.put_tag(tags::NODE_VT_DATA);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(declaration))));
                    out.put_uvarint(WireU64::from(WireUsize::from(arguments.len())));
                },
                ValueType::Record(ref fields) => {
                    out.put_tag(tags::NODE_VT_RECORD);
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                    for label in fields.keys() {
                        encode_text(&mut out, ArtifactText::from(label.as_ref()));
                    }
                },
                ValueType::Base(base) => {
                    out.put_tag(tags::NODE_VT_BASE);
                    out.put_tag(base_type_tag(base));
                },
                ValueType::PathUniverse(..) => out.put_tag(tags::NODE_VT_PATH_UNIVERSE),
                ValueType::FlowUniverse(..) => out.put_tag(tags::NODE_VT_FLOW_UNIVERSE),
                ValueType::Path { .. } => out.put_tag(tags::NODE_VT_PATH),
                ValueType::Flow { .. } => out.put_tag(tags::NODE_VT_FLOW),
                ValueType::Bridge { .. } => out.put_tag(tags::NODE_VT_BRIDGE),
                ValueType::Universe {
                    sort: GroundSort::Value,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_UNIVERSE);
                    encode_level(&mut out, level);
                },
                ValueType::Universe {
                    sort: GroundSort::Computation,
                    ref level,
                } => {
                    out.put_tag(tags::NODE_VT_COMPUTATION_UNIVERSE);
                    encode_level(&mut out, level);
                },
                ValueType::Abstract(atom) => {
                    out.put_tag(tags::NODE_VT_ABSTRACT);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
                },
                ValueType::Product(ref components) => {
                    out.put_tag(tags::NODE_VT_PRODUCT);
                    out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
                },
                ValueType::Sigma { .. } => out.put_tag(tags::NODE_VT_SIGMA),
                ValueType::Sum(ref summands) => {
                    out.put_tag(tags::NODE_VT_SUM);
                    out.put_uvarint(WireU64::from(WireUsize::from(summands.len())));
                },
                ValueType::Session { ref graph, .. } => {
                    out.put_tag(tags::NODE_VT_SESSION);
                    graph.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                ValueType::List(_) => out.put_tag(tags::NODE_VT_LIST),
                ValueType::Thunk(_) => out.put_tag(tags::NODE_VT_THUNK),
                ValueType::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_LIFT);
                    encode_level(&mut out, target);
                },
                ValueType::Element { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_ELEMENT);
                    encode_level(&mut out, target);
                },
                ValueType::StaticPi { .. } => out.put_tag(tags::NODE_VT_STATIC_PI),
                // Outside the encoding domain, as an absent id is: interning
                // writes a stage's base in its place.
                ValueType::Staged { .. } => {
                    out.put_tag(tags::NODE_VT_PRODUCT);
                    out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
                },
            },
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            Some(&CompType::Returner(_)) | None => out.put_tag(tags::NODE_CT_RETURNER),
            Some(&CompType::Arrow { .. }) => out.put_tag(tags::NODE_CT_ARROW),
            Some(&CompType::Pi { .. }) => out.put_tag(tags::NODE_CT_PI),
            Some(&CompType::Element { ref target, .. }) => {
                out.put_tag(tags::NODE_CT_ELEMENT);
                encode_level(&mut out, target);
            },
            Some(&CompType::With(ref components)) => {
                out.put_tag(tags::NODE_CT_WITH);
                out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
            },
            Some(&CompType::Codata {
                declaration,
                ref arguments,
            }) => {
                out.put_tag(tags::NODE_CT_CODATA);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(declaration))));
                out.put_uvarint(WireU64::from(WireUsize::from(arguments.len())));
            },
        },
        AnyNode::Value(id) => match arena.value(id) {
            None => {
                out.put_tag(tags::NODE_V_TUPLE);
                out.put_uvarint(WireU64::from(WireUsize::from(0_usize)));
            },
            Some(value) => match *value {
                Value::Constructor {
                    tag, ref fields, ..
                } => {
                    out.put_tag(tags::NODE_V_CONSTRUCTOR);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(tag))));
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                },
                Value::Record(ref fields) => {
                    out.put_tag(tags::NODE_V_RECORD);
                    out.put_uvarint(WireU64::from(WireUsize::from(fields.len())));
                    for label in fields.keys() {
                        encode_text(&mut out, ArtifactText::from(label.as_ref()));
                    }
                },
                Value::Variable(index) => {
                    out.put_tag(tags::NODE_V_VARIABLE);
                    out.put_uvarint(WireU64::from(u64::from(u32::from(index))));
                },
                Value::Constant(index) => {
                    out.put_tag(tags::NODE_V_CONSTANT);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(index))));
                },
                Value::SessionPath { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_SESSION_PATH);
                    evidence.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                Value::SessionFlow { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_SESSION_FLOW);
                    evidence.write(|word| out.put_uvarint(WireU64::from(word.0)));
                },
                Value::Stay { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_STAY);
                    for word in crate::identity::endpoint_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::ForwardFlow { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_FORWARD_FLOW);
                    for word in crate::identity::forward_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::FunctionFlow { .. } => out.put_tag(tags::NODE_V_FUNCTION_FLOW),
                Value::Then { seam, .. } => {
                    out.put_tag(tags::NODE_V_THEN);
                    out.put_tag(seam_tag(seam));
                },
                Value::FlowProduct(..) => out.put_tag(tags::NODE_V_FLOW_PRODUCT),
                Value::PathRefl(_) => out.put_tag(tags::NODE_V_PATH_REFL),
                Value::PathProduct(..) => out.put_tag(tags::NODE_V_PATH_PRODUCT),
                Value::PathEquiv { ref evidence, .. } => {
                    out.put_tag(tags::NODE_V_PATH_EQUIV);
                    for word in evidence.words() {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Univalence { .. } => out.put_tag(tags::NODE_V_UNIVALENCE),
                Value::Here { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_HERE);
                    for word in crate::identity::endpoint_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Returned(_) => out.put_tag(tags::NODE_V_RETURNED),
                Value::Higher { ref program, .. } => {
                    out.put_tag(tags::NODE_V_HIGHER);
                    for word in program.words() {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::HigherEvaluation { ref dialogues, .. } => {
                    out.put_tag(tags::NODE_V_HIGHER_EVALUATION);
                    for word in crate::identity::evaluation_words(dialogues) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::QuantifiedEvaluation { ref steps, .. } => {
                    out.put_tag(tags::NODE_V_QUANTIFIED_EVALUATION);
                    for word in crate::identity::quantified_words(steps) {
                        out.put_uvarint(WireU64::from(word.0));
                    }
                },
                Value::Literal(ref literal) => {
                    out.put_tag(tags::NODE_V_LITERAL);
                    encode_literal(&mut out, literal);
                },
                Value::Tuple(ref components) => {
                    out.put_tag(tags::NODE_V_TUPLE);
                    out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
                },
                Value::ListNil => out.put_tag(tags::NODE_V_LIST_NIL),
                Value::ListCons(..) => out.put_tag(tags::NODE_V_LIST_CONS),
                Value::Injection(summand, _) => {
                    out.put_tag(tags::NODE_V_INJECTION);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(summand))));
                },
                Value::Thunk(_) => out.put_tag(tags::NODE_V_THUNK),
                Value::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_V_LIFT);
                    encode_level(&mut out, target);
                },
                Value::Quote(_) => out.put_tag(tags::NODE_V_QUOTE),
                Value::QuoteComputation(_) => out.put_tag(tags::NODE_V_QUOTE_COMPUTATION),
                Value::StaticApplication(..) => out.put_tag(tags::NODE_V_STATIC_APPLICATION),
            },
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            Some(&Computation::DataCase {
                ref branches,
                equations,
                ..
            }) => {
                if equations == crate::EquationCount::NONE {
                    out.put_tag(tags::NODE_C_DATA_CASE);
                    out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
                }
                else {
                    out.put_tag(tags::NODE_C_INDEXED_DATA_CASE);
                    out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(equations))));
                }
            },
            Some(&Computation::SigmaSplit { .. }) => out.put_tag(tags::NODE_C_SIGMA_SPLIT),
            Some(&Computation::RecordProjection(_, ref label)) => {
                out.put_tag(tags::NODE_C_RECORD_PROJECTION);
                encode_text(&mut out, ArtifactText::from(label.as_ref()));
            },
            Some(&Computation::TupleProjection(_, component)) => {
                out.put_tag(tags::NODE_C_TUPLE_PROJECTION);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(component))));
            },
            Some(&Computation::Transport(..)) => out.put_tag(tags::NODE_C_TRANSPORT),
            Some(&Computation::PathTransport { .. }) => {
                out.put_tag(tags::NODE_C_PATH_TRANSPORT);
            },
            Some(&Computation::TelescopeTransport { .. }) => {
                out.put_tag(tags::NODE_C_TELESCOPE_TRANSPORT);
            },
            Some(&Computation::Ride { .. }) => out.put_tag(tags::NODE_C_RIDE),
            Some(&Computation::TelescopeRide { .. }) => {
                out.put_tag(tags::NODE_C_TELESCOPE_RIDE);
            },
            Some(&Computation::RelatedApplication { .. }) => {
                out.put_tag(tags::NODE_C_RELATED_APPLICATION);
            },
            Some(&Computation::Lambda(_)) => out.put_tag(tags::NODE_C_LAMBDA),
            Some(&Computation::Fixpoint { evidence, .. }) => {
                out.put_tag(tags::NODE_C_FIXPOINT);
                out.put_tag(evidence_tag(evidence));
                if let crate::FixpointEvidence::Staged { position } = evidence {
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(position))));
                }
            },
            Some(&Computation::Application(..)) => out.put_tag(tags::NODE_C_APPLICATION),
            Some(&Computation::Return(_)) | None => out.put_tag(tags::NODE_C_RETURN),
            Some(&Computation::Bind(..)) => out.put_tag(tags::NODE_C_BIND),
            Some(&Computation::Force(_)) => out.put_tag(tags::NODE_C_FORCE),
            Some(&Computation::Case { ref branches, .. }) => {
                out.put_tag(tags::NODE_C_CASE);
                out.put_uvarint(WireU64::from(WireUsize::from(branches.len())));
            },
            Some(&Computation::ListFold { .. }) => out.put_tag(tags::NODE_C_LIST_FOLD),
            Some(&Computation::ListCase { .. }) => out.put_tag(tags::NODE_C_LIST_CASE),
            Some(&Computation::With(ref components)) => {
                out.put_tag(tags::NODE_C_WITH);
                out.put_uvarint(WireU64::from(WireUsize::from(components.len())));
            },
            Some(&Computation::Project(component, _)) => {
                out.put_tag(tags::NODE_C_PROJECT);
                out.put_uvarint(WireU64::from(WireUsize::from(usize::from(component))));
            },
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
            ConstraintRelation::Leq => tags::RELATION_LEQ,
            ConstraintRelation::Eq => tags::RELATION_EQ,
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
        Literal::Integer(ref integer) => {
            out.put_tag(tags::LITERAL_INTEGER);
            out.put_tag(sign_tag(integer.sign()));
            let digits = integer.magnitude().to_digits();
            encode_text(out, ArtifactText::from(digits.as_str()));
        },
        Literal::Text(ref text) => {
            out.put_tag(tags::LITERAL_TEXT);
            let content = text.to_content();
            encode_text(out, ArtifactText::from(content.as_str()));
        },
        Literal::Numeric(ref numeric) => {
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
        BaseType::Integer => tags::BASE_INTEGER,
        BaseType::String => tags::BASE_STRING,
        BaseType::Numeric => tags::BASE_NUMERIC,
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
        Sign::NonNegative => tags::SIGN_NON_NEGATIVE,
        Sign::Negative => tags::SIGN_NEGATIVE,
    }
}

/// The wire tag of a fixpoint's termination claim.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each claim to its frozen tag; a staged claim's position
///   follows the tag at the write site.
/// - provides: the total claim-to-tag map, so a claim's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes the literal entry bytes of a fixpoint under each
///   claim; a swapped or dropped claim byte changes the golden.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match evidence {
        crate::FixpointEvidence::Partial => tags::FIXPOINT_PARTIAL,
        crate::FixpointEvidence::StructuralDescent => tags::FIXPOINT_STRUCTURAL_DESCENT,
        crate::FixpointEvidence::Staged { .. } => tags::FIXPOINT_STAGED,
    },
)]
#[inline]
fn evidence_tag(evidence: crate::FixpointEvidence) -> WireTag
{
    match evidence {
        crate::FixpointEvidence::Partial => tags::FIXPOINT_PARTIAL,
        crate::FixpointEvidence::StructuralDescent => tags::FIXPOINT_STRUCTURAL_DESCENT,
        crate::FixpointEvidence::Staged { .. } => tags::FIXPOINT_STAGED,
    }
}

/// The wire tag of a composition's seam.
///
/// # Specification
/// - requires: nothing.
/// - ensures: maps each seam to its frozen tag.
/// - provides: the total seam-to-tag map, so a seam's byte is decided in one
///   place rather than at each write site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 observes the literal entry bytes of a composition under
///   each seam; a swapped or dropped seam byte changes the golden.
/// - witness: `encode::tests::entry_goldens_pin_every_former_and_child_position`
#[spec(
    ensures: |ret| ret == match seam {
        crate::Seam::Sequence => tags::SEAM_SEQUENCE,
        crate::Seam::Feedback => tags::SEAM_FEEDBACK,
    },
)]
#[inline]
fn seam_tag(seam: crate::Seam) -> WireTag
{
    match seam {
        crate::Seam::Sequence => tags::SEAM_SEQUENCE,
        crate::Seam::Feedback => tags::SEAM_FEEDBACK,
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
    use crate::term::Summand;
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
        let mut expected: Vec<u8> = Vec::new();
        for &(ref text, length) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_text(&mut out, ArtifactText::from(text.as_str()));
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
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
        let mut expected: Vec<u8> = Vec::new();
        for &(ref literal, bytes) in cases {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_literal(&mut out, literal);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
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
        let mut expected: Vec<u8> = Vec::new();
        for &(ref level, bytes) in levels {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level(&mut out, level);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
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
        let mut expected: Vec<u8> = Vec::new();
        for &(ref signature, bytes) in signatures {
            let mut out = EncodedArtifact::new();
            out.put_image(ArtifactImage::from([0xde_u8, 0xad].as_slice()));
            super::encode_level_signature(&mut out, signature);
            expected.clear();
            expected.extend_from_slice(&[0xde, 0xad]);
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
            (AnyNode::ValueType(arena.value_type_unit()), &[], &[0x03, 0]),
            (AnyNode::ValueType(arena.value_type_empty()), &[], &[
                0x04, 0,
            ]),
            (
                AnyNode::ValueType(arena.value_type_universe(GroundSort::Value, level.clone())),
                &[],
                &[0x02, 7, 0],
            ),
            (
                AnyNode::ValueType(arena.value_type_product(&[t0, t1])),
                &[first, second],
                &[0x03, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_sum(&[t0, t1, t0])),
                &[first, second, third],
                &[0x04, 3, 3, 0x81, 1, 0x80, 0x80, 1],
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
            (AnyNode::Value(arena.value_unit()), &[], &[0x0d, 0]),
            (
                AnyNode::Value(
                    arena.value_literal(Literal::Text(StringLiteral::new(String::from("é")))),
                ),
                &[],
                &[0x0c, 1, 2, 0xc3, 0xa9],
            ),
            (
                AnyNode::Value(arena.value_tuple(&[v0, v1])),
                &[first, second],
                &[0x0d, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_injection(Summand::from(0_usize), v0)),
                &[first],
                &[0x0e, 0, 3],
            ),
            (
                AnyNode::Value(arena.value_injection(Summand::from(129_usize), v0)),
                &[first],
                &[0x0e, 0x81, 1, 3],
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
                AnyNode::Computation(
                    arena.computation_fixpoint(c0, crate::FixpointEvidence::Partial),
                ),
                &[first],
                &[0x63, 0, 3],
            ),
            (
                AnyNode::Computation(
                    arena.computation_fixpoint(c0, crate::FixpointEvidence::StructuralDescent),
                ),
                &[first],
                &[0x63, 1, 3],
            ),
            (
                AnyNode::Computation(arena.computation_fixpoint(
                    c0,
                    crate::FixpointEvidence::Staged {
                        position: crate::StagedPosition::from(129_usize),
                    },
                )),
                &[first],
                &[0x63, 2, 0x81, 1, 3],
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
                AnyNode::Computation(arena.computation_case(v0, &[c0, c1])),
                &[first, second, third],
                &[0x16, 2, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Computation(arena.computation_case(v0, &[])),
                &[first],
                &[0x16, 0, 3],
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
            (
                AnyNode::CompType(arena.comp_type_with(&[k0, k1])),
                &[first, second],
                &[0x65, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_with(&[c0, c1])),
                &[first, second],
                &[0x66, 2, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(
                    arena.computation_project(crate::Component::from(0_usize), c0),
                ),
                &[second],
                &[0x67, 0, 0x81, 1],
            ),
            (
                AnyNode::Computation(
                    arena.computation_project(crate::Component::from(1_usize), c0),
                ),
                &[second],
                &[0x67, 1, 0x81, 1],
            ),
            (
                AnyNode::ValueType(arena.value_type_flow(t0, v0, v1)),
                &[first, second, third],
                &[0x4A, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (AnyNode::Value(arena.value_stay(v0)), &[first], &[
                0x4B, 0, 0, 3,
            ]),
            (
                AnyNode::Value(arena.value_forward_flow(
                    t0,
                    v0,
                    [v1].into(),
                    alloc::sync::Arc::from([Vec::new()]),
                )),
                &[first, second, third],
                &[0x4C, 1, 0, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Value(arena.value_function_flow(t0, v0, v1)),
                &[first, second, third],
                &[0x4D, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Value(arena.value_then(v0, v1, crate::Seam::Sequence)),
                &[first, second],
                &[0x4E, 0, 3, 0x81, 1],
            ),
            (
                AnyNode::Value(arena.value_then(v0, v1, crate::Seam::Feedback)),
                &[first, second],
                &[0x4E, 1, 3, 0x81, 1],
            ),
            (
                AnyNode::Computation(arena.computation_ride(t0, v0, v1)),
                &[first, second, third],
                &[0x4F, 3, 0x81, 1, 0x80, 0x80, 1],
            ),
            (
                AnyNode::Computation(arena.computation_telescope_ride(k0, v0, v1, v0, v1)),
                &[first, second, third, first, second],
                &[0x68, 3, 0x81, 1, 0x80, 0x80, 1, 3, 0x81, 1],
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
        let first_pair = arena.value_tuple(&[first_unit, variable]);
        let equal_pair = arena.value_tuple(&[second_unit, variable]);
        let reversed = arena.value_tuple(&[variable, first_unit]);
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
        let expected: &[&[u8]] = &[&[0x09, 0x80, 0x80, 1], &[0x0d, 2, 0, 1]];
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
            [0x0d, 2, 1, 0]
        );
        assert_eq!(interner.next, GlobalIndex::from(4_u32));
        assert_eq!(interner.by_content.len(), 4);
        assert_eq!(interner.by_node.len(), 6);
        assert_eq!(first_segment, prefix);
    }

    #[test]
    fn a_staged_type_is_written_as_its_base()
    {
        let mut arena = TermArena::new();
        let integer = arena.value_type_base(crate::BaseType::Integer);
        let staged =
            arena.value_type_staged(integer, crate::Stage::At(crate::StageId::from(0_usize)));
        let plain_list = arena.value_type_list(integer);
        let staged_list = arena.value_type_list(staged);
        let mut interner = super::Interner::new();
        let mut segment = Vec::new();
        let plain = super::intern(
            &arena,
            &mut interner,
            &mut segment,
            AnyNode::ValueType(plain_list),
        );
        let written = segment.clone();
        assert_eq!(
            super::intern(
                &arena,
                &mut interner,
                &mut segment,
                AnyNode::ValueType(staged_list)
            ),
            plain,
            "a list of a staged type is the list of its base on the wire"
        );
        assert_eq!(segment, written, "a stage writes no entry");
        assert_eq!(
            interner.by_node.get(&AnyNode::ValueType(staged)),
            interner.by_node.get(&AnyNode::ValueType(integer))
        );
    }

    #[test]
    fn declaration_sequences_match_literal_segment_fixtures()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let atom = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
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
        // The atom is open, so it is written closed after the two declarations
        // that follow it; its segment carries the universe and the integer
        // representation as entries, then its kind root, its representation
        // root and that extent.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 1, 0, 3, 0, 2, 0, 0, 0, 2, 0x02, 0, 0, 0x00, 0x00, 0, 1,
            2, 1, 0, 2, 1, b'a', 2, 0xc3, 0xa9, 0, 0, 2, 0x17, 0, 0x1c, 2, 0, 3, 0, 0, 0, 0, 0, 1,
            0, 0, 0, 0, 2,
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
    fn a_relating_definition_closes_its_segment_with_its_pairs()
    {
        use gandr_kernel_conversion_trace::ConversionDecision;
        use gandr_kernel_conversion_trace::ConversionSide;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let wrapped = builder.arena().value_tuple(&[unit]);
        let related = alloc::vec![crate::decl::RelatedEndpoints {
            left: unit,
            right: wrapped,
            dialogue: alloc::vec![
                ConversionDecision::Decompose,
                ConversionDecision::ReturnEta {
                    side: ConversionSide::Right,
                }
            ],
        }];
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .relating(related.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The relating kind, then the plain definition's fields: the unit type,
        // the unit and the wrapped unit as entries, the declared and body roots
        // and the four empty slots; then one pair, its two roots and its two
        // decision words.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 7, 0, 0, 0, 3, 0x03, 0, 0x0D, 0, 0x0D, 1, 1, 0,
            1, 0, 0, 0, 0, 1, 1, 2, 2, 0x0B, 0x0E,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().related().len(), 1);
        assert_eq!(
            declaration
                .declaration()
                .related()
                .first()
                .map(|pair| pair.dialogue.clone()),
            related.first().map(|pair| pair.dialogue.clone())
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A relating kind closing with no pair decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 7, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 0, 0, 0,
            0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // A word outside the decision alphabet is refused as path evidence.
        let mut unknown = expected;
        if let Some(word) = unknown.last_mut() {
            *word = 0x7F;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::PathEvidence,
            })
        );
        // The plain kind over the same bytes leaves the pair unread.
        let mut plain = expected;
        if let Some(kind) = plain.get_mut(9) {
            *kind = 0;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_lawful_definition_closes_its_segment_with_its_laws()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let laws = alloc::vec![ConstantIndex::from(5_usize), ConstantIndex::from(2_usize)];
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .lawful(laws.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The lawful kind, then the plain definition's fields: the unit type
        // and the unit as entries, the declared and body roots and the four
        // empty slots; then no related pair, and the two laws in written order.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 9, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 0, 0, 0,
            0, 0, 2, 5, 2,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().laws(), laws.as_slice());
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A lawful kind closing with no law decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 9, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 0, 0, 0,
            0, 0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // The relating kind over the same bytes reads the pair count and leaves
        // the laws unread.
        let mut relating = expected;
        if let Some(kind) = relating.get_mut(9) {
            *kind = 7;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(relating.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_stage_signature_fills_the_erasure_slot()
    {
        use crate::stage_signature::PlacedChild;
        use crate::stage_signature::StageBinder;
        use crate::stage_signature::StageBound;
        use crate::stage_signature::StageMark;
        use crate::stage_signature::StageReach;
        use crate::stage_signature::StageSignature;
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        let stages = StageSignature::new(
            alloc::vec![
                StageBound::Unbounded,
                StageBound::Below(StageBinder::from(0_usize))
            ],
            alloc::vec![
                StageMark::new(
                    alloc::vec![PlacedChild::from(0_usize), PlacedChild::from(1_usize)],
                    StageBinder::from(0_usize),
                    StageReach::Below(crate::term::StageDepth::ONE),
                ),
                StageMark::new(
                    alloc::vec![PlacedChild::from(1_usize)],
                    StageBinder::from(1_usize),
                    StageReach::At,
                ),
            ],
        );
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .staged(stages.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The plain definition's fields up to its body root; then the erasure
        // slot: two binders, the second below the first, and two marks, each
        // its binder, its depth and its path; then the three other slots.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 2, 0, 1,
            2, 0, 1, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(declaration.declaration().stages(), &stages);
        // A signature binding nothing writes the empty slot.
        let plain =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), unit_type, unit);
        let plain = super::encode(&arena, &[MarkedDeclaration::new(
            AdmissionMark::Checked,
            plain,
        )]);
        assert_eq!(
            plain.as_image().as_ref().get(20 ..),
            Some(&[0_u8, 0, 0, 0][..])
        );
        // A bound naming no earlier binder, and a mark naming a binder the
        // signature does not bind, are refused at the slot.
        let malformed = Err(crate::error::DecodeError::Malformed {
            site: crate::error::MalformedSite::StageSignature,
        });
        for slot in [&[1_u8, 1][..], &[1_u8, 0, 1, 1, 0, 0][..]] {
            let mut forged = expected.get(.. 20).unwrap_or_default().to_vec();
            forged.extend_from_slice(slot);
            forged.extend_from_slice(&[0, 0, 0]);
            assert_eq!(
                crate::decode::decode(ArtifactImage::from(forged.as_slice())).map(|_| ()),
                malformed
            );
        }
    }

    #[test]
    fn a_ruled_definition_closes_its_segment_with_its_rules()
    {
        use crate::operation_rules::OperationNode;
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let unit_type = builder.arena().value_type_unit();
        let unit = builder.arena().value_unit();
        // `f(x) ==> S(x)`, f at position 0 and S constructor 1 of the data
        // declaration at position 3.
        let rules = crate::operation_rules::OperationRules::new(alloc::vec![
            crate::operation_rules::OperationRule::new(
                alloc::boxed::Box::from([
                    OperationNode::Operation {
                        constant: ConstantIndex::from(0_usize),
                        arity: crate::presented::FieldCount::from(1_usize),
                    },
                    OperationNode::Variable(crate::presented::RuleVariable::from(0_u32)),
                ]),
                alloc::boxed::Box::from([
                    OperationNode::Constructor {
                        family: ConstantIndex::from(3_usize),
                        tag: crate::term::ConstructorTag::from(1_usize),
                    },
                    OperationNode::Results(crate::presented::FieldCount::from(4_usize)),
                ]),
            ),
        ]);
        let definition = builder
            .def(LevelSignature::monomorphic(), unit_type, unit)
            .ruled(rules.clone());
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, definition)];
        // The ruled kind, then the plain definition's fields; then no related
        // pair, no law, and the one rule: its left side, an operation at 0 of
        // arity 1 and variable 0, and its right side, constructor 1 of the
        // declaration at 3 and a results tuple of 4.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 0x0E, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 0, 0,
            0, 0, 0, 0, 1, 2, 2, 0, 1, 1, 0, 2, 0, 3, 1, 3, 4,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(
            bytes.as_image().as_ref(),
            expected,
            "the ruled segment's literal bytes"
        );
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded.declarations().first().expect("one definition");
        assert_eq!(
            declaration.declaration().operation_rules(),
            &rules,
            "the rules decode in written order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected,
            "and re-encode to the same bytes"
        );
        // A ruled kind closing with no rule decodes to a plain definition,
        // whose canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 0x0E, 0, 0, 0, 2, 0x03, 0, 0x0D, 0, 0, 1, 0, 0,
            0, 0, 0, 0, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            }),
            "an empty rule block is not canonical"
        );
        // A node tag outside the alphabet refuses at its own site.
        let mut unknown = expected;
        if let Some(tag) = unknown.get_mut(28) {
            *tag = 9;
        }
        assert!(
            matches!(
                crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
                Err(crate::error::DecodeError::UnknownTag {
                    site: crate::error::TagSite::RuleNode,
                    ..
                })
            ),
            "an unknown rule node tag is refused"
        );
    }

    #[test]
    fn a_codata_declaration_closes_its_segment_with_its_observations()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Computation, Level::zero());
        let parameter = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        // `Stream(a)`: `head : F Integer` and `tail : Stream(a)`.
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let head = builder.arena().comp_type_returner(integer);
        let own = builder.arena().value_variable(DeBruijnIndex::from(0_u32));
        let tail = builder
            .arena()
            .comp_type_codata(ConstantIndex::from(0_usize), alloc::vec![own]);
        let codata = builder.codata(
            LevelSignature::monomorphic(),
            alloc::vec![parameter],
            alloc::vec![head, tail],
            kind,
        );
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, codata)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        // The kind follows the header, the empty atom table and the admission
        // mark.
        let kind_at = 9;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_CODATA))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("a codata declaration decodes");
        let declaration = decoded.declarations().first().expect("one codata");
        let crate::decl::DeclarationContent::Codata {
            ref parameters,
            ref observations,
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the declaration decodes as codata");
        };
        assert_eq!(parameters.len(), 1);
        let read = |at: usize| {
            let id = observations.get(at)?;
            decoded.arena().comp_type(*id)
        };
        assert!(
            matches!(read(0), Some(&crate::types::CompType::Returner(_)))
                && matches!(
                    read(1),
                    Some(&crate::types::CompType::Codata { declaration, ref arguments })
                        if usize::from(declaration) == 0 && arguments.len() == 1
                ),
            "the observations are read back in order, the second naming the declaration"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The data kind over the same bytes reads the observation roots as a
        // constructor's fields, and refuses them as computation types.
        let mut plain = image.as_ref().to_vec();
        if let Some(kind) = plain.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_DATA);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::Polarity,
            })
        );
    }

    #[test]
    fn a_presented_data_declaration_closes_its_segment_with_its_rules()
    {
        use crate::presented::Presentation;
        use crate::presented::PresentedRule;
        use crate::presented::RuleNode;
        use crate::presented::RuleVariable;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = builder
            .arena()
            .value_type_data(crate::ConstantIndex::from(0_usize), alloc::vec![]);
        let tag = |ordinal: usize| RuleNode::Constructor(crate::ConstructorTag::from(ordinal));
        let variable = RuleNode::Variable(RuleVariable::from(0_u32));
        // The circle: `base`, `loop(x)`, `unloop(x)`, with
        // `loop(unloop(x)) ==> x` and `unloop(loop(x)) ==> x`.
        let rules = alloc::vec![
            PresentedRule::new(
                alloc::vec![tag(1), tag(2), variable].into(),
                alloc::vec![variable].into()
            ),
            PresentedRule::new(
                alloc::vec![tag(2), tag(1), variable].into(),
                alloc::vec![variable].into()
            ),
        ];
        let data = builder
            .data(
                LevelSignature::monomorphic(),
                alloc::vec![],
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(Presentation::new(rules.clone()));
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        // The presented kind, then the plain data declaration's fields: the
        // universe and the circle's own type as entries, the declared root, no
        // parameter, three constructors of arity zero, one and one; then two
        // rules, each two sides of a node count and tagged nodes.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 8, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 0, 0, 0, 0, 3,
            0, 1, 1, 1, 1, 2, 3, 0, 1, 0, 2, 1, 0, 1, 1, 0, 3, 0, 2, 0, 1, 1, 0, 1, 1, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(declaration.declaration().presentation().rules(), rules);
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // A presented kind closing with no rule decodes to a free type, whose
        // canonical bytes carry the plain kind.
        let empty = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 8, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 0, 0, 0, 0, 3,
            0, 1, 1, 1, 1, 0,
        ];
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(empty.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::NonCanonical,
            })
        );
        // A node tag outside the constructor and variable alphabet is refused
        // at the rule-node site.
        let mut unknown = expected;
        if let Some(node) = unknown.get_mut(32) {
            *node = 2;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(unknown.as_slice())),
            Err(crate::error::DecodeError::UnknownTag {
                site: crate::error::TagSite::RuleNode,
                tag: crate::WireTag::from(2_u8),
            })
        );
        // The plain kind over the same bytes leaves the rules unread.
        let mut plain = expected;
        if let Some(kind) = plain.get_mut(9) {
            *kind = 6;
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_type_of_words_closes_its_segment_with_its_cells()
    {
        use crate::presented::FreeCell;
        use crate::presented::FreeCells;
        use crate::presented::Presentation;
        use crate::presented::RuleNode;

        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = builder
            .arena()
            .value_type_data(crate::ConstantIndex::from(0_usize), alloc::vec![]);
        let base = || {
            alloc::boxed::Box::from([RuleNode::Constructor(crate::ConstructorTag::from(0_usize))])
        };
        let cells = FreeCells::new(crate::ConstantIndex::from(0_usize), alloc::vec![
            FreeCell::new(base(), base())
        ]);
        let data = builder
            .data(
                LevelSignature::monomorphic(),
                alloc::vec![],
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(Presentation::words(cells.clone()));
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        // The words kind, then the presented declaration's fields as the
        // circle writes them; then the sort's position, one cell, and its two
        // endpoints, each the one constructor `base`.
        let expected = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 10, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 0, 0, 0, 0, 3,
            0, 1, 1, 1, 1, 2, 3, 0, 1, 0, 2, 1, 0, 1, 1, 0, 3, 0, 2, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1,
            0, 0, 1, 0, 0,
        ];
        let bytes = super::encode(&arena, &declarations);
        assert_eq!(bytes.as_image().as_ref(), expected);
        let decoded = crate::decode::decode(ArtifactImage::from(expected.as_slice()))
            .expect("the literal artifact is structurally admissible");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert_eq!(
            declaration.declaration().presentation(),
            &Presentation::words(cells.clone())
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            expected
        );
        // Words whose rules were dropped still decode, to be refused by the
        // kernel against the mint, and keep their canonical bytes.
        let dropped = [
            b'G', b'K', b'X', b'1', 7, 0, 0, 1, 0, 10, 0, 0, 0, 2, 0x02, 0, 0, 0x5D, 0, 0, 0, 0, 3,
            0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0,
        ];
        let decoded = crate::decode::decode(ArtifactImage::from(dropped.as_slice()))
            .expect("a rule count of none decodes under the words kind");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        assert!(declaration.declaration().presentation().rules().is_empty());
        assert_eq!(
            declaration.declaration().presentation().cells(),
            Some(&cells)
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            dropped
        );
    }

    #[test]
    fn an_interfaced_atom_closes_its_segment_with_its_interface()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let relation = builder.arena().value_unit();
        let reflexivity = builder.arena().value_tuple(&[relation]);
        let interface = crate::decl::AtomInterface::new(relation, reflexivity);
        let atom = builder
            .abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                super::SealScope::Open,
            )
            .interfaced(interface);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, atom)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        // The kind follows the header, the one-entry atom table and the
        // admission mark.
        let kind_at = 10;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_ABSTRACT_INTERFACED))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("an interfaced atom decodes");
        let declaration = decoded.declarations().first().expect("one atom");
        let crate::decl::DeclarationContent::AbstractType {
            interface: super::Maybe::Present(read),
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the atom decodes with its interface");
        };
        let arity = |value| {
            decoded
                .arena()
                .value(value)
                .and_then(crate::term::Value::components)
                .map(<[_]>::len)
        };
        assert_eq!(
            (arity(read.relation()), arity(read.reflexivity())),
            (Some(0), Some(1)),
            "the relation and the reflexivity are read back in order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The plain kind over the same bytes leaves the interface unread.
        let mut plain = image.as_ref().to_vec();
        if let Some(kind) = plain.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_ABSTRACT_TYPE);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn a_lawful_atom_closes_its_segment_with_its_law()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let relation = builder.arena().value_unit();
        let reflexivity = builder.arena().value_tuple(&[relation]);
        let law = builder.arena().value_tuple(&[relation, reflexivity]);
        let interface = crate::decl::AtomInterface::new(relation, reflexivity).lawful(law);
        let atom = builder
            .abstract_type(
                LevelSignature::monomorphic(),
                kind,
                integer,
                super::SealScope::Open,
            )
            .interfaced(interface);
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, atom)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        let kind_at = 10;
        assert_eq!(
            image.as_ref().get(kind_at).copied(),
            Some(u8::from(crate::tags::KIND_ABSTRACT_LAWFUL))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("a lawful atom decodes");
        let declaration = decoded.declarations().first().expect("one atom");
        let crate::decl::DeclarationContent::AbstractType {
            interface: super::Maybe::Present(read),
            ..
        } = *declaration.declaration().content()
        else {
            panic!("the atom decodes with its interface");
        };
        let arity = |value| {
            decoded
                .arena()
                .value(value)
                .and_then(crate::term::Value::components)
                .map(<[_]>::len)
        };
        let super::Maybe::Present(read_law) = read.law()
        else {
            panic!("the atom decodes with its law");
        };
        assert_eq!(
            (
                arity(read.relation()),
                arity(read.reflexivity()),
                arity(read_law)
            ),
            (Some(0), Some(1), Some(2)),
            "the relation, the reflexivity and the law are read back in order"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The interfaced kind over the same bytes leaves the law unread.
        let mut lawless = image.as_ref().to_vec();
        if let Some(kind) = lawless.get_mut(kind_at) {
            *kind = u8::from(crate::tags::KIND_ABSTRACT_INTERFACED);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(lawless.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
        );
    }

    #[test]
    fn an_indexed_data_declaration_closes_its_segment_with_its_indices()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let kind = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let index = builder.arena().value_type_unit();
        let at = builder.arena().value_unit();
        let data = builder.indexed(
            LevelSignature::monomorphic(),
            alloc::vec![],
            (alloc::vec![index], alloc::vec![alloc::vec![]], alloc::vec![
                alloc::vec![at]
            ]),
            kind,
        );
        let declarations = [MarkedDeclaration::new(AdmissionMark::Checked, data)];
        let bytes = super::encode(&arena, &declarations);
        let image = bytes.as_image();
        assert_eq!(
            image.as_ref().get(9).copied(),
            Some(u8::from(crate::tags::KIND_DATA_INDEXED))
        );
        let decoded = crate::decode::decode(ArtifactImage::from(image.as_ref()))
            .expect("an indexed declaration decodes");
        let declaration = decoded
            .declarations()
            .first()
            .expect("one data declaration");
        let crate::decl::DeclarationContent::Data {
            ref indices,
            ref results,
            ..
        } = *declaration.declaration().content()
        else {
            panic!("a data declaration decodes as data");
        };
        assert_eq!(indices.len(), 1, "the index classifier is read back");
        assert_eq!(
            results.iter().map(Vec::len).collect::<Vec<_>>(),
            [1],
            "the constructor's result index is read back"
        );
        assert_eq!(
            super::encode(decoded.arena(), decoded.declarations())
                .as_image()
                .as_ref(),
            image.as_ref()
        );
        // The plain kind over the same bytes leaves the indices unread.
        let mut plain = image.as_ref().to_vec();
        if let Some(kind) = plain.get_mut(9) {
            *kind = u8::from(crate::tags::KIND_DATA);
        }
        assert_eq!(
            crate::decode::decode(ArtifactImage::from(plain.as_slice())),
            Err(crate::error::DecodeError::Malformed {
                site: crate::error::MalformedSite::TrailingBytes,
            })
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
                    builder.abstract_type(
                        LevelSignature::monomorphic(),
                        kind,
                        declared,
                        super::SealScope::Open,
                    )
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

    #[test]
    fn an_encoding_resumed_after_its_prefix_writes_the_whole_encoding_776()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let atom = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Closed(super::SealExtent::from(2_usize)),
        );
        let mut builder = DeclarationBuilder::new(&mut arena);
        let abstract_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let quote = builder.arena().value_quote(abstract_type);
        let definition = builder
            .def(LevelSignature::monomorphic(), universe, quote)
            .named(StructuredName::from(alloc::vec![
                NameSegment::from_text(String::from("a")).expect("segment"),
            ]));
        let axiom =
            DeclarationBuilder::new(&mut arena).axiom(LevelSignature::monomorphic(), abstract_type);
        let leading = [
            MarkedDeclaration::new(AdmissionMark::Checked, atom),
            MarkedDeclaration::new(AdmissionMark::UncheckedBypass, definition),
            MarkedDeclaration::new(AdmissionMark::Checked, axiom),
        ];
        let prefixes: Vec<_> = (0 ..= leading.len())
            .map(|split| {
                match super::encode_prefix(&arena, leading.get(.. split).expect("a split")) {
                    super::Maybe::Present(prefix) => prefix,
                    super::Maybe::Absent(absent) => panic!("no seal is open: {absent:?}"),
                }
            })
            .collect();
        // Built after the prefixes were encoded, as an editor's admission
        // builds a document's declarations after its closure's: one body is
        // the leading definition's own node, one is built anew to the same
        // content, and the last atom's seal is open to the end.
        let shared =
            DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), universe, quote);
        let mut builder = DeclarationBuilder::new(&mut arena);
        let rebuilt_type = builder
            .arena()
            .value_type_abstract(ConstantIndex::from(0_usize));
        let rebuilt = builder.arena().value_quote(rebuilt_type);
        let anew = builder.def(LevelSignature::monomorphic(), universe, rebuilt);
        let open = DeclarationBuilder::new(&mut arena).abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
        let whole: Vec<_> = leading
            .iter()
            .cloned()
            .chain([
                MarkedDeclaration::new(AdmissionMark::Checked, shared),
                MarkedDeclaration::new(AdmissionMark::Checked, anew),
                MarkedDeclaration::new(AdmissionMark::Checked, open),
            ])
            .collect();
        let expected = super::encode(&arena, &whole);
        for prefix in &prefixes {
            let end = usize::from(prefix.end());
            assert_eq!(
                super::encode_after(prefix, &arena, whole.get(end ..).expect("a split")),
                expected,
                "resumed after {end} declarations"
            );
        }
    }

    #[test]
    fn a_prefix_with_an_open_seal_is_not_encoded_776()
    {
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let universe = builder
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let integer = builder.arena().value_type_base(BaseType::Integer);
        let open = builder.abstract_type(
            LevelSignature::monomorphic(),
            universe,
            integer,
            super::SealScope::Open,
        );
        let leading = [MarkedDeclaration::new(AdmissionMark::Checked, open)];
        assert!(matches!(
            super::encode_prefix(&arena, &leading),
            super::Maybe::Absent(super::encoded_prefix::Absent::OpenSeal)
        ));
    }
}
