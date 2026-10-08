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
//! key is shallow, so interning is amortized constant time and the whole pass
//! is linear in the node count.
//!
//! Deduplication is content-keyed and **never id-keyed**, and the reason is a
//! canonicality property rather than a performance one: an id-keyed
//! deduplication would make the bytes depend on decode history, and the bytes
//! must be a function of the abstract environment alone.
//!
//! The first completion of a node assigns the next free global index and
//! appends its entry to the *current* declaration's segment; a later occurrence
//! reuses the index without appending. That is **post-order first-completion
//! order**, which is the only order consistent with children being referenced
//! by strictly earlier index — a preorder emits a parent before its children
//! and cannot satisfy it — and it is what makes the table streaming-decodable
//! and its index assignment unique.
//!
//! # The walk is sharing-aware, and that is load-bearing twice
//!
//! An arena node is visited once, memoized by id, so re-encoding a decoded DAG
//! costs the number of entries rather than the expanded size. That matters for
//! the encoder's own cost, and it matters more for the decoder, which uses this
//! encoder as its canonical-form oracle: **a re-encoder that walked the graph
//! as a tree would itself be an amplification vector**, turning the defence
//! into the vulnerability.
//!
//! # The encoder is untrusted
//!
//! It feeds no judgement and is not a trusted fast path. The decoder's
//! whole-artifact re-encode-compare is what enforces canonical form, so a buggy
//! or malicious encoder is caught rather than believed — which is how a
//! linear-time optimization stays outside the trusted base entirely.

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
use crate::tags;
use crate::term::Computation;
use crate::term::ConstantIndex;
use crate::term::Side;
use crate::term::Value;
use crate::types::CompType;
use crate::types::ValueType;
use crate::wire::ArtifactImage;
use crate::wire::ArtifactText;
use crate::wire::EncodedArtifact;
use crate::wire::WireTag;
use crate::wire::WireU64;
use crate::wire::WireUsize;

/// The canonical bytes of one encoded subterm-table entry, which are also its
/// deduplication key.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct EncodedEntry(EncodedArtifact);

/// The content-keyed subterm interner, carrying the global index counter and
/// both memos across declaration segments.
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
/// - requires: `declarations` is in admission order and every content root
///   resolves in `arena`. A dangling root is admissible input and encodes as
///   the unit of its family, which is the fail-safe reading rather than a
///   failure mode a caller could act on.
/// - ensures: the bytes carry the magic, the format version, the minted-atom
///   table, the declaration count, and one maximal-sharing segment per
///   declaration; two runs over *abstract* environments that agree — regardless
///   of how the two arenas happen to share in memory — produce byte-identical
///   images.
/// - provides: the canonical byte image, and the canonical-form oracle the
///   decoder compares against. The clause checks the magic and the
///   format-version prefix. The minted-atom table, the declaration count, the
///   per-declaration segments and the determinism of two runs stay prose:
///   reading them back would replay the decoder, and determinism relates two
///   calls rather than one.
/// - fails: never — encoding is total.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the round-trip differential pins that every artifact
///   decodes to what it encoded with its sharing retained, and the determinism
///   differential pins that two differently shared spellings of one abstract
///   environment write identically; the L3 residues are the empty sequence and
///   the bypass admission mark, asserted as exact byte images.
/// - witness: `sharing_format::sharing_format::sharing_round_trips_with_sharing_at_the_shared_nodes`
/// - witness: `sharing_format::sharing_format::differently_shared_equal_inputs_write_identical_bytes`
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `sharing_format::sharing_format::a_bypass_admission_mark_survives_the_round_trip`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret.as_image().as_ref().starts_with(tags::MAGIC.as_slice())
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
/// - requires: `interner` carries the index assignment of every earlier
///   segment, since the table's index space runs across segments and
///   cross-declaration sharing lives there. A dangling content root is
///   admissible input.
/// - ensures: the segment carries only the entries this declaration first
///   completes, in post-order first-completion order, with children referenced
///   by strictly earlier global index; an axiom and an abstract type write one
///   root and no per-definition annotation slots, a definition writes two roots
///   and four slots of which the sealing-provenance one is live.
/// - provides: the per-declaration step of the canonical byte image. This
///   segment contract stays prose: the entries and the root references reach
///   `out` as bytes, so checking their order, their strictly-earlier child
///   references or the slot count would replay the decoder over a segment the
///   encoder exposes no independent view of.
/// - fails: never — encoding is total.
/// - panics: none.
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
    // The structured name: reserved, and written as zero segments.
    out.put_uvarint(WireU64::from(0_u64));
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

/// Write the sealing-provenance slot: a count followed by admission positions.
///
/// A declaration no projection touched writes a zero count, which is
/// byte-identical to what the slot carried while it was reserved — so filling
/// the slot moved no other field and invalidated no artifact.
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
/// - requires: nothing — a dangling root is admissible and interns as the unit
///   of its family.
/// - ensures: every node reachable from `root` has a global index; entries
///   first completed here are appended to `segment` in post-order
///   first-completion order; the root's global index is returned.
/// - provides: the maximal-sharing intern of one declaration root. The clause
///   checks the returned index against the memo. Reachability and post-order
///   first-completion stay prose: both would need an allocating traversal of
///   the sub-DAG, paid once per root.
/// - fails: never.
/// - panics: none.
/// - intension: the walk is a resumable-frame post-order over an explicit heap
///   stack, never host recursion, so it is total on any term depth; each arena
///   node is scheduled at most once, so the cost is linear in reachable nodes
///   and edges rather than in expanded size.
#[spec(ensures: |ret| interner.by_node.get(&root) == Some(&ret))]
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
/// A dangling id encodes as the unit of its family, which is the fail-safe
/// reading: an encoder cannot report an error, so it must not invent content
/// either, and the unit is the one node of each family that carries nothing.
///
/// # Specification
/// - requires: `child_globals` holds the already-assigned global indices of
///   `node`'s children, in the order the arena's child relation yields them.
/// - ensures: the node tag, then the canonical inline payload, then each
///   child's global index as a minimal varint — which is both the entry's wire
///   image and its deduplication key, so two structurally equal nodes produce
///   equal bytes. A dangling id yields the unit entry of its family.
/// - provides: the content key the interner deduplicates on, and the bytes one
///   table entry occupies. The clause checks the exact node tag, including the
///   unit reading of a dangling id. The inline payload and the trailing child
///   indices stay prose: recomputing them would replay the allocating payload
///   encoders.
/// - fails: never — encoding is total.
/// - panics: none.
#[spec(ensures: |ret| ret.0.as_image().as_ref().first().copied()
    == Some(u8::from(match node {
        AnyNode::ValueType(id) => match arena.value_type(id) {
            None | Some(&ValueType::Unit) => tags::NODE_VT_UNIT,
            Some(&ValueType::Base(_)) => tags::NODE_VT_BASE,
            Some(&ValueType::Universe(_)) => tags::NODE_VT_UNIVERSE,
            Some(&ValueType::Abstract(_)) => tags::NODE_VT_ABSTRACT,
            Some(&ValueType::Product(..)) => tags::NODE_VT_PRODUCT,
            Some(&ValueType::Sum(..)) => tags::NODE_VT_SUM,
            Some(&ValueType::Thunk(_)) => tags::NODE_VT_THUNK,
            Some(&ValueType::Lift { .. }) => tags::NODE_VT_LIFT,
            Some(&ValueType::Element { .. }) => tags::NODE_VT_ELEMENT,
        },
        AnyNode::CompType(id) => match arena.comp_type(id) {
            None | Some(&CompType::Returner(_)) => tags::NODE_CT_RETURNER,
            Some(&CompType::Arrow { .. }) => tags::NODE_CT_ARROW,
            Some(&CompType::Pi { .. }) => tags::NODE_CT_PI,
        },
        AnyNode::Value(id) => match arena.value(id) {
            None | Some(&Value::Unit) => tags::NODE_V_UNIT,
            Some(&Value::Variable(_)) => tags::NODE_V_VARIABLE,
            Some(&Value::Constant(_)) => tags::NODE_V_CONSTANT,
            Some(&Value::Literal(_)) => tags::NODE_V_LITERAL,
            Some(&Value::Pair(..)) => tags::NODE_V_PAIR,
            Some(&Value::Injection(..)) => tags::NODE_V_INJECTION,
            Some(&Value::Thunk(_)) => tags::NODE_V_THUNK,
            Some(&Value::Lift { .. }) => tags::NODE_V_LIFT,
        },
        AnyNode::Computation(id) => match arena.computation(id) {
            None | Some(&Computation::Return(_)) => tags::NODE_C_RETURN,
            Some(&Computation::Lambda(_)) => tags::NODE_C_LAMBDA,
            Some(&Computation::Application(..)) => tags::NODE_C_APPLICATION,
            Some(&Computation::Bind(..)) => tags::NODE_C_BIND,
            Some(&Computation::Force(_)) => tags::NODE_C_FORCE,
            Some(&Computation::Case { .. }) => tags::NODE_C_CASE,
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
                | ValueType::Unit => out.put_tag(tags::NODE_VT_UNIT),
                | ValueType::Universe(ref level) => {
                    out.put_tag(tags::NODE_VT_UNIVERSE);
                    encode_level(&mut out, level);
                },
                | ValueType::Abstract(atom) => {
                    out.put_tag(tags::NODE_VT_ABSTRACT);
                    out.put_uvarint(WireU64::from(WireUsize::from(usize::from(atom))));
                },
                | ValueType::Product(..) => out.put_tag(tags::NODE_VT_PRODUCT),
                | ValueType::Sum(..) => out.put_tag(tags::NODE_VT_SUM),
                | ValueType::Thunk(_) => out.put_tag(tags::NODE_VT_THUNK),
                | ValueType::Lift { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_LIFT);
                    encode_level(&mut out, target);
                },
                | ValueType::Element { ref target, .. } => {
                    out.put_tag(tags::NODE_VT_ELEMENT);
                    encode_level(&mut out, target);
                },
            },
        },
        | AnyNode::CompType(id) => match arena.comp_type(id) {
            | Some(&CompType::Returner(_)) | None => out.put_tag(tags::NODE_CT_RETURNER),
            | Some(&CompType::Arrow { .. }) => out.put_tag(tags::NODE_CT_ARROW),
            | Some(&CompType::Pi { .. }) => out.put_tag(tags::NODE_CT_PI),
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
            },
        },
        | AnyNode::Computation(id) => match arena.computation(id) {
            | Some(&Computation::Lambda(_)) => out.put_tag(tags::NODE_C_LAMBDA),
            | Some(&Computation::Application(..)) => out.put_tag(tags::NODE_C_APPLICATION),
            | Some(&Computation::Return(_)) | None => out.put_tag(tags::NODE_C_RETURN),
            | Some(&Computation::Bind(..)) => out.put_tag(tags::NODE_C_BIND),
            | Some(&Computation::Force(_)) => out.put_tag(tags::NODE_C_FORCE),
            | Some(&Computation::Case { .. }) => out.put_tag(tags::NODE_C_CASE),
        },
    }
    for &child in child_globals {
        out.put_uvarint(WireU64::from(u64::from(u32::from(child))));
    }
    EncodedEntry(out)
}

/// Write a declaration's prenex level signature.
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
#[inline]
fn sign_tag(sign: Sign) -> WireTag
{
    match sign {
        | Sign::NonNegative => tags::SIGN_NON_NEGATIVE,
        | Sign::Negative => tags::SIGN_NEGATIVE,
    }
}

/// The wire tag of an injection side.
#[inline]
fn side_tag(side: Side) -> WireTag
{
    match side {
        | Side::Left => tags::SIDE_LEFT,
        | Side::Right => tags::SIDE_RIGHT,
    }
}
