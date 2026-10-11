//! Declarations as data: the prenex level signature, the three live content
//! shapes, the structured name, the admission mark that rides with each
//! declaration in an artifact, and the borrowing builder that ties content
//! minting to the arena watermark.
//!
//! Nothing here admits anything. A [`Declaration`] is the unit an artifact
//! carries and a choke point later re-checks; the checking, the audit, and the
//! environment that orders admissions belong to the crate above this one.

use alloc::string::String;
use alloc::vec::Vec;
use core::mem::ManuallyDrop;

use anodized::spec;
use gandr_kernel_strata::LandmarkConstraint;

use crate::arena::ArenaWatermark;
use crate::arena::TermArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::term::ConstantIndex;

/// The number of prenex level parameters a declaration binds.
///
/// # Specification
/// - requires: all u32 parameter counts are representable.
/// - ensures: distinguishes a parameter count from a level variable index; no
///   scope validation is implied.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 covers all four finishers over staged four-family graphs,
///   with ordered level constraints, unchecked parameter counts, distinct roots
///   and malformed sealing provenance. Full arena snapshots and metadata
///   observations separate premature rollback, changed roots, reordered
///   constraints and silently normalized producer claims. Both admission marks
///   and replacement names are observed, but neither the tests nor this data
///   layer prove admission, typing or the truth of provenance.
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelParamCount(u32);

impl From<u32> for LevelParamCount
{
    /// The count for a number of level parameters.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<LevelParamCount> for u32
{
    /// The number of parameters the count carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: LevelParamCount) -> Self
    {
        count.0
    }
}

/// The admission position of one minted atom, as the artifact's minted-atom
/// table records it.
///
/// A bare index would be the wrong type here even though the representation is
/// the same integer: the table's entries are positions in an admission
/// sequence, and the reader compares them against positions it re-derived. The
/// wrapper is what stops one being crossed with a subterm-table index or a byte
/// offset at a signature.
///
/// # Specification
/// - requires: all host admission positions are representable.
/// - ensures: distinguishes a claimed minted-atom position from a subterm-table
///   index; the decoder validates the complete table against declarations.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L0 distinguishes a claimed admission position from wire
///   indices. L3 takes a two-declaration artifact containing one abstract type
///   and one definition, then replaces its atom table with a repeat, an
///   omission or the definition’s position. Exact slot refusal and retained
///   declaration kind separate unchecked claims and position confusion;
///   host-width ceilings and longer tables are not covered by these fixtures.
/// - witness: `sharing_format::sharing_format::a_sealed_artifact_round_trips_with_its_atom_table`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_with_a_repeat_is_refused`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_omitting_an_atom_is_refused`
/// - witness: `sharing_format::sharing_format::a_minted_atom_table_naming_a_definition_is_refused`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MintedAtom(usize);

impl From<usize> for MintedAtom
{
    /// The atom for an admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<MintedAtom> for usize
{
    /// The admission position the atom carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(atom: MintedAtom) -> Self
    {
        atom.0
    }
}

/// A declaration's prenex level interface: how many level parameters it binds
/// and which landmark constraints it declares over them.
///
/// # Specification
/// - requires: all parameter counts and ordered, individually well-formed
///   landmark constraints are admitted.
/// - ensures: retains the ordered producer interface without validating
///   variable scope or consistency.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 covers all four finishers over staged four-family graphs,
///   with ordered level constraints, unchecked parameter counts, distinct roots
///   and malformed sealing provenance. Full arena snapshots and metadata
///   observations separate premature rollback, changed roots, reordered
///   constraints and silently normalized producer claims. Both admission marks
///   and replacement names are observed, but neither the tests nor this data
///   layer prove admission, typing or the truth of provenance.
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct LevelSignature
{
    /// The number of prenex level parameters.
    params: LevelParamCount,
    /// The declared landmark constraints, in declaration order.
    constraints: Vec<LandmarkConstraint>,
}

impl LevelSignature
{
    /// The signature of a declaration binding no level parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the signature binding zero level parameters and
    ///   declaring no constraints.
    /// - provides: the one monomorphic signature, so a declaration that binds
    ///   nothing does not have to spell an empty constraint list.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        ensures: |ret| ret.params.0 == 0
                && ret.constraints.is_empty(),
    )]
    #[inline]
    #[must_use]
    pub fn monomorphic() -> Self
    {
        Self::default()
    }

    /// Pair a parameter count with the constraints declared over it.
    ///
    /// # Specification
    /// - requires: nothing — a constraint naming a parameter outside the count
    ///   is a rejection at the choke point rather than a construction error,
    ///   because the kernel grants the producer no credence about its own
    ///   signature.
    /// - ensures: the signature carries `params` and `constraints` verbatim, in
    ///   declaration order, which is the order the artifact writes them in.
    /// - provides: the level interface a declaration crosses the format with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[inline]
    #[must_use]
    #[spec(captures: [entry_constraint_count = constraints.len()], ensures: |ret| ret.params() == params && ret.constraints().len() == entry_constraint_count)]
    pub fn new(
        params: LevelParamCount,
        constraints: Vec<LandmarkConstraint>,
    ) -> Self
    {
        Self {
            params,
            constraints,
        }
    }

    /// The number of prenex level parameters.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> LevelParamCount
    {
        self.params
    }

    /// The declared landmark constraints, in declaration order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn constraints(&self) -> &[LandmarkConstraint]
    {
        &self.constraints
    }
}

/// The content of a declaration: its roots into the arena that owns them.
///
/// The derived equality is child-id equality within one arena, never structural
/// equality across arenas; code needing agreement across arenas re-encodes.
///
/// # Specification
/// - requires: typed root ids are supplied; liveness and typing are external
///   obligations.
/// - ensures: distinguishes definitions, axioms and abstract types; derived
///   equality compares root ids rather than recursively comparing arenas.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 covers all four finishers over staged four-family graphs,
///   with ordered level constraints, unchecked parameter counts, distinct roots
///   and malformed sealing provenance. Full arena snapshots and metadata
///   observations separate premature rollback, changed roots, reordered
///   constraints and silently normalized producer claims. Both admission marks
///   and replacement names are observed, but neither the tests nor this data
///   layer prove admission, typing or the truth of provenance.
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum DeclarationContent
{
    /// A nominal data declaration, identified by its admission position.
    Data
    {
        /// Classifier telescope, each entry scoped under earlier parameters.
        parameters: Vec<ValueTypeId>,
        /// Field types per constructor, scoped under the whole telescope.
        constructors: Vec<Vec<ValueTypeId>>,
        /// Universe classifier bounding every constructor field.
        kind: ValueTypeId,
    },
    /// A typed definition: a declared value type and a fully elaborated body,
    /// which a checker verifies against that type.
    Def
    {
        /// The declared value type's root id.
        declared: ValueTypeId,
        /// The elaborated value body's root id.
        body: ValueId,
    },
    /// A tracked typed hole: a declared value type with no body. Everything
    /// resting on it is what an audit reports.
    Axiom
    {
        /// The declared value type's root id.
        declared: ValueTypeId,
    },
    /// A sealed abstract type: a minted nominal atom, declared at a universe
    /// kind and with no unfolding rule.
    ///
    /// It is neither a definition nor a hole, and the distinction is the point.
    /// A definition carries a body a kernel must verify; an axiom claims an
    /// inhabitant and is therefore audited. An abstract type claims no
    /// inhabitant — it introduces an uninterpreted type constant, a
    /// conservative extension — so it is not audited as an axiom.
    AbstractType
    {
        /// The atom's kind: a universe value-type root id.
        kind: ValueTypeId,
    },
}

/// One segment of a declaration's structured name: text holding no `.`.
///
/// A name is a list of segments, never one dotted string. A segment holding the
/// separator would let two different lists render as one string, so the
/// constructor refuses it and the decoder refuses it on the wire; a namespace
/// layer's dotted spelling cannot become an exported identity either way.
///
/// # Specification
/// - requires: text contains no ASCII period; empty and arbitrary remaining
///   UTF-8 text are admitted.
/// - ensures: retains a separator-free segment without normalization.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 classifies empty segments, a period at each boundary and in
///   the middle, NUL, line breaks, other punctuation, a fullwidth period and
///   composed/decomposed Unicode. Exact accepted bytes and refusal
///   classification separate a broadened delimiter set, invented normalization
///   and accidental empty-segment rejection. This is a finite UTF-8 boundary
///   domain, not an exhaustive Unicode proof.
/// - witness: `decl::tests::names_classify_the_separator_without_normalizing_unicode`
/// - witness: `sharing_format::sharing_format::a_segment_holding_a_separator_is_refused`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NameSegment(String);

impl NameSegment
{
    /// The separator a rendered name writes between segments, which no segment
    /// holds.
    pub const SEPARATOR: char = '.';

    /// Build a segment from `text`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(segment)` holding `text` unchanged exactly when `text`
    ///   holds no [`Self::SEPARATOR`].
    /// - provides: the only construction of a segment, so the encoder's input
    ///   cannot carry a separator and the encoder stays total.
    /// - fails: returns `None` when `text` holds [`Self::SEPARATOR`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 classifies empty segments, a period at each boundary
    ///   and in the middle, NUL, line breaks, other punctuation, a fullwidth
    ///   period and composed/decomposed Unicode. Exact accepted bytes and
    ///   refusal classification separate a broadened delimiter set, invented
    ///   normalization and accidental empty-segment rejection. This is a finite
    ///   UTF-8 boundary domain, not an exhaustive Unicode proof.
    /// - witness: `decl::tests::names_classify_the_separator_without_normalizing_unicode`
    /// - witness: `sharing_format::sharing_format::a_segment_holding_a_separator_is_refused`
    #[spec(
        captures: entry = (!text.contains(Self::SEPARATOR), text.len(), text.as_bytes().first().copied(), text.as_bytes().last().copied()),
        ensures: |ret| ret.as_ref().map_or(!entry.0,
            |segment| entry.0
                && segment.0.len() == entry.1
                && segment.0.as_bytes().first().copied() == entry.2
                && segment.0.as_bytes().last().copied() == entry.3
                && !segment.0.contains(Self::SEPARATOR)),
    )]
    #[inline]
    #[must_use]
    pub fn from_text(text: String) -> Option<Self>
    {
        if text.contains(Self::SEPARATOR) {
            return None;
        }
        Some(Self(text))
    }
}

impl AsRef<str> for NameSegment
{
    /// Borrow the segment's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

/// A declaration's structured name: its segments, outermost first.
///
/// The name is identity for a reader and nothing more. A reference reads the
/// admission position of what it names, so a declaration carries no name until
/// a producer gives it one, and no check reads it.
///
/// # Specification
/// - requires: any ordered segment sequence is admitted, including no segments
///   and empty segments.
/// - ensures: retains the ordered reader identity; names do not participate in
///   typing or admission-position references.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 classifies empty segments, a period at each boundary and in
///   the middle, NUL, line breaks, other punctuation, a fullwidth period and
///   composed/decomposed Unicode. Exact accepted bytes and refusal
///   classification separate a broadened delimiter set, invented normalization
///   and accidental empty-segment rejection. This is a finite UTF-8 boundary
///   domain, not an exhaustive Unicode proof.
/// - witness: `decl::tests::names_classify_the_separator_without_normalizing_unicode`
/// - witness: `sharing_format::sharing_format::a_segment_holding_a_separator_is_refused`
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StructuredName(Vec<NameSegment>);

impl StructuredName
{
    /// The segments, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn segments(&self) -> &[NameSegment]
    {
        &self.0
    }
}

impl From<Vec<NameSegment>> for StructuredName
{
    /// The name made of `segments`, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(segments: Vec<NameSegment>) -> Self
    {
        Self(segments)
    }
}

/// A declaration: a level interface, its content roots, its sealing
/// provenance, and its structured name.
///
/// # Specification
/// - requires: root ids and producer metadata are supplied; their admission
///   obligations are external.
/// - ensures: carries levels, content, provenance and an optional structured
///   name without validating the producer’s claims.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 covers all four finishers over staged four-family graphs,
///   with ordered level constraints, unchecked parameter counts, distinct roots
///   and malformed sealing provenance. Full arena snapshots and metadata
///   observations separate premature rollback, changed roots, reordered
///   constraints and silently normalized producer claims. Both admission marks
///   and replacement names are observed, but neither the tests nor this data
///   layer prove admission, typing or the truth of provenance.
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Declaration
{
    /// The prenex level interface.
    levels: LevelSignature,
    /// The content roots, addressing the arena that minted them.
    content: DeclarationContent,
    /// The atoms this declaration's sealing projection rebound, as the
    /// artifact's sealing-provenance slot carries them.
    ///
    /// It records the projection, never the event. "This module was sealed" is
    /// a claim about an elaborator's history that a kernel would have to take
    /// on faith; "this declaration's type was projected onto these atoms"
    /// is a claim about *this declaration's type*, which a choke point
    /// re-derives by walking it. Empty for every declaration no projection
    /// touched.
    provenance: Vec<ConstantIndex>,
    /// The structured name the artifact's name record carries; empty for a
    /// declaration no producer named.
    name: StructuredName,
}

impl Declaration
{
    /// The prenex level interface.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn levels(&self) -> &LevelSignature
    {
        &self.levels
    }

    /// The content roots.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content(&self) -> &DeclarationContent
    {
        &self.content
    }

    /// The declared value-type root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared_id(&self) -> ValueTypeId
    {
        self.content.declared_id()
    }

    /// The atoms this declaration's projection rebound, in the order the
    /// artifact carries them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn provenance(&self) -> &[ConstantIndex]
    {
        &self.provenance
    }

    /// The structured name, empty for a declaration no producer named.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> &StructuredName
    {
        &self.name
    }

    /// This declaration under `name`, its levels, content and provenance
    /// unchanged.
    ///
    /// # Specification
    /// - requires: nothing — a name is never a typing fact, so any name suits
    ///   any declaration.
    /// - ensures: returns the declaration carrying `name` as its structured
    ///   name, every other field as it was.
    /// - provides: the one way a producer names a declaration, after whichever
    ///   finisher built it, so no finisher changes its signature for a name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    /// - witness: `sharing_format::sharing_format::a_structured_name_round_trips_as_segments`
    #[spec(
        captures: entry = (self.content.clone(), self.levels.params, self.levels.constraints.len(), self.provenance.len(), self.provenance.first().copied(), self.provenance.last().copied(), name.0.len()),
        ensures: |ret| ret.content == entry.0
                && ret.levels.params == entry.1
                && ret.levels.constraints.len() == entry.2
                && ret.provenance.len() == entry.3
                && ret.provenance.first().copied() == entry.4
                && ret.provenance.last().copied() == entry.5
                && ret.name.0.len() == entry.6,
    )]
    #[inline]
    #[must_use]
    pub fn named(
        self,
        name: StructuredName,
    ) -> Self
    {
        Self { name, ..self }
    }
}

/// The producer’s claimed admission mode, not evidence of successful checking.
///
/// One bit, never a trust lattice: either the checked choke point admitted it
/// or a warned bypass did, and the artifact carries which so the audit survives
/// serialization.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AdmissionMark
{
    /// Admitted through the checked choke point.
    Checked,
    /// Admitted through the warned bypass.
    UncheckedBypass,
}

/// A declaration paired with the admission mark it carries on the wire.
///
/// This is the unit an artifact is a sequence of, in admission order, in both
/// directions: the encoder takes a slice of them and the decoder returns one.
///
/// # Specification
/// - requires: the caller pairs its claimed admission mode with a declaration.
/// - ensures: retains both data components without providing evidence that
///   checking occurred.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; constructors
///   and consumers supply its executable observations.
///
/// # Adequacy
/// - hypothesis: L3 covers all four finishers over staged four-family graphs,
///   with ordered level constraints, unchecked parameter counts, distinct roots
///   and malformed sealing provenance. Full arena snapshots and metadata
///   observations separate premature rollback, changed roots, reordered
///   constraints and silently normalized producer claims. Both admission marks
///   and replacement names are observed, but neither the tests nor this data
///   layer prove admission, typing or the truth of provenance.
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MarkedDeclaration
{
    /// How the producing environment admitted this declaration.
    mark: AdmissionMark,
    /// The declaration itself.
    declaration: Declaration,
}

impl MarkedDeclaration
{
    /// Pair an admission mark with a declaration.
    ///
    /// # Specification
    /// - requires: a producer-supplied admission-mode claim; the relationship
    ///   between the mark and declaration is not validated here.
    /// - ensures: returns the pair carrying both unchanged.
    /// - provides: the marked data a consumer stores, not evidence that
    ///   admission occurred or succeeded.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        ensures: |ret| matches!((ret.mark, mark), (AdmissionMark::Checked, AdmissionMark::Checked) | (AdmissionMark::UncheckedBypass, AdmissionMark::UncheckedBypass)),
    )]
    #[inline]
    #[must_use]
    pub const fn new(
        mark: AdmissionMark,
        declaration: Declaration,
    ) -> Self
    {
        Self { mark, declaration }
    }

    /// The admission mark.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mark(&self) -> AdmissionMark
    {
        self.mark
    }

    /// The declaration, whose content roots address the arena beside it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declaration(&self) -> &Declaration
    {
        &self.declaration
    }
}

/// A borrowing builder for one declaration's content.
///
/// It lends the arena for minting the declared type and body, then finalizes a
/// [`Declaration`] over the roots that minting produced.
///
/// **Abandoning a builder truncates the arena.** A builder dropped without
/// reaching a finisher — a scope exit on a failure path, or an explicit
/// [`Self::discard`] — truncates each family to the lesser of its current
/// length and the length the watermark recorded at construction holds for it.
/// A finisher consumes the builder without truncating: the minted content
/// becomes the declaration's.
///
/// # Specification
/// - requires: content for exactly one declaration is minted through
///   [`Self::arena`] between construction and a finisher, with no other
///   allocation into the arena interleaved — the recorded watermark and the
///   arena's end must describe a contiguous suffix.
/// - ensures: a finisher yields a [`Declaration`] over the minted roots and
///   leaves them in the arena; dropping the builder before a finisher truncates
///   each family to `min(current_len, content_start)`.
/// - provides: the construction surface that ties content minting to the
///   watermark discipline, so the truncation is structural rather than a step a
///   failure path has to remember. Constructor, finisher and destructor
///   predicates observe their own boundaries; caller-visible rollback is
///   witnessed after the mutable arena borrow ends.
/// - fails: never — minting is total.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; predicates
///   on new, arena, finishers and Drop observe its lifecycle locally.
///
/// # Adequacy
/// - hypothesis: L3 covers scope exit and explicit discard over nonempty
///   four-family prefixes, then truncation below a saved mark. Whole-arena
///   equality observes retained payloads as well as lengths and separates
///   accidental growth, prefix damage and a forgotten rollback. Allocation
///   failure and panic unwinding are outside these probes. L3 covers all four
///   finishers over staged four-family graphs, with ordered level constraints,
///   unchecked parameter counts, distinct roots and malformed sealing
///   provenance. Full arena snapshots and metadata observations separate
///   premature rollback, changed roots, reordered constraints and silently
///   normalized producer claims. Both admission marks and replacement names are
///   observed, but neither the tests nor this data layer prove admission,
///   typing or the truth of provenance.
/// - witness: `decl::tests::rollback_covers_all_families_and_never_regrows_a_truncated_prefix`
/// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
/// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
/// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
pub struct DeclarationBuilder<'arena>
{
    /// The borrowed arena.
    arena: &'arena mut TermArena,
    /// The watermark at construction, which is where this content begins.
    content_start: ArenaWatermark,
}

impl<'arena> DeclarationBuilder<'arena>
{
    /// Begin building a declaration's content into `arena`, recording the
    /// content-start watermark.
    ///
    /// # Specification
    /// - requires: `arena` is the arena this declaration's content will be
    ///   minted into.
    /// - ensures: returns a builder holding the arena's watermark at entry.
    /// - provides: the staging scope: a finisher leaves the minted content in
    ///   the arena, and dropping the builder before one truncates each family
    ///   to `min(current_len, content_start)`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers scope exit and explicit discard over nonempty
    ///   four-family prefixes, then truncation below a saved mark. Whole-arena
    ///   equality observes retained payloads as well as lengths and separates
    ///   accidental growth, prefix damage and a forgotten rollback. Allocation
    ///   failure and panic unwinding are outside these probes. L3 covers all
    ///   four finishers over staged four-family graphs, with ordered level
    ///   constraints, unchecked parameter counts, distinct roots and malformed
    ///   sealing provenance. Full arena snapshots and metadata observations
    ///   separate premature rollback, changed roots, reordered constraints and
    ///   silently normalized producer claims. Both admission marks and
    ///   replacement names are observed, but neither the tests nor this data
    ///   layer prove admission, typing or the truth of provenance.
    /// - witness: `decl::tests::rollback_covers_all_families_and_never_regrows_a_truncated_prefix`
    /// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
    /// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        captures: entry = (arena.watermark(), &raw const *arena),
        ensures: |ret| ret.content_start == entry.0
                && ret.arena.watermark() == entry.0
                && core::ptr::eq(&raw const *ret.arena, entry.1),
    )]
    #[inline]
    #[must_use]
    pub fn new(arena: &'arena mut TermArena) -> Self
    {
        let content_start = arena.watermark();
        Self {
            arena,
            content_start,
        }
    }

    /// The watermark this content began at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn content_start(&self) -> ArenaWatermark
    {
        self.content_start
    }

    /// The borrowed arena, for minting this declaration's content.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the borrowed arena, unchanged.
    /// - provides: the only minting handle inside a staging scope. It is the
    ///   whole arena, so a caller can truncate through it as well as mint
    ///   through it; whatever the family lengths then are, dropping the builder
    ///   before a finisher truncates each family to `min(current_len,
    ///   content_start)`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers scope exit and explicit discard over nonempty
    ///   four-family prefixes, then truncation below a saved mark. Whole-arena
    ///   equality observes retained payloads as well as lengths and separates
    ///   accidental growth, prefix damage and a forgotten rollback. Allocation
    ///   failure and panic unwinding are outside these probes.
    /// - witness: `decl::tests::rollback_covers_all_families_and_never_regrows_a_truncated_prefix`
    /// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
    /// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
    #[spec(
        captures: entry = (self.arena.watermark(), &raw const *self.arena),
        ensures: |ret| ret.watermark() == entry.0
                && core::ptr::eq(&raw const *ret, entry.1),
    )]
    #[inline]
    pub fn arena(&mut self) -> &mut TermArena
    {
        self.arena
    }

    /// Discard the staged content, truncating each family to
    /// `min(current_len, content_start)`.
    ///
    /// This is the explicit form of what the destructor does on scope exit;
    /// name it where the abandonment is the point of the path rather than the
    /// tail of an error return.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each family holds its `min(current_len, content_start)`
    ///   leading nodes.
    /// - provides: the named abandonment path. The truncation stays prose: it
    ///   occurs when the consumed builder drops, after the attribute's
    ///   normal-return checks; no post-return arena borrow is available without
    ///   changing this signature.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — rollback happens when the consumed builder drops,
    ///   after normal-return checks; this signature exposes no safe post-drop
    ///   arena borrow to the predicate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers scope exit and explicit discard over nonempty
    ///   four-family prefixes, then truncation below a saved mark. Whole-arena
    ///   equality observes retained payloads as well as lengths and separates
    ///   accidental growth, prefix damage and a forgotten rollback. Allocation
    ///   failure and panic unwinding are outside these probes.
    /// - witness: `decl::tests::rollback_covers_all_families_and_never_regrows_a_truncated_prefix`
    /// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
    /// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
    #[inline]
    pub fn discard(self)
    {
        // Dropping `self` truncates each family to `min(current_len,
        // content_start)`.
    }

    /// Finalize a definition over an already-minted declared type and body.
    ///
    /// # Specification
    /// - requires: declared and body resolve in the borrowed arena, including
    ///   roots that predate the builder’s saved mark. The level interface is a
    ///   producer claim; typing is checked elsewhere.
    /// - ensures: returns a definition over those roots with the supplied
    ///   levels, empty provenance and no name; all staged arena content remains
    ///   allocated.
    /// - provides: a consuming finisher that permits shared prefix roots and
    ///   suppresses rollback.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        requires: self.arena.value_type(declared).is_some()
                && self.arena.value(body).is_some(), captures: entry = (levels.params, levels.constraints.len()),
        ensures: |ret| ret.content == DeclarationContent::Def { declared, body }
                && ret.levels.params == entry.0
                && ret.levels.constraints.len() == entry.1
                && ret.name.0.is_empty()
                && ret.provenance.is_empty(),
    )]
    #[inline]
    #[must_use]
    pub fn def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Def { declared, body },
            provenance: Vec::new(),
            name: StructuredName::default(),
        }
    }

    /// Finalize a definition carrying sealing provenance: the atoms the
    /// projection that produced its declared type rebound.
    ///
    /// # Specification
    /// - requires: nothing — a malformed provenance is a rejection at a choke
    ///   point, never a construction error, because the kernel grants the
    ///   producer no credence about what it sealed.
    /// - ensures: a declaration whose provenance slot carries `provenance`
    ///   verbatim, so admission checks exactly what the artifact would carry.
    /// - provides: the sealed-member construction surface.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        captures: entry = (levels.params, levels.constraints.len(), provenance.len(), provenance.first().copied(), provenance.last().copied()),
        ensures: |ret| ret.content == DeclarationContent::Def { declared, body }
                && ret.levels.params == entry.0
                && ret.levels.constraints.len() == entry.1
                && ret.name.0.is_empty()
                && ret.provenance.len() == entry.2
                && ret.provenance.first().copied() == entry.3
                && ret.provenance.last().copied() == entry.4,
    )]
    #[inline]
    #[must_use]
    pub fn sealed_def(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
        body: ValueId,
        provenance: Vec<ConstantIndex>,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Def { declared, body },
            provenance,
            name: StructuredName::default(),
        }
    }

    /// Finalize an axiom over an already-minted declared type.
    ///
    /// # Specification
    /// - requires: declared resolves in the borrowed arena, including a root
    ///   that predates the builder’s saved mark. The level interface remains a
    ///   producer claim.
    /// - ensures: returns an axiom over that root with the supplied levels,
    ///   empty provenance and no name; all staged arena content remains
    ///   allocated.
    /// - provides: a consuming, body-free finisher that permits shared prefix
    ///   roots and suppresses rollback.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        requires: self.arena.value_type(declared).is_some(), captures: entry = (levels.params, levels.constraints.len()),
        ensures: |ret| ret.content == DeclarationContent::Axiom { declared }
                && ret.levels.params == entry.0
                && ret.levels.constraints.len() == entry.1
                && ret.name.0.is_empty()
                && ret.provenance.is_empty(),
    )]
    #[inline]
    #[must_use]
    pub fn axiom(
        self,
        levels: LevelSignature,
        declared: ValueTypeId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Axiom { declared },
            provenance: Vec::new(),
            name: StructuredName::default(),
        }
    }

    /// Finalize a sealed abstract type at an already-minted universe kind.
    ///
    /// # Specification
    /// - requires: nothing — a non-universe kind is a rejection at a choke
    ///   point, not a construction error.
    /// - ensures: a declaration whose content is an abstract type and whose
    ///   provenance is empty, an atom being what a projection produces rather
    ///   than something carrying a projection of its own.
    /// - provides: the atom-minting construction surface.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers all four finishers over staged four-family
    ///   graphs, with ordered level constraints, unchecked parameter counts,
    ///   distinct roots and malformed sealing provenance. Full arena snapshots
    ///   and metadata observations separate premature rollback, changed roots,
    ///   reordered constraints and silently normalized producer claims. Both
    ///   admission marks and replacement names are observed, but neither the
    ///   tests nor this data layer prove admission, typing or the truth of
    ///   provenance.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    #[spec(
        captures: entry = (levels.params, levels.constraints.len()),
        ensures: |ret| ret.content == DeclarationContent::AbstractType { kind }
                && ret.levels.params == entry.0
                && ret.levels.constraints.len() == entry.1
                && ret.name.0.is_empty()
                && ret.provenance.is_empty(),
    )]
    #[inline]
    #[must_use]
    pub fn abstract_type(
        self,
        levels: LevelSignature,
        kind: ValueTypeId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::AbstractType { kind },
            provenance: Vec::new(),
            name: StructuredName::default(),
        }
    }
}

impl Drop for DeclarationBuilder<'_>
{
    /// Truncate each family to `min(current_len, content_start)`.
    ///
    /// # Specification
    /// - requires: nothing; a builder consumed by a finisher never reaches
    ///   this, because each finisher forgets the builder instead of dropping
    ///   it.
    /// - ensures: truncates each family to `min(current_len, content_start)`.
    /// - provides: the truncation that ends an abandoned staging scope, so no
    ///   failure path has to name the watermark itself.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 covers scope exit and explicit discard over nonempty
    ///   four-family prefixes, then truncation below a saved mark. Whole-arena
    ///   equality observes retained payloads as well as lengths and separates
    ///   accidental growth, prefix damage and a forgotten rollback. Allocation
    ///   failure and panic unwinding are outside these probes.
    /// - witness: `decl::tests::rollback_covers_all_families_and_never_regrows_a_truncated_prefix`
    /// - witness: `decl::tests::an_abandoned_builder_restores_the_arena`
    /// - witness: `decl::tests::a_discarded_builder_restores_the_arena`
    #[spec(
        captures: entry = self.arena.watermark(),
        ensures: |ret| self.arena.watermark() == self.content_start.clamped_into(ArenaWatermark::default(), entry),
    )]
    #[inline]
    fn drop(&mut self)
    {
        self.arena.truncate_to(self.content_start);
    }
}

impl DeclarationBuilder<'_>
{
    /// Finish a nominal declaration with a parameter telescope and
    /// constructors.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn data(
        self,
        levels: LevelSignature,
        parameters: Vec<ValueTypeId>,
        constructors: Vec<Vec<ValueTypeId>>,
        kind: ValueTypeId,
    ) -> Declaration
    {
        let _kept = ManuallyDrop::new(self);
        Declaration {
            levels,
            content: DeclarationContent::Data {
                parameters,
                constructors,
                kind,
            },
            provenance: Vec::new(),
            name: StructuredName::default(),
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::DeclarationBuilder;
    use super::LevelSignature;
    use crate::arena::TermArena;

    #[test]
    fn names_classify_the_separator_without_normalizing_unicode()
    {
        for (text, accepted) in [
            ("", true),
            ("a", true),
            ("é", true),
            ("e\u{301}", true),
            ("．", true),
            ("a/b", true),
            ("a\\b", true),
            ("a\0b", true),
            ("\r\n", true),
            (".", false),
            (".a", false),
            ("a.", false),
            ("a.b", false),
            ("a..b", false),
            ("é.文", false),
        ] {
            let segment = super::NameSegment::from_text(alloc::string::String::from(text));
            assert_eq!(segment.is_some(), accepted, "{text:?}");
            if let Some(segment) = segment {
                assert_eq!(segment.as_ref().as_bytes(), text.as_bytes());
            }
        }
        let unnamed = super::StructuredName::default();
        let empty_segment = super::StructuredName::from(alloc::vec![
            super::NameSegment::from_text(alloc::string::String::new())
                .expect("an empty segment has no separator")
        ]);
        let mut arena = TermArena::new();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let declared = builder.arena().value_type_unit();
        let body = builder.arena().value_unit();
        let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
        let unnamed_bytes = crate::encode::encode(&arena, &[super::MarkedDeclaration::new(
            super::AdmissionMark::Checked,
            declaration.clone().named(unnamed.clone()),
        )]);
        let empty_segment_bytes = crate::encode::encode(&arena, &[super::MarkedDeclaration::new(
            super::AdmissionMark::Checked,
            declaration.named(empty_segment.clone()),
        )]);
        assert_ne!(
            unnamed_bytes, empty_segment_bytes,
            "no segments and one empty segment have distinct wire identities"
        );
        let unnamed_decoded =
            crate::decode::decode(unnamed_bytes.as_image()).expect("unnamed declaration");
        let empty_segment_decoded =
            crate::decode::decode(empty_segment_bytes.as_image()).expect("empty named segment");
        assert_eq!(
            unnamed_decoded
                .declarations()
                .first()
                .expect("one declaration")
                .declaration()
                .name(),
            &unnamed
        );
        assert_eq!(
            empty_segment_decoded
                .declarations()
                .first()
                .expect("one declaration")
                .declaration()
                .name(),
            &empty_segment
        );
    }

    #[test]
    fn rollback_covers_all_families_and_never_regrows_a_truncated_prefix()
    {
        for explicit in [false, true] {
            for shortened in [false, true] {
                let mut arena = TermArena::new();
                let value = arena.value_variable(crate::term::DeBruijnIndex::from(7_u32));
                let computation = arena.computation_return(value);
                let value_type = arena.value_type_base(crate::base::BaseType::String);
                let comp_type = arena.comp_type_returner(value_type);
                let expected = if shortened {
                    TermArena::new()
                }
                else {
                    arena.clone()
                };
                let mut builder = DeclarationBuilder::new(&mut arena);
                let _value = builder.arena().value_pair(value, value);
                let _computation = builder.arena().computation_lambda(computation);
                let _value_type = builder.arena().value_type_product(value_type, value_type);
                let _comp_type = builder.arena().comp_type_arrow(value_type, comp_type);
                if shortened {
                    builder
                        .arena()
                        .truncate_to(crate::arena::ArenaWatermark::default());
                }
                if explicit {
                    builder.discard();
                }
                else {
                    drop(builder);
                }
                assert_eq!(arena, expected);
            }
        }
    }

    #[test]
    fn finishers_preserve_payloads_and_staged_graphs()
    {
        let x = gandr_kernel_strata::Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(0_u32),
        ));
        let y = gandr_kernel_strata::Level::var(gandr_kernel_strata::LevelVar::new(
            gandr_kernel_strata::LevelVarIndex::from(1_u32),
        ));
        let constraints = alloc::vec![
            gandr_kernel_strata::LandmarkConstraint::equal(y.clone(), x.clone())
                .expect("variable-only sides"),
            gandr_kernel_strata::LandmarkConstraint::leq(x, y).expect("variable-only sides"),
        ];
        let provenance = alloc::vec![
            crate::term::ConstantIndex::from(usize::MAX),
            crate::term::ConstantIndex::from(0_usize),
            crate::term::ConstantIndex::from(usize::MAX)
        ];
        let mut arena = TermArena::new();
        let _prefix_type = arena.value_type_base(crate::base::BaseType::Numeric);
        let _prefix_value = arena.value_variable(crate::term::DeBruijnIndex::from(9_u32));
        for supplied_count in [None, Some(0_u32), Some(1), Some(2), Some(u32::MAX)] {
            for shape in 0_u8 .. 4 {
                let levels = supplied_count.map_or_else(LevelSignature::monomorphic, |count| {
                    LevelSignature::new(super::LevelParamCount::from(count), constraints.clone())
                });
                let expected_constraints = if supplied_count.is_none() {
                    &[][..]
                }
                else {
                    constraints.as_slice()
                };
                let mut builder = DeclarationBuilder::new(&mut arena);
                let unit_type = builder.arena().value_type_unit();
                let result_type = builder.arena().comp_type_returner(unit_type);
                let thunk_type = builder.arena().value_type_thunk(result_type);
                let unit_value = builder.arena().value_unit();
                let returned = builder.arena().computation_return(unit_value);
                let thunk = builder.arena().value_thunk(returned);
                let declared = match shape {
                    | 0 => thunk_type,
                    | 1 => builder.arena().value_type_product(unit_type, thunk_type),
                    | 2 => builder.arena().value_type_sum(unit_type, thunk_type),
                    | _ => builder.arena().value_type_universe(
                        crate::types::GroundSort::Value,
                        gandr_kernel_strata::Level::zero(),
                    ),
                };
                let body = if shape == 1 {
                    builder.arena().value_pair(unit_value, thunk)
                }
                else {
                    thunk
                };
                let staged = builder.arena().clone();
                let expected_content = match shape {
                    | 0 | 1 => super::DeclarationContent::Def { declared, body },
                    | 2 => super::DeclarationContent::Axiom { declared },
                    | _ => super::DeclarationContent::AbstractType { kind: declared },
                };
                let declaration = match shape {
                    | 0 => builder.def(levels, declared, body),
                    | 1 => builder.sealed_def(levels, declared, body, provenance.clone()),
                    | 2 => builder.axiom(levels, declared),
                    | _ => builder.abstract_type(levels, declared),
                };
                assert_eq!(arena, staged, "a finisher must not run rollback");
                assert_eq!(declaration.content(), &expected_content);
                assert_eq!(declaration.declared_id(), declared);
                assert_eq!(
                    declaration.levels().params(),
                    super::LevelParamCount::from(supplied_count.unwrap_or(0))
                );
                assert_eq!(declaration.levels().constraints(), expected_constraints);
                let expected_provenance = if shape == 1 {
                    provenance.as_slice()
                }
                else {
                    &[][..]
                };
                assert_eq!(declaration.provenance(), expected_provenance);
                assert_eq!(declaration.name().segments(), &[]);
                let first_name = super::StructuredName::from(alloc::vec![
                    super::NameSegment::from_text(alloc::string::String::from("old"))
                        .expect("bare name")
                ]);
                let replacement = super::StructuredName::from(alloc::vec![
                    super::NameSegment::from_text(alloc::string::String::new())
                        .expect("empty segment"),
                    super::NameSegment::from_text(alloc::string::String::from("e\u{301}"))
                        .expect("decomposed Unicode"),
                    super::NameSegment::from_text(alloc::string::String::from("\0"))
                        .expect("NUL segment"),
                ]);
                let named = declaration.named(first_name).named(replacement.clone());
                assert_eq!(named.name(), &replacement);
                assert_eq!(named.content(), &expected_content);
                assert_eq!(
                    named.levels().params(),
                    super::LevelParamCount::from(supplied_count.unwrap_or(0))
                );
                assert_eq!(named.levels().constraints(), expected_constraints);
                assert_eq!(named.provenance(), expected_provenance);
                for mark in [
                    super::AdmissionMark::Checked,
                    super::AdmissionMark::UncheckedBypass,
                ] {
                    let marked = super::MarkedDeclaration::new(mark, named.clone());
                    assert_eq!(marked.mark(), mark);
                    assert_eq!(marked.declaration(), &named);
                }
                assert_eq!(
                    arena, staged,
                    "renaming and marking cannot alter staged content"
                );
            }
        }
    }

    #[test]
    fn an_abandoned_builder_restores_the_arena()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let staged = {
            let mut builder = DeclarationBuilder::new(&mut arena);
            builder.arena().value_unit()
        };
        assert_eq!(
            before,
            arena.watermark(),
            "a builder dropped at scope exit restores the watermark"
        );
        assert!(
            arena.value(staged).is_none(),
            "content staged by an abandoned builder is gone"
        );
    }

    #[test]
    fn a_discarded_builder_restores_the_arena()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let mut builder = DeclarationBuilder::new(&mut arena);
        let staged = builder.arena().value_unit();
        builder.discard();
        assert_eq!(
            before,
            arena.watermark(),
            "an explicitly discarded builder restores the watermark"
        );
        assert!(
            arena.value(staged).is_none(),
            "content staged by a discarded builder is gone"
        );
    }

    #[test]
    fn a_finished_builder_keeps_its_content()
    {
        let mut arena = TermArena::new();
        let before = arena.watermark();
        let mut builder = DeclarationBuilder::new(&mut arena);
        assert_eq!(
            before,
            builder.content_start(),
            "the builder records the watermark it began at"
        );
        let declared = builder.arena().value_type_unit();
        let body = builder.arena().value_unit();
        let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
        assert_ne!(
            before,
            arena.watermark(),
            "a finisher leaves the minted content in the arena"
        );
        assert!(
            arena.value(body).is_some(),
            "the finished declaration's body still resolves"
        );
        assert_eq!(
            declared,
            declaration.declared_id(),
            "the declared root is kept"
        );
        assert!(
            declaration.provenance().is_empty(),
            "an ordinary definition carries no sealing provenance"
        );
    }
}
