//! The append-only term arena: the single owner of every term and type node,
//! addressed by four typed `u32`-backed node ids.
//!
//! # Why an arena rather than owned trees
//!
//! A deep uniquely-owned tree still recurses on destruction, and a decoder can
//! build an arbitrarily deep graph from bytes: an adversary offers one, has it
//! rejected, and overflows the stack *dropping* it. Iterative decode and
//! iterative checking do not cover deallocation, so under owned pointers the
//! answer is a hand-written iterative destructor that becomes a permanent
//! fixture of the trusted base.
//!
//! The arena **dissolves** that obligation rather than managing it. Ids are
//! `Copy`, so no deep clone exists to make iterative; teardown is a flat vector
//! drop with no recursive drop glue; and the derived equality, hashing and
//! debug instances are shallow over ids. This is also the sanctioned form of
//! the flat-representation rule: recursive owned data is id-addressed, so the
//! type plane has no owning-pointer cycle to reject.
//!
//! # Constructor and admission disciplines
//!
//! - **Constructor-only minting.** A constructor appends to one family over
//!   caller-supplied live children. Within that family, a new index follows its
//!   children while the family length fits u32; cross-family ids have no common
//!   ordering. Ids carry no arena provenance or reuse generation.
//! - **The admission watermark.** [`TermArena::watermark`] snapshots four
//!   family lengths. [`TermArena::truncate_to`] removes suffixes but cannot
//!   grow a shorter family or restore overwritten nodes. The caller keeps
//!   removed ids unreachable from retained content and pairs each mark with its
//!   arena; these obligations are not encoded in the mark.
//!
//! # The honest cost
//!
//! An owned tree cannot be ill-formed; a `u32` id *can* name no node, or a node
//! in another arena. The mitigations that keep that fail-closed are
//! constructor-only minting, one arena per environment, a checked lookup
//! returning an option rather than an index, and decode-side validation of
//! every child reference before it mints.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;

use crate::base::BaseType;
use crate::base::Literal;
use crate::term::Computation;
use crate::term::ConstantIndex;
use crate::term::DeBruijnIndex;
use crate::term::Side;
use crate::term::Value;
use crate::types::CompType;
use crate::types::GroundSort;
use crate::types::ValueType;

/// The id of a [`Value`] node in a [`TermArena`].
///
/// A family ordinal minted by a [`TermArena`] constructor. It can dangle after
/// truncation or alias a reminted or foreign ordinal; it carries no arena
/// provenance. Only same-family children share its allocation order.
///
/// # Specification
/// - requires: all ordinals are representable; resolution depends on the
///   selected arena’s current values family.
/// - ensures: carries a family-specific u32 ordinal, not arena provenance or a
///   reuse generation.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 observes all four family prefixes before and after
///   truncation, stale marks, dangling ids, reminting and a foreign id with a
///   coincident ordinal. Exact retained variants and dense indices separate
///   prefix damage, accidental growth, wrong-family lookup and
///   generation/provenance assumptions. Allocation at the u32 ceiling is not
///   exercised; its conversion is checked separately.
/// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueId(u32);

/// The id of a [`Computation`] node in a [`TermArena`].
///
/// # Specification
/// - requires: all ordinals are representable; resolution depends on the
///   selected arena’s current computations family.
/// - ensures: carries a family-specific u32 ordinal, not arena provenance or a
///   reuse generation.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 observes all four family prefixes before and after
///   truncation, stale marks, dangling ids, reminting and a foreign id with a
///   coincident ordinal. Exact retained variants and dense indices separate
///   prefix damage, accidental growth, wrong-family lookup and
///   generation/provenance assumptions. Allocation at the u32 ceiling is not
///   exercised; its conversion is checked separately.
/// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComputationId(u32);

/// The id of a [`ValueType`] node in a [`TermArena`].
///
/// # Specification
/// - requires: all ordinals are representable; resolution depends on the
///   selected arena’s current value-type family.
/// - ensures: carries a family-specific u32 ordinal, not arena provenance or a
///   reuse generation.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 observes all four family prefixes before and after
///   truncation, stale marks, dangling ids, reminting and a foreign id with a
///   coincident ordinal. Exact retained variants and dense indices separate
///   prefix damage, accidental growth, wrong-family lookup and
///   generation/provenance assumptions. Allocation at the u32 ceiling is not
///   exercised; its conversion is checked separately.
/// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeId(u32);

// The const projection lives beside the id representation so its predicate
// can compare private ordinals without exposing a scalar observer.
impl crate::decl::DeclarationContent
{
    /// The declared value-type root: the declared type of a definition or an
    /// axiom, and the kind of an abstract type.
    ///
    /// The three share one accessor because they share one well-formedness
    /// obligation — whatever the root is, it must form. What differs is what
    /// admission additionally demands of it, which is not this crate's plane.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the declared value-type root, whichever of the three
    ///   forms the content takes.
    /// - provides: the one root every form owes well-formedness for, so a
    ///   consumer checking that obligation cannot reach a form it forgot.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 checks distinct selected roots across all content forms
    ///   and evaluates each projection in a const context. This separates
    ///   wrong-variant selection and incorrect root ordinals without claiming
    ///   that the root is well formed.
    /// - witness: `decl::tests::finishers_preserve_payloads_and_staged_graphs`
    /// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
    #[spec(
        ensures: |ret| ret.0 == match *self { Self::Def { declared, .. } | Self::Axiom { declared } | Self::AbstractType { kind: declared } => declared.0 },
    )]
    #[inline]
    #[must_use]
    pub const fn declared_id(&self) -> ValueTypeId
    {
        match *self {
            | Self::Def { declared, .. }
            | Self::Axiom { declared }
            | Self::AbstractType { kind: declared } => declared,
        }
    }
}

/// The id of a [`CompType`] node in a [`TermArena`].
///
/// # Specification
/// - requires: all ordinals are representable; resolution depends on the
///   selected arena’s current computation-type family.
/// - ensures: carries a family-specific u32 ordinal, not arena provenance or a
///   reuse generation.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 observes all four family prefixes before and after
///   truncation, stale marks, dangling ids, reminting and a foreign id with a
///   coincident ordinal. Exact retained variants and dense indices separate
///   prefix damage, accidental growth, wrong-family lookup and
///   generation/provenance assumptions. Allocation at the u32 ceiling is not
///   exercised; its conversion is checked separately.
/// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CompTypeId(u32);

/// A cross-family node reference: the work item every walk over the arena's
/// edge relation carries.
///
/// # Specification
/// - requires: all four typed node ids are admitted, including dangling ones.
/// - ensures: retains the node family together with its ordinal; no
///   cross-family allocation ordering is implied.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 builds all former families with distinguishable children,
///   nonzero levels and literal payloads, observes the exact stored nodes and
///   ordered edges, and checks each operation changes only its own family
///   length. Quote decoding covers matching, crossed and non-quote codes
///   without allocating an alias node. These distinguish child permutations,
///   payload loss, wrong-family minting and accidental hash-consing; the probes
///   are not a typing or arena-provenance proof.
/// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AnyNode
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
}

/// The number of nodes allocated in one arena family.
///
/// # Specification
/// - requires: all usize counts are representable.
/// - ensures: distinguishes a host family length or offset from a compact
///   ordinal.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArenaLength(usize);

/// The stored index of one node within its arena family.
///
/// # Specification
/// - requires: all u32 ordinals are representable.
/// - ensures: distinguishes the compact id width from a host family length.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArenaIndex(u32);

/// Convert an arena length to the `u32` an id wraps, saturating at the ceiling.
///
/// # Specification
/// - requires: `length` is a family length within an arena.
/// - ensures: the equal index when representable, otherwise the u32 ceiling.
///   The decode entry cap stays below this ceiling; unrestricted constructor
///   calls have no corresponding allocation cap.
/// - provides: a total, panic-free length-to-index conversion, without arena
///   provenance.
/// - fails: never; it saturates.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[inline]
#[spec(ensures: |ret| ret.0 == u32::try_from(length.0).unwrap_or(u32::MAX))]
fn id_index(length: ArenaLength) -> ArenaIndex
{
    ArenaIndex(u32::try_from(length.0).unwrap_or(u32::MAX))
}

/// Convert an id's index to the offset a checked vector read takes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the equal offset, lossless on every supported platform of at
///   least 32 bits.
/// - provides: the total, panic-free index-to-offset conversion.
/// - fails: never; it saturates at the offset ceiling, which a checked read
///   then rejects.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[inline]
#[spec(ensures: |ret| ret.0 == usize::try_from(index.0).unwrap_or(usize::MAX))]
fn id_offset(index: ArenaIndex) -> ArenaLength
{
    ArenaLength(usize::try_from(index.0).unwrap_or(usize::MAX))
}

/// Clamp one family length into an inclusive length interval.
///
/// # Specification
/// - requires: all lengths and both ordered and inverted bounds are admitted.
/// - ensures: returns low for an inverted interval; otherwise returns low below
///   the interval, high above it and value inside it.
/// - provides: the total per-coordinate clamp used by [`ArenaWatermark`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[spec(
    ensures: |ret| ret.0 == if low.0 >= high.0 || value.0 < low.0 { low.0 }
        else if value.0 > high.0 { high.0 }
        else { value.0 },
)]
#[inline]
const fn clamp_length(
    value: ArenaLength,
    low: ArenaLength,
    high: ArenaLength,
) -> ArenaLength
{
    let capped = if value.0 < high.0 { value.0 } else { high.0 };
    ArenaLength(if capped > low.0 { capped } else { low.0 })
}

/// A snapshot of the four family lengths: the admission watermark.
///
/// Truncation removes a suffix from each family without growing a shorter
/// family or restoring overwritten content. The default is the empty
/// arena's watermark, which is the floor an environment starts at.
///
/// # Specification
/// - requires: each coordinate is an independent host length; no relation to a
///   particular arena is encoded.
/// - ensures: carries four family lengths; the default coordinates are zero and
///   clamping is componentwise.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds over
///   zero, small values and the usize ceiling, with different coordinates in
///   each watermark. Widened numeric observations cover id conversion at zero,
///   the u32 ceiling and the target ceiling without allocating huge arenas.
///   These separate wraparound, min/max reversal and coordinate substitution;
///   hypothetical pointer widths are not emulated.
/// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArenaWatermark
{
    /// The [`Value`] family length.
    values: usize,
    /// The [`Computation`] family length.
    computations: usize,
    /// The [`ValueType`] family length.
    value_types: usize,
    /// The [`CompType`] family length.
    comp_types: usize,
}

impl ArenaWatermark
{
    /// Clamp this watermark, family by family, into the inclusive interval
    /// `[low, high]`.
    ///
    /// This is the rollback mark an admission choke point truncates to when it
    /// rejects: the declaration's content-start mark, clamped between the
    /// admission floor and the mark taken on entry. The clamp is what stops a
    /// rollback from reaching below content a prior admission committed when
    /// staging order is not admission order, and from leaving an intermediate
    /// behind when the content-start mark is not the one the arena grew from.
    ///
    /// # Specification
    /// - requires: all component values and both ordered and inverted bounds
    ///   are admitted.
    /// - ensures: clamps each coordinate independently into its inclusive
    ///   interval; an inverted coordinate interval returns its low component.
    /// - provides: the rejection rollback mark without changing any arena or
    ///   allocating a snapshot.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 enumerates ordered, equal and inverted clamp bounds
    ///   over zero, small values and the usize ceiling, with different
    ///   coordinates in each watermark. Widened numeric observations cover id
    ///   conversion at zero, the u32 ceiling and the target ceiling without
    ///   allocating huge arenas. These separate wraparound, min/max reversal
    ///   and coordinate substitution; hypothetical pointer widths are not
    ///   emulated.
    /// - witness: `arena::tests::scalar_clamps_and_index_ceilings_match_widened_models`
    /// - witness: `arena::tests::a_watermark_clamps_into_its_interval`
    #[spec(
        ensures: |ret| ret.values == if low.values >= high.values || self.values < low.values { low.values }
            else if self.values > high.values { high.values }
            else { self.values }
                && ret.computations == if low.computations >= high.computations || self.computations < low.computations { low.computations }
            else if self.computations > high.computations { high.computations }
            else { self.computations }
                && ret.value_types == if low.value_types >= high.value_types || self.value_types < low.value_types { low.value_types }
            else if self.value_types > high.value_types { high.value_types }
            else { self.value_types }
                && ret.comp_types == if low.comp_types >= high.comp_types || self.comp_types < low.comp_types { low.comp_types }
            else if self.comp_types > high.comp_types { high.comp_types }
            else { self.comp_types },
    )]
    #[inline]
    #[must_use]
    pub const fn clamped_into(
        self,
        low: Self,
        high: Self,
    ) -> Self
    {
        Self {
            values: clamp_length(
                ArenaLength(self.values),
                ArenaLength(low.values),
                ArenaLength(high.values),
            )
            .0,
            computations: clamp_length(
                ArenaLength(self.computations),
                ArenaLength(low.computations),
                ArenaLength(high.computations),
            )
            .0,
            value_types: clamp_length(
                ArenaLength(self.value_types),
                ArenaLength(low.value_types),
                ArenaLength(high.value_types),
            )
            .0,
            comp_types: clamp_length(
                ArenaLength(self.comp_types),
                ArenaLength(low.comp_types),
                ArenaLength(high.comp_types),
            )
            .0,
        }
    }
}

/// The append-only arena owning every term and type node of one environment.
///
/// The four families are parallel append-only vectors and a node's children are
/// ids into the same arena. The node enums derive shallow clone and drop, so
/// cloning or dropping a whole arena is a flat per-family vector operation,
/// total on any term depth.
///
/// # Specification
/// - requires: callers retain only live reachable ids when truncating and
///   supply live children to constructors.
/// - ensures: stores four flat family vectors; construction does not hash-cons,
///   provenance is external and truncation permits index reuse.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary; executable
///   predicates belong to its constructors and observers.
///
/// # Adequacy
/// - hypothesis: L3 builds all former families with distinguishable children,
///   nonzero levels and literal payloads, observes the exact stored nodes and
///   ordered edges, and checks each operation changes only its own family
///   length. Quote decoding covers matching, crossed and non-quote codes
///   without allocating an alias node. These distinguish child permutations,
///   payload loss, wrong-family minting and accidental hash-consing; the probes
///   are not a typing or arena-provenance proof. L3 observes all four family
///   prefixes before and after truncation, stale marks, dangling ids, reminting
///   and a foreign id with a coincident ordinal. Exact retained variants and
///   dense indices separate prefix damage, accidental growth, wrong-family
///   lookup and generation/provenance assumptions. Allocation at the u32
///   ceiling is not exercised; its conversion is checked separately.
/// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
/// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TermArena
{
    /// The value nodes, in allocation order, which is child-before-parent.
    values: Vec<Value>,
    /// The computation nodes.
    computations: Vec<Computation>,
    /// The value-type nodes.
    value_types: Vec<ValueType>,
    /// The computation-type nodes.
    comp_types: Vec<CompType>,
}

impl TermArena
{
    /// Append raw finite session-code syntax; admission checks its invariants.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_session(
        &mut self,
        graph: alloc::sync::Arc<crate::session::Graph>,
        payloads: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Session { graph, payloads })
    }

    /// Append an untrusted session-path introduction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_session_path(
        &mut self,
        path_type: ValueTypeId,
        evidence: alloc::sync::Arc<crate::session::Evidence>,
        payload_paths: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::SessionPath {
            path_type,
            evidence,
            payload_paths,
        })
    }
    /// An empty arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The current watermark: the four family lengths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the four families' current lengths.
    /// - provides: the mark [`Self::truncate_to`] takes, truncating each family
    ///   to `min(current_len, mark)`, so a checker's intermediates are dropped
    ///   after a verdict. The mark carries no arena identity, so pairing it
    ///   with the arena it came from is the caller's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        ensures: |ret| ret.values == self.values.len()
                && ret.computations == self.computations.len()
                && ret.value_types == self.value_types.len()
                && ret.comp_types == self.comp_types.len(),
    )]
    #[inline]
    #[must_use]
    pub fn watermark(&self) -> ArenaWatermark
    {
        ArenaWatermark {
            values: self.values.len(),
            computations: self.computations.len(),
            value_types: self.value_types.len(),
            comp_types: self.comp_types.len(),
        }
    }

    /// Truncate each family to `min(current_len, watermark)`, dropping later
    /// allocations.
    ///
    /// # Specification
    /// - requires: `watermark` was taken from this arena, and every id minted
    ///   after it is unreachable from content the caller retains, which the
    ///   admission discipline establishes. A family already shorter than the
    ///   mark is admissible: its truncation is a no-op.
    /// - ensures: each family's length becomes `min(entry_len, watermark)` —
    ///   the mark's length where the family is longer, the length it already
    ///   has where it is shorter; an id whose index is at or past the resulting
    ///   length dangles, and a lookup of one fails closed rather than resolving
    ///   to a later node.
    /// - provides: the truncation an admission choke point performs after a
    ///   verdict, on rejection and on success alike. The clause checks family
    ///   lengths, including the stale-mark no-op. Arena provenance,
    ///   retained-node identity and external reachability stay prose: the
    ///   watermark has no arena identity, and checking retained nodes would
    ///   require an owned arena snapshot.
    /// - fails: never — a truncation past the end is a no-op, so a stale
    ///   watermark cannot grow the arena.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.min(watermark.values)
                && self.computations.len() == before.computations.min(watermark.computations)
                && self.value_types.len() == before.value_types.min(watermark.value_types)
                && self.comp_types.len() == before.comp_types.min(watermark.comp_types),
    )]
    #[inline]
    pub fn truncate_to(
        &mut self,
        watermark: ArenaWatermark,
    )
    {
        self.values.truncate(watermark.values);
        self.computations.truncate(watermark.computations);
        self.value_types.truncate(watermark.value_types);
        self.comp_types.truncate(watermark.comp_types);
    }

    /// Resolve a value id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the value node `id` names, and `None` exactly when
    ///   the id's index is past this family's length — after a truncation past
    ///   it, or for an id this arena never minted.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        ensures: |ret| match (ret, self.values.get(usize::try_from(id.0).unwrap_or(usize::MAX))) { (Some(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (None, None) => true, _ => false },
    )]
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        id: ValueId,
    ) -> Option<&Value>
    {
        self.values.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a computation id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the computation node `id` names, and `None` exactly
    ///   when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        ensures: |ret| match (ret, self.computations.get(usize::try_from(id.0).unwrap_or(usize::MAX))) { (Some(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (None, None) => true, _ => false },
    )]
    #[inline]
    #[must_use]
    pub fn computation(
        &self,
        id: ComputationId,
    ) -> Option<&Computation>
    {
        self.computations.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a value-type id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the value-type node `id` names, and `None` exactly
    ///   when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        ensures: |ret| match (ret, self.value_types.get(usize::try_from(id.0).unwrap_or(usize::MAX))) { (Some(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (None, None) => true, _ => false },
    )]
    #[inline]
    #[must_use]
    pub fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Option<&ValueType>
    {
        self.value_types.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a computation-type id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the computation-type node `id` names, and `None`
    ///   exactly when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all four family prefixes before and after
    ///   truncation, stale marks, dangling ids, reminting and a foreign id with
    ///   a coincident ordinal. Exact retained variants and dense indices
    ///   separate prefix damage, accidental growth, wrong-family lookup and
    ///   generation/provenance assumptions. Allocation at the u32 ceiling is
    ///   not exercised; its conversion is checked separately.
    /// - witness: `arena::tests::truncation_preserves_prefixes_reuses_indices_and_checks_all_families`
    #[spec(
        ensures: |ret| match (ret, self.comp_types.get(usize::try_from(id.0).unwrap_or(usize::MAX))) { (Some(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (None, None) => true, _ => false },
    )]
    #[inline]
    #[must_use]
    pub fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Option<&CompType>
    {
        self.comp_types.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Append a value node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `value` resolves in this arena.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the single minting site for a [`ValueId`], which is what
    ///   puts constructor-only minting in one checkable place. An id is a
    ///   family index, so [`Self::truncate_to`] makes index reuse a supported
    ///   path: after a truncation the next push mints an id equal to one minted
    ///   before it; and above the ceiling [`id_index`] saturates at, the
    ///   returned id no longer names the appended node.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: match value {
            Value::Pair(first, second) | Value::StaticApplication(first, second) | Value::PathProduct(first, second) => self.value(first).is_some() && self.value(second).is_some(),
            Value::Injection(_, body) | Value::Lift { body, .. } | Value::PathRefl(body) => self.value(body).is_some(),
            Value::PathEquiv { path_type, forward, backward, .. } => self.value_type(path_type).is_some() && self.value(forward).is_some() && self.value(backward).is_some(),
            Value::SessionPath { path_type, payload_paths, .. } => self.value_type(path_type).is_some() && self.value(payload_paths).is_some(),
            Value::Thunk(body) => self.computation(body).is_some(),
            Value::Quote(quoted) => self.value_type(quoted).is_some(),
            Value::QuoteComputation(quoted) => self.comp_type(quoted).is_some(),
            Value::Variable(_) | Value::Constant(_) | Value::Unit | Value::Literal(_) => true,
        }, captures: entry = (self.watermark(), core::mem::discriminant(&value)),
        ensures: |ret| self.values.len() == entry.0.values.saturating_add(1)
                && self.computations.len() == entry.0.computations
                && self.value_types.len() == entry.0.value_types
                && self.comp_types.len() == entry.0.comp_types
                && ret.0 == u32::try_from(entry.0.values).unwrap_or(u32::MAX)
                && self.values.last().map(core::mem::discriminant) == Some(entry.1),
    )]
    #[inline]
    fn alloc_value(
        &mut self,
        value: Value,
    ) -> ValueId
    {
        let id = ValueId(id_index(ArenaLength(self.values.len())).0);
        self.values.push(value);
        id
    }

    /// Append a computation node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `computation` resolves in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the single minting site for a [`ComputationId`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: match computation {
            Computation::Lambda(body) => self.computation(body).is_some(),
            Computation::Application(head, argument) => self.computation(head).is_some() && self.value(argument).is_some(),
            Computation::Return(value) | Computation::Force(value) | Computation::Absurd(value) => self.value(value).is_some(),
            Computation::Transport(path, value) => self.value(path).is_some() && self.value(value).is_some(),
            Computation::Bind(bound, body) => self.computation(bound).is_some() && self.computation(body).is_some(),
            Computation::Case { scrutinee, on_left, on_right } => self.value(scrutinee).is_some() && self.computation(on_left).is_some() && self.computation(on_right).is_some(),
        }, captures: entry = (self.watermark(), core::mem::discriminant(&computation)),
        ensures: |ret| self.values.len() == entry.0.values
                && self.computations.len() == entry.0.computations.saturating_add(1)
                && self.value_types.len() == entry.0.value_types
                && self.comp_types.len() == entry.0.comp_types
                && ret.0 == u32::try_from(entry.0.computations).unwrap_or(u32::MAX)
                && self.computations.last().map(core::mem::discriminant) == Some(entry.1),
    )]
    #[inline]
    fn alloc_computation(
        &mut self,
        computation: Computation,
    ) -> ComputationId
    {
        let id = ComputationId(id_index(ArenaLength(self.computations.len())).0);
        self.computations.push(computation);
        id
    }

    /// Append a value-type node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `value_type` resolves in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the single minting site for a [`ValueTypeId`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: match value_type {
            ValueType::Product(first, second) | ValueType::Sum(first, second) | ValueType::StaticPi { domain: first, codomain: second } => self.value_type(first).is_some() && self.value_type(second).is_some(),
            ValueType::PathUniverse(first, second) => self.value(first).is_some() && self.value(second).is_some(),
            ValueType::Thunk(body) => self.comp_type(body).is_some(),
            ValueType::Session { payloads, .. } => self.value_type(payloads).is_some(),
            ValueType::Lift { inner, .. } | ValueType::List(inner) => self.value_type(inner).is_some(),
            ValueType::Element { code, .. } => self.value(code).is_some(),
            ValueType::Base(_) | ValueType::Unit | ValueType::Empty | ValueType::Universe { .. } | ValueType::Abstract(_) => true,
        }, captures: entry = (self.watermark(), core::mem::discriminant(&value_type)),
        ensures: |ret| self.values.len() == entry.0.values
                && self.computations.len() == entry.0.computations
                && self.value_types.len() == entry.0.value_types.saturating_add(1)
                && self.comp_types.len() == entry.0.comp_types
                && ret.0 == u32::try_from(entry.0.value_types).unwrap_or(u32::MAX)
                && self.value_types.last().map(core::mem::discriminant) == Some(entry.1),
    )]
    #[inline]
    fn alloc_value_type(
        &mut self,
        value_type: ValueType,
    ) -> ValueTypeId
    {
        let id = ValueTypeId(id_index(ArenaLength(self.value_types.len())).0);
        self.value_types.push(value_type);
        id
    }

    /// Append a computation-type node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `comp_type` resolves in this arena.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is greater than
    ///   every computation-type id currently live in this arena.
    /// - provides: the single minting site for a [`CompTypeId`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: match comp_type { CompType::Returner(result) => self.value_type(result).is_some(), CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => self.value_type(domain).is_some()
                && self.comp_type(codomain).is_some(), CompType::Element { code, .. } => self.value(code).is_some() }, captures: entry = (self.watermark(), core::mem::discriminant(&comp_type)),
        ensures: |ret| self.values.len() == entry.0.values
                && self.computations.len() == entry.0.computations
                && self.value_types.len() == entry.0.value_types
                && self.comp_types.len() == entry.0.comp_types.saturating_add(1)
                && ret.0 == u32::try_from(entry.0.comp_types).unwrap_or(u32::MAX)
                && self.comp_types.last().map(core::mem::discriminant) == Some(entry.1),
    )]
    #[inline]
    fn alloc_comp_type(
        &mut self,
        comp_type: CompType,
    ) -> CompTypeId
    {
        let id = CompTypeId(id_index(ArenaLength(self.comp_types.len())).0);
        self.comp_types.push(comp_type);
        id
    }

    // Value constructors mint over live children. Only same-family indices
    // share an order, and the returned index saturates at the u32 ceiling.

    /// Mint a bound value variable.
    ///
    /// # Specification
    /// - requires: nothing; a de Bruijn index is an inline payload, and whether
    ///   it names an enclosing binder is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a bound variable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Variable(actual)) if actual == index),
    )]
    #[inline]
    pub fn value_variable(
        &mut self,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        self.alloc_value(Value::Variable(index))
    }

    /// Mint a constant reference to a prior declaration.
    ///
    /// # Specification
    /// - requires: nothing; whether the admission position names an admitted
    ///   declaration is a typing fact, refused at the choke point rather than
    ///   here.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a constant
    ///   reference.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Constant(actual)) if actual == index),
    )]
    #[inline]
    pub fn value_constant(
        &mut self,
        index: ConstantIndex,
    ) -> ValueId
    {
        self.alloc_value(Value::Constant(index))
    }

    /// Mint the unit value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for the unit value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Unit)),
    )]
    #[inline]
    pub fn value_unit(&mut self) -> ValueId
    {
        self.alloc_value(Value::Unit)
    }

    /// Mint a base-type literal value.
    ///
    /// # Specification
    /// - requires: nothing; the literal is an inline payload, and whether it
    ///   inhabits its base type is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a literal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = (self.watermark(), literal.base_type()),
        ensures: |ret| self.values.len() == before.0.values.saturating_add(1)
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types
                && self.comp_types.len() == before.0.comp_types
                && ret.0 == u32::try_from(before.0.values).unwrap_or(u32::MAX)
                && self.values.last().is_some_and(|node| match *node { Value::Literal(ref actual) => actual.base_type() == before.1, _ => false }),
    )]
    #[inline]
    pub fn value_literal(
        &mut self,
        literal: Literal,
    ) -> ValueId
    {
        self.alloc_value(Value::Literal(literal))
    }

    /// Mint a pair over two already-allocated value children.
    ///
    /// # Specification
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is strictly greater than both child
    ///   ids, which the precondition keeps live.
    /// - provides: the pair node, acyclic by construction; the id ordering is
    ///   what the subterm table's strictly-earlier invariant rests on.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(first).is_some()
                && self.value(second).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Pair(left, right)) if left == first
                && right == second),
    )]
    #[inline]
    pub fn value_pair(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Pair(first, second))
    }

    /// Mint a sum injection over an already-allocated value body.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena.
    /// - ensures: appends the node on the named side and returns the value
    ///   family's length before the push, saturated at the `u32` ceiling; while
    ///   that length fits `u32` the id names the appended node and is strictly
    ///   greater than `body`, which the precondition keeps live.
    /// - provides: the injection node, acyclic by construction; which summand
    ///   the side selects is a typing fact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(body).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Injection(actual_side, actual_body)) if actual_side == side
                && actual_body == body),
    )]
    #[inline]
    pub fn value_injection(
        &mut self,
        side: Side,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Injection(side, body))
    }

    /// Mint a thunk over an already-allocated computation body.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena's computation family.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the one value form embedding a computation, which suspends
    ///   rather than runs it. The child crosses families, so the two ids share
    ///   no allocation order and none is claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.computation(body).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Thunk(actual)) if actual == body),
    )]
    #[inline]
    pub fn value_thunk(
        &mut self,
        body: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Thunk(body))
    }

    /// Mint a value lift over an already-allocated value body.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena; whether its type's level sits
    ///   strictly below `target` is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is strictly greater than `body`,
    ///   which the precondition keeps live.
    /// - provides: the written lift; there is no implicit cumulativity, so a
    ///   lift exists only where a producer minted one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(body).is_some(), captures: before = (self.watermark(), target.constant_part()),
        ensures: |ret| self.values.len() == before.0.values.saturating_add(1)
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types
                && self.comp_types.len() == before.0.comp_types
                && ret.0 == u32::try_from(before.0.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Lift { ref target, body: actual }) if actual == body
                && target.constant_part() == before.1),
    )]
    #[inline]
    pub fn value_lift(
        &mut self,
        target: Level,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Lift { target, body })
    }

    /// Mint the code of an already-allocated value type.
    ///
    /// # Specification
    /// - requires: `quoted` resolves in this arena's value-type family.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling.
    /// - provides: the quote `⌜A⌝`; its universe level is formation's to read.
    ///   The child crosses families, so the two ids share no allocation order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(quoted).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::Quote(actual)) if actual == quoted),
    )]
    #[inline]
    pub fn value_quote(
        &mut self,
        quoted: ValueTypeId,
    ) -> ValueId
    {
        self.alloc_value(Value::Quote(quoted))
    }

    /// Mint the code of an already-allocated computation type.
    ///
    /// # Specification
    /// - requires: `quoted` resolves in this arena's computation-type family.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling.
    /// - provides: the quote `⌜C⌝` of a computation type, which is a value like
    ///   every code.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.comp_type(quoted).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::QuoteComputation(actual)) if actual == quoted),
    )]
    #[inline]
    pub fn value_quote_computation(
        &mut self,
        quoted: CompTypeId,
    ) -> ValueId
    {
        self.alloc_value(Value::QuoteComputation(quoted))
    }

    /// Mint a static application of an already-allocated type operator to an
    /// already-allocated code.
    ///
    /// # Specification
    /// - requires: `head` and `argument` resolve in this arena; whether `head`
    ///   inhabits a static Pi whose domain `argument` checks against is checked
    ///   at the choke point.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is strictly greater than both child
    ///   ids, which the precondition keeps live.
    /// - provides: the neutral static application: the vocabulary has no static
    ///   lambda, so no arena holds a static redex and the node never reduces.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(head).is_some()
                && self.value(argument).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values.saturating_add(1)
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.values).unwrap_or(u32::MAX)
                && matches!(self.values.last(), Some(&Value::StaticApplication(left, right)) if left == head
                && right == argument),
    )]
    #[inline]
    pub fn value_static_application(
        &mut self,
        head: ValueId,
        argument: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::StaticApplication(head, argument))
    }

    // Computation constructors.

    /// Mint a lambda over an already-allocated computation body.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   `body`, which the precondition keeps live.
    /// - provides: the lambda node, acyclic by construction; the binder is
    ///   positional, so no name is represented.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.computation(body).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Lambda(actual)) if actual == body),
    )]
    #[inline]
    pub fn computation_lambda(
        &mut self,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Lambda(body))
    }

    /// Mint an application over an already-allocated head and argument.
    ///
    /// # Specification
    /// - requires: `head` and `argument` resolve in this arena, in its
    ///   computation and value families respectively.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena, `head` included.
    /// - provides: the application node; whether the argument matches the
    ///   head's domain is a typing fact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.computation(head).is_some()
                && self.value(argument).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Application(left, right)) if left == head
                && right == argument),
    )]
    #[inline]
    pub fn computation_application(
        &mut self,
        head: ComputationId,
        argument: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Application(head, argument))
    }

    /// Mint a returner over an already-allocated value.
    ///
    /// # Specification
    /// - requires: `value` resolves in this arena's value family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the returner node. The child crosses families, so the two
    ///   ids share no allocation order and none is claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(value).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Return(actual)) if actual == value),
    )]
    #[inline]
    pub fn computation_return(
        &mut self,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Return(value))
    }

    /// Mint a bind over an already-allocated bound computation and body.
    ///
    /// # Specification
    /// - requires: `bound` and `body` resolve in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the sequencing node; the value `bound` returns is bound
    ///   positionally in `body`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.computation(bound).is_some()
                && self.computation(body).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Bind(left, right)) if left == bound
                && right == body),
    )]
    #[inline]
    pub fn computation_bind(
        &mut self,
        bound: ComputationId,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Bind(bound, body))
    }

    /// Mint a force over an already-allocated value.
    ///
    /// # Specification
    /// - requires: `value` resolves in this arena's value family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the force node. Whether `value` is a thunk is a typing fact,
    ///   and the child crosses families, so no id ordering is claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(value).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Force(actual)) if actual == value),
    )]
    #[inline]
    pub fn computation_force(
        &mut self,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Force(value))
    }

    /// Mint a case over an already-allocated scrutinee and two branches.
    ///
    /// # Specification
    /// - requires: `scrutinee`, `on_left`, and `on_right` resolve in this
    ///   arena, the scrutinee in its value family and the branches in its
    ///   computation family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both branch ids, which the precondition keeps live.
    /// - provides: the sum elimination; each branch is checked with the
    ///   injected value bound, which is a typing fact rather than a
    ///   representation one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(scrutinee).is_some()
                && self.computation(on_left).is_some()
                && self.computation(on_right).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations.saturating_add(1)
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.computations).unwrap_or(u32::MAX)
                && matches!(self.computations.last(), Some(&Computation::Case { scrutinee: actual, on_left: left, on_right: right }) if actual == scrutinee
                && left == on_left
                && right == on_right),
    )]
    #[inline]
    pub fn computation_case(
        &mut self,
        scrutinee: ValueId,
        on_left: ComputationId,
        on_right: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Case {
            scrutinee,
            on_left,
            on_right,
        })
    }

    /// Mint empty elimination over an already-allocated scrutinee.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_absurd(
        &mut self,
        scrutinee: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Absurd(scrutinee))
    }

    /// Mint the empty value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_empty(&mut self) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Empty)
    }

    // Value-type constructors.

    /// Mint a base value type.
    ///
    /// # Specification
    /// - requires: nothing; the base type is an inline payload.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the only way to obtain a [`ValueTypeId`] for a base type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Base(actual)) if actual == base),
    )]
    #[inline]
    pub fn value_type_base(
        &mut self,
        base: BaseType,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Base(base))
    }

    /// Mint the unit value type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the only way to obtain a [`ValueTypeId`] for the unit type.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Unit)),
    )]
    #[inline]
    pub fn value_type_unit(&mut self) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Unit)
    }

    /// Mint a product over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the product type, acyclic by construction.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(first).is_some()
                && self.value_type(second).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Product(left, right)) if left == first
                && right == second),
    )]
    #[inline]
    pub fn value_type_product(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Product(first, second))
    }

    /// Mint a sum over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the sum type, acyclic by construction; the summand order is
    ///   the order the two arguments are given in.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(first).is_some()
                && self.value_type(second).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Sum(left, right)) if left == first
                && right == second),
    )]
    #[inline]
    pub fn value_type_sum(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Sum(first, second))
    }

    /// Allocate the strictly positive list code over an element type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_list(
        &mut self,
        element: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::List(element))
    }

    /// Mint a thunk type over an already-allocated computation type.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena's computation-type family.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the thunk type `U C`. The child crosses families, so the two
    ///   ids share no allocation order and none is claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.comp_type(body).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Thunk(actual)) if actual == body),
    )]
    #[inline]
    pub fn value_type_thunk(
        &mut self,
        body: CompTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Thunk(body))
    }

    /// Mint the universe of one ground sort at a canonical level.
    ///
    /// # Specification
    /// - requires: `level` is a canonical level; the arena stores it as given.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the universe of `sort` at that level.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = (self.watermark(), level.constant_part()),
        ensures: |ret| self.values.len() == before.0.values
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types.saturating_add(1)
                && self.comp_types.len() == before.0.comp_types
                && ret.0 == u32::try_from(before.0.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Universe { sort: actual, ref level }) if actual == sort
                && level.constant_part() == before.1),
    )]
    #[inline]
    pub fn value_type_universe(
        &mut self,
        sort: GroundSort,
        level: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Universe { sort, level })
    }

    /// Mint a reference to a sealed abstract type by its declaration's
    /// admission position.
    ///
    /// Minting does not check the position: whether it names an admitted
    /// abstract-type declaration is a typing fact, so an unadmitted position is
    /// a rejection at the choke point rather than an unrepresentable node here.
    ///
    /// # Specification
    /// - requires: nothing; the admission position is checked at the choke
    ///   point rather than here.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the reference to a sealed abstract type, representable
    ///   whether or not the position is admitted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Abstract(actual)) if actual == atom),
    )]
    #[inline]
    pub fn value_type_abstract(
        &mut self,
        atom: ConstantIndex,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Abstract(atom))
    }

    /// Mint the type a code denotes, over an already-allocated code value,
    /// decoding a value quote on mint.
    ///
    /// Minting checks neither the code nor the level: that the code inhabits
    /// the value universe at `target` is a typing fact, so a mismatched pair is
    /// a rejection at the choke point rather than an unrepresentable node
    /// here. A code that is a quote is the one exception, because `El ⌜A⌝` is
    /// `A` by the decoding rule: the quoted type is returned and nothing is
    /// minted, whatever level was written, since the quoted type carries its
    /// own.
    ///
    /// # Specification
    /// - requires: `code` resolves in this arena's value family; whether it
    ///   inhabits the value universe at `target` is checked at the choke point.
    /// - ensures: when `code` is a value quote `⌜A⌝`, returns `A` and mints
    ///   nothing; otherwise appends the node and returns the value-type
    ///   family's length before the push, saturated at the `u32` ceiling; while
    ///   that length fits `u32` the id names the appended node and is greater
    ///   than every value-type id currently live in this arena.
    /// - provides: the type a code denotes, with its β-rule fired at the one
    ///   place a decode is made, so no arena ever holds the redex. The child
    ///   crosses families, so the two ids share no allocation order and none is
    ///   claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(code).is_some(), captures: before = (self.watermark(), match self.value(code) { Some(&Value::Quote(quoted)) => Some(quoted), _ => None }, target.constant_part()),
        ensures: |ret| match before.1 { Some(quoted) => ret == quoted
                && self.watermark() == before.0, None => self.values.len() == before.0.values
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types.saturating_add(1)
                && self.comp_types.len() == before.0.comp_types
                && ret.0 == u32::try_from(before.0.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Element { code: actual, ref target }) if actual == code
                && target.constant_part() == before.2) },
    )]
    #[inline]
    pub fn value_type_element(
        &mut self,
        code: ValueId,
        target: Level,
    ) -> ValueTypeId
    {
        if let Some(&Value::Quote(quoted)) = self.value(code) {
            return quoted;
        }
        self.alloc_value_type(ValueType::Element { code, target })
    }

    /// Mint a static Pi over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` resolve in this arena; whether both
    ///   are static classifiers is formation's to check.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the classifier of a type operator. Its codomain stands in
    ///   the ambient context, so the former binds nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(domain).is_some()
                && self.value_type(codomain).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types.saturating_add(1)
                && self.comp_types.len() == before.comp_types
                && ret.0 == u32::try_from(before.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::StaticPi { domain: left, codomain: right }) if left == domain
                && right == codomain),
    )]
    #[inline]
    pub fn value_type_static_pi(
        &mut self,
        domain: ValueTypeId,
        codomain: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::StaticPi { domain, codomain })
    }

    /// Mint a value-type lift over an already-allocated inner value type.
    ///
    /// # Specification
    /// - requires: `inner` resolves in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   `inner`, which the precondition keeps live.
    /// - provides: the written type-level lift; whether `inner`'s level sits
    ///   below `target` is a typing fact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(inner).is_some(), captures: before = (self.watermark(), target.constant_part()),
        ensures: |ret| self.values.len() == before.0.values
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types.saturating_add(1)
                && self.comp_types.len() == before.0.comp_types
                && ret.0 == u32::try_from(before.0.value_types).unwrap_or(u32::MAX)
                && matches!(self.value_types.last(), Some(&ValueType::Lift { inner: actual, ref target }) if actual == inner
                && target.constant_part() == before.1),
    )]
    #[inline]
    pub fn value_type_lift(
        &mut self,
        inner: ValueTypeId,
        target: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Lift { inner, target })
    }

    // Computation-type constructors.

    /// Mint a returner type over an already-allocated value type.
    ///
    /// # Specification
    /// - requires: `result` resolves in this arena's value-type family.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is greater than
    ///   every computation-type id currently live in this arena.
    /// - provides: the returner type `F A`. The child crosses families, so the
    ///   two ids share no allocation order and none is claimed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(result).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types.saturating_add(1)
                && ret.0 == u32::try_from(before.comp_types).unwrap_or(u32::MAX)
                && matches!(self.comp_types.last(), Some(&CompType::Returner(actual)) if actual == result),
    )]
    #[inline]
    pub fn comp_type_returner(
        &mut self,
        result: ValueTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Returner(result))
    }

    /// Mint an arrow type over an already-allocated domain and codomain.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` resolve in this arena, in its
    ///   value-type and computation-type families respectively.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is strictly
    ///   greater than `codomain`, which the precondition keeps live.
    /// - provides: the non-dependent arrow, where the codomain does not read
    ///   the domain's binder.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(domain).is_some()
                && self.comp_type(codomain).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types.saturating_add(1)
                && ret.0 == u32::try_from(before.comp_types).unwrap_or(u32::MAX)
                && matches!(self.comp_types.last(), Some(&CompType::Arrow { domain: left, codomain: right }) if left == domain
                && right == codomain),
    )]
    #[inline]
    pub fn comp_type_arrow(
        &mut self,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Arrow { domain, codomain })
    }

    /// Mint a dependent arrow over an already-allocated domain and a codomain
    /// scoped under the domain's binder.
    ///
    /// Minting does not check the scoping: whether the codomain reads the
    /// binder is a typing fact rather than a representation one, so a
    /// codomain that ignores it is representable here and is the producer's
    /// obligation rather than an unrepresentable node.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` resolve in this arena, in its
    ///   value-type and computation-type families respectively.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is strictly
    ///   greater than `codomain`, which the precondition keeps live.
    /// - provides: the dependent arrow. Whether the codomain reads the domain's
    ///   binder is the producer's obligation, not a representation one, so a
    ///   codomain that ignores it is still representable.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value_type(domain).is_some()
                && self.comp_type(codomain).is_some(), captures: before = self.watermark(),
        ensures: |ret| self.values.len() == before.values
                && self.computations.len() == before.computations
                && self.value_types.len() == before.value_types
                && self.comp_types.len() == before.comp_types.saturating_add(1)
                && ret.0 == u32::try_from(before.comp_types).unwrap_or(u32::MAX)
                && matches!(self.comp_types.last(), Some(&CompType::Pi { domain: left, codomain: right }) if left == domain
                && right == codomain),
    )]
    #[inline]
    pub fn comp_type_pi(
        &mut self,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Pi { domain, codomain })
    }

    /// Mint the computation type a code denotes, decoding a computation quote
    /// on mint.
    ///
    /// # Specification
    /// - requires: `code` resolves in this arena's value family; whether it
    ///   inhabits the computation universe at `target` is checked at the choke
    ///   point.
    /// - ensures: when `code` is a computation quote `⌜C⌝`, returns `C` and
    ///   mints nothing; otherwise appends the decode and returns the
    ///   computation-type family's length before the push, saturated at the
    ///   `u32` ceiling.
    /// - provides: the computation decode, with its β-rule fired at the one
    ///   place a decode is made, so no arena ever holds the redex.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[spec(
        requires: self.value(code).is_some(), captures: before = (self.watermark(), match self.value(code) { Some(&Value::QuoteComputation(quoted)) => Some(quoted), _ => None }, target.constant_part()),
        ensures: |ret| match before.1 { Some(quoted) => ret == quoted
                && self.watermark() == before.0, None => self.values.len() == before.0.values
                && self.computations.len() == before.0.computations
                && self.value_types.len() == before.0.value_types
                && self.comp_types.len() == before.0.comp_types.saturating_add(1)
                && ret.0 == u32::try_from(before.0.comp_types).unwrap_or(u32::MAX)
                && matches!(self.comp_types.last(), Some(&CompType::Element { code: actual, ref target }) if actual == code
                && target.constant_part() == before.2) },
    )]
    #[inline]
    pub fn comp_type_element(
        &mut self,
        code: ValueId,
        target: Level,
    ) -> CompTypeId
    {
        if let Some(&Value::QuoteComputation(quoted)) = self.value(code) {
            return quoted;
        }
        self.alloc_comp_type(CompType::Element { code, target })
    }

    /// Mint the native universe-path classifier over quoted codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_path_universe(
        &mut self,
        source: ValueId,
        target: ValueId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::PathUniverse(source, target))
    }

    /// Mint reflexivity without claiming that its code forms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_refl(
        &mut self,
        code: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::PathRefl(code))
    }

    /// Mint a componentwise product of universe paths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_product(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::PathProduct(first, second))
    }

    /// Mint an untrusted equivalence with portable round-trip evidence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_equiv(
        &mut self,
        path_type: ValueTypeId,
        forward: ValueId,
        backward: ValueId,
        evidence: alloc::sync::Arc<crate::PathEvidence>,
    ) -> ValueId
    {
        self.alloc_value(Value::PathEquiv {
            path_type,
            forward,
            backward,
            evidence,
        })
    }

    /// Mint transport; admission derives its source and result types.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_transport(
        &mut self,
        path: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Transport(path, value))
    }

    /// The immediate child references of `node`, in the order the format writes
    /// them.
    ///
    /// # Specification
    /// - requires: all family ids are admitted, including dangling ids.
    /// - ensures: returns exactly the resolved node’s children in wire-field
    ///   order, retaining their family and multiplicity; leaves and dangling
    ///   nodes return an empty vector.
    /// - provides: cross-family edges for the encoder, budget walk and arity
    ///   oracle. Numeric ordering applies only within a family, under the
    ///   constructor and truncation disciplines.
    /// - fails: never; a missing node has no observable children.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds all former families with distinguishable
    ///   children, nonzero levels and literal payloads, observes the exact
    ///   stored nodes and ordered edges, and checks each operation changes only
    ///   its own family length. Quote decoding covers matching, crossed and
    ///   non-quote codes without allocating an alias node. These distinguish
    ///   child permutations, payload loss, wrong-family minting and accidental
    ///   hash-consing; the probes are not a typing or arena-provenance proof.
    /// - witness: `arena::tests::ordered_edges_preserve_distinct_children_and_quote_boundaries`
    #[must_use]
    #[spec(ensures: |ret| match node {
        AnyNode::Value(id) => match self.value(id) {
            Some(&Value::Variable(_) | &Value::Constant(_) | &Value::Unit | &Value::Literal(_))
            | None => ret.is_empty(),
            Some(&Value::PathEquiv { path_type, forward, backward, .. }) =>
                ret.as_slice() == [AnyNode::ValueType(path_type), AnyNode::Value(forward), AnyNode::Value(backward)],
            Some(&Value::SessionPath { path_type, payload_paths, .. }) => ret.as_slice() == [AnyNode::ValueType(path_type), AnyNode::Value(payload_paths)],
            Some(&Value::PathRefl(code)) => ret.as_slice() == [AnyNode::Value(code)],
            Some(&Value::PathProduct(first, second) | &Value::Pair(first, second) | &Value::StaticApplication(first, second)) =>
                ret.as_slice() == [AnyNode::Value(first), AnyNode::Value(second)],
            Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) =>
                ret.as_slice() == [AnyNode::Value(body)],
            Some(&Value::Thunk(body)) => ret.as_slice() == [AnyNode::Computation(body)],
            Some(&Value::Quote(quoted)) => ret.as_slice() == [AnyNode::ValueType(quoted)],
            Some(&Value::QuoteComputation(quoted)) => ret.as_slice() == [AnyNode::CompType(quoted)],
        },
        AnyNode::Computation(id) => match self.computation(id) {
            None => ret.is_empty(),
            Some(&Computation::Transport(path, value)) => ret.as_slice() == [AnyNode::Value(path), AnyNode::Value(value)],
            Some(&Computation::Lambda(body)) => ret.as_slice() == [AnyNode::Computation(body)],
            Some(&Computation::Application(head, argument)) =>
                ret.as_slice() == [AnyNode::Computation(head), AnyNode::Value(argument)],
            Some(&Computation::Return(value) | &Computation::Force(value) | &Computation::Absurd(value)) =>
                ret.as_slice() == [AnyNode::Value(value)],
            Some(&Computation::Bind(bound, body)) =>
                ret.as_slice() == [AnyNode::Computation(bound), AnyNode::Computation(body)],
            Some(&Computation::Case { scrutinee, on_left, on_right }) =>
                ret.as_slice() == [
                    AnyNode::Value(scrutinee),
                    AnyNode::Computation(on_left),
                    AnyNode::Computation(on_right),
                ],
        },
        AnyNode::ValueType(id) => match self.value_type(id) {
            Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Empty | &ValueType::Universe { .. } | &ValueType::Abstract(_))
            | None => ret.is_empty(),
            Some(&ValueType::Product(first, second) | &ValueType::Sum(first, second)
                | &ValueType::StaticPi { domain: first, codomain: second }) =>
                ret.as_slice() == [AnyNode::ValueType(first), AnyNode::ValueType(second)],
            Some(&ValueType::Session { payloads, .. }) => ret.as_slice() == [AnyNode::ValueType(payloads)],
            Some(&ValueType::PathUniverse(source, target)) => ret.as_slice() == [AnyNode::Value(source), AnyNode::Value(target)],
            Some(&ValueType::Thunk(body)) => ret.as_slice() == [AnyNode::CompType(body)],
            Some(&ValueType::Lift { inner, .. } | &ValueType::List(inner)) => ret.as_slice() == [AnyNode::ValueType(inner)],
            Some(&ValueType::Element { code, .. }) => ret.as_slice() == [AnyNode::Value(code)],
        },
        AnyNode::CompType(id) => match self.comp_type(id) {
            None => ret.is_empty(),
            Some(&CompType::Returner(result)) => ret.as_slice() == [AnyNode::ValueType(result)],
            Some(&CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain }) =>
                ret.as_slice() == [AnyNode::ValueType(domain), AnyNode::CompType(codomain)],
            Some(&CompType::Element { code, .. }) => ret.as_slice() == [AnyNode::Value(code)],
        },
    })]
    pub(crate) fn children_of(
        &self,
        node: AnyNode,
    ) -> Vec<AnyNode>
    {
        let mut children: Vec<AnyNode> = Vec::new();
        match node {
            | AnyNode::Value(id) => match self.value(id) {
                | Some(
                    &Value::Variable(_) | &Value::Constant(_) | &Value::Unit | &Value::Literal(_),
                )
                | None => {},
                | Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    children.push(AnyNode::ValueType(path_type));
                    children.push(AnyNode::Value(forward));
                    children.push(AnyNode::Value(backward));
                },
                | Some(&Value::SessionPath {
                    path_type,
                    payload_paths,
                    ..
                }) => {
                    children.push(AnyNode::ValueType(path_type));
                    children.push(AnyNode::Value(payload_paths));
                },
                | Some(&Value::PathRefl(code)) => children.push(AnyNode::Value(code)),
                | Some(
                    &Value::PathProduct(first, second)
                    | &Value::Pair(first, second)
                    | &Value::StaticApplication(first, second),
                ) => {
                    children.push(AnyNode::Value(first));
                    children.push(AnyNode::Value(second));
                },
                | Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                    children.push(AnyNode::Value(body));
                },
                | Some(&Value::Thunk(body)) => children.push(AnyNode::Computation(body)),
                | Some(&Value::Quote(quoted)) => children.push(AnyNode::ValueType(quoted)),
                | Some(&Value::QuoteComputation(quoted)) => {
                    children.push(AnyNode::CompType(quoted));
                },
            },
            | AnyNode::Computation(id) => match self.computation(id) {
                | None => {},
                | Some(&Computation::Transport(path, value)) => {
                    children.push(AnyNode::Value(path));
                    children.push(AnyNode::Value(value));
                },
                | Some(&Computation::Lambda(body)) => children.push(AnyNode::Computation(body)),
                | Some(&Computation::Application(head, argument)) => {
                    children.push(AnyNode::Computation(head));
                    children.push(AnyNode::Value(argument));
                },
                | Some(
                    &Computation::Return(value)
                    | &Computation::Force(value)
                    | &Computation::Absurd(value),
                ) => {
                    children.push(AnyNode::Value(value));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    children.push(AnyNode::Computation(bound));
                    children.push(AnyNode::Computation(body));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    children.push(AnyNode::Value(scrutinee));
                    children.push(AnyNode::Computation(on_left));
                    children.push(AnyNode::Computation(on_right));
                },
            },
            | AnyNode::ValueType(id) => match self.value_type(id) {
                | Some(
                    &ValueType::Base(_)
                    | &ValueType::Unit
                    | &ValueType::Empty
                    | &ValueType::Universe { .. }
                    | &ValueType::Abstract(_),
                )
                | None => {},
                | Some(
                    &ValueType::Product(first, second)
                    | &ValueType::Sum(first, second)
                    | &ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    },
                ) => {
                    children.push(AnyNode::ValueType(first));
                    children.push(AnyNode::ValueType(second));
                },
                | Some(&ValueType::Session { payloads, .. }) => {
                    children.push(AnyNode::ValueType(payloads));
                },
                | Some(&ValueType::PathUniverse(source, target)) => {
                    children.push(AnyNode::Value(source));
                    children.push(AnyNode::Value(target));
                },
                | Some(&ValueType::Thunk(body)) => children.push(AnyNode::CompType(body)),
                | Some(&ValueType::Lift { inner, .. } | &ValueType::List(inner)) => {
                    children.push(AnyNode::ValueType(inner));
                },
                // The one edge that leaves the type language: a code is a value,
                // which is what lets a type mention a bound variable at all.
                | Some(&ValueType::Element { code, .. }) => children.push(AnyNode::Value(code)),
            },
            | AnyNode::CompType(id) => match self.comp_type(id) {
                | None => {},
                | Some(&CompType::Returner(result)) => children.push(AnyNode::ValueType(result)),
                | Some(
                    &CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain },
                ) => {
                    children.push(AnyNode::ValueType(domain));
                    children.push(AnyNode::CompType(codomain));
                },
                | Some(&CompType::Element { code, .. }) => children.push(AnyNode::Value(code)),
            },
        }
        children
    }
}

#[cfg(test)]
mod tests
{
    use super::AnyNode;
    use super::ArenaWatermark;
    use super::TermArena;
    use super::ValueId;

    #[test]
    fn scalar_clamps_and_index_ceilings_match_widened_models()
    {
        let selected = const {
            [
                crate::decl::DeclarationContent::Def {
                    declared: super::ValueTypeId(7),
                    body: ValueId(99),
                }
                .declared_id()
                .0,
                crate::decl::DeclarationContent::Axiom {
                    declared: super::ValueTypeId(11),
                }
                .declared_id()
                .0,
                crate::decl::DeclarationContent::AbstractType {
                    kind: super::ValueTypeId(17),
                }
                .declared_id()
                .0,
            ]
        };
        assert_eq!(selected, [7_u32, 11, 17]);
        let lengths = [0_usize, 1, 7, usize::MAX.saturating_sub(1), usize::MAX];
        for value in lengths {
            for low in lengths {
                for high in lengths {
                    let model = if low > high {
                        low
                    }
                    else {
                        value.clamp(low, high)
                    };
                    assert_eq!(
                        super::clamp_length(
                            super::ArenaLength(value),
                            super::ArenaLength(low),
                            super::ArenaLength(high)
                        )
                        .0,
                        model
                    );
                    let input = ArenaWatermark {
                        values: value,
                        computations: low,
                        value_types: high,
                        comp_types: usize::MAX.saturating_sub(value),
                    };
                    let floor = ArenaWatermark {
                        values: low,
                        computations: high,
                        value_types: value,
                        comp_types: 0,
                    };
                    let ceiling = ArenaWatermark {
                        values: high,
                        computations: value,
                        value_types: low,
                        comp_types: usize::MAX,
                    };
                    let actual = input.clamped_into(floor, ceiling);
                    for (observed, scalar, lower, upper) in [
                        (actual.values, input.values, floor.values, ceiling.values),
                        (
                            actual.computations,
                            input.computations,
                            floor.computations,
                            ceiling.computations,
                        ),
                        (
                            actual.value_types,
                            input.value_types,
                            floor.value_types,
                            ceiling.value_types,
                        ),
                        (
                            actual.comp_types,
                            input.comp_types,
                            floor.comp_types,
                            ceiling.comp_types,
                        ),
                    ] {
                        assert_eq!(
                            observed,
                            if lower > upper {
                                lower
                            }
                            else {
                                scalar.clamp(lower, upper)
                            }
                        );
                    }
                }
            }
        }
        for length in lengths
            .into_iter()
            .chain([usize::try_from(u32::MAX).unwrap_or(usize::MAX)])
        {
            let widened = u128::try_from(length).expect("host lengths fit u128");
            assert_eq!(
                u128::from(super::id_index(super::ArenaLength(length)).0),
                widened.min(u128::from(u32::MAX))
            );
        }
        for index in [0_u32, 1, u32::MAX.saturating_sub(1), u32::MAX] {
            let observed = super::id_offset(super::ArenaIndex(index)).0;
            assert_eq!(
                u128::try_from(observed).expect("host offsets fit u128"),
                u128::from(index).min(u128::try_from(usize::MAX).expect("host ceiling fits u128"))
            );
        }
    }

    #[test]
    fn truncation_preserves_prefixes_reuses_indices_and_checks_all_families()
    {
        let mut arena = TermArena::new();
        let value = arena.value_variable(super::DeBruijnIndex::from(3_u32));
        let computation = arena.computation_return(value);
        let value_type = arena.value_type_base(super::BaseType::Integer);
        let comp_type = arena.comp_type_returner(value_type);
        let kept = arena.clone();
        let low = arena.watermark();
        let removed_value = arena.value_unit();
        let removed_computation = arena.computation_force(value);
        let removed_value_type = arena.value_type_unit();
        let removed_comp_type = arena.comp_type_arrow(value_type, comp_type);
        let stale = arena.watermark();
        arena.truncate_to(low);
        assert_eq!(arena, kept);
        assert_eq!(arena.value(removed_value), None);
        assert_eq!(arena.computation(removed_computation), None);
        assert_eq!(arena.value_type(removed_value_type), None);
        assert_eq!(arena.comp_type(removed_comp_type), None);
        for node in [
            AnyNode::Value(removed_value),
            AnyNode::Computation(removed_computation),
            AnyNode::ValueType(removed_value_type),
            AnyNode::CompType(removed_comp_type),
        ] {
            assert_eq!(arena.children_of(node), alloc::vec![]);
        }
        arena.truncate_to(stale);
        assert_eq!(arena, kept, "a stale high mark cannot grow a family");
        assert_eq!(
            arena.value_variable(super::DeBruijnIndex::from(9_u32)),
            removed_value
        );
        assert_eq!(arena.computation_lambda(computation), removed_computation);
        assert_eq!(
            arena.value_type_base(super::BaseType::String),
            removed_value_type
        );
        assert_eq!(arena.comp_type_pi(value_type, comp_type), removed_comp_type);
        assert_eq!(
            arena.value(removed_value),
            Some(&super::Value::Variable(super::DeBruijnIndex::from(9_u32)))
        );
        assert_eq!(
            arena.computation(removed_computation),
            Some(&super::Computation::Lambda(computation))
        );
        assert_eq!(
            arena.value_type(removed_value_type),
            Some(&super::ValueType::Base(super::BaseType::String))
        );
        assert_eq!(
            arena.comp_type(removed_comp_type),
            Some(&super::CompType::Pi {
                domain: value_type,
                codomain: comp_type
            })
        );
        let mut foreign = TermArena::new();
        let foreign_value = foreign.value_unit();
        let foreign_computation = foreign.computation_force(foreign_value);
        let foreign_value_type = foreign.value_type_unit();
        let foreign_comp_type = foreign.comp_type_returner(foreign_value_type);
        assert_eq!(arena.value(foreign_value), kept.value(value));
        assert_eq!(
            arena.computation(foreign_computation),
            kept.computation(computation)
        );
        assert_eq!(
            arena.value_type(foreign_value_type),
            kept.value_type(value_type)
        );
        assert_eq!(
            arena.comp_type(foreign_comp_type),
            kept.comp_type(comp_type)
        );
        arena.truncate_to(ArenaWatermark::default());
        assert_eq!(arena, TermArena::new());
    }

    #[test]
    fn ordered_edges_preserve_distinct_children_and_quote_boundaries()
    {
        use super::CompType;
        use super::Computation;
        use super::GroundSort;
        use super::Value;
        use super::ValueType;

        let mut arena = TermArena::new();
        let v0 = arena.value_variable(super::DeBruijnIndex::from(u32::MAX));
        let v1 = arena.value_variable(super::DeBruijnIndex::from(7_u32));
        let c0 = arena.computation_return(v0);
        let c1 = arena.computation_force(v1);
        let t0 = arena.value_type_unit();
        let t1 = arena.value_type_base(super::BaseType::Integer);
        let k0 = arena.comp_type_returner(t0);
        let k1 = arena.comp_type_returner(t1);
        assert_eq!(arena.watermark(), ArenaWatermark {
            values: 2,
            computations: 2,
            value_types: 2,
            comp_types: 2
        });
        let level =
            gandr_kernel_strata::Level::constant(gandr_kernel_strata::LevelConstant::from(7_u64))
                .max(&gandr_kernel_strata::Level::var(
                    gandr_kernel_strata::LevelVar::new(gandr_kernel_strata::LevelVarIndex::from(
                        2_u32,
                    )),
                ));
        let literal = super::Literal::Text(crate::base::StringLiteral::new(
            alloc::string::String::from("a\0é"),
        ));
        let start = arena.watermark();
        let values: &[(super::ValueId, Value, &[AnyNode])] = &[
            (
                arena.value_variable(super::DeBruijnIndex::from(u32::MAX)),
                Value::Variable(super::DeBruijnIndex::from(u32::MAX)),
                &[],
            ),
            (
                arena.value_constant(super::ConstantIndex::from(usize::MAX)),
                Value::Constant(super::ConstantIndex::from(usize::MAX)),
                &[],
            ),
            (arena.value_unit(), Value::Unit, &[]),
            (
                arena.value_literal(literal.clone()),
                Value::Literal(literal),
                &[],
            ),
            (arena.value_pair(v0, v1), Value::Pair(v0, v1), &[
                AnyNode::Value(v0),
                AnyNode::Value(v1),
            ]),
            (
                arena.value_injection(super::Side::Left, v0),
                Value::Injection(super::Side::Left, v0),
                &[AnyNode::Value(v0)],
            ),
            (
                arena.value_injection(super::Side::Right, v1),
                Value::Injection(super::Side::Right, v1),
                &[AnyNode::Value(v1)],
            ),
            (arena.value_thunk(c1), Value::Thunk(c1), &[
                AnyNode::Computation(c1),
            ]),
            (
                arena.value_lift(level.clone(), v1),
                Value::Lift {
                    target: level.clone(),
                    body: v1,
                },
                &[AnyNode::Value(v1)],
            ),
            (arena.value_quote(t1), Value::Quote(t1), &[
                AnyNode::ValueType(t1),
            ]),
            (
                arena.value_quote_computation(k1),
                Value::QuoteComputation(k1),
                &[AnyNode::CompType(k1)],
            ),
            (
                arena.value_static_application(v0, v1),
                Value::StaticApplication(v0, v1),
                &[AnyNode::Value(v0), AnyNode::Value(v1)],
            ),
        ];
        for (offset, &(id, ref expected, children)) in values.iter().enumerate() {
            assert_eq!(
                usize::try_from(id.0).expect("small id"),
                start.values.saturating_add(offset)
            );
            assert_eq!(arena.value(id), Some(expected));
            assert_eq!(arena.children_of(AnyNode::Value(id)).as_slice(), children);
        }
        assert_eq!(arena.watermark(), ArenaWatermark {
            values: start.values.saturating_add(values.len()),
            ..start
        });
        let start = arena.watermark();
        let computations: &[(super::ComputationId, Computation, &[AnyNode])] = &[
            (arena.computation_lambda(c1), Computation::Lambda(c1), &[
                AnyNode::Computation(c1),
            ]),
            (
                arena.computation_application(c0, v1),
                Computation::Application(c0, v1),
                &[AnyNode::Computation(c0), AnyNode::Value(v1)],
            ),
            (arena.computation_return(v1), Computation::Return(v1), &[
                AnyNode::Value(v1),
            ]),
            (
                arena.computation_bind(c0, c1),
                Computation::Bind(c0, c1),
                &[AnyNode::Computation(c0), AnyNode::Computation(c1)],
            ),
            (arena.computation_force(v0), Computation::Force(v0), &[
                AnyNode::Value(v0),
            ]),
            (
                arena.computation_case(v1, c0, c1),
                Computation::Case {
                    scrutinee: v1,
                    on_left: c0,
                    on_right: c1,
                },
                &[
                    AnyNode::Value(v1),
                    AnyNode::Computation(c0),
                    AnyNode::Computation(c1),
                ],
            ),
        ];
        for (offset, &(id, ref expected, children)) in computations.iter().enumerate() {
            assert_eq!(
                usize::try_from(id.0).expect("small id"),
                start.computations.saturating_add(offset)
            );
            assert_eq!(arena.computation(id), Some(expected));
            assert_eq!(
                arena.children_of(AnyNode::Computation(id)).as_slice(),
                children
            );
        }
        assert_eq!(arena.watermark(), ArenaWatermark {
            computations: start.computations.saturating_add(computations.len()),
            ..start
        });
        let start = arena.watermark();
        let value_types: &[(super::ValueTypeId, ValueType, &[AnyNode])] = &[
            (
                arena.value_type_base(super::BaseType::String),
                ValueType::Base(super::BaseType::String),
                &[],
            ),
            (arena.value_type_unit(), ValueType::Unit, &[]),
            (
                arena.value_type_product(t0, t1),
                ValueType::Product(t0, t1),
                &[AnyNode::ValueType(t0), AnyNode::ValueType(t1)],
            ),
            (arena.value_type_sum(t1, t0), ValueType::Sum(t1, t0), &[
                AnyNode::ValueType(t1),
                AnyNode::ValueType(t0),
            ]),
            (arena.value_type_thunk(k1), ValueType::Thunk(k1), &[
                AnyNode::CompType(k1),
            ]),
            (
                arena.value_type_universe(GroundSort::Value, level.clone()),
                ValueType::Universe {
                    sort: GroundSort::Value,
                    level: level.clone(),
                },
                &[],
            ),
            (
                arena.value_type_universe(GroundSort::Computation, level.clone()),
                ValueType::Universe {
                    sort: GroundSort::Computation,
                    level: level.clone(),
                },
                &[],
            ),
            (
                arena.value_type_abstract(super::ConstantIndex::from(usize::MAX)),
                ValueType::Abstract(super::ConstantIndex::from(usize::MAX)),
                &[],
            ),
            (
                arena.value_type_element(v1, level.clone()),
                ValueType::Element {
                    code: v1,
                    target: level.clone(),
                },
                &[AnyNode::Value(v1)],
            ),
            (
                arena.value_type_static_pi(t0, t1),
                ValueType::StaticPi {
                    domain: t0,
                    codomain: t1,
                },
                &[AnyNode::ValueType(t0), AnyNode::ValueType(t1)],
            ),
            (
                arena.value_type_lift(t1, level.clone()),
                ValueType::Lift {
                    inner: t1,
                    target: level.clone(),
                },
                &[AnyNode::ValueType(t1)],
            ),
        ];
        for (offset, &(id, ref expected, children)) in value_types.iter().enumerate() {
            assert_eq!(
                usize::try_from(id.0).expect("small id"),
                start.value_types.saturating_add(offset)
            );
            assert_eq!(arena.value_type(id), Some(expected));
            assert_eq!(
                arena.children_of(AnyNode::ValueType(id)).as_slice(),
                children
            );
        }
        assert_eq!(arena.watermark(), ArenaWatermark {
            value_types: start.value_types.saturating_add(value_types.len()),
            ..start
        });
        let start = arena.watermark();
        let comp_types: &[(super::CompTypeId, CompType, &[AnyNode])] = &[
            (arena.comp_type_returner(t1), CompType::Returner(t1), &[
                AnyNode::ValueType(t1),
            ]),
            (
                arena.comp_type_arrow(t0, k1),
                CompType::Arrow {
                    domain: t0,
                    codomain: k1,
                },
                &[AnyNode::ValueType(t0), AnyNode::CompType(k1)],
            ),
            (
                arena.comp_type_pi(t1, k0),
                CompType::Pi {
                    domain: t1,
                    codomain: k0,
                },
                &[AnyNode::ValueType(t1), AnyNode::CompType(k0)],
            ),
            (
                arena.comp_type_element(v0, level.clone()),
                CompType::Element {
                    code: v0,
                    target: level.clone(),
                },
                &[AnyNode::Value(v0)],
            ),
        ];
        for (offset, &(id, ref expected, children)) in comp_types.iter().enumerate() {
            assert_eq!(
                usize::try_from(id.0).expect("small id"),
                start.comp_types.saturating_add(offset)
            );
            assert_eq!(arena.comp_type(id), Some(expected));
            assert_eq!(
                arena.children_of(AnyNode::CompType(id)).as_slice(),
                children
            );
        }
        assert_eq!(arena.watermark(), ArenaWatermark {
            comp_types: start.comp_types.saturating_add(comp_types.len()),
            ..start
        });
        let quote = arena.value_quote(t0);
        let quote_computation = arena.value_quote_computation(k0);
        let before = arena.watermark();
        assert_eq!(
            arena.value_type_element(quote, gandr_kernel_strata::Level::zero()),
            t0
        );
        assert_eq!(
            arena.comp_type_element(quote_computation, gandr_kernel_strata::Level::zero()),
            k0
        );
        assert_eq!(
            arena.watermark(),
            before,
            "matching quotes discard the written target without minting"
        );
        let crossed = arena.comp_type_element(quote, level.clone());
        assert_eq!(
            arena.comp_type(crossed),
            Some(&CompType::Element {
                code: quote,
                target: level.clone()
            })
        );
        assert_eq!(arena.watermark(), ArenaWatermark {
            comp_types: before.comp_types.saturating_add(1),
            ..before
        });
        let before = arena.watermark();
        let crossed = arena.value_type_element(quote_computation, level.clone());
        assert_eq!(
            arena.value_type(crossed),
            Some(&ValueType::Element {
                code: quote_computation,
                target: level
            })
        );
        assert_eq!(arena.watermark(), ArenaWatermark {
            value_types: before.value_types.saturating_add(1),
            ..before
        });
    }

    #[test]
    fn a_child_id_is_strictly_below_its_parent()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_pair(unit, unit);
        assert!(
            unit < pair,
            "constructor-only minting orders child below parent"
        );
    }

    #[test]
    fn truncating_to_a_watermark_drops_later_nodes()
    {
        let mut arena = TermArena::new();
        let kept = arena.value_unit();
        let mark = arena.watermark();
        let dropped = arena.value_unit();
        arena.truncate_to(mark);
        assert!(
            arena.value(kept).is_some(),
            "content below the mark survives"
        );
        assert!(
            arena.value(dropped).is_none(),
            "an id minted past the mark dangles after truncation"
        );
        arena.truncate_to(mark);
        assert!(
            arena.value(kept).is_some(),
            "truncating twice to the same mark is a no-op"
        );
    }

    #[test]
    fn a_watermark_clamps_into_its_interval()
    {
        let mut arena = TermArena::new();
        let low = arena.watermark();
        let _first = arena.value_unit();
        let middle = arena.watermark();
        let _second = arena.value_unit();
        let high = arena.watermark();

        assert_eq!(
            low,
            low.clamped_into(low, high),
            "a mark at the floor holds"
        );
        assert_eq!(
            middle,
            middle.clamped_into(low, high),
            "a mark inside the interval holds"
        );
        assert_eq!(
            middle,
            high.clamped_into(low, middle),
            "a mark above the ceiling clamps down"
        );
        assert_eq!(
            middle,
            low.clamped_into(middle, high),
            "a mark below the floor clamps up"
        );
        assert_eq!(
            high,
            middle.clamped_into(high, low),
            "an inverted interval resolves to its floor"
        );
    }

    #[test]
    fn a_dangling_node_has_no_children()
    {
        let arena = TermArena::new();
        let dangling = AnyNode::Value(ValueId(7));
        assert!(
            arena.children_of(dangling).is_empty(),
            "an unresolvable id yields no children rather than panicking"
        );
    }

    #[test]
    fn the_default_watermark_is_the_empty_arena()
    {
        let arena = TermArena::new();
        assert_eq!(
            ArenaWatermark::default(),
            arena.watermark(),
            "an empty arena sits at the admission floor"
        );
    }

    #[test]
    fn a_decoded_quote_is_the_quoted_type()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_type_unit();
        let quote = arena.value_quote(unit);
        let level = gandr_kernel_strata::Level::zero();
        assert_eq!(
            unit,
            arena.value_type_element(quote, level.clone()),
            "a value decode of a value quote is the quoted type itself"
        );
        let returner = arena.comp_type_returner(unit);
        let quoted = arena.value_quote_computation(returner);
        assert_eq!(
            returner,
            arena.comp_type_element(quoted, level.clone()),
            "and a computation decode of a computation quote is the quoted computation type"
        );
        let crossed = arena.comp_type_element(quote, level);
        assert!(
            matches!(
                arena.comp_type(crossed),
                Some(&super::CompType::Element { code, .. }) if code == quote
            ),
            "while a decode across the families is minted as written, for the checker to refuse"
        );
    }
}
