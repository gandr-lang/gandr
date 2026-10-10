//! The term language: [`Value`] on the positive side and [`Computation`] on the
//! negative side, together with the reference forms [`DeBruijnIndex`] and
//! [`ConstantIndex`] and the injection [`Side`].
//!
//! Terms are nameless. A bound value variable is a [`DeBruijnIndex`] counting
//! binders outward from its use site, so α-equivalence is syntactic identity
//! and no name capture is representable. A [`Value::Constant`] names a prior
//! declaration by its admission position.
//!
//! The vocabulary is closed: no hole, metavariable, mark, annotation, effect
//! row, handler, or control operator exists to be represented.
//!
//! # Children are ids, and the derived relations are shallow
//!
//! A node's children are typed arena ids ([`ValueId`], [`ComputationId`])
//! rather than owned pointers; leaf payloads stay inline. Because an id is
//! `Copy`, the derived `Clone`, `Drop`, `PartialEq`, `Eq` and `Hash` are
//! **shallow** — they do not walk term depth — which is what retires the
//! hand-written iterative destructor an owned-tree representation needs and
//! makes arena teardown a flat vector drop.
//!
//! **The derived equality is child-id equality, not structural equality.** Two
//! structurally equal subterms need not share an id, because the kernel
//! preserves the sharing a decode handed it and never creates more. Every use
//! site therefore either compares only inline leaf payloads or resolves ids
//! explicitly; the format's deduplication is keyed on encoded content, never on
//! a node's derived equality.
//!
//! [`ValueId`]: crate::ValueId
//! [`ComputationId`]: crate::ComputationId

use anodized::spec;
use gandr_kernel_strata::Level;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::Literal;

/// A bound value variable, as a de Bruijn index counting binders outward: `0`
/// is the nearest enclosing binder.
///
/// # Specification
/// - requires: all u32 distances are representable; binder scope is checked by
///   admission.
/// - ensures: carries a binder distance distinct from a declaration position.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeBruijnIndex(u32);

impl From<u32> for DeBruijnIndex
{
    /// The index for a binder distance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<DeBruijnIndex> for u32
{
    /// The binder distance the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: DeBruijnIndex) -> Self
    {
        index.0
    }
}

/// A reference to a prior declaration by its admission position, where `0` is
/// the first admitted declaration.
///
/// An admission position and a subterm-table index are two different things
/// that both spell as an integer, and confusing them is the format's most
/// available mistake; the wrapper is what stops one being passed where the
/// other belongs.
///
/// # Specification
/// - requires: all host positions are representable; declaration existence is
///   checked by admission.
/// - ensures: carries a declaration position distinct from a binder distance
///   and a wire-table index.
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstantIndex(usize);

impl From<usize> for ConstantIndex
{
    /// The index for an admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ConstantIndex> for usize
{
    /// The admission position the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ConstantIndex) -> Self
    {
        index.0
    }
}

/// The side of a sum injection.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// The left injection, into the left summand of `A + B`.
    Left,
    /// The right injection, into the right summand of `A + B`.
    Right,
}

/// A value: the positive fragment of the term vocabulary.
///
/// Values are the total, thunkable half of the polarity split. No value
/// constructor introduces a computation effect; the only value embedding a
/// computation is [`Self::Thunk`], and a thunk suspends rather than runs it.
///
/// # Specification
/// - requires: payload types are well formed; typing, live-child resolution and
///   scoping are external obligations.
/// - ensures: retains the selected positive former and its typed child ids;
///   derived equality compares child ordinals rather than recursively comparing
///   graphs.
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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Value
{
    /// A session bisimulation inhabiting a native `Path_U` classifier.
    SessionPath
    {
        /// Source and target session codes.
        path_type: ValueTypeId,
        /// Finite untrusted relation, replayed at formation.
        evidence: alloc::sync::Arc<crate::session::Evidence>,
        /// Native payload-path tuple, terminated by Unit.
        payload_paths: ValueId,
    },
    /// Reflexivity at a quoted closed first-order or session code.
    PathRefl(ValueId),
    /// A componentwise path between product codes.
    PathProduct(ValueId, ValueId),
    /// An equivalence whose round trips are replayed during formation.
    PathEquiv
    {
        /// The native universe-path classifier.
        path_type: ValueTypeId,
        /// The closed forward translator.
        forward: ValueId,
        /// The closed backward translator.
        backward: ValueId,
        /// Untrusted dialogue data, never a formation verdict.
        evidence: alloc::sync::Arc<PathEvidence>,
    },
    /// A bound value variable.
    Variable(DeBruijnIndex),
    /// A reference to a prior declaration.
    Constant(ConstantIndex),
    /// The unique inhabitant of the unit type.
    Unit,
    /// A base-type literal.
    Literal(Literal),
    /// A pair, introducing the product `A × B`.
    Pair(ValueId, ValueId),
    /// A sum injection, introducing `A + B` on the given side.
    Injection(Side, ValueId),
    /// A thunk, suspending a computation into the value type `U C`.
    Thunk(ComputationId),
    /// An explicit universe lift: given `body : A` with `A`'s level strictly
    /// below `target`, this value inhabits `Lift A target`.
    ///
    /// The lift is written, never inferred: a bare `body : A` does not inhabit
    /// `Lift A target` on its own, because there is no implicit cumulativity.
    Lift
    {
        /// The target universe level of the lift.
        target: Level,
        /// The value being lifted.
        body: ValueId,
    },
    /// The code of a value type: `⌜A⌝`, an inhabitant of the value universe at
    /// `A`'s level.
    Quote(ValueTypeId),
    /// The code of a computation type: `⌜C⌝`, an inhabitant of the
    /// computation universe at `C`'s level.
    QuoteComputation(CompTypeId),
    /// A static application `F a` of a type operator to a code: an inhabitant
    /// of the static Pi's codomain at the head's classifier.
    ///
    /// The vocabulary has no static lambda, so a static application is always
    /// neutral: its head is a constant or a variable, possibly under further
    /// static applications, and nothing reduces it. A static lambda a producer
    /// wrote is normalized away before export.
    StaticApplication(ValueId, ValueId),
}

/// A computation: the negative fragment of the term vocabulary.
///
/// The eliminators — application, force, bind, case — synthesize; the
/// introductions — lambda, return — check against an expected computation type.
///
/// # Specification
/// - requires: payload types are well formed; typing, live-child resolution and
///   scoping are external obligations.
/// - ensures: retains the selected negative former and its typed child ids;
///   derived equality compares child ordinals rather than recursively comparing
///   graphs.
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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Computation
{
    /// Empty elimination: checks against any computation type when its
    /// scrutinee checks at Empty. There is no beta rule.
    Absurd(ValueId),
    /// A lambda `λ. M`, binding one value variable; introduces `A → C`.
    Lambda(ComputationId),
    /// An application `M v` of a computation to a value argument.
    Application(ComputationId, ValueId),
    /// A returner `return v`, introducing `F A`.
    Return(ValueId),
    /// A sequencing bind `x ← M; N`, binding the value `M` returns into `N`.
    Bind(ComputationId, ComputationId),
    /// A force `force v` of a thunk value `v : U C`, running it as `C`.
    Force(ValueId),
    /// A sum elimination, binding the injected value into each branch.
    Case
    {
        /// The scrutinee value, of a sum type.
        scrutinee: ValueId,
        /// The left branch, checked with the left summand bound.
        on_left: ComputationId,
        /// The right branch, checked with the right summand bound.
        on_right: ComputationId,
    },
    /// Transport a value along a universe path.
    Transport(ValueId, ValueId),
}

/// Portable round-trip dialogues for closed universe-path translators.
///
/// # Specification
/// - provides: source and target traces in constructor-pattern order. Unit
///   anchors carry no arena identity; the kernel reconstructs every boundary.
///   Evidence participates in content identity but not certificate conversion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — artifact framing retains both ordered dialogue lists,
///   including empty dialogues and the full portable decision alphabet.
/// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct PathEvidence
{
    /// Backward after forward, once for every source constructor pattern.
    pub source:
        alloc::vec::Vec<alloc::vec::Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>>,
    /// Forward after backward, once for every target constructor pattern.
    pub target:
        alloc::vec::Vec<alloc::vec::Vec<gandr_kernel_conversion_trace::ConversionDecision<()>>>,
}

/// One canonical unsigned word of portable path evidence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvidenceWord(pub u64);

impl TryFrom<EvidenceWord> for gandr_kernel_conversion_trace::ConversionDecision<()>
{
    type Error = crate::MalformedSite;

    /// Decode the portable decision alphabet, rejecting oversized premises.
    ///
    /// # Specification
    /// - ensures: accepts exactly the tagged decision words produced by
    ///   `decision_word`.
    /// - fails: `PathEvidence` for an unknown tag or a premise exceeding u32.
    /// - panics: none.
    ///
    /// # Errors
    /// Malformed path evidence.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unknown tags and oversized premise positions are
    ///   refused.
    /// - witness: `term::tests::evidence_words_reject_unknown_and_oversized_premises`
    #[inline]
    #[spec(ensures: |ret| {
        ret.is_ok() == (word.0 <= 0x0B_u64 ||
            (word.0 & 0xFF_u64 == 0x0C_u64 && u32::try_from(word.0 >> 8_u32).is_ok()))
    })]
    fn try_from(word: EvidenceWord) -> Result<Self, Self::Error>
    {
        use gandr_kernel_conversion_trace::ConversionSide;
        let invalid = crate::MalformedSite::PathEvidence;
        Ok(match word.0 {
            | 0 => Self::ReduceLeft { redex: () },
            | 1 => Self::ReduceRight { redex: () },
            | 2 => Self::ConstShortcut { constant: () },
            | 3 => Self::Unfold { constant: () },
            | 4 => Self::Postpone { constant: () },
            | 5 => Self::Freeze {
                constant: (),
                side: ConversionSide::Left,
            },
            | 6 => Self::Freeze {
                constant: (),
                side: ConversionSide::Right,
            },
            | 7 => Self::EtaExpand {
                variable: (),
                side: ConversionSide::Left,
            },
            | 8 => Self::EtaExpand {
                variable: (),
                side: ConversionSide::Right,
            },
            | 9 => Self::Force { thunk: () },
            | 10 => Self::ComparedShared {
                left: (),
                right: (),
            },
            | 11 => Self::Decompose,
            | value if value & 0xFF_u64 == 0x0C_u64 => {
                let position = u32::try_from(value >> 8_u32).map_err(|_error| invalid)?;
                Self::NegativeSubgoal {
                    position: position.into(),
                }
            },
            | _ => return Err(invalid),
        })
    }
}

impl PathEvidence
{
    /// Stream the canonical evidence payload without allocating an image.
    ///
    /// # Specification
    /// - requires: nothing; evidence is still untrusted.
    /// - ensures: source then target, each prefixed by its dialogue count; each
    ///   dialogue has its decision count followed by tagged words.
    /// - provides: identical evidence content for wire and memo encoders.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — framing is a law of subsequent iterator
    ///   consumption; checking the opaque iterator here would consume or
    ///   materialize it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — persisted evidence retains dialogue boundaries,
    ///   order, sides and negative premise positions.
    /// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
    #[inline]
    pub fn words(&self) -> impl Iterator<Item = EvidenceWord> + '_
    {
        [&self.source, &self.target]
            .into_iter()
            .flat_map(|direction| {
                core::iter::once(EvidenceWord(u64::from(crate::wire::WireU64::from(
                    crate::wire::WireUsize::from(direction.len()),
                ))))
                .chain(direction.iter().flat_map(|dialogue| {
                    core::iter::once(EvidenceWord(u64::from(crate::wire::WireU64::from(
                        crate::wire::WireUsize::from(dialogue.len()),
                    ))))
                    .chain(dialogue.iter().copied().map(decision_word))
                }))
            })
    }
}

/// Encode one decision; only negative premises carry an integer payload.
///
/// # Specification
/// - requires: nothing; every decision belongs to the portable alphabet.
/// - ensures: distinct decisions have distinct words; anchors are unit-valued.
/// - provides: a closed, arena-independent decision alphabet.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — wire decoding distinguishes sides and premise positions.
/// - witness: `sharing_format::sharing_format::native_path_evidence_preserves_framing_and_refuses_malformed_words`
#[spec(ensures: |ret| gandr_kernel_conversion_trace::ConversionDecision::<()>::try_from(ret) == Ok(decision))]
fn decision_word(decision: gandr_kernel_conversion_trace::ConversionDecision<()>) -> EvidenceWord
{
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    EvidenceWord(match decision {
        | ConversionDecision::ReduceLeft { .. } => 0,
        | ConversionDecision::ReduceRight { .. } => 1,
        | ConversionDecision::ConstShortcut { .. } => 2,
        | ConversionDecision::Unfold { .. } => 3,
        | ConversionDecision::Postpone { .. } => 4,
        | ConversionDecision::Freeze {
            side: ConversionSide::Left,
            ..
        } => 5,
        | ConversionDecision::Freeze {
            side: ConversionSide::Right,
            ..
        } => 6,
        | ConversionDecision::EtaExpand {
            side: ConversionSide::Left,
            ..
        } => 7,
        | ConversionDecision::EtaExpand {
            side: ConversionSide::Right,
            ..
        } => 8,
        | ConversionDecision::Force { .. } => 9,
        | ConversionDecision::ComparedShared { .. } => 10,
        | ConversionDecision::Decompose => 11,
        | ConversionDecision::NegativeSubgoal { position } => {
            (u64::from(u32::from(position)) << 8_u32) | 0x0C_u64
        },
    })
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_conversion_trace::ConversionDecision;

    use super::EvidenceWord;

    #[test]
    fn evidence_words_reject_unknown_and_oversized_premises()
    {
        for position in [0_u32, u32::MAX] {
            let word = EvidenceWord((u64::from(position) << 8_u32) | 0x0C_u64);
            assert_eq!(
                Ok(ConversionDecision::NegativeSubgoal {
                    position: position.into()
                }),
                ConversionDecision::try_from(word)
            );
        }
        for word in [
            0x0D_u64,
            0xFF_u64,
            0x100_u64,
            0x0100_0000_000C_u64,
            u64::MAX,
        ] {
            assert_eq!(
                Err(crate::MalformedSite::PathEvidence),
                ConversionDecision::try_from(EvidenceWord(word)),
                "unknown tags and overflowing premises cannot be truncated into accepted evidence"
            );
        }
    }
}
