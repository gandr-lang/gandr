//! One shape for the obstruction an analysis reports.
//!
//! An analysis refuses a global property when a local fact admits no global
//! answer. A block's rules are no rewriting system when two of them rewrite
//! one term to two normal forms. A system of level constraints has no
//! valuation when a cycle of them sums above zero. In each case the fact lives
//! on some cells of the analysis's site, and it carries a witness in the
//! analysis's coefficients.
//!
//! [`Obstruction`] holds the two. It borrows both from the analysis, so a
//! refusal reports what obstructs it with no copy. Only the message that a
//! face shows takes new memory.
//!
//! Completion fills the shape first. A critical pair whose two sides reach two
//! different normal forms is a [`PartingPair`]. Its cells are the later rule,
//! the earlier rule and the peak where they overlap. Its witness is the two
//! normal forms. [`parting`] reads it off the cell diagnostic that completion
//! records, and the refusal's message names the peak and both normal forms.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — background: §
//!   presented-spaces-frame and § presented-spaces-reorganisation — every
//!   analysis's obstruction as a set of cells and a witness, in one shape.

use anodized::spec;
use gandr_surface_lowering::coincide::CoherenceFault;
use gandr_surface_lowering::coincide::PairTerm;
use gandr_surface_lowering::desc_cells::CellDiagnostic;
use gandr_surface_lowering::desc_cells::CellFault;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

/// What a refusal of a global property names: the cells it lives on and its
/// witness in the analysis's coefficients.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Obstruction<Cells, Witness>
{
    /// The cells of the analysis's site that the obstruction lives on.
    pub cells: Cells,
    /// The obstruction's witness, in the analysis's coefficients.
    pub witness: Witness,
}

/// The cells of a critical pair: the two rules that overlap, and the peak
/// where they do.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Overlap<'fault>
{
    /// The later rule's written interval: the refusal's own span.
    pub later: ByteSpan,
    /// The earlier rule's written interval.
    pub earlier: ByteSpan,
    /// The term both rules match.
    pub peak: &'fault PairTerm,
}

/// The two normal forms that the sides of a critical pair reach.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Parted<'fault>
{
    /// The earlier rule's normal form of the peak.
    pub earlier: &'fault PairTerm,
    /// The later rule's normal form of the peak.
    pub later: &'fault PairTerm,
}

/// A critical pair whose two sides part: completion's obstruction.
pub type PartingPair<'fault> = Obstruction<Overlap<'fault>, Parted<'fault>>;

quenchant_shape::reason_enum! {
    /// Why a refusal fills no obstruction shape.
    pub mod obstructed {
        /// The reason none is filled.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal holds no parting pair: it names no peak, or only
            /// one normal form.
            Unparted,
        }
    }
}

/// The parting pair that the cell diagnostic `diagnostic` holds, borrowed.
///
/// # Specification
/// - ensures: present exactly for a coherence fault that diverges or that
///   completion leaves apart. The later rule is the diagnostic's span. The
///   earlier rule, the peak and the two normal forms are the fault's own, by
///   reference.
/// - provides: [`obstructed::Absent::Unparted`] for every other fault.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a divergent pair, a pair completion leaves apart, an
///   unoriented rule and a completion that never ends. A swapped normal form, a
///   lost peak or a filled shape for a pair with no two normal forms changes
///   the observed shape.
/// - witness: `tests::diagnostics::a_parting_pair_borrows_the_faults_rules_peak_and_normal_forms`
/// - witness: `tests::diagnostics::a_fault_with_no_second_normal_form_fills_no_shape`
#[spec(ensures: |output| match (&diagnostic.fault, output) {
    (&CellFault::Coherence(CoherenceFault::Diverges { first, ref peak, ref left, ref right }
        | CoherenceFault::Uncompleted { first, ref peak, ref left, ref right }), Maybe::Present(pair)) =>
        pair.cells.later == diagnostic.span && pair.cells.earlier == first
            && core::ptr::eq(core::ptr::from_ref(pair.cells.peak), &raw const **peak)
            && core::ptr::eq(core::ptr::from_ref(pair.witness.earlier), &raw const **left)
            && core::ptr::eq(core::ptr::from_ref(pair.witness.later), &raw const **right),
    (&CellFault::Coherence(CoherenceFault::Diverges { .. } | CoherenceFault::Uncompleted { .. }), Maybe::Absent(_))
        | (_, Maybe::Present(_)) => false,
    (_, Maybe::Absent(_)) => true,
})]
#[inline]
pub fn parting(diagnostic: &CellDiagnostic) -> Maybe<PartingPair<'_>, obstructed::Absent>
{
    let CellFault::Coherence(
        CoherenceFault::Diverges {
            first,
            ref peak,
            ref left,
            ref right,
        }
        | CoherenceFault::Uncompleted {
            first,
            ref peak,
            ref left,
            ref right,
        },
    ) = diagnostic.fault
    else {
        return Maybe::Absent(obstructed::Absent::Unparted);
    };
    Maybe::Present(Obstruction {
        cells: Overlap {
            later: diagnostic.span,
            earlier: first,
            peak,
        },
        witness: Parted {
            earlier: left,
            later: right,
        },
    })
}
