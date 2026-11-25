//! The record of a nominated hole that the lowering's context holds.
//!
//! The classification nominates a hole for an implicit that a call omits and
//! for a wildcard that the text writes. This record says what each hole stands
//! for, and `gandr-surface-lowering` names it at its old path.

use crate::resolve::SurfaceName;

/// What a nominated hole stands for: an implicit a call omits, or a wildcard
/// the text writes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an omitted implicit keeps the function's name and the implicit's.
/// - provides: what the origin table records for the hole once it is minted,
///   and a refusal of the hole names.
/// - panics: none.
/// - executable: none — a record of names, holding no tree to check them
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — a call omitting both implicits of `first` nominates one
///   hole per implicit, each naming it; a wildcard beside them nominates its
///   own.
/// - witness: `gandr-surface-lowering::lower::implicit::tests::an_omitted_implicit_is_a_nominated_hole`
/// - witness: `gandr-surface-lowering::lower::implicit::tests::a_wildcard_is_a_nominated_hole_of_its_own`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Nomination<'source>
{
    /// The implicit `implicit` of `function`, which a call omits.
    Omitted
    {
        /// The function the call applies.
        function: SurfaceName<'source>,
        /// The implicit the call omits.
        implicit: SurfaceName<'source>,
    },
    /// A component of the model answering a capability scope over `theory`,
    /// which names none.
    Answering
    {
        /// The theory the scope handles.
        theory: SurfaceName<'source>,
    },
    /// A wildcard `_` written where a value is read.
    Wildcard,
    /// A splice `~t` written where a value is read, running the tactic `t`.
    Spliced(gandr_core_term::tactic::Tactic),
}
