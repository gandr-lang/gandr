//! The precedence and status a path order compares symbols by, as data: each
//! symbol's place and status.
//!
//! A ranked symbol stands above every symbol of a lower rank and above every
//! ground symbol; a ground symbol — a constructor, a results tuple — stands
//! above nothing. An abstraction and a bound occurrence stand where a ground
//! symbol does. Two symbols are equivalent exactly when they are one symbol,
//! so the precedence is the quasi-order whose equivalence is identity, and its
//! strict part is well founded because ranks are naturals.

/// A symbol's place in the precedence. Places are ordered as the precedence
/// orders the symbols holding them: ground below every rank, ranks by number.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Place
{
    /// Below every ranked symbol, and above none.
    Ground,
    /// Above every ground symbol and every symbol of a lower rank.
    Ranked(Rank),
}

/// A ranked symbol's rank.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Rank(u64);

impl From<u64> for Rank
{
    /// The rank `rank`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: u64) -> Self
    {
        Self(rank)
    }
}

impl From<Rank> for u64
{
    /// The rank's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: Rank) -> Self
    {
        rank.0
    }
}

/// How two applications of one symbol compare their arguments.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Status
{
    /// Left to right: the first pair that differs decides.
    Lexicographic,
    /// As multisets: the arguments the other does not share are each below
    /// one of the arguments this one does not share, and this one has one.
    Multiset,
}

/// The precedence over a signature's symbols, as data.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a place and a status for every symbol.
/// - panics: none.
/// - executable: none — a trait declaration; each implementation's witnesses
///   observe its places.
pub trait Precedence
{
    /// The signature's symbols.
    type Symbol: Copy + Eq;

    /// The symbol's place.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the place the precedence gives `symbol`.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a symbol ranked above another orients a descending
    ///   recursion that leaves it unoriented at equal places, and a ground
    ///   symbol stands below every ranked one.
    /// - witness: `tests::lpo::a_descending_recursion_is_oriented_and_its_derivation_replays`
    /// - witness: `tests::lpo::an_abstraction_and_a_bound_occurrence_stand_where_a_ground_symbol_does`
    fn place(
        &self,
        symbol: Self::Symbol,
    ) -> Place;

    /// The symbol's status.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: how two applications of `symbol` compare their arguments.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one head at multiset status orients a pair whose
    ///   arguments are permuted, which lexicographic status leaves unoriented.
    /// - witness: `tests::lpo::multiset_status_orients_what_lexicographic_status_does_not`
    fn status(
        &self,
        symbol: Self::Symbol,
    ) -> Status;
}
