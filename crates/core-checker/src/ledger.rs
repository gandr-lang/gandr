//! The obligation ledger: the holes a run owes, and nothing else.
//!
//! # Absence-only, by construction
//!
//! An [`ObligationEntry`] is built from an [`Absence`] and from nothing else,
//! and an [`Absence`] has no public constructor: the judgement makes one when a
//! hole meets a declared type, and only then. A refusal therefore cannot be
//! spelled as an obligation — not by the checker, not by a caller — and the
//! ledger's count is the number of holes owed, never a count of errors.

use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_term::ConstantIndex;

use crate::declaration::OriginToken;
use crate::formation::FormedValueType;

/// A hole met in checking position: the declaration it stands for, the type
/// it owes, and the declaration's origin.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Absence
{
    /// The admission position of the declaration whose body is the hole.
    constant: ConstantIndex,
    /// The declared type the hole absorbed.
    declared: FormedValueType,
    /// The declaration's origin.
    origin: OriginToken,
}

impl Absence
{
    /// The hole of the declaration at `constant`, owing `declared`.
    ///
    /// # Specification
    /// - requires: the declaration at `constant` carries `declared` as its
    ///   signature and a hole as its body; the hole rule is the only caller.
    /// - ensures: the accessors return exactly the arguments.
    /// - panics: none.
    pub(crate) const fn new(
        constant: ConstantIndex,
        declared: FormedValueType,
        origin: OriginToken,
    ) -> Self
    {
        Self {
            constant,
            declared,
            origin,
        }
    }

    /// The admission position of the declaration whose body is the hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// The declared type the hole owes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> FormedValueType
    {
        self.declared
    }

    /// The declaration's origin.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.origin
    }
}

/// One obligation the run owes: an absence, recorded.
///
/// The only way in is [`From<Absence>`]; a refusal has no conversion, and an
/// [`Absence`] has no public constructor.
///
/// ```compile_fail
/// use gandr_core_checker::CheckRefusal;
/// use gandr_core_checker::ObligationEntry;
///
/// fn owe(refusal: CheckRefusal) -> ObligationEntry
/// {
///     ObligationEntry::from(refusal)
/// }
/// ```
///
/// ```compile_fail
/// use gandr_core_checker::Absence;
///
/// let forge = Absence::new;
/// ```
///
/// The positive control: the one conversion that does exist.
///
/// ```
/// use gandr_core_checker::Absence;
/// use gandr_core_checker::ObligationEntry;
///
/// fn owe(absence: Absence) -> ObligationEntry
/// {
///     ObligationEntry::from(absence)
/// }
/// ```
///
/// These three blocks are exercised by the doc-test lane rather than named as
/// witnesses.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObligationEntry
{
    /// The absence the entry records.
    absence: Absence,
}

impl From<Absence> for ObligationEntry
{
    /// The entry recording `absence`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(absence: Absence) -> Self
    {
        Self { absence }
    }
}

impl ObligationEntry
{
    /// The absence the entry records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn absence(&self) -> Absence
    {
        self.absence
    }
}

/// How many obligations a ledger holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObligationCount(usize);

impl From<usize> for ObligationCount
{
    /// The count of `obligations` obligations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(obligations: usize) -> Self
    {
        Self(obligations)
    }
}

impl From<ObligationCount> for usize
{
    /// The number of obligations `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ObligationCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for ObligationCount
{
    /// Writes the number of obligations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The obligations a run owes, in the order their holes were met.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct ObligationLedger
{
    /// The entries, in the order recorded.
    entries: Vec<ObligationEntry>,
}

impl ObligationLedger
{
    /// The empty ledger.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            entries: Vec::new(),
        }
    }

    /// Record `entry`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `entry` is the last of [`Self::entries`], and the count is
    ///   one higher.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surface is the append order, separated by two
    ///   holes recorded in module order and read back in that order.
    /// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
    #[inline]
    pub fn record(
        &mut self,
        entry: ObligationEntry,
    )
    {
        self.entries.push(entry);
    }

    /// The entries, in the order recorded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[ObligationEntry]
    {
        &self.entries
    }

    /// How many obligations the ledger holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(&self) -> ObligationCount
    {
        ObligationCount(self.entries.len())
    }
}
