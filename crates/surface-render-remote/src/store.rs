//! The store card: one row for each value that the store under the hub's data
//! directory holds, keyed by its content pointer, and the cells that no layer
//! fills yet, each with the unit that brings it.
//!
//! A [`StoreRow`] names the kind of the value, where it resides, the bytes of
//! the images of its chunks, their count, and the in-degree of its root chunk:
//! how many values of the card hold that chunk in their closure. A value whose
//! chunks the store refuses holds the refusal in place of the counts. A store
//! that does not open is the refusal of the whole card.
//!
//! The commit that wrote a value, the world it stands in, the location-
//! addressable memory and the reduct are cells that no layer fills yet. The
//! card names each one once, as an [`OwedCell`], with the number of the unit
//! that brings it. That number is never zero, so a renderer prints the unit,
//! and never a zero count.
//!
//! The hub sends the whole card, as the stack card goes, since a card holds
//! one row for each value and an edit list would cost more than the rows it
//! saves.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-store gives the columns of the store pane that a row
//!   carries.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use crate::visual::Count;

/// The key of a store row: the digest of the value's root chunk as 64
/// hexadecimal digits, with `+n` after it for a value at the offset `n` of
/// that chunk.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StoreKey(String);

impl From<String> for StoreKey
{
    /// The key spelled `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for StoreKey
{
    /// The key's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for StoreKey
{
    /// Write the key's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// What a value of the store is, by the name that finds it.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StoreKind
{
    /// A receipt of kernel verdicts.
    Receipt,
    /// A stratum of the outcomes kept at one level.
    Stratum,
    /// The export of a package.
    Export,
    /// The identity of a package that a lock records.
    Identity,
}

/// Where a value of the store resides, and what it takes there; or the
/// refusal of the store.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum StoreResidence
{
    /// In the content-addressable memory.
    Cam
    {
        /// The bytes of the images of its chunks.
        bytes: Count,
        /// The number of its chunks.
        chunks: Count,
        /// How many values of the card hold its root chunk in their closure,
        /// itself among them.
        shared: Count,
    },
    /// The store refused a chunk of the value.
    Refused
    {
        /// The store's refusal.
        why: String,
    },
}

/// One value of the store.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StoreRow
{
    /// The row's key.
    pub key: StoreKey,
    /// What the value is.
    pub kind: StoreKind,
    /// Where it resides.
    pub residence: StoreResidence,
}

/// The number of the issue of a unit, which is never zero.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnitNumber(NonZeroU32);

impl From<NonZeroU32> for UnitNumber
{
    /// The unit numbered `number`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: NonZeroU32) -> Self
    {
        Self(number)
    }
}

impl fmt::Display for UnitNumber
{
    /// Write the number as an issue reference, `#` before it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// A cell of every row that no layer fills yet, and the unit that brings it.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct OwedCell
{
    /// The cell's name, as the pane heads its column.
    pub column: String,
    /// The unit that brings it.
    pub unit: UnitNumber,
}

/// The store under the hub's data directory.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct StoreCard
{
    /// One row for each value, in the order of their keys.
    pub rows: Vec<StoreRow>,
    /// The cells that no layer fills yet, in the order of the pane's columns.
    pub owed: Vec<OwedCell>,
    /// The store's refusal to open, which leaves the rows as the hub read
    /// them last; absent when the store opened.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub refused: Option<String>,
}
