//! A file that an entry names: a slot of the ring's file table or a
//! descriptor of the process.

use ::core::ops::Deref;
use ::std::os::fd::AsRawFd;

use crate::arg::Holds;

/// A file that an entry names. The kernel reads a slot of the ring's file
/// table when the entry carries the fixed-file flag, and a descriptor of the
/// process otherwise.
#[derive(Clone, Copy)]
pub enum SlotDesc<T>
{
    /// A slot of the ring's file table.
    Slot(::core::ffi::c_uint),
    /// A descriptor of the process, behind its owner.
    Desc(T),
}

impl<T> AsRawFd for SlotDesc<T>
where
    T: Deref,
    T::Target: AsRawFd,
{
    /// The slot's index, or the descriptor's number.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd
    {
        match *self {
            Self::Slot(slot) => slot.cast_signed(),
            Self::Desc(ref desc) => desc.as_raw_fd(),
        }
    }
}

impl<T> From<T> for SlotDesc<T>
{
    /// A descriptor of the process.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: T) -> Self
    {
        Self::Desc(value)
    }
}

impl<T> SlotDesc<T>
{
    /// The same slot, or the descriptor's target by reference.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn as_deref(&self) -> SlotDesc<&<T as Deref>::Target>
    where
        T: Deref,
    {
        match *self {
            Self::Slot(idx) => SlotDesc::Slot(idx),
            Self::Desc(ref val) => SlotDesc::Desc(&**val),
        }
    }

    /// The same slot, or the descriptor by reference.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const fn as_ref(&self) -> SlotDesc<&T>
    {
        match *self {
            Self::Slot(idx) => SlotDesc::Slot(idx),
            Self::Desc(ref val) => SlotDesc::Desc(val),
        }
    }

    /// Whether this is a descriptor of the process.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const fn is_desc(&self) -> Holds
    {
        Holds(matches!(self, &Self::Desc(..)))
    }

    /// Whether this is a slot of the ring's file table.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub const fn is_slot(&self) -> Holds
    {
        Holds(matches!(self, &Self::Slot(..)))
    }
}
