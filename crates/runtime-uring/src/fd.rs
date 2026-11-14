use ::core::ops::Deref;
use ::std::os::fd::AsRawFd;

#[derive(Clone, Copy)]
pub enum SlotDesc<T> {
    Slot(::core::ffi::c_uint),
    Desc(T),
}

impl<T> AsRawFd for SlotDesc<T>
where
    T: Deref,
    T::Target: AsRawFd,
{
    fn as_raw_fd(&self) -> std::os::unix::prelude::RawFd {
        match self {
            | &Self::Slot(slot) => slot.cast_signed(),
            | &Self::Desc(ref desc) => desc.as_raw_fd(),
        }
    }
}

impl<T> From<T> for SlotDesc<T> {
    fn from(value: T) -> Self {
        Self::Desc(value)
    }
}

impl<T> SlotDesc<T> {
    pub fn as_deref(&self) -> SlotDesc<&<T as Deref>::Target>
    where
        T: Deref,
    {
        match self {
            | &Self::Slot(idx) => SlotDesc::Slot(idx),
            | &Self::Desc(ref val) => SlotDesc::Desc(&**val),
        }
    }

    pub const fn as_ref(&self) -> SlotDesc<&T> {
        match self {
            | &Self::Slot(idx) => SlotDesc::Slot(idx),
            | &Self::Desc(ref val) => SlotDesc::Desc(val),
        }
    }

    pub const fn is_desc(&self) -> bool {
        matches!(self, &Self::Desc(..))
    }

    pub const fn is_slot(&self) -> bool {
        matches!(self, &Self::Slot(..))
    }
}
