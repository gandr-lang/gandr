//! The registers of a system call: one type for each argument's index and
//! one for the answer, so a call cannot put an argument in another's place.
//!
//! Each register holds a pointer, so a pointer that goes into a call, or
//! that the kernel answers, keeps its provenance. A number goes in as a
//! pointer with no provenance.

use core::ffi::c_void;
use core::marker::PhantomData;
use core::ptr::NonNull;
use std::os::fd::AsRawFd as _;
use std::os::fd::BorrowedFd;

use crate::sys::Errno;
use crate::sys::Word;

/// The type that a register's pointer points at: private, so a register
/// serves no other use.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Opaque(c_void);

/// The index of an argument: the first to the sixth.
pub trait Index: sealed::Index
{
}

/// The first argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct First(());

/// The second argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Second(());

/// The third argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Third(());

/// The fourth argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Fourth(());

/// The fifth argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Fifth(());

/// The sixth argument.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Sixth(());

impl Index for First
{
}
impl Index for Second
{
}
impl Index for Third
{
}
impl Index for Fourth
{
}
impl Index for Fifth
{
}
impl Index for Sixth
{
}

/// The traits that no other crate implements.
mod sealed
{
    /// The index of an argument.
    pub trait Index
    {
    }
    impl Index for super::First
    {
    }
    impl Index for super::Second
    {
    }
    impl Index for super::Third
    {
    }
    impl Index for super::Fourth
    {
    }
    impl Index for super::Fifth
    {
    }
    impl Index for super::Sixth
    {
    }
}

/// One argument of a system call, at the index `At`, which may borrow
/// memory or a descriptor for `'arg`.
///
/// # Specification
/// trivial.
#[must_use]
#[repr(transparent)]
pub struct Argument<'arg, At>
where
    At: Index,
{
    /// The register's value.
    raw: *mut Opaque,
    /// The borrow and the index.
    marker: PhantomData<(&'arg (), At)>,
}

impl<'arg, At> Argument<'arg, At>
where
    At: Index,
{
    /// The number `word`, as a pointer with no provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn word(word: Word) -> Self
    {
        Self {
            raw: core::ptr::without_provenance_mut(word.0),
            marker: PhantomData,
        }
    }

    /// A pointer of zero, for an argument that a call does not read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn none() -> Self
    {
        Self::word(Word(0))
    }

    /// The descriptor `file`, which stays open for the borrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn descriptor(file: BorrowedFd<'arg>) -> Self
    {
        // A descriptor that a borrow holds is never negative.
        Self::word(Word(
            usize::try_from(file.as_raw_fd()).unwrap_or(usize::MAX),
        ))
    }

    /// The place of `value`, which the kernel may write for the borrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn place<T>(value: &'arg mut T) -> Self
    {
        Self {
            raw: core::ptr::from_mut(value).cast(),
            marker: PhantomData,
        }
    }

    /// The pointer `pointer`, with its provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn pointer<T>(pointer: *const T) -> Self
    {
        Self {
            raw: pointer.cast_mut().cast(),
            marker: PhantomData,
        }
    }

    /// The register's value, for the instruction alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn into_raw(self) -> *mut Opaque
    {
        self.raw
    }
}

/// The number of a system call on this architecture.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Number(pub u32);

impl Number
{
    /// The number, as the instruction takes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn into_raw(self) -> *mut Opaque
    {
        core::ptr::without_provenance_mut(usize::try_from(self.0).unwrap_or(usize::MAX))
    }
}

/// The kernel's answers from this address up are error numbers, from 4095
/// down to 1.
const FIRST_ERROR: usize = usize::MAX.wrapping_sub(4_094);

/// The register that a system call answers in.
///
/// # Specification
/// trivial.
#[must_use]
#[repr(transparent)]
pub struct Answer(*mut Opaque);

impl Answer
{
    /// The answer that the instruction leaves in its register.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn from_raw(raw: *mut Opaque) -> Self
    {
        Self(raw)
    }

    /// The error number that the answer names, if it names one.
    ///
    /// # Specification
    /// trivial.
    fn error(&self) -> Option<Errno>
    {
        let address = self.0.addr();
        (address >= FIRST_ERROR)
            .then(|| Errno(u16::try_from(address.wrapping_neg()).unwrap_or(u16::MAX)))
    }

    /// The answer as a number, or the error number it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn word(self) -> Result<Word, Errno>
    {
        self.error().map_or_else(|| Ok(Word(self.0.addr())), Err)
    }

    /// The answer as a pointer, with the provenance that the kernel gives
    /// it, or the error number it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn pointer(self) -> Result<NonNull<c_void>, Errno>
    {
        if let Some(error) = self.error() {
            return Err(error);
        }
        NonNull::new(self.0.cast::<c_void>()).ok_or(Errno::PROTOCOL)
    }
}
