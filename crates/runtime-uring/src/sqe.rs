//! The submission entries: the two sizes of entry, a run of free entries,
//! and one module of preparers for each kind of operation.

pub(crate) mod accept;
pub(crate) mod bind;
pub(crate) mod buffers;
pub(crate) mod cancel;
pub(crate) mod close;
pub(crate) mod cmd_discard;
pub(crate) mod cmd_sock;
pub(crate) mod connect;
pub(crate) mod epoll;
pub(crate) mod fadvise;
pub(crate) mod fallocate;
pub(crate) mod files_update;
pub(crate) mod fixed_fd_install;
pub(crate) mod fsync;
pub(crate) mod ftruncate;
pub(crate) mod futex;
pub(crate) mod link;
pub(crate) mod listen;
pub(crate) mod madvise;
pub(crate) mod mkdir;
pub(crate) mod msg;
pub(crate) mod nop;
pub(crate) mod open;
pub(crate) mod pipe;
pub(crate) mod poll;
pub(crate) mod read;
pub(crate) mod recv;
pub(crate) mod rename;
pub(crate) mod send;
pub(crate) mod shutdown;
pub(crate) mod socket;
pub(crate) mod splice;
pub(crate) mod statx;
pub(crate) mod symlink;
pub(crate) mod sync_file_range;
pub(crate) mod tee;
pub(crate) mod timeout;
pub(crate) mod unlink;
pub(crate) mod waitid;
pub(crate) mod write;
pub(crate) mod xattr;

use ::core::marker::PhantomData;
use ::core::ptr::NonNull;

use crate::SubmissionQueue;
use crate::arg::Count;

/// A run of free entries of the submission queue, each given once.
pub struct Sqes<'sq, S>
{
    /// The ring that liburing holds.
    ring: NonNull<::liburing_rs::io_uring>,
    /// The count of entries that the run still gives.
    rem: u32,
    /// The borrow of the submission queue.
    marker: PhantomData<&'sq mut SubmissionQueue<'sq, S>>,
}

impl<'sq, 'ring, S> Sqes<'sq, S>
{
    /// A run of `len` free entries of `sq`. The caller checks that the queue
    /// has `len` free entries.
    ///
    /// # Specification
    ///
    /// trivial.
    #[expect(clippy::needless_pass_by_ref_mut, reason = "API")]
    pub(crate) fn new(
        sq: &'sq mut SubmissionQueue<'ring, S>,
        Count(len): Count<u32>,
    ) -> Self
    {
        let ring = sq.ring();
        Self {
            ring,
            rem: len,
            marker: PhantomData,
        }
    }
}

impl<'sq, S> Iterator for Sqes<'sq, S>
where
    S: self::Kind,
{
    type Item = S::Repr<'sq>;

    /// The next free entry, until the run has given its count.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.rem = self.rem.checked_sub(1)?;
        // SAFETY: `ring` is the live ring that the run borrows, and the
        // queue had `rem` free entries when the run began.
        unsafe { self::get_sqe_raw::<S>(self.ring) }
    }
}

/// The next free entry of `ring`, or nothing when the queue is full.
///
/// # Safety
///
/// - unsafe invariants: `ring` is a live ring set up with entries of the size
///   that `S` names, and the caller holds the borrow of its submission queue
///   for `'sq`.
///
/// # Specification
///
/// trivial.
pub(crate) unsafe fn get_sqe_raw<'sq, S>(
    ring: NonNull<::liburing_rs::io_uring>
) -> Option<S::Repr<'sq>>
where
    S: self::Kind,
{
    let ring = ring.as_ptr();
    // SAFETY: the caller gives a live ring.
    let sqe = unsafe { ::liburing_rs::io_uring_get_sqe(ring) };
    // SAFETY: liburing gives a null pointer or an entry of the ring, which
    // the caller's borrow of the queue holds alone.
    let sqe = unsafe { sqe.as_mut() }?;
    // SAFETY: the ring's entries have the size that `S` names.
    Some(unsafe { S::new(sqe) })
}

/// A size of submission entry: 64 bytes or 128 bytes.
pub trait Kind: self::sealed::Kind
{
    /// The entry of this size.
    type Repr<'sq>: Into<self::repr::Sqe64<'sq>>;

    /// The entry of this size over `sqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `sqe` is an entry of a ring set up with entries of
    ///   this size.
    ///
    /// # Specification
    ///
    /// - executable: none — a trait declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind prepares the entries of a ring of that
    ///   kind.
    /// - declaration-only: each kind of entry implements it, and its tests
    ///   prepare the entries of a ring of that kind.
    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_>;
}

impl Kind for self::kind::Sqe64
{
    type Repr<'sq> = self::repr::Sqe64<'sq>;

    /// The entry of 64 bytes over `sqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `sqe` is an entry of a ring.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_>
    {
        // SAFETY: the caller gives an entry of a ring.
        unsafe { Self::Repr::new(sqe) }
    }
}

impl Kind for self::kind::Sqe128
{
    type Repr<'sq> = self::repr::Sqe128<'sq>;

    /// The entry of 128 bytes over `sqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `sqe` is an entry of a ring set up with entries of
    ///   128 bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_>
    {
        // SAFETY: the caller gives an entry of 128 bytes.
        unsafe { Self::Repr::new(sqe) }
    }
}
impl<'sq> From<self::repr::Sqe128<'sq>> for self::repr::Sqe64<'sq>
{
    /// The first 64 bytes of an entry of 128 bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(mut value: self::repr::Sqe128<'sq>) -> Self
    {
        let sqe = ::core::ptr::from_mut(value.sqe()).cast();
        // SAFETY: an entry of 128 bytes starts with the fields of an entry of
        // 64 bytes, and the borrow moves from `value` to the result.
        let sqe = unsafe { &mut *sqe };
        // SAFETY: `sqe` is the entry of `value`, whose borrow of the
        // submission queue moves to the result for `'sq`.
        unsafe { Self::new(sqe) }
    }
}

/// The seal: no type outside the crate is a size of entry.
mod sealed
{
    /// The sealed trait.
    pub trait Kind
    {
    }
    impl Kind for super::kind::Sqe64
    {
    }
    impl Kind for super::kind::Sqe128
    {
    }
}

/// The two sizes of submission entry, as types.
pub mod kind
{
    /// The entry of 64 bytes, the kernel's default.
    #[non_exhaustive]
    pub struct Sqe64;

    /// The entry of 128 bytes, for the commands that need the space.
    #[non_exhaustive]
    pub struct Sqe128;
}

/// The submission entries, each a borrow of an entry of the ring.
pub mod repr
{
    use ::core::ops::Deref;
    use ::core::ops::DerefMut;

    use crate::arg::Code;
    use crate::arg::Fd;
    use crate::arg::Flags;
    use crate::arg::Len;
    use crate::arg::Offset;
    use crate::arg::UserData;

    /// The entry of the default size.
    pub type Sqe<'sq> = Sqe64<'sq>;

    /// An entry of 64 bytes, borrowed from the submission queue.
    #[repr(transparent)]
    pub struct Sqe64<'sq>
    {
        /// The entry that liburing holds.
        sqe: &'sq mut ::liburing_rs::io_uring_sqe,
    }
    impl<'sq> Sqe64<'sq>
    {
        /// The entry over `sqe`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `sqe` is an entry of a ring, and the caller
        ///   holds the borrow of its submission queue for `'sq`.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub const unsafe fn new(sqe: &'sq mut ::liburing_rs::io_uring_sqe) -> Self
        {
            Self { sqe }
        }

        /// The entry that liburing holds, for the preparers of the
        /// operations.
        ///
        /// # Specification
        ///
        /// trivial.
        pub(crate) const fn sqe(&mut self) -> &mut ::liburing_rs::io_uring_sqe
        {
            self.sqe
        }
    }

    /// An entry of 128 bytes, borrowed from the submission queue.
    #[repr(transparent)]
    pub struct Sqe128<'sq>
    {
        /// The entry that liburing holds.
        sqe: &'sq mut ::liburing_rs::io_uring_sqe,
    }
    impl<'sq> Sqe128<'sq>
    {
        /// The entry over `sqe`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `sqe` is an entry of a ring set up with entries
        ///   of 128 bytes, and the caller holds the borrow of its submission
        ///   queue for `'sq`.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub const unsafe fn new(sqe: &'sq mut ::liburing_rs::io_uring_sqe) -> Self
        {
            Self { sqe }
        }

        /// The entry that liburing holds, for the preparers of the
        /// operations.
        ///
        /// # Specification
        ///
        /// trivial.
        pub(crate) const fn sqe(&mut self) -> &mut ::liburing_rs::io_uring_sqe
        {
            self.sqe
        }
    }
    impl<'sq> Deref for Sqe128<'sq>
    {
        type Target = Sqe64<'sq>;

        /// The entry as an entry of 64 bytes.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        fn deref(&self) -> &Self::Target
        {
            let ptr = (&raw const *self).cast::<Self::Target>();
            // SAFETY: both types are transparent over the same borrow of an
            // entry, so the cast keeps the layout.
            unsafe { &*ptr }
        }
    }
    impl DerefMut for Sqe128<'_>
    {
        /// The entry as an entry of 64 bytes.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target
        {
            let ptr = (&raw mut *self).cast::<Self::Target>();
            // SAFETY: both types are transparent over the same borrow of an
            // entry, so the cast keeps the layout.
            unsafe { &mut *ptr }
        }
    }

    impl Sqe64<'_>
    {
        /// Prepares the entry for the operation `op` on `fd`, with `addr`,
        /// `len` and `offset` in the fields that the operation reads.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `addr` points to memory that stays valid, and
        ///   does not move, until the kernel posts the entry's completion. `fd`
        ///   is an open descriptor, or a slot of the ring's file table when the
        ///   entry carries the fixed-file flag.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn prep_rw(
            &mut self,
            Code(op): Code<::core::ffi::c_uint>,
            Fd(fd): Fd,
            addr: *const ::core::ffi::c_void,
            Len(len): Len<::core::ffi::c_uint>,
            Offset(offset): Offset<u64>,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_rw(op, sqe, fd, addr, len, offset) }
        }

        /// Sets the entry's flags to `flags`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `flags` holds only the entry flags that the
        ///   kernel knows, and a fixed-file flag only when the entry names a
        ///   slot of the file table.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn set_flags(
            &mut self,
            Flags(flags): Flags<::core::ffi::c_uint>,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_sqe_set_flags(sqe, flags);
            }
        }

        /// Sets the entry's user data to the pointer `data`, which its
        /// completion gives back.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The kernel does not read `data`; the caller
        ///   that reads it back from the completion keeps it valid until then.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn set_data(
            &mut self,
            data: *const ::core::ffi::c_void,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_sqe_set_data(sqe, data.cast_mut());
            }
        }

        /// Sets the entry's user data to `data`, which its completion gives
        /// back.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: The owner's crate marks each setter `unsafe`.
        ///   This one reads no pointer and names no descriptor, so it holds no
        ///   invariant of its own.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub unsafe fn set_data64(
            &mut self,
            UserData(data): UserData,
        )
        {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe {
                ::liburing_rs::io_uring_sqe_set_data64(sqe, data);
            }
        }
    }
}
