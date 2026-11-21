//! The completion entries: the two sizes of entry, and the two runs that
//! read them, the ready entries and the entries that a wait gives.

use ::core::marker::PhantomData;
use ::core::mem::MaybeUninit;
use ::core::ptr::NonNull;

use crate::arg::Count;

/// The completions that are ready now, each given once. The drop marks the
/// given ones as seen, so the kernel can reuse their slots.
pub struct CqesReady<'cq, C>
where
    C: self::Kind,
{
    /// liburing's iterator over the ready completions.
    iter: ::liburing_rs::io_uring_cqe_iter,
    /// The count of completions that the run gives.
    seen: u32,
    /// The ring that liburing holds.
    ring: NonNull<::liburing_rs::io_uring>,
    /// The borrow of the completion queue.
    marker: PhantomData<C::Repr<'cq>>,
}

impl<C> Drop for CqesReady<'_, C>
where
    C: self::Kind,
{
    /// Marks each given completion as seen.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let ring = self.ring.as_ptr();
        // SAFETY: `ring` is the live ring that the run borrows, and the run
        // gave `seen` completions.
        unsafe {
            ::liburing_rs::io_uring_cq_advance(ring, self.seen);
        }
    }
}

impl<C> CqesReady<'_, C>
where
    C: self::Kind,
{
    /// The completions of `ring` that are ready now.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn new(ring: NonNull<::liburing_rs::io_uring>) -> Self
    {
        // SAFETY: `ring` is the live ring that the completion queue borrows.
        let iter = unsafe { ::liburing_rs::io_uring_cqe_iter_init(ring.as_ptr()) };
        Self {
            iter,
            seen: 0,
            ring,
            marker: PhantomData,
        }
    }
}

impl<'cq, C> Iterator for CqesReady<'cq, C>
where
    C: self::Kind,
{
    type Item = C::Repr<'cq>;

    /// The next ready completion.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        // The run gives at most the queue's entries, so `seen` stays within
        // 32 bits, and past them the run ends.
        let seen = self.seen.checked_add(1)?;
        let mut cqe = MaybeUninit::<C::Repr<'cq>>::uninit();
        // SAFETY: the iterator is liburing's over this ring, and `cqe` has
        // room for one pointer to a completion.
        if !unsafe {
            ::liburing_rs::io_uring_cqe_iter_next(&raw mut self.iter, cqe.as_mut_ptr().cast())
        } {
            return None;
        }
        self.seen = seen;
        // SAFETY: liburing wrote the completion's pointer when it answered
        // true.
        Some(unsafe { cqe.assume_init() })
    }

    /// The count of ready completions that the run still gives.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        // The ring's head and tail run free and wrap, so their distance is
        // the wrapping difference, as liburing and the kernel read it.
        let min = self.iter.tail.wrapping_sub(self.iter.head);
        #[expect(
            clippy::as_conversions,
            reason = "usize is at least 32 bits on supported platforms"
        )]
        let min = min as usize;
        (min, Some(min))
    }
}

/// The completions that a wait gives, each given once. The drop marks the
/// given ones as seen, so the kernel can reuse their slots.
pub struct CqesWait<'cq, C>
where
    C: self::Kind,
{
    /// The next completion.
    cqe_ptr: NonNull<::liburing_rs::io_uring_cqe>,
    /// The count of completions that the run still gives.
    left: usize,
    /// The count of completions that the run gives.
    seen: u32,
    /// The ring that liburing holds.
    ring: NonNull<::liburing_rs::io_uring>,
    /// The borrow of the completion queue.
    marker: PhantomData<C::Repr<'cq>>,
}

impl<C> Drop for CqesWait<'_, C>
where
    C: self::Kind,
{
    /// Marks each given completion as seen.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let ring = self.ring.as_ptr();
        // SAFETY: `ring` is the live ring that the run borrows, and the run
        // gave `seen` completions.
        unsafe {
            ::liburing_rs::io_uring_cq_advance(ring, self.seen);
        }
    }
}

impl<C> CqesWait<'_, C>
where
    C: self::Kind,
{
    /// The `len` completions of `ring` from `cqe_ptr`, which a wait gives.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn new(
        ring: NonNull<::liburing_rs::io_uring>,
        cqe_ptr: NonNull<::liburing_rs::io_uring_cqe>,
        Count(len): Count<usize>,
    ) -> Self
    {
        Self {
            ring,
            cqe_ptr,
            left: len,
            seen: 0,
            marker: PhantomData,
        }
    }
}

impl<'cq, C> Iterator for CqesWait<'cq, C>
where
    C: self::Kind,
{
    type Item = C::Repr<'cq>;

    /// The next completion that the wait gives.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        let left = self.left.checked_sub(1)?;
        let seen = self.seen.checked_add(1)?;
        self.left = left;
        self.seen = seen;

        // SAFETY: the wait gave `left` completions in a row from `cqe_ptr`.
        let cqe = unsafe { self.cqe_ptr.as_ref() };
        // SAFETY: the completion is an entry of this ring, of the size that
        // `C` names.
        let cqe = unsafe { C::new(cqe) };

        // The step is one entry of the ring's size: 16 bytes, or 32 bytes for
        // a ring set up with entries of 32 bytes.
        // SAFETY: the wait gave `left` entries in a row, so the next entry
        // lies in the ring's array of entries, or one past its end after the
        // last.
        self.cqe_ptr = unsafe { self.cqe_ptr.byte_add(C::STEP) };

        Some(cqe)
    }

    /// The count of completions that the run still gives.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let min = self.left;
        (min, Some(min))
    }
}

/// A size of completion entry: 16 bytes or 32 bytes.
pub trait Kind: self::sealed::Kind
{
    /// The entry of this size.
    type Repr<'cq>: Into<self::repr::Cqe16<'cq>>;

    /// The entry of this size over `cqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `cqe` is an entry of a ring set up with entries of
    ///   this size.
    ///
    /// # Specification
    ///
    /// - executable: none — a trait declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind gives the completions of a ring of that
    ///   kind.
    /// - declaration-only: each kind of entry implements it, and its tests read
    ///   the completions of a ring of that kind.
    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>;
}

impl Kind for self::kind::Cqe16
{
    type Repr<'cq> = self::repr::Cqe16<'cq>;

    /// The entry of 16 bytes over `cqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `cqe` is an entry of a ring.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>
    {
        // SAFETY: the caller gives an entry of a ring.
        unsafe { Self::Repr::new(cqe) }
    }
}

impl Kind for self::kind::Cqe32
{
    type Repr<'cq> = self::repr::Cqe32<'cq>;

    /// The entry of 32 bytes over `cqe`.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: `cqe` is an entry of a ring set up with entries of
    ///   32 bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>
    {
        // SAFETY: the caller gives an entry of 32 bytes.
        unsafe { Self::Repr::new(cqe) }
    }
}
impl<'cq> From<self::repr::Cqe32<'cq>> for self::repr::Cqe16<'cq>
{
    /// The first 16 bytes of an entry of 32 bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(value: self::repr::Cqe32<'cq>) -> Self
    {
        let cqe = ::core::ptr::from_ref(value.cqe()).cast();
        // SAFETY: an entry of 32 bytes starts with the fields of an entry of
        // 16 bytes, and the borrow moves from `value` to the result.
        let cqe = unsafe { &*cqe };
        // SAFETY: `cqe` is the entry of `value`, which the kernel posted and
        // the ring has not yet marked as seen.
        unsafe { Self::new(cqe) }
    }
}

/// The seal: no type outside the crate is a size of entry.
mod sealed
{
    /// The sealed trait, with the step from one entry of the ring to the
    /// next.
    pub trait Kind
    {
        /// The size of one entry of the ring, in bytes.
        const STEP: usize;
    }
    impl Kind for super::kind::Cqe16
    {
        const STEP: usize = size_of::<::liburing_rs::io_uring_cqe>();
    }
    impl Kind for super::kind::Cqe32
    {
        const STEP: usize = size_of::<[::liburing_rs::io_uring_cqe; 2]>();
    }
}

/// The two sizes of completion entry, as types.
pub mod kind
{
    /// The entry of 16 bytes, the kernel's default.
    #[non_exhaustive]
    pub struct Cqe16;

    /// The entry of 32 bytes, for the commands that give more.
    #[non_exhaustive]
    pub struct Cqe32;
}

/// The completion entries, each a borrow of an entry of the ring.
pub mod repr
{
    use ::core::ops::Deref;
    use ::core::ops::DerefMut;

    use crate::arg::Answer;
    use crate::arg::Flags;
    use crate::arg::UserData;

    /// The entry of the default size.
    pub type Cqe<'cq> = Cqe16<'cq>;

    /// An entry of 16 bytes, borrowed from the completion queue.
    #[derive(Debug)]
    #[repr(transparent)]
    pub struct Cqe16<'cq>
    {
        /// The entry that liburing holds.
        cqe: &'cq ::liburing_rs::io_uring_cqe,
    }
    impl<'cq> Cqe16<'cq>
    {
        /// The entry over `cqe`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `cqe` is an entry of a ring that the kernel has
        ///   posted and the ring has not yet marked as seen.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        #[inline]
        pub const unsafe fn new(cqe: &'cq ::liburing_rs::io_uring_cqe) -> Self
        {
            Self { cqe }
        }

        /// The entry that liburing holds, for the tests that read a
        /// completion's fields.
        ///
        /// # Specification
        ///
        /// trivial.
        #[cfg(test)]
        #[must_use]
        pub(crate) const fn cqe(&self) -> &'cq ::liburing_rs::io_uring_cqe
        {
            self.cqe
        }

        /// The operation's result: a count or a descriptor when it is not
        /// negative, and the negated error number when it is.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        #[inline]
        pub const fn res(&self) -> Answer<i32>
        {
            Answer(self.cqe.res)
        }

        /// The user data that the operation's entry carries.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        #[inline]
        pub const fn user_data(&self) -> UserData
        {
            UserData(self.cqe.user_data)
        }

        /// The kernel's flags of the completion.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        #[inline]
        pub const fn flags(&self) -> Flags<u32>
        {
            Flags(self.cqe.flags)
        }
    }

    /// An entry of 32 bytes, borrowed from the completion queue.
    #[repr(transparent)]
    pub struct Cqe32<'cq>
    {
        /// The entry that liburing holds.
        cqe: &'cq ::liburing_rs::io_uring_cqe,
    }
    impl<'cq> Cqe32<'cq>
    {
        /// The entry over `cqe`.
        ///
        /// # Safety
        ///
        /// - unsafe invariants: `cqe` is an entry of a ring set up with entries
        ///   of 32 bytes, that the kernel has posted and the ring has not yet
        ///   marked as seen.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        #[inline]
        pub const unsafe fn new(cqe: &'cq ::liburing_rs::io_uring_cqe) -> Self
        {
            Self { cqe }
        }

        /// The entry that liburing holds, for the conversion between the
        /// two sizes of entry.
        ///
        /// # Specification
        ///
        /// trivial.
        #[must_use]
        pub(crate) const fn cqe(&self) -> &'cq ::liburing_rs::io_uring_cqe
        {
            self.cqe
        }
    }
    impl<'cq> Deref for Cqe32<'cq>
    {
        type Target = Cqe16<'cq>;

        /// The entry as an entry of 16 bytes.
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
    impl DerefMut for Cqe32<'_>
    {
        /// The entry as an entry of 16 bytes.
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
}
