//! The completion entries: the two sizes of entry, and the two runs that
//! read them, the ready entries and the entries that a wait gives.

use ::core::marker::PhantomData;
use ::core::mem::MaybeUninit;
use ::core::num::NonZero;
use ::core::ptr::NonNull;

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
        let mut cqe = MaybeUninit::<C::Repr<'cq>>::uninit();
        // SAFETY: the iterator is liburing's over this ring, and `cqe` has
        // room for one pointer to a completion.
        if !unsafe {
            ::liburing_rs::io_uring_cqe_iter_next(&raw mut self.iter, cqe.as_mut_ptr().cast())
        } {
            return None;
        }
        self.seen += 1;
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
        let min = self.iter.tail - self.iter.head;
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
        len: usize,
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
        if self.left == 0 {
            return None;
        }

        self.left -= 1;
        self.seen += 1;

        // SAFETY: the wait gave `left` completions in a row from `cqe_ptr`.
        let cqe = unsafe { self.cqe_ptr.as_ref() };
        // SAFETY: the completion is an entry of this ring, of the size that
        // `C` names.
        let cqe = unsafe { C::new(cqe) };

        // The step is one entry of 16 bytes. A ring with entries of 32 bytes
        // needs a step of 32 bytes; the owner's list of open work names
        // this check, and #7645 owes it.
        self.cqe_ptr = self.cqe_ptr.map_addr(|addr| {
            let res = usize::from(addr) + size_of::<::liburing_rs::io_uring_cqe>();
            // SAFETY: the address of an entry of the ring is not zero, and
            // the next one is above it.
            unsafe { NonZero::new_unchecked(res) }
        });

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
        let cqe = ::core::ptr::from_ref(value.cqe).cast();
        // SAFETY: an entry of 32 bytes starts with the fields of an entry of
        // 16 bytes, and the borrow moves from `value` to the result.
        let cqe = unsafe { &*cqe };
        Self { cqe }
    }
}

/// The seal: no type outside the crate is a size of entry.
mod sealed
{
    /// The sealed trait.
    pub trait Kind
    {
    }
    impl Kind for super::kind::Cqe16
    {
    }
    impl Kind for super::kind::Cqe32
    {
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

    /// The entry of the default size.
    pub type Cqe<'cq> = Cqe16<'cq>;

    /// An entry of 16 bytes, borrowed from the completion queue.
    #[derive(Debug)]
    #[repr(transparent)]
    pub struct Cqe16<'cq>
    {
        /// The entry that liburing holds.
        pub(crate) cqe: &'cq ::liburing_rs::io_uring_cqe,
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
    }

    /// An entry of 32 bytes, borrowed from the completion queue.
    #[repr(transparent)]
    pub struct Cqe32<'cq>
    {
        /// The entry that liburing holds.
        pub(crate) cqe: &'cq ::liburing_rs::io_uring_cqe,
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
            let ptr = <*const Self>::cast(self);
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
            let ptr = <*mut Self>::cast(self);
            // SAFETY: both types are transparent over the same borrow of an
            // entry, so the cast keeps the layout.
            unsafe { &mut *ptr }
        }
    }
}
