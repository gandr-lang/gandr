use ::core::marker::PhantomData;
use ::core::mem::MaybeUninit;
use ::core::num::NonZero;
use ::core::ptr::NonNull;

pub struct CqesReady<'cq, C>
where
    C: self::Kind,
{
    iter: ::liburing_rs::io_uring_cqe_iter,
    seen: u32,
    ring: NonNull<::liburing_rs::io_uring>,
    marker: PhantomData<C::Repr<'cq>>,
}

impl<C> Drop for CqesReady<'_, C>
where
    C: self::Kind,
{
    fn drop(&mut self)
    {
        let ring = self.ring.as_ptr();
        // SAFETY:
        unsafe { ::liburing_rs::io_uring_cq_advance(ring, self.seen) };
    }
}

impl<C> CqesReady<'_, C>
where
    C: self::Kind,
{
    pub(crate) fn new(ring: NonNull<::liburing_rs::io_uring>) -> Self
    {
        // SAFETY:
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

    fn next(&mut self) -> Option<Self::Item>
    {
        let mut cqe = MaybeUninit::<C::Repr<'cq>>::uninit();
        // SAFETY:
        if !unsafe {
            ::liburing_rs::io_uring_cqe_iter_next(&raw mut self.iter, cqe.as_mut_ptr().cast())
        } {
            return None;
        }
        self.seen += 1;
        // SAFETY:
        Some(unsafe { cqe.assume_init() })
    }

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

pub struct CqesWait<'cq, C>
where
    C: self::Kind,
{
    cqe_ptr: NonNull<::liburing_rs::io_uring_cqe>,
    left: usize,
    seen: u32,
    ring: NonNull<::liburing_rs::io_uring>,
    marker: PhantomData<C::Repr<'cq>>,
}

impl<C> Drop for CqesWait<'_, C>
where
    C: self::Kind,
{
    fn drop(&mut self)
    {
        let ring = self.ring.as_ptr();
        // SAFETY:
        unsafe { ::liburing_rs::io_uring_cq_advance(ring, self.seen) };
    }
}

impl<C> CqesWait<'_, C>
where
    C: self::Kind,
{
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

    fn next(&mut self) -> Option<Self::Item>
    {
        if self.left == 0 {
            return None;
        }

        self.left -= 1;
        self.seen += 1;

        // SAFETY:
        let cqe = unsafe { self.cqe_ptr.as_ref() };
        // SAFETY:
        let cqe = unsafe { C::new(cqe) };

        // FIXME: include offsets for big cqe
        self.cqe_ptr = self.cqe_ptr.map_addr(|addr| {
            let res = usize::from(addr) + size_of::<::liburing_rs::io_uring_cqe>();
            // SAFETY:
            unsafe { NonZero::new_unchecked(res) }
        });

        Some(cqe)
    }

    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let min = self.left;
        (min, Some(min))
    }
}

pub trait Kind: self::sealed::Kind
{
    type Repr<'cq>: Into<self::repr::Cqe16<'cq>>;

    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>;
}

impl Kind for self::kind::Cqe16
{
    type Repr<'cq> = self::repr::Cqe16<'cq>;

    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>
    {
        // SAFETY:
        unsafe { Self::Repr::new(cqe) }
    }
}

impl Kind for self::kind::Cqe32
{
    type Repr<'cq> = self::repr::Cqe32<'cq>;

    unsafe fn new(cqe: &::liburing_rs::io_uring_cqe) -> Self::Repr<'_>
    {
        // SAFETY:
        unsafe { Self::Repr::new(cqe) }
    }
}
impl<'cq> From<self::repr::Cqe32<'cq>> for self::repr::Cqe16<'cq>
{
    fn from(value: self::repr::Cqe32<'cq>) -> Self
    {
        let cqe = ::core::ptr::from_ref(value.cqe).cast();
        // SAFETY:
        let cqe = unsafe { &*cqe };
        Self { cqe }
    }
}

mod sealed
{
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

pub mod kind
{
    #[non_exhaustive]
    pub struct Cqe16;

    #[non_exhaustive]
    pub struct Cqe32;
}

pub mod repr
{
    use ::core::ops::Deref;
    use ::core::ops::DerefMut;

    pub type Cqe<'cq> = Cqe16<'cq>;

    #[derive(Debug)]
    #[repr(transparent)]
    pub struct Cqe16<'cq>
    {
        pub(crate) cqe: &'cq ::liburing_rs::io_uring_cqe,
    }
    impl<'cq> Cqe16<'cq>
    {
        #[must_use]
        pub const unsafe fn new(cqe: &'cq ::liburing_rs::io_uring_cqe) -> Self
        {
            Self { cqe }
        }
    }

    #[repr(transparent)]
    pub struct Cqe32<'cq>
    {
        pub(crate) cqe: &'cq ::liburing_rs::io_uring_cqe,
    }
    impl<'cq> Cqe32<'cq>
    {
        #[must_use]
        pub const unsafe fn new(cqe: &'cq ::liburing_rs::io_uring_cqe) -> Self
        {
            Self { cqe }
        }
    }
    impl<'cq> Deref for Cqe32<'cq>
    {
        type Target = Cqe16<'cq>;

        fn deref(&self) -> &Self::Target
        {
            let ptr = <*const Self>::cast(self);
            // SAFETY:
            unsafe { &*ptr }
        }
    }
    impl DerefMut for Cqe32<'_>
    {
        fn deref_mut(&mut self) -> &mut Self::Target
        {
            let ptr = <*mut Self>::cast(self);
            // SAFETY:
            unsafe { &mut *ptr }
        }
    }
}
