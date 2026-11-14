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

pub struct Sqes<'sq, S> {
    ring: NonNull<::liburing_rs::io_uring>,
    rem: u32,
    marker: PhantomData<&'sq mut SubmissionQueue<'sq, S>>,
}

impl<'sq, 'ring, S> Sqes<'sq, S> {
    #[expect(clippy::needless_pass_by_ref_mut, reason = "API")]
    pub(crate) fn new(sq: &'sq mut SubmissionQueue<'ring, S>, len: u32) -> Self {
        let ring = NonNull::clone(&sq.ring);
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

    fn next(&mut self) -> Option<Self::Item> {
        if self.rem == 0 {
            return None;
        }
        self.rem -= 1;
        // SAFETY: FIXME
        unsafe { self::get_sqe_raw::<S>(self.ring) }
    }
}

pub(crate) unsafe fn get_sqe_raw<'sq, S>(ring: NonNull<::liburing_rs::io_uring>) -> Option<S::Repr<'sq>>
where
    S: self::Kind,
{
    let ring = ring.as_ptr();
    // SAFETY: FIXME
    let sqe = unsafe { ::liburing_rs::io_uring_get_sqe(ring) };
    // SAFETY: FIXME
    let sqe = unsafe { sqe.as_mut() }?;
    // SAFETY: FIXME
    Some(unsafe { S::new(sqe) })
}

pub trait Kind: self::sealed::Kind {
    type Repr<'sq>: Into<self::repr::Sqe64<'sq>>;

    /// # Safety
    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_>;
}

impl Kind for self::kind::Sqe64 {
    type Repr<'sq> = self::repr::Sqe64<'sq>;

    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_> {
        // SAFETY:
        unsafe { Self::Repr::new(sqe) }
    }
}

impl Kind for self::kind::Sqe128 {
    type Repr<'sq> = self::repr::Sqe128<'sq>;

    unsafe fn new(sqe: &mut ::liburing_rs::io_uring_sqe) -> Self::Repr<'_> {
        // SAFETY:
        unsafe { Self::Repr::new(sqe) }
    }
}
impl<'sq> From<self::repr::Sqe128<'sq>> for self::repr::Sqe64<'sq> {
    fn from(value: self::repr::Sqe128<'sq>) -> Self {
        let sqe = ::core::ptr::from_mut(value.sqe).cast();
        // SAFETY:
        let sqe = unsafe { &mut *sqe };
        Self { sqe }
    }
}

mod sealed {
    pub trait Kind {}
    impl Kind for super::kind::Sqe64 {}
    impl Kind for super::kind::Sqe128 {}
}

pub mod kind {
    #[non_exhaustive]
    pub struct Sqe64;

    #[non_exhaustive]
    pub struct Sqe128;
}

pub mod repr {
    use ::core::ops::Deref;
    use ::core::ops::DerefMut;

    pub type Sqe<'sq> = Sqe64<'sq>;

    #[repr(transparent)]
    pub struct Sqe64<'sq> {
        pub(crate) sqe: &'sq mut ::liburing_rs::io_uring_sqe,
    }
    impl<'sq> Sqe64<'sq> {
        /// # Safety
        pub const unsafe fn new(sqe: &'sq mut ::liburing_rs::io_uring_sqe) -> Self {
            Self { sqe }
        }
    }

    #[repr(transparent)]
    pub struct Sqe128<'sq> {
        pub(crate) sqe: &'sq mut ::liburing_rs::io_uring_sqe,
    }
    impl<'sq> Sqe128<'sq> {
        /// # Safety
        pub const unsafe fn new(sqe: &'sq mut ::liburing_rs::io_uring_sqe) -> Self {
            Self { sqe }
        }
    }
    impl<'sq> Deref for Sqe128<'sq> {
        type Target = Sqe64<'sq>;

        fn deref(&self) -> &Self::Target {
            let ptr = <*const Self>::cast(self);
            // SAFETY:
            unsafe { &*ptr }
        }
    }
    impl DerefMut for Sqe128<'_> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            let ptr = <*mut Self>::cast(self);
            // SAFETY:
            unsafe { &mut *ptr }
        }
    }

    impl Sqe64<'_> {
        /// # Safety
        pub unsafe fn prep_rw(
            &mut self,
            op: ::core::ffi::c_uint,
            fd: ::core::ffi::c_int,
            addr: *const ::core::ffi::c_void,
            len: ::core::ffi::c_uint,
            offset: u64,
        ) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_prep_rw(op, sqe, fd, addr, len, offset) }
        }

        pub unsafe fn set_flags(&mut self, flags: ::core::ffi::c_uint) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_sqe_set_flags(sqe, flags) };
        }

        pub unsafe fn set_data(&mut self, data: *const ::core::ffi::c_void) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_sqe_set_data(sqe, data.cast_mut()) };
        }

        pub unsafe fn set_data64(&mut self, data: u64) {
            let sqe = &raw mut *self.sqe;
            // SAFETY: The enclosing method preserves the safety interface.
            unsafe { ::liburing_rs::io_uring_sqe_set_data64(sqe, data) };
        }
    }
}
