//! The ring: its setup through a typed builder, with each setup flag at most
//! once, and the borrows of its two queues and its registrar.

use ::bon::bon;
use ::core::marker::PhantomData;
use ::core::ptr::NonNull;
use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;

use self::io_uring_builder::IsUnset;
use crate::CompletionQueue;
use crate::Registrar;
use crate::SubmissionQueue;
use crate::arg::Answer;
use crate::arg::Bytes;
use crate::arg::Count;
use crate::arg::Cpu;
use crate::arg::Millis;
use crate::arg::Switch;
use crate::ring::io_uring_builder::SetFlagSetupClamp;
use crate::ring::io_uring_builder::SetFlagSetupCoopTaskrun;
use crate::ring::io_uring_builder::SetFlagSetupCqe32;
use crate::ring::io_uring_builder::SetFlagSetupDeferTaskrun;
use crate::ring::io_uring_builder::SetFlagSetupHybridIopoll;
use crate::ring::io_uring_builder::SetFlagSetupIopoll;
use crate::ring::io_uring_builder::SetFlagSetupNoMmap;
use crate::ring::io_uring_builder::SetFlagSetupNoSqarray;
use crate::ring::io_uring_builder::SetFlagSetupRDisabled;
use crate::ring::io_uring_builder::SetFlagSetupRegisteredFdOnly;
use crate::ring::io_uring_builder::SetFlagSetupSingleIssuer;
use crate::ring::io_uring_builder::SetFlagSetupSqAff;
use crate::ring::io_uring_builder::SetFlagSetupSqe128;
use crate::ring::io_uring_builder::SetFlagSetupSqpoll;
use crate::ring::io_uring_builder::SetFlagSetupSubmitAll;
use crate::ring::io_uring_builder::SetFlagSetupTaskrunFlag;
use crate::sys::SysResult as _;

/// The kernel's ring, held by liburing. `S` and `C` are the sizes of its
/// submission and completion entries.
#[non_exhaustive]
pub struct IoUring<'fd, S = crate::sqe::kind::Sqe64, C = crate::cqe::kind::Cqe16>
{
    /// The ring that liburing holds.
    ring: ::liburing_rs::io_uring,
    /// The borrow of the shared work queue's descriptor, and the two sizes
    /// of entry.
    marker: PhantomData<(&'fd ::liburing_rs::io_uring, S, C)>,
}

impl<S, C> Drop for IoUring<'_, S, C>
{
    /// Tears the ring down: liburing unmaps its queues and closes it.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let ring = &raw mut self.ring;
        // SAFETY: `ring` is the ring that `make` set up, and no borrow of it
        // outlives the ring.
        unsafe {
            ::liburing_rs::io_uring_queue_exit(ring);
        }
    }
}

impl<S, C> IoUring<'_, S, C>
{
    /// The ring that liburing holds, for the queues and the registrar that
    /// borrow it.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) fn ring(&self) -> NonNull<::liburing_rs::io_uring>
    {
        NonNull::from(&self.ring)
    }
}

impl<'fd> IoUring<'fd, crate::sqe::kind::Sqe64, crate::cqe::kind::Cqe16>
{
    /// A ring of 4096 entries with no setup flag.
    ///
    /// # Errors
    ///
    /// The kernel refuses the ring and gives its error number.
    ///
    /// # Specification
    ///
    /// - fails: the kernel refuses the ring.
    /// - executable: none — the outcome is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ring that this sets up takes a submission and
    ///   gives its completion.
    /// - witness: `cqueue::test::cqes::ready::one`
    #[inline]
    pub fn new() -> ::std::io::Result<Self>
    {
        Self::builder().build()
    }

    /// The builder of a ring with entries of the default sizes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn builder() -> IoUringBuilder<'fd, crate::sqe::kind::Sqe64, crate::cqe::kind::Cqe16>
    {
        Self::make()
    }
}

#[bon]
impl<'fd, S, C> IoUring<'fd, S, C>
where
    C: crate::cqe::Kind,
    S: crate::sqe::Kind,
{
    /// Sets up a ring of `entries` entries with the flags and the values
    /// that the builder holds. The builder's macro makes one setter for
    /// each argument. With `setup_mem` the rings live in the caller's
    /// memory, which stays borrowed for the ring's life, as
    /// `IORING_SETUP_NO_MMAP` asks.
    ///
    /// # Errors
    ///
    /// The kernel refuses the ring or the mark against fork, or the
    /// caller's memory is too small for the rings, and the call gives the
    /// error number.
    ///
    /// # Specification
    ///
    /// - fails: the kernel refuses the ring or the mark against fork, or the
    ///   caller's memory is too small for the rings.
    /// - executable: none — the outcome is the kernel's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each setup flag that the kernel takes alone gives a
    ///   ring, and `IORING_SETUP_NO_MMAP` with the caller's memory gives a ring
    ///   in that memory.
    /// - witness: `ring::test::new::with_setup_sqpoll`
    /// - witness: `ring::test::new::with_setup_cqsize`
    /// - witness: `ring::test::new::with_setup_no_mmap`
    #[builder(builder_type = IoUringBuilder, finish_fn = build, state_mod(vis = "pub(crate)"))]
    pub fn make(
        #[builder(default = Count(4096))] entries: Count<u32>,
        #[builder(default, setters(vis = ""))] flag_setup_iopoll: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_hybrid_iopoll: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_sqpoll: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_sq_aff: Switch,
        setup_cqsize: Option<Count<u32>>,
        #[builder(default, setters(vis = ""))] flag_setup_clamp: Switch,
        setup_attach_wq: Option<BorrowedFd<'fd>>,
        setup_mem: Option<Bytes<&'fd mut [u8]>>,
        #[builder(default, setters(vis = ""))] flag_setup_r_disabled: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_submit_all: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_coop_taskrun: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_taskrun_flag: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_sqe128: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_cqe32: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_single_issuer: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_defer_taskrun: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_no_mmap: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_registered_fd_only: Switch,
        #[builder(default, setters(vis = ""))] flag_setup_no_sqarray: Switch,
        #[builder(default)] sq_thread_cpu: Cpu,
        #[builder(default)] sq_thread_idle: Millis,
        #[builder(default)] dontfork: Switch,
    ) -> ::std::io::Result<Self>
    {
        let mut ring = ::liburing_rs::io_uring::default();

        let mut params = ::liburing_rs::io_uring_params::default();

        if flag_setup_iopoll.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_IOPOLL;
        }
        if flag_setup_hybrid_iopoll.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_HYBRID_IOPOLL;
        }
        if flag_setup_sqpoll.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_SQPOLL;
        }
        if flag_setup_sq_aff.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_SQ_AFF;
        }
        if flag_setup_clamp.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_CLAMP;
        }
        if flag_setup_r_disabled.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_R_DISABLED;
        }
        if flag_setup_submit_all.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_SUBMIT_ALL;
        }
        if flag_setup_coop_taskrun.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_COOP_TASKRUN;
        }
        if flag_setup_taskrun_flag.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_TASKRUN_FLAG;
        }
        if flag_setup_sqe128.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_SQE128;
        }
        if flag_setup_cqe32.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_CQE32;
        }
        if flag_setup_single_issuer.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_SINGLE_ISSUER;
        }
        if flag_setup_defer_taskrun.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_DEFER_TASKRUN;
        }
        if flag_setup_no_mmap.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_NO_MMAP;
        }
        if flag_setup_registered_fd_only.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_REGISTERED_FD_ONLY;
        }
        if flag_setup_no_sqarray.0 {
            params.flags |= ::liburing_rs::IORING_SETUP_NO_SQARRAY;
        }

        if let Some(Count(cq_entries)) = setup_cqsize {
            params.cq_entries = cq_entries;
            params.flags |= ::liburing_rs::IORING_SETUP_CQSIZE;
        }
        if let Some(fd) = setup_attach_wq {
            params.wq_fd = fd.as_raw_fd().cast_unsigned();
            params.flags |= ::liburing_rs::IORING_SETUP_ATTACH_WQ;
        }

        params.sq_thread_cpu = sq_thread_cpu.0;
        params.sq_thread_idle = sq_thread_idle.0;

        if let Some(Bytes(mem)) = setup_mem {
            // SAFETY: `ring` and `params` are this frame's own, `mem` stays
            // borrowed for `'fd`, which the ring does not outlive, and
            // liburing fills `ring` when the answer is not negative.
            Answer(unsafe {
                ::liburing_rs::io_uring_queue_init_mem(
                    entries.0,
                    &raw mut ring,
                    &raw mut params,
                    mem.as_mut_ptr().cast(),
                    mem.len(),
                )
            })
            .sys_uint()?;
        }
        else {
            // SAFETY: `ring` and `params` are this frame's own, and liburing
            // fills `ring` when the answer is zero.
            Answer(unsafe {
                ::liburing_rs::io_uring_queue_init_params(entries.0, &raw mut ring, &raw mut params)
            })
            .sys_zero()?;
        }

        if dontfork.0 {
            // SAFETY: `ring` is the ring that the call above set up.
            Answer(unsafe { ::liburing_rs::io_uring_ring_dontfork(&raw mut ring) }).sys_zero()?;
        }

        Ok(Self {
            ring,
            marker: PhantomData, // tarpaulin
        })
    }

    /// A borrow of the completion queue.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn cqueue(&mut self) -> CompletionQueue<'_, C>
    {
        CompletionQueue::new(self)
    }

    /// A borrow of the submission queue.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn squeue(&mut self) -> SubmissionQueue<'_, S>
    {
        SubmissionQueue::new(self)
    }

    /// The registrar of the ring's file table.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn registrar(&self) -> Registrar<'_>
    {
        Registrar::new(self)
    }

    /// The ring's own descriptor.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn ring_fd(&self) -> BorrowedFd<'_>
    {
        // SAFETY: the descriptor stays open while the ring lives, and the
        // borrow ends with the borrow of `self`.
        unsafe { BorrowedFd::borrow_raw(self.ring.ring_fd) }
    }

    /// Borrows of both queues at once.
    ///
    /// # Specification
    ///
    /// trivial.
    #[must_use]
    #[inline]
    pub fn queues(&mut self) -> (SubmissionQueue<'_, S>, CompletionQueue<'_, C>)
    {
        (SubmissionQueue::new(self), CompletionQueue::new(self))
    }
}

/// A builder method that sets one setup flag: the method's name, the
/// builder's setter, and the builder's two state types of the flag.
macro_rules! io_uring_flag_setup {
    ($method:ident, $setter:ident, $SetFlagSetup:ident, $FlagSetup:ident) => {
        /// Sets the setup flag that the method names. The builder's type
        /// refuses a second call.
        ///
        /// # Specification
        ///
        /// trivial.
        #[inline]
        pub fn $method(self) -> IoUringBuilder<'fd, S, C, $SetFlagSetup<State>>
        where
            State::$FlagSetup: IsUnset,
        {
            self.$setter(Switch(true))
        }
    };
}

impl<'fd, S, C, State: io_uring_builder::State> IoUringBuilder<'fd, S, C, State>
where
    C: crate::cqe::Kind,
    S: crate::sqe::Kind,
{
    io_uring_flag_setup!(
        setup_iopoll,
        flag_setup_iopoll,
        SetFlagSetupIopoll,
        FlagSetupIopoll
    );

    io_uring_flag_setup!(
        setup_hybrid_iopoll,
        flag_setup_hybrid_iopoll,
        SetFlagSetupHybridIopoll,
        FlagSetupHybridIopoll
    );

    io_uring_flag_setup!(
        setup_sqpoll,
        flag_setup_sqpoll,
        SetFlagSetupSqpoll,
        FlagSetupSqpoll
    );

    io_uring_flag_setup!(
        setup_sq_aff,
        flag_setup_sq_aff,
        SetFlagSetupSqAff,
        FlagSetupSqAff
    );

    io_uring_flag_setup!(
        setup_clamp,
        flag_setup_clamp,
        SetFlagSetupClamp,
        FlagSetupClamp
    );

    io_uring_flag_setup!(
        setup_r_disabled,
        flag_setup_r_disabled,
        SetFlagSetupRDisabled,
        FlagSetupRDisabled
    );

    io_uring_flag_setup!(
        setup_submit_all,
        flag_setup_submit_all,
        SetFlagSetupSubmitAll,
        FlagSetupSubmitAll
    );

    io_uring_flag_setup!(
        setup_coop_taskrun,
        flag_setup_coop_taskrun,
        SetFlagSetupCoopTaskrun,
        FlagSetupCoopTaskrun
    );

    io_uring_flag_setup!(
        setup_taskrun_flag,
        flag_setup_taskrun_flag,
        SetFlagSetupTaskrunFlag,
        FlagSetupTaskrunFlag
    );

    io_uring_flag_setup!(
        setup_single_issuer,
        flag_setup_single_issuer,
        SetFlagSetupSingleIssuer,
        FlagSetupSingleIssuer
    );

    io_uring_flag_setup!(
        setup_defer_taskrun,
        flag_setup_defer_taskrun,
        SetFlagSetupDeferTaskrun,
        FlagSetupDeferTaskrun
    );

    io_uring_flag_setup!(
        setup_no_mmap,
        flag_setup_no_mmap,
        SetFlagSetupNoMmap,
        FlagSetupNoMmap
    );

    io_uring_flag_setup!(
        setup_registered_fd_only,
        flag_setup_registered_fd_only,
        SetFlagSetupRegisteredFdOnly,
        FlagSetupRegisteredFdOnly
    );

    io_uring_flag_setup!(
        setup_no_sqarray,
        flag_setup_no_sqarray,
        SetFlagSetupNoSqarray,
        FlagSetupNoSqarray
    );

    /// Sets the flag for completion entries of 32 bytes, and makes them the
    /// ring's completion type.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn setup_cqe32(
        self
    ) -> IoUringBuilder<'fd, S, crate::cqe::kind::Cqe32, SetFlagSetupCqe32<State>>
    where
        State::FlagSetupCqe32: IsUnset,
    {
        // SAFETY: the two builder types differ in a type parameter alone,
        // which the builder holds as a marker of no size.
        let this: IoUringBuilder<'_, S, crate::cqe::kind::Cqe32, State> =
            unsafe { ::core::mem::transmute(self) };
        this.flag_setup_cqe32(Switch(true)) // tarpaulin
    }

    /// Sets the flag for submission entries of 128 bytes, and makes them the
    /// ring's submission type.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    pub fn setup_sqe128(
        self
    ) -> IoUringBuilder<'fd, crate::sqe::kind::Sqe128, C, SetFlagSetupSqe128<State>>
    where
        State::FlagSetupSqe128: IsUnset,
    {
        // SAFETY: the two builder types differ in a type parameter alone,
        // which the builder holds as a marker of no size.
        let this: IoUringBuilder<'_, crate::sqe::kind::Sqe128, C, State> =
            unsafe { ::core::mem::transmute(self) };
        this.flag_setup_sqe128(Switch(true)) // tarpaulin
    }
}

#[cfg(test)]
pub mod test
{
    use crate::arg::Bytes;
    use crate::arg::Count;
    use crate::arg::Cpu;
    use crate::arg::Millis;
    use crate::arg::Switch;
    use crate::ring::IoUring;

    mod new
    {
        use super::*;

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_entries()
        {
            IoUring::builder().entries(Count(1024)).build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_iopoll()
        {
            IoUring::builder().setup_iopoll().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_hybrid_iopoll()
        {
            IoUring::builder()
                .setup_iopoll()
                .setup_hybrid_iopoll()
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_sqpoll()
        {
            IoUring::builder().setup_sqpoll().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_sq_aff()
        {
            // NOTE: tarpaulin runs cause `::num_cpus::get()` to return 1.
            let cpus = ::num_cpus::get_physical();
            let sq_thread_cpu = Cpu(u32::try_from(cpus).unwrap() - 1);
            IoUring::builder()
                .setup_sqpoll()
                .setup_sq_aff()
                .sq_thread_cpu(sq_thread_cpu)
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_cqsize()
        {
            IoUring::builder()
                .entries(Count(128))
                .setup_cqsize(Count(256))
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_clamp()
        {
            IoUring::builder().setup_clamp().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_attach_wq()
        {
            let ring = IoUring::builder().build().unwrap();
            let ring_fd = ring.ring_fd();
            IoUring::builder().setup_attach_wq(ring_fd).build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_r_disabled()
        {
            IoUring::builder().setup_r_disabled().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_submit_all()
        {
            IoUring::builder().setup_submit_all().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_coop_taskrun()
        {
            IoUring::builder().setup_coop_taskrun().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_taskrun_flag()
        {
            IoUring::builder()
                .setup_coop_taskrun()
                .setup_taskrun_flag()
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_sqe128()
        {
            IoUring::builder().setup_sqe128().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_cqe32()
        {
            IoUring::builder().setup_cqe32().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_single_issuer()
        {
            IoUring::builder().setup_single_issuer().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_defer_taskrun()
        {
            IoUring::builder()
                .setup_single_issuer()
                .setup_defer_taskrun()
                .build()
                .unwrap();
        }

        /// The size of a block of the rings' memory: 64 KiB, a whole number
        /// of pages for each page size up to 64 KiB.
        const BLOCK: usize = 64 * 1024;

        /// A ring of 8 entries in the caller's memory: the tail of three
        /// blocks from the first boundary of a block, which is a page
        /// boundary, as the kernel asks.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_no_mmap()
        {
            let mut mem = vec![0_u8; 3 * BLOCK];
            let start = mem.as_ptr().align_offset(BLOCK);
            let (_, mem) = mem.split_at_mut(start);
            IoUring::builder()
                .entries(Count(8))
                .setup_no_mmap()
                .setup_mem(Bytes(mem))
                .build()
                .unwrap();
        }

        /// `IORING_SETUP_REGISTERED_FD_ONLY` needs `IORING_SETUP_NO_MMAP`, so
        /// the ring takes the caller's memory as above.
        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_registered_fd_only()
        {
            let mut mem = vec![0_u8; 3 * BLOCK];
            let start = mem.as_ptr().align_offset(BLOCK);
            let (_, mem) = mem.split_at_mut(start);
            IoUring::builder()
                .entries(Count(8))
                .setup_no_mmap()
                .setup_registered_fd_only()
                .setup_mem(Bytes(mem))
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_setup_no_sqarray()
        {
            IoUring::builder().setup_no_sqarray().build().unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_sq_thread_cpu()
        {
            // NOTE: tarpaulin runs cause `::num_cpus::get()` to return 1.
            let cpus = ::num_cpus::get_physical();
            let sq_thread_cpu = Cpu(u32::try_from(cpus).unwrap() - 1);
            IoUring::builder()
                .setup_sqpoll()
                .setup_sq_aff()
                .sq_thread_cpu(sq_thread_cpu)
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_sq_thread_idle()
        {
            let sq_thread_idle = Millis(250u32);
            IoUring::builder()
                .setup_sqpoll()
                .sq_thread_idle(sq_thread_idle)
                .build()
                .unwrap();
        }

        #[test]
        #[cfg_attr(
            miri,
            ignore = "it sets up a ring through liburing, which Miri cannot run"
        )]
        fn with_dontfork()
        {
            IoUring::builder().dontfork(Switch(true)).build().unwrap();
        }
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn new()
    {
        IoUring::new().unwrap();
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn cqueue()
    {
        let mut ring = IoUring::new().unwrap();
        ring.cqueue();
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn squeue()
    {
        let mut ring = IoUring::new().unwrap();
        ring.squeue();
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn queues()
    {
        let mut ring = IoUring::new().unwrap();
        drop(ring.queues());
    }

    #[test]
    #[cfg_attr(
        miri,
        ignore = "it sets up a ring through liburing, which Miri cannot run"
    )]
    fn registrar()
    {
        let ring = IoUring::new().unwrap();
        drop(ring.registrar());
    }

    /// On riscv64 the bindings give glibc's context types the sizes of the
    /// host's headers, so the ring builds there.
    #[cfg(all(target_os = "linux", target_arch = "riscv64"))]
    #[test]
    fn context_types_take_the_sizes_of_the_headers_7720()
    {
        use ::core::mem::size_of;
        assert_eq!(size_of::<::liburing_rs::__riscv_mc_fp_state>(), 528);
        assert_eq!(size_of::<::liburing_rs::mcontext_t>(), 784);
        assert_eq!(size_of::<::liburing_rs::ucontext_t>(), 960);
    }
}
