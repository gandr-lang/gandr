use ::bon::bon;
use ::core::marker::PhantomData;
use ::std::os::fd::AsRawFd as _;
use ::std::os::fd::BorrowedFd;

use self::io_uring_builder::IsUnset;
use crate::CompletionQueue;
use crate::Registrar;
use crate::SubmissionQueue;
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

#[non_exhaustive]
pub struct IoUring<'fd, S = crate::sqe::kind::Sqe64, C = crate::cqe::kind::Cqe16>
{
    pub(crate) ring: ::liburing_rs::io_uring,
    marker: PhantomData<(&'fd ::liburing_rs::io_uring, S, C)>,
}

impl<S, C> Drop for IoUring<'_, S, C>
{
    fn drop(&mut self)
    {
        let ring = &raw mut self.ring;
        // SAFETY: FIXME
        unsafe { ::liburing_rs::io_uring_queue_exit(ring) };
    }
}

impl<'fd> IoUring<'fd, crate::sqe::kind::Sqe64, crate::cqe::kind::Cqe16>
{
    /// # Errors
    pub fn new() -> ::std::io::Result<Self>
    {
        Self::builder().build()
    }

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
    /// # Errors
    #[builder(builder_type = IoUringBuilder, finish_fn = build, state_mod(vis = "pub(crate)"))]
    pub fn make(
        #[builder(default = 4096)] entries: u32,
        #[builder(default, setters(vis = ""))] flag_setup_iopoll: bool,
        #[builder(default, setters(vis = ""))] flag_setup_hybrid_iopoll: bool,
        #[builder(default, setters(vis = ""))] flag_setup_sqpoll: bool,
        #[builder(default, setters(vis = ""))] flag_setup_sq_aff: bool,
        setup_cqsize: Option<u32>,
        #[builder(default, setters(vis = ""))] flag_setup_clamp: bool,
        setup_attach_wq: Option<BorrowedFd<'fd>>,
        #[builder(default, setters(vis = ""))] flag_setup_r_disabled: bool,
        #[builder(default, setters(vis = ""))] flag_setup_submit_all: bool,
        #[builder(default, setters(vis = ""))] flag_setup_coop_taskrun: bool,
        #[builder(default, setters(vis = ""))] flag_setup_taskrun_flag: bool,
        #[builder(default, setters(vis = ""))] flag_setup_sqe128: bool,
        #[builder(default, setters(vis = ""))] flag_setup_cqe32: bool,
        #[builder(default, setters(vis = ""))] flag_setup_single_issuer: bool,
        #[builder(default, setters(vis = ""))] flag_setup_defer_taskrun: bool,
        #[builder(default, setters(vis = ""))] flag_setup_no_mmap: bool,
        #[builder(default, setters(vis = ""))] flag_setup_registered_fd_only: bool,
        #[builder(default, setters(vis = ""))] flag_setup_no_sqarray: bool,
        #[builder(default)] sq_thread_cpu: u32,
        #[builder(default)] sq_thread_idle: u32,
        #[builder(default)] dontfork: bool,
    ) -> ::std::io::Result<Self>
    {
        let mut ring = ::liburing_rs::io_uring::default();

        let mut params = ::liburing_rs::io_uring_params::default();

        if flag_setup_iopoll {
            params.flags |= ::liburing_rs::IORING_SETUP_IOPOLL;
        }
        if flag_setup_hybrid_iopoll {
            params.flags |= ::liburing_rs::IORING_SETUP_HYBRID_IOPOLL;
        }
        if flag_setup_sqpoll {
            params.flags |= ::liburing_rs::IORING_SETUP_SQPOLL;
        }
        if flag_setup_sq_aff {
            params.flags |= ::liburing_rs::IORING_SETUP_SQ_AFF;
        }
        if flag_setup_clamp {
            params.flags |= ::liburing_rs::IORING_SETUP_CLAMP;
        }
        if flag_setup_r_disabled {
            params.flags |= ::liburing_rs::IORING_SETUP_R_DISABLED;
        }
        if flag_setup_submit_all {
            params.flags |= ::liburing_rs::IORING_SETUP_SUBMIT_ALL;
        }
        if flag_setup_coop_taskrun {
            params.flags |= ::liburing_rs::IORING_SETUP_COOP_TASKRUN;
        }
        if flag_setup_taskrun_flag {
            params.flags |= ::liburing_rs::IORING_SETUP_TASKRUN_FLAG;
        }
        if flag_setup_sqe128 {
            params.flags |= ::liburing_rs::IORING_SETUP_SQE128;
        }
        if flag_setup_cqe32 {
            params.flags |= ::liburing_rs::IORING_SETUP_CQE32;
        }
        if flag_setup_single_issuer {
            params.flags |= ::liburing_rs::IORING_SETUP_SINGLE_ISSUER;
        }
        if flag_setup_defer_taskrun {
            params.flags |= ::liburing_rs::IORING_SETUP_DEFER_TASKRUN;
        }
        if flag_setup_no_mmap {
            params.flags |= ::liburing_rs::IORING_SETUP_NO_MMAP;
        }
        if flag_setup_registered_fd_only {
            params.flags |= ::liburing_rs::IORING_SETUP_REGISTERED_FD_ONLY;
        }
        if flag_setup_no_sqarray {
            params.flags |= ::liburing_rs::IORING_SETUP_NO_SQARRAY;
        }

        if let Some(cq_entries) = setup_cqsize {
            params.cq_entries = cq_entries;
            params.flags |= ::liburing_rs::IORING_SETUP_CQSIZE;
        }
        if let Some(fd) = setup_attach_wq {
            params.wq_fd = fd.as_raw_fd().cast_unsigned();
            params.flags |= ::liburing_rs::IORING_SETUP_ATTACH_WQ;
        }

        params.sq_thread_cpu = sq_thread_cpu;
        params.sq_thread_idle = sq_thread_idle;

        // SAFETY: FIXME
        unsafe {
            ::liburing_rs::io_uring_queue_init_params(entries, &raw mut ring, &raw mut params)
        }
        .sys_zero()?;

        if dontfork {
            // SAFETY: FIXME
            unsafe { ::liburing_rs::io_uring_ring_dontfork(&raw mut ring) }.sys_zero()?;
        }

        Ok(Self {
            ring,
            marker: PhantomData, // tarpaulin
        })
    }

    pub fn cqueue(&mut self) -> CompletionQueue<'_, C>
    {
        CompletionQueue::new(self)
    }

    pub fn squeue(&mut self) -> SubmissionQueue<'_, S>
    {
        SubmissionQueue::new(self)
    }

    #[must_use]
    pub fn registrar(&self) -> Registrar<'_>
    {
        Registrar::new(self)
    }

    #[must_use]
    pub const fn ring_fd(&self) -> BorrowedFd<'_>
    {
        // SAFETY:
        unsafe { BorrowedFd::borrow_raw(self.ring.ring_fd) }
    }

    #[must_use]
    pub fn queues(&mut self) -> (SubmissionQueue<'_, S>, CompletionQueue<'_, C>)
    {
        (SubmissionQueue::new(self), CompletionQueue::new(self))
    }
}

macro_rules! io_uring_flag_setup {
    ($method:ident, $setter:ident, $SetFlagSetup:ident, $FlagSetup:ident) => {
        pub fn $method(self) -> IoUringBuilder<'fd, S, C, $SetFlagSetup<State>>
        where
            State::$FlagSetup: IsUnset,
        {
            self.$setter(true)
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

    pub fn setup_cqe32(
        self
    ) -> IoUringBuilder<'fd, S, crate::cqe::kind::Cqe32, SetFlagSetupCqe32<State>>
    where
        State::FlagSetupCqe32: IsUnset,
    {
        // SAFETY:
        let this: IoUringBuilder<S, crate::cqe::kind::Cqe32, State> =
            unsafe { ::core::mem::transmute(self) };
        this.flag_setup_cqe32(true) // tarpaulin
    }

    pub fn setup_sqe128(
        self
    ) -> IoUringBuilder<'fd, crate::sqe::kind::Sqe128, C, SetFlagSetupSqe128<State>>
    where
        State::FlagSetupSqe128: IsUnset,
    {
        // SAFETY:
        let this: IoUringBuilder<crate::sqe::kind::Sqe128, C, State> =
            unsafe { ::core::mem::transmute(self) };
        this.flag_setup_sqe128(true) // tarpaulin
    }
}

#[cfg(test)]
pub(crate) mod test
{
    use crate::ring::IoUring;

    mod new
    {
        use super::*;

        #[test]
        fn with_entries()
        {
            IoUring::builder().entries(1024).build().unwrap();
        }

        #[test]
        fn with_setup_iopoll()
        {
            IoUring::builder().setup_iopoll().build().unwrap();
        }

        #[test]
        fn with_setup_hybrid_iopoll()
        {
            IoUring::builder()
                .setup_iopoll()
                .setup_hybrid_iopoll()
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_sqpoll()
        {
            IoUring::builder().setup_sqpoll().build().unwrap();
        }

        #[test]
        fn with_setup_sq_aff()
        {
            // NOTE: tarpaulin runs cause `::num_cpus::get()` to return 1.
            let cpus = ::num_cpus::get_physical();
            let sq_thread_cpu = u32::try_from(cpus).unwrap() - 1;
            IoUring::builder()
                .setup_sqpoll()
                .setup_sq_aff()
                .sq_thread_cpu(sq_thread_cpu)
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_cqsize()
        {
            IoUring::builder()
                .entries(128)
                .setup_cqsize(256)
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_clamp()
        {
            IoUring::builder().setup_clamp().build().unwrap();
        }

        #[test]
        fn with_setup_attach_wq()
        {
            let ring = IoUring::builder().build().unwrap();
            let ring_fd = ring.ring_fd();
            IoUring::builder().setup_attach_wq(ring_fd).build().unwrap();
        }

        #[test]
        fn with_setup_r_disabled()
        {
            IoUring::builder().setup_r_disabled().build().unwrap();
        }

        #[test]
        fn with_setup_submit_all()
        {
            IoUring::builder().setup_submit_all().build().unwrap();
        }

        #[test]
        fn with_setup_coop_taskrun()
        {
            IoUring::builder().setup_coop_taskrun().build().unwrap();
        }

        #[test]
        fn with_setup_taskrun_flag()
        {
            IoUring::builder()
                .setup_coop_taskrun()
                .setup_taskrun_flag()
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_sqe128()
        {
            IoUring::builder().setup_sqe128().build().unwrap();
        }

        #[test]
        fn with_setup_cqe32()
        {
            IoUring::builder().setup_cqe32().build().unwrap();
        }

        #[test]
        fn with_setup_single_issuer()
        {
            IoUring::builder().setup_single_issuer().build().unwrap();
        }

        #[test]
        fn with_setup_defer_taskrun()
        {
            IoUring::builder()
                .setup_single_issuer()
                .setup_defer_taskrun()
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_no_mmap()
        {
            IoUring::builder().setup_no_mmap().build().unwrap();
        }

        #[test]
        fn with_setup_registered_fd_only()
        {
            IoUring::builder()
                .setup_no_mmap()
                .setup_registered_fd_only()
                .build()
                .unwrap();
        }

        #[test]
        fn with_setup_no_sqarray()
        {
            IoUring::builder().setup_no_sqarray().build().unwrap();
        }

        #[test]
        fn with_sq_thread_cpu()
        {
            // NOTE: tarpaulin runs cause `::num_cpus::get()` to return 1.
            let cpus = ::num_cpus::get_physical();
            let sq_thread_cpu = u32::try_from(cpus).unwrap() - 1;
            IoUring::builder()
                .setup_sqpoll()
                .setup_sq_aff()
                .sq_thread_cpu(sq_thread_cpu)
                .build()
                .unwrap();
        }

        #[test]
        fn with_sq_thread_idle()
        {
            let sq_thread_idle = 250u32;
            IoUring::builder()
                .setup_sqpoll()
                .sq_thread_idle(sq_thread_idle)
                .build()
                .unwrap();
        }

        #[test]
        fn with_dontfork()
        {
            IoUring::builder().dontfork(true).build().unwrap();
        }
    }

    #[test]
    fn new()
    {
        IoUring::new().unwrap();
    }

    #[test]
    fn cqueue()
    {
        let mut ring = IoUring::new().unwrap();
        ring.cqueue();
    }

    #[test]
    fn squeue()
    {
        let mut ring = IoUring::new().unwrap();
        ring.squeue();
    }

    #[test]
    fn queues()
    {
        let mut ring = IoUring::new().unwrap();
        drop(ring.queues());
    }

    #[test]
    fn registrar()
    {
        let ring = IoUring::new().unwrap();
        drop(ring.registrar());
    }
}
