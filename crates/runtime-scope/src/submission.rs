use ::alloc::sync::Arc;
use ::core::marker::PhantomData;
use ::core::sync::atomic::AtomicU32;

pub(crate) struct Submission {
    pub(crate) sqe: ::io_uring::squeue::Entry,
    pub(crate) cqe_tx: ::oneshot::Sender<::io_uring::cqueue::Entry>,
    pub(crate) cancel: Arc<AtomicU32>,
}

impl Submission {
    pub(crate) fn new(sqe: ::io_uring::squeue::Entry, cqe_tx: ::oneshot::Sender<::io_uring::cqueue::Entry>) -> Self {
        let cancel = Arc::new(AtomicU32::new(0u32));
        Self { sqe, cqe_tx, cancel }
    }
}
