use ::alloc::sync::Arc;
use ::core::marker::PhantomData;
use ::core::sync::atomic::AtomicU32;

use crate::completion::Cqe;

pub(crate) struct Submission
{
    pub(crate) cqe_tx: ::oneshot::Sender<Cqe>,
    pub(crate) cancel: Arc<AtomicU32>,
}

impl Submission
{
    pub(crate) fn new(cqe_tx: ::oneshot::Sender<Cqe>) -> Self
    {
        let cancel = Arc::new(AtomicU32::new(0u32));
        Self { cqe_tx, cancel }
    }
}
