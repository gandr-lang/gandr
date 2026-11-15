use ::alloc::sync::Arc;
use ::core::marker::PhantomData;
use ::core::sync::atomic::AtomicU32;

use crate::completion::Cqe;

#[expect(
    clippy::field_scoped_visibility_modifiers,
    reason = "the owner's text; the bounded queue of #7652 replaces the struct"
)]
pub struct Submission
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
