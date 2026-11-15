use ::core::marker::PhantomData;

use crate::Sender;
use crate::completion::Completion;
use crate::submission::Submission;

pub struct Scope<'tsk, 'env: 'tsk> {
    req_tx: Sender<Submission>,
    phd_env: PhantomData<&'env mut &'env ()>,
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk, 'env: 'tsk> Scope<'tsk, 'env> {
    pub(crate) fn new(req_tx: Sender<Submission>) -> Self {
        Self {
            req_tx,
            phd_tsk: PhantomData,
            phd_env: PhantomData,
        }
    }

    pub fn request(&'tsk self, sqe: ::io_uring::squeue::Entry) -> Completion<'tsk> {
        let (cqe_tx, cqe_rx) = ::oneshot::channel();
        let sqe = Submission::new(sqe, cqe_tx);
        let sqe = self.req_tx.send(sqe);
        Completion::new(sqe, cqe_rx)
    }
}
