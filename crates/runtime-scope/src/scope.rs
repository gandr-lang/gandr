use ::core::cell::RefCell;
use ::core::marker::PhantomData;
use ::gandr_runtime_uring::IoUring;
use ::gandr_runtime_uring::Sqe64;
use ::slab::Slab;

use crate::completion::Completion;
use crate::submission::Submission;

pub struct Scope<'tsk, 'env: 'tsk>
{
    io: &'tsk RefCell<IoUring<'static>>,
    tasks: &'tsk RefCell<Slab<Submission>>,
    phd_env: PhantomData<&'env mut &'env ()>,
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk, 'env: 'tsk> Scope<'tsk, 'env>
{
    pub(crate) fn new(
        io: &'tsk RefCell<IoUring<'static>>,
        tasks: &'tsk RefCell<Slab<Submission>>,
    ) -> Self
    {
        Self {
            io,
            tasks,
            phd_tsk: PhantomData,
            phd_env: PhantomData,
        }
    }

    /// Prepares the next free entry of the ring with `prep`, and gives the
    /// completion of its operation. The run loop submits the entry.
    pub fn request<P>(
        &'tsk self,
        prep: P,
    ) -> Completion<'tsk>
    where
        P: for<'sq> FnOnce(&mut Sqe64<'sq>),
    {
        let mut io = self.io.borrow_mut();
        let mut sq = io.squeue();
        let Some(mut sqe) = sq.get_sqe()
        else {
            return Completion::full();
        };
        prep(&mut sqe);
        let (cqe_tx, cqe_rx) = ::oneshot::channel();
        let key = self.tasks.borrow_mut().insert(Submission::new(cqe_tx));
        // A key of the slab fits the user data on every Linux target.
        let data = u64::try_from(key).unwrap_or(u64::MAX);
        // SAFETY: the user data is a number that the kernel only hands back.
        unsafe {
            sqe.set_data64(data);
        }
        Completion::new(cqe_rx)
    }
}
