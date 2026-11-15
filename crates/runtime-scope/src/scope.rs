use ::core::cell::RefCell;
use ::core::marker::PhantomData;
use ::gandr_runtime_uring::IoUring;
use ::gandr_runtime_uring::Sqe64;

use crate::completion::Completion;
use crate::runtime::reap;
use crate::submission::Table;

pub struct Scope<'tsk, 'env: 'tsk>
{
    io: &'tsk RefCell<IoUring<'static>>,
    table: &'tsk Table,
    phd_env: PhantomData<&'env mut &'env ()>,
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk, 'env: 'tsk> Scope<'tsk, 'env>
{
    pub(crate) fn new(
        io: &'tsk RefCell<IoUring<'static>>,
        table: &'tsk Table,
    ) -> Self
    {
        Self {
            io,
            table,
            phd_tsk: PhantomData,
            phd_env: PhantomData,
        }
    }

    /// A free slot of the table. When every slot is taken and the kernel
    /// holds some of their operations, the caller waits for a drain: the
    /// ring completes at least one, and its slot may come free. Gives
    /// nothing when no slot comes free.
    fn slot(&self) -> Option<usize>
    {
        loop {
            if let Some(key) = self.table.take() {
                return Some(key);
            }
            if self.table.held() == 0 {
                return None;
            }
            reap(self.io, self.table).ok()?;
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
        let Some(key) = self.slot()
        else {
            return Completion::full(self.table);
        };
        let mut io = self.io.borrow_mut();
        let mut sq = io.squeue();
        let Some(mut sqe) = sq.get_sqe()
        else {
            self.table.give_back(key);
            return Completion::full(self.table);
        };
        prep(&mut sqe);
        // A key of the table fits the user data on every Linux target.
        let data = u64::try_from(key).unwrap_or(u64::MAX);
        // SAFETY: the user data is a number that the kernel only hands back.
        unsafe {
            sqe.set_data64(data);
        }
        Completion::new(self.table, key)
    }
}
