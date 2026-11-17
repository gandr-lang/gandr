//! The scope: the handle through which the tasks of one run request the
//! kernel's operations.

use ::core::cell::RefCell;
use ::core::marker::PhantomData;
use ::gandr_runtime_uring::IoUring;
use ::gandr_runtime_uring::Sqe64;
use ::gandr_runtime_uring::arg::UserData;

use crate::completion::Completion;
use crate::error::RuntimeError;
use crate::runtime::reap;
use crate::submission::Hold;
use crate::submission::Key;
use crate::submission::Table;

/// The scope of one run. `'env` is the lifetime of the captures of the
/// scope's future, and `'tsk` the lifetime of the scope's tasks, which
/// borrow the scope and the memory that `'env` lends them.
pub struct Scope<'tsk, 'env: 'tsk>
{
    /// The kernel's ring.
    io: &'tsk RefCell<IoUring<'static>>,
    /// The table of the operations in flight.
    table: &'tsk Table,
    /// The brand of the captures.
    phd_env: PhantomData<&'env mut &'env ()>,
    /// The brand of the tasks.
    phd_tsk: PhantomData<&'tsk mut &'tsk ()>,
}

impl<'tsk, 'env: 'tsk> Scope<'tsk, 'env>
{
    /// The scope of a run on `io` with the table `table`.
    ///
    /// # Specification
    ///
    /// trivial.
    pub(crate) const fn new(
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
    /// ring completes at least one, and its slot may come free.
    ///
    /// # Specification
    ///
    /// - provides: the key of a slot that the call took.
    /// - fails: `Full` when every slot is taken and the kernel holds none of
    ///   their operations, and the error of a drain.
    /// - panics: none.
    /// - executable: none — the slots' states are cells that no predicate of
    ///   the call reads before it.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a request past the table's depth waits for a drain,
    ///   and gives `Full` when the drain frees no slot.
    /// - witness: `runtime::test::run::full`
    fn slot(&self) -> Result<Key, RuntimeError>
    {
        loop {
            if let Some(key) = self.table.take() {
                return Ok(key);
            }
            if self.table.hold() == Hold::Drained {
                return Err(RuntimeError::Full);
            }
            reap(self.io, self.table)?;
        }
    }

    /// Prepares the next free entry of the ring with `prep`, and gives the
    /// completion of its operation. The run loop submits the entry.
    ///
    /// # Specification
    ///
    /// - requires: the memory that `prep` gives the entry outlives `'tsk`.
    /// - ensures: the entry's user data names the operation's slot.
    /// - provides: the completion of the operation, which reads its slot.
    /// - fails: the completion gives `Full` when no slot comes free, and the
    ///   error of a drain.
    /// - panics: none.
    /// - executable: none — the entry is the kernel's memory, and the call
    ///   holds nothing to check it against.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a thousand no-ops each complete through their slots,
    ///   and a request past the table's depth gives `Full`.
    /// - witness: `tests::path::request::a_request_allocates_nothing_after_the_start`
    /// - witness: `runtime::test::run::full`
    #[inline]
    pub fn request<P>(
        &'tsk self,
        prep: P,
    ) -> Completion<'tsk>
    where
        P: for<'sq> FnOnce(&mut Sqe64<'sq>),
    {
        let key = match self.slot() {
            Ok(key) => key,
            Err(error) => return Completion::refused(self.table, error),
        };
        let Ok(data) = u64::try_from(key)
        else {
            self.table.give_back(key);
            return Completion::refused(self.table, RuntimeError::Full);
        };
        let mut io = self.io.borrow_mut();
        let mut sq = io.squeue();
        let Some(mut sqe) = sq.get_sqe()
        else {
            self.table.give_back(key);
            return Completion::refused(self.table, RuntimeError::Full);
        };
        prep(&mut sqe);
        // SAFETY: the user data is a number that the kernel only hands back.
        unsafe {
            sqe.set_data64(UserData(data));
        }
        Completion::new(self.table, key)
    }
}
