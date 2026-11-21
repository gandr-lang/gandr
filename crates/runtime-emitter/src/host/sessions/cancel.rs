//! An end abandoned before its protocol ended is cancelled, the daimon its
//! peer is owed: the messages queued at it are given up, an end one carries
//! cancelled in turn, and a task waiting at its peer is readied to be
//! abandoned. A send or a select to a cancelled peer, and a receive or an
//! offer from one with nothing queued, abandon the acting task's
//! continuation: its frames' unwinds run, every end it still holds is
//! cancelled, and the task ends. A root so ended leaves the run stuck at that
//! action, cancelled.

use gandr_core_sequent::CommandId;
use gandr_runtime_stencils::Refusal;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Word;

use super::super::Calls;
use super::super::give_up;
use super::super::unit;
use super::ChannelIndex;
use super::Message;
use super::Party;
use super::Ready;
use super::Standing;
use super::Task;
use super::capability_end;
use super::end_of;
use crate::transfer::owned;

impl Calls<'_, '_>
{
    /// Cancel each open end the cells `held` hold, as [`Self::cancel`] does:
    /// the session ends an abandoned stack's frames hold.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::cancel`].
    pub(in crate::host) fn cancel_cells(
        &mut self,
        runtime: &mut Runtime,
        held: &[Word],
    ) -> Result<(), Refusal>
    {
        let ends = held.iter().filter_map(|&cell| end_of(cell).ok()).collect();
        self.cancel(runtime, ends)
    }

    /// Cancel `ends` and every end their cancellation reaches. An end still
    /// open is marked cancelled; the messages queued at it, which no task will
    /// take, are given up, and an end one carries is cancelled in turn; and a
    /// task waiting at its peer is readied to be abandoned. A closed or an
    /// already cancelled end is left as it is.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for an end of a channel no fork made.
    pub(super) fn cancel(
        &mut self,
        runtime: &mut Runtime,
        mut ends: Vec<(ChannelIndex, Party)>,
    ) -> Result<(), Refusal>
    {
        let sites = self.sites;
        while let Some((channel, party)) = ends.pop() {
            let end = self.scheduler.end(channel, party)?;
            if matches!(end.standing, Standing::Closed | Standing::Cancelled) {
                continue;
            }
            end.standing = Standing::Cancelled;
            end.noted.clear();
            for message in core::mem::take(&mut end.queued) {
                if let Message::Payload(payload) = message {
                    ends.extend(capability_end(payload).ok());
                    // SAFETY: a queued payload holds one owner of a value of
                    // the run's heap, which no task takes once its end is
                    // cancelled.
                    unsafe {
                        give_up(runtime, payload, |object| owned(object, sites));
                    }
                }
            }
            if let Some(parked) = self.scheduler.end(channel, party.peer())?.waiting.take() {
                self.scheduler.parked = self.scheduler.parked.saturating_sub(1);
                self.scheduler.ready.push_back(Ready::Abandon {
                    task: parked.task,
                    stack: parked.stack,
                    at: parked.at,
                });
            }
        }
        Ok(())
    }

    /// Abandon the running task's continuation at the action `at`, which met
    /// an end its peer cancelled: its frames from the base captured, then
    /// ended as [`Self::forsake`] ends them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::capture`] and [`Self::forsake`].
    pub(super) fn abandoned(
        &mut self,
        runtime: &mut Runtime,
        at: CommandId,
    ) -> Result<Word, Refusal>
    {
        let base = runtime.frame_base();
        let stack = self.capture(runtime, base)?;
        self.forsake(runtime, stack, at)
    }

    /// End the running task, its frames `stack` abandoned at the action `at`:
    /// above the base, a frame for each access the stack captured, entering
    /// its unwind, as [`Self::unwound`] pushes them; every end the task still
    /// holds cancelled; and the topmost frame popped with the unit in hand, so
    /// the unwinds run and the joined frame's block ends the task. A root so
    /// ended leaves the run no answer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::unwound`], [`Self::cancel`] and [`unit()`].
    pub(super) fn forsake(
        &mut self,
        runtime: &mut Runtime,
        stack: Word,
        at: CommandId,
    ) -> Result<Word, Refusal>
    {
        runtime.set_frame_top(runtime.frame_base());
        self.unwound(runtime, stack)?;
        let task = self.scheduler.running;
        let held = self.scheduler.held_by(task);
        self.cancel(runtime, held)?;
        if task == Task::ROOT {
            self.scheduler.cancelled = Some(at);
        }
        let top = runtime.frame_top().wrapping_sub(2);
        // SAFETY: a task's frames stand on the joined frame below the base,
        // and each unwind's frame stands above it.
        let code = unsafe { *top };
        // SAFETY: as above.
        let window = unsafe { *top.wrapping_add(1) };
        runtime.set_frame_top(top);
        runtime.jump(code, window.to_pointer());
        unit(runtime)
    }
}
