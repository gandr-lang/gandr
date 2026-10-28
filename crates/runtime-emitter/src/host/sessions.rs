//! A run's tasks take turns on its thread and its frame region: the scheduler
//! is the run's own, held in its host state, and switches tasks only at a
//! call. Every task's frames stand on the joined frame just below the base,
//! whose block ends the task. A fork makes a channel, one queue of messages
//! per end, each end a capability held in a cell; it queues the child's
//! closure with the child's end and answers the parent's end, and the parent
//! runs on. A send and a select queue their message at the peer's end, or hand
//! it to the task waiting there, which joins the back of the ready queue. A
//! receive and an offer take the oldest message at their end, or capture the
//! task's frames from the base and continue the next task ready: a child is
//! entered as its closure with its end in hand, a waiting task's frames are
//! replayed and its top frame popped with what it took. A task's end gives a
//! child's answer up, keeps the root's, and continues the next task ready;
//! once every task has ended the root's answer pops the halt frame. With no
//! task ready and one waiting, the run is stuck at the actions the tasks wait
//! at.
//!
//! An end abandoned before its protocol ended is cancelled, and a task that
//! meets a cancelled peer is abandoned ([`cancel`]).

mod cancel;

use alloc::collections::VecDeque;

use gandr_core_sequent::CommandId;
use gandr_core_term::FieldLabel;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Refusal;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Word;

use super::Calls;
use super::Recording;
use super::Refused;
use super::VALUE;
use super::allocate;
use super::allocate_cell;
use super::cell;
use super::give_up;
use super::kind;
use super::object_header;
use super::unit;
use crate::function::Label;
use crate::trace::Carried;
use crate::trace::ChannelNumber;
use crate::trace::Play;
use crate::trace::Played;
use crate::trace::TaskNumber;
use crate::transfer::Moved;
use crate::transfer::Tables;
use crate::transfer::owned;
use crate::transfer::transfer;

/// The fields of a session's end: its channel's number and its party.
const END_FIELDS: usize = 2;

/// A task of a run: the root, numbered zero, or a fork's child, numbered in
/// the order its fork ran.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Task(usize);

impl Task
{
    /// The task a run starts as.
    const ROOT: Self = Self(0);
}

/// A channel of a run, numbered in the order its fork ran: what its ends'
/// first field holds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ChannelIndex(usize);

/// One of a channel's two ends: the child's, or its parent's.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Party
{
    /// The end the fork's child holds.
    Child,
    /// The end the forking task holds.
    Parent,
}

impl Party
{
    /// The other end.
    ///
    /// # Specification
    /// trivial.
    const fn peer(self) -> Self
    {
        match self {
            Self::Child => Self::Parent,
            Self::Parent => Self::Child,
        }
    }

    /// The word an end's second field holds.
    ///
    /// # Specification
    /// trivial.
    fn word(self) -> Word
    {
        Word::from(match self {
            Self::Child => 0_usize,
            Self::Parent => 1_usize,
        })
    }

    /// The end an end's second field names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a word naming neither end.
    fn of(word: Word) -> Result<Self, Refusal>
    {
        match usize::from(word) {
            0 => Ok(Self::Child),
            1 => Ok(Self::Parent),
            _ => Err(Refusal::Operands),
        }
    }

    /// The dialogue's endpoint the end plays: the child's, at the fork's
    /// protocol, the left; the parent's, at its dual, the right.
    ///
    /// # Specification
    /// trivial.
    const fn side(self) -> Endpoint
    {
        match self {
            Self::Child => Endpoint::Left,
            Self::Parent => Endpoint::Right,
        }
    }
}

/// What a send or a select puts on a channel.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub(super) enum Message<'run>
{
    /// A send's payload.
    Payload(Word),
    /// A select's label.
    Label(&'run FieldLabel),
}

/// What a task waiting at an end takes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub(super) enum Waits<'run>
{
    /// A receive's payload, answered in a fresh cell.
    Payload,
    /// An offer's label, answered by its position among these.
    Label(&'run [FieldLabel]),
}

/// A task waiting at an end: its frames, captured from the base, the action
/// it waits at and what it takes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Parked<'run>
{
    /// The task.
    task: Task,
    /// Its frames.
    stack: Word,
    /// The receive or offer it waits at.
    at: CommandId,
    /// What it takes.
    waits: Waits<'run>,
}

/// A task ready to run.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Ready
{
    /// A fork's child, entered as its closure with its end's cell in hand.
    Start
    {
        /// The child.
        task: Task,
        /// Its closure.
        closure: Word,
        /// Its end's cell.
        end: Word,
    },
    /// A task that waited: its frames replayed and its top frame popped with
    /// what it took.
    Resume
    {
        /// The task.
        task: Task,
        /// Its frames.
        stack: Word,
        /// What it took: a payload's cell, or a label's position.
        answer: Word,
    },
    /// A task that waited at an end its peer cancelled: its frames abandoned,
    /// their unwinds run, and the task ended.
    Abandon
    {
        /// The task.
        task: Task,
        /// Its frames.
        stack: Word,
        /// The receive or offer it waited at.
        at: CommandId,
    },
}

/// Who holds an end, and whether its protocol goes on.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing
{
    /// A task holds it, in its frames or its window.
    Held(Task),
    /// A message carries it, queued at an end.
    Sent,
    /// Closed: its protocol ended.
    Closed,
    /// Abandoned before its protocol ended: a cancellation its peer's next
    /// action observes.
    Cancelled,
}

/// One end of a channel: the messages sent to it and not yet taken, oldest
/// first, the receipt or offer a traced run records as each is taken, the
/// task waiting at it, and who holds it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct End<'run>
{
    /// The messages.
    queued: VecDeque<Message<'run>>,
    /// The moves taking them makes, kept only by a traced run.
    noted: VecDeque<RecordedMove<Carried>>,
    /// The task waiting, if any.
    waiting: Option<Parked<'run>>,
    /// Who holds it.
    standing: Standing,
}

impl End<'_>
{
    /// A fresh end the task `task` holds.
    ///
    /// # Specification
    /// trivial.
    const fn held(task: Task) -> Self
    {
        Self {
            queued: VecDeque::new(),
            noted: VecDeque::new(),
            waiting: None,
            standing: Standing::Held(task),
        }
    }
}

/// A channel: its two ends.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Channel<'run>
{
    /// The child's end.
    child: End<'run>,
    /// The parent's end.
    parent: End<'run>,
}

/// A run's tasks: its channels, the tasks ready, oldest first, the task
/// running, the root's answer once the root has ended, and the action a
/// cancellation abandoned the root at, once one has. Scheduling is
/// deterministic: a fork's parent runs on, and a child or a task a message
/// or a cancellation readies joins the back of the queue.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub(super) struct Scheduler<'run>
{
    /// The joined frame's code word; zero for a run that acts on no session.
    joined: Word,
    /// The channels, by number.
    channels: Vec<Channel<'run>>,
    /// The tasks ready.
    ready: VecDeque<Ready>,
    /// The task running.
    running: Task,
    /// The last task forked; the root before any fork.
    forked: Task,
    /// How many tasks wait at an end.
    parked: usize,
    /// The root's answer, once the root has ended.
    answer: Option<Word>,
    /// The action a cancellation abandoned the root's continuation at: the
    /// run then has no answer.
    cancelled: Option<CommandId>,
}

impl<'run> Scheduler<'run>
{
    /// The scheduler of a run whose joined frame resumes at `joined`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(joined: Word) -> Self
    {
        Self {
            joined,
            channels: Vec::new(),
            ready: VecDeque::new(),
            running: Task::ROOT,
            forked: Task::ROOT,
            parked: 0,
            answer: None,
            cancelled: None,
        }
    }

    /// The end `party` of the channel `channel`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a channel no fork made.
    fn end(
        &mut self,
        channel: ChannelIndex,
        party: Party,
    ) -> Result<&mut End<'run>, Refusal>
    {
        let held = self.channels.get_mut(channel.0).ok_or(Refusal::Operands)?;
        Ok(match party {
            Party::Child => &mut held.child,
            Party::Parent => &mut held.parent,
        })
    }

    /// The ends the task `task` holds.
    ///
    /// # Specification
    /// trivial.
    fn held_by(
        &self,
        task: Task,
    ) -> Vec<(ChannelIndex, Party)>
    {
        self.channels
            .iter()
            .enumerate()
            .flat_map(|(index, channel)| {
                [
                    (Party::Child, &channel.child),
                    (Party::Parent, &channel.parent),
                ]
                .into_iter()
                .filter(move |&(_, end)| end.standing == Standing::Held(task))
                .map(move |(party, _)| (ChannelIndex(index), party))
            })
            .collect()
    }

    /// The actions the waiting tasks wait at, in the order the tasks forked.
    ///
    /// # Specification
    /// trivial.
    fn waiting(&self) -> Vec<CommandId>
    {
        let mut parked: Vec<(Task, CommandId)> = self
            .channels
            .iter()
            .flat_map(|channel| [&channel.child, &channel.parent])
            .filter_map(|end| end.waiting.map(|parked| (parked.task, parked.at)))
            .collect();
        parked.sort_unstable_by_key(|&(task, _)| task);
        parked.into_iter().map(|(_, at)| at).collect()
    }
}

/// A fresh end `party` of the channel `channel`, in a fresh cell as a linear
/// binder holds it: a capability whose fields are the channel's number and
/// the party.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Heap`] past the heap's limit.
fn endpoint(
    runtime: &mut Runtime,
    channel: ChannelIndex,
    party: Party,
) -> Result<Word, Refusal>
{
    let fields = Arity::try_from(END_FIELDS).map_err(|_overflow| Refusal::Operands)?;
    let end = allocate(runtime, &[
        object_header(Kind::Capability, fields)?,
        Word::from(channel.0),
        party.word(),
    ])?;
    allocate_cell(runtime, &[end])
}

/// The channel and the party of the end the cell `held` holds.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a value that is no cell holding an end.
fn end_of(held: Word) -> Result<(ChannelIndex, Party), Refusal>
{
    // SAFETY: a cell holds its value first.
    let end = unsafe { *cell(held)?.wrapping_add(VALUE) };
    capability_end(end)
}

/// Push the cell `held` onto `ends` when it holds a session's end.
///
/// # Specification
/// trivial.
pub(super) fn gather_end(
    ends: &mut Vec<Word>,
    held: Word,
)
{
    if end_of(held).is_ok() {
        ends.push(held);
    }
}

/// The channel and the party of the end `end`: a capability whose fields
/// are its channel's number and its party, as a cell holds it and a send
/// carries it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a value that is no end.
fn capability_end(end: Word) -> Result<(ChannelIndex, Party), Refusal>
{
    if kind(end)? != Kind::Capability {
        return Err(Refusal::Operands);
    }
    let object = end.to_pointer::<Word>();
    // SAFETY: an object's first word is its header.
    if usize::from(Header::from_word(unsafe { *object }).arity()) != END_FIELDS {
        return Err(Refusal::Operands);
    }
    // SAFETY: an end holds its channel's number, then its party.
    let channel = ChannelIndex(usize::from(unsafe { *object.wrapping_add(1) }));
    // SAFETY: as above.
    let party = Party::of(unsafe { *object.wrapping_add(2) })?;
    Ok((channel, party))
}

/// What a task waiting for `waits` takes of `message`: a payload in a fresh
/// cell, or a label's position among the offer's labels.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a message other than the task waits for, or a
/// label the offer lacks; [`Refusal::Heap`] past the heap's limit.
fn delivered(
    runtime: &mut Runtime,
    message: Message<'_>,
    waits: Waits<'_>,
) -> Result<Word, Refusal>
{
    match (message, waits) {
        (Message::Payload(payload), Waits::Payload) => allocate_cell(runtime, &[payload]),
        (Message::Label(label), Waits::Label(labels)) => labels
            .iter()
            .position(|held| held == label)
            .map(Word::from)
            .ok_or(Refusal::Operands),
        (Message::Payload(_), Waits::Label(_)) | (Message::Label(_), Waits::Payload) => {
            Err(Refusal::Operands)
        },
    }
}

impl<'run> Calls<'run, '_>
{
    /// Fork at `at`: make a channel, a play of it in a traced run, queue the
    /// child's closure `closure` with the child's end, and answer the
    /// parent's end.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Heap`] past the heap's limit.
    pub(super) fn forked(
        &mut self,
        runtime: &mut Runtime,
        at: CommandId,
        closure: Word,
    ) -> Result<Word, Refusal>
    {
        let channel = ChannelIndex(self.scheduler.channels.len());
        let theirs = endpoint(runtime, channel, Party::Child)?;
        let ours = endpoint(runtime, channel, Party::Parent)?;
        if let Recording::Into(ref mut trace) = self.recording {
            trace.plays.push(Play {
                fork: at,
                moves: Vec::new(),
            });
        }
        let task = Task(self.scheduler.forked.0.saturating_add(1));
        self.scheduler.forked = task;
        self.scheduler.channels.push(Channel {
            child: End::held(task),
            parent: End::held(self.scheduler.running),
        });
        self.scheduler.ready.push_back(Ready::Start {
            task,
            closure,
            end: theirs,
        });
        Ok(ours)
    }

    /// Record, in a traced run, the move `movement` the task `task` made at
    /// the end `party` of the channel `channel`.
    ///
    /// # Specification
    /// trivial.
    fn note(
        &mut self,
        (channel, party): (ChannelIndex, Party),
        task: Task,
        movement: RecordedMove<Carried>,
    )
    {
        if let Recording::Into(ref mut trace) = self.recording
            && let Some(play) = trace
                .plays
                .get_mut(self.played_before.saturating_add(channel.0))
        {
            play.moves.push(Played {
                task: TaskNumber(task.0),
                side: party.side(),
                movement,
            });
        }
    }

    /// The moves `message` makes out of its sender's end and into its
    /// receiver's, as a traced run records them: a payload sent and received,
    /// or a label selected and offered.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::carried`].
    fn moves(
        &mut self,
        message: Message<'run>,
    ) -> Result<[RecordedMove<Carried>; 2], Refusal>
    {
        Ok(match message {
            Message::Payload(word) => {
                let carried = self.carried(word)?;
                [RecordedMove::Sent(carried), RecordedMove::Received(carried)]
            },
            Message::Label(label) => [
                RecordedMove::Selected(label.clone()),
                RecordedMove::Offered(label.clone()),
            ],
        })
    }

    /// What a traced run records the payload `word` as: the channel and the
    /// side an end names, or the value it moves into the caller's store,
    /// apart from what the run's other moves moved.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a payload that does not move into the store,
    /// recorded as [`Refused::Transfer`].
    fn carried(
        &mut self,
        word: Word,
    ) -> Result<Carried, Refusal>
    {
        if let Ok((channel, party)) = end_of(word) {
            return Ok(Carried::End {
                channel: ChannelNumber(channel.0),
                side: party.side(),
            });
        }
        let tables = Tables {
            heads: &self.heads,
            literals: &self.literals,
            codes: self.code_table,
        };
        let mut moved = Moved::new();
        // SAFETY: the payload is a value of this run, whose heap and
        // constants are live while its host call runs.
        let carried =
            unsafe { transfer(word, self.sites, tables, self.arena, self.store, &mut moved) };
        carried.map(Carried::Value).map_err(|refusal| {
            self.refused = Some(Refused::Transfer(refusal));
            Refusal::Operands
        })
    }

    /// Close the end the cell `held` holds, the close recorded by a traced
    /// run. Answers the unit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`end_of`] and [`unit()`].
    pub(super) fn closed(
        &mut self,
        runtime: &mut Runtime,
        held: Word,
    ) -> Result<Word, Refusal>
    {
        let end = end_of(held)?;
        let task = self.scheduler.running;
        self.note(end, task, RecordedMove::Closed);
        self.scheduler.end(end.0, end.1)?.standing = Standing::Closed;
        unit(runtime)
    }

    /// Put `message` on the end the cell `held` holds, for the action `at`:
    /// handed to the task waiting at the peer's end, which joins the back of
    /// the ready queue and holds an end the message carries, or queued there.
    /// Answers the unit. A cancelled peer takes no message: the payload is
    /// given up, an end it carries cancelled, and the running task's
    /// continuation abandoned as [`Self::abandoned`] does.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`end_of`], [`delivered`], [`Self::cancel`] and
    /// [`Self::abandoned`].
    pub(super) fn sent(
        &mut self,
        runtime: &mut Runtime,
        held: Word,
        at: CommandId,
        message: Message<'run>,
    ) -> Result<Word, Refusal>
    {
        let (channel, party) = end_of(held)?;
        let carried = match message {
            Message::Payload(payload) => capability_end(payload).ok(),
            Message::Label(_) => None,
        };
        if self.scheduler.end(channel, party.peer())?.standing == Standing::Cancelled {
            if let Message::Payload(payload) = message {
                let sites = self.sites;
                // SAFETY: the send owns its payload, a value of the run's
                // heap, which no task takes once its peer is cancelled.
                unsafe {
                    give_up(runtime, payload, |object| owned(object, sites));
                }
            }
            self.cancel(runtime, carried.into_iter().collect())?;
            return self.abandoned(runtime, at);
        }
        let received = match self.recording {
            Recording::Into(_) => {
                let [sent, received] = self.moves(message)?;
                let task = self.scheduler.running;
                self.note((channel, party), task, sent);
                Some(received)
            },
            Recording::Off => None,
        };
        let peer = self.scheduler.end(channel, party.peer())?;
        let holder = if let Some(parked) = peer.waiting.take() {
            let answer = delivered(runtime, message, parked.waits)?;
            self.scheduler.parked = self.scheduler.parked.saturating_sub(1);
            self.scheduler.ready.push_back(Ready::Resume {
                task: parked.task,
                stack: parked.stack,
                answer,
            });
            if let Some(received) = received {
                self.note((channel, party.peer()), parked.task, received);
            }
            Standing::Held(parked.task)
        }
        else {
            peer.queued.push_back(message);
            peer.noted.extend(received);
            Standing::Sent
        };
        if let Some((carried, side)) = carried {
            self.scheduler.end(carried, side)?.standing = holder;
        }
        unit(runtime)
    }

    /// Take what `waits` names at the end the cell `held` holds, for the
    /// action `at`: the oldest message queued there, an end it carries then
    /// held by the running task; with none and the peer cancelled, abandon
    /// the running task's continuation as [`Self::abandoned`] does; or, with
    /// none, park the running task's frames at the end and continue the next
    /// task ready.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`end_of`], [`delivered`], [`Self::capture`], [`Self::switch`] and
    /// [`Self::abandoned`].
    pub(super) fn awaited(
        &mut self,
        runtime: &mut Runtime,
        held: Word,
        at: CommandId,
        waits: Waits<'run>,
    ) -> Result<Word, Refusal>
    {
        let (channel, party) = end_of(held)?;
        let end = self.scheduler.end(channel, party)?;
        if let Some(message) = end.queued.pop_front() {
            let noted = end.noted.pop_front();
            let task = self.scheduler.running;
            if let Some(received) = noted {
                self.note((channel, party), task, received);
            }
            if let Message::Payload(payload) = message
                && let Ok((carried, side)) = capability_end(payload)
            {
                self.scheduler.end(carried, side)?.standing = Standing::Held(task);
            }
            return delivered(runtime, message, waits);
        }
        if self.scheduler.end(channel, party.peer())?.standing == Standing::Cancelled {
            return self.abandoned(runtime, at);
        }
        let base = runtime.frame_base();
        let stack = self.capture(runtime, base)?;
        let task = self.scheduler.running;
        self.scheduler.end(channel, party)?.waiting = Some(Parked {
            task,
            stack,
            at,
            waits,
        });
        self.scheduler.parked = self.scheduler.parked.saturating_add(1);
        self.switch(runtime)
    }

    /// Continue at the arm of `arms` whose position is `position`, in the
    /// window in reach.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a position past the arms.
    pub(super) fn branched(
        &self,
        runtime: &mut Runtime,
        arms: &[Label],
        position: Word,
    ) -> Result<Word, Refusal>
    {
        let arm = arms.get(usize::from(position)).ok_or(Refusal::Operands)?;
        let window = runtime.environment();
        runtime.jump(self.codes.label(*arm), window);
        Ok(position)
    }

    /// End the running task, its answer `answer`, at the joined frame's
    /// block. The joined frame is written back below the base, where the
    /// block's own call overwrote it; the root's answer is kept, unless a
    /// cancellation abandoned the root, and a child's given up. Once every
    /// task has ended, the root's answer pops the halt frame; otherwise the
    /// next task ready continues.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::switch`].
    pub(super) fn finished(
        &mut self,
        runtime: &mut Runtime,
        answer: Word,
    ) -> Result<Word, Refusal>
    {
        let below = runtime.frame_base().wrapping_sub(2);
        // SAFETY: a run that acts on a session sets its base past the halt
        // frame and the joined frame above it.
        unsafe {
            *below = self.scheduler.joined;
        }
        // SAFETY: as above.
        unsafe {
            *below.wrapping_add(1) = Word::from_pointer(runtime.environment());
        }
        if self.scheduler.running == Task::ROOT && self.scheduler.cancelled.is_none() {
            self.scheduler.answer = Some(answer);
        }
        else {
            let sites = self.sites;
            // SAFETY: a task's end owns its answer, which nothing reads once
            // the task has ended or a cancellation has abandoned it.
            unsafe {
                give_up(runtime, answer, |object| owned(object, sites));
            }
        }
        match self.scheduler.answer {
            Some(root) if self.scheduler.ready.is_empty() && self.scheduler.parked == 0 => {
                runtime.set_frame_top(below);
                Ok(root)
            },
            Some(_) | None => self.switch(runtime),
        }
    }

    /// Continue the next task ready, its frames from the base: a child is
    /// entered as its closure with its end's cell in hand, a task that waited
    /// has its frames replayed and its top frame popped with what it took,
    /// and one whose peer was cancelled is ended as [`Self::forsake`] ends
    /// it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] with no task ready, recorded as
    /// [`Refused::Cancelled`] once a cancellation abandoned the root and as
    /// [`Refused::Deadlock`] otherwise; as [`Self::replay`] and
    /// [`Self::forsake`].
    fn switch(
        &mut self,
        runtime: &mut Runtime,
    ) -> Result<Word, Refusal>
    {
        let base = runtime.frame_base();
        runtime.set_frame_top(base);
        match self.scheduler.ready.pop_front() {
            Some(Ready::Start { task, closure, end }) => {
                self.scheduler.running = task;
                let entry = closure.to_pointer::<Word>();
                // SAFETY: a closure's word after its header is its entry's
                // code word.
                let code = unsafe { *entry.wrapping_add(1) };
                runtime.jump(code, entry);
                Ok(end)
            },
            Some(Ready::Resume {
                task,
                stack,
                answer,
            }) => {
                self.scheduler.running = task;
                let _replayed = self.replay(runtime, stack)?;
                let top = runtime.frame_top().wrapping_sub(2);
                // SAFETY: the task's frames end in the frame its receive or
                // offer pushed.
                let code = unsafe { *top };
                // SAFETY: as above.
                let window = unsafe { *top.wrapping_add(1) };
                runtime.set_frame_top(top);
                runtime.jump(code, window.to_pointer());
                Ok(answer)
            },
            Some(Ready::Abandon { task, stack, at }) => {
                self.scheduler.running = task;
                self.forsake(runtime, stack, at)
            },
            None => {
                self.refused = Some(match self.scheduler.cancelled {
                    Some(at) => Refused::Cancelled(at),
                    None => Refused::Deadlock(self.scheduler.waiting()),
                });
                Err(Refusal::Operands)
            },
        }
    }
}
