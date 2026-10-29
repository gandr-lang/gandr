//! The host a run's call stencils enter: the primitives, evaluated by the
//! prelude's own evaluator over operands read from the heap, and the control
//! operations, which read and rewrite the frame region.
//!
//! A call names its callee by its number in the function's callee table and
//! passes up to two operands. An integer operand is a machine-word integer
//! or a literal the run's literal table holds; a boolean is an injection of
//! the empty tuple, the left one true. The answer is allocated where the call
//! stencil's heap pointer stood, as a constructor stencil would allocate it:
//! an integer past 64 bits joins the literal table and is answered by its
//! entry. Operands the callee does not take, or an evaluation the prelude
//! refuses (a division by zero), stop the run stuck, and the host records
//! the refusal the run names: `Stuck::Primitive` or `Stuck::NonScalar`.
//!
//! # Control
//!
//! The host finds frames by their code words. A handler's frame resumes at
//! its return clause's label and a reset's at the shared reset stub; every
//! other frame resumes either at a shared stub, its second word a value, or
//! at a label of the function, its second word the window the label's block
//! reads, whose slot count the lowering recorded.
//!
//! - An operation scans down from the top for its handler — the nearest
//!   delimiter decides, or the handler whose window holds the capability —
//!   captures the frames from that handler's up, writes the payload into the
//!   handler's window and continues at the clause with the stack in hand. A
//!   shift captures from the nearest reset's frame up.
//! - A capture copies each window its frames resume in into the stack, once
//!   however many frames share it, so neither the live run nor a replay sees
//!   the other's writes. A replay pushes the frames back above the top and
//!   copies each window afresh, moving each mark into the captured frames by
//!   the distance the frames moved; a mark at or below the captured frames'
//!   base names a frame of the tail and stays.
//! - Counted, a frame owns what its block will consume: the values in the slots
//!   the window table names for its label, one owner per entry, or a stub
//!   frame's word that is a value. A capture takes its frames off the region,
//!   so their owners pass to the stack unchanged. A replay gives each copy an
//!   owner of its own and gives up the stack, or, holding the stack's last
//!   owner, moves the owners into the copies and frees the stack; an
//!   abandonment gives the stack up, and the stack's release drops what its
//!   frames own. A capability a perform is handed is given up once its handler
//!   is found. A payload the host is offered stays: the run's moved values map
//!   back to it, so a reply naming it lays out as the same object.
//! - A held binding and a view are cells, so a write-back reaches every window
//!   that copied the binding. A view holds the value lent, how it ended and the
//!   held cell; its access's frame, popped, writes a resumed value back and
//!   passes the answer on, or saves the answer in an answer frame and continues
//!   at the unwind.
//!
//! An operation no handler of the run answers and the host declines, a shift
//! with no reset, a resume of a value that is no stack, and a view ended
//! twice or never stop the run stuck, each named by the command it stopped
//! at.
//!
//! # Sessions
//!
//! [`sessions`] holds the run's tasks, their channels and the scheduler that
//! switches between them, and the handlers of the session actions.

mod sessions;

use alloc::borrow::Cow;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::btree_map::Entry;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_core_session::DialogueWeb;
use gandr_core_session::Facing;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::primitive::PrimitiveError;
use gandr_core_term::primitive::Scalar;
use gandr_core_term::world::Unmigrated;
use gandr_core_term::world::World;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::COUNT_IMMORTAL;
use gandr_runtime_stencils::COUNT_ONE;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::RELEASE;
use gandr_runtime_stencils::Refusal;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Tag;
use gandr_runtime_stencils::Word;
use gandr_runtime_stencils::Words;
use gandr_runtime_stencils::count_word;

use self::sessions::Message;
use self::sessions::Scheduler;
use self::sessions::Waits;
use self::sessions::gather_end;
use crate::executor::Program;
use crate::function::Function;
use crate::function::Label;
use crate::function::Slots;
use crate::function::Stub;
use crate::lower::Callee;
use crate::lower::Clause;
use crate::lower::Handler;
use crate::lower::Lowered;
use crate::lower::Path;
use crate::lower::Reach;
use crate::lower::Reified;
use crate::lower::Slot;
use crate::lower::Window;
use crate::lower::integer_word;
use crate::lower::lower_suspended;
use crate::run::RunInputs;
use crate::run::Tier;
use crate::seam::HostRequest;
use crate::seam::HostValues;
use crate::seam::Migrated;
use crate::seam::MigrationRequest;
use crate::seam::Offer;
use crate::seam::Offered;
use crate::trace::Trace;
use crate::transfer::Moved;
use crate::transfer::Owners;
use crate::transfer::Sites;
use crate::transfer::Tables;
use crate::transfer::TransferRefusal;
use crate::transfer::owned;
use crate::transfer::transfer;
use crate::world::migrate;

/// A view's state: no eliminator has run.
const OPEN: usize = 0;
/// A view's state: resumed, its value to be written back.
const RESUMED: usize = 1;
/// A view's state: aborted.
const ABORTED: usize = 2;

/// The word of a cell holding its value: a held binding's and a view's.
const VALUE: usize = 1;
/// The word of a view holding its state.
const STATE: usize = 2;
/// The word of a view holding the value a resume writes back.
const WRITTEN: usize = 3;
/// The word of a view holding the held cell it writes back to.
const HELD: usize = 4;
/// The word of a view at a place holding its index.
const INDEX: usize = 5;
/// The fields of a view at a place: its value, state, written value, held
/// cell and index.
const PLACED: usize = 5;

/// A stack's words before its frames: the header, the captured frames' base
/// and top.
pub const STACK_PREFIX: usize = 3;

/// Where a run's code words are: what the host compares frames' codes with
/// and continues at.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub enum Codes<'run>
{
    /// Emitted code: each label's address by label, and each of
    /// [`Stub::ALL`]'s shared copy. Only a host with a patcher emits code,
    /// so the variant stands with it (#684).
    #[cfg(gandr_patcher)]
    Native
    {
        /// Each label's address.
        labels: &'run [Word],
        /// Each stub's address.
        stubs: &'run [Word; Stub::ALL.len()],
    },
    /// An executor program and the function it was built from.
    Executor(&'run Program, &'run Function),
}

impl Codes<'_>
{
    /// The code word of `label`; zero for a label never bound.
    ///
    /// # Specification
    /// trivial.
    pub fn label(
        self,
        label: Label,
    ) -> Word
    {
        match self {
            #[cfg(gandr_patcher)]
            Self::Native { labels, .. } => labels
                .get(usize::from(label))
                .copied()
                .unwrap_or(Word::ZERO),
            Self::Executor(program, function) => {
                program.code(function, label).unwrap_or(Word::ZERO)
            },
        }
    }

    /// The code word of `stub`'s shared copy.
    ///
    /// # Specification
    /// trivial.
    pub fn stub(
        self,
        stub: Stub,
    ) -> Word
    {
        match self {
            #[cfg(gandr_patcher)]
            Self::Native { stubs, .. } => stub.of(stubs),
            Self::Executor(program, _) => program.stub(stub),
        }
    }

    /// The tier the code is for.
    ///
    /// # Specification
    /// trivial.
    pub const fn tier(self) -> Tier
    {
        match self {
            #[cfg(gandr_patcher)]
            Self::Native { .. } => Tier::Native,
            Self::Executor(..) => Tier::Executor,
        }
    }
}

/// One run's host state: the function's callees, handlers and frame
/// windows, where its code is, the heads and literals the run holds — the
/// function's own, then those its calls made — and what the run moves into
/// the caller's store: the host's payloads, the answer and the values a stuck
/// run names.
///
/// # Specification
/// trivial.
pub struct Calls<'run, 'host>
{
    /// The callees, by the number a call stencil passes.
    callees: &'run [Callee],
    /// The handlers the function installs.
    handlers: &'run [Handler],
    /// Each frame label with its window's slot count.
    windows: &'run [Window],
    /// Each access's frame code with its unwind's code.
    unwinds: BTreeMap<Word, Word>,
    /// The marker's code, when a clause of the function leaves its frames
    /// standing.
    marker: Option<Word>,
    /// The heads a head object names, by family: the function's own, then the
    /// webs its decompositions made.
    heads: Vec<ConstructorTag>,
    /// The codes a code object names, by family.
    code_table: &'run [gandr_core_term::ValueId],
    /// Where the run's code is.
    codes: Codes<'run>,
    /// The closure sites, by their code words.
    sites: &'run Sites<'run>,
    /// The commands the function was lowered from.
    arena: &'run CommandArena,
    /// The constants' definitions, which a migration's body is lowered over.
    definitions: &'run Definitions,
    /// Each migration's body this run has lowered, by its command.
    migrations: BTreeMap<CommandId, Lowered>,
    /// The caller's store.
    store: &'run mut Store,
    /// The objects already moved into the store.
    moved: Moved,
    /// The host unclaimed operations are offered to, if any.
    offer: Option<&'run mut (dyn Offer + 'host)>,
    /// The literals, by the family a literal object names.
    literals: Vec<Literal>,
    /// Why the host last refused a call, when it named a reason.
    refused: Option<Refused>,
    /// The run's tasks and channels.
    scheduler: Scheduler<'run>,
    /// Where the run records its channels' plays, when its caller asks.
    recording: Recording<'run>,
    /// How many plays the trace held before this run: its first channel's
    /// play is the next.
    played_before: usize,
}

impl core::fmt::Debug for Calls<'_, '_>
{
    /// The run's tables and refusal; the store and the host stay opaque.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Calls")
            .field("callees", &self.callees)
            .field("literals", &self.literals)
            .field("refused", &self.refused)
            .finish_non_exhaustive()
    }
}

/// Why the host refused a call: what the run is stuck at, its values still
/// words of the run's heap.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Refused
{
    /// No handler of the run answers the operation this command performs.
    PerformNoHandler(CommandId),
    /// No reset is reachable from this shift.
    ShiftNoReset(CommandId),
    /// This resumption was given a value that is no stack.
    ResumedNonStack
    {
        /// The resumption.
        at: CommandId,
        /// The value.
        value: Word,
    },
    /// The prelude refused a primitive's operands.
    Primitive(PrimitiveError),
    /// A primitive's operand is neither an integer, a boolean nor a string.
    NonScalar(Word),
    /// This access's body answered with its view never ended.
    Unended(CommandId),
    /// This access's index named no element of its held list.
    Outside(CommandId),
    /// A constant the definitions do not hold was read.
    UndefinedConstant(ConstantIndex),
    /// A constant's unfolding read its own value.
    CyclicConstant(ConstantIndex),
    /// The host stopped the run.
    Aborted,
    /// A call refused operands no stuck answer names: a memory form on a
    /// value that is no cell, a reified stack past a region.
    Operands,
    /// The host resumed with a value its store does not hold, or one a run
    /// cannot hold: code the host built rather than a value the run moved
    /// out.
    Reply(HeapValueId),
    /// A payload could not be moved into the store.
    Transfer(TransferRefusal),
    /// This migration answered nothing, for the reason named.
    Migration(CommandId, Unmigrated),
    /// Every task waits at a receive or an offer and none is ready: the
    /// actions they wait at, in the order the tasks forked.
    Deadlock(Vec<CommandId>),
    /// The root's action here met an end its peer cancelled, abandoning the
    /// root's continuation: the run has no answer.
    Cancelled(CommandId),
}

/// The parts a run's host state holds: the function lowered from `arena`
/// over `definitions`, its code, its closure sites, and the run's inputs.
///
/// # Specification
/// trivial.
pub struct Parts<'run, 'host>
{
    /// The function.
    pub lowered: &'run Lowered,
    /// Where its code is.
    pub codes: Codes<'run>,
    /// Its closure sites, by their code words.
    pub sites: &'run Sites<'run>,
    /// The commands it was lowered from.
    pub arena: &'run CommandArena,
    /// The constants' definitions it was lowered over.
    pub definitions: &'run Definitions,
    /// The run's store, captures, host and recording.
    pub inputs: RunInputs<'run, 'host>,
}

/// Whether a run records its channels' plays, and into which trace.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub enum Recording<'run>
{
    /// The run records nothing.
    Off,
    /// The run appends a play per channel to the trace.
    Into(&'run mut Trace),
}

impl Recording<'_>
{
    /// The same recording, for one run of several a caller makes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn again(&mut self) -> Recording<'_>
    {
        match *self {
            Self::Off => Recording::Off,
            Self::Into(ref mut trace) => Recording::Into(trace),
        }
    }
}

impl<'run, 'host> Calls<'run, 'host>
{
    /// The state of a run of `parts`' function.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(parts: Parts<'run, 'host>) -> Self
    {
        let Parts {
            lowered,
            codes,
            sites,
            arena,
            definitions,
            inputs,
        } = parts;
        let (store, offer, recording) = inputs.into_held();
        let played_before = match recording {
            Recording::Off => 0,
            Recording::Into(ref trace) => trace.plays.len(),
        };
        Self {
            callees: &lowered.callees,
            handlers: &lowered.handlers,
            windows: &lowered.windows,
            unwinds: lowered
                .unwinds
                .iter()
                .map(|&(ended, unwind)| (codes.label(ended), codes.label(unwind)))
                .collect(),
            heads: lowered.heads.clone(),
            code_table: &lowered.codes,
            codes,
            sites,
            arena,
            definitions,
            migrations: BTreeMap::new(),
            store,
            moved: Moved::new(),
            offer,
            literals: lowered.literals.clone(),
            refused: None,
            scheduler: Scheduler::new(
                lowered
                    .joined
                    .map_or(Word::ZERO, |label| codes.label(label)),
            ),
            recording,
            played_before,
            marker: lowered.marker.map(|label| codes.label(label)),
        }
    }

    /// Move the run's value `value` into the caller's store, sharing what
    /// earlier moves of the run moved.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`transfer`].
    ///
    /// # Safety
    /// - unsafe invariants: `value` is a value of this run, whose heap and
    ///   constants are still live.
    #[inline]
    pub unsafe fn moved(
        &mut self,
        value: Word,
    ) -> Result<HeapValueId, TransferRefusal>
    {
        let tables = Tables {
            heads: &self.heads,
            literals: &self.literals,
            codes: self.code_table,
        };
        // SAFETY: the caller's invariant; `moved` holds only this run's
        // objects, moved into this store.
        unsafe {
            transfer(
                value,
                self.sites,
                tables,
                self.arena,
                self.store,
                &mut self.moved,
            )
        }
    }

    /// Lay the caller's store's values `values` out on the run's heap, in
    /// order, as a host's reply is laid out: the captures a command closed
    /// over the store runs over.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Laying::laid`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — commands over captures run from the store and answer
    ///   what forcing each in place answers, and a record a migration answers
    ///   comes back; a word missing or zero leaves a capture slot or the answer
    ///   addressing nothing.
    /// - witness: `tests::closed::a_thunk_runs_from_the_store_as_it_runs_in_place`
    /// - witness: `tests::world::a_record_built_only_at_the_world_comes_back`
    #[inline]
    pub fn laid_out(
        &mut self,
        runtime: &mut Runtime,
        values: &[HeapValueId],
    ) -> Result<Vec<Word>, Unlaid>
    {
        Laying {
            store: self.store,
            heads: &mut self.heads,
            code_table: self.code_table,
            literals: &mut self.literals,
            moved: &self.moved,
            sites: self.sites,
            arena: self.arena,
        }
        .laid(runtime, values)
    }

    /// Why the host refused the call a stuck run stopped at, when it named a
    /// reason.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refused(&self) -> Option<&Refused>
    {
        self.refused.as_ref()
    }

    /// The integer, boolean, string, floating-point number or width value the
    /// operand `word` addresses.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for an object that is neither.
    fn scalar(
        &self,
        word: Word,
    ) -> Result<Scalar, Refusal>
    {
        let object = word.to_pointer::<Word>();
        // SAFETY: an operand is a positive value, which addresses an object.
        let header = Header::from_word(unsafe { *object });
        match header.kind() {
            Ok(Kind::Integer) => {
                // SAFETY: an integer object holds its bits in its second word.
                let bits = unsafe { *object.wrapping_add(1) };
                Ok(Scalar::Integer(integer_literal(bits)))
            },
            Ok(Kind::Literal) => match usize::try_from(header.family())
                .ok()
                .and_then(|entry| self.literals.get(entry))
            {
                Some(&Literal::Integer(ref integer)) => Ok(Scalar::Integer(integer.clone())),
                Some(&Literal::Text(ref text)) => Ok(Scalar::Text(text.clone())),
                Some(&Literal::Float64(float)) => Ok(Scalar::Float64(float)),
                Some(&Literal::Fixed(fixed)) => Ok(Scalar::Fixed(fixed)),
                Some(&(Literal::Numeric(_) | Literal::Character(_))) | None => {
                    Err(Refusal::Operands)
                },
            },
            Ok(Kind::Injection) if usize::from(header.arity()) == 1 => {
                // SAFETY: an injection holds its one field after its header.
                let field = unsafe { *object.wrapping_add(1) }.to_pointer::<Word>();
                // SAFETY: a field is a positive value, which addresses an
                // object.
                let inner = Header::from_word(unsafe { *field });
                let side = Side::try_from(Summand::from(usize::from(header.tag())))
                    .map_err(|_summand| Refusal::Operands)?;
                if inner.kind() == Ok(Kind::Tuple) && usize::from(inner.arity()) == 0 {
                    Ok(Scalar::Boolean(side))
                }
                else {
                    Err(Refusal::Operands)
                }
            },
            Ok(_) | Err(_) => Err(Refusal::Operands),
        }
    }

    /// Answer the call of callee `entry` on `first` and `second`, as many of
    /// them as the callee takes, recording why a refused one refused.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for an operand the callee does not take, an
    /// evaluation the prelude refuses, a control operation the run cannot
    /// answer, a migration that answers nothing, a session action no task is
    /// ready to follow or a payload a traced run sends that does not move into
    /// the store; [`Refusal::Heap`] or [`Refusal::Frames`] past a region's
    /// limit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs halt alike on both tiers with the
    ///   answers they state: a primitive, a control call and a memory call each
    ///   answered wrong, or not at all, changes an answer.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn call(
        &mut self,
        runtime: &mut Runtime,
        entry: Word,
        first: Word,
        second: Word,
    ) -> Result<Word, Refusal>
    {
        let callees = self.callees;
        let callee = callees.get(usize::from(entry)).ok_or(Refusal::Operands)?;
        let answered = match *callee {
            Callee::Primitive(primitive) => self.primitive(runtime, primitive, first, second),
            Callee::Perform {
                ref signature,
                ref operation,
                reach,
                at,
            } => {
                let (capability, payload) = match reach {
                    Reach::Nearest => (None, first),
                    Reach::Capability => (Some(first), second),
                };
                let performed =
                    self.perform(runtime, (signature, operation, at), capability, payload);
                if let Some(capability) = capability {
                    let sites = self.sites;
                    // SAFETY: a perform owns the capability it was
                    // handed, read no more once its handler is found.
                    unsafe {
                        give_up(runtime, capability, |object| owned(object, sites));
                    }
                }
                performed
            },
            Callee::Shift(_) => self.shift(runtime),
            Callee::Replay(_) => self.replay(runtime, first),
            Callee::Abandon(_) => self.abandon(runtime, first),
            Callee::Rejoin(_) => self.rejoin(runtime, first),
            Callee::Escape => self.escape(runtime, first),
            Callee::Hold => allocate_cell(runtime, &[first]),
            Callee::Access => {
                let held = cell(first)?;
                // SAFETY: a cell holds its value first.
                let lent = unsafe { *held.wrapping_add(VALUE) };
                allocate_cell(runtime, &[lent, Word::from(OPEN), Word::ZERO, first])
            },
            Callee::AccessAt(at) => {
                let lent = self.element(at, first, second)?;
                allocate_cell(runtime, &[
                    lent,
                    Word::from(OPEN),
                    Word::ZERO,
                    first,
                    second,
                ])
            },
            Callee::Element(at) => {
                let read = self.element(at, first, second)?;
                allocate_cell(runtime, &[read])
            },
            Callee::Resumed => {
                settle(first, Word::from(RESUMED), second)?;
                unit(runtime)
            },
            Callee::Aborted => {
                settle(first, Word::from(ABORTED), Word::ZERO)?;
                unit(runtime)
            },
            Callee::Ended { unwind, .. } => self.ended(runtime, unwind, first, second),
            Callee::Reify(ref shape) => self.reify(runtime, shape),
            Callee::Decompose => self.decompose(runtime, first),
            Callee::Migrate { at, world, body } => self.migrated(runtime, (at, world, body), first),
            Callee::Fork(at) => self.forked(runtime, at, first),
            Callee::Send(at) => self.sent(runtime, first, at, Message::Payload(second)),
            Callee::Select { at, ref label } => {
                self.sent(runtime, first, at, Message::Label(label))
            },
            Callee::Receive(at) => self.awaited(runtime, first, at, Waits::Payload),
            Callee::Offer { at, ref labels } => {
                self.awaited(runtime, first, at, Waits::Label(labels))
            },
            Callee::Branch(ref arms) => self.branched(runtime, arms, first),
            Callee::Close(_) => self.closed(runtime, first),
            Callee::Joined => self.finished(runtime, first),
            Callee::Undefined(_) | Callee::Cyclic(_) => Err(Refusal::Operands),
        };
        if matches!(answered, Err(Refusal::Operands)) && self.refused.is_none() {
            self.refused = match *callee {
                Callee::Perform { at, .. } => Some(Refused::PerformNoHandler(at)),
                Callee::Shift(at) => Some(Refused::ShiftNoReset(at)),
                Callee::Replay(at) => Some(Refused::ResumedNonStack { at, value: first }),
                Callee::Ended { at, .. } => Some(Refused::Unended(at)),
                Callee::Undefined(constant) => Some(Refused::UndefinedConstant(constant)),
                Callee::Cyclic(constant) => Some(Refused::CyclicConstant(constant)),
                Callee::Migrate { at, .. } => Some(Refused::Migration(at, Unmigrated::Unanswered)),
                Callee::Primitive(_)
                | Callee::Abandon(_)
                | Callee::Rejoin(_)
                | Callee::Escape
                | Callee::Hold
                | Callee::Access
                | Callee::AccessAt(_)
                | Callee::Element(_)
                | Callee::Resumed
                | Callee::Aborted
                | Callee::Reify(_)
                | Callee::Decompose
                | Callee::Fork(_)
                | Callee::Send(_)
                | Callee::Receive(_)
                | Callee::Select { .. }
                | Callee::Offer { .. }
                | Callee::Branch(_)
                | Callee::Close(_)
                | Callee::Joined => Some(Refused::Operands),
            };
        }
        answered
    }

    /// The element of the list the held cell `held` holds at the index
    /// `index`, which the access `at` lends.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for an index naming no element, recorded as
    /// [`Refused::Outside`] at `at`, and for a held value that is no native
    /// list or an index that is no integer.
    fn element(
        &mut self,
        at: CommandId,
        held: Word,
        index: Word,
    ) -> Result<Word, Refusal>
    {
        let list = cell(held)?;
        // SAFETY: a cell holds its value first.
        let Walked::Reached(reached) = walk(unsafe { *list.wrapping_add(VALUE) }, index)?
        else {
            self.refused = Some(Refused::Outside(at));
            return Err(Refusal::Operands);
        };
        // SAFETY: a list cell holds its head after its header.
        Ok(unsafe { *reached.wrapping_add(1) })
    }

    /// Evaluate `callee` on `first` and, for a binary primitive, `second`,
    /// allocating the answer on `runtime`'s heap.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::call`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named primitive calls answer the sum, the product
    ///   past 64 bits and the comparison they state on both tiers, and a string
    ///   appended answers its text there and a string added to an integer is
    ///   refused by the prelude.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn primitive(
        &mut self,
        runtime: &mut Runtime,
        callee: Primitive,
        first: Word,
        second: Word,
    ) -> Result<Word, Refusal>
    {
        let mut operands = Vec::with_capacity(2);
        let arguments: &[Word] = if callee.arguments().len() == 2 {
            &[first, second]
        }
        else {
            &[first]
        };
        for &argument in arguments {
            match self.scalar(argument) {
                Ok(scalar) => operands.push(scalar),
                Err(refusal) => {
                    self.refused = Some(Refused::NonScalar(argument));
                    return Err(refusal);
                },
            }
        }
        let borrowed: Vec<Scalar<&IntegerLiteral, &StringLiteral>> =
            operands.iter().map(Scalar::borrowed).collect();
        let answer = match callee.evaluate(&borrowed) {
            Ok(answer) => answer,
            Err(error) => {
                self.refused = Some(Refused::Primitive(error));
                return Err(Refusal::Operands);
            },
        };
        let width = |_overflow| Refusal::Operands;
        let made = match answer {
            Scalar::Integer(integer) => match integer_word(&integer) {
                Some(bits) => {
                    let header = Header::new(
                        Kind::Integer,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(1_usize).map_err(width)?,
                        Family::UNNAMED,
                    );
                    allocate(runtime, &[header.word(), bits])
                },
                None => self.literal(runtime, Literal::Integer(integer)),
            },
            Scalar::Text(text) => self.literal(runtime, Literal::Text(text)),
            Scalar::Float64(float) => self.literal(runtime, Literal::Float64(float)),
            Scalar::Fixed(fixed) => self.literal(runtime, Literal::Fixed(fixed)),
            Scalar::Boolean(side) => {
                let unit = Header::new(
                    Kind::Tuple,
                    Tag::try_from(0_usize).map_err(width)?,
                    Arity::try_from(0_usize).map_err(width)?,
                    Family::UNNAMED,
                );
                let injection = Header::new(
                    Kind::Injection,
                    Tag::try_from(usize::from(Summand::from(side))).map_err(width)?,
                    Arity::try_from(1_usize).map_err(width)?,
                    Family::UNNAMED,
                );
                let held = allocate(runtime, &[unit.word()])?;
                allocate(runtime, &[injection.word(), held])
            },
        }?;
        let sites = self.sites;
        for &argument in arguments {
            // SAFETY: a counted call owns its operands, values of the
            // run's heap or immortal constants, and reads them no more.
            unsafe {
                give_up(runtime, argument, |object| owned(object, sites));
            }
        }
        Ok(made)
    }

    /// Decompose the dialogue the operand `dialogue` addresses: allocate its
    /// web on `runtime`'s heap as a head object naming the web's entry in the
    /// run's head table, which the web joins when no entry holds it yet.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for an operand that is no dialogue, a web whose
    /// edges close a cycle or a table past a header's family width, or as the
    /// allocation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a dialogue decomposes on both tiers to the web its
    ///   moves' facings give, and two interleavings of one dialogue to one web.
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn decompose(
        &mut self,
        runtime: &mut Runtime,
        dialogue: Word,
    ) -> Result<Word, Refusal>
    {
        let object = dialogue.to_pointer::<Word>();
        // SAFETY: an operand is a positive value, which addresses an object.
        let header = Header::from_word(unsafe { *object });
        let row = usize::try_from(header.family())
            .ok()
            .filter(|_| header.kind() == Ok(Kind::Head));
        let Some(&ConstructorTag::Dialogue(ref turns)) = row.and_then(|row| self.heads.get(row))
        else {
            return Err(Refusal::Operands);
        };
        let pieces = DialogueWeb::of(
            turns
                .iter()
                .map(|turn| (turn.endpoint, Facing::of(&turn.movement))),
        )
        .decompose()
        .map_err(|_cyclic| Refusal::Operands)?;
        let family =
            joined(&mut self.heads, &ConstructorTag::Web(pieces)).ok_or(Refusal::Operands)?;
        let width = |_overflow| Refusal::Operands;
        let made = allocate(runtime, &[Header::new(
            Kind::Head,
            Tag::try_from(0_usize).map_err(width)?,
            Arity::try_from(0_usize).map_err(width)?,
            family,
        )
        .word()])?;
        let sites = self.sites;
        // SAFETY: a counted call owns its operand, a value of the run's heap or
        // an immortal constant, and reads it no more.
        unsafe {
            give_up(runtime, dialogue, |object| owned(object, sites));
        }
        Ok(made)
    }

    /// Allocate `literal` on `runtime`'s heap as an object naming its entry in
    /// the run's literal table, which it joins.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a table past a header's family width, or as
    /// the allocation refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::primitive`]: a product past 64 bits and an
    ///   appended string read back as the literals they were written as.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn literal(
        &mut self,
        runtime: &mut Runtime,
        literal: Literal,
    ) -> Result<Word, Refusal>
    {
        let width = |_overflow| Refusal::Operands;
        let header = Header::new(
            Kind::Literal,
            Tag::try_from(0_usize).map_err(width)?,
            Arity::try_from(0_usize).map_err(width)?,
            Family::try_from(self.literals.len()).map_err(width)?,
        );
        let answer = allocate(runtime, &[header.word()])?;
        self.literals.push(literal);
        Ok(answer)
    }

    /// The handler whose frame resumes at `code`, when one does.
    ///
    /// # Specification
    /// trivial.
    fn handler(
        &self,
        code: Word,
    ) -> Option<&'run Handler>
    {
        let codes = self.codes;
        self.handlers
            .iter()
            .find(|handler| codes.label(handler.label) == code)
    }

    /// The slot count of the window a frame resuming at `code` holds second,
    /// or none for a frame holding a value there.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a code the function never pushes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a captured stack resumed twice and a handler resuming
    ///   its stack twice answer as they state: a frame read as holding a value
    ///   where it holds a window, or as another frame's window, resumes over
    ///   the captured window or a short copy of it.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn window(
        &self,
        code: Word,
    ) -> Result<Option<Slots>, Refusal>
    {
        let codes = self.codes;
        // A stub's frame, and the marker's, holds a value or a mark there.
        if Stub::ALL.iter().any(|&stub| codes.stub(stub) == code) || self.marker == Some(code) {
            return Ok(None);
        }
        self.windows
            .iter()
            .find(|window| codes.label(window.label) == code)
            .map(|window| Some(window.slots))
            .ok_or(Refusal::Operands)
    }

    /// Perform `operation` of `signature` at the command `at` through
    /// `capability`, or by the nearest delimiter when there is none: capture
    /// from its handler's frame up, write `payload` into the handler's window
    /// and continue at the clause with the stack in hand; offer it to the
    /// host when no handler of the run claims it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] when neither a handler of the run nor the host
    /// answers: the nearest delimiter handles another interface or lacks the
    /// operation, or no handler introduced the capability, and the host
    /// declines, aborts or is absent.
    fn perform(
        &mut self,
        runtime: &mut Runtime,
        (signature, operation, at): (&EffectName, &OperationName, CommandId),
        capability: Option<Word>,
        payload: Word,
    ) -> Result<Word, Refusal>
    {
        let reset = self.codes.stub(Stub::Reset);
        let base = runtime.frame_base();
        let mut frame = runtime.frame_top();
        let mut selected: Option<(*mut Word, *mut Word, &Clause)> = None;
        while frame > base {
            frame = frame.wrapping_sub(2);
            // SAFETY: every two words from the base mark to the top are a
            // frame.
            let code = unsafe { *frame };
            if capability.is_none() && code == reset {
                break;
            }
            let Some(handler) = self.handler(code)
            else {
                continue;
            };
            // SAFETY: a handler's frame holds its window second.
            let window = unsafe { *frame.wrapping_add(1) }.to_pointer::<Word>();
            let installed = handler
                .capability
                .map(|slot| slot_in(window, slot))
                .transpose()?
                // SAFETY: the capability's slot lies inside the handler's
                // window.
                .map(|slot| unsafe { *slot });
            if capability.is_some() && installed != capability {
                continue;
            }
            if handler.signature == *signature {
                selected = handler
                    .clauses
                    .iter()
                    .find(|clause| clause.operation == *operation)
                    .map(|clause| (frame, window, clause));
            }
            break;
        }
        let Some((frame, window, clause)) = selected
        else {
            return self.offered(runtime, at, payload);
        };
        let answer = match clause.path {
            Path::Capture => {
                let stack = self.capture(runtime, frame)?;
                runtime.set_frame_top(frame);
                let at = slot_in(window, clause.payload)?;
                // SAFETY: the payload's slot lies inside the handler's window.
                unsafe {
                    *at = payload;
                }
                stack
            },
            // The frames left standing hold the window's slots below the
            // clause's, so the clause binds the payload in hand.
            Path::Resume | Path::Return => {
                self.stand(runtime, frame)?;
                payload
            },
        };
        runtime.jump(self.codes.label(clause.label), window);
        Ok(answer)
    }

    /// Offer the operation the command `at` performs with `payload` to the
    /// host, and answer its reply.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] when there is no host, it declines or aborts —
    /// recorded — or its reply cannot be laid out on the run's heap, or the
    /// payload moved into the store; [`Refusal::Heap`] past the heap's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — scripted hosts that resume, abort and decline an
    ///   operation no handler of the run claims, on each tier; an offer never
    ///   made, or a reply that addresses nothing, changes the answer or the
    ///   ending.
    /// - witness: `tests::seam::a_host_resumes_a_single_unhandled_perform`
    /// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
    fn offered(
        &mut self,
        runtime: &mut Runtime,
        at: CommandId,
        payload: Word,
    ) -> Result<Word, Refusal>
    {
        let arena = self.arena;
        let (
            Some(offer),
            Some(&CommandNode::Perform {
                ref signature,
                ref operation,
                ..
            }),
        ) = (self.offer.as_deref_mut(), arena.command(at))
        else {
            return Err(Refusal::Operands);
        };
        let tables = Tables {
            heads: &self.heads,
            literals: &self.literals,
            codes: self.code_table,
        };
        // SAFETY: the payload is a value of this run, whose heap and
        // constants are live while its host call runs.
        let moved = unsafe {
            transfer(
                payload,
                self.sites,
                tables,
                arena,
                self.store,
                &mut self.moved,
            )
        };
        let moved = match moved {
            Ok(moved) => moved,
            Err(refusal) => {
                self.refused = Some(Refused::Transfer(refusal));
                return Err(Refusal::Operands);
            },
        };
        let request = HostRequest {
            signature,
            operation,
            payload: moved,
        };
        let mut values = HostValues::new(arena, self.store);
        match offer.offer(request, &mut values) {
            Offered::Resume(reply) => {
                let mut laying = Laying {
                    store: self.store,
                    heads: &mut self.heads,
                    code_table: self.code_table,
                    literals: &mut self.literals,
                    moved: &self.moved,
                    sites: self.sites,
                    arena: self.arena,
                };
                match laying.laid(runtime, core::slice::from_ref(&reply)) {
                    Ok(words) => words.first().copied().ok_or(Refusal::Operands),
                    Err(Unlaid::Value(value)) => {
                        self.refused = Some(Refused::Reply(value));
                        Err(Refusal::Operands)
                    },
                    Err(Unlaid::Run(refusal)) => Err(refusal),
                }
            },
            Offered::Abort => {
                self.refused = Some(Refused::Aborted);
                Err(Refusal::Operands)
            },
            Offered::Decline => Err(Refusal::Operands),
        }
    }

    /// Run the migration `at` to `world`, whose body is `body`, closed over the
    /// captures the tuple `captures` holds, and lay its answer out on the
    /// run's heap: where the host's [`Offer::migrate`] decides, and here, on a
    /// thread and over a store of its own, by default — its body lowered at
    /// the run's first migration to it, run on this run's tier and the fuel
    /// it has left.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] when the tuple cannot be moved into the store —
    /// recorded — the host refuses the migration — its reason recorded — the
    /// body does not lower, the migration answers nothing, or its answer
    /// cannot be laid out; [`Refusal::Heap`] past the heap's limit.
    fn migrated(
        &mut self,
        runtime: &mut Runtime,
        (at, world, body): (CommandId, World, CommandId),
        captures: Word,
    ) -> Result<Word, Refusal>
    {
        // SAFETY: the tuple is a value of this run, whose heap and constants
        // are live while its host call runs.
        let moved = match unsafe { self.moved(captures) } {
            Ok(moved) => moved,
            Err(refusal) => {
                self.refused = Some(Refused::Transfer(refusal));
                return Err(Refusal::Operands);
            },
        };
        let Some(&HeapValue::Constructed { ref fields, .. }) = self.store.value(moved)
        else {
            return Err(Refusal::Operands);
        };
        let fields = fields.to_vec();
        let decided = match self.offer.as_deref_mut() {
            Some(offer) => {
                let mut values = HostValues::new(self.arena, self.store);
                let request = MigrationRequest {
                    world,
                    at,
                    captures: &fields,
                };
                offer.migrate(request, &mut values)
            },
            None => Migrated::Here,
        };
        let answer = match decided {
            Migrated::Here => {
                let lowered = match self.migrations.entry(body) {
                    Entry::Occupied(lowered) => lowered.into_mut(),
                    Entry::Vacant(vacant) => vacant.insert(
                        lower_suspended(self.arena, self.definitions, body)
                            .map_err(|_form| Refusal::Operands)?,
                    ),
                };
                migrate(
                    self.codes.tier(),
                    (self.arena, self.definitions, lowered),
                    runtime.fuel(),
                    (self.store, &fields),
                )
                .ok_or(Refusal::Operands)?
            },
            Migrated::Answered(answer) => answer,
            Migrated::Refused(why) => {
                self.refused = Some(Refused::Migration(at, why));
                return Err(Refusal::Operands);
            },
        };
        match self.laid_out(runtime, core::slice::from_ref(&answer)) {
            Ok(words) => words.first().copied().ok_or(Refusal::Operands),
            Err(Unlaid::Value(_)) => Err(Refusal::Operands),
            Err(Unlaid::Run(refusal)) => Err(refusal),
        }
    }

    /// Capture from the nearest reset's frame up; answers the stack.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] when no reset is reachable.
    fn shift(
        &self,
        runtime: &mut Runtime,
    ) -> Result<Word, Refusal>
    {
        let reset = self.codes.stub(Stub::Reset);
        let base = runtime.frame_base();
        let mut frame = runtime.frame_top();
        while frame > base {
            frame = frame.wrapping_sub(2);
            // SAFETY: every two words from the base mark to the top are a
            // frame.
            if unsafe { *frame } == reset {
                let stack = self.capture(runtime, frame)?;
                runtime.set_frame_top(frame);
                return Ok(stack);
            }
        }
        Err(Refusal::Operands)
    }

    /// Copy the frames from `from` to the top into a stack. The frames leave
    /// the region, so what they own passes to the stack with no count changed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a frame the function never pushes, or one
    /// that resumes a block midway, whose owners no node names; as [`stack`]
    /// otherwise.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a captured stack resumed twice, and an access
    ///   abandoned by a shift, answer as they state: a capture that took the
    ///   wrong frames resumes the wrong rest.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn capture(
        &self,
        runtime: &mut Runtime,
        from: *mut Word,
    ) -> Result<Word, Refusal>
    {
        let top = runtime.frame_top();
        let mut frames = Vec::new();
        let mut cursor = from;
        while cursor < top {
            // SAFETY: every two words from the base mark to the top are a
            // frame.
            let code = unsafe { *cursor };
            // SAFETY: as above.
            let word = unsafe { *cursor.wrapping_add(1) };
            frames.push(Frame {
                code,
                word,
                window: self.window(code)?,
            });
            if matches!(self.sites.owners(code), Some(Owners::Unplaced)) {
                return Err(Refusal::Operands);
            }
            cursor = cursor.wrapping_add(2);
        }
        stack(
            runtime,
            Word::from_pointer(from),
            Word::from_pointer(top),
            &frames,
        )
    }

    /// Build the reified stack `shape` describes, innermost first: each
    /// application frame takes the call's next argument, which lie popped at
    /// the frame region's top in order, each projection frame resumes at its
    /// side's stub, and each bind frame resumes at its label in a copy of the
    /// window in reach. No frame of the region is in it, so a replay moves no
    /// mark.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a bind label the function never pushes; as
    /// [`stack`] otherwise.
    fn reify(
        &self,
        runtime: &mut Runtime,
        shape: &[Reified],
    ) -> Result<Word, Refusal>
    {
        let window = Word::from_pointer(runtime.environment());
        let arguments = runtime.frame_top();
        let mut remaining = shape
            .iter()
            .filter(|&&frame| frame == Reified::Apply)
            .count();
        let mut frames = Vec::with_capacity(shape.len());
        for &frame in shape.iter().rev() {
            frames.push(match frame {
                Reified::Apply => {
                    remaining = remaining.saturating_sub(1);
                    Frame {
                        code: self.codes.stub(Stub::Apply),
                        // SAFETY: the call's arguments lie at the top, popped
                        // but intact while the host runs.
                        word: unsafe { *arguments.wrapping_add(remaining) },
                        window: None,
                    }
                },
                Reified::Project(component) => Frame {
                    code: self.codes.stub(Stub::Project),
                    word: Word::from(usize::from(component)),
                    window: None,
                },
                Reified::Bind(label) => {
                    let code = self.codes.label(label);
                    Frame {
                        code,
                        word: window,
                        window: self.window(code)?,
                    }
                },
            });
        }
        stack(runtime, Word::ZERO, Word::ZERO, &frames)
    }

    /// Push the frames of `stack` above the top, each window copied afresh
    /// and each mark into the captured frames moved with them; answers the
    /// stack. Counted, each frame's copy gains an owner of each value the
    /// frame owns and the stack is given up, unless it was the stack's last
    /// owner, whose frames' owners move into the copies.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a value that is no stack;
    /// [`Refusal::Frames`] or [`Refusal::Heap`] past a region's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a captured stack resumed twice and a handler resuming
    ///   its stack twice answer as they state: a replay that gave its copy no
    ///   owner of its own, or moved the owners of a stack another owner keeps,
    ///   frees a pair the second resumption returns. A stack resumed below the
    ///   frames it was captured from, whose inner frame answers to a frame the
    ///   stack holds, answers as it states: a mark into the captured frames
    ///   left where they were skips that frame.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn replay(
        &self,
        runtime: &mut Runtime,
        stack: Word,
    ) -> Result<Word, Refusal>
    {
        if kind(stack)? != Kind::Stack {
            return Err(Refusal::Operands);
        }
        let object = stack.to_pointer::<Word>();
        // SAFETY: a stack's first words are its header and its captured
        // frames' base and top.
        let header = Header::from_word(unsafe { *object });
        // SAFETY: as above.
        let low = usize::from(unsafe { *object.wrapping_add(1) });
        // SAFETY: as above.
        let high = usize::from(unsafe { *object.wrapping_add(2) });
        let count = usize::from(header.arity());
        let base = runtime.frame_top();
        let top = base.wrapping_add(count.saturating_mul(2));
        hold_frames(top, runtime.frame_limit())?;
        let captured = Captured { low, high, base };
        // A stack no other owner holds gives its frames' owners to the
        // copies; any other lends them, each copy gaining an owner of its own.
        // SAFETY: a stack is preceded by its count word.
        let unique = unsafe { *count_word(stack) } == COUNT_ONE;
        let mut copies: BTreeMap<Word, Word> = BTreeMap::new();
        let mut words = Vec::new();
        for index in 0 .. count {
            let at = object.wrapping_add(STACK_PREFIX.saturating_add(index.saturating_mul(2)));
            // SAFETY: the stack holds its frames after its prefix.
            let code = unsafe { *at };
            // SAFETY: as above.
            let word = unsafe { *at.wrapping_add(1) };
            let resumed = match self.window(code)? {
                None => word,
                Some(slots) => {
                    if let Some(&fresh) = copies.get(&word) {
                        fresh
                    }
                    else {
                        let stored = word.to_pointer::<Word>();
                        words.clear();
                        words.reserve(slots.0);
                        for slot in 0 .. slots.0 {
                            // SAFETY: the stored window holds its slots.
                            let held = unsafe { *stored.wrapping_add(slot) };
                            words.push(captured.moved(held));
                        }
                        let fresh = allocate_window(runtime, &words)?;
                        let _first = copies.insert(word, fresh);
                        fresh
                    }
                },
            };
            let frame = base.wrapping_add(index.saturating_mul(2));
            // SAFETY: the frames fit below the region's limit.
            unsafe {
                *frame = code;
            }
            // SAFETY: as above.
            unsafe {
                *frame.wrapping_add(1) = resumed;
            }
            if !unique {
                match self.sites.owners(code) {
                    Some(Owners::Window(slots)) => {
                        let window = resumed.to_pointer::<Word>();
                        for &slot in slots {
                            // SAFETY: the fresh window holds its frame's
                            // owned slots.
                            share(unsafe { *slot_in(window, slot)? });
                        }
                    },
                    Some(Owners::Word) => share(resumed),
                    Some(Owners::Unplaced) | None => {},
                }
            }
        }
        runtime.set_frame_top(top);
        if unique {
            // SAFETY: the stack's one owner is the replay's, and its frames'
            // owners moved into the copies.
            unsafe {
                runtime.reclaim(stack);
            }
        }
        else {
            let sites = self.sites;
            // SAFETY: a replay owns the stack it was handed, which
            // another owner keeps.
            unsafe {
                give_up(runtime, stack, |object| owned(object, sites));
            }
        }
        Ok(stack)
    }

    /// Leave the frames from `from`, a handler's frame, to the top standing,
    /// and push the marker above them, its second word the mark `from`: the
    /// clause about to run on top of them neither captures nor walks them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a function with no marker;
    /// [`Refusal::Frames`] past the frame region's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — clauses that resume from their root, answer without
    ///   resuming, or do either by a case, over frames that own pairs, answer
    ///   as they state on both tiers: a marker pushed below the top, or marking
    ///   another frame, resumes or gives up the wrong frames.
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn stand(
        &self,
        runtime: &mut Runtime,
        from: *mut Word,
    ) -> Result<(), Refusal>
    {
        let marker = self.marker.ok_or(Refusal::Operands)?;
        let top = runtime.frame_top();
        let next = top.wrapping_add(2);
        hold_frames(next, runtime.frame_limit())?;
        // SAFETY: the frame fits below the region's limit.
        unsafe {
            *top = marker;
        }
        // SAFETY: as above.
        unsafe {
            *top.wrapping_add(1) = Word::from_pointer(from);
        }
        runtime.set_frame_top(next);
        Ok(())
    }

    /// Resume the frames a clause's operation left standing: pop the marker
    /// above them, which a resumption from the clause's tail position finds
    /// on top; answers `stand_in`, the word the clause held for its stack.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] when the marker is not on top.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Self::stand`]: a resumption that pops another
    ///   frame delivers the clause's reply to the wrong rest.
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn rejoin(
        &self,
        runtime: &mut Runtime,
        stand_in: Word,
    ) -> Result<Word, Refusal>
    {
        let top = runtime.frame_top();
        let frame = top.wrapping_sub(2);
        // SAFETY: the base mark's sentinel frame lies below any frame above
        // the base.
        if top <= runtime.frame_base() || self.marker != Some(unsafe { *frame }) {
            return Err(Refusal::Operands);
        }
        runtime.set_frame_top(frame);
        Ok(stand_in)
    }

    /// Leave a clause whose operation left its frames standing, once the
    /// clause answers `answer` to the marker the run just popped: give up what
    /// each frame from the marker's mark to the top owns, as the release of a
    /// stack holding them would, and pop them with their handler's frame;
    /// answers `answer`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a mark outside the frames, or a frame whose
    /// owners are unplaced; as [`slot_in`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a clause answering without resuming, over frames that
    ///   own a pair, and one answering the pair its handler keeps, answer as
    ///   they state on both tiers: a frame given up twice, or one the clause
    ///   still reads given up first, frees a pair the answer holds.
    /// - witness: `tests::forms::each_form_ends_alike_on_both_executors_as_its_program_states`
    fn escape(
        &self,
        runtime: &mut Runtime,
        answer: Word,
    ) -> Result<Word, Refusal>
    {
        // The popped marker's second word is in the window register.
        let from = runtime.environment();
        let top = runtime.frame_top();
        if from < runtime.frame_base() || from > top {
            return Err(Refusal::Operands);
        }
        let sites = self.sites;
        let mut cursor = from;
        while cursor < top {
            // SAFETY: every two words from the mark to the top are a frame.
            let code = unsafe { *cursor };
            // SAFETY: as above.
            let word = unsafe { *cursor.wrapping_add(1) };
            let held: Vec<Word> = match sites.owners(code) {
                Some(Owners::Window(slots)) => slots
                    .iter()
                    // SAFETY: a window frame's word is its window, which
                    // holds its frame's owned slots.
                    .map(|&slot| slot_in(word.to_pointer::<Word>(), slot).map(|at| unsafe { *at }))
                    .collect::<Result<_, _>>()?,
                Some(Owners::Word) => Vec::from([word]),
                Some(Owners::Unplaced) => return Err(Refusal::Operands),
                None => Vec::new(),
            };
            for value in held {
                // SAFETY: the frame owned `value`, a value of the run's heap or
                // an immortal constant, and leaves the region unread.
                unsafe {
                    give_up(runtime, value, |object| owned(object, sites));
                }
            }
            cursor = cursor.wrapping_add(2);
        }
        runtime.set_frame_top(from);
        Ok(answer)
    }

    /// Abandon `stack` as [`Self::unwound`] does; answers the unit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::unwound`] and [`unit()`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an access abandoned by a shift, whose unwind reads a
    ///   pair the answer holds too, answers that pair: an abandonment that runs
    ///   no unwind, or gives its owners no owner of their own, frees it.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn abandon(
        &mut self,
        runtime: &mut Runtime,
        stack: Word,
    ) -> Result<Word, Refusal>
    {
        self.unwound(runtime, stack)?;
        unit(runtime)
    }

    /// Push above the top a frame for each access `stack` captured, in the
    /// stack's order so the innermost is on top, each entering that access's
    /// unwind in the window its frame held; cancel each session end the
    /// stack's other frames hold in their linear slots and no unwind consumes;
    /// and give the stack up. The stack's other frames are dropped unrun.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a value that is no stack;
    /// [`Refusal::Frames`] past the frame region's limit; as
    /// [`Self::cancel_cells`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a peer waiting on an end the abandoned stack holds is
    ///   abandoned and the run answers: an abandonment that cancels no end
    ///   leaves the peer waiting and the run stuck.
    /// - witness: `tests::sessions::an_abandoned_end_s_waiting_peer_is_abandoned`
    fn unwound(
        &mut self,
        runtime: &mut Runtime,
        stack: Word,
    ) -> Result<(), Refusal>
    {
        if kind(stack)? != Kind::Stack {
            return Err(Refusal::Operands);
        }
        let object = stack.to_pointer::<Word>();
        // SAFETY: a stack's first word is its header.
        let header = Header::from_word(unsafe { *object });
        let mut top = runtime.frame_top();
        let mut held = Vec::new();
        let mut spared = Vec::new();
        for index in 0 .. usize::from(header.arity()) {
            let at = object.wrapping_add(STACK_PREFIX.saturating_add(index.saturating_mul(2)));
            // SAFETY: the stack holds its frames after its prefix.
            let code = unsafe { *at };
            // SAFETY: as above.
            let window = unsafe { *at.wrapping_add(1) };
            let unwinds = self.unwinds.get(&code).copied();
            for &slot in self.sites.linears(code) {
                // SAFETY: a frame holding linear names is a window frame, whose
                // word is its window copy, each such slot holding a cell.
                let cell = unsafe { *slot_in(window.to_pointer::<Word>(), slot)? };
                gather_end(
                    if unwinds.is_some() {
                        &mut spared
                    }
                    else {
                        &mut held
                    },
                    cell,
                );
            }
            let Some(unwind) = unwinds
            else {
                continue;
            };
            let next = top.wrapping_add(2);
            hold_frames(next, runtime.frame_limit())?;
            if let Some(Owners::Window(slots)) = self.sites.owners(code) {
                // The unwind consumes what the access's frame owns, which
                // the stack's release below drops too: each gains an owner.
                let copy = window.to_pointer::<Word>();
                for &slot in slots {
                    // SAFETY: a window frame's word is its window copy, which
                    // holds its frame's owned slots.
                    share(unsafe { *slot_in(copy, slot)? });
                }
            }
            // SAFETY: the frame fits below the region's limit.
            unsafe {
                *top = unwind;
            }
            // SAFETY: as above.
            unsafe {
                *top.wrapping_add(1) = window;
            }
            top = next;
        }
        runtime.set_frame_top(top);
        spared.sort_unstable();
        held.retain(|cell| spared.binary_search(cell).is_err());
        self.cancel_cells(runtime, &held)?;
        let sites = self.sites;
        // SAFETY: a counted abandonment owns the stack it was handed, a
        // value of the run's heap, and reads it no more.
        unsafe {
            give_up(runtime, stack, |object| owned(object, sites));
        }
        Ok(())
    }

    /// Pop an access's frame with `answer` in hand and the view `view`: a
    /// resumed view's value is written into its held cell and the answer
    /// passes on; an aborted one's answer is saved in an answer frame and the
    /// run continues at `unwind`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a view never ended; [`Refusal::Frames`]
    /// past the frame region's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a held pair written back whole and a held list
    ///   written back at a place answer the values written: an end that writes
    ///   nothing back, or releases the old value early, answers the old value
    ///   or a freed one.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn ended(
        &self,
        runtime: &mut Runtime,
        unwind: Label,
        answer: Word,
        view: Word,
    ) -> Result<Word, Refusal>
    {
        let object = cell(view)?;
        // SAFETY: a view holds its state, the value written back and its held
        // cell after its value.
        let state = usize::from(unsafe { *object.wrapping_add(STATE) });
        // SAFETY: as above.
        let written = unsafe { *object.wrapping_add(WRITTEN) };
        // SAFETY: as above.
        let held = unsafe { *object.wrapping_add(HELD) };
        match state {
            RESUMED => {
                let target = cell(held)?;
                // SAFETY: a view's header counts its fields.
                let fields = usize::from(Header::from_word(unsafe { *object }).arity());
                // SAFETY: a cell holds its value first.
                let old = unsafe { *target.wrapping_add(VALUE) };
                let replacement = if fields == PLACED {
                    // SAFETY: a view at a place holds its index after its held
                    // cell.
                    let index = unsafe { *object.wrapping_add(INDEX) };
                    replaced(runtime, old, index, written)?
                }
                else {
                    written
                };
                // SAFETY: a cell holds its value first.
                unsafe {
                    *target.wrapping_add(VALUE) = replacement;
                }
                let sites = self.sites;
                // SAFETY: the held cell owned the value it held, which the
                // write-back replaced; a rebuilt list's copies own what
                // they share with it.
                unsafe {
                    give_up(runtime, old, |object| owned(object, sites));
                }
                // SAFETY: the access has ended: its frame is popping and its
                // body's slot is dead, so nothing reads the view again. It
                // owns nothing: its value moved into the held cell.
                unsafe {
                    runtime.reclaim(view);
                }
                Ok(answer)
            },
            ABORTED => {
                let top = runtime.frame_top();
                let next = top.wrapping_add(2);
                hold_frames(next, runtime.frame_limit())?;
                let code = self.codes.stub(Stub::Answer);
                // SAFETY: the frame fits below the region's limit.
                unsafe {
                    *top = code;
                }
                // SAFETY: as above.
                unsafe {
                    *top.wrapping_add(1) = answer;
                }
                runtime.set_frame_top(next);
                runtime.jump(self.codes.label(unwind), runtime.environment());
                Ok(answer)
            },
            _ => Err(Refusal::Operands),
        }
    }
}

/// A frame a stack holds: its code word, its second word, and the slot count
/// of the window that word addresses, when it addresses one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// The code the frame resumes.
    code: Word,
    /// Its second word: a window or a value.
    word: Word,
    /// The window's slot count, or none for a value.
    window: Option<Slots>,
}

/// Why a store's value could not be laid out on the run's heap.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unlaid
{
    /// The store does not hold this value, or a run cannot hold it: code the
    /// host built, a capability no handler of the run introduced.
    Value(HeapValueId),
    /// The run's heap refused.
    Run(Refusal),
}

/// Values of the caller's store laid out on the run's heap: a value the run
/// moved out answered by the object it was moved from.
struct Laying<'laying>
{
    /// The caller's store.
    store: &'laying Store,
    /// The run's heads, by family, which a head the value holds and the
    /// table lacks joins.
    heads: &'laying mut Vec<ConstructorTag>,
    /// The function's codes, by family.
    code_table: &'laying [gandr_core_term::ValueId],
    /// The run's literals, by family, which a literal the reply holds joins.
    literals: &'laying mut Vec<Literal>,
    /// The run's objects already moved into the store.
    moved: &'laying Moved,
    /// The function's closure sites, a thunk, a fixpoint or a closure moved
    /// into the run is laid out at.
    sites: &'laying Sites<'laying>,
    /// The commands the function was lowered from, which name each site's
    /// thunk.
    arena: &'laying CommandArena,
}

impl Laying<'_>
{
    /// The objects the store's values `values` are laid out as, in order,
    /// each object's fields laid out first.
    ///
    /// # Specification
    /// - requires: `runtime` is the record of the run whose objects `moved`
    ///   names.
    /// - ensures: a value the run moved out answers the object it was moved
    ///   from, so a thunk or a function keeps its identity; any other value is
    ///   allocated once, however many of `values` and their fields hold it,
    ///   counted one owner per holder, as the run lays out its own: an integer
    ///   a word holds as an integer object, another literal as an object naming
    ///   its new row in the run's literal table, a tuple, an injection or a
    ///   datatype's constructor over its fields, any other head as a head
    ///   object naming its row in the run's head table, which it joins when the
    ///   function's lacks it, an opaque constant as an opaque object, and a
    ///   thunk, a fixpoint or a closure as a closure at the function's site for
    ///   its code, of the flavour that site allocates, its captures its fields.
    /// - executable: none — the objects are memory no predicate reads.
    ///
    /// # Errors
    /// [`Unlaid::Value`] naming a value the store does not hold, or code, a
    /// capability, a stack, or a thunk, a fixpoint or a closure whose code has
    /// no site or whose captures its site does not take, that the run did not
    /// move out; [`Unlaid::Run`] past the heap's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — replies of an integer, the unit, the payload itself,
    ///   a value the store does not hold and a pair holding one value twice,
    ///   and two captures bound to one value, each continuing or stopping the
    ///   run as it states; a second holder left uncounted frees the value while
    ///   it is read. A record a migration answers, which the caller's function
    ///   never builds, is laid out under the head it joins to the table. A
    ///   thunk a migration answers runs at the caller's site for its body. A
    ///   fixpoint and a function a writer's captures hold run at the writer's
    ///   sites for their code. Two holders count alike whichever is counted,
    ///   and an owner too many shows in no answer, so the counts of a value
    ///   under three holders, two roots and a field, and of values under one
    ///   are read where they are laid.
    /// - witness: `tests::seam::a_host_reply_flows_into_the_rest_of_the_run`
    /// - witness: `tests::seam::a_host_reply_of_its_payload_keeps_its_identity`
    /// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
    /// - witness: `tests::seam::a_host_reply_sharing_a_field_counts_each_holder_3170`
    /// - witness: `tests::closed::a_shared_capture_is_laid_out_once_and_counted_twice`
    /// - witness: `tests::world::a_record_built_only_at_the_world_comes_back`
    /// - witness: `tests::world::a_thunk_a_migration_returns_runs_at_the_caller_3265`
    /// - witness: `tests::cut::a_recursive_writer_capturing_its_own_fixpoint_answers_2954`
    /// - witness: `tests::cut::a_writer_over_a_captured_function_answers_as_its_sequential_schedule`
    /// - witness: `host::tests::a_laying_counts_one_owner_per_holder`
    fn laid(
        &mut self,
        runtime: &mut Runtime,
        values: &[HeapValueId],
    ) -> Result<Vec<Word>, Unlaid>
    {
        let store = self.store;
        let mut laid: BTreeMap<HeapValueId, Word> =
            self.moved.iter().map(|(&word, &id)| (id, word)).collect();
        // The values this laying allocates, each counted one owner by its
        // allocation, and those of them a holder already holds: each later
        // holder, a field or one of `values`, counts one owner more.
        let mut fresh = BTreeSet::new();
        let mut held = BTreeSet::new();
        let mut words = Vec::with_capacity(values.len());
        for &root in values {
            let mut pending = Vec::from([(root, false)]);
            while let Some((id, entered)) = pending.pop() {
                if laid.contains_key(&id) {
                    continue;
                }
                let value = store.value(id).ok_or(Unlaid::Value(id))?;
                let fields: Cow<'_, [HeapValueId]> = match *value {
                    HeapValue::Constructed { ref fields, .. } => Cow::Borrowed(fields),
                    HeapValue::Thunk { environment, .. }
                    | HeapValue::Fixpoint { environment, .. }
                    | HeapValue::Closure { environment, .. } => {
                        Cow::Owned(store.bound_values(environment).collect())
                    },
                    HeapValue::Literal(_)
                    | HeapValue::Stack { .. }
                    | HeapValue::Opaque(_)
                    | HeapValue::Code(_)
                    | HeapValue::Capability => Cow::Borrowed(&[]),
                };
                if !entered {
                    pending.push((id, true));
                    pending.extend(
                        fields
                            .iter()
                            .rev()
                            .filter(|field| !laid.contains_key(field))
                            .map(|&field| (field, false)),
                    );
                    continue;
                }
                let word = self.object(runtime, id, &laid)?;
                for &field in fields.iter() {
                    if fresh.contains(&field) && !held.insert(field) {
                        share(*laid.get(&field).ok_or(Unlaid::Value(field))?);
                    }
                }
                laid.insert(id, word);
                fresh.insert(id);
            }
            let word = *laid.get(&root).ok_or(Unlaid::Value(root))?;
            if fresh.contains(&root) && !held.insert(root) {
                share(word);
            }
            words.push(word);
        }
        Ok(words)
    }

    /// Allocate the store's value `id`, its fields laid out in `laid`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::laid`].
    fn object(
        &mut self,
        runtime: &mut Runtime,
        id: HeapValueId,
        laid: &BTreeMap<HeapValueId, Word>,
    ) -> Result<Word, Unlaid>
    {
        let width = |_overflow| Unlaid::Value(id);
        let header = |kind, tag: usize, arity: usize, family| -> Result<Word, Unlaid> {
            Ok(Header::new(
                kind,
                Tag::try_from(tag).map_err(width)?,
                Arity::try_from(arity).map_err(width)?,
                family,
            )
            .word())
        };
        let value = self.store.value(id).ok_or(Unlaid::Value(id))?;
        let words = match *value {
            HeapValue::Literal(ref literal) => {
                let bits = match *literal {
                    Literal::Integer(ref integer) => integer_word(integer),
                    Literal::Text(_)
                    | Literal::Numeric(_)
                    | Literal::Character(_)
                    | Literal::Float64(_)
                    | Literal::Fixed(_) => None,
                };
                if let Some(bits) = bits {
                    Vec::from([header(Kind::Integer, 0, 1, Family::UNNAMED)?, bits])
                }
                else {
                    let family = Family::try_from(self.literals.len()).map_err(width)?;
                    self.literals.push(literal.clone());
                    Vec::from([header(Kind::Literal, 0, 0, family)?])
                }
            },
            HeapValue::Constructed {
                ref tag,
                ref fields,
            } => {
                let (kind, bits, family) = match *tag {
                    ConstructorTag::Tuple(_) => (Kind::Tuple, 0, Family::UNNAMED),
                    ConstructorTag::Injection(summand) => {
                        (Kind::Injection, usize::from(summand), Family::UNNAMED)
                    },
                    ConstructorTag::Data {
                        tag: constructor,
                        family,
                        ..
                    } => (
                        Kind::Data,
                        usize::from(constructor),
                        family.map_or(Ok(Family::UNNAMED), |family| {
                            Family::try_from(usize::from(family)).map_err(width)
                        })?,
                    ),
                    ConstructorTag::Record(_)
                    | ConstructorTag::ListNil
                    | ConstructorTag::ListCons
                    | ConstructorTag::Lift(_)
                    | ConstructorTag::Recorded(_)
                    | ConstructorTag::Dialogue(_)
                    | ConstructorTag::Web(_) => {
                        let family = joined(self.heads, tag).ok_or(Unlaid::Value(id))?;
                        (Kind::Head, 0, family)
                    },
                };
                let mut words = Vec::with_capacity(fields.len().saturating_add(1));
                words.push(header(kind, bits, fields.len(), family)?);
                for field in fields {
                    words.push(*laid.get(field).ok_or(Unlaid::Value(*field))?);
                }
                words
            },
            HeapValue::Opaque(constant) => Vec::from([header(
                Kind::Opaque,
                0,
                0,
                Family::try_from(usize::from(constant)).map_err(width)?,
            )?]),
            HeapValue::Code(code) => {
                let row = self
                    .code_table
                    .iter()
                    .position(|held| *held == code)
                    .ok_or(Unlaid::Value(id))?;
                Vec::from([header(
                    Kind::Code,
                    0,
                    0,
                    Family::try_from(row).map_err(width)?,
                )?])
            },
            HeapValue::Thunk { environment, .. }
            | HeapValue::Fixpoint { environment, .. }
            | HeapValue::Closure { environment, .. } => {
                let (code, site, flavour) = self
                    .sites
                    .closure(self.arena, value)
                    .ok_or(Unlaid::Value(id))?;
                let captures: Vec<HeapValueId> = self.store.bound_values(environment).collect();
                if captures.len() != site.captures.len() {
                    return Err(Unlaid::Value(id));
                }
                let mut words = Vec::from([
                    Header::new(
                        Kind::Closure,
                        Tag::from(flavour),
                        Arity::try_from(captures.len()).map_err(width)?,
                        Family::UNNAMED,
                    )
                    .word(),
                    code,
                ]);
                words.resize(captures.len().saturating_add(2), Word::from(0_usize));
                // Each capture goes to the slot the site's body reads it from.
                for (capture, slot) in captures.iter().zip(&site.captures) {
                    let field = usize::try_from(slot.0)
                        .ok()
                        .and_then(|slot| slot.checked_add(2))
                        .and_then(|field| words.get_mut(field))
                        .ok_or(Unlaid::Value(id))?;
                    *field = *laid.get(capture).ok_or(Unlaid::Value(*capture))?;
                }
                words
            },
            HeapValue::Capability | HeapValue::Stack { .. } => return Err(Unlaid::Value(id)),
        };
        allocate(runtime, &words).map_err(Unlaid::Run)
    }
}

/// The family of the head `tag` in the run's table `heads`, which it joins as
/// a new row when the table lacks it; nothing past the family field's width.
///
/// # Specification
/// trivial.
fn joined(
    heads: &mut Vec<ConstructorTag>,
    tag: &ConstructorTag,
) -> Option<Family>
{
    let row = heads
        .iter()
        .position(|head| head == tag)
        .unwrap_or_else(|| {
            heads.push(tag.clone());
            heads.len().saturating_sub(1)
        });
    Family::try_from(row).ok()
}

/// Allocate a stack of `frames`, bottom first, captured from the region
/// `[base, top)`: each window the frames resume in is copied once after
/// them, however many frames share it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for more frames than the arity field holds;
/// [`Refusal::Heap`] past the heap's limit.
fn stack(
    runtime: &mut Runtime,
    base: Word,
    top: Word,
    frames: &[Frame],
) -> Result<Word, Refusal>
{
    let mut copies: Vec<(Word, Slots)> = Vec::new();
    let mut offsets: BTreeMap<Word, usize> = BTreeMap::new();
    let mut length = STACK_PREFIX.saturating_add(frames.len().saturating_mul(2));
    for frame in frames {
        if let Some(slots) = frame.window
            && !offsets.contains_key(&frame.word)
        {
            let _first = offsets.insert(frame.word, length);
            copies.push((frame.word, slots));
            length = length.saturating_add(slots.0);
        }
    }
    let arity = Arity::try_from(frames.len()).map_err(|_overflow| Refusal::Operands)?;
    let object = runtime.reserve(Words(length))?;
    let mut words = Vec::with_capacity(length);
    words.push(object_header(Kind::Stack, arity)?);
    words.push(base);
    words.push(top);
    for frame in frames {
        words.push(frame.code);
        let copied = frame
            .window
            .and_then(|_| offsets.get(&frame.word))
            .map_or(frame.word, |&offset| {
                Word::from_pointer(object.wrapping_add(offset))
            });
        words.push(copied);
    }
    for &(word, slots) in &copies {
        let window = word.to_pointer::<Word>();
        for slot in 0 .. slots.0 {
            // SAFETY: the window holds the slots its frame's block reads.
            words.push(unsafe { *window.wrapping_add(slot) });
        }
    }
    fill(object, &words);
    Ok(Word::from_pointer(object))
}

/// The kind of the object `word` addresses.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a header no kind names.
fn kind(word: Word) -> Result<Kind, Refusal>
{
    // SAFETY: a value addresses an object, whose first word is its header.
    Header::from_word(unsafe { *word.to_pointer::<Word>() })
        .kind()
        .map_err(|_unknown| Refusal::Operands)
}

/// The header word of an object of `kind` with `fields` fields.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] never in practice: a zero tag fits.
fn object_header(
    kind: Kind,
    fields: Arity,
) -> Result<Word, Refusal>
{
    let tag = Tag::try_from(0_usize).map_err(|_overflow| Refusal::Operands)?;
    Ok(Header::new(kind, tag, fields, Family::UNNAMED).word())
}

/// The cell `word` addresses.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for an object that is no cell.
fn cell(word: Word) -> Result<*mut Word, Refusal>
{
    if kind(word)? == Kind::Cell {
        Ok(word.to_pointer::<Word>())
    }
    else {
        Err(Refusal::Operands)
    }
}

/// Allocate a cell holding `words` after its header.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Heap`] past the heap's limit.
fn allocate_cell(
    runtime: &mut Runtime,
    words: &[Word],
) -> Result<Word, Refusal>
{
    let fields = Arity::try_from(words.len()).map_err(|_overflow| Refusal::Operands)?;
    let mut object = Vec::with_capacity(words.len().saturating_add(1));
    object.push(object_header(Kind::Cell, fields)?);
    object.extend_from_slice(words);
    allocate(runtime, &object)
}

/// Where an index falls in a native list.
///
/// # Specification
/// trivial.
enum Walked
{
    /// The list's cell at the index.
    Reached(*mut Word),
    /// The index is negative or wider than a word, or the list ends before
    /// it.
    Outside,
}

/// Walk the native list `list` to its cell at the index `index`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for an index that is no integer, or a list whose
/// cells are no native list cells.
fn walk(
    list: Word,
    index: Word,
) -> Result<Walked, Refusal>
{
    let written = kind(index)?;
    let count = if written == Kind::Integer {
        // SAFETY: an integer object holds its bits in its second word.
        let bits = unsafe { *index.to_pointer::<Word>().wrapping_add(1) };
        u64::try_from(i64::from(bits))
            .ok()
            .and_then(|count| usize::try_from(count).ok())
    }
    // A literal integer is wider than a word: no list reaches it.
    else if written == Kind::Literal {
        None
    }
    else {
        return Err(Refusal::Operands);
    };
    let Some(count) = count
    else {
        return Ok(Walked::Outside);
    };
    let mut remaining = count;
    let mut cursor = list;
    loop {
        let object = cursor.to_pointer::<Word>();
        // SAFETY: a value addresses an object, whose first word is its header.
        let header = Header::from_word(unsafe { *object });
        if header.kind() != Ok(Kind::Head) {
            return Err(Refusal::Operands);
        }
        match usize::from(header.arity()) {
            0 => return Ok(Walked::Outside),
            2 => {},
            _other => return Err(Refusal::Operands),
        }
        let Some(rest) = remaining.checked_sub(1)
        else {
            return Ok(Walked::Reached(object));
        };
        remaining = rest;
        // SAFETY: a list cell holds its head, then its tail, after its header.
        cursor = unsafe { *object.wrapping_add(2) };
    }
}

/// The native list `list` with its element at the index `index` replaced by
/// `written`: the cells before it copied in order, the cells after it shared.
/// Each value a copy shares with `list`, the tail after the element and each
/// copied head, gains an owner.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] as [`walk`], and for an index naming no element;
/// [`Refusal::Heap`] past the heap's limit.
///
/// # Adequacy
/// - hypothesis: L2 — a held list of pairs written back past its head answers
///   the copied head and the shared tail beside a pair allocated after: a copy
///   that shares a head or the tail without an owner frees it, and the fresh
///   pair takes its block.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
fn replaced(
    runtime: &mut Runtime,
    list: Word,
    index: Word,
    written: Word,
) -> Result<Word, Refusal>
{
    let Walked::Reached(reached) = walk(list, index)?
    else {
        return Err(Refusal::Operands);
    };
    // SAFETY: a list cell holds its header first.
    let header = unsafe { *reached };
    // SAFETY: a list cell holds its tail in its third word.
    let tail = unsafe { *reached.wrapping_add(2) };
    share(tail);
    let rebuilt = allocate(runtime, &[header, written, tail])?;
    let mut first = rebuilt;
    let mut previous: Option<*mut Word> = None;
    let mut cursor = list;
    while cursor.to_pointer::<Word>() != reached {
        let earlier = cursor.to_pointer::<Word>();
        // SAFETY: a list cell holds its header first.
        let header = unsafe { *earlier };
        // SAFETY: a list cell holds its head in its second word.
        let head = unsafe { *earlier.wrapping_add(1) };
        share(head);
        let copied = allocate(runtime, &[header, head, rebuilt])?;
        match previous {
            // SAFETY: the previous copy is a fresh list cell, its tail in its
            // third word.
            Some(copy) => unsafe { *copy.wrapping_add(2) = copied },
            None => first = copied,
        }
        previous = Some(copied.to_pointer::<Word>());
        // SAFETY: a list cell holds its tail in its third word.
        cursor = unsafe { *earlier.wrapping_add(2) };
    }
    Ok(first)
}

/// End the view `view` in `state`, recording `written` for a resume.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a view already ended.
fn settle(
    view: Word,
    state: Word,
    written: Word,
) -> Result<(), Refusal>
{
    let object = cell(view)?;
    // SAFETY: a view holds its state and the value written back after its
    // value.
    if usize::from(unsafe { *object.wrapping_add(STATE) }) != OPEN {
        return Err(Refusal::Operands);
    }
    // SAFETY: as above.
    unsafe {
        *object.wrapping_add(STATE) = state;
    }
    // SAFETY: as above.
    unsafe {
        *object.wrapping_add(WRITTEN) = written;
    }
    Ok(())
}

/// Allocate the unit an eliminator answers.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Heap`] past the heap's limit.
fn unit(runtime: &mut Runtime) -> Result<Word, Refusal>
{
    let fields = Arity::try_from(0_usize).map_err(|_overflow| Refusal::Operands)?;
    allocate(runtime, &[object_header(Kind::Tuple, fields)?])
}

/// The slot `slot` of `window`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] for a slot past the address width.
fn slot_in(
    window: *mut Word,
    slot: Slot,
) -> Result<*mut Word, Refusal>
{
    let offset = usize::try_from(slot.0).map_err(|_overflow| Refusal::Operands)?;
    Ok(window.wrapping_add(offset))
}

/// Allocate the object `words`, header first, through `runtime`'s free lists
/// or at its heap's top, and answer its address.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Heap`] when the words would pass the heap's limit.
fn allocate(
    runtime: &mut Runtime,
    words: &[Word],
) -> Result<Word, Refusal>
{
    let object = runtime.reserve(Words(words.len()))?;
    fill(object, words);
    Ok(Word::from_pointer(object))
}

/// Allocate the window `words` at `runtime`'s heap's top, with no count, and
/// answer its address.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Heap`] when the words would pass the heap's limit.
fn allocate_window(
    runtime: &mut Runtime,
    words: &[Word],
) -> Result<Word, Refusal>
{
    let window = runtime.bump(Words(words.len()))?;
    fill(window, words);
    Ok(Word::from_pointer(window))
}

/// Write `words` from `at` on.
///
/// # Specification
/// trivial.
fn fill(
    at: *mut Word,
    words: &[Word],
)
{
    for (offset, &word) in words.iter().enumerate() {
        // SAFETY: the caller allocated the words at `at`, in the region the
        // run owns.
        unsafe {
            *at.wrapping_add(offset) = word;
        }
    }
}

/// The integer literal whose two's-complement bits `bits` holds.
///
/// # Specification
/// trivial.
#[must_use]
pub fn integer_literal(bits: Word) -> IntegerLiteral
{
    let integer = i64::from(bits);
    let sign = if integer < 0_i64 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let magnitude = Magnitude::from_decimal_text(integer.unsigned_abs().to_string())
        .unwrap_or_else(Magnitude::zero);
    IntegerLiteral::new(sign, magnitude)
}

/// Release `object`, whose last owner a drop gave up.
///
/// Its block is freed and each value `owned` names it holding loses an
/// owner; each whose last owner that was is released in turn, through a
/// worklist. Immortal values are left alone.
///
/// # Specification
/// - requires: `object` addresses a heap object whose count is one, and `owned`
///   names values the object holds, each one owner's worth.
/// - ensures: every object whose count reaches zero has its block on the free
///   list of its size; every other value `owned` names counts one owner fewer.
/// - executable: none — the counts are words of the run's heap.
///
/// # Adequacy
/// - hypothesis: L3 — a pair released frees itself and the field whose last
///   owner it held, and leaves a field another owner holds counted one less.
/// - witness: `tests::count::a_released_object_drops_what_it_holds`
///
/// # Safety
/// - unsafe invariants: `object` and every value `owned` names, transitively,
///   address objects of `runtime`'s heap or immortal constants, each preceded
///   by its count word, and no live value reaches an object whose count reaches
///   zero.
#[inline]
pub unsafe fn release<Owned>(
    runtime: &mut Runtime,
    object: Word,
    mut owned: Owned,
) where
    Owned: FnMut(Word) -> Vec<Word>,
{
    let mut pending = Vec::from([object]);
    while let Some(dead) = pending.pop() {
        for held in owned(dead) {
            let count = count_word(held);
            // SAFETY: a value the object owns is an object, preceded by its
            // count word.
            let word = unsafe { *count };
            if word == COUNT_ONE {
                pending.push(held);
            }
            else if word != COUNT_IMMORTAL {
                // SAFETY: as above.
                unsafe {
                    *count = Word::from(usize::from(word).wrapping_sub(1));
                }
            }
        }
        // SAFETY: the object's last owner is gone and its fields were read.
        unsafe {
            runtime.reclaim(dead);
        }
    }
}

/// Give up one owner of `value`: its count shrinks by one, and at its last
/// owner it is released as [`release`] does. An immortal value is left alone.
///
/// # Specification
/// - requires: `value` addresses a heap object or an immortal constant, and
///   `owned` names values an object holds, each one owner's worth.
/// - ensures: `value` counts one owner fewer, or is released when it counted
///   one, or is unchanged when immortal.
/// - executable: none — the counts are words of the run's heap.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over the named programs,
///   counted, calling primitives on values that die there: an operand given up
///   twice is freed while still held and read after.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
///
/// # Safety
/// - unsafe invariants: as [`release`], for `value` in place of the object.
#[inline]
pub unsafe fn give_up<Owned>(
    runtime: &mut Runtime,
    value: Word,
    owned: Owned,
) where
    Owned: FnMut(Word) -> Vec<Word>,
{
    let count = count_word(value);
    // SAFETY: the caller's value is preceded by its count word.
    let word = unsafe { *count };
    if word == COUNT_ONE {
        // SAFETY: the value's last owner is the caller's, given up.
        unsafe {
            release(runtime, value, owned);
        }
    }
    else if word != COUNT_IMMORTAL {
        // SAFETY: as above.
        unsafe {
            *count = Word::from(usize::from(word).wrapping_sub(1));
        }
    }
}

/// Count one more owner of `value`, a value of the run: its count grows by
/// one, unless it is immortal.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs that resume a stack twice answer as
///   they state: an owner left uncounted frees a value the second resumption
///   reads.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
fn share(value: Word)
{
    let count = count_word(value);
    // SAFETY: a value of the run addresses an object of its heap or an
    // immortal constant, each preceded by its count word.
    let word = unsafe { *count };
    if word != COUNT_IMMORTAL {
        // SAFETY: as above; a heap object's count word is the run's.
        unsafe {
            *count = Word::from(usize::from(word).wrapping_add(1));
        }
    }
}

/// The host entry every call stencil of a run enters: [`Calls::call`] on the
/// state the record's context addresses, or [`release`] for a drop's
/// [`RELEASE`] entry, over the values [`owned`] reads.
///
/// # Specification
/// - requires: the record's context addresses the run's live [`Calls`].
/// - ensures: as [`gandr_runtime_stencils::Host`]'s contract states.
/// - executable: none — the entry runs inside a chain of tail calls no
///   predicate observes.
///
/// # Adequacy
/// - hypothesis: L2 — the agreement differential over the named programs
///   calling primitives, each halting with the answer it states.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
pub extern "C" fn enter(
    runtime: *mut Runtime,
    entry: Word,
    first: Word,
    second: Word,
) -> Word
{
    // SAFETY: the call stencil passes the run's live record, which no other
    // reference reaches during the call.
    let record = unsafe { &mut *runtime };
    let calls = record.context().to_pointer::<Calls<'_, '_>>();
    // SAFETY: the run made the record with its live state as the context.
    let state = unsafe { &mut *calls };
    if entry == RELEASE {
        let sites = state.sites;
        // SAFETY: a drop passes an object of the run's heap at its last
        // owner, and what `owned` reads are values the object holds.
        unsafe {
            release(record, first, |object| owned(object, sites));
        }
        return Word::ZERO;
    }
    match state.call(record, entry, first, second) {
        Ok(answer) => answer,
        Err(refusal) => {
            record.refuse(refusal);
            Word::ZERO
        },
    }
}

/// Check that frames reaching up to `top` fit the frame region whose limit is
/// `limit`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Frames`] when `top` passes `limit`.
///
/// # Adequacy
/// - hypothesis: L3 — frames reaching exactly the limit fit and one frame more
///   does not; a strict, an equal or a reversed comparison changes one answer.
///   No named program fills the frame region.
/// - witness: `host::tests::frames_fit_their_region_up_to_its_limit`
fn hold_frames(
    top: *mut Word,
    limit: *mut Word,
) -> Result<(), Refusal>
{
    if top > limit {
        return Err(Refusal::Frames);
    }
    Ok(())
}

/// A stack's captured frames as a replay moves them: they stood in
/// `(low, high]` of the region they were captured from, as their marks read,
/// and their copies stand from `base`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Captured
{
    /// The frame region's top below the captured frames.
    low: usize,
    /// The frame region's top above them.
    high: usize,
    /// Where their copies start.
    base: *mut Word,
}

impl Captured
{
    /// The word `held`, read from a captured frame's window, with a mark
    /// into the captured frames moved as far as the frames moved.
    ///
    /// A mark is the region's top just above the frame it names: a captured
    /// frame's is past `low` and at most `high`. A mark at `low` names the
    /// frame below the captured ones, which stays where it stood, and so
    /// does every other word.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mark at each end of the captured frames moves and
    ///   the word at `low` and the one past `high` stay; either bound written
    ///   loose or strict changes one answer.
    /// - witness: `host::tests::a_replay_moves_the_marks_into_its_frames_alone`
    fn moved(
        self,
        held: Word,
    ) -> Word
    {
        let address = usize::from(held);
        if address > self.low && address <= self.high {
            Word::from_pointer(self.base.wrapping_byte_add(address.wrapping_sub(self.low)))
        }
        else {
            held
        }
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_sequent::CommandArena;
    use gandr_core_sequent::ConstructorTag;
    use gandr_core_sequent::HeapValue;
    use gandr_core_sequent::HeapValueId;
    use gandr_core_sequent::ProducerArity;
    use gandr_core_sequent::Store;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_runtime_stencils::Fuel;
    use gandr_runtime_stencils::Refusal;
    use gandr_runtime_stencils::Runtime;
    use gandr_runtime_stencils::Word;
    use gandr_runtime_stencils::count_word;

    use super::Captured;
    use super::Laying;
    use super::enter;
    use super::hold_frames;
    use crate::transfer::Moved;
    use crate::transfer::Sites;

    /// Frames fill their region up to its limit, and one frame past it is
    /// refused before it is written.
    #[test]
    fn frames_fit_their_region_up_to_its_limit()
    {
        let mut region = [Word::ZERO; 4];
        let base = (&raw mut region).cast::<Word>();
        let limit = base.wrapping_add(4);
        assert_eq!(Ok(()), hold_frames(base, limit), "no frame");
        assert_eq!(Ok(()), hold_frames(limit, limit), "frames up to the limit");
        assert_eq!(
            Err(Refusal::Frames),
            hold_frames(limit.wrapping_add(2), limit),
            "one frame past the limit"
        );
    }

    /// A replay moves each mark into the frames it copies by as far as the
    /// frames moved, the marks of the first and the last captured frame
    /// alike, and leaves the mark of the frame below them and a word past
    /// them where they were.
    #[test]
    fn a_replay_moves_the_marks_into_its_frames_alone()
    {
        let mut from = [Word::ZERO; 8];
        let mut to = [Word::ZERO; 8];
        let from = (&raw mut from).cast::<Word>();
        let to = (&raw mut to).cast::<Word>();
        let mark = |region: *mut Word, index: usize| Word::from_pointer(region.wrapping_add(index));
        let low = usize::from(mark(from, 2));
        let high = usize::from(mark(from, 6));
        let captured = Captured {
            low,
            high,
            base: to,
        };
        assert_eq!(
            mark(to, 2),
            captured.moved(mark(from, 4)),
            "the first captured frame's mark"
        );
        assert_eq!(
            mark(to, 4),
            captured.moved(mark(from, 6)),
            "the last captured frame's mark"
        );
        assert_eq!(
            mark(from, 2),
            captured.moved(mark(from, 2)),
            "the frame below stays"
        );
        assert_eq!(
            mark(from, 7),
            captured.moved(mark(from, 7)),
            "a word past the frames stays"
        );
    }

    /// A laying counts one owner per holder, the allocation counting the
    /// first: `[x, x, p]` with `x = (1, 2)` and `p = (x, 3)` lays `x` out once,
    /// held by both roots and `p`'s first field, and `1`, `2`, `3` and `p`
    /// under one holder each. An owner counted at the first holder rather than
    /// a later one, or at every holder, is a leak or a free no answer shows.
    #[test]
    fn a_laying_counts_one_owner_per_holder()
    {
        let mut store = Store::new();
        let mut integer = |digits: &str| {
            store
                .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
                    Sign::NonNegative,
                    Magnitude::from_decimal_text(String::from(digits)).expect("decimal digits"),
                ))))
                .expect("the store has room")
        };
        let one = integer("1");
        let two = integer("2");
        let three = integer("3");
        let pair = |store: &mut Store, fields: [HeapValueId; 2]| {
            store
                .allocate(HeapValue::Constructed {
                    tag: ConstructorTag::Tuple(ProducerArity::from(2_usize)),
                    fields: Box::new(fields),
                })
                .expect("the store has room")
        };
        let x = pair(&mut store, [one, two]);
        let p = pair(&mut store, [x, three]);
        let mut heap = [Word::ZERO; 64];
        let mut frames = [Word::ZERO; 2];
        let heap_base = (&raw mut heap).cast::<Word>();
        let frame_base = (&raw mut frames).cast::<Word>();
        let mut runtime = Runtime::new(
            heap_base,
            heap_base.wrapping_add(64),
            frame_base.wrapping_add(2),
            frame_base,
            Fuel::from(0_usize),
            enter,
            Word::ZERO,
        );
        let arena = CommandArena::new();
        let sites = Sites::default();
        let moved = Moved::new();
        let mut heads = Vec::new();
        let mut literals = Vec::new();
        let laid = Laying {
            store: &store,
            heads: &mut heads,
            code_table: &[],
            literals: &mut literals,
            moved: &moved,
            sites: &sites,
            arena: &arena,
        }
        .laid(&mut runtime, &[x, x, p])
        .expect("the values fit the heap");
        let [laid_x, again, laid_p] = <[Word; 3]>::try_from(laid).expect("one word per root");
        let count = |object: Word| {
            // SAFETY: the laying allocated `object` on `heap`, its count word
            // before its header.
            usize::from(unsafe { *count_word(object) })
        };
        let fields = |object: Word| {
            let header = object.to_pointer::<Word>();
            // SAFETY: the laying allocated `object` on `heap`, a pair whose
            // first field follows its header.
            let first = unsafe { *header.wrapping_add(1) };
            // SAFETY: as above, its second field after the first.
            let second = unsafe { *header.wrapping_add(2) };
            [first, second]
        };
        let [held, laid_three] = fields(laid_p);
        let [laid_one, laid_two] = fields(laid_x);
        assert_eq!(laid_x, again, "x is laid out once");
        assert_eq!(laid_x, held, "p's first field is x");
        assert_eq!(
            [3, 1, 1, 1, 1],
            [
                count(laid_x),
                count(laid_one),
                count(laid_two),
                count(laid_three),
                count(laid_p)
            ],
            "the counts of x, 1, 2, 3 and p"
        );
    }
}
