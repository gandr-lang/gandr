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

use alloc::collections::BTreeMap;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Store;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::primitive::PrimitiveError;
use gandr_core_term::primitive::Scalar;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::Summand;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Refusal;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Tag;
use gandr_runtime_stencils::Word;

use crate::executor::Program;
use crate::function::Function;
use crate::function::Label;
use crate::function::Slots;
use crate::function::Stub;
use crate::lower::Callee;
use crate::lower::Clause;
use crate::lower::Handler;
use crate::lower::Lowered;
use crate::lower::Reach;
use crate::lower::Reified;
use crate::lower::Slot;
use crate::lower::integer_word;
use crate::seam::HostRequest;
use crate::seam::HostValues;
use crate::seam::Offer;
use crate::seam::Offered;
use crate::transfer::Moved;
use crate::transfer::Sites;
use crate::transfer::Tables;
use crate::transfer::TransferRefusal;
use crate::transfer::transfer;

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
}

/// One run's host state: the function's callees, handlers and frame
/// windows, where its code is, the literals the run holds — the function's
/// own, then those its calls made — and what the run moves into the caller's
/// store: the host's payloads, the answer and the values a stuck run names.
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
    windows: &'run [(Label, Slots)],
    /// The heads a head object names, by family.
    heads: &'run [ConstructorTag],
    /// The codes a code object names, by family.
    code_table: &'run [gandr_core_term::ValueId],
    /// Where the run's code is.
    codes: Codes<'run>,
    /// The closure sites, by their code words.
    sites: &'run Sites<'run>,
    /// The commands the function was lowered from.
    arena: &'run CommandArena,
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
    /// A primitive's operand is neither an integer nor a boolean.
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
}

/// The parts a run's host state holds: the function lowered from `arena`,
/// its code, its closure sites, the caller's store and the host.
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
    /// The caller's store.
    pub store: &'run mut Store,
    /// The host unclaimed operations are offered to, if any.
    pub offer: Option<&'run mut (dyn Offer + 'host)>,
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
            store,
            offer,
        } = parts;
        Self {
            callees: &lowered.callees,
            handlers: &lowered.handlers,
            windows: &lowered.windows,
            heads: &lowered.heads,
            code_table: &lowered.codes,
            codes,
            sites,
            arena,
            store,
            moved: Moved::new(),
            offer,
            literals: lowered.literals.clone(),
            refused: None,
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
            heads: self.heads,
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

    /// The integer or boolean the operand `word` addresses.
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
                Some(&(Literal::Text(_) | Literal::Numeric(_))) | None => Err(Refusal::Operands),
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
    /// evaluation the prelude refuses or a control operation the run cannot
    /// answer; [`Refusal::Heap`] or [`Refusal::Frames`] past a region's limit.
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
                self.perform(runtime, (signature, operation, at), capability, payload)
            },
            Callee::Shift(_) => self.shift(runtime),
            Callee::Replay(_) => self.replay(runtime, first),
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
                Callee::Primitive(_)
                | Callee::Hold
                | Callee::Access
                | Callee::AccessAt(_)
                | Callee::Element(_)
                | Callee::Resumed
                | Callee::Aborted
                | Callee::Reify(_) => Some(Refused::Operands),
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
        let borrowed: Vec<Scalar<&IntegerLiteral>> =
            operands.iter().map(Scalar::borrowed).collect();
        let answer = match callee.evaluate(&borrowed) {
            Ok(answer) => answer,
            Err(error) => {
                self.refused = Some(Refused::Primitive(error));
                return Err(Refusal::Operands);
            },
        };
        let width = |_overflow| Refusal::Operands;
        match answer {
            Scalar::Integer(integer) => {
                if let Some(bits) = integer_word(&integer) {
                    let header = Header::new(
                        Kind::Integer,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(1_usize).map_err(width)?,
                        Family::UNNAMED,
                    );
                    allocate(runtime, &[header.word(), bits])
                }
                else {
                    let entry = self.literals.len();
                    let header = Header::new(
                        Kind::Literal,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(0_usize).map_err(width)?,
                        Family::try_from(entry).map_err(width)?,
                    );
                    let answer = allocate(runtime, &[header.word()])?;
                    self.literals.push(Literal::Integer(integer));
                    Ok(answer)
                }
            },
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
        }
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
    fn window(
        &self,
        code: Word,
    ) -> Result<Option<Slots>, Refusal>
    {
        let codes = self.codes;
        if Stub::ALL.iter().any(|&stub| codes.stub(stub) == code) {
            return Ok(None);
        }
        self.windows
            .iter()
            .find(|&&(label, _)| codes.label(label) == code)
            .map(|&(_, slots)| Some(slots))
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
        let stack = self.capture(runtime, frame)?;
        runtime.set_frame_top(frame);
        let at = slot_in(window, clause.payload)?;
        // SAFETY: the payload's slot lies inside the handler's window.
        unsafe {
            *at = payload;
        }
        runtime.jump(self.codes.label(clause.label), window);
        Ok(stack)
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
            heads: self.heads,
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
                    heads: self.heads,
                    code_table: self.code_table,
                    literals: &mut self.literals,
                    moved: &self.moved,
                };
                match laying.laid(runtime, reply) {
                    Ok(word) => Ok(word),
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

    /// Copy the frames from `from` to the top into a stack.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a frame the function never pushes; as
    /// [`stack`] otherwise.
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
    /// stack.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Refusal::Operands`] for a value that is no stack;
    /// [`Refusal::Frames`] or [`Refusal::Heap`] past a region's limit.
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
        if top > runtime.frame_limit() {
            return Err(Refusal::Frames);
        }
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
                            let address = usize::from(held);
                            words.push(if address > low && address <= high {
                                Word::from_pointer(
                                    base.wrapping_byte_add(address.wrapping_sub(low)),
                                )
                            }
                            else {
                                held
                            });
                        }
                        let fresh = allocate(runtime, &words)?;
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
        }
        runtime.set_frame_top(top);
        Ok(stack)
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
                let replacement = if fields == PLACED {
                    // SAFETY: a view at a place holds its index after its held
                    // cell.
                    let index = unsafe { *object.wrapping_add(INDEX) };
                    // SAFETY: a cell holds its value first.
                    let list = unsafe { *target.wrapping_add(VALUE) };
                    replaced(runtime, list, index, written)?
                }
                else {
                    written
                };
                // SAFETY: a cell holds its value first.
                unsafe {
                    *target.wrapping_add(VALUE) = replacement;
                }
                Ok(answer)
            },
            ABORTED => {
                let top = runtime.frame_top();
                let next = top.wrapping_add(2);
                if next > runtime.frame_limit() {
                    return Err(Refusal::Frames);
                }
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

/// Why a host's reply could not be laid out on the run's heap.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unlaid
{
    /// The store does not hold this value, or a run cannot hold it: code the
    /// host built, a capability no handler of the run introduced.
    Value(HeapValueId),
    /// The run's heap refused.
    Run(Refusal),
}

/// A reply laid out on the run's heap: read from the caller's store, a value
/// the run moved out answered by the object it was moved from.
struct Laying<'laying>
{
    /// The caller's store.
    store: &'laying Store,
    /// The function's heads, by family.
    heads: &'laying [ConstructorTag],
    /// The function's codes, by family.
    code_table: &'laying [gandr_core_term::ValueId],
    /// The run's literals, by family, which a literal the reply holds joins.
    literals: &'laying mut Vec<Literal>,
    /// The run's objects already moved into the store.
    moved: &'laying Moved,
}

impl Laying<'_>
{
    /// The object the store's value `reply` is laid out as, its fields laid
    /// out first.
    ///
    /// # Specification
    /// - requires: `runtime` is the record of the run whose objects `moved`
    ///   names.
    /// - ensures: a value the run moved out answers the object it was moved
    ///   from, so a thunk or a function keeps its identity; any other value is
    ///   allocated as the run lays out its own: an integer a word holds as an
    ///   integer object, another literal as an object naming its new row in the
    ///   run's literal table, a tuple, an injection or a datatype's constructor
    ///   over its fields, a head the function's table holds as a head object,
    ///   an opaque constant as an opaque object.
    /// - executable: none — the objects are memory no predicate reads.
    ///
    /// # Errors
    /// [`Unlaid::Value`] naming a value the store does not hold, a head the
    /// function's table lacks, or code or a capability the host built;
    /// [`Unlaid::Run`] past the heap's limit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — replies of an integer, the unit, the payload itself
    ///   and a value the store does not hold, each continuing or stopping the
    ///   run as it states.
    /// - witness: `tests::seam::a_host_reply_flows_into_the_rest_of_the_run`
    /// - witness: `tests::seam::a_host_reply_of_its_payload_keeps_its_identity`
    /// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
    fn laid(
        &mut self,
        runtime: &mut Runtime,
        reply: HeapValueId,
    ) -> Result<Word, Unlaid>
    {
        let mut laid: BTreeMap<HeapValueId, Word> =
            self.moved.iter().map(|(&word, &id)| (id, word)).collect();
        let mut pending = Vec::from([(reply, false)]);
        while let Some((id, entered)) = pending.pop() {
            if laid.contains_key(&id) {
                continue;
            }
            let value = self.store.value(id).ok_or(Unlaid::Value(id))?;
            if !entered {
                pending.push((id, true));
                if let HeapValue::Constructed { ref fields, .. } = *value {
                    pending.extend(
                        fields
                            .iter()
                            .rev()
                            .filter(|field| !laid.contains_key(field))
                            .map(|&field| (field, false)),
                    );
                }
                continue;
            }
            let word = self.object(runtime, id, &laid)?;
            laid.insert(id, word);
        }
        laid.get(&reply).copied().ok_or(Unlaid::Value(reply))
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
        let words = match *self.store.value(id).ok_or(Unlaid::Value(id))? {
            HeapValue::Literal(ref literal) => {
                let bits = match *literal {
                    Literal::Integer(ref integer) => integer_word(integer),
                    Literal::Text(_) | Literal::Numeric(_) => None,
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
                    | ConstructorTag::Recorded(_) => {
                        let row = self
                            .heads
                            .iter()
                            .position(|head| head == tag)
                            .ok_or(Unlaid::Value(id))?;
                        (Kind::Head, 0, Family::try_from(row).map_err(width)?)
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
            HeapValue::Capability
            | HeapValue::Thunk { .. }
            | HeapValue::Fixpoint { .. }
            | HeapValue::Closure { .. }
            | HeapValue::Stack { .. } => return Err(Unlaid::Value(id)),
        };
        allocate(runtime, &words).map_err(Unlaid::Run)
    }
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
    let object = runtime.heap_top();
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
    allocate(runtime, &words)
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
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Refusal::Operands`] as [`walk`], and for an index naming no element;
/// [`Refusal::Heap`] past the heap's limit.
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

/// Allocate `words` at `runtime`'s heap top, and answer their address.
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
    let top = runtime.heap_top();
    let next = top.wrapping_add(words.len());
    if next > runtime.heap_limit() {
        return Err(Refusal::Heap);
    }
    for (offset, &word) in words.iter().enumerate() {
        // SAFETY: the words fit below the heap's limit, in the region the run
        // owns.
        unsafe {
            *top.wrapping_add(offset) = word;
        }
    }
    runtime.set_heap_top(next);
    Ok(Word::from_pointer(top))
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

/// The host entry every call stencil of a run enters: [`Calls::call`] on the
/// state the record's context addresses.
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
    match state.call(record, entry, first, second) {
        Ok(answer) => answer,
        Err(refusal) => {
            record.refuse(refusal);
            Word::ZERO
        },
    }
}
