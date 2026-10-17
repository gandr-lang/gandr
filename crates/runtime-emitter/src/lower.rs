//! Lowering: an IL command to a straight list of stencil instructions.
//!
//! The IL binds continuations; a stencil list is linear. The lowering imposes
//! this linear form:
//!
//! - **One slot per binder.** The environment is a window of word slots, a
//!   binder at lexical depth `d` writing slot `d` — producer variables and
//!   covariables in one sequence of depths, their index spaces kept apart only
//!   in the lowering's scope chain. A de Bruijn index becomes a slot number at
//!   lowering time; no chain is walked at run time. A binder's slot is
//!   overwritten only by a binder at the same depth, which runs after every
//!   reader of the old binding has left scope, because every continuation is a
//!   frame popped in LIFO order.
//! - **A covariable is a mark in a slot.** Loading a `μ̃` or a match as a
//!   continuation pushes a two-word frame (its code, the window) and binds the
//!   `μ`'s covariable to the mark above it; loading a covariable or `★` shrinks
//!   to its mark and aliases it. Delivering to a covariable shrinks to its mark
//!   and resumes the frame below. A sentinel frame resuming the halt exit sits
//!   under the base mark, so delivery never tests for an empty region.
//! - **Constructor fields on the frame region.** A constructor's fields are
//!   evaluated left to right, each pushed, and the constructor pops them.
//! - **Constants in the function's data.** A literal and a constructor of no
//!   fields are laid out once after the code; evaluating one loads its address.
//!   A literal no word holds — text, a numeric, an integer past 64 bits — is a
//!   one-word object naming its entry in the function's literal table.
//! - **Heads by identity.** A record, a native list's nil and cell, a lift and
//!   a recorded run are compared only by their head: each distinct head is an
//!   entry of the function's head table, which a header names by its family.
//!   Selecting a field by label reads a table laid out per selection, by head
//!   entry, so the labels never reach the stencils.
//! - **A fold is a loop.** Folding a native list tests each cell in turn and,
//!   for each, pushes a frame holding a closure over the window with the head
//!   bound; nil runs the empty branch with its covariable at the top, and each
//!   frame's closure answers its cell when the tail's result returns, as the L
//!   machine's bind frames do.
//! - **A primitive is a host call.** Its arguments are pushed as a
//!   constructor's fields are, and `call` passes them to the host, which
//!   evaluates the prelude row the function's callee table names.
//! - **A delimiter is a frame; control is a host call.** A handler pushes a
//!   frame resuming at its return clause, a reset one resuming at the shared
//!   reset stub, an access one resuming where its view's ending is read, and
//!   the covariable each binds falls through: delivering to it resumes whatever
//!   frame is on top, and loading it pushes nothing. An operation, a shift, a
//!   resume of a stack, a reified stack and every memory form call the host,
//!   which captures and replays frames by their code words: the function's
//!   handler table names each handler's frame code, interface, capability slot
//!   and clauses, and its window table the slot count of every frame label's
//!   window, which a capture copies. A clause is laid out in its handler's
//!   window and binds the payload the host wrote and the stack in hand.
//! - **A linear variable is a cell.** A hold binds a cell holding the value and
//!   an access a view cell lent its value, so a write-back reaches every window
//!   that copied the binding; reading the variable reads the cell's first
//!   field.
//! - **Code order is evaluation order.** A `μ`'s body is laid out before the
//!   continuation it loaded, a match's tests before its arms; every block ends
//!   in a delivery, so nothing falls through a label.
//! - **A closure copies its creator's window.** A thunk, a fixpoint and a
//!   one-arm copattern object (`apply` or `force`) evaluate to a closure over
//!   the first `d` slots, `d` the depth they are created at; the body's entry,
//!   laid out after the creator's code, allocates a fresh window on the heap,
//!   copies the captures into its first `d` slots and binds its own binders
//!   above them. A window is never shared, so a frame resumed in it finds its
//!   slots as it left them.
//! - **An observation enters code.** Delivering to `apply(p; c)` or `force(c)`
//!   saves the observed value and the argument in slots, loads `c`, and jumps
//!   to the closure's entry; loading `c` pushes, for each destructor on it, a
//!   two-word frame (a shared stub, the argument), so a returned function meets
//!   its next argument as `ret` pops it. A nominal match pushes one application
//!   frame per field and forces its branch.
//! - **A transparent constant is inlined.** Its definition is a closed
//!   producer, evaluated where the constant is, under a scope barrier so its
//!   binders take fresh slots. The machine's unfold-once memo only shares that
//!   evaluation; a pure program answers the same either way.
//!
//! A closure site is recorded for every closure the function creates: the
//! producer it suspends and the slots its visible producer binders occupy,
//! innermost first. A run's answer is moved into the machine's store through
//! these sites, so a closure in an answer is read back as the machine would
//! read its own.
//!
//! What the lowering refuses is named by [`Form`]; the L machine runs those
//! commands.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Introduces;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Route;
use gandr_core_sequent::Selector;
use gandr_core_term::FieldLabel;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::primitive::Primitive;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Flavour;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::StencilId;
use gandr_runtime_stencils::Tag;
use gandr_runtime_stencils::Word;
use gandr_theory_cell_complexes::Polarity;

use crate::function::Alt;
use crate::function::Constant;
use crate::function::Function;
use crate::function::Immediate;
use crate::function::Instruction;
use crate::function::Label;
use crate::function::Operand;
use crate::function::Position;
use crate::function::Slots;
use crate::function::Stub;

/// A form the lowering does not cover: the L machine runs a command that
/// reaches one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A constant the definitions do not hold.
    UndefinedConstant,
    /// Constants that unfold into one another past the unfolding bound.
    ConstantCycle,
    /// A constructor with consumer fields.
    ConsumerFields,
    /// A copattern object of several arms, or of one arm neither `apply` nor
    /// `force`.
    Copattern,
    /// A destructor other than `apply` of one argument or `force`, or one of
    /// several continuations, as a consumer or as a reified stack's frame.
    Destructor,
    /// A context capture used as a value.
    CaptureAsValue,
    /// A `μ` against a `μ̃` at a negative cut: the by-name capture.
    ByNameCapture,
    /// A header field past its width: a tag, an arity, a family or a table
    /// entry.
    HeaderWidth,
    /// A function past the instruction bound, larger than a region holds.
    Oversized,
    /// A node the arena does not hold.
    Dangling,
    /// A variable or covariable bound by nothing in the command.
    Unbound,
}

/// What a binder binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// A producer variable.
    Producer,
    /// A covariable whose slot holds its mark.
    Covariable,
    /// A covariable a delimiter binds, delivering to whatever frame is on
    /// top: its slot holds nothing.
    FallThrough,
    /// A linear variable, whose slot holds its cell.
    Linear,
    /// A slot the lowering holds a value in, which no index names.
    Temporary,
}

impl Binding
{
    /// The index space the binder counts in: covariables of either kind
    /// share one.
    ///
    /// # Specification
    /// trivial.
    const fn space(self) -> Self
    {
        match self {
            Self::FallThrough => Self::Covariable,
            Self::Producer | Self::Covariable | Self::Linear | Self::Temporary => self,
        }
    }
}

/// A slot of a window.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Slot(pub u32);

impl Slot
{
    /// The slot as an immediate operand.
    ///
    /// # Specification
    /// trivial.
    fn operand(self) -> Operand
    {
        Operand::Immediate(Immediate::from(self.0))
    }
}

/// One binder in scope.
#[derive(Clone, Copy, Debug)]
struct Binder
{
    /// The binder outside it.
    parent: Scope,
    /// What it binds.
    binding: Binding,
    /// Its slot, which is its depth.
    slot: Slot,
}

/// A scope: the innermost binder, if any.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Scope
{
    /// No binder is visible.
    Empty,
    /// The binder at this index of the scope tree is innermost.
    At(usize),
}

/// The binders of a lowering, as a tree of persistent chains.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Scopes
{
    /// Every binder, children after parents.
    binders: Vec<Binder>,
}

impl Scopes
{
    /// The depth of `scope`: the slot its next binder takes.
    ///
    /// # Specification
    /// trivial.
    fn depth(
        &self,
        scope: Scope,
    ) -> Slot
    {
        match scope {
            Scope::Empty => Slot(0),
            Scope::At(at) => self
                .binders
                .get(at)
                .map_or(Slot(0), |binder| Slot(binder.slot.0.saturating_add(1))),
        }
    }

    /// `scope` extended by one binder of `binding`, and the binder's slot.
    ///
    /// # Specification
    /// trivial.
    fn bind(
        &mut self,
        scope: Scope,
        binding: Binding,
    ) -> (Scope, Slot)
    {
        let slot = self.depth(scope);
        self.binders.push(Binder {
            parent: scope,
            binding,
            slot,
        });
        (Scope::At(self.binders.len().saturating_sub(1)), slot)
    }

    /// A scope at `scope`'s depth in which no binder is visible: where a
    /// closed definition is inlined, so its binders take fresh slots.
    ///
    /// # Specification
    /// trivial.
    fn barrier(
        &mut self,
        scope: Scope,
    ) -> Scope
    {
        let depth = self.depth(scope);
        let Some(below) = depth.0.checked_sub(1)
        else {
            return Scope::Empty;
        };
        self.binders.push(Binder {
            parent: Scope::Empty,
            binding: Binding::Temporary,
            slot: Slot(below),
        });
        Scope::At(self.binders.len().saturating_sub(1))
    }

    /// The binder `index` binders of `binding`'s index space out from
    /// `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] when the chain holds fewer such binders.
    fn find(
        &self,
        scope: Scope,
        binding: Binding,
        index: Index,
    ) -> Result<Binder, Form>
    {
        let mut cursor = scope;
        let mut remaining = index.0;
        while let Scope::At(at) = cursor {
            let binder = *self.binders.get(at).ok_or(Form::Unbound)?;
            if binder.binding.space() == binding.space() {
                let Some(next) = remaining.checked_sub(1)
                else {
                    return Ok(binder);
                };
                remaining = next;
            }
            cursor = binder.parent;
        }
        Err(Form::Unbound)
    }

    /// The slot of the binder `index` binders of `binding` out from `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] when the chain holds fewer such binders.
    fn slot(
        &self,
        scope: Scope,
        binding: Binding,
        index: Index,
    ) -> Result<Slot, Form>
    {
        self.find(scope, binding, index).map(|binder| binder.slot)
    }

    /// The slot of the covariable `index` covariables out from `scope`, or
    /// none for a covariable that falls through to the top frame.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] when the chain holds fewer covariables.
    fn covariable(
        &self,
        scope: Scope,
        index: Index,
    ) -> Result<Option<Slot>, Form>
    {
        let binder = self.find(scope, Binding::Covariable, index)?;
        Ok((binder.binding == Binding::Covariable).then_some(binder.slot))
    }

    /// The slots of `scope`'s visible producer binders, innermost first.
    ///
    /// # Specification
    /// trivial.
    fn producers(
        &self,
        scope: Scope,
    ) -> Vec<Slot>
    {
        let mut slots = Vec::new();
        let mut cursor = scope;
        while let Scope::At(at) = cursor {
            let Some(&binder) = self.binders.get(at)
            else {
                break;
            };
            if binder.binding == Binding::Producer {
                slots.push(binder.slot);
            }
            cursor = binder.parent;
        }
        slots
    }
}

/// A de Bruijn index, as the lowering counts it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// One step of the lowering's worklist.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Lower a command.
    Command(CommandId, Scope),
    /// Evaluate a producer into the value register.
    Producer(ProducerId, Scope),
    /// Deliver the value register to a consumer.
    Deliver(ConsumerId, Scope),
    /// Load a consumer as an observation's continuation.
    Load(ConsumerId, Scope),
    /// Fold the native list in hand by a fold consumer whose continuation is
    /// loaded.
    Fold(ConsumerId, Scope),
    /// Select from the value in hand by a selection consumer whose
    /// continuation is loaded, and deliver the field to it.
    Selected(ConsumerId),
    /// A frame's block binding the value in hand and a covariable that falls
    /// through: a handler's return clause, a reified stack's bind frame.
    Bound(CommandId, Scope),
    /// An operation clause, entered by the host with the captured stack in
    /// hand and the payload in its slot.
    Clause(CommandId, Scope),
    /// An access's frame, popped with the body's answer in hand: the view's
    /// slot and the unwind's label.
    Ended(Slot, Label),
    /// Bind a label to the next instruction.
    Bind(Label),
    /// Append one one-way instruction.
    Emit(StencilId, Operand, Operand),
}

/// How a closure's entry binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Entry
{
    /// An application arm: its argument, then its return covariable.
    Apply,
    /// A thunk or a force arm: its return covariable.
    Force,
    /// A fixpoint: itself, then its return covariable.
    Fixpoint,
}

/// A closure body awaiting its own window.
#[derive(Clone, Copy, Debug)]
struct Body
{
    /// Its entry's label.
    label: Label,
    /// How the entry binds.
    entry: Entry,
    /// The body.
    command: CommandId,
    /// The scope the closure was created in.
    scope: Scope,
}

/// A closure the function creates: what the run's answer is moved into the
/// machine's store by.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site
{
    /// The entry's label: a closure's code word is this label's address.
    pub label: Label,
    /// The suspended producer: a thunk, a fixpoint or a copattern object.
    pub producer: ProducerId,
    /// The slots of the producer binders visible where the closure is
    /// created, innermost first: the captures its environment binds.
    pub captures: Vec<Slot>,
}

/// How an operation finds its handler.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reach
{
    /// The nearest delimiter decides; the operation's one argument is its
    /// payload.
    Nearest,
    /// The handler that introduced the capability decides; the operation's
    /// arguments are the capability and the payload.
    Capability,
}

/// What a host call does, by its number in the function's callee table.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Callee
{
    /// Evaluate a primitive on its arguments.
    Primitive(Primitive),
    /// Perform an operation: capture to its handler and enter the clause.
    Perform
    {
        /// The interface the operation belongs to.
        signature: EffectName,
        /// The operation.
        operation: OperationName,
        /// How it finds its handler.
        reach: Reach,
    },
    /// Capture to the nearest reset; answers the stack.
    Shift,
    /// Push a stack's frames back, each window copied afresh.
    Replay,
    /// Hold the argument in a fresh cell; answers the cell.
    Hold,
    /// Lend a held cell's value through a fresh view; answers the view.
    Access,
    /// End a view, its value to be written back; answers the unit.
    Resumed,
    /// End a view with nothing written; answers the unit.
    Aborted,
    /// Pop an access's frame: write a resumed view back and pass the answer
    /// on, or save the answer and continue at the unwind's label.
    Ended
    {
        /// The unwind's label.
        unwind: Label,
    },
    /// Build a reified stack in the window in reach: its frames innermost
    /// first, each application's argument among the call's arguments in
    /// order.
    Reify(Vec<Reified>),
}

/// A frame of a reified stack.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reified
{
    /// An application frame: its argument is the call's next argument.
    Apply,
    /// A bind frame resuming at the label, in a copy of the window.
    Bind(Label),
}

/// An operation clause of a handler.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Clause
{
    /// The operation it answers.
    pub operation: OperationName,
    /// The clause's label, which the host continues at.
    pub label: Label,
    /// The slot of the handler's window the payload is written to.
    pub payload: Slot,
}

/// A handler the function installs: what an operation's capture finds by
/// the code of the handler's frame.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Handler
{
    /// The return clause's label: the handler frame's code.
    pub label: Label,
    /// The interface it handles.
    pub signature: EffectName,
    /// The slot of the frame's window holding the capability it introduced,
    /// when it introduces one.
    pub capability: Option<Slot>,
    /// Its operation clauses.
    pub clauses: Vec<Clause>,
}

/// A lowered command: the function, its closure sites and the tables its
/// objects and calls name.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lowered
{
    /// The function both tiers run.
    pub function: Function,
    /// Every closure site, in creation order.
    pub sites: Vec<Site>,
    /// The heads a head object names by its family.
    pub heads: Vec<ConstructorTag>,
    /// The literals a literal constant names by its family.
    pub literals: Vec<Literal>,
    /// The host calls a call names by its operand A.
    pub callees: Vec<Callee>,
    /// The handlers the function installs.
    pub handlers: Vec<Handler>,
    /// Each label a frame resumes at in a window, with the window's slot
    /// count: what a capture copies.
    pub windows: Vec<(Label, Slots)>,
}

/// The most constant unfoldings one lowering inlines: past it a cycle among
/// definitions is refused rather than unfolded forever.
const UNFOLDINGS: usize = 1 << 12;

/// The most instructions one lowering emits: past it the command runs on the
/// L machine rather than being copied into a function larger than a region.
const INSTRUCTIONS: usize = 1 << 18;

/// Push the value in hand onto the frame region: a constructor's field or a
/// call's argument.
const PUSH: Task = Task::Emit(StencilId::Push, Operand::Unused, Operand::Unused);

/// A position in one of a lowering's tables.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Row(usize);

impl Row
{
    /// The family field naming this row.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] past the family field's width.
    fn family(self) -> Result<Family, Form>
    {
        Family::try_from(self.0).map_err(|_overflow| Form::HeaderWidth)
    }
}

/// The row of `item` in `table`, appended when absent.
///
/// # Specification
/// trivial.
fn intern<Item>(
    table: &mut Vec<Item>,
    item: &Item,
) -> Row
where
    Item: Clone + PartialEq,
{
    if let Some(position) = table.iter().position(|held| held == item) {
        return Row(position);
    }
    table.push(item.clone());
    Row(table.len().saturating_sub(1))
}

/// An integer literal as a machine word, when 64 bits hold it.
///
/// # Specification
/// trivial.
#[must_use]
pub fn integer_word(integer: &IntegerLiteral) -> Option<Word>
{
    let magnitude: i128 = integer.magnitude().as_ref().parse().ok()?;
    let value = if integer.sign() == Sign::Negative {
        magnitude.checked_neg()?
    }
    else {
        magnitude
    };
    i64::try_from(value).ok().map(Word::from)
}

/// The low 32 bits of `header` and its family field: operands A and B of a
/// constructor, a case arm or a closure.
///
/// # Specification
/// trivial.
fn header_operands(header: Header) -> (Operand, Operand)
{
    let low = u32::try_from(usize::from(header.matched())).unwrap_or(u32::MAX);
    (
        Operand::Immediate(Immediate::from(low)),
        Operand::Immediate(Immediate::from(u32::from(header.family()))),
    )
}

/// One lowering's state.
struct Lowering<'run>
{
    /// The commands.
    arena: &'run CommandArena,
    /// The constants' definitions.
    definitions: &'run Definitions,
    /// The function being written.
    function: Function,
    /// The closure sites so far.
    sites: Vec<Site>,
    /// The binders.
    scopes: Scopes,
    /// The worklist of the block being written.
    tasks: Vec<Task>,
    /// Continuation blocks loaded in the current window, awaiting layout:
    /// each label and the task its block runs.
    blocks: Vec<(Label, Task)>,
    /// Closure bodies awaiting their own windows.
    bodies: Vec<Body>,
    /// The current window's slot count so far.
    window: u32,
    /// The constant unfoldings so far.
    unfoldings: usize,
    /// The heads a head object names, by family.
    heads: Vec<ConstructorTag>,
    /// The literals a literal constant names, by family.
    literals: Vec<Literal>,
    /// The host calls a call names.
    callees: Vec<Callee>,
    /// Each label selection, its table patched once every head is known.
    selections: Vec<(Position, FieldLabel)>,
    /// The handlers installed so far.
    handlers: Vec<Handler>,
    /// The frame labels of the windows already closed, with their slot
    /// counts.
    windows: Vec<(Label, Slots)>,
    /// The frame labels of the current window, its slot count still open.
    pending: Vec<Label>,
}

impl Lowering<'_>
{
    /// Append one instruction.
    ///
    /// # Specification
    /// trivial.
    fn emit(
        &mut self,
        stencil: StencilId,
        a: Operand,
        b: Operand,
    ) -> Position
    {
        self.function.push(Instruction {
            stencil,
            a,
            b,
            alt: Alt::None,
        })
    }

    /// Append one two-way instruction continuing at `alt` on a match.
    ///
    /// # Specification
    /// trivial.
    fn emit_two_way(
        &mut self,
        stencil: StencilId,
        a: Operand,
        b: Operand,
        alt: Label,
    ) -> Position
    {
        self.function.push(Instruction {
            stencil,
            a,
            b,
            alt: Alt::At(alt),
        })
    }

    /// Extend `scope` by one binder of `binding`, counting its slot in the
    /// window.
    ///
    /// # Specification
    /// trivial.
    fn bind(
        &mut self,
        scope: Scope,
        binding: Binding,
    ) -> (Scope, Slot)
    {
        let (inner, slot) = self.scopes.bind(scope, binding);
        self.window = self.window.max(slot.0.saturating_add(1));
        (inner, slot)
    }

    /// Allocate a closure over `scope`'s slots whose body is `command`,
    /// recording its site.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field.
    fn closure(
        &mut self,
        producer: ProducerId,
        scope: Scope,
        entry: Entry,
        flavour: Flavour,
        command: CommandId,
    ) -> Result<(), Form>
    {
        let label = self.suspend(scope, entry, flavour, command)?;
        self.sites.push(Site {
            label,
            producer,
            captures: self.scopes.producers(scope),
        });
        Ok(())
    }

    /// Allocate a closure over `scope`'s slots whose body is `command`, and
    /// queue the body; answers the body's label. A closure no site records
    /// never reaches an answer: a fold's cell closure lives only in a frame.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field.
    fn suspend(
        &mut self,
        scope: Scope,
        entry: Entry,
        flavour: Flavour,
        command: CommandId,
    ) -> Result<Label, Form>
    {
        let label = self.function.label();
        let depth = self.scopes.depth(scope);
        let count = usize::try_from(depth.0).map_err(|_overflow| Form::HeaderWidth)?;
        let header = Header::new(
            Kind::Closure,
            Tag::from(flavour),
            Arity::try_from(count).map_err(|_overflow| Form::HeaderWidth)?,
            Family::UNNAMED,
        );
        let (low, _) = header_operands(header);
        self.emit(StencilId::Closure, Operand::Code(label), low);
        self.bodies.push(Body {
            label,
            entry,
            command,
            scope,
        });
        Ok(label)
    }

    /// The header of a constructor head: a tuple's, an injection's and a
    /// datatype constructor's by their fields; any other head by its row in
    /// the head table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a field past its width.
    fn header(
        &mut self,
        tag: &ConstructorTag,
    ) -> Result<Header, Form>
    {
        let width = |_overflow| Form::HeaderWidth;
        match *tag {
            ConstructorTag::Tuple(arity) => Ok(Header::new(
                Kind::Tuple,
                Tag::try_from(0_usize).map_err(width)?,
                Arity::try_from(usize::from(arity)).map_err(width)?,
                Family::UNNAMED,
            )),
            ConstructorTag::Injection(summand) => Ok(Header::new(
                Kind::Injection,
                Tag::try_from(usize::from(summand)).map_err(width)?,
                Arity::try_from(1_usize).map_err(width)?,
                Family::UNNAMED,
            )),
            ConstructorTag::Data { tag, arity, family } => Ok(Header::new(
                Kind::Data,
                Tag::try_from(usize::from(tag)).map_err(width)?,
                Arity::try_from(usize::from(arity)).map_err(width)?,
                match family {
                    Some(constant) => Family::try_from(usize::from(constant)).map_err(width)?,
                    None => Family::UNNAMED,
                },
            )),
            ConstructorTag::Record(_)
            | ConstructorTag::ListNil
            | ConstructorTag::ListCons
            | ConstructorTag::Lift(_)
            | ConstructorTag::Recorded(_) => Ok(Header::new(
                Kind::Head,
                Tag::try_from(0_usize).map_err(width)?,
                Arity::try_from(usize::from(tag.producer_arity())).map_err(width)?,
                intern(&mut self.heads, tag).family()?,
            )),
        }
    }

    /// The constant holding `literal`: an integer 64 bits hold as itself,
    /// any other literal as a one-word object naming its row in the literal
    /// table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a literal table past the family field.
    fn literal(
        &mut self,
        literal: &Literal,
    ) -> Result<Constant, Form>
    {
        let width = |_overflow| Form::HeaderWidth;
        if let Literal::Integer(ref integer) = *literal
            && let Some(value) = integer_word(integer)
        {
            let header = Header::new(
                Kind::Integer,
                Tag::try_from(0_usize).map_err(width)?,
                Arity::try_from(1_usize).map_err(width)?,
                Family::UNNAMED,
            );
            return Ok(self.function.constant(&[header.word(), value]));
        }
        let header = Header::new(
            Kind::Literal,
            Tag::try_from(0_usize).map_err(width)?,
            Arity::try_from(0_usize).map_err(width)?,
            intern(&mut self.literals, literal).family()?,
        );
        Ok(self.function.constant(&[header.word()]))
    }

    /// Select by `selector` from the value in hand: the field in hand after
    /// the emitted instructions, the unmatched exit when the value holds no
    /// such field.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a component past an immediate's width.
    fn select(
        &mut self,
        selector: &Selector,
    ) -> Result<(), Form>
    {
        let found = self.function.label();
        match *selector {
            Selector::Component(component) => {
                let component =
                    u32::try_from(usize::from(component)).map_err(|_overflow| Form::HeaderWidth)?;
                self.emit_two_way(
                    StencilId::SelectComponent,
                    Operand::Immediate(Immediate::from(component)),
                    Operand::Unused,
                    found,
                );
            },
            Selector::Label(ref label) => {
                let at = self.emit_two_way(
                    StencilId::SelectField,
                    Operand::Unused,
                    Operand::Unused,
                    found,
                );
                self.selections.push((at, label.clone()));
            },
        }
        self.emit(StencilId::Unmatched, Operand::Unused, Operand::Unused);
        self.function.bind(found);
        Ok(())
    }

    /// Fold the native list in hand by the fold consumer `id`, whose
    /// continuation is loaded, in `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn fold(
        &mut self,
        id: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let &ConsumerNode::ListFold {
            on_nil, on_cons, ..
        } = self.arena.consumer(id).ok_or(Form::Dangling)?
        else {
            return Err(Form::Dangling);
        };
        let (nil_low, nil_family) = header_operands(self.header(&ConstructorTag::ListNil)?);
        let (cell_low, cell_family) = header_operands(self.header(&ConstructorTag::ListCons)?);
        let test = self.function.label();
        let empty = self.function.label();
        let cell = self.function.label();
        self.function.bind(test);
        self.emit_two_way(StencilId::Match, nil_low, nil_family, empty);
        self.emit_two_way(StencilId::Match, cell_low, cell_family, cell);
        self.emit(StencilId::Unmatched, Operand::Unused, Operand::Unused);
        self.function.bind(cell);
        let (with_head, head) = self.bind(scope, Binding::Producer);
        self.emit(StencilId::Field, head.operand(), Slot(0).operand());
        let (with_tail, tail) = self.bind(with_head, Binding::Temporary);
        self.emit(StencilId::Field, tail.operand(), Slot(1).operand());
        self.suspend(with_head, Entry::Apply, Flavour::Apply, on_cons)?;
        let (_, closure) = self.bind(with_tail, Binding::Temporary);
        self.emit(StencilId::Bind, closure.operand(), Operand::Unused);
        self.emit(
            StencilId::PushApply,
            closure.operand(),
            Operand::Stub(Stub::Argument),
        );
        self.emit(StencilId::Var, tail.operand(), Operand::Unused);
        self.emit_two_way(StencilId::Jump, Operand::Unused, Operand::Unused, test);
        self.function.bind(empty);
        let (inner, alpha) = self.bind(scope, Binding::Covariable);
        self.emit(StencilId::Mark, alpha.operand(), Operand::Unused);
        self.tasks.push(Task::Command(on_nil, inner));
        Ok(())
    }

    /// A fresh label a frame resumes at in the current window, counted among
    /// the labels a capture copies the window of.
    ///
    /// # Specification
    /// trivial.
    fn frame_label(&mut self) -> Label
    {
        let label = self.function.label();
        self.pending.push(label);
        label
    }

    /// The call of `callee` on `count` pushed arguments, as one instruction
    /// to queue.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a callee table past an immediate's width.
    fn call(
        &mut self,
        callee: &Callee,
        count: Immediate,
    ) -> Result<Task, Form>
    {
        let row = intern(&mut self.callees, callee);
        let row = u32::try_from(row.0).map_err(|_overflow| Form::HeaderWidth)?;
        Ok(Task::Emit(
            StencilId::Call,
            Operand::Immediate(Immediate::from(row)),
            Operand::Immediate(count),
        ))
    }

    /// Lower the control command `id` in `scope`. A handler's and a reset's
    /// frames are pushed as frames are, and the covariable a delimiter binds
    /// falls through to whatever frame is on top; an operation, a capture, a
    /// replay and every memory form are host calls.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn control(
        &mut self,
        id: CommandId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        match *arena.command(id).ok_or(Form::Dangling)? {
            CommandNode::Cut { .. } => return Err(Form::Dangling),
            CommandNode::Perform {
                ref signature,
                ref operation,
                route,
                payload,
                continuation,
            } => {
                let (reach, count) = match route {
                    Route::Nearest => (Reach::Nearest, Immediate::from(1_u32)),
                    Route::Capability(_) => (Reach::Capability, Immediate::from(2_u32)),
                };
                let call = self.call(
                    &Callee::Perform {
                        signature: signature.name().clone(),
                        operation: operation.clone(),
                        reach,
                    },
                    count,
                )?;
                // The host continues at the clause or refuses: nothing reaches
                // the instruction after the call.
                self.tasks.push(Task::Emit(
                    StencilId::Stuck,
                    Operand::Unused,
                    Operand::Unused,
                ));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(payload, scope));
                if let Route::Capability(capability) = route {
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Producer(capability, scope));
                }
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Handle {
                ref signature,
                introduces,
                subject,
                on_return,
                ref clauses,
                continuation,
            } => {
                let returned = self.frame_label();
                let payload = self.scopes.depth(scope);
                let mut entries = Vec::with_capacity(clauses.len());
                for clause in clauses.iter() {
                    let label = self.function.label();
                    self.blocks.push((label, Task::Clause(clause.body, scope)));
                    entries.push(Clause {
                        operation: clause.operation.clone(),
                        label,
                        payload,
                    });
                }
                self.blocks.push((returned, Task::Bound(on_return, scope)));
                let (held, capability) = match introduces {
                    Introduces::Nothing => (scope, None),
                    Introduces::Capability => {
                        let (held, slot) = self.bind(scope, Binding::Producer);
                        (held, Some(slot))
                    },
                };
                self.handlers.push(Handler {
                    label: returned,
                    signature: signature.name().clone(),
                    capability,
                    clauses: entries,
                });
                let (inner, _) = self.bind(held, Binding::FallThrough);
                self.tasks.push(Task::Command(subject, inner));
                self.tasks.push(Task::Emit(
                    StencilId::Pushf,
                    Operand::Code(returned),
                    Operand::Unused,
                ));
                if let Some(slot) = capability {
                    // A capability is a fresh object, compared by its address.
                    let width = |_overflow| Form::HeaderWidth;
                    let unit = Header::new(
                        Kind::Tuple,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(0_usize).map_err(width)?,
                        Family::UNNAMED,
                    );
                    let unit = self.function.constant(&[unit.word()]);
                    let (low, family) = header_operands(Header::new(
                        Kind::Capability,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(1_usize).map_err(width)?,
                        Family::UNNAMED,
                    ));
                    self.tasks
                        .push(Task::Emit(StencilId::Bind, slot.operand(), Operand::Unused));
                    self.tasks.push(Task::Emit(StencilId::Ctor1, low, family));
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Emit(
                        StencilId::Const,
                        Operand::Data(unit),
                        Operand::Unused,
                    ));
                }
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Reset { body, continuation } => {
                let (inner, _) = self.bind(scope, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(Task::Emit(
                    StencilId::PushForce,
                    Operand::Stub(Stub::Reset),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Shift { body, continuation } => {
                let call = self.call(&Callee::Shift, Immediate::from(0_u32))?;
                let (held, stack) = self.bind(scope, Binding::Producer);
                let (inner, _) = self.bind(held, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(Task::Emit(
                    StencilId::Bind,
                    stack.operand(),
                    Operand::Unused,
                ));
                self.tasks.push(call);
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                let call = self.call(&Callee::Replay, Immediate::from(1_u32))?;
                let (inner, _) = self.bind(scope, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(stack, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Memory {
                ref form,
                continuation,
            } => self.memory(form, continuation, scope)?,
        }
        Ok(())
    }

    /// Lower the memory form `form` with its continuation in `scope`. A
    /// linear binder's slot holds a cell: a hold's holds the value, an
    /// access's view holds the value lent, how the view ended and the held
    /// cell it writes back to.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn memory(
        &mut self,
        form: &MemoryForm<ProducerId, CommandId>,
        continuation: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *form {
            MemoryForm::Hold { value, body } => {
                let call = self.call(&Callee::Hold, Immediate::from(1_u32))?;
                let (held, cell) = self.bind(scope, Binding::Linear);
                let (inner, _) = self.bind(held, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks
                    .push(Task::Emit(StencilId::Bind, cell.operand(), Operand::Unused));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(value, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            MemoryForm::Access { held, body, unwind } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(held)))?;
                let call = self.call(&Callee::Access, Immediate::from(1_u32))?;
                let (viewed, view) = self.bind(scope, Binding::Linear);
                let (inner, _) = self.bind(viewed, Binding::FallThrough);
                let ended = self.frame_label();
                let unwinding = self.function.label();
                let (unwound, _) = self.bind(scope, Binding::FallThrough);
                self.blocks.push((ended, Task::Ended(view, unwinding)));
                self.blocks
                    .push((unwinding, Task::Command(unwind, unwound)));
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(Task::Emit(
                    StencilId::Pushf,
                    Operand::Code(ended),
                    Operand::Unused,
                ));
                self.tasks
                    .push(Task::Emit(StencilId::Bind, view.operand(), Operand::Unused));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks
                    .push(Task::Emit(StencilId::Var, cell.operand(), Operand::Unused));
                self.tasks.push(Task::Load(continuation, scope));
            },
            MemoryForm::Resume { view, value } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(view)))?;
                let call = self.call(&Callee::Resumed, Immediate::from(2_u32))?;
                self.tasks.push(Task::Deliver(continuation, scope));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(value, scope));
                self.tasks.push(PUSH);
                self.tasks
                    .push(Task::Emit(StencilId::Var, cell.operand(), Operand::Unused));
            },
            MemoryForm::Abort { view } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(view)))?;
                let call = self.call(&Callee::Aborted, Immediate::from(1_u32))?;
                self.tasks.push(Task::Deliver(continuation, scope));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks
                    .push(Task::Emit(StencilId::Var, cell.operand(), Operand::Unused));
            },
        }
        Ok(())
    }

    /// Open a closure body: bind its label, emit its entry, and queue its
    /// command. Answers the entry's instruction, whose window operand is
    /// written once the body is lowered.
    ///
    /// # Specification
    /// trivial.
    fn open(
        &mut self,
        body: Body,
    ) -> Position
    {
        self.function.bind(body.label);
        let depth = self.scopes.depth(body.scope);
        self.window = depth.0;
        let (stencil, bindings): (StencilId, &[Binding]) = match body.entry {
            Entry::Apply => (StencilId::EnterApply, &[
                Binding::Producer,
                Binding::Covariable,
            ]),
            Entry::Force => (StencilId::EnterForce, &[Binding::Covariable]),
            Entry::Fixpoint => (StencilId::EnterFix, &[
                Binding::Producer,
                Binding::Covariable,
            ]),
        };
        let at = self.emit(stencil, Slot(0).operand(), depth.operand());
        let mut scope = body.scope;
        for &binding in bindings {
            scope = self.bind(scope, binding).0;
        }
        self.tasks.push(Task::Command(body.command, scope));
        at
    }

    /// Run one task.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The [`Form`] of the first node outside the lowered fragment.
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), Form>
    {
        if self.function.instructions().len() > INSTRUCTIONS {
            return Err(Form::Oversized);
        }
        match task {
            Task::Emit(stencil, a, b) => {
                self.emit(stencil, a, b);
                Ok(())
            },
            Task::Bind(label) => {
                self.function.bind(label);
                Ok(())
            },
            Task::Command(id, scope) => self.command(id, scope),
            Task::Producer(id, scope) => self.producer(id, scope),
            Task::Deliver(id, scope) => self.deliver(id, scope),
            Task::Load(id, scope) => self.load(id, scope),
            Task::Fold(id, scope) => self.fold(id, scope),
            Task::Selected(id) => {
                let ConsumerNode::Select { ref selector, .. } =
                    *self.arena.consumer(id).ok_or(Form::Dangling)?
                else {
                    return Err(Form::Dangling);
                };
                self.select(selector)?;
                self.emit(StencilId::Pop, Operand::Unused, Operand::Unused);
                Ok(())
            },
            Task::Bound(body, scope) => {
                let (held, value) = self.bind(scope, Binding::Producer);
                self.emit(StencilId::Bind, value.operand(), Operand::Unused);
                let (inner, _) = self.bind(held, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                Ok(())
            },
            Task::Clause(body, scope) => {
                // The host wrote the payload's slot before entering.
                let (with_payload, _) = self.bind(scope, Binding::Producer);
                let (with_stack, stack) = self.bind(with_payload, Binding::Producer);
                self.emit(StencilId::Bind, stack.operand(), Operand::Unused);
                let (inner, _) = self.bind(with_stack, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                Ok(())
            },
            Task::Ended(view, unwind) => {
                let call = self.call(&Callee::Ended { unwind }, Immediate::from(2_u32))?;
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks
                    .push(Task::Emit(StencilId::Var, view.operand(), Operand::Unused));
                self.tasks.push(PUSH);
                Ok(())
            },
        }
    }

    /// Lower the command `id` in `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn command(
        &mut self,
        id: CommandId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        let (polarity, producer, consumer) = match *arena.command(id).ok_or(Form::Dangling)? {
            CommandNode::Cut {
                polarity,
                producer,
                consumer,
            } => (polarity, producer, consumer),
            CommandNode::Perform { .. }
            | CommandNode::Handle { .. }
            | CommandNode::Resume { .. }
            | CommandNode::Reset { .. }
            | CommandNode::Shift { .. }
            | CommandNode::Memory { .. } => return self.control(id, scope),
        };
        let &ProducerNode::Mu { body } = arena.producer(producer).ok_or(Form::Dangling)?
        else {
            self.tasks.push(Task::Deliver(consumer, scope));
            self.tasks.push(Task::Producer(producer, scope));
            return Ok(());
        };
        let (inner, alpha) = self.bind(scope, Binding::Covariable);
        match *arena.consumer(consumer).ok_or(Form::Dangling)? {
            ConsumerNode::MuTilde { .. } if polarity == Polarity::Negative => {
                return Err(Form::ByNameCapture);
            },
            ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } => {
                let resume = self.frame_label();
                self.emit(StencilId::Pushk, Operand::Code(resume), alpha.operand());
                self.tasks.push(Task::Deliver(consumer, scope));
                self.tasks.push(Task::Bind(resume));
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Covariable(index) => {
                if let Some(target) = self.scopes.covariable(scope, Index(u32::from(index)))? {
                    self.emit(StencilId::Alias, alpha.operand(), target.operand());
                    self.tasks.push(Task::Command(body, inner));
                }
                else {
                    let (through, _) = self.bind(scope, Binding::FallThrough);
                    self.tasks.push(Task::Command(body, through));
                }
            },
            ConsumerNode::Top => {
                self.emit(StencilId::AliasTop, alpha.operand(), Operand::Unused);
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Destructor { .. }
            | ConsumerNode::DataCase { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. } => {
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(Task::Emit(
                    StencilId::Mark,
                    alpha.operand(),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(consumer, scope));
            },
        }
        Ok(())
    }

    /// Evaluate the producer `id` into the value register.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn producer(
        &mut self,
        id: ProducerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *self.arena.producer(id).ok_or(Form::Dangling)? {
            ProducerNode::Literal(ref literal) => {
                let at = self.literal(literal)?;
                self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
            },
            ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => {
                let slot = self
                    .scopes
                    .slot(scope, Binding::Producer, Index(u32::from(index)))?;
                self.emit(StencilId::Var, slot.operand(), Operand::Unused);
            },
            ProducerNode::Variable {
                zone: Zone::Linear,
                index,
            } => {
                // A linear slot holds a cell, whose first field is the value.
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(index)))?;
                let (_, read) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Var, cell.operand(), Operand::Unused);
                self.emit(StencilId::Field, read.operand(), Slot(0).operand());
                self.emit(StencilId::Var, read.operand(), Operand::Unused);
            },
            ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                if !consumers.is_empty() {
                    return Err(Form::ConsumerFields);
                }
                let header = self.header(tag)?;
                let stencil = match producers.len() {
                    0 => {
                        let at = self.function.constant(&[header.word()]);
                        self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
                        return Ok(());
                    },
                    1 => StencilId::Ctor1,
                    2 => StencilId::Ctor2,
                    3 => StencilId::Ctor3,
                    _ => StencilId::CtorN,
                };
                let (low, family) = header_operands(header);
                self.tasks.push(Task::Emit(stencil, low, family));
                for &field in producers.iter().rev() {
                    self.tasks.push(Task::Emit(
                        StencilId::Push,
                        Operand::Unused,
                        Operand::Unused,
                    ));
                    self.tasks.push(Task::Producer(field, scope));
                }
            },
            ProducerNode::Mu { .. } => return Err(Form::CaptureAsValue),
            ProducerNode::Thunk { body } => {
                self.closure(id, scope, Entry::Force, Flavour::Thunk, body)?;
            },
            ProducerNode::Fixpoint { body, .. } => {
                self.closure(id, scope, Entry::Fixpoint, Flavour::Fixpoint, body)?;
            },
            ProducerNode::Cocase { ref arms } => match **arms {
                [arm] if arm.destructor == DestructorTag::Apply => {
                    self.closure(id, scope, Entry::Apply, Flavour::Apply, arm.body)?;
                },
                [arm] if arm.destructor == DestructorTag::Force => {
                    self.closure(id, scope, Entry::Force, Flavour::Force, arm.body)?;
                },
                _ => return Err(Form::Copattern),
            },
            ProducerNode::Constant(constant) => match self.definitions.get(constant) {
                Some(Definition::Transparent(definition)) => {
                    self.unfoldings = self.unfoldings.saturating_add(1);
                    if self.unfoldings > UNFOLDINGS {
                        return Err(Form::ConstantCycle);
                    }
                    let barrier = self.scopes.barrier(scope);
                    self.tasks.push(Task::Producer(definition, barrier));
                },
                Some(Definition::Opaque) => {
                    let width = |_overflow| Form::HeaderWidth;
                    let header = Header::new(
                        Kind::Opaque,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(0_usize).map_err(width)?,
                        Family::try_from(usize::from(constant)).map_err(width)?,
                    );
                    let at = self.function.constant(&[header.word()]);
                    self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
                },
                None => return Err(Form::UndefinedConstant),
            },
            ProducerNode::Primitive {
                primitive,
                ref arguments,
            } => {
                let count =
                    u32::try_from(arguments.len()).map_err(|_overflow| Form::HeaderWidth)?;
                let call = self.call(&Callee::Primitive(primitive), Immediate::from(count))?;
                self.tasks.push(call);
                for &argument in arguments.iter().rev() {
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Producer(argument, scope));
                }
            },
            ProducerNode::Reify(ref frames) => {
                let mut shape = Vec::with_capacity(frames.len());
                let mut arguments = Vec::new();
                for frame in frames.iter() {
                    match *frame {
                        StackFrame::Apply(argument) => {
                            arguments.push(argument);
                            shape.push(Reified::Apply);
                        },
                        StackFrame::Bind(body) => {
                            let label = self.frame_label();
                            self.blocks.push((label, Task::Bound(body, scope)));
                            shape.push(Reified::Bind(label));
                        },
                        StackFrame::Project(_) => return Err(Form::Destructor),
                    }
                }
                let count =
                    u32::try_from(arguments.len()).map_err(|_overflow| Form::HeaderWidth)?;
                let call = self.call(&Callee::Reify(shape), Immediate::from(count))?;
                self.tasks.push(call);
                for &argument in arguments.iter().rev() {
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Producer(argument, scope));
                }
            },
        }
        Ok(())
    }

    /// Deliver the value register to the consumer `id`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn deliver(
        &mut self,
        id: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *self.arena.consumer(id).ok_or(Form::Dangling)? {
            ConsumerNode::Top => {
                self.emit(StencilId::Halt, Operand::Unused, Operand::Unused);
            },
            ConsumerNode::Covariable(index) => {
                match self.scopes.covariable(scope, Index(u32::from(index)))? {
                    Some(slot) => {
                        self.emit(StencilId::Ret, slot.operand(), Operand::Unused);
                    },
                    None => {
                        self.emit(StencilId::Pop, Operand::Unused, Operand::Unused);
                    },
                }
            },
            ConsumerNode::MuTilde { body } => {
                let (inner, slot) = self.bind(scope, Binding::Producer);
                self.emit(StencilId::Bind, slot.operand(), Operand::Unused);
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Case { ref arms } => {
                let mut labels = Vec::with_capacity(arms.len());
                for arm in arms {
                    let (low, family) = header_operands(self.header(&arm.constructor)?);
                    let label = self.function.label();
                    self.emit_two_way(StencilId::Match, low, family, label);
                    labels.push(label);
                }
                self.emit(StencilId::Unmatched, Operand::Unused, Operand::Unused);
                for (arm, &label) in arms.iter().zip(&labels).rev() {
                    let mut inner = scope;
                    let mut binds = Vec::new();
                    let fields = u32::try_from(usize::from(arm.constructor.producer_arity()))
                        .map_err(|_overflow| Form::HeaderWidth)?;
                    for field in 0 .. fields {
                        let (next, slot) = self.bind(inner, Binding::Producer);
                        inner = next;
                        binds.push(Task::Emit(
                            StencilId::Field,
                            slot.operand(),
                            Slot(field).operand(),
                        ));
                    }
                    self.tasks.push(Task::Command(arm.body, inner));
                    self.tasks.extend(binds.into_iter().rev());
                    self.tasks.push(Task::Bind(label));
                }
            },
            ConsumerNode::DataCase { ref branches, then } => {
                let mut labels = Vec::with_capacity(branches.len());
                for ordinal in 0 .. branches.len() {
                    let label = self.function.label();
                    let ordinal = u32::try_from(ordinal).map_err(|_overflow| Form::HeaderWidth)?;
                    self.emit_two_way(
                        StencilId::MatchTag,
                        Slot(ordinal).operand(),
                        Operand::Unused,
                        label,
                    );
                    labels.push(label);
                }
                self.emit(StencilId::Unmatched, Operand::Unused, Operand::Unused);
                for (&branch, &label) in branches.iter().zip(&labels).rev() {
                    let (inner, held) = self.bind(scope, Binding::Temporary);
                    self.tasks.push(Task::Emit(
                        StencilId::InvokeForceValue,
                        Operand::Unused,
                        Operand::Unused,
                    ));
                    self.tasks.push(Task::Producer(branch, inner));
                    self.tasks.push(Task::Emit(
                        StencilId::PushFields,
                        held.operand(),
                        Operand::Stub(Stub::Apply),
                    ));
                    self.tasks.push(Task::Load(then, inner));
                    self.tasks
                        .push(Task::Emit(StencilId::Bind, held.operand(), Operand::Unused));
                    self.tasks.push(Task::Bind(label));
                }
            },
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let &[then] = &**consumers
                else {
                    return Err(Form::Destructor);
                };
                let (held, function) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Bind, function.operand(), Operand::Unused);
                match (tag, &**producers) {
                    (DestructorTag::Apply, &[argument]) => {
                        let (inner, slot) = self.bind(held, Binding::Temporary);
                        self.tasks.push(Task::Emit(
                            StencilId::InvokeApply,
                            function.operand(),
                            slot.operand(),
                        ));
                        self.tasks.push(Task::Load(then, inner));
                        self.tasks.push(Task::Emit(
                            StencilId::Bind,
                            slot.operand(),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Producer(argument, held));
                    },
                    (DestructorTag::Force, &[]) => {
                        self.tasks.push(Task::Emit(
                            StencilId::InvokeForce,
                            function.operand(),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Load(then, held));
                    },
                    _ => return Err(Form::Destructor),
                }
            },
            ConsumerNode::Select { ref selector, then } => {
                self.select(selector)?;
                self.tasks.push(Task::Deliver(then, scope));
            },
            ConsumerNode::ListFold { continuation, .. } => {
                let (held, list) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Bind, list.operand(), Operand::Unused);
                self.tasks.push(Task::Fold(id, scope));
                self.tasks
                    .push(Task::Emit(StencilId::Var, list.operand(), Operand::Unused));
                self.tasks.push(Task::Load(continuation, held));
            },
        }
        Ok(())
    }

    /// Load the consumer `id` as an observation's continuation.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    fn load(
        &mut self,
        id: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *self.arena.consumer(id).ok_or(Form::Dangling)? {
            ConsumerNode::Top => {
                self.emit(StencilId::ShrinkTop, Operand::Unused, Operand::Unused);
            },
            ConsumerNode::Covariable(index) => {
                // A covariable that falls through loads nothing: its frame is
                // already on top.
                if let Some(slot) = self.scopes.covariable(scope, Index(u32::from(index)))? {
                    self.emit(StencilId::Shrink, slot.operand(), Operand::Unused);
                }
            },
            ConsumerNode::MuTilde { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::DataCase { .. } => {
                let label = self.frame_label();
                self.emit(StencilId::Pushf, Operand::Code(label), Operand::Unused);
                self.blocks.push((label, Task::Deliver(id, scope)));
            },
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let &[then] = &**consumers
                else {
                    return Err(Form::Destructor);
                };
                match (tag, &**producers) {
                    (DestructorTag::Apply, &[argument]) => {
                        let (inner, slot) = self.bind(scope, Binding::Temporary);
                        self.tasks.push(Task::Emit(
                            StencilId::PushApply,
                            slot.operand(),
                            Operand::Stub(Stub::Apply),
                        ));
                        self.tasks.push(Task::Load(then, inner));
                        self.tasks.push(Task::Emit(
                            StencilId::Bind,
                            slot.operand(),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Producer(argument, scope));
                    },
                    (DestructorTag::Force, &[]) => {
                        self.tasks.push(Task::Emit(
                            StencilId::PushForce,
                            Operand::Stub(Stub::Force),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Load(then, scope));
                    },
                    _ => return Err(Form::Destructor),
                }
            },
            ConsumerNode::Select { then, .. } => {
                let label = self.frame_label();
                self.blocks.push((label, Task::Selected(id)));
                self.tasks.push(Task::Emit(
                    StencilId::Pushf,
                    Operand::Code(label),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(then, scope));
            },
            ConsumerNode::ListFold { continuation, .. } => {
                let label = self.frame_label();
                self.blocks.push((label, Task::Fold(id, scope)));
                self.tasks.push(Task::Emit(
                    StencilId::Pushf,
                    Operand::Code(label),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(continuation, scope));
            },
        }
        Ok(())
    }
}

/// Lower the closed command `root`.
///
/// # Specification
/// - requires: every constant `root` reaches is defined in `definitions`.
/// - ensures: the function's entry runs `root` from an empty frame region,
///   delivering its answer to the halt exit, as the L machine runs it: each
///   transparent constant inlined, each closure site recorded with the producer
///   it suspends.
/// - executable: none — running as the L machine does is observed only by
///   running both.
///
/// # Errors
/// The [`Form`] of the first node outside the lowered fragment.
///
/// # Adequacy
/// - hypothesis: L2 — a differential against the L machine over the named
///   programs: returns, binds, cases, constructors, functions, thunks and an
///   application. The stencils' suite runs the generated programs and the
///   corpus through this lowering too, each refused form counted by name.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub fn lower(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Result<Lowered, Form>
{
    let mut lowering = Lowering {
        arena,
        definitions,
        function: Function::default(),
        sites: Vec::new(),
        scopes: Scopes::default(),
        tasks: Vec::from([Task::Command(root, Scope::Empty)]),
        blocks: Vec::new(),
        bodies: Vec::new(),
        window: 0,
        unfoldings: 0,
        heads: Vec::new(),
        literals: Vec::new(),
        callees: Vec::new(),
        selections: Vec::new(),
        handlers: Vec::new(),
        windows: Vec::new(),
        pending: Vec::new(),
    };
    let mut entry: Option<Position> = None;
    loop {
        while let Some(task) = lowering.tasks.pop() {
            lowering.step(task)?;
        }
        if let Some((label, task)) = lowering.blocks.pop() {
            lowering.function.bind(label);
            lowering.tasks.push(task);
            continue;
        }
        let window = Slot(lowering.window);
        match entry {
            None => lowering.function.set_slots(Slots(
                usize::try_from(window.0).map_err(|_overflow| Form::HeaderWidth)?,
            )),
            Some(at) => lowering.function.set_a(at, window.operand()),
        }
        let slots = Slots(usize::try_from(window.0).map_err(|_overflow| Form::HeaderWidth)?);
        for label in core::mem::take(&mut lowering.pending) {
            lowering.windows.push((label, slots));
        }
        let Some(body) = lowering.bodies.pop()
        else {
            break;
        };
        entry = Some(lowering.open(body));
    }
    for (at, label) in core::mem::take(&mut lowering.selections) {
        let mut table = Vec::with_capacity(lowering.heads.len().saturating_add(1));
        table.push(Word::from(lowering.heads.len()));
        for head in &lowering.heads {
            let position = match *head {
                ConstructorTag::Record(ref labels) => labels
                    .iter()
                    .position(|held| *held == label)
                    .map_or(0, |position| position.saturating_add(1)),
                ConstructorTag::Tuple(_)
                | ConstructorTag::Injection(_)
                | ConstructorTag::Data { .. }
                | ConstructorTag::ListNil
                | ConstructorTag::ListCons
                | ConstructorTag::Lift(_)
                | ConstructorTag::Recorded(_) => 0,
            };
            table.push(Word::from(position));
        }
        let constant = lowering.function.constant(&table);
        lowering.function.set_a(at, Operand::Data(constant));
    }
    Ok(Lowered {
        function: lowering.function,
        sites: lowering.sites,
        heads: lowering.heads,
        literals: lowering.literals,
        callees: lowering.callees,
        handlers: lowering.handlers,
        windows: lowering.windows,
    })
}
