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
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_term::Zone;
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
    /// A control command: perform, handle, resume, reset, shift or memory.
    Control,
    /// A primitive operation.
    Primitive,
    /// A literal other than an integer.
    NonIntegerLiteral,
    /// An integer past 64 bits.
    WideInteger,
    /// A structural record.
    Record,
    /// A native list constructor or fold.
    NativeList,
    /// A lift to a level.
    Lift,
    /// A recorded session run.
    RecordedRun,
    /// A selection of a field.
    Selection,
    /// A declaration with no body: owed or refused.
    OpaqueConstant,
    /// Constants that unfold into one another past the unfolding bound.
    ConstantCycle,
    /// A linear variable.
    LinearVariable,
    /// A constructor with consumer fields.
    ConsumerFields,
    /// A copattern object of several arms, or of one arm neither `apply` nor
    /// `force`.
    Copattern,
    /// A destructor other than `apply` of one argument or `force`, or one of
    /// several continuations.
    Destructor,
    /// A context capture used as a value.
    CaptureAsValue,
    /// A `μ` against a `μ̃` at a negative cut: the by-name capture.
    ByNameCapture,
    /// A reified stack.
    ReifiedStack,
    /// A header field past its width: a tag, an arity or a family.
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
    /// A covariable.
    Covariable,
    /// A slot the lowering holds a value in, which no index names.
    Temporary,
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
        let mut cursor = scope;
        let mut remaining = index.0;
        while let Scope::At(at) = cursor {
            let binder = *self.binders.get(at).ok_or(Form::Unbound)?;
            if binder.binding == binding {
                let Some(next) = remaining.checked_sub(1)
                else {
                    return Ok(binder.slot);
                };
                remaining = next;
            }
            cursor = binder.parent;
        }
        Err(Form::Unbound)
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

/// A lowered command: the function and its closure sites.
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
}

/// The most constant unfoldings one lowering inlines: past it a cycle among
/// definitions is refused rather than unfolded forever.
const UNFOLDINGS: usize = 1 << 12;

/// The most instructions one lowering emits: past it the command runs on the
/// L machine rather than being copied into a function larger than a region.
const INSTRUCTIONS: usize = 1 << 18;

/// The header of a constructor head.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`Form`] naming a head outside the lowered fragment, or
/// [`Form::HeaderWidth`] for a field past its width.
pub fn constructor_header(tag: &ConstructorTag) -> Result<Header, Form>
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
        ConstructorTag::Record(_) => Err(Form::Record),
        ConstructorTag::ListNil | ConstructorTag::ListCons => Err(Form::NativeList),
        ConstructorTag::Lift(_) => Err(Form::Lift),
        ConstructorTag::Recorded(_) => Err(Form::RecordedRun),
    }
}

/// An integer literal as a machine word.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Form::WideInteger`] past 64 bits.
pub fn integer_word(integer: &IntegerLiteral) -> Result<Word, Form>
{
    let magnitude: i128 = integer
        .magnitude()
        .as_ref()
        .parse()
        .map_err(|_overflow| Form::WideInteger)?;
    let value = if integer.sign() == Sign::Negative {
        magnitude.checked_neg().ok_or(Form::WideInteger)?
    }
    else {
        magnitude
    };
    i64::try_from(value)
        .map(Word::from)
        .map_err(|_overflow| Form::WideInteger)
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
    /// Continuation blocks loaded in the current window, awaiting layout.
    blocks: Vec<(Label, ConsumerId, Scope)>,
    /// Closure bodies awaiting their own windows.
    bodies: Vec<Body>,
    /// The current window's slot count so far.
    window: u32,
    /// The constant unfoldings so far.
    unfoldings: usize,
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
    )
    {
        self.function.push(Instruction {
            stencil,
            a,
            b,
            alt: Alt::At(alt),
        });
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
        self.sites.push(Site {
            label,
            producer,
            captures: self.scopes.producers(scope),
        });
        self.bodies.push(Body {
            label,
            entry,
            command,
            scope,
        });
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
            | CommandNode::Memory { .. } => return Err(Form::Control),
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
                let resume = self.function.label();
                self.emit(StencilId::Pushk, Operand::Code(resume), alpha.operand());
                self.tasks.push(Task::Deliver(consumer, scope));
                self.tasks.push(Task::Bind(resume));
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Covariable(index) => {
                let target =
                    self.scopes
                        .slot(scope, Binding::Covariable, Index(u32::from(index)))?;
                self.emit(StencilId::Alias, alpha.operand(), target.operand());
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Top => {
                self.emit(StencilId::AliasTop, alpha.operand(), Operand::Unused);
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Destructor { .. } | ConsumerNode::DataCase { .. } => {
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(Task::Emit(
                    StencilId::Mark,
                    alpha.operand(),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(consumer, scope));
            },
            ConsumerNode::Select { .. } => return Err(Form::Selection),
            ConsumerNode::ListFold { .. } => return Err(Form::NativeList),
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
                let Literal::Integer(ref integer) = *literal
                else {
                    return Err(Form::NonIntegerLiteral);
                };
                let value = integer_word(integer)?;
                let header = Header::new(
                    Kind::Integer,
                    Tag::try_from(0_usize).map_err(|_overflow| Form::HeaderWidth)?,
                    Arity::try_from(1_usize).map_err(|_overflow| Form::HeaderWidth)?,
                    Family::UNNAMED,
                );
                let at = self.function.constant(&[header.word(), value]);
                self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
            },
            ProducerNode::Variable { zone, index } => {
                if zone != Zone::Intuitionistic {
                    return Err(Form::LinearVariable);
                }
                let slot = self
                    .scopes
                    .slot(scope, Binding::Producer, Index(u32::from(index)))?;
                self.emit(StencilId::Var, slot.operand(), Operand::Unused);
            },
            ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                if !consumers.is_empty() {
                    return Err(Form::ConsumerFields);
                }
                let header = constructor_header(tag)?;
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
                Some(Definition::Opaque) | None => return Err(Form::OpaqueConstant),
            },
            ProducerNode::Primitive { .. } => return Err(Form::Primitive),
            ProducerNode::Reify(_) => return Err(Form::ReifiedStack),
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
                let slot = self
                    .scopes
                    .slot(scope, Binding::Covariable, Index(u32::from(index)))?;
                self.emit(StencilId::Ret, slot.operand(), Operand::Unused);
            },
            ConsumerNode::MuTilde { body } => {
                let (inner, slot) = self.bind(scope, Binding::Producer);
                self.emit(StencilId::Bind, slot.operand(), Operand::Unused);
                self.tasks.push(Task::Command(body, inner));
            },
            ConsumerNode::Case { ref arms } => {
                let mut labels = Vec::with_capacity(arms.len());
                for arm in arms {
                    let (low, family) = header_operands(constructor_header(&arm.constructor)?);
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
            ConsumerNode::Select { .. } => return Err(Form::Selection),
            ConsumerNode::ListFold { .. } => return Err(Form::NativeList),
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
                let slot = self
                    .scopes
                    .slot(scope, Binding::Covariable, Index(u32::from(index)))?;
                self.emit(StencilId::Shrink, slot.operand(), Operand::Unused);
            },
            ConsumerNode::MuTilde { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::DataCase { .. } => {
                let label = self.function.label();
                self.emit(StencilId::Pushf, Operand::Code(label), Operand::Unused);
                self.blocks.push((label, id, scope));
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
            ConsumerNode::Select { .. } => return Err(Form::Selection),
            ConsumerNode::ListFold { .. } => return Err(Form::NativeList),
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
    };
    let mut entry: Option<Position> = None;
    loop {
        while let Some(task) = lowering.tasks.pop() {
            lowering.step(task)?;
        }
        if let Some((label, consumer, scope)) = lowering.blocks.pop() {
            lowering.function.bind(label);
            lowering.tasks.push(Task::Deliver(consumer, scope));
            continue;
        }
        let window = Slot(lowering.window);
        match entry {
            None => lowering.function.set_slots(Slots(
                usize::try_from(window.0).map_err(|_overflow| Form::HeaderWidth)?,
            )),
            Some(at) => lowering.function.set_a(at, window.operand()),
        }
        let Some(body) = lowering.bodies.pop()
        else {
            break;
        };
        entry = Some(lowering.open(body));
    }
    Ok(Lowered {
        function: lowering.function,
        sites: lowering.sites,
    })
}
