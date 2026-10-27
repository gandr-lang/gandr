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
//!   frame's closure answers its cell when the tail's result returns, as a bind
//!   frame answers its value.
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
//!   window, which a capture copies, and the slots its frame owns. A clause is
//!   laid out in its handler's window and binds the payload the host wrote and
//!   the stack in hand.
//! - **A linear variable is a cell.** A hold binds a cell holding the value and
//!   an access a view cell lent its value, so a write-back reaches every window
//!   that copied the binding; reading the variable reads the cell's first
//!   field.
//! - **Code order is evaluation order.** A `μ`'s body is laid out before the
//!   continuation it loaded, a match's tests before its arms; every block ends
//!   in a delivery, so nothing falls through a label.
//! - **A closure captures what it names.** A thunk, a fixpoint, a copattern
//!   object and a fold's cell closure evaluate to a closure over the slots
//!   their support selects past their own binders — producer variables and
//!   linear cells, never a covariable — each pushed in the creator's binding
//!   order and popped into the closure. A closure is second-class in the frame
//!   region: it holds no mark, since the frame a mark names may be popped and
//!   its place taken before the closure runs. `check_command` refuses a closure
//!   naming a covariable outside its own binders, and one that reaches the
//!   lowering fails to lower: an outer covariable is unbound in its body. The
//!   body's entry, laid out after the creator's code, allocates a fresh window
//!   in the window region, copies the captures into its first slots and binds
//!   its own binders above them; in the body's scope every binder the creator
//!   had still counts, so the body's indices resolve unchanged, and one it does
//!   not capture holds no slot. A window is never shared, so a frame resumed in
//!   it finds its slots as it left them. The alternative, copying the creator's
//!   whole window prefix, kept every binding in reach alive in every closure,
//!   which a counted runtime cannot afford: a closure owns exactly what it
//!   names.
//! - **An observation enters code.** Delivering to `apply(p; c)` or `force(c)`
//!   saves the observed value and the argument in slots, loads `c`, and jumps
//!   to the closure's entry; loading `c` pushes, for each destructor on it, a
//!   two-word frame (a shared stub, the argument), so a returned function meets
//!   its next argument as `ret` pops it. A nominal match pushes one application
//!   frame per field and forces its branch.
//! - **A transparent constant unfolds once a run.** Each constant the function
//!   reads has a word in the run's constant table at the heap's base, zero
//!   until its first read. A read of a zero word marks it unfolding, evaluates
//!   the definition — a closed producer laid out as its own body — and writes
//!   the value to the word, which every later read loads; a read of a word
//!   still marked unfolding is a cycle and sticks at the constant. A constant
//!   the definitions do not hold sticks where it is read; the value written is
//!   immortal, so a read shares it uncounted.
//! - **Every owner is counted.** Every command inserts the counting its
//!   ownership reading (`Ownership`, read once with the root and each
//!   constant's definition a root of its own) places: before a node runs it
//!   duplicates each name two of its children use, and on entry to a child it
//!   drops each name the child ignores. A use of a name moves its owner into
//!   what reads it. A match duplicates the matched object's fields into its
//!   binders, then drops the object; a selection duplicates the field and drops
//!   the record; a closure's entry duplicates each producer capture into its
//!   window, then drops the closure it entered, which a fixpoint's own binder
//!   keeps; a primitive's host drops its operands. A read of a linear name
//!   duplicates the value its cell holds, the cell keeping its own owner. A
//!   fold's walk owns the list: each cell's tail and each name its cell closure
//!   captures, the head among them, gain an owner before the cell is dropped,
//!   and at the empty list the walk drops the list and the names the fold's
//!   node handed the cell branch. An exclusive access's frame owns what its
//!   unwind selects, which a resumed view's end drops and an abandoned one's
//!   unwind consumes; a write-back drops the value the held cell held. A held
//!   cell is never freed: a held value outlives its cell's last read. A view is
//!   freed when its access ends, its value written back.
//! - **A body gives its window back.** Windows live in a region of their own, a
//!   stack apart from the object heap: an entry takes the region's top, and a
//!   body's return gives its window back by moving the top down to it
//!   (`leave`). Every window above it was taken by an entry after it, and every
//!   frame resuming in one sits above the body's mark, which the return pops. A
//!   call whose continuation is the body's own return — through the frames of
//!   the observations it loads, or through a `μ` or a hold that falls through
//!   to it — is the body's last act: its window is given back just before the
//!   call (`release`), the call reading its operands first, so a loop by tail
//!   recursion runs in one window's words. A window outside the region — the
//!   entry window, a replay's copy, which the host allocates on the heap — is
//!   never given back. #1175 records a heap-wide watermark instead: a
//!   stack-shaped body would restore the heap's top on return. Measured, every
//!   probe's body allocates an object that outlives it (a boxed integer written
//!   back, a field of a rebuilt pair) above its window, and freed blocks above
//!   a mark would stay on the size lists, so a heap-wide mark would almost
//!   never restore; a region of windows alone restores on every return,
//!   whatever escapes. Revisit if objects gain an arena of their own whose
//!   lifetime a body bounds.
//! - **A waiting frame owns what its block will consume.** The window table
//!   names, per frame label, the slots of the names the frame's node selects,
//!   one owner each; a handler's frame owns, besides its return clause's names,
//!   one owner of each name its clauses keep and of its capability, and gives
//!   them up when its return clause runs. A clause runs once per perform in its
//!   handler's window, so it duplicates what it keeps on entry, before a binder
//!   it ignores is dropped. A capture takes its frames off the region and their
//!   owners with them, no count changed; a replay copies each window out with
//!   an owner per entry, the stack keeping its own; the stack's release drops
//!   them. A frame resuming a block midway, after a constant's unfolding, owns
//!   the rest of the block, which no node names, so a capture across one
//!   refuses.
//!
//! A closure site is recorded for every closure the function creates: the
//! producer it suspends and its capture positions of the producer bindings
//! its support selects (`CommandArena::captures`), innermost first; a reified
//! stack's bind frame is recorded by the slots of its window, from its body's
//! support past the frame's value. A run's outcome is moved into the caller's
//! store through these records, so a closure moves exactly the values it
//! names, and a closure or a literal stack in an answer reads back as the IL
//! it suspends.
//!
//! What the lowering refuses is named by [`Form`], and the run declines with
//! it.

use alloc::collections::BTreeSet;
use core::ops::Range;

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
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::NodeCount;
use gandr_core_sequent::Ownership;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Route;
use gandr_core_sequent::Selector;
use gandr_core_sequent::Suspension;
use gandr_core_sequent::reach;
use gandr_core_term::BinderDepth;
use gandr_core_term::FieldLabel;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::OperationName;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::support::Indices;
use gandr_core_term::world::WorldForm;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_runtime_stencils::Arity;
use gandr_runtime_stencils::Family;
use gandr_runtime_stencils::Flavour;
use gandr_runtime_stencils::Header;
use gandr_runtime_stencils::Kind;
use gandr_runtime_stencils::Observed;
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
use crate::fuse::Fused;
use crate::fuse::fuse;

/// A command the lowering does not lay out.
///
/// One ill-formed — children that contradict their head, a node or a binder
/// missing — or one past a width the layout holds. A run of a command that
/// reaches one declines.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form
{
    /// A constructor with consumer fields.
    ConsumerFields,
    /// A destructor of other than one continuation, or of arguments its tag
    /// does not take, as a consumer or as a reified stack's frame.
    Destructor,
    /// A header field past its width: a tag, an arity, a family or a table
    /// entry.
    HeaderWidth,
    /// A function past the instruction bound, larger than a region holds.
    Oversized,
    /// A node the arena does not hold.
    Dangling,
    /// A variable or covariable bound by nothing in the command.
    Unbound,
    /// A node the lowering reaches that the ownership reading places nowhere,
    /// or that two parents drop differently.
    Unowned,
}

impl core::fmt::Display for Form
{
    /// Names the form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::ConsumerFields => "a constructor with consumer fields",
            Self::Destructor => "a destructor whose children contradict its tag",
            Self::HeaderWidth => "a header field past its width",
            Self::Oversized => "a function larger than a region",
            Self::Dangling => "a node the arena does not hold",
            Self::Unbound => "a variable bound by nothing in the command",
            Self::Unowned => "a node the ownership reading does not place",
        })
    }
}

/// What a binder binds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Binding
{
    /// A producer variable.
    Producer,
    /// A covariable whose slot holds its mark.
    Covariable,
    /// The covariable a closure entry binds, whose slot holds the mark of the
    /// frame its body returns to: delivered to, the body's window is given
    /// back.
    Returns,
    /// A covariable a delimiter binds, delivering to whatever frame is on
    /// top: its slot holds nothing.
    FallThrough,
    /// A covariable that falls through to the frame a closure body returns
    /// to, loaded on top with nothing pushed above it: delivered to, the
    /// body's window is given back.
    Returning,
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   and a body that returns or ends in a tail call gives its window back.
    ///   A covariable read from the wrong slot or delivered the wrong way
    ///   answers wrongly; a window kept grows the region the counts read.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_body_gives_its_window_back_at_its_tail_call_and_its_return`
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    const fn space(self) -> Self
    {
        match self {
            Self::FallThrough | Self::Returning | Self::Returns => Self::Covariable,
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
    /// Its slot, or none in a closure body that does not capture it.
    slot: Option<Slot>,
    /// The slot the next binder inside it takes.
    depth: Slot,
}

/// How a value reaches a covariable.
#[derive(Clone, Copy, Debug)]
enum Delivery
{
    /// The covariable a closure entry bound, its mark in the slot: the body
    /// returns, giving its window back.
    Return(Slot),
    /// A covariable whose slot holds its mark.
    Mark(Slot),
    /// The frame on top.
    FallThrough,
    /// The frame on top, which the closure body returns to: the body
    /// returns, giving its window back.
    Returning,
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
            Scope::At(at) => self.binders.get(at).map_or(Slot(0), |binder| binder.depth),
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
            slot: Some(slot),
            depth: Slot(slot.0.saturating_add(1)),
        });
        (Scope::At(self.binders.len().saturating_sub(1)), slot)
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
        self.find(scope, binding, index)?.slot.ok_or(Form::Unbound)
    }

    /// The slot of the covariable `index` covariables out from `scope`, or
    /// none for a covariable that falls through to the top frame.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] when the chain holds fewer covariables.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   and a body that returns or ends in a tail call gives its window back.
    ///   A covariable read from the wrong slot or delivered the wrong way
    ///   answers wrongly; a window kept grows the region the counts read.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_body_gives_its_window_back_at_its_tail_call_and_its_return`
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    /// - witness: `lower::tests::a_delivery_to_a_marked_covariable_shrinks_to_its_slot`
    fn covariable(
        &self,
        scope: Scope,
        index: Index,
    ) -> Result<Option<Slot>, Form>
    {
        Ok(match self.delivery(scope, index)? {
            Delivery::Return(slot) | Delivery::Mark(slot) => Some(slot),
            Delivery::FallThrough | Delivery::Returning => None,
        })
    }

    /// How a value is delivered to the covariable `index` covariables out
    /// from `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] when the chain holds fewer covariables.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   and a body that returns or ends in a tail call gives its window back.
    ///   A covariable read from the wrong slot or delivered the wrong way
    ///   answers wrongly; a window kept grows the region the counts read.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_body_gives_its_window_back_at_its_tail_call_and_its_return`
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    fn delivery(
        &self,
        scope: Scope,
        index: Index,
    ) -> Result<Delivery, Form>
    {
        let binder = self.find(scope, Binding::Covariable, index)?;
        match binder.binding {
            Binding::Returns => binder.slot.map(Delivery::Return).ok_or(Form::Unbound),
            Binding::Covariable => binder.slot.map(Delivery::Mark).ok_or(Form::Unbound),
            Binding::Returning => Ok(Delivery::Returning),
            Binding::Producer | Binding::FallThrough | Binding::Linear | Binding::Temporary => {
                Ok(Delivery::FallThrough)
            },
        }
    }

    /// `scope` and every scope outside it, innermost first, as binders of the
    /// scope tree; the empty scope ends them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   among them a split and a nominal match that rebuild their dying
    ///   scrutinee, a split that builds a triple before the pair it rebuilds, a
    ///   split whose scrutinee a thunk shares, and a nominal branch answering a
    ///   function past its constructor's fields; the counts rebuild a unique
    ///   scrutinee in its own block and a shared one in a fresh block. A token
    ///   built into with the wrong fields, never built into, or overwriting a
    ///   shared cell changes an answer or a count.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
    /// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
    /// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
    fn outward(
        &self,
        scope: Scope,
    ) -> impl Iterator<Item = Scope>
    {
        core::iter::successors(Some(scope), |&cursor| match cursor {
            Scope::At(at) => self.binders.get(at).map(|found| found.parent),
            Scope::Empty => None,
        })
        .take_while(|&cursor| cursor != Scope::Empty)
    }

    /// The slots of `scope`'s visible producer binders, innermost first; a
    /// binder a closure body does not capture holds none.
    ///
    /// # Specification
    /// trivial.
    fn producers(
        &self,
        scope: Scope,
    ) -> Vec<Option<Slot>>
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

    /// The base of a closure body's scope over the creator's `scope`: every
    /// binder that counts in an index space, outermost first, those `captured`
    /// selects in a fresh slot each, in order, and the rest holding none. A
    /// covariable is never captured: each outside the body's own binders is
    /// bound there as a mark it holds none of, unbound to load or deliver to.
    /// Answers the base and the creator's slot each capture copies, in slot
    /// order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   and a body that returns or ends in a tail call gives its window back.
    ///   A covariable read from the wrong slot or delivered the wrong way
    ///   answers wrongly; a window kept grows the region the counts read.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_body_gives_its_window_back_at_its_tail_call_and_its_return`
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    fn enclose(
        &mut self,
        scope: Scope,
        captured: &Captured,
    ) -> (Scope, Vec<Slot>)
    {
        let mut chain = Vec::new();
        let mut cursor = scope;
        let (mut producers, mut linears) = (Index(0), Index(0));
        while let Scope::At(at) = cursor {
            let Some(&binder) = self.binders.get(at)
            else {
                break;
            };
            let kept = match binder.binding {
                Binding::Producer => Some(captured.producers.contains(&next(&mut producers).0)),
                Binding::Linear => Some(captured.linears.contains(&next(&mut linears).0)),
                Binding::Covariable
                | Binding::Returns
                | Binding::FallThrough
                | Binding::Returning => Some(false),
                Binding::Temporary => None,
            };
            if let Some(kept) = kept {
                chain.push((binder, kept));
            }
            cursor = binder.parent;
        }
        let mut base = Scope::Empty;
        let mut sources = Vec::new();
        for (binder, kept) in chain.into_iter().rev() {
            let depth = self.depth(base);
            let slot = match (kept, binder.slot) {
                (true, Some(source)) => {
                    sources.push(source);
                    Some(depth)
                },
                (..) => None,
            };
            self.binders.push(Binder {
                parent: base,
                binding: binder.binding.space(),
                slot,
                depth: slot.map_or(depth, |taken| Slot(taken.0.saturating_add(1))),
            });
            base = Scope::At(self.binders.len().saturating_sub(1));
        }
        (base, sources)
    }
}

/// The index `counter` stands at, advancing it past.
///
/// # Specification
/// trivial.
fn next(counter: &mut Index) -> Index
{
    let index = *counter;
    *counter = Index(counter.0.saturating_add(1));
    index
}

/// What a closure body names outside its own binders, as indices counted where
/// the closure is created, per index space a capture copies from: no covariable
/// is captured.
#[derive(Debug, Default)]
struct Captured
{
    /// The intuitionistic producer variables.
    producers: BTreeSet<u32>,
    /// The linear variables.
    linears: BTreeSet<u32>,
}

/// The producer binders a closure body's own entry opens, which its captures
/// lie past.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Crossed
{
    /// The producer binders.
    producers: u32,
}

impl Crossed
{
    /// None: a producer's support already lies past its own binders, and a
    /// fold's empty branch opens only a covariable.
    const NONE: Self = Self { producers: 0 };
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
    /// Run a match's arm or branch, by position, the scrutinee in hand.
    Matched(ConsumerId, NodeCount, Scope),
    /// Enter a node counted where its parent is lowered in place.
    Entered(NodeAddress, Scope),
    /// Select from the value in hand by a selection consumer whose
    /// continuation is loaded, and deliver the field to it.
    Selected(ConsumerId, Scope),
    /// A frame's block binding the value in hand and a covariable that falls
    /// through: a reified stack's bind frame.
    Bound(CommandId, Scope),
    /// A handler's frame, popped with the subject's answer in hand: the
    /// handler gives up what it kept for its clauses and its capability, and
    /// its return clause runs as a bound frame's block does.
    Returned(CommandId, Scope),
    /// An operation clause, entered by the host with the captured stack in
    /// hand and the payload in its slot.
    Clause(CommandId, Scope),
    /// An access's frame, popped with the body's answer in hand: the view's
    /// slot, the unwind's label, the access command and its scope.
    Ended(Slot, Label, CommandId, Scope),
    /// Run the suspended capture in hand against the consumer its cut
    /// delivers it to: the consumer loaded, the capture entered.
    Capture(ConsumerId, Scope),
    /// Read a constant not yet unfolded: unfold it, or stick as cyclic when
    /// it is unfolding.
    Unfold(Unfolding),
    /// A copattern object's dispatch: an arm test per arm, each entering the
    /// arm's body, queued in the scope the object was created in.
    Dispatch(ProducerId, Scope),
    /// Bind a label to the next instruction.
    Bind(Label),
    /// Append one one-way instruction.
    Emit(StencilId, Operand, Operand),
    /// Append one two-way instruction of no operands, continuing at the label
    /// on a match.
    Branch(StencilId, Label),
}

/// A constant's slow read at one site.
#[derive(Clone, Copy, Debug)]
struct Unfolding
{
    /// The constant.
    constant: ConstantIndex,
    /// Its word in the run's constant table.
    word: Immediate,
    /// Where the read continues with the value in hand.
    resume: Label,
    /// The entry of the constant's unfolding.
    entry: Label,
}

/// How a closure's entry binds, and what it runs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Entry
{
    /// An application arm: its argument, then its return covariable.
    Apply(CommandId),
    /// A thunk, a force or projection arm, or a suspended capture: its return
    /// covariable.
    Force(CommandId),
    /// A fixpoint: itself, then its return covariable.
    Fixpoint(CommandId),
    /// A constant's unfolding: its definition evaluated into its word, then
    /// returned to the frame on top.
    Unfold(ProducerId, Immediate),
}

/// A closure body awaiting its own window.
#[derive(Clone, Copy, Debug)]
struct Body
{
    /// Its entry's label.
    label: Label,
    /// How the entry binds, and what it runs.
    entry: Entry,
    /// The scope the closure was created in.
    scope: Scope,
}

/// A closure the function creates: what moves a closure in the run's
/// answer into the caller's store.
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
    /// The slots of the producer binders the closure captures where it is
    /// created — the bindings its producer's support selects — innermost
    /// first: the captures its environment binds.
    pub captures: Vec<Slot>,
}

/// A fold's cell closure: it lives only in the frame that applies it, so no
/// site records it, and it owns one reference of each producer it captures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cell
{
    /// The entry's label: the closure's code word is this label's address.
    pub label: Label,
    /// The closure's capture positions of the producers it owns.
    pub captures: Vec<Slot>,
}

/// A bind frame a reified stack holds: what moves a stack in the run's
/// answer into the caller's store.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bound
{
    /// The label the frame resumes at: its code word is this label's
    /// address.
    pub label: Label,
    /// The command the frame runs, binding one producer variable and one
    /// covariable.
    pub body: CommandId,
    /// The slots of the producer binders the body captures where the stack
    /// is reified — the bindings its support selects past the frame's own
    /// value — innermost first: the captures the body's environment binds.
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
        /// The command, which a run no handler answers is stuck at.
        at: CommandId,
    },
    /// Capture to the nearest reset; answers the stack.
    Shift(CommandId),
    /// Push a stack's frames back, each window copied afresh.
    Replay(CommandId),
    /// End a stack without resuming it: push one frame per access it
    /// captured, innermost on top, each entering that access's unwind in the
    /// window its frame held; answers the unit.
    Abandon(CommandId),
    /// Hold the argument in a fresh cell; answers the cell.
    Hold,
    /// Lend a held cell's value through a fresh view; answers the view.
    Access,
    /// Lend the element of a held cell's list at an index through a fresh
    /// view, which writes back at the index; answers the view.
    AccessAt(CommandId),
    /// Read the element of a held cell's list at an index into a fresh cell;
    /// answers the cell.
    Element(CommandId),
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
        /// The access, which a body answering with its view unended is stuck
        /// at.
        at: CommandId,
    },
    /// Build a reified stack in the window in reach: its frames innermost
    /// first, each application's argument among the call's arguments in
    /// order.
    Reify(Vec<Reified>),
    /// Decompose a dialogue: answers its web, a head the run's table joins.
    Decompose,
    /// Run a migration's body at its world: a run of its own, on a thread and
    /// over a store of its own, closed over the captures the argument's tuple
    /// holds, innermost first, each crossed in by content; answers the body's
    /// answer crossed back.
    Migrate
    {
        /// The migration, which a run is declined at when its body does not
        /// lower or runs to no value, or a value it takes or answers does not
        /// cross.
        at: CommandId,
        /// The body, a command binding one covariable, which the host lowers
        /// to run closed over its captures when the migration first runs.
        body: CommandId,
    },
    /// Stick at a constant the definitions do not hold.
    Undefined(ConstantIndex),
    /// Stick at a constant whose unfolding needs its own value.
    Cyclic(ConstantIndex),
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
    /// A projection frame, taking the component.
    Project(Component),
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

/// A label a frame resumes at in a window: what a capture copies of the
/// window, and which of the copied values the frame owns.
///
/// While a frame waits, its window holds one owner of each intuitionistic
/// name the block it resumes will consume; the slots holding them, one entry
/// per owner, are the frame's run of the owner table. A capture takes the
/// frame off the region, so those owners pass to the stack with no count
/// changed; each replay copies them out with an owner of its own; the
/// stack's release drops them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Window
{
    /// The label.
    pub label: Label,
    /// The window's slot count.
    pub slots: Slots,
    /// The frame's run of [`Lowered::owners`]; none for a frame that resumes
    /// a block midway, after a constant's unfolding, whose owners are the
    /// rest of the block's and no node's.
    pub owners: Option<OwnerRun>,
}

/// A run of [`Lowered::owners`]: the slots a frame owns while it waits, one
/// entry per owner.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct OwnerRun(pub Range<usize>);

/// A lowered command: the function, its closure sites and the tables its
/// objects and calls name.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lowered
{
    /// The function both tiers run, its adjacent pairs fused.
    pub function: Function,
    /// The fusions that ran the function's adjacent pairs as one, ascending;
    /// [`crate::replay`] re-derives the function from the unfused one by them.
    pub fused: Vec<Fused>,
    /// Every closure site, in creation order.
    pub sites: Vec<Site>,
    /// The entry window's slots holding the captures of a suspended root
    /// ([`lower_suspended`]), innermost first, as the store environment it
    /// runs under binds them; none for a closed command.
    pub captures: Vec<Slot>,
    /// Every fold cell closure the function creates.
    pub cells: Vec<Cell>,
    /// Every bind frame of a reified stack, in creation order.
    pub bounds: Vec<Bound>,
    /// The heads a head object names by its family.
    pub heads: Vec<ConstructorTag>,
    /// The literals a literal constant names by its family.
    pub literals: Vec<Literal>,
    /// The codes a code constant names by its family, in the IL arena's
    /// annotations.
    pub codes: Vec<gandr_core_term::ValueId>,
    /// The host calls a call names by its operand A.
    pub callees: Vec<Callee>,
    /// The handlers the function installs.
    pub handlers: Vec<Handler>,
    /// Each label a frame resumes at in a window, with the window's slot
    /// count and the slots its frame owns: what a capture copies.
    pub windows: Vec<Window>,
    /// The owner table: the slots each window's frame owns, as runs its
    /// [`Window::owners`] names.
    pub owners: Vec<Slot>,
    /// Each access's frame label with its unwind's label: what an abandoned
    /// stack runs for each access it captured.
    pub unwinds: Vec<(Label, Label)>,
    /// The case, selection or fold of each unmatched exit, by the site its
    /// operand names.
    pub unmatched: Vec<ConsumerId>,
    /// The constants the function unfolds, by their word in the run's
    /// constant table.
    pub globals: Vec<ConstantIndex>,
}

/// The most instructions one lowering emits: past it the command declines
/// rather than being copied into a function larger than a region.
const INSTRUCTIONS: usize = 1 << 18;

/// Check that `function` holds no more instructions than one lowering emits.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Form::Oversized`] once `function` holds more than [`INSTRUCTIONS`].
///
/// # Adequacy
/// - hypothesis: L3 — a function of exactly the ceiling is held and one
///   instruction more is refused; a strict, an equal or a reversed comparison
///   changes one answer. No named program reaches the ceiling.
/// - witness: `lower::tests::a_function_holds_up_to_the_instruction_ceiling`
fn hold_size(function: &Function) -> Result<(), Form>
{
    if function.instructions().len() > INSTRUCTIONS {
        return Err(Form::Oversized);
    }
    Ok(())
}

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

/// The immediate operand naming `component` of a lazy product.
///
/// # Specification
/// - ensures: the component's index, unchanged.
/// - fails: [`Form::HeaderWidth`] for an index past an immediate's 32 bits.
/// - executable: none — the conversion is the body's one computation; a
///   predicate would restate it.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L2 — projections of the second and the third component of a
///   lazy product of three answer their own arms on both tiers, where a wrong
///   index would answer another.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
fn component_immediate(component: Component) -> Result<Immediate, Form>
{
    u32::try_from(usize::from(component))
        .map(Immediate::from)
        .map_err(|_overflow| Form::HeaderWidth)
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
    /// The fold cell closures created so far.
    cells: Vec<Cell>,
    /// The reified bind frames so far.
    bounds: Vec<Bound>,
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
    /// The constants unfolded so far, by word, each with its unfolding's
    /// entry.
    globals: Vec<(ConstantIndex, Label)>,
    /// Whether a cut delivering a variable or a constant tests for a
    /// suspended capture first.
    checked: bool,
    /// The heads a head object names, by family.
    heads: Vec<ConstructorTag>,
    /// The literals a literal constant names, by family.
    literals: Vec<Literal>,
    /// The codes a code constant names, by family.
    codes: Vec<gandr_core_term::ValueId>,
    /// The host calls a call names.
    callees: Vec<Callee>,
    /// Each label selection, its table patched once every head is known.
    selections: Vec<(Position, FieldLabel)>,
    /// The handlers installed so far.
    handlers: Vec<Handler>,
    /// The frame labels of the windows already closed, with their slot
    /// counts.
    windows: Vec<Window>,
    /// The frame labels of the current window, its slot count still open,
    /// with their runs of the owner table.
    pending: Vec<(Label, Option<OwnerRun>)>,
    /// The slots each frame owns while it waits, as runs its window names.
    owners: Vec<Slot>,
    /// Each access's frame label with its unwind's label.
    unwinds: Vec<(Label, Label)>,
    /// The consumer of each unmatched exit so far.
    unmatched: Vec<ConsumerId>,
    /// The ownership reading of the root and of each constant it unfolds,
    /// each its own root.
    ownership: Ownership,
    /// The reading's reuse pairs: each match by its consumer, the arm or
    /// branch by position, and the constructor it builds.
    reuses: Vec<(ConsumerId, NodeCount, ProducerId)>,
    /// The reuse tokens waiting for their constructors: the constructor, the
    /// token's binder and its slot.
    tokens: Vec<(ProducerId, Scope, Slot)>,
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

    /// Emit `stencil` over the slot of each producer name `indices` reads in
    /// `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] for a name no slot of `scope` holds.
    fn each_name(
        &mut self,
        stencil: StencilId,
        scope: Scope,
        indices: &[DeBruijnIndex],
    ) -> Result<(), Form>
    {
        for &index in indices {
            let slot = self
                .scopes
                .slot(scope, Binding::Producer, Index(u32::from(index)))?;
            self.emit(stencil, slot.operand(), Operand::Unused);
        }
        Ok(())
    }

    /// Enter `node` in `scope` counted: duplicate each name two of its
    /// children use, then drop each name it ignores that the edge reaching it
    /// gives it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Unbound`] for a counted name no slot of `scope` holds;
    /// [`Form::Unowned`] for a node the ownership reading does not place.
    fn enter(
        &mut self,
        node: NodeAddress,
        scope: Scope,
    ) -> Result<(), Form>
    {
        // reason: the reading is set aside while its names are emitted, which
        // needs the lowering mutably.
        let ownership = core::mem::take(&mut self.ownership);
        let entered = ownership.entry(node).map_or(Err(Form::Unowned), |entry| {
            self.each_name(StencilId::Dup, scope, entry.dups)?;
            self.each_name(StencilId::Drop, scope, entry.drops)
        });
        self.ownership = ownership;
        entered
    }

    /// Allocate a closure over what `producer` names in `scope`, entered by
    /// `entry`, recording its site and the bindings it captures.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field;
    /// [`Form::Dangling`] and [`Form::Unbound`] as [`Self::captured`].
    fn closure(
        &mut self,
        producer: ProducerId,
        scope: Scope,
        entry: Entry,
        flavour: Flavour,
    ) -> Result<(), Form>
    {
        let (base, label) = self.suspend(
            scope,
            NodeAddress::Producer(producer),
            Crossed::NONE,
            entry,
            flavour,
        )?;
        let captures = self.captured(Suspension::Producer(producer), base)?;
        self.sites.push(Site {
            label,
            producer,
            captures,
        });
        Ok(())
    }

    /// The slots of the producer binders `suspension` captures where it is
    /// created, read in `scope`: the bindings its support selects, innermost
    /// first. In a closure body's base scope these are the closure's own
    /// capture positions.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] for a suspension the arena does not hold;
    /// [`Form::Unbound`] for a captured index no producer binder of `scope`
    /// binds to a slot.
    fn captured(
        &self,
        suspension: Suspension,
        scope: Scope,
    ) -> Result<Vec<Slot>, Form>
    {
        let visible = self.scopes.producers(scope);
        let captures = self.arena.captures(suspension).ok_or(Form::Dangling)?;
        captures
            .map(|index| {
                usize::try_from(u32::from(index))
                    .ok()
                    .and_then(|at| visible.get(at))
                    .copied()
                    .flatten()
                    .ok_or(Form::Unbound)
            })
            .collect()
    }

    /// The base of a closure body's scope over what `node` names in `scope`
    /// past the binders `crossed` counts, and the slots its captures copy.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] for a node the arena does not hold.
    fn enclosed(
        &mut self,
        scope: Scope,
        node: NodeAddress,
        crossed: Crossed,
    ) -> Result<(Scope, Vec<Slot>), Form>
    {
        let support = self.arena.node_scope(node).ok_or(Form::Dangling)?;
        let past = |indices: Indices<'_>, crossed: u32| -> BTreeSet<u32> {
            indices
                .map(|index| u32::from(index).saturating_sub(crossed))
                .collect()
        };
        let depth = |count: u32| BinderDepth::from(usize::try_from(count).unwrap_or(usize::MAX));
        let captured = Captured {
            producers: past(
                support
                    .producers()
                    .outside(Zone::Intuitionistic, depth(crossed.producers)),
                crossed.producers,
            ),
            linears: past(support.producers().outside(Zone::Linear, depth(0)), 0),
        };
        Ok(self.scopes.enclose(scope, &captured))
    }

    /// Allocate a closure over what `node` names in `scope` past the binders
    /// `crossed` counts, entered by `entry`, and queue its body over the
    /// captures; answers the body's base scope and label. A closure no site
    /// records never reaches an answer: a fold's cell closure lives only in a
    /// frame.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field;
    /// [`Form::Dangling`] for a node the arena does not hold.
    fn suspend(
        &mut self,
        scope: Scope,
        node: NodeAddress,
        crossed: Crossed,
        entry: Entry,
        flavour: Flavour,
    ) -> Result<(Scope, Label), Form>
    {
        let (base, sources) = self.enclosed(scope, node, crossed)?;
        let label = self.allocate(&sources, flavour)?;
        self.bodies.push(Body {
            label,
            entry,
            scope: base,
        });
        Ok((base, label))
    }

    /// Allocate a closure of `flavour` over the words in `sources`, in order,
    /// whose code is a fresh label, and answer the label: each source is pushed
    /// and the closure pops them.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field.
    fn allocate(
        &mut self,
        sources: &[Slot],
        flavour: Flavour,
    ) -> Result<Label, Form>
    {
        let label = self.function.label();
        let header = Header::new(
            Kind::Closure,
            Tag::from(flavour),
            Arity::try_from(sources.len()).map_err(|_overflow| Form::HeaderWidth)?,
            Family::UNNAMED,
        );
        for &source in sources {
            self.emit(StencilId::Var, source.operand(), Operand::Unused);
            self.emit(StencilId::Push, Operand::Unused, Operand::Unused);
        }
        let (low, _) = header_operands(header);
        self.emit(StencilId::Closure, Operand::Code(label), low);
        Ok(label)
    }

    /// Allocate the copattern object `id` over what it names in `scope`,
    /// recording its site and the bindings it captures; its code is a dispatch
    /// laid out among the current window's blocks, since it reads no slot, and
    /// every arm's body opens over the object's captures.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a capture count past the arity field;
    /// [`Form::Dangling`] and [`Form::Unbound`] as [`Self::captured`].
    fn object(
        &mut self,
        id: ProducerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let (base, sources) = self.enclosed(scope, NodeAddress::Producer(id), Crossed::NONE)?;
        let label = self.allocate(&sources, Flavour::Object)?;
        self.blocks.push((label, Task::Dispatch(id, base)));
        let captures = self.captured(Suspension::Producer(id), base)?;
        self.sites.push(Site {
            label,
            producer: id,
            captures,
        });
        Ok(())
    }

    /// Lay out the copattern object `id`'s dispatch: per arm, in order, a
    /// test of the observed word entering the arm's body, queued in `scope`;
    /// the stuck exit when no arm answers.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] when `id` is no copattern object;
    /// [`Form::HeaderWidth`] never, an observed word being below 2³².
    fn dispatch(
        &mut self,
        id: ProducerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        let Some(&ProducerNode::Cocase { ref arms }) = arena.producer(id)
        else {
            return Err(Form::Dangling);
        };
        for arm in arms {
            let (observed, entry) = match arm.destructor {
                DestructorTag::Apply => (Observed::Apply, Entry::Apply(arm.body)),
                DestructorTag::Force => (Observed::Force, Entry::Force(arm.body)),
                DestructorTag::Project(component) => (
                    Observed::Project(Word::from(usize::from(component))),
                    Entry::Force(arm.body),
                ),
            };
            let word = u32::try_from(usize::from(Word::from(observed)))
                .map_err(|_overflow| Form::HeaderWidth)?;
            let label = self.function.label();
            self.emit_two_way(
                StencilId::Arm,
                Operand::Immediate(Immediate::from(word)),
                Operand::Unused,
                label,
            );
            self.bodies.push(Body {
                label,
                entry,
                scope,
            });
        }
        self.emit(StencilId::Unobserved, Operand::Unused, Operand::Unused);
        Ok(())
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
            | ConstructorTag::Recorded(_)
            | ConstructorTag::Dialogue(_)
            | ConstructorTag::Web(_) => Ok(Header::new(
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
            return Ok(self.function.object(&[header.word(), value]));
        }
        let header = Header::new(
            Kind::Literal,
            Tag::try_from(0_usize).map_err(width)?,
            Arity::try_from(0_usize).map_err(width)?,
            intern(&mut self.literals, literal).family()?,
        );
        Ok(self.function.object(&[header.word()]))
    }

    /// Select by `selector` from the value in hand for the selection
    /// consumer `id`: the field in hand after the emitted instructions, the
    /// unmatched exit when the value holds no such field.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a component past an immediate's width.
    fn select(
        &mut self,
        id: ConsumerId,
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
        self.unmatched(id)?;
        self.function.bind(found);
        Ok(())
    }

    /// Select by `selector` for the selection consumer `id` in `scope`, as
    /// [`Self::select`]; counted, the field in hand gains the owner the
    /// selection hands on, and the record it was handed is given up.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::select`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a component projected from a fresh pair of pairs
    ///   answers that component beside a pair allocated after: a selection that
    ///   skips the field or its owner answers the record or a freed field.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn selected(
        &mut self,
        id: ConsumerId,
        selector: &Selector,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let (held, record) = self.bind(scope, Binding::Temporary);
        self.emit(StencilId::Bind, record.operand(), Operand::Unused);
        self.select(id, selector)?;
        let (_, field) = self.bind(held, Binding::Temporary);
        self.emit(StencilId::Bind, field.operand(), Operand::Unused);
        self.emit(StencilId::Dup, field.operand(), Operand::Unused);
        self.emit(StencilId::Drop, record.operand(), Operand::Unused);
        Ok(())
    }

    /// The unmatched exit of the case, selection or fold `arms`, its site the
    /// next row of the unmatched table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a table past an immediate's width.
    fn unmatched(
        &mut self,
        arms: ConsumerId,
    ) -> Result<(), Form>
    {
        let site = u32::try_from(self.unmatched.len()).map_err(|_overflow| Form::HeaderWidth)?;
        self.unmatched.push(arms);
        self.emit(
            StencilId::Unmatched,
            Operand::Immediate(Immediate::from(site)),
            Operand::Unused,
        );
        Ok(())
    }

    /// Fold the native list in hand by the fold consumer `id`, whose
    /// continuation is loaded, in `scope`.
    ///
    /// Counted, the walk owns the list in hand. Each cell's tail gains an
    /// owner for the next step and each cell closure one of each name it
    /// captures, the head among them, before the cell is given up; at the
    /// empty list the walk gives up the list and the owner of each name the
    /// fold's node handed the cell branch, which every closure now holds one
    /// of its own.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a fold over a list built where it runs, whose cell
    ///   branch pairs each head with a pair bound outside it, answers the list
    ///   it states: a walk that gives a tail or a capture no owner of its own
    ///   reads a freed cell.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
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
        let (walked, list) = self.bind(scope, Binding::Temporary);
        self.function.bind(test);
        self.emit_two_way(StencilId::Match, nil_low, nil_family, empty);
        self.emit_two_way(StencilId::Match, cell_low, cell_family, cell);
        self.unmatched(id)?;
        self.function.bind(cell);
        self.emit(StencilId::Bind, list.operand(), Operand::Unused);
        let (with_head, head) = self.bind(walked, Binding::Producer);
        self.emit(StencilId::Field, head.operand(), Slot(0).operand());
        let (with_tail, tail) = self.bind(with_head, Binding::Temporary);
        self.emit(StencilId::Field, tail.operand(), Slot(1).operand());
        // The cell branch binds the head, the tail's result and a covariable;
        // the head is bound here, the other two by the closure's entry, and
        // the covariable is captured by none.
        let crossed = Crossed { producers: 1 };
        let (base, label) = self.suspend(
            with_head,
            NodeAddress::Command(on_cons),
            crossed,
            Entry::Apply(on_cons),
            Flavour::Apply,
        )?;
        self.emit(StencilId::Dup, tail.operand(), Operand::Unused);
        for capture in self.named(NodeAddress::Command(on_cons), with_head, crossed)? {
            self.emit(StencilId::Dup, capture.operand(), Operand::Unused);
        }
        self.emit(StencilId::Drop, list.operand(), Operand::Unused);
        let captures = self.scopes.producers(base).into_iter().flatten().collect();
        self.cells.push(Cell { label, captures });
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
        self.emit(StencilId::Bind, list.operand(), Operand::Unused);
        self.emit(StencilId::Drop, list.operand(), Operand::Unused);
        let past = Crossed { producers: 2 };
        for capture in self.named(NodeAddress::Command(on_cons), scope, past)? {
            self.emit(StencilId::Drop, capture.operand(), Operand::Unused);
        }
        let (inner, alpha) = self.bind(scope, Binding::Covariable);
        self.emit(StencilId::Mark, alpha.operand(), Operand::Unused);
        self.tasks.push(Task::Command(on_nil, inner));
        Ok(())
    }

    /// A fresh label a frame resumes at in the current window, counted among
    /// the labels a capture copies the window of, its frame owning the run
    /// `owners` of the owner table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer as they state: a frame
    ///   resuming at another frame's label runs another block.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn frame_label(
        &mut self,
        owners: Option<OwnerRun>,
    ) -> Label
    {
        let label = self.function.label();
        self.pending.push((label, owners));
        label
    }

    /// No owners: the run of a frame whose block consumes nothing of its
    /// window.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an access's unwinding frame and a selection's frame
    ///   own nothing, and the programs holding them answer as they state.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn unowned(&self) -> OwnerRun
    {
        let at = self.owners.len();
        OwnerRun(at .. at)
    }

    /// The slot in `scope` of each intuitionistic name `node`'s support
    /// selects past the binders `crossed` counts, once each, in support order.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] for a node the arena does not hold;
    /// [`Form::Unbound`] for a name no slot of `scope` holds.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the fold and the access programs answer as they
    ///   state: a name read off the wrong slot, or not at all, duplicates or
    ///   drops the wrong value.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn named(
        &self,
        node: NodeAddress,
        scope: Scope,
        crossed: Crossed,
    ) -> Result<Vec<Slot>, Form>
    {
        let support = self.arena.node_scope(node).ok_or(Form::Dangling)?;
        let depth = BinderDepth::from(usize::try_from(crossed.producers).unwrap_or(usize::MAX));
        support
            .producers()
            .outside(Zone::Intuitionistic, depth)
            .map(|index| {
                let name = Index(u32::from(index).saturating_sub(crossed.producers));
                self.scopes.slot(scope, Binding::Producer, name)
            })
            .collect()
    }

    /// Record the owners a frame holds while it waits to run `node` in
    /// `scope`, its block opening the binders `crossed` counts: the slot of
    /// each name [`Self::named`] reads, one owner each. Answers their run of
    /// the owner table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::named`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a captured stack resumed twice answers the pair its
    ///   frames return: a frame that owns nothing gives its copy no owner, and
    ///   the second resumption returns a freed pair.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn owners(
        &mut self,
        node: NodeAddress,
        scope: Scope,
        crossed: Crossed,
    ) -> Result<OwnerRun, Form>
    {
        let start = self.owners.len();
        let named = self.named(node, scope, crossed)?;
        self.owners.extend(named);
        Ok(OwnerRun(start .. self.owners.len()))
    }

    /// The slots in `scope` of the names the handler `handle` keeps for its
    /// clauses: each name a clause selects past its payload and its stack,
    /// once however many clauses select it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] when `handle` is no handler; [`Form::Unbound`] for
    /// a name no slot of `scope` holds.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a handler resuming its stack twice answers as it
    ///   states. A handler's frame that keeps none of its clauses' names leaks
    ///   them, which no answer shows: the clause duplicates what it names on
    ///   entry, so only the drops at the handler's return go missing. L3 — a
    ///   handler whose clause alone names a pair bound outside it owns the
    ///   pair's slot in its frame and drops it at its return.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_handler_keeps_what_its_clauses_name_past_their_binders`
    fn kept(
        &self,
        handle: CommandId,
        scope: Scope,
    ) -> Result<BTreeSet<Slot>, Form>
    {
        let arena = self.arena;
        let Some(&CommandNode::Handle { ref clauses, .. }) = arena.command(handle)
        else {
            return Err(Form::Dangling);
        };
        let mut kept = BTreeSet::new();
        for clause in clauses.iter() {
            let support = arena
                .node_scope(NodeAddress::Command(clause.body))
                .ok_or(Form::Dangling)?;
            for index in support
                .producers()
                .outside(Zone::Intuitionistic, BinderDepth::from(2_usize))
            {
                let name = Index(u32::from(index).saturating_sub(2));
                let _first = kept.insert(self.scopes.slot(scope, Binding::Producer, name)?);
            }
        }
        Ok(kept)
    }

    /// Record the owners the frame of the handler `handle` holds while it
    /// waits, in `scope`: each name its return clause `on_return` selects past
    /// the value it binds, each name the handler keeps for its clauses, and
    /// the capability in the slot `capability` when it introduces one. Answers
    /// their run of the owner table.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::owners`] and [`Self::kept`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a handler whose return clause answers a pair bound
    ///   outside it, and whose clause resumes its stack twice, answers that
    ///   pair: a handler frame that owns nothing is copied without an owner of
    ///   it, and the pair is freed.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn handled(
        &mut self,
        handle: CommandId,
        on_return: CommandId,
        scope: Scope,
        capability: Option<Slot>,
    ) -> Result<OwnerRun, Form>
    {
        let returned = self.owners(NodeAddress::Command(on_return), scope, Crossed {
            producers: 1,
        })?;
        let kept = self.kept(handle, scope)?;
        self.owners.extend(kept);
        self.owners.extend(capability);
        Ok(OwnerRun(returned.0.start .. self.owners.len()))
    }

    /// The word of `constant`, defined as `definition`, in the run's constant
    /// table, and its unfolding's entry; the first use queues the unfolding.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::HeaderWidth`] for a constant table past an immediate's width.
    fn global(
        &mut self,
        constant: ConstantIndex,
        definition: ProducerId,
    ) -> Result<(Immediate, Label), Form>
    {
        let held = self
            .globals
            .iter()
            .position(|&(unfolded, _)| unfolded == constant);
        let position = held.unwrap_or(self.globals.len());
        let word = Immediate::from(u32::try_from(position).map_err(|_overflow| Form::HeaderWidth)?);
        if let Some(&(_, entry)) = self.globals.get(position) {
            return Ok((word, entry));
        }
        let entry = self.function.label();
        self.globals.push((constant, entry));
        self.bodies.push(Body {
            label: entry,
            entry: Entry::Unfold(definition, word),
            scope: Scope::Empty,
        });
        Ok((word, entry))
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs that handle, delimit, capture,
    ///   resume and abandon answer as they state on both tiers.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn control(
        &mut self,
        id: CommandId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        self.enter(NodeAddress::Command(id), scope)?;
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
                        at: id,
                    },
                    count,
                )?;
                // A handler of the run continues at its clause; the host's
                // reply returns here, to the loaded continuation.
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
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
                let (held, capability) = match introduces {
                    Introduces::Nothing => (scope, None),
                    Introduces::Capability => {
                        let (held, slot) = self.bind(scope, Binding::Producer);
                        (held, Some(slot))
                    },
                };
                let owners = self.handled(id, on_return, scope, capability)?;
                let returned = self.frame_label(Some(owners));
                self.blocks.push((returned, Task::Returned(id, scope)));
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
                    let unit = self.function.object(&[unit.word()]);
                    let (low, family) = header_operands(Header::new(
                        Kind::Capability,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(1_usize).map_err(width)?,
                        Family::UNNAMED,
                    ));
                    // The handler's frame owns the capability too, so its
                    // address names no other object while the frame waits.
                    self.tasks
                        .push(Task::Emit(StencilId::Dup, slot.operand(), Operand::Unused));
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
                let call = self.call(&Callee::Shift(id), Immediate::from(0_u32))?;
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
                let call = self.call(&Callee::Replay(id), Immediate::from(1_u32))?;
                let (inner, _) = self.bind(scope, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(stack, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            // An abandoned stack's frames are never resumed. Its continuation
            // is loaded first; above it the abandonment pushes a frame per
            // access the stack captured, and the unit returned to the top runs
            // each access's unwind in turn, innermost first, before the
            // continuation receives it.
            CommandNode::Abandon {
                stack,
                continuation,
            } => {
                let call = self.call(&Callee::Abandon(id), Immediate::from(1_u32))?;
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(stack, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            CommandNode::Memory {
                ref form,
                continuation,
            } => self.memory(id, form, continuation, scope)?,
            CommandNode::World {
                ref form,
                continuation,
            } => self.world(id, form, continuation, scope)?,
        }
        Ok(())
    }

    /// Lower the memory form `form` of the command `id` with its continuation
    /// in `scope`. A linear binder's slot holds a cell: a hold's holds the
    /// value, an exclusive access's view holds the value lent, how the view
    /// ended and the held cell it writes back to, and, at a place, the index
    /// it writes back at. A shared access's view of the whole value is the
    /// held cell itself: the held value is frozen for the body, nothing ends
    /// the view, and the body answers to the continuation directly. A shared
    /// view at a place is a fresh cell holding the element. A consume answers
    /// the value its held cell holds, read as a read of the slot reads it; the
    /// checker has spent the slot, so nothing reads the cell after it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs that hold, access, write back and
    ///   abandon a view answer as they state on both tiers.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn memory(
        &mut self,
        id: CommandId,
        form: &MemoryForm<ProducerId, CommandId>,
        continuation: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *form {
            MemoryForm::Hold { value, body, .. } => {
                let call = self.call(&Callee::Hold, Immediate::from(1_u32))?;
                let (held, cell) = self.bind(scope, Binding::Linear);
                // reason: the hold pushes no frame, so its body falls through
                // to the loaded continuation, the body's return when that is
                // where the continuation delivers.
                let falls = match self.returns_through(continuation, scope)? {
                    Some(_) => Binding::Returning,
                    None => Binding::FallThrough,
                };
                let (inner, _) = self.bind(held, falls);
                self.tasks.push(Task::Command(body, inner));
                self.tasks
                    .push(Task::Emit(StencilId::Bind, cell.operand(), Operand::Unused));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(value, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            MemoryForm::Access {
                mode: AccessMode::Shared,
                held,
                place,
                body,
            } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(held)))?;
                let (viewed, view) = self.bind(scope, Binding::Linear);
                let (inner, _) = self.bind(viewed, Binding::FallThrough);
                self.tasks.push(Task::Command(body, inner));
                self.tasks
                    .push(Task::Emit(StencilId::Bind, view.operand(), Operand::Unused));
                if let Place::At { index } = place {
                    let call = self.call(&Callee::Element(id), Immediate::from(2_u32))?;
                    self.tasks.push(call);
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Producer(index, scope));
                    self.tasks.push(PUSH);
                }
                self.tasks
                    .push(Task::Emit(StencilId::Var, cell.operand(), Operand::Unused));
                self.tasks.push(Task::Load(continuation, scope));
            },
            MemoryForm::Access {
                mode: AccessMode::Exclusive { unwind },
                held,
                place,
                body,
            } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(held)))?;
                let call = match place {
                    Place::Whole => self.call(&Callee::Access, Immediate::from(1_u32))?,
                    Place::At { .. } => self.call(&Callee::AccessAt(id), Immediate::from(2_u32))?,
                };
                let (viewed, view) = self.bind(scope, Binding::Linear);
                let (inner, _) = self.bind(viewed, Binding::FallThrough);
                // The access's frame owns what its unwind selects while the
                // body runs: an aborted view's unwind consumes it, a resumed
                // one's end gives it up.
                let owners = self.owners(NodeAddress::Command(unwind), scope, Crossed::NONE)?;
                let ended = self.frame_label(Some(owners));
                let unwinding = self.frame_label(Some(self.unowned()));
                self.unwinds.push((ended, unwinding));
                let (unwound, _) = self.bind(scope, Binding::FallThrough);
                self.blocks
                    .push((ended, Task::Ended(view, unwinding, id, scope)));
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
                if let Place::At { index } = place {
                    self.tasks.push(Task::Producer(index, scope));
                    self.tasks.push(PUSH);
                }
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
            MemoryForm::Consume { held } => {
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(held)))?;
                let (_, read) = self.bind(scope, Binding::Temporary);
                self.tasks.push(Task::Deliver(continuation, scope));
                self.tasks
                    .push(Task::Emit(StencilId::Var, read.operand(), Operand::Unused));
                self.tasks.push(Task::Emit(
                    StencilId::Field,
                    read.operand(),
                    Slot(0).operand(),
                ));
                self.tasks
                    .push(Task::Emit(StencilId::Var, cell.operand(), Operand::Unused));
            },
        }
        Ok(())
    }

    /// Lower the world form `form` of the command `id` with its continuation
    /// in `scope`. In one process a handle is its content: a hold delivers its
    /// value, and a leta binds the handle's value as a hold binds its cell. A
    /// migration's body runs at its world, lowered apart by the host to run
    /// closed; here its captures are gathered, innermost first, into the tuple
    /// the host call takes, each capture's owner passing to the tuple as a
    /// closure's captures pass to the closure.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a value held, opened by a leta and answered twice
    ///   reads back alike in place and inside a migration on both tiers; a leta
    ///   bound to other than its handle, or a capture left out of the tuple,
    ///   changes the answer or declines the run.
    /// - witness: `tests::world::a_migration_crosses_its_capture_in_and_its_answer_back`
    fn world(
        &mut self,
        id: CommandId,
        form: &WorldForm<ProducerId, CommandId>,
        continuation: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        match *form {
            WorldForm::Hold { value } => {
                self.tasks.push(Task::Deliver(continuation, scope));
                self.tasks.push(Task::Producer(value, scope));
            },
            WorldForm::Leta { value, body } => {
                let (bound, slot) = self.bind(scope, Binding::Producer);
                // reason: as a hold's, a leta's body falls through to the loaded
                // continuation, the body's return when that is where the
                // continuation delivers.
                let falls = match self.returns_through(continuation, scope)? {
                    Some(_) => Binding::Returning,
                    None => Binding::FallThrough,
                };
                let (inner, _) = self.bind(bound, falls);
                self.tasks.push(Task::Command(body, inner));
                self.tasks
                    .push(Task::Emit(StencilId::Bind, slot.operand(), Operand::Unused));
                self.tasks.push(Task::Producer(value, scope));
                self.tasks.push(Task::Load(continuation, scope));
            },
            WorldForm::Migrate { body, .. } => {
                let captures = self.captured(Suspension::Thunk(body), scope)?;
                let call = self.call(&Callee::Migrate { at: id, body }, Immediate::from(1_u32))?;
                let header =
                    self.header(&ConstructorTag::Tuple(ProducerArity::from(captures.len())))?;
                let (low, family) = header_operands(header);
                let gather = match captures.len() {
                    0 => {
                        let at = self.function.object(&[header.word()]);
                        Task::Emit(StencilId::Const, Operand::Data(at), Operand::Unused)
                    },
                    1 => Task::Emit(StencilId::Ctor1, low, family),
                    2 => Task::Emit(StencilId::Ctor2, low, family),
                    3 => Task::Emit(StencilId::Ctor3, low, family),
                    _ => Task::Emit(StencilId::CtorN, low, family),
                };
                self.tasks.push(Task::Deliver(continuation, scope));
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(gather);
                for &capture in captures.iter().rev() {
                    self.tasks.push(PUSH);
                    self.tasks.push(Task::Emit(
                        StencilId::Var,
                        capture.operand(),
                        Operand::Unused,
                    ));
                }
            },
        }
        Ok(())
    }

    /// Open a closure body: bind its label, emit its entry, and queue what it
    /// runs — a command, or a constant's definition evaluated into its word
    /// and returned to the frame its read pushed; a computed definition's `μ`
    /// runs its command against a frame of its own, which sets the word with
    /// the answer. Answers the entry's instruction, whose window operand is
    /// written once the body is lowered. Counted, the window's captures each
    /// gain an owner and the closure entered is given up; a fixpoint's own
    /// binder keeps it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a thunk forced twice, whose first answer is dropped
    ///   before a fresh pair is allocated, answers its capture: an entry that
    ///   took its captures without an owner of its own frees the capture.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `tests::agreement::a_computed_constant_unfolds_once_to_its_answer`
    fn open(
        &mut self,
        body: Body,
    ) -> Position
    {
        self.function.bind(body.label);
        let depth = self.scopes.depth(body.scope);
        self.window = depth.0;
        let (stencil, bindings): (StencilId, &[Binding]) = match body.entry {
            Entry::Apply(_) => (StencilId::EnterApply, &[
                Binding::Producer,
                Binding::Returns,
                Binding::Temporary,
            ]),
            Entry::Force(_) | Entry::Unfold(..) => (StencilId::EnterForce, &[
                Binding::Returns,
                Binding::Temporary,
            ]),
            Entry::Fixpoint(_) => (StencilId::EnterFix, &[Binding::Producer, Binding::Returns]),
        };
        let at = self.emit(stencil, Slot(0).operand(), depth.operand());
        let mut scope = body.scope;
        let mut closure = None;
        for &binding in bindings {
            let (inner, slot) = self.bind(scope, binding);
            scope = inner;
            if binding == Binding::Temporary {
                closure = Some(slot);
            }
        }
        if !matches!(body.entry, Entry::Unfold(..)) {
            for capture in self.scopes.producers(body.scope).into_iter().flatten() {
                self.emit(StencilId::Dup, capture.operand(), Operand::Unused);
            }
            if let Some(closure) = closure {
                self.emit(StencilId::Drop, closure.operand(), Operand::Unused);
            }
        }
        match body.entry {
            Entry::Apply(command) | Entry::Force(command) | Entry::Fixpoint(command) => {
                self.tasks.push(Task::Command(command, scope));
            },
            Entry::Unfold(definition, word) => {
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
                self.tasks.push(Task::Emit(
                    StencilId::SetGlobal,
                    Operand::Immediate(word),
                    Operand::Unused,
                ));
                if let Some(&ProducerNode::Mu { body: computed }) = self.arena.producer(definition)
                {
                    let owners = self.unowned();
                    let resume = self.frame_label(Some(owners));
                    let (inner, alpha) = self.bind(scope, Binding::Covariable);
                    self.emit(StencilId::Pushk, Operand::Code(resume), alpha.operand());
                    self.tasks.push(Task::Bind(resume));
                    self.tasks.push(Task::Command(computed, inner));
                }
                else {
                    self.tasks.push(Task::Producer(definition, scope));
                }
            },
        }
        at
    }

    /// Open `body`, a command binding one covariable, as the function's root:
    /// the producer bindings its support selects in the entry window's first
    /// slots, as a closure body's base scope holds its captures, and its
    /// covariable aliasing the halt frame's mark, as a `μ` cut against `★`
    /// binds one. Answers the captures' slots, innermost first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] for a body the arena does not hold.
    fn suspended(
        &mut self,
        body: CommandId,
    ) -> Result<Vec<Slot>, Form>
    {
        let node = NodeAddress::Command(body);
        let support = self.arena.node_scope(node).ok_or(Form::Dangling)?;
        let binders = support
            .producers()
            .outside(Zone::Intuitionistic, BinderDepth::from(0_usize))
            .map(|index| u32::from(index).saturating_add(1))
            .max()
            .unwrap_or_default();
        // The scope the body would be created in: one producer binder per
        // index up to the outermost it names, which `enclose` keeps where the
        // body captures it.
        let mut creator = Scope::Empty;
        for _ in 0 .. binders {
            creator = self.scopes.bind(creator, Binding::Producer).0;
        }
        let (base, _) = self.enclosed(creator, node, Crossed::NONE)?;
        let captures = self.captured(Suspension::Thunk(body), base)?;
        let (inner, alpha) = self.bind(base, Binding::Covariable);
        self.emit(StencilId::AliasTop, alpha.operand(), Operand::Unused);
        self.tasks.push(Task::Command(body, inner));
        Ok(captures)
    }

    /// Run one task.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The [`Form`] of the first node outside the lowered fragment.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program lowers and answers as it states
    ///   on both tiers: a step that emits nothing answers nothing.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), Form>
    {
        hold_size(&self.function)?;
        match task {
            Task::Emit(stencil, a, b) => {
                self.emit(stencil, a, b);
                Ok(())
            },
            Task::Branch(stencil, alt) => {
                self.emit_two_way(stencil, Operand::Unused, Operand::Unused, alt);
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
            Task::Matched(id, position, scope) => self.matched(id, position, scope),
            Task::Entered(node, scope) => self.enter(node, scope),
            Task::Selected(id, scope) => {
                let ConsumerNode::Select { ref selector, .. } =
                    *self.arena.consumer(id).ok_or(Form::Dangling)?
                else {
                    return Err(Form::Dangling);
                };
                self.selected(id, selector, scope)?;
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
            Task::Returned(handle, scope) => {
                let &CommandNode::Handle {
                    introduces,
                    on_return,
                    ..
                } = self.arena.command(handle).ok_or(Form::Dangling)?
                else {
                    return Err(Form::Dangling);
                };
                for kept in self.kept(handle, scope)? {
                    self.emit(StencilId::Drop, kept.operand(), Operand::Unused);
                }
                if matches!(introduces, Introduces::Capability) {
                    // Dropped before the answer is bound over its slot.
                    let capability = self.scopes.depth(scope);
                    self.emit(StencilId::Drop, capability.operand(), Operand::Unused);
                }
                self.tasks.push(Task::Bound(on_return, scope));
                Ok(())
            },
            Task::Clause(body, scope) => {
                // The host wrote the payload's slot before entering.
                let (with_payload, _) = self.bind(scope, Binding::Producer);
                let (with_stack, stack) = self.bind(with_payload, Binding::Producer);
                self.emit(StencilId::Bind, stack.operand(), Operand::Unused);
                let (inner, _) = self.bind(with_stack, Binding::FallThrough);
                // The handler keeps the clause's captures, since it runs
                // once per perform: each run duplicates what it names
                // before a binder it ignores is dropped, the stack among
                // them, which may hold the handler's last owners.
                let ownership = core::mem::take(&mut self.ownership);
                let entered = ownership
                    .entry(NodeAddress::Command(body))
                    .map_or(Err(Form::Unowned), |entry| {
                        self.each_name(StencilId::Dup, inner, entry.entered)
                    });
                self.ownership = ownership;
                entered?;
                self.tasks.push(Task::Command(body, inner));
                Ok(())
            },
            Task::Ended(view, unwind, at, scope) => {
                let call = self.call(&Callee::Ended { unwind, at }, Immediate::from(2_u32))?;
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
                // Resumed, the unwind never runs: its names are given up before
                // the frame pops.
                let Some(&CommandNode::Memory {
                    form:
                        MemoryForm::Access {
                            mode: AccessMode::Exclusive { unwind: body },
                            ..
                        },
                    ..
                }) = self.arena.command(at)
                else {
                    return Err(Form::Dangling);
                };
                for name in self.named(NodeAddress::Command(body), scope, Crossed::NONE)? {
                    self.tasks
                        .push(Task::Emit(StencilId::Drop, name.operand(), Operand::Unused));
                }
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks
                    .push(Task::Emit(StencilId::Var, view.operand(), Operand::Unused));
                self.tasks.push(PUSH);
                Ok(())
            },
            Task::Capture(consumer, scope) => {
                // Loading the consumer may evaluate an argument into hand.
                let (inner, held) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Bind, held.operand(), Operand::Unused);
                self.tasks.push(Task::Emit(
                    StencilId::RunCapture,
                    Operand::Unused,
                    Operand::Unused,
                ));
                self.tasks
                    .push(Task::Emit(StencilId::Var, held.operand(), Operand::Unused));
                self.tasks.push(Task::Load(consumer, inner));
                Ok(())
            },
            Task::Unfold(Unfolding {
                constant,
                word,
                resume,
                entry,
            }) => {
                self.emit(StencilId::Pushf, Operand::Code(resume), Operand::Unused);
                let cyclic = self.function.label();
                self.emit_two_way(
                    StencilId::Unfold,
                    Operand::Immediate(word),
                    Operand::Unused,
                    cyclic,
                );
                self.emit_two_way(StencilId::Jump, Operand::Unused, Operand::Unused, entry);
                self.function.bind(cyclic);
                // The call refuses; the pop only ends the block.
                let call = self.call(&Callee::Cyclic(constant), Immediate::from(0_u32))?;
                self.tasks
                    .push(Task::Emit(StencilId::Pop, Operand::Unused, Operand::Unused));
                self.tasks.push(call);
                Ok(())
            },
            Task::Dispatch(id, scope) => self.dispatch(id, scope),
        }
    }

    /// Lower the command `id` in `scope`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer as they state: a command
    ///   lowered to nothing runs none of its cut.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
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
            CommandNode::Memory { .. }
            | CommandNode::World { .. }
            | CommandNode::Perform { .. }
            | CommandNode::Handle { .. }
            | CommandNode::Resume { .. }
            | CommandNode::Abandon { .. }
            | CommandNode::Reset { .. }
            | CommandNode::Shift { .. } => return self.control(id, scope),
        };
        self.enter(NodeAddress::Command(id), scope)?;
        let target = arena.consumer(consumer).ok_or(Form::Dangling)?;
        let binds = matches!(*target, ConsumerNode::MuTilde { .. });
        let body = match *arena.producer(producer).ok_or(Form::Dangling)? {
            // The by-name side of a negative cut against a binder suspends the
            // capture and binds it; every other cut runs it.
            ProducerNode::Mu { body } if !(binds && polarity == Polarity::Negative) => body,
            ProducerNode::Variable { .. } | ProducerNode::Constant(_) if self.checked && !binds => {
                // A suspended capture delivered to anything but a binder runs
                // against it.
                let run = self.function.label();
                self.blocks.push((run, Task::Capture(consumer, scope)));
                self.tasks.push(Task::Deliver(consumer, scope));
                self.tasks.push(Task::Branch(StencilId::Captured, run));
                self.tasks.push(Task::Producer(producer, scope));
                return Ok(());
            },
            ProducerNode::Mu { .. }
            | ProducerNode::Variable { .. }
            | ProducerNode::Constant(_)
            | ProducerNode::Literal(_)
            | ProducerNode::Code(_)
            | ProducerNode::Constructor { .. }
            | ProducerNode::Thunk { .. }
            | ProducerNode::Fixpoint { .. }
            | ProducerNode::Cocase { .. }
            | ProducerNode::Closure { .. }
            | ProducerNode::Primitive { .. }
            | ProducerNode::Decompose(_)
            | ProducerNode::Reify(_) => {
                self.tasks.push(Task::Deliver(consumer, scope));
                self.tasks.push(Task::Producer(producer, scope));
                return Ok(());
            },
        };
        self.enter(NodeAddress::Producer(producer), scope)?;
        // reason: a `μ` run against the body's return aliases its mark, and
        // delivering to it returns as delivering to the return does.
        let kind = match *target {
            ConsumerNode::Covariable(index) => {
                match self.scopes.delivery(scope, Index(u32::from(index)))? {
                    Delivery::Return(_) => Binding::Returns,
                    Delivery::Mark(_) | Delivery::FallThrough | Delivery::Returning => {
                        Binding::Covariable
                    },
                }
            },
            ConsumerNode::Top
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::DataCase { .. }
            | ConsumerNode::Destructor { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. } => Binding::Covariable,
        };
        let (inner, alpha) = self.bind(scope, kind);
        match *target {
            ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } => {
                let owners = self.owners(NodeAddress::Consumer(consumer), scope, Crossed::NONE)?;
                let resume = self.frame_label(Some(owners));
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
                    let falls = match self.scopes.delivery(scope, Index(u32::from(index)))? {
                        Delivery::Returning => Binding::Returning,
                        Delivery::Return(_) | Delivery::Mark(_) | Delivery::FallThrough => {
                            Binding::FallThrough
                        },
                    };
                    let (through, _) = self.bind(scope, falls);
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program evaluates its producers to the
    ///   answers it states on both tiers.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn producer(
        &mut self,
        id: ProducerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        self.enter(NodeAddress::Producer(id), scope)?;
        match *self.arena.producer(id).ok_or(Form::Dangling)? {
            ProducerNode::Literal(ref literal) => {
                let at = self.literal(literal)?;
                self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
            },
            ProducerNode::Code(code) => {
                let width = |_overflow| Form::HeaderWidth;
                let header = Header::new(
                    Kind::Code,
                    Tag::try_from(0_usize).map_err(width)?,
                    Arity::try_from(0_usize).map_err(width)?,
                    intern(&mut self.codes, &code).family()?,
                );
                let at = self.function.object(&[header.word()]);
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
                // The cell keeps its owner; the read takes one of its own.
                let cell = self
                    .scopes
                    .slot(scope, Binding::Linear, Index(u32::from(index)))?;
                let (_, read) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Var, cell.operand(), Operand::Unused);
                self.emit(StencilId::Field, read.operand(), Slot(0).operand());
                self.emit(StencilId::Dup, read.operand(), Operand::Unused);
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
                        let at = self.function.object(&[header.word()]);
                        self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
                        return Ok(());
                    },
                    1 => StencilId::Ctor1,
                    2 => StencilId::Ctor2,
                    3 => StencilId::Ctor3,
                    _ => StencilId::CtorN,
                };
                let (low, family) = header_operands(header);
                match self.token(id, scope) {
                    // The token goes in hand past the last field's push.
                    Some(token) => {
                        self.tasks
                            .push(Task::Emit(StencilId::CtorInto, low, family));
                        self.tasks.push(Task::Emit(
                            StencilId::Var,
                            token.operand(),
                            Operand::Unused,
                        ));
                    },
                    None => self.tasks.push(Task::Emit(stencil, low, family)),
                }
                for &field in producers.iter().rev() {
                    self.tasks.push(Task::Emit(
                        StencilId::Push,
                        Operand::Unused,
                        Operand::Unused,
                    ));
                    self.tasks.push(Task::Producer(field, scope));
                }
            },
            ProducerNode::Mu { body } => {
                self.closure(id, scope, Entry::Force(body), Flavour::Capture)?;
            },
            ProducerNode::Thunk { body } => {
                self.closure(id, scope, Entry::Force(body), Flavour::Thunk)?;
            },
            ProducerNode::Fixpoint { body, .. } => {
                self.closure(id, scope, Entry::Fixpoint(body), Flavour::Fixpoint)?;
            },
            ProducerNode::Cocase { ref arms } => match **arms {
                [arm] if arm.destructor == DestructorTag::Apply => {
                    self.closure(id, scope, Entry::Apply(arm.body), Flavour::Apply)?;
                },
                [arm] if arm.destructor == DestructorTag::Force => {
                    self.closure(id, scope, Entry::Force(arm.body), Flavour::Force)?;
                },
                _ => self.object(id, scope)?,
            },
            ProducerNode::Closure {
                ref environment,
                code,
            } => {
                // Each value is evaluated where the closure stands, in a scope
                // whose temporaries lie past the slots the values take, and
                // bound to its slot; the code then closes over those slots as
                // over any binder's.
                let mut evaluated = scope;
                let mut bound = scope;
                let mut slots = Vec::with_capacity(environment.len());
                for _ in environment {
                    (evaluated, _) = self.bind(evaluated, Binding::Temporary);
                    let slot;
                    (bound, slot) = self.bind(bound, Binding::Producer);
                    slots.push(slot);
                }
                self.tasks.push(Task::Producer(code, bound));
                for (&value, slot) in environment.iter().zip(slots).rev() {
                    self.tasks
                        .push(Task::Emit(StencilId::Bind, slot.operand(), Operand::Unused));
                    self.tasks.push(Task::Producer(value, evaluated));
                }
            },
            ProducerNode::Constant(constant) => match self.definitions.get(constant) {
                Some(Definition::Transparent(definition)) => {
                    let (word, entry) = self.global(constant, definition)?;
                    let slow = self.function.label();
                    let resume = self.frame_label(None);
                    self.emit_two_way(
                        StencilId::Global,
                        Operand::Immediate(word),
                        Operand::Unused,
                        slow,
                    );
                    self.function.bind(resume);
                    self.blocks.push((
                        slow,
                        Task::Unfold(Unfolding {
                            constant,
                            word,
                            resume,
                            entry,
                        }),
                    ));
                },
                Some(Definition::Opaque) => {
                    let width = |_overflow| Form::HeaderWidth;
                    let header = Header::new(
                        Kind::Opaque,
                        Tag::try_from(0_usize).map_err(width)?,
                        Arity::try_from(0_usize).map_err(width)?,
                        Family::try_from(usize::from(constant)).map_err(width)?,
                    );
                    let at = self.function.object(&[header.word()]);
                    self.emit(StencilId::Const, Operand::Data(at), Operand::Unused);
                },
                None => {
                    let call = self.call(&Callee::Undefined(constant), Immediate::from(0_u32))?;
                    self.tasks.push(call);
                },
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
            ProducerNode::Decompose(dialogue) => {
                let call = self.call(&Callee::Decompose, Immediate::from(1_u32))?;
                self.tasks.push(call);
                self.tasks.push(PUSH);
                self.tasks.push(Task::Producer(dialogue, scope));
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
                            let captures = self.captured(Suspension::Bind(body), scope)?;
                            let owners =
                                self.owners(NodeAddress::Command(body), scope, Crossed {
                                    producers: 1,
                                })?;
                            let label = self.frame_label(Some(owners));
                            self.blocks.push((label, Task::Bound(body, scope)));
                            self.bounds.push(Bound {
                                label,
                                body,
                                captures,
                            });
                            shape.push(Reified::Bind(label));
                        },
                        StackFrame::Project(side) => shape.push(Reified::Project(side)),
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every named program delivers its values to the
    ///   consumers that answer as it states on both tiers.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn deliver(
        &mut self,
        id: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        self.enter(NodeAddress::Consumer(id), scope)?;
        match *self.arena.consumer(id).ok_or(Form::Dangling)? {
            ConsumerNode::Top => {
                self.emit(StencilId::Halt, Operand::Unused, Operand::Unused);
            },
            ConsumerNode::Covariable(index) => {
                match self.scopes.delivery(scope, Index(u32::from(index)))? {
                    Delivery::Return(slot) => {
                        self.emit(StencilId::Leave, slot.operand(), Operand::Unused);
                    },
                    Delivery::Mark(slot) => {
                        self.emit(StencilId::Ret, slot.operand(), Operand::Unused);
                    },
                    Delivery::FallThrough => {
                        self.emit(StencilId::Pop, Operand::Unused, Operand::Unused);
                    },
                    Delivery::Returning => {
                        self.emit(StencilId::Release, Operand::Unused, Operand::Unused);
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
                self.unmatched(id)?;
                for (position, &label) in labels.iter().enumerate().rev() {
                    self.tasks
                        .push(Task::Matched(id, NodeCount::from(position), scope));
                    self.tasks.push(Task::Bind(label));
                }
            },
            ConsumerNode::DataCase { ref branches, .. } => {
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
                self.unmatched(id)?;
                for (position, &label) in labels.iter().enumerate().rev() {
                    self.tasks
                        .push(Task::Matched(id, NodeCount::from(position), scope));
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
                // reason: a call whose continuation is the body's own return
                // is the body's last act; its window is given back before the
                // callee's entry takes the region's top, the call's operands
                // read from it first.
                let tail = self.returns_through(then, scope)?;
                let release = || Task::Emit(StencilId::Release, Operand::Unused, Operand::Unused);
                match (tag, &**producers) {
                    (DestructorTag::Apply, &[argument]) => {
                        let (inner, slot) = self.bind(held, Binding::Temporary);
                        self.tasks.push(Task::Emit(
                            StencilId::InvokeApply,
                            function.operand(),
                            slot.operand(),
                        ));
                        if tail.is_some() {
                            self.tasks.push(release());
                        }
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
                        if tail.is_some() {
                            self.tasks.push(release());
                        }
                        self.tasks.push(Task::Load(then, held));
                    },
                    (DestructorTag::Project(component), &[]) => {
                        self.tasks.push(Task::Emit(
                            StencilId::Project,
                            Operand::Immediate(component_immediate(component)?),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Emit(
                            StencilId::Var,
                            function.operand(),
                            Operand::Unused,
                        ));
                        self.tasks.push(Task::Load(then, held));
                    },
                    (
                        DestructorTag::Apply | DestructorTag::Force | DestructorTag::Project(_),
                        _,
                    ) => {
                        return Err(Form::Destructor);
                    },
                }
            },
            ConsumerNode::Select { ref selector, then } => {
                self.selected(id, selector, scope)?;
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

    /// How `then` delivers at last when that is the closure body's return,
    /// through the frames of observations it loads — each an application's,
    /// a force's or a projection's, whose frame holds no window — and none
    /// for any other continuation.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Form::Dangling`] for a consumer the arena does not hold;
    /// [`Form::Unbound`] as [`Scopes::delivery`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   and a body that returns or ends in a tail call gives its window back.
    ///   A covariable read from the wrong slot or delivered the wrong way
    ///   answers wrongly; a window kept grows the region the counts read.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_body_gives_its_window_back_at_its_tail_call_and_its_return`
    /// - witness: `tests::count::a_returned_body_gives_its_window_back`
    /// - witness: `tests::count::a_tail_call_gives_its_window_back_before_the_callee_enters`
    fn returns_through(
        &self,
        then: ConsumerId,
        scope: Scope,
    ) -> Result<Option<Delivery>, Form>
    {
        let mut at = then;
        loop {
            match *self.arena.consumer(at).ok_or(Form::Dangling)? {
                ConsumerNode::Covariable(index) => {
                    return Ok(
                        match self.scopes.delivery(scope, Index(u32::from(index)))? {
                            delivery @ (Delivery::Return(_) | Delivery::Returning) => {
                                Some(delivery)
                            },
                            Delivery::Mark(_) | Delivery::FallThrough => None,
                        },
                    );
                },
                ConsumerNode::Destructor {
                    tag: DestructorTag::Apply | DestructorTag::Force | DestructorTag::Project(_),
                    ref consumers,
                    ..
                } => {
                    let &[next] = &**consumers
                    else {
                        return Ok(None);
                    };
                    at = next;
                },
                ConsumerNode::Top
                | ConsumerNode::MuTilde { .. }
                | ConsumerNode::Case { .. }
                | ConsumerNode::DataCase { .. }
                | ConsumerNode::Select { .. }
                | ConsumerNode::ListFold { .. } => return Ok(None),
            }
        }
    }

    /// Run the arm or branch at `position` of the match `id`, the
    /// scrutinee in hand: its binders take the fields, and the match gives
    /// the scrutinee up. Where the ownership reading pairs the arm with a
    /// constructor it builds, the scrutinee is given up as a reuse token that
    /// constructor writes into. A nominal branch that is a thunk of as many
    /// curried objects as its constructor has fields runs where the match
    /// stands, each field in a slot of the match's window; any other is
    /// forced against the fields' application frames.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   among them a split and a nominal match that rebuild their dying
    ///   scrutinee, a split that builds a triple before the pair it rebuilds, a
    ///   split whose scrutinee a thunk shares, and a nominal branch answering a
    ///   function past its constructor's fields; the counts rebuild a unique
    ///   scrutinee in its own block and a shared one in a fresh block. A token
    ///   built into with the wrong fields, never built into, or overwriting a
    ///   shared cell changes an answer or a count.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
    /// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
    /// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
    fn matched(
        &mut self,
        id: ConsumerId,
        position: NodeCount,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        let at = usize::from(position);
        match *arena.consumer(id).ok_or(Form::Dangling)? {
            ConsumerNode::Case { ref arms } => {
                let arm = arms.get(at).ok_or(Form::Dangling)?;
                let fields = u32::try_from(usize::from(arm.constructor.producer_arity()))
                    .map_err(|_overflow| Form::HeaderWidth)?;
                let mut inner = scope;
                for field in 0 .. fields {
                    let (next, slot) = self.bind(inner, Binding::Producer);
                    inner = next;
                    self.emit(StencilId::Field, slot.operand(), Slot(field).operand());
                }
                let (holder, held) = self.bind(inner, Binding::Temporary);
                self.emit(StencilId::Bind, held.operand(), Operand::Unused);
                // reason: a token outlives the match in its slot, so the arm's
                // binders go past it; without one they reuse the slot.
                let token = self.reuse(id, position, holder, held);
                let body = if token.is_some() { holder } else { inner };
                self.tasks.push(Task::Command(arm.body, body));
                self.give_up(held, token);
            },
            ConsumerNode::DataCase {
                ref branches,
                ref arities,
                then,
            } => {
                let branch = *branches.get(at).ok_or(Form::Dangling)?;
                let inline = match arities.get(at) {
                    Some(&arity) => inlined(arena, branch, arity)?,
                    None => None,
                };
                let (inner, held) = self.bind(scope, Binding::Temporary);
                self.emit(StencilId::Bind, held.operand(), Operand::Unused);
                let Some((levels, body)) = inline
                else {
                    self.tasks.push(Task::Emit(
                        StencilId::InvokeForceValue,
                        Operand::Unused,
                        Operand::Unused,
                    ));
                    self.tasks.push(Task::Producer(branch, inner));
                    // The application frames own the fields; the match
                    // gives up the object it was handed.
                    self.tasks
                        .push(Task::Emit(StencilId::Drop, held.operand(), Operand::Unused));
                    self.tasks.push(Task::Emit(
                        StencilId::DupFields,
                        held.operand(),
                        Operand::Unused,
                    ));
                    self.tasks.push(Task::Emit(
                        StencilId::PushFields,
                        held.operand(),
                        Operand::Stub(Stub::Apply),
                    ));
                    self.tasks.push(Task::Load(then, inner));
                    return Ok(());
                };
                // The branch and its curried objects run where the match
                // stands: no closure is made, so none is given up, and each
                // object's continuation falls through to the loaded frame.
                let mut entered =
                    Vec::with_capacity(levels.len().saturating_mul(3).saturating_add(1));
                entered.push((NodeAddress::Producer(branch), inner));
                let (mut level_scope, _forced) = self.bind(inner, Binding::FallThrough);
                for (field, level) in (0_u32 ..).zip(&levels) {
                    entered.push((NodeAddress::Command(level.cut), level_scope));
                    entered.push((NodeAddress::Producer(level.object), level_scope));
                    entered.push((NodeAddress::Consumer(level.returned), level_scope));
                    let (taken, slot) = self.bind(level_scope, Binding::Producer);
                    self.emit(StencilId::Field, slot.operand(), Slot(field).operand());
                    (level_scope, _) = self.bind(taken, Binding::FallThrough);
                }
                let token = self.reuse(id, position, inner, held);
                self.tasks.push(Task::Command(body, level_scope));
                self.tasks.extend(
                    entered
                        .into_iter()
                        .rev()
                        .map(|(node, at)| Task::Entered(node, at)),
                );
                self.give_up(held, token);
                self.tasks.push(Task::Load(then, inner));
            },
            ConsumerNode::Covariable(_)
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Destructor { .. }
            | ConsumerNode::Select { .. }
            | ConsumerNode::ListFold { .. }
            | ConsumerNode::Top => return Err(Form::Dangling),
        }
        Ok(())
    }

    /// The reuse token for the arm at `position` of `id` when the ownership
    /// reading pairs it with a constructor: the slot `held`, which holds the
    /// scrutinee until it is given up and which the binder `scope` ends in
    /// keeps from every later binder of the arm, recorded for that
    /// constructor.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   among them a split and a nominal match that rebuild their dying
    ///   scrutinee, a split that builds a triple before the pair it rebuilds, a
    ///   split whose scrutinee a thunk shares, and a nominal branch answering a
    ///   function past its constructor's fields; the counts rebuild a unique
    ///   scrutinee in its own block and a shared one in a fresh block. A token
    ///   built into with the wrong fields, never built into, or overwriting a
    ///   shared cell changes an answer or a count. L3 — a match with a
    ///   rebuilding branch and a branch building nothing leaves one token.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
    /// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
    /// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
    /// - witness: `lower::tests::only_the_branch_paired_with_its_rebuild_takes_a_token`
    fn reuse(
        &mut self,
        id: ConsumerId,
        position: NodeCount,
        scope: Scope,
        held: Slot,
    ) -> Option<Slot>
    {
        let built = self
            .reuses
            .iter()
            .find(|&&(matched, arm, _)| matched == id && arm == position)
            .map(|&(_, _, built)| built)?;
        self.tokens.push((built, scope, held));
        Some(held)
    }

    /// Queue giving up the scrutinee in `held` whose fields an arm's
    /// binders took: as the reuse token in `token` when the arm has one,
    /// else each field gains an owner and the scrutinee loses one.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   among them a split and a nominal match that rebuild their dying
    ///   scrutinee, a split that builds a triple before the pair it rebuilds, a
    ///   split whose scrutinee a thunk shares, and a nominal branch answering a
    ///   function past its constructor's fields; the counts rebuild a unique
    ///   scrutinee in its own block and a shared one in a fresh block. A token
    ///   built into with the wrong fields, never built into, or overwriting a
    ///   shared cell changes an answer or a count.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
    /// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
    /// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
    fn give_up(
        &mut self,
        held: Slot,
        token: Option<Slot>,
    )
    {
        if let Some(token) = token {
            self.tasks.push(Task::Emit(
                StencilId::Reuse,
                held.operand(),
                token.operand(),
            ));
            return;
        }
        self.tasks
            .push(Task::Emit(StencilId::Drop, held.operand(), Operand::Unused));
        self.tasks.push(Task::Emit(
            StencilId::DupFields,
            held.operand(),
            Operand::Unused,
        ));
    }

    /// The reuse token waiting for the constructor `built` in a slot of
    /// `scope`'s window, taken: a constructor lowered twice writes into the
    /// token once.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs answer alike on both executors,
    ///   among them a split and a nominal match that rebuild their dying
    ///   scrutinee, a split that builds a triple before the pair it rebuilds, a
    ///   split whose scrutinee a thunk shares, and a nominal branch answering a
    ///   function past its constructor's fields; the counts rebuild a unique
    ///   scrutinee in its own block and a shared one in a fresh block. A token
    ///   built into with the wrong fields, never built into, or overwriting a
    ///   shared cell changes an answer or a count. The binder test is
    ///   defensive: the ownership reading pairs no constructor that runs in
    ///   another window than its branch, so every paired constructor is lowered
    ///   under its token's binder and no program tells the test from its
    ///   negation.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    /// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
    /// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
    /// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
    fn token(
        &mut self,
        built: ProducerId,
        scope: Scope,
    ) -> Option<Slot>
    {
        let at = self.tokens.iter().position(|&(constructor, binder, _)| {
            constructor == built && self.scopes.outward(scope).any(|outer| outer == binder)
        })?;
        Some(self.tokens.swap_remove(at).2)
    }

    /// Load the consumer `id` as an observation's continuation.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::step`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the named programs that load a continuation before an
    ///   observation, a fold or a selection answer as they state on both tiers.
    /// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
    /// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
    fn load(
        &mut self,
        id: ConsumerId,
        scope: Scope,
    ) -> Result<(), Form>
    {
        let arena = self.arena;
        let node = arena.consumer(id).ok_or(Form::Dangling)?;
        // A match or a binder is entered where its frame is delivered to.
        if !matches!(
            *node,
            ConsumerNode::MuTilde { .. }
                | ConsumerNode::Case { .. }
                | ConsumerNode::DataCase { .. }
        ) {
            self.enter(NodeAddress::Consumer(id), scope)?;
        }
        match *node {
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
                let owners = self.owners(NodeAddress::Consumer(id), scope, Crossed::NONE)?;
                let label = self.frame_label(Some(owners));
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
                    (DestructorTag::Project(component), &[]) => {
                        self.tasks.push(Task::Emit(
                            StencilId::PushProject,
                            Operand::Stub(Stub::Project),
                            Operand::Immediate(component_immediate(component)?),
                        ));
                        self.tasks.push(Task::Load(then, scope));
                    },
                    (
                        DestructorTag::Apply | DestructorTag::Force | DestructorTag::Project(_),
                        _,
                    ) => {
                        return Err(Form::Destructor);
                    },
                }
            },
            ConsumerNode::Select { then, .. } => {
                let label = self.frame_label(Some(self.unowned()));
                self.blocks.push((label, Task::Selected(id, scope)));
                self.tasks.push(Task::Emit(
                    StencilId::Pushf,
                    Operand::Code(label),
                    Operand::Unused,
                ));
                self.tasks.push(Task::Load(then, scope));
            },
            ConsumerNode::ListFold {
                continuation,
                on_nil,
                on_cons,
                ..
            } => {
                // The frame owns what the empty branch and the cell branch
                // each select: the walk gives the cell branch's up at the
                // empty list.
                let empty = self.owners(NodeAddress::Command(on_nil), scope, Crossed::NONE)?;
                let cells = self.owners(NodeAddress::Command(on_cons), scope, Crossed {
                    producers: 2,
                })?;
                let label = self.frame_label(Some(OwnerRun(empty.0.start .. cells.0.end)));
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

/// Lower the closed command `root`, then fuse its adjacent pairs.
///
/// # Specification
/// - ensures: as [`lower_unfused`], each pair a rule fuses run as one
///   instruction and named in the trace, which [`crate::replay`] replays over
///   [`lower_unfused`]'s function to this function.
/// - executable: none — running as the source means is observed only by running
///   both tiers against stated answers, and fused against unfused.
///
/// # Errors
/// As [`lower_unfused`].
///
/// # Adequacy
/// - hypothesis: L2 — the named, generated and corpus programs run fused on
///   both tiers and unfused beside them with equal outcomes, each fused
///   function the replay of its trace, and fusions asserted to occur.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
#[inline]
pub fn lower(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Result<Lowered, Form>
{
    Ok(fused(lowered(arena, definitions, Root::Closed(root))?))
}

/// Lower `body`, a command binding one covariable, to run over the producer
/// bindings its support selects, then fuse its adjacent pairs: the code a
/// command closed over a store's values runs.
///
/// # Specification
/// - ensures: as [`lower`], the entry opening `body` over a window whose first
///   slots, [`Lowered::captures`], hold the bindings its support selects — the
///   captures a closure suspending `body` would hold, innermost first — and
///   binding its covariable to the halt frame's mark, so delivering to it ends
///   the run with the value delivered. Each capture slot holds one owner, which
///   the body consumes.
/// - executable: none — as [`lower`].
///
/// # Errors
/// As [`lower_unfused`]; [`Form::Unbound`] for a linear variable `body`
/// names, which no store binds.
///
/// # Adequacy
/// - hypothesis: L2 — thunks a run answered with, over no capture, one, two and
///   one shared by two fields, run from the store on both tiers and answer what
///   forcing each in place answers; a capture slot swapped, dropped or left
///   uncounted changes an answer or frees a value still read.
/// - witness: `tests::closed::a_thunk_runs_from_the_store_as_it_runs_in_place`
/// - witness: `tests::closed::a_shared_capture_is_laid_out_once_and_counted_twice`
#[inline]
pub fn lower_suspended(
    arena: &CommandArena,
    definitions: &Definitions,
    body: CommandId,
) -> Result<Lowered, Form>
{
    Ok(fused(lowered(arena, definitions, Root::Suspended(body))?))
}

/// `lowered` with its adjacent pairs fused, the trace recorded.
///
/// # Specification
/// trivial.
fn fused(lowered: Lowered) -> Lowered
{
    let (function, trace) = fuse(&lowered.function);
    Lowered {
        function,
        fused: trace,
        ..lowered
    }
}

/// Lower the closed command `root`, every instruction its own dispatch: the
/// function a fused one's trace is replayed over.
///
/// # Specification
/// - ensures: the function's entry runs `root` from an empty frame region,
///   delivering its answer to the halt exit: each transparent constant unfolded
///   once per run at its first read, each closure site recorded with the
///   producer it suspends, and every owner counted. One that suspends a capture
///   is lowered with every cut delivering a variable or a constant to anything
///   but a binder testing for one first, which runs it against that consumer.
///   One visit over the nodes the command reaches decides that before it
///   starts, and the command is lowered once. The trace of fusions is empty.
/// - executable: none — running as the source means is observed only by running
///   both tiers against stated answers.
///
/// # Errors
/// The [`Form`] of the first ill-formed or oversized node, or
/// [`Form::Unowned`] for a node the ownership reading does not place.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs halt on both tiers with equal answers:
///   returns, binds, cases, constructors, functions, thunks, lazy products and
///   an application. The stencils' suite runs the generated programs and the
///   corpus through this lowering too, each refused form counted by name.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
#[inline]
pub fn lower_unfused(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Result<Lowered, Form>
{
    lowered(arena, definitions, Root::Closed(root))
}

/// What a lowering opens at its entry.
#[derive(Clone, Copy, Debug)]
enum Root
{
    /// A closed command, delivering to `★`.
    Closed(CommandId),
    /// A command binding one covariable, over the producer bindings its
    /// support selects.
    Suspended(CommandId),
}

/// Lower `root` unfused: [`lower_unfused`] for a closed command, the
/// unfused function of [`lower_suspended`] for a suspended one.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`lower_unfused`].
fn lowered(
    arena: &CommandArena,
    definitions: &Definitions,
    root: Root,
) -> Result<Lowered, Form>
{
    let (Root::Closed(command) | Root::Suspended(command)) = root;
    let survey = survey(arena, definitions, command)?;
    let ownership =
        Ownership::of(arena, &survey.roots, &survey.reached).map_err(|_dangling| Form::Dangling)?;
    let mut reuses = Vec::with_capacity(ownership.reuses().len());
    for reuse in ownership.reuses() {
        if let Some(&CommandNode::Cut { consumer, .. }) = arena.command(reuse.matched) {
            reuses.push((consumer, reuse.branch, reuse.built));
        }
    }
    let checked = survey.checked;
    let mut lowering = Lowering {
        arena,
        definitions,
        function: Function::default(),
        sites: Vec::new(),
        cells: Vec::new(),
        bounds: Vec::new(),
        scopes: Scopes::default(),
        tasks: Vec::new(),
        blocks: Vec::new(),
        bodies: Vec::new(),
        window: 0,
        globals: Vec::new(),
        checked,
        heads: Vec::new(),
        literals: Vec::new(),
        codes: Vec::new(),
        callees: Vec::new(),
        selections: Vec::new(),
        unmatched: Vec::new(),
        handlers: Vec::new(),
        windows: Vec::new(),
        pending: Vec::new(),
        owners: Vec::new(),
        unwinds: Vec::new(),
        ownership,
        reuses,
        tokens: Vec::new(),
    };
    let captures = match root {
        Root::Closed(command) => {
            lowering.tasks.push(Task::Command(command, Scope::Empty));
            Vec::new()
        },
        Root::Suspended(body) => lowering.suspended(body)?,
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
        for (label, owners) in core::mem::take(&mut lowering.pending) {
            lowering.windows.push(Window {
                label,
                slots,
                owners,
            });
        }
        let Some(body) = lowering.bodies.pop()
        else {
            break;
        };
        entry = Some(lowering.open(body));
    }
    let mut table = Vec::with_capacity(lowering.heads.len().saturating_add(1));
    for (at, label) in core::mem::take(&mut lowering.selections) {
        table.clear();
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
                | ConstructorTag::Recorded(_)
                | ConstructorTag::Dialogue(_)
                | ConstructorTag::Web(_) => 0,
            };
            table.push(Word::from(position));
        }
        let constant = lowering.function.constant(&table);
        lowering.function.set_a(at, Operand::Data(constant));
    }
    let lowered = Lowered {
        function: lowering.function,
        fused: Vec::new(),
        sites: lowering.sites,
        captures,
        cells: lowering.cells,
        bounds: lowering.bounds,
        heads: lowering.heads,
        literals: lowering.literals,
        codes: lowering.codes,
        callees: lowering.callees,
        handlers: lowering.handlers,
        windows: lowering.windows,
        owners: lowering.owners,
        unwinds: lowering.unwinds,
        unmatched: lowering.unmatched,
        globals: lowering
            .globals
            .into_iter()
            .map(|(constant, _)| constant)
            .collect(),
    };
    Ok(lowered)
}

/// What one visit over a command finds before it is lowered.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Survey
{
    /// Whether a cut delivering a variable or a constant tests it for a
    /// suspended capture first: whether the command creates one, which only a
    /// `μ` cut negatively against a binder does ([`Lowering::command`]); a `μ`
    /// cut any other way runs where it stands and suspends nothing.
    checked: bool,
    /// The roots its ownership is read from: the command, then each
    /// transparent constant's definition in the order the visit meets it.
    roots: Vec<NodeAddress>,
    /// Every node the roots reach, each once, in first-visit order.
    reached: Vec<NodeAddress>,
}

/// Visit each node `root` reaches, and each node the definition of a
/// transparent constant it reads reaches, once, in first-visit order.
///
/// The visit reads at least every node the lowering does, and its walk is
/// the one the ownership reading reads over.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Form::Dangling`] for a node the arena does not hold.
///
/// # Adequacy
/// - hypothesis: L2 — every named program lowers counted: a survey that reads
///   no root leaves every node unplaced, and the lowering refuses. L3 — a bind
///   whose continuation is named by a positive `μ` leaves the lowering
///   unchecked.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
/// - witness: `lower::tests::a_named_continuation_that_runs_tests_no_capture_1856`
fn survey(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> Result<Survey, Form>
{
    let mut captured = false;
    let mut seen = BTreeSet::new();
    let mut unfolded = BTreeSet::new();
    let mut reached = Vec::new();
    let mut roots = Vec::from([NodeAddress::Command(root)]);
    let mut walked = 0;
    while walked < roots.len() {
        let from = reached.len();
        reach(
            arena,
            roots.get(walked ..).unwrap_or_default(),
            &mut seen,
            &mut reached,
        )
        .map_err(|_dangling| Form::Dangling)?;
        walked = roots.len();
        for &node in reached.get(from ..).unwrap_or_default() {
            match node {
                NodeAddress::Producer(id) => match *arena.producer(id).ok_or(Form::Dangling)? {
                    ProducerNode::Constant(constant) => {
                        if let Some(Definition::Transparent(definition)) = definitions.get(constant)
                            && unfolded.insert(definition)
                        {
                            roots.push(NodeAddress::Producer(definition));
                        }
                    },
                    ProducerNode::Mu { .. }
                    | ProducerNode::Primitive { .. }
                    | ProducerNode::Decompose(_)
                    | ProducerNode::Variable { .. }
                    | ProducerNode::Literal(_)
                    | ProducerNode::Code(_)
                    | ProducerNode::Constructor { .. }
                    | ProducerNode::Thunk { .. }
                    | ProducerNode::Fixpoint { .. }
                    | ProducerNode::Cocase { .. }
                    | ProducerNode::Closure { .. }
                    | ProducerNode::Reify(_) => {},
                },
                NodeAddress::Command(id) => {
                    if let CommandNode::Cut {
                        polarity: Polarity::Negative,
                        producer,
                        consumer,
                    } = *arena.command(id).ok_or(Form::Dangling)?
                        && let ProducerNode::Mu { .. } =
                            *arena.producer(producer).ok_or(Form::Dangling)?
                        && let ConsumerNode::MuTilde { .. } =
                            *arena.consumer(consumer).ok_or(Form::Dangling)?
                    {
                        captured = true;
                    }
                },
                NodeAddress::Consumer(_) => {},
            }
        }
    }
    Ok(Survey {
        checked: captured,
        roots,
        reached,
    })
}

/// One curried object of a nominal branch run where its match stands: the
/// cut that hands it back, the object and the continuation it is handed to.
#[derive(Clone, Copy, Debug)]
struct Level
{
    /// `⟨object |− α0⟩`.
    cut: CommandId,
    /// The single-arm `apply` object.
    object: ProducerId,
    /// The `α0` the cut hands the object to.
    returned: ConsumerId,
}

/// The `arity` curried objects of the nominal branch `branch` and the body
/// under them, when the branch is `{force(α) ⇒ ⟨cocase {apply(x; α) ⇒ …} |−
/// α0⟩}` that many levels deep and the body names no continuation of the
/// chain but its own: the chain then runs in its match's window, each field
/// in a slot. None for any other branch, which is forced as a closure.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Form::Dangling`] for a node the arena does not hold.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs answer alike on both executors, among
///   them a split and a nominal match that rebuild their dying scrutinee, a
///   split that builds a triple before the pair it rebuilds, a split whose
///   scrutinee a thunk shares, and a nominal branch answering a function past
///   its constructor's fields; the counts rebuild a unique scrutinee in its own
///   block and a shared one in a fresh block. A token built into with the wrong
///   fields, never built into, or overwriting a shared cell changes an answer
///   or a count. L3 — a branch of each shape a level or its body can break the
///   chain with, against the one inlined, and a body naming the chain's force
///   against one naming the first continuation past it.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
/// - witness: `lower::tests::a_nominal_branch_rebuilds_in_place_into_its_scrutinee`
/// - witness: `tests::count::a_unique_scrutinee_is_rebuilt_in_its_own_block`
/// - witness: `tests::count::a_shared_scrutinee_is_rebuilt_in_a_fresh_block`
/// - witness: `lower::tests::a_branch_is_inlined_only_in_its_exact_shape`
fn inlined(
    arena: &CommandArena,
    branch: ProducerId,
    arity: FieldCount,
) -> Result<Option<(Vec<Level>, CommandId)>, Form>
{
    let ProducerNode::Thunk { body } = *arena.producer(branch).ok_or(Form::Dangling)?
    else {
        return Ok(None);
    };
    let fields = usize::from(arity);
    let mut levels = Vec::with_capacity(fields);
    let mut at = body;
    for _field in 0 .. fields {
        let CommandNode::Cut {
            producer, consumer, ..
        } = *arena.command(at).ok_or(Form::Dangling)?
        else {
            return Ok(None);
        };
        let returned = matches!(
            arena.consumer(consumer),
            Some(&ConsumerNode::Covariable(index)) if u32::from(index) == 0
        );
        let Some(&ProducerNode::Cocase { ref arms }) = arena.producer(producer)
        else {
            return Ok(None);
        };
        let &[ref arm] = &**arms
        else {
            return Ok(None);
        };
        if !returned || arm.destructor != DestructorTag::Apply {
            return Ok(None);
        }
        levels.push(Level {
            cut: at,
            object: producer,
            returned: consumer,
        });
        at = arm.body;
    }
    // reason: the body's own continuation is the match's; the chain's others
    // are the application frames a forced branch would have, which an inlined
    // one never pushes.
    let support = arena
        .node_scope(NodeAddress::Command(at))
        .ok_or(Form::Dangling)?;
    let chain = u32::try_from(fields).map_err(|_overflow| Form::HeaderWidth)?;
    let outside = BinderDepth::from(1_usize);
    if support
        .covariables()
        .outside(Zone::Intuitionistic, outside)
        .any(|index| u32::from(index) <= chain)
    {
        return Ok(None);
    }
    Ok(Some((levels, at)))
}

#[cfg(test)]
mod tests
{
    use gandr_core_sequent::CopatternArm;
    use gandr_core_sequent::CovariableIndex;
    use gandr_core_sequent::Provenance;
    use gandr_core_sequent::focus_computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;

    use super::*;

    /// A thunk created under two bindings that names only the outer one
    /// holds that one capture, not the creator's two slots, and its site reads
    /// the capture at the closure's first position.
    #[test]
    fn a_closure_holds_exactly_what_it_names()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let outer = core.computation_return(unit);
        let inner = core.computation_return(unit);
        let named = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let suspended = core.computation_return(named);
        let thunk = core.value_thunk(suspended);
        let body = core.computation_return(thunk);
        let within = core.computation_bind(inner, body);
        let root = core.computation_bind(outer, within);
        let mut commands = CommandArena::new();
        let root = focus_computation(&core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        let lowered = lower(&commands, &Definitions::new(), root).expect("the program lowers");
        let arities: Vec<usize> = lowered
            .function
            .instructions()
            .iter()
            .filter(|instruction| instruction.stencil == StencilId::Closure)
            .map(|instruction| match instruction.b {
                // The header's arity field: bits 16 to 31.
                Operand::Immediate(low) => (usize::from(low) >> 16_u32) & 0xFFFF,
                other @ (Operand::Unused
                | Operand::Code(_)
                | Operand::Data(_)
                | Operand::Stub(_)) => {
                    panic!("a closure's header is an immediate, not {other:?}")
                },
            })
            .collect();
        assert_eq!(vec![1], arities, "the thunk captures one binding");
        let captures: Vec<&[Slot]> = lowered
            .sites
            .iter()
            .map(|site| site.captures.as_slice())
            .collect();
        assert_eq!(
            vec![&[Slot(0)][..]],
            captures,
            "its site reads the one capture"
        );
    }

    /// A nominal match whose branch rebuilds the constructor it took apart
    /// runs the branch where the match stands — no closure for the branch or
    /// its curried objects, no application frames — and writes the new object
    /// into the scrutinee's block: the token the match leaves in its slot is
    /// what the constructor is built into.
    #[test]
    fn a_nominal_branch_rebuilds_in_place_into_its_scrutinee()
    {
        let mut core = CoreArena::new();
        let one = core.value_unit();
        let two = core.value_unit();
        let datatype = core.value_type_data(0_usize.into(), Vec::new());
        let built = core.value_constructor(datatype, 0_usize.into(), vec![one, two]);
        let bound = core.computation_return(built);
        let scrutinee = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let first = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let second = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let rebuilt = core.value_constructor(datatype, 0_usize.into(), vec![second, first]);
        let answered = core.computation_return(rebuilt);
        let inner = core.computation_lambda(answered);
        let branch = core.computation_lambda(inner);
        let motive = core.comp_type_unknown();
        let cased =
            core.computation_data_case(scrutinee, motive, vec![branch], vec![FieldCount::from(
                2_usize,
            )]);
        let root = core.computation_bind(bound, cased);
        let mut commands = CommandArena::new();
        let root = focus_computation(&core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        let lowered = lower(&commands, &Definitions::new(), root).expect("the program lowers");
        let instructions = lowered.function.instructions();
        let stencils: Vec<StencilId> = instructions
            .iter()
            .map(|instruction| instruction.stencil)
            .collect();
        for absent in [
            StencilId::Closure,
            StencilId::PushFields,
            StencilId::InvokeForceValue,
        ] {
            assert!(
                !stencils.contains(&absent),
                "the branch runs in place: no {absent:?} in {stencils:?}"
            );
        }
        let reuse = instructions
            .iter()
            .find(|instruction| instruction.stencil == StencilId::Reuse)
            .expect("the match leaves a token");
        let into = instructions
            .iter()
            .position(|instruction| instruction.stencil == StencilId::CtorInto)
            .expect("the constructor is built into the token");
        let token = instructions
            .get(into.wrapping_sub(1))
            .expect("the token is put in hand");
        assert_eq!(
            (StencilId::Var, reuse.b),
            (token.stencil, token.a),
            "the constructor takes the token from the slot the match left it in"
        );
    }

    /// A thunk whose body forces a second thunk as its last act gives its
    /// window back before the force, and the second thunk's body gives its
    /// window back as it returns.
    #[test]
    fn a_body_gives_its_window_back_at_its_tail_call_and_its_return()
    {
        let mut core = CoreArena::new();
        let one = core.value_unit();
        let inner = core.computation_return(one);
        let second = core.value_thunk(inner);
        let bound = core.computation_return(second);
        let named = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let forced = core.computation_force(named);
        let body = core.computation_bind(bound, forced);
        let first = core.value_thunk(body);
        let root = core.computation_force(first);
        let mut commands = CommandArena::new();
        let root = focus_computation(&core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        let lowered = lower(&commands, &Definitions::new(), root).expect("the program lowers");
        let stencils: Vec<StencilId> = lowered
            .function
            .instructions()
            .iter()
            .map(|instruction| instruction.stencil)
            .collect();
        let release = stencils
            .iter()
            .position(|&stencil| stencil == StencilId::Release)
            .expect("the first body releases its window at its tail call");
        assert_eq!(
            Some(&StencilId::InvokeForce),
            stencils.get(release.wrapping_add(1)),
            "the release comes just before the force: {stencils:?}"
        );
        assert!(
            stencils.contains(&StencilId::Leave),
            "the second body leaves its window as it returns: {stencils:?}"
        );
    }

    /// A bind whose bound computation is itself a bind names its continuation
    /// with a `μ` that runs where it stands: it suspends nothing, so no cut
    /// tests what it delivers for a capture, and what follows the bind is
    /// lowered once (#1856).
    #[test]
    fn a_named_continuation_that_runs_tests_no_capture_1856()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let made = core.computation_return(unit);
        let inner = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let returned = core.computation_return(inner);
        let bound = core.computation_bind(made, returned);
        let outer = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let rest = core.computation_return(outer);
        let root = core.computation_bind(bound, rest);
        let mut commands = CommandArena::new();
        let root = focus_computation(&core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        let named = (0_u32 ..).take(usize::from(commands.command_count())).any(|index| {
            matches!(
                commands.command(CommandId::from(index)),
                Some(&CommandNode::Cut { polarity: Polarity::Positive, producer, consumer })
                    if matches!(commands.producer(producer), Some(&ProducerNode::Mu { .. }))
                        && matches!(commands.consumer(consumer), Some(&ConsumerNode::MuTilde { .. }))
            )
        });
        assert!(
            named,
            "the inner bind's continuation is named by a positive μ"
        );
        let lowered =
            lower_unfused(&commands, &Definitions::new(), root).expect("the program lowers");
        let stencils: Vec<StencilId> = lowered
            .function
            .instructions()
            .iter()
            .map(|instruction| instruction.stencil)
            .collect();
        assert!(
            !stencils.contains(&StencilId::Captured),
            "no delivery tests for a capture: {stencils:?}"
        );
    }

    /// Every form the lowering refuses renders apart from the others.
    #[test]
    fn every_refused_form_renders_apart()
    {
        let mut rendered: alloc::vec::Vec<alloc::string::String> = [
            Form::ConsumerFields,
            Form::Destructor,
            Form::HeaderWidth,
            Form::Oversized,
            Form::Dangling,
            Form::Unbound,
            Form::Unowned,
        ]
        .iter()
        .map(alloc::string::ToString::to_string)
        .collect();
        let count = rendered.len();
        rendered.sort();
        rendered.dedup();
        assert_eq!(rendered.len(), count, "{rendered:?}");
    }

    /// The instructions of `root`'s fused lowering, `core` focused.
    ///
    /// # Specification
    /// trivial.
    fn lowered(
        core: &CoreArena,
        root: gandr_core_term::ComputationId,
    ) -> Vec<Instruction>
    {
        let mut commands = CommandArena::new();
        let root = focus_computation(core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        lower(&commands, &Definitions::new(), root)
            .expect("the program lowers")
            .function
            .instructions()
            .to_vec()
    }

    /// A nominal match whose first branch rebuilds the constructor it took
    /// apart and whose second builds nothing leaves a reuse token in the
    /// first alone: the second gives its scrutinee up, its fields gaining an
    /// owner, rather than holding a token no constructor is built into.
    #[test]
    fn only_the_branch_paired_with_its_rebuild_takes_a_token()
    {
        let mut core = CoreArena::new();
        let one = core.value_unit();
        let two = core.value_unit();
        let datatype = core.value_type_data(0_usize.into(), Vec::new());
        let built = core.value_constructor(datatype, 0_usize.into(), vec![one, two]);
        let bound = core.computation_return(built);
        let scrutinee = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let first = core.value_variable(Zone::Intuitionistic, 1_u32.into());
        let second = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let rebuilt = core.value_constructor(datatype, 0_usize.into(), vec![second, first]);
        let answered = core.computation_return(rebuilt);
        let inner = core.computation_lambda(answered);
        let rebuilding = core.computation_lambda(inner);
        let nothing = core.value_unit();
        let empty = core.computation_return(nothing);
        let motive = core.comp_type_unknown();
        let cased = core.computation_data_case(scrutinee, motive, vec![rebuilding, empty], vec![
            FieldCount::from(2_usize),
            FieldCount::from(0_usize),
        ]);
        let root = core.computation_bind(bound, cased);
        let stencils: Vec<StencilId> = lowered(&core, root)
            .iter()
            .map(|instruction| instruction.stencil)
            .collect();
        let count = |stencil: StencilId| stencils.iter().filter(|&&each| each == stencil).count();
        assert_eq!(
            (1, 1),
            (count(StencilId::Reuse), count(StencilId::CtorInto)),
            "one token, built into once: {stencils:?}"
        );
        assert_eq!(
            1,
            count(StencilId::DupFields),
            "the other branch gives its scrutinee up: {stencils:?}"
        );
    }

    /// A force under a bind delivers to the bind's frame: the window is shrunk
    /// to the slot the frame's push marked before the force is invoked.
    #[test]
    fn a_delivery_to_a_marked_covariable_shrinks_to_its_slot()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let made = core.computation_return(unit);
        let thunk = core.value_thunk(made);
        let held = core.computation_return(thunk);
        let named = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let forced = core.computation_force(named);
        let inner = core.computation_bind(held, forced);
        let outer = core.value_variable(Zone::Intuitionistic, 0_u32.into());
        let rest = core.computation_return(outer);
        let root = core.computation_bind(inner, rest);
        let instructions = lowered(&core, root);
        let stencils: Vec<StencilId> = instructions
            .iter()
            .map(|instruction| instruction.stencil)
            .collect();
        let pushed = instructions
            .iter()
            .find(|instruction| instruction.stencil == StencilId::Pushk)
            .expect("the bind pushes its frame");
        let shrunk = instructions
            .iter()
            .position(|instruction| instruction.stencil == StencilId::Shrink)
            .unwrap_or_else(|| panic!("the force's delivery shrinks the window: {stencils:?}"));
        assert_eq!(
            pushed.b, instructions[shrunk].a,
            "to the slot the frame marked: {stencils:?}"
        );
        assert_eq!(
            Some(&StencilId::InvokeForce),
            stencils.get(shrunk.wrapping_add(1)),
            "just before the force: {stencils:?}"
        );
    }

    /// A nominal branch of one field, `{force(α) ⇒ ⟨cocase {head(x; β) ⇒
    /// ⟨x | named⟩} |− handed⟩}`, the head and both covariables chosen.
    ///
    /// # Specification
    /// trivial.
    fn branch(
        head: DestructorTag,
        handed: CovariableIndex,
        named: CovariableIndex,
    ) -> (CommandArena, ProducerId)
    {
        let mut arena = CommandArena::new();
        let field = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            })
            .expect("a leaf mints");
        let answer = arena
            .mint_consumer(ConsumerNode::Covariable(named))
            .expect("a leaf mints");
        let body = arena
            .mint_cut(Polarity::Positive, field, answer)
            .expect("the children resolve");
        let object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([CopatternArm {
                    destructor: head,
                    body,
                }]),
            })
            .expect("the arm resolves");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(handed))
            .expect("a leaf mints");
        let cut = arena
            .mint_cut(Polarity::Negative, object, back)
            .expect("the children resolve");
        let thunk = arena
            .mint_producer(ProducerNode::Thunk { body: cut })
            .expect("the body resolves");
        (arena, thunk)
    }

    /// A branch runs where its match stands only when each level applies
    /// and hands its object back to its own `α0`, and its body names no
    /// continuation of the chain but its own: the chain's force `α1` keeps
    /// it a closure, and the first continuation past the chain, `α2`, does
    /// not.
    #[test]
    fn a_branch_is_inlined_only_in_its_exact_shape()
    {
        let one = FieldCount::from(1_usize);
        let inlines = |head: DestructorTag, handed: u32, named: u32| {
            let (arena, thunk) = branch(head, handed.into(), named.into());
            inlined(&arena, thunk, one)
                .expect("the arena holds the branch")
                .is_some()
        };
        assert!(
            inlines(DestructorTag::Apply, 0, 0),
            "a body answering its own continuation"
        );
        assert!(
            inlines(DestructorTag::Apply, 0, 2),
            "a body naming the first continuation past the chain"
        );
        assert!(
            !inlines(DestructorTag::Apply, 0, 1),
            "a body naming the chain's force"
        );
        assert!(
            !inlines(DestructorTag::Apply, 1, 0),
            "a level handing its object to another continuation"
        );
        assert!(
            !inlines(DestructorTag::Force, 0, 0),
            "a level answering another head"
        );
    }

    /// A function holds as many instructions as one lowering emits, and one
    /// more is refused as oversized.
    #[test]
    fn a_function_holds_up_to_the_instruction_ceiling()
    {
        let mut function = Function::default();
        let halt = Instruction {
            stencil: StencilId::Halt,
            a: Operand::Unused,
            b: Operand::Unused,
            alt: Alt::None,
        };
        assert_eq!(Ok(()), hold_size(&function), "an empty function");
        for _instruction in 0 .. INSTRUCTIONS {
            let _at = function.push(halt);
        }
        assert_eq!(Ok(()), hold_size(&function), "a function at the ceiling");
        let _past = function.push(halt);
        assert_eq!(
            Err(Form::Oversized),
            hold_size(&function),
            "one instruction past the ceiling"
        );
    }

    /// A handler whose operation clause answers a pair bound outside it, and
    /// whose return clause names nothing, keeps that pair while its frame
    /// waits: its frame owns the pair's slot, and its return gives it up.
    #[test]
    fn a_handler_keeps_what_its_clauses_name_past_their_binders()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let outer = core.value_tuple(&[unit, unit]);
        let bound = core.computation_return(outer);
        let payload = core.value_type_unit();
        let signature = EffectSig::new(EffectName::from("E"), [EffectOp {
            name: OperationName::from("op"),
            payload,
            reply: payload,
        }])
        .expect("one operation");
        let performed =
            core.computation_perform(signature.clone(), OperationName::from("op"), unit);
        let answered = core.computation_return(unit);
        let subject = core.computation_bind(performed, answered);
        let on_return = core.computation_return(unit);
        // reason: past the clause's stack `x0` and payload `x1`, the pair is
        // `x2`.
        let kept = core.value_variable(Zone::Intuitionistic, 2_u32.into());
        let clause = core.computation_return(kept);
        let handled = core.computation_handle(
            signature,
            subject,
            on_return,
            alloc::sync::Arc::from([EffectClause {
                operation: OperationName::from("op"),
                body: clause,
            }]),
        );
        let root = core.computation_bind(bound, handled);
        let mut commands = CommandArena::new();
        let root = focus_computation(&core, root, &mut commands, &mut Provenance::new())
            .expect("the program focuses");
        let lowered = lower(&commands, &Definitions::new(), root).expect("the program lowers");
        let handler = lowered
            .handlers
            .first()
            .expect("the program installs one handler");
        let window = lowered
            .windows
            .iter()
            .find(|window| window.label == handler.label)
            .expect("the handler's frame resumes in a window");
        let run = window
            .owners
            .clone()
            .expect("the handler's frame owns a run");
        let owned = &lowered.owners[run.0];
        assert_eq!(1, owned.len(), "the frame owns the pair alone: {owned:?}");
        let dropped = lowered.function.instructions().iter().any(|instruction| {
            instruction.stencil == StencilId::Drop && instruction.a == owned[0].operand()
        });
        assert!(dropped, "the handler's return gives the pair up");
    }
}
