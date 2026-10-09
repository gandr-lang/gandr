//! The lowering itself: [`lower_module`], the [`LoweringBudget`] that bounds
//! it, and the two sweeps over the arena it is made of.
//!
//! # Two sweeps over one level-order arena, and no recursion anywhere
//!
//! The molded tree lays its nodes out in level order, so a walk in ascending
//! position order visits every parent before any of its children and a walk in
//! descending order visits every child before its parent. Lowering needs both
//! directions and gets each as a plain loop with no stack of its own.
//!
//! The **ascending sweep classifies**. A node's sort is fixed by its parent —
//! the same identifier is a binder, a type head or a term name depending on
//! where it sits — so the sort and the binder frame flow down. The sweep
//! dispatches every form on its grammar kind, reads its own tiles apart from
//! its operands, resolves every name, parses every literal, and decides every
//! refusal; what it decides for a form is recorded as that form's plan.
//!
//! The **descending sweep mints**. Every child is already lowered when its
//! parent is reached, which is exactly what the core arena's constructor-only
//! minting requires, so the sweep carries out each plan, records an origin,
//! and can fail at nothing. A node whose children did not lower simply does
//! not lower, which is how a refused declaration's subtree costs nothing.
//!
//! # A node's produced sort is a function of its own form
//!
//! The classification never pushes an expected sort into a place that has to
//! re-derive it: `+U` produces a value type and `-F` a computation type, a
//! thunk is a value and a lambda is a computation, and a grouping is whatever
//! it wraps. So a sort mismatch is decided where the node stands rather than
//! where its result is consumed, and every refusal carries the sort its own
//! position demanded.
//!
//! # Five insertions, by the sort of the position
//!
//! Where the source writes a value and the position reads a computation, or
//! the reverse, the fragment refuses — with five exceptions, each a site the
//! grammar's own shape names. An application's head reads a computation, and
//! a value standing there is forced; a function's result reads a computation
//! type, and a value type standing there gains a returner; a function's body is
//! a computation where the declaration takes a value, and is thunked; a type
//! standing where a value is read is quoted into its code; and a name standing
//! where a type is read, bound at a universe, is decoded out of it. Each
//! bridge is decided by the position and the name's binder, never searched
//! for, and its origin is the syntax node that demanded it, marked inserted,
//! so a reader can be shown the cast they did not write. Everywhere else the
//! mismatch stays a refusal: a lambda written where a value belongs is still
//! the author's mistake to suspend.
//!
//! # A parameter a type names binds a dependent arrow
//!
//! A function's declared type is a chain of arrows, one per parameter, and an
//! arrow binds its parameter in the codomain only when it is dependent. A
//! parameter whose name a later parameter's type or the result decodes is
//! recorded on its binder frame as the classification reads that type, so by
//! the time the signature is minted each frame knows whether its arrow binds.
//! A decode's code is the variable counted over the frames between it and its
//! binder that bind in the type: every frame a lambda binds, and a typed
//! parameter's only when its arrow is dependent.
//!
//! # One order of checks, the same at every form
//!
//! A form is checked in a fixed order, and the first check it fails is its
//! refusal: a kind the fragment has no reading for; a repair the parser made
//! among its children; a former of the wrong family for its position, a term
//! where a type belongs or the reverse; a reserved form; a former that does
//! not produce the sort its position demands; a variant of the form the
//! fragment does not admit, or a number of operands it does not take; and
//! last, the names and literals it holds.
//!
//! # The allowance is what bounds the work
//!
//! Every node visit and every binder frame walked spends one step of a caller's
//! allowance. Without it the binder-chain walk makes lowering quadratic in the
//! depth of a module nothing else bounds; with it the whole lowering is linear
//! in the allowance, and running out is an engine fault rather than a wrong
//! answer.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::ops::ControlFlow;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::attribute::AttributeEntry;
use crate::attribute::AttributeRegistry;
use crate::attribute::AttributeTable;
use crate::attribute::PayloadForm;
use crate::attribute::PayloadVerdict;
use crate::attribute::RegisteredAttribute;
use crate::attribute::payload;
use crate::attribute::payload_form;
use crate::attribute::payload_verdict;
use crate::classify::FailureClass;
use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::Cursor;
use crate::form::FormName;
use crate::form::Former;
use crate::form::Piece;
use crate::form::Pieces;
use crate::form::Placed;
use crate::form::Run;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::read_pieces;
use crate::form::shape_of;
use crate::import::ModuleImports;
use crate::module::Collected;
use crate::module::ComponentScope;
use crate::module::Container;
use crate::module::DeclarationOutcome;
use crate::module::DeclarationParts;
use crate::module::DeclarationSlot;
use crate::module::Half;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::module::LoweredStructure;
use crate::module::ManifestComponent;
use crate::module::Member;
use crate::module::Operand;
use crate::module::Payload;
use crate::module::Role;
use crate::module::SlotIndex;
use crate::module::StructureIndex;
use crate::module::ValueComponent;
use crate::module::WrittenAttribute;
use crate::module::collect;
use crate::module::declaration_half;
use crate::module::manifest_type;
use crate::module::slot_refusal;
use crate::namespace::Binding;
use crate::namespace::NamePath;
use crate::namespace::PathResolution;
use crate::namespace::Recognition;
use crate::namespace::RecognitionSite;
use crate::namespace::Recognized;
use crate::namespace::Segment;
use crate::namespace::Trie;
use crate::origin::Insertion;
use crate::origin::Origin;
use crate::origin::OriginTable;
use crate::resolve::Bound;
use crate::resolve::Frame;
use crate::resolve::HeadArity;
use crate::resolve::OperandCount;
use crate::resolve::Scope;
use crate::resolve::ScopeId;
use crate::resolve::SurfaceName;
use crate::resolve::TypeAtom;
use crate::resolve::TypeFormer;
use crate::resolve::binder_type;
use crate::resolve::type_atom;
use crate::resolve::type_former;

quenchant_shape::reason_enum! {
    /// Why a node has no lowered core node.
    pub mod lowered {
        /// The mint sweep produced nothing usable for the node.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The node was not minted: unread, refused, or under a refusal.
            Unminted,
            /// The node was minted at another sort than the one asked for.
            OtherSort,
            /// The function tail states no type: a parameter or the result is
            /// untyped.
            Unstated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a lexeme denotes no literal.
    pub mod literal {
        /// The text is not a lexeme of the literal form asked about.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The text is not the form's lexeme.
            Malformed,
            /// The former is not a literal former at all.
            NotALiteral,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a tile in a block names no statement.
    pub mod statement {
        /// The tile opens none of the statements a block holds.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The tile is no statement's keyword.
            NotAKeyword,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a node sees no manifest type component.
    pub mod scoped {
        /// The node lies in no module signature.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No signature type encloses the node.
            Unscoped,
        }
    }
}

/// The work one lowering may spend before it refuses.
///
/// One step is charged per node visited, per binder frame walked, per module
/// child and per attribute, so the allowance bounds the whole lowering rather
/// than any single sweep.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LoweringBudget(usize);

impl LoweringBudget
{
    /// The allowance a caller with no reason to bound the walk takes.
    pub const DEFAULT: Self = Self(1_000_000_usize);
}

impl From<usize> for LoweringBudget
{
    /// The allowance of `steps` steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: usize) -> Self
    {
        Self(steps)
    }
}

impl From<LoweringBudget> for usize
{
    /// The number of steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: LoweringBudget) -> Self
    {
        budget.0
    }
}

impl fmt::Display for LoweringBudget
{
    /// Writes the number of steps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// One lowering's remaining allowance.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Fuel
{
    /// How many steps are left.
    remaining: usize,
    /// The allowance the caller set, carried so a refusal can name it.
    budget: LoweringBudget,
}

impl Fuel
{
    /// A full tank at `budget`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(budget: LoweringBudget) -> Self
    {
        Self {
            remaining: budget.0,
            budget,
        }
    }

    /// Charge one step of work.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the remaining allowance is one lower on success, so a caller
    ///   that charges once per unit of work cannot outrun the allowance by more
    ///   than the unit it was charged for.
    /// - provides: the one place the allowance is spent, so no sweep can walk
    ///   uncharged.
    /// - fails: [`LoweringRefusal::BudgetExceeded`], naming the allowance the
    ///   caller set, once nothing remains; the tank stays empty, so every later
    ///   charge refuses alike.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance is spent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one checked subtraction, separated by the
    ///   boundary pair of the last successful charge and the first refused one
    ///   over an allowance of one, with the exact refusal variant and its
    ///   allowance asserted.
    /// - witness: `lower::tests::the_last_step_of_an_allowance_is_spendable`
    /// - witness: `lower::tests::a_step_past_the_allowance_is_refused`
    #[inline]
    pub fn spend<'refusal>(&mut self) -> Result<(), LoweringRefusal<'refusal>>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(LoweringRefusal::BudgetExceeded {
                budget: self.budget,
            });
        };
        self.remaining = remaining;

        Ok(())
    }
}

/// How a node's position reads it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Reading
{
    /// Not read: an own tile, layout, or a node under a form that refused.
    Unread,
    /// Read as a value type, under the binder frame named here.
    ValueType(Frame),
    /// Read as a computation type, under the binder frame named here.
    CompType(Frame),
    /// Read as a value, under the binder frame named here.
    Value(Frame),
    /// Read as a computation, under the binder frame named here.
    Computation(Frame),
    /// Read as an application's head: a computation under the binder frame
    /// named here, which a value standing here reaches by an inserted force.
    Head(Frame),
    /// Read as a function's result: a computation type under the binder frame
    /// named here, which a value type standing here reaches by an inserted
    /// returner.
    Result(Frame),
    /// Read as a function: the declaration form whose tail is one.
    Function,
}

impl Reading
{
    /// The sort a refusal at this position reports.
    ///
    /// # Specification
    /// trivial.
    const fn sort(self) -> FragmentSort
    {
        match self {
            | Self::Unread | Self::Function => FragmentSort::Declaration,
            | Self::ValueType(_frame) => FragmentSort::ValueType,
            | Self::CompType(_frame) | Self::Result(_frame) => FragmentSort::CompType,
            | Self::Value(_frame) => FragmentSort::Value,
            | Self::Computation(_frame) | Self::Head(_frame) => FragmentSort::Computation,
        }
    }

    /// The family of formers this reading admits.
    ///
    /// # Specification
    /// trivial.
    const fn family(self) -> Family
    {
        match self {
            | Self::Unread | Self::Function => Family::Neither,
            | Self::ValueType(_frame) | Self::CompType(_frame) | Self::Result(_frame) => {
                Family::Type
            },
            | Self::Value(_frame) | Self::Computation(_frame) | Self::Head(_frame) => Family::Term,
        }
    }

    /// The binder frame this reading is under, the outermost for a reading
    /// that names none.
    ///
    /// # Specification
    /// trivial.
    const fn frame(self) -> Frame
    {
        match self {
            | Self::Unread | Self::Function => Frame::Outermost,
            | Self::ValueType(frame)
            | Self::CompType(frame)
            | Self::Value(frame)
            | Self::Computation(frame)
            | Self::Head(frame)
            | Self::Result(frame) => frame,
        }
    }
}

/// The two families of formers, which never stand in each other's place.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Family
{
    /// Values and computations.
    Term,
    /// Value types and computation types.
    Type,
    /// Neither: a declaration or an attribute block.
    Neither,
}

/// The family `former` belongs to.
///
/// # Specification
/// trivial.
const fn family_of(former: Former) -> Family
{
    match former {
        | Former::Name
        | Former::Constructor
        | Former::Number
        | Former::Text
        | Former::Parenthesized
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Force
        | Former::Call
        | Former::Projection => Family::Term,
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::ParenthesizedType => Family::Type,
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Unadmitted => Family::Neither,
    }
}

/// The sort a former produces, which a position must demand.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Produced
{
    /// A value.
    Value,
    /// A computation.
    Computation,
    /// A value type.
    ValueType,
    /// A computation type.
    CompType,
}

/// What the mint sweep writes over a node's own core node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Bridge
{
    /// Nothing: the node's sort is the sort its position reads.
    Bare,
    /// The bridge from the node's sort to the one its position reads.
    Inserted(Insertion),
}

quenchant_shape::reason_enum! {
    /// Why a function's parameter or result carries no type.
    pub mod stated {
        /// The function tail leaves the type to a signature written apart.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The source wrote no `: T` after the binder, or no `-> T` after
            /// the parameter list.
            Unstated,
        }
    }
}

/// A stretch of one of the lowerer's flat stores, which a plan reads its list
/// from rather than owning one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Stretch
{
    /// The first entry.
    start: usize,
    /// One past the last entry.
    end: usize,
}

/// One `run x <- c ;` statement of a block.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Statement
{
    /// The `run` tile, the origin of the bind.
    run: NodeIndex,
    /// The computation whose returned value the statement binds.
    bound: NodeIndex,
}

/// A block: its statements, in source order, and its last computation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Block
{
    /// The block's statements, in the lowerer's statement store.
    statements: Stretch,
    /// The computation the block ends with.
    last: NodeIndex,
}

/// One parameter of a function tail.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Parameter
{
    /// The binder tile, the origin of the parameter's lambda and arrow.
    binder: NodeIndex,
    /// The frame the parameter binds, which says whether a type names it.
    frame: ScopeId,
    /// The parameter's type, when the source wrote one.
    declared: Maybe<NodeIndex, stated::Absent>,
}

/// A universe as the source wrote it: its sort and its level, each defaulted
/// when left off.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Universe
{
    /// The sort, `+` for the value types and `-` for the computation types.
    sort: GroundSort,
    /// The level.
    level: LevelConstant,
}

impl Universe
{
    /// The universe a bare `Type` names and an unwritten one defaults to:
    /// the value types at the fuss-free level.
    const FUSS_FREE: Self = Self {
        sort: GroundSort::Value,
        level: LevelConstant::ZERO,
    };
}

/// The code a decode reads its type from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Code
{
    /// A binder, named from a use site under the frame `from`, whose index is
    /// counted in the signature's telescope once every type has been read.
    Bound
    {
        /// The use site's frame.
        from: Frame,
        /// The binder's frame.
        binder: ScopeId,
    },
    /// A declaration at this admission position.
    Constant(ConstantIndex),
}

quenchant_shape::reason_enum! {
    /// Why a name resolves to nothing.
    pub mod named {
        /// Neither scope carries the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No enclosing binder and no earlier declaration is named so.
            Unresolved,
        }
    }
}

/// What a name resolved to.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Resolved
{
    /// An enclosing binder.
    Binder(Bound),
    /// A declaration strictly earlier than the name's own.
    Declaration
    {
        /// The declaration's admission position.
        constant: ConstantIndex,
        /// The type its signature was written with, when it has one.
        declared: Maybe<NodeIndex, binder_type::Absent>,
    },
}

impl Resolved
{
    /// The plan of the value the name stands for in term position.
    ///
    /// # Specification
    /// trivial.
    const fn term(self) -> Plan
    {
        match self {
            | Self::Binder(bound) => Plan::Variable(bound.index),
            | Self::Declaration { constant, .. } => Plan::Constant(constant),
        }
    }
}

/// A function tail's reading: `(params) -> T? { … }`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Function
{
    /// The parameters, in the lowerer's parameter store.
    parameters: Stretch,
    /// The result type, when the source wrote one.
    result: Maybe<NodeIndex, stated::Absent>,
    /// The body.
    block: Block,
}

/// What the mint sweep does for one node, decided by the classification.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Plan
{
    /// Mint nothing.
    Unplanned,
    /// A variable at this index.
    Variable(DeBruijnIndex),
    /// A constant at this admission position.
    Constant(ConstantIndex),
    /// The unit value.
    Unit,
    /// A literal, already parsed from the node's own text.
    Literal(Literal),
    /// A nullary type atom.
    Atom(TypeAtom),
    /// A universe.
    Universe(Universe),
    /// The type a code denotes, in the universe it was declared at.
    Decode(Code, Universe),
    /// A type former over its argument.
    Former(TypeFormer, NodeIndex),
    /// An arrow over its domain and codomain.
    Arrow(NodeIndex, NodeIndex),
    /// Adopt the child's lowered node unchanged.
    Transparent(NodeIndex),
    /// A thunk over its block.
    Thunk(Block),
    /// A returner over its value.
    Return(NodeIndex),
    /// A force over its value.
    Force(NodeIndex),
    /// A lambda over its block.
    Lambda(Block),
    /// An application of its head to its arguments, left to right, in the
    /// lowerer's operand store.
    Application(NodeIndex, Stretch),
    /// A function tail's declared type and body.
    Function(Function),
}

/// A node's lowered core node, at the sort its own form produced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Lowered
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
    /// A function tail: its declared type, when it states one, and its body.
    Function
    {
        /// `+U (A1 -> … -> An -> C)`, from the parameter and result types.
        signature: Maybe<ValueTypeId, lowered::Absent>,
        /// `thunk (λ … λ. block)`.
        body: ValueId,
    },
}

/// Whether a form can stand where a value is expected.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct ValueForm(bool);

/// Whether a spelling is a numeric lexeme with a fraction or an exponent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Fractional(bool);

/// Whether a node lies inside an attribute payload, which lowers whatever
/// its declaration's outcome.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct InPayload(bool);

/// One form being classified: where it stands, what it is called, and how
/// its position reads it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Site
{
    /// The form.
    at: Placed,
    /// The form's kind, as a diagnostic writes it.
    name: FormName,
    /// How the form's position reads it.
    reading: Reading,
}

impl Site
{
    /// The refusal this form earns for leaving the fragment by `boundary`.
    ///
    /// # Specification
    /// trivial.
    const fn out<'source>(
        self,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        self.folded(self.name, boundary)
    }

    /// The refusal this form earns as the folded form `form`.
    ///
    /// # Specification
    /// trivial.
    const fn folded<'source>(
        self,
        form: FormName,
        boundary: FragmentBoundary,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::OutOfFragment {
            span: self.at.span,
            form,
            sort: self.reading.sort(),
            boundary,
        }
    }

    /// The refusal this form earns for `fault` at `span`.
    ///
    /// # Specification
    /// trivial.
    const fn fault<'source>(
        self,
        span: ByteSpan,
        fault: FormFault,
    ) -> LoweringRefusal<'source>
    {
        LoweringRefusal::MalformedForm {
            span,
            form: self.name,
            fault,
        }
    }

    /// The operand a one-operand hole holds, or the fault its run earns.
    ///
    /// # Specification
    /// - requires: `run` is a hole of this form.
    /// - ensures: the operand of a one-operand run; an empty run is a missing
    ///   operand at its gap, and a longer run an extra operand at its second.
    /// - provides: the one-hole reading every former shares.
    /// - fails: yields the missing-operand or extra-operand refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a hole not holding one form.
    const fn one<'source>(
        self,
        run: Run,
    ) -> Result<Placed, LoweringRefusal<'source>>
    {
        match run {
            | Run::One(operand) => Ok(operand),
            | Run::Empty(gap) => Err(self.fault(gap, FormFault::MissingOperand)),
            | Run::Several { extra, .. } => Err(self.fault(extra.span, FormFault::ExtraOperand)),
        }
    }
}

/// The lowering's working state, shared by both sweeps.
struct Lowerer<'run, 'source>
{
    /// The grammar the tree was molded under.
    pbg: &'run Pbg,
    /// The tree being lowered.
    tree: &'run SyntaxTree<'source>,
    /// The module's declarations and the slot each node belongs to.
    collected: Collected<'source>,
    /// How each node's position reads it.
    readings: Vec<Reading>,
    /// What the mint sweep does for each node.
    plans: Vec<Plan>,
    /// What the mint sweep writes over each node's own core node.
    bridges: Vec<Bridge>,
    /// Each node's lowered core node.
    lowered: Vec<Maybe<Lowered, lowered::Absent>>,
    /// Which nodes lie inside an attribute payload.
    payload: Vec<InPayload>,
    /// The manifest type components each node sees, where it lies in a
    /// module signature.
    scopes: Vec<Maybe<ComponentScope, scoped::Absent>>,
    /// Each type head that named a manifest type component, with the held
    /// slot owning that component's type.
    manifests: Vec<(SlotIndex, NodeIndex)>,
    /// Each exported value component's full path, with the member's slot.
    exported: BTreeMap<NamePath, SlotIndex>,
    /// Each witness's body, by slot.
    witnessed: BTreeMap<SlotIndex, ValueId>,
    /// The arguments every planned application reads, stretch by stretch.
    operands: Vec<NodeIndex>,
    /// The statements every planned block reads, stretch by stretch.
    statements: Vec<Statement>,
    /// The parameters every planned function reads, stretch by stretch.
    parameters: Vec<Parameter>,
    /// The binder frames the lambdas, the parameters and the statements
    /// extended.
    scope: Scope<'source>,
    /// The outermost scope every declared name is declared in and every
    /// binder is reported against.
    recognition: Recognition,
    /// The remaining allowance.
    fuel: Fuel,
    /// The scratch reading of the form being classified.
    pieces: Pieces,
    /// The scratch reading of a written universe a decode reads its sort and
    /// level from.
    scratch: Pieces,
}

/// Where the mint sweep writes: the arena and the origin table.
struct Sink<'run>
{
    /// The arena the core nodes are minted into.
    arena: &'run mut CoreArena,
    /// The table every minted node's origin is recorded in.
    origins: &'run mut OriginTable,
}

/// Lower one module into `arena`, declaring its names over `outermost`.
///
/// # Specification
/// - requires: `tree` was molded under `pbg` over the source being lowered;
///   `arena` is the arena the lowered module's ids are read against; `budget`
///   bounds the work; `outermost` holds the seed tables and the shadow policy
///   the module's names are declared against.
/// - ensures: one declaration per distinct declared name, in admission order,
///   each carrying its admission position, the content identity of each of its
///   declaration forms, an origin token, and what its declarations amount to —
///   a completed pair, an uncompleted signature, a bodiless definition, or the
///   declaration's first refusal by arena position; a function tail is a
///   definition, and a signature too when it types every parameter and its
///   result. Every core node the module minted has an origin recorded, terms
///   and types alike, the force, thunk, returner, quote and decode the lowering
///   inserted marked as inserted, and every attribute the module carries is
///   resolved against the registry and filed under the content identity of the
///   declaration form it decorates. Every import is kept in source order with
///   its alias bound in the import scope and no address resolved. Every
///   declared name is declared over `outermost` in admission order, tagged with
///   its name's bytes, and every lambda, parameter and `run` binder is reported
///   against it; the outermost scope is returned with the module.
/// - provides: the whole surface-to-core step, in one pass over one tree with
///   one strictness and one verdict per name.
/// - fails: [`LoweringRefusal::GrammarMismatch`] when the tree was molded under
///   another grammar; [`LoweringRefusal::OutOfFragment`] and
///   [`LoweringRefusal::MalformedForm`] when the module's own shape is wrong —
///   a root that is not a module, a root child that is neither a declaration
///   nor an import, a declaration with no name, an import out of shape, or an
///   attribute block decorating nothing;
///   [`LoweringRefusal::DuplicateImportAlias`] when two imports bind one alias;
///   [`LoweringRefusal::UnknownMold`] for a mold `pbg` does not hold; and
///   [`LoweringRefusal::BudgetExceeded`] when the work outruns `budget`. A
///   refusal inside a declaration is carried by that declaration instead —
///   [`LoweringRefusal::ShadowedBuiltin`], a declared name or a binder over a
///   builtin under the reject policy, included — so one bad declaration does
///   not hide the rest of the module.
/// - panics: none. Every tree lookup is checked and a position the tree does
///   not hold contributes nothing.
///
/// # Errors
/// [`LoweringRefusal::GrammarMismatch`] for a tree of another grammar,
/// [`LoweringRefusal::OutOfFragment`], [`LoweringRefusal::MalformedForm`] and
/// [`LoweringRefusal::DuplicateImportAlias`] for a module whose own shape is
/// not a list of declarations and well-formed imports,
/// [`LoweringRefusal::UnknownMold`] for a foreign mold, and
/// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
///
/// # Adequacy
/// - hypothesis: L2 for the shape of what is produced — every accepted source
///   is parsed by the real parser and lowered, and each declaration's lowered
///   ids are read back out of the arena it wrote into and asserted as the exact
///   core node, an oracle outside the lowering; L3 for the residue — one
///   witness per refusal variant on a boundary-biased source, asserting the
///   exact variant, its span and its classification, plus the admission-order
///   and origin-coverage postconditions asserted over a multi-declaration
///   module.
/// - witness: `lower::tests::a_completed_declaration_lowers_both_halves`
/// - witness: `lower::tests::an_uncompleted_signature_is_the_obligation_producer`
/// - witness: `lower::tests::a_bodiless_definition_lowers_its_body_alone`
/// - witness: `lower::tests::the_thunk_and_returner_heads_lower_to_their_formers`
/// - witness: `lower::tests::an_arrow_lowers_under_a_thunk_type`
/// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
/// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
/// - witness: `lower::tests::u_and_f_are_names`
/// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
/// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
/// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
/// - witness: `lower::tests::the_producer_does_not_admit_a_graded_bridge`
/// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
/// - witness: `lower::tests::a_lambda_body_binds_its_own_de_bruijn_index`
/// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
/// - witness: `lower::tests::the_empty_parentheses_lower_to_the_unit_value`
/// - witness: `lower::tests::an_identifier_spelled_unit_is_an_ordinary_name`
/// - witness: `lower::tests::a_grouping_lowers_to_what_it_wraps`
/// - witness: `lower::tests::a_text_literal_lowers_with_its_escapes_decoded`
/// - witness: `lower::tests::force_and_application_lower_over_their_children`
/// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
/// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
/// - witness: `lower::tests::a_tail_missing_a_type_writes_its_definition_alone`
/// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
/// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
/// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
/// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
/// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
/// - witness: `lower::tests::a_self_reference_is_unresolved`
/// - witness: `lower::tests::an_undefined_term_name_is_refused`
/// - witness: `lower::tests::an_undefined_type_head_is_refused`
/// - witness: `lower::tests::an_applied_nullary_head_is_refused`
/// - witness: `lower::tests::an_applied_head_no_former_answers_is_refused`
/// - witness: `lower::tests::the_reserved_product_is_declined`
/// - witness: `lower::tests::the_reserved_pair_is_declined`
/// - witness: `lower::tests::an_arrow_at_declaration_sort_is_refused`
/// - witness: `lower::tests::a_lambda_in_value_position_is_refused`
/// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
/// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
/// - witness: `lower::tests::a_malformed_integer_literal_is_refused`
/// - witness: `lower::tests::a_malformed_text_literal_is_refused`
/// - witness: `lower::tests::a_repaired_declaration_is_refused`
/// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
/// - witness: `lower::tests::a_tile_out_of_place_is_refused`
/// - witness: `lower::tests::a_root_that_is_not_a_module_is_refused`
/// - witness: `lower::tests::a_tree_of_another_grammar_is_refused`
/// - witness: `lower::tests::a_mold_the_grammar_does_not_hold_is_refused`
/// - witness: `lower::tests::an_unknown_attribute_is_refused_with_its_suggestion`
/// - witness: `lower::tests::an_attribute_written_twice_for_one_name_is_refused`
/// - witness: `lower::tests::a_schema_taking_a_payload_refuses_an_absent_one`
/// - witness: `lower::tests::a_non_value_payload_is_refused`
/// - witness: `lower::tests::a_payload_of_the_wrong_form_is_refused`
/// - witness: `lower::tests::a_marker_given_a_payload_is_refused`
/// - witness: `lower::tests::an_attribute_is_filed_under_its_declaration_digest`
/// - witness: `lower::tests::a_refused_declarations_attributes_are_filed_under_its_digest`
/// - witness: `lower::tests::the_attribute_diagnostics_fire_on_a_refused_declaration`
/// - witness: `lower::tests::every_minted_node_has_an_origin`
/// - witness: `lower::tests::a_refused_declaration_leaves_the_others_lowered`
/// - witness: `lower::tests::a_module_past_the_allowance_is_refused`
/// - witness: `namespace::namespace::source_import_reaches_the_namespace_engine_and_exposes_its_alias`
/// - witness: `namespace::namespace::an_import_binds_its_alias_and_resolves_no_address`
/// - witness: `namespace::namespace::source_import_without_alias_becomes_a_refusal`
/// - witness: `namespace::namespace::duplicate_source_import_alias_becomes_a_refusal`
/// - witness: `recognition::recognition::a_shadowed_builtin_is_reported_as_a_warning`
/// - witness: `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
/// - witness: `recognition::recognition::user_shadowing_is_the_only_observable_delta`
/// - witness: `recognition::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
#[inline]
pub fn lower_module<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    arena: &mut CoreArena,
    budget: LoweringBudget,
    outermost: Recognition,
) -> Result<LoweredModule<'source>, LoweringRefusal<'source>>
{
    if tree.grammar() != pbg.fingerprint() {
        return Err(LoweringRefusal::GrammarMismatch {
            tree: tree.grammar(),
            grammar: pbg.fingerprint(),
        });
    }
    let empty = |outermost| {
        LoweredModule::new(
            Vec::new(),
            Vec::new(),
            AttributeTable::new(),
            OriginTable::new(),
            ModuleImports::new(),
            outermost,
        )
    };
    let Some(root) = tree.node(tree.root())
    else {
        return Ok(empty(outermost));
    };
    match shape_of(pbg, root)? {
        | Shape::Root => {},
        | Shape::Layout => return Ok(empty(outermost)),
        | Shape::Form { name, .. } => {
            return Err(LoweringRefusal::OutOfFragment {
                span: root.span(),
                form: name,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            });
        },
        | Shape::Repair(repair) => {
            return Err(LoweringRefusal::MalformedForm {
                span: root.span(),
                form: FormName::ROOT,
                fault: FormFault::Repaired(repair),
            });
        },
    }
    let mut fuel = Fuel::new(budget);
    let collected = collect(pbg, tree, &mut fuel)?;
    let mut lowerer = Lowerer::new(pbg, tree, collected, fuel, outermost);
    lowerer.declare();
    lowerer.seed()?;
    lowerer.classify()?;
    lowerer.propagate_manifests();
    let mut origins = OriginTable::new();
    lowerer.mint(&mut Sink {
        arena,
        origins: &mut origins,
    })?;
    let mut attributes = AttributeTable::new();
    lowerer.attribute(&mut attributes)?;
    let declarations = lowerer.assemble(&mut origins);
    let structures = lowerer.structures();
    let Lowerer {
        collected,
        recognition,
        ..
    } = lowerer;

    Ok(LoweredModule::new(
        declarations,
        structures,
        attributes,
        origins,
        collected.imports,
        recognition,
    ))
}

impl<'run, 'source> Lowerer<'run, 'source>
{
    /// The state for lowering `tree`, everything unread.
    ///
    /// # Specification
    /// trivial.
    fn new(
        pbg: &'run Pbg,
        tree: &'run SyntaxTree<'source>,
        collected: Collected<'source>,
        fuel: Fuel,
        recognition: Recognition,
    ) -> Self
    {
        let count = usize::from(tree.node_count());
        let mut readings = Vec::new();
        readings.resize(count, Reading::Unread);
        let mut plans = Vec::new();
        plans.resize(count, Plan::Unplanned);
        let mut bridges = Vec::new();
        bridges.resize(count, Bridge::Bare);
        let mut lowered = Vec::new();
        lowered.resize(count, Maybe::Absent(lowered::Absent::Unminted));
        let mut payload = Vec::new();
        payload.resize(count, InPayload(false));
        let mut scopes = Vec::new();
        scopes.resize(count, Maybe::Absent(scoped::Absent::Unscoped));

        Self {
            pbg,
            tree,
            collected,
            readings,
            plans,
            bridges,
            lowered,
            payload,
            scopes,
            manifests: Vec::new(),
            exported: BTreeMap::new(),
            witnessed: BTreeMap::new(),
            operands: Vec::new(),
            statements: Vec::new(),
            parameters: Vec::new(),
            scope: Scope::new(),
            recognition,
            fuel,
            pieces: Pieces::new(),
            scratch: Pieces::new(),
        }
    }

    /// Declare every top-level name over the outermost scope: each top-level
    /// declaration, then each top-level module with the namespace it exports.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: each top-level declaration is declared as a definition, and
    ///   each top-level module as a namespace governing exactly the components
    ///   it exports — a value component as a component, a nested module as a
    ///   namespace of its own, walked by an explicit worklist — each tagged
    ///   with its name tile's bytes and displacing the builtin subtree it lands
    ///   on; every exported value component's full path is recorded with its
    ///   member. A declaration the shadow policy refuses holds
    ///   [`LoweringRefusal::ShadowedBuiltin`] at its name, offered at its
    ///   declaration form, and a module so refused files a held slot carrying
    ///   it; the scope keeps the builtin. Module members and hidden members are
    ///   declared nowhere in the outermost scope.
    /// - provides: the outermost half of the module's names, and the governance
    ///   of every module path.
    /// - fails: never; a refusal is carried by its declaration.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration over a builtin under each policy and
    ///   over nothing, asserted as the exact record, outcome and resolution; a
    ///   module exporting a component, hiding a member and exporting a nested
    ///   module, each path asserted as the exact resolution.
    /// - witness: `recognition::recognition::a_shadowed_builtin_is_reported_as_a_warning`
    /// - witness: `recognition::recognition::a_declaration_shadowing_a_builtin_is_rejected_under_policy`
    /// - witness: `recognition::recognition::user_shadowing_is_the_only_observable_delta`
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_hidden_member_is_admitted_and_absent_from_the_namespace`
    fn declare(&mut self)
    {
        for slot in &mut self.collected.slots {
            if slot.container != Container::TopLevel || slot.role != Role::Declared {
                continue;
            }
            let site = slot.named.span;
            let mut subtree = Trie::empty();
            let _fresh = subtree.insert(
                &NamePath::root(),
                Binding::new(Recognized::Definition, RecognitionSite::Source(site)),
            );
            let declared =
                self.recognition
                    .declare(Segment::from(slot.name.as_ref()), subtree, site);
            if let Err(_refused) = declared {
                slot.refuse(slot.introduced_by.node, LoweringRefusal::ShadowedBuiltin {
                    span: site,
                    name: slot.name,
                });
            }
        }
        let tops: Vec<StructureIndex> = self
            .collected
            .structures
            .iter()
            .enumerate()
            .filter(|&(_position, structure)| structure.container == Container::TopLevel)
            .map(|(position, _structure)| StructureIndex::from(position))
            .collect();
        for top in tops {
            self.declare_module(top);
        }
    }

    /// Declare the top-level module at `top` with the namespace it exports.
    ///
    /// # Specification
    /// - requires: `top` names a closed top-level module.
    /// - ensures: as [`Self::declare`] for one module.
    /// - provides: the per-module half of [`Self::declare`].
    /// - fails: never.
    /// - panics: none.
    fn declare_module(
        &mut self,
        top: StructureIndex,
    )
    {
        let Some(module) = self.collected.structures.get(usize::from(top))
        else {
            return;
        };
        let (name, named, declared_by) = (module.name, module.named, module.declared_by);
        let root = NamePath::from(Vec::from([Segment::from(name.as_ref())]));
        let mut subtree = Trie::empty();
        let _root = subtree.insert(
            &NamePath::root(),
            Binding::new(
                Recognized::ModuleNamespace,
                RecognitionSite::Source(named.span),
            ),
        );
        let mut work = Vec::from([(top, NamePath::root())]);
        while let Some((structure, relative)) = work.pop() {
            let Some(entry) = self.collected.structures.get(usize::from(structure))
            else {
                continue;
            };
            for &export in &entry.exports {
                let (segment, site, recognized) = match export {
                    | Member::Slot(slot) => {
                        let Some(member) = self.collected.slots.get(usize::from(slot))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleComponent)
                    },
                    | Member::Module(nested) => {
                        let Some(member) = self.collected.structures.get(usize::from(nested))
                        else {
                            continue;
                        };
                        (member.name, member.named.span, Recognized::ModuleNamespace)
                    },
                };
                let path = relative.extended(&NamePath::from(Vec::from([Segment::from(
                    segment.as_ref(),
                )])));
                let _fresh = subtree.insert(
                    &path,
                    Binding::new(recognized, RecognitionSite::Source(site)),
                );
                match export {
                    | Member::Slot(slot) => {
                        let _replaced = self.exported.insert(root.extended(&path), slot);
                    },
                    | Member::Module(nested) => work.push((nested, path)),
                }
            }
        }
        let declared = self
            .recognition
            .declare(Segment::from(name.as_ref()), subtree, named.span);
        if let Err(_refused) = declared {
            let held = SlotIndex::from(self.collected.slots.len());
            let mut slot = DeclarationSlot {
                name,
                container: Container::TopLevel,
                role: Role::Held,
                constant: ConstantIndex::from(usize::from(held)),
                introduced_by: declared_by,
                named,
                signature: Maybe::Absent(declaration_half::Absent::Unwritten),
                definition: Maybe::Absent(declaration_half::Absent::Unwritten),
                attributes: Vec::new(),
                refusal: Maybe::Absent(slot_refusal::Absent::Unrefused),
            };
            slot.refuse(declared_by.node, LoweringRefusal::ShadowedBuiltin {
                span: named.span,
                name,
            });
            self.collected.slots.push(slot);
        }
    }

    /// Report the binder `binder`, spelling `name`, against the outermost
    /// scope.
    ///
    /// # Specification
    /// - requires: `binder` is a lambda, parameter or `run` binder.
    /// - ensures: a binder over a builtin root is recorded under
    ///   warn-and-allow; the outermost scope is never changed.
    /// - provides: the binder half of the outermost report.
    /// - fails: [`LoweringRefusal::ShadowedBuiltin`] at the binder for a
    ///   builtin root under the reject policy.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ShadowedBuiltin`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lambda binder over a builtin under each policy,
    ///   asserted as the exact record and outcome.
    /// - witness: `recognition::recognition::a_binder_shadowing_a_builtin_is_rejected_under_policy`
    fn note_binder(
        &mut self,
        binder: Placed,
        name: SurfaceName<'source>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let noted = self
            .recognition
            .note_binder(Segment::from(name.as_ref()), binder.span);
        match noted {
            | Ok(()) => Ok(()),
            | Err(_refused) => Err(LoweringRefusal::ShadowedBuiltin {
                span: binder.span,
                name,
            }),
        }
    }

    /// Read every declaration's operands at the sort the declaration demands.
    ///
    /// # Specification
    /// - requires: the collection pass has run.
    /// - ensures: a signature's type is read as a value type, a definition's
    ///   body as a value in the outermost frame, a function tail's declaration
    ///   form as a function, which reads both halves it wrote at once, a
    ///   manifest type component's type as a value type, and an attribute's
    ///   payload as a value when its form can stand as one; a witness's body, a
    ///   member rather than a form, is read nowhere. Every other node stays
    ///   unread. Every written payload is marked as one, whatever its form, and
    ///   every signature type's root with the manifest components it sees.
    /// - provides: the entry points of the ascending sweep.
    /// - fails: [`LoweringRefusal::UnknownMold`] for a payload of a mold the
    ///   grammar does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::UnknownMold`] for a foreign mold.
    fn seed(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        let mut seeds: Vec<(NodeIndex, Reading)> = Vec::new();
        let mut payloads: Vec<NodeIndex> = Vec::new();
        for structure in &self.collected.structures {
            for manifest in &structure.types {
                seeds.push((manifest.defined.node, Reading::ValueType(Frame::Outermost)));
            }
        }
        for &(root, seen) in &self.collected.scopes {
            if let Some(held) = self.scopes.get_mut(usize::from(root)) {
                *held = Maybe::Present(seen);
            }
        }
        for slot in &self.collected.slots {
            if let Maybe::Present(half) = slot.signature
                && let Operand::Written(operand) = half.operand
            {
                seeds.push((operand.node, Reading::ValueType(Frame::Outermost)));
            }
            if let Maybe::Present(half) = slot.definition {
                match half.operand {
                    | Operand::Written(operand) => {
                        seeds.push((operand.node, Reading::Value(Frame::Outermost)));
                    },
                    | Operand::Function => {
                        seeds.push((half.declaration.node, Reading::Function));
                    },
                    | Operand::Member(_) => {},
                }
            }
            for written in &slot.attributes {
                let Payload::Written(payload) = written.payload
                else {
                    continue;
                };
                payloads.push(payload.node);
                let (_shape, value) = self.payload_former(payload)?;
                if value.0 {
                    seeds.push((payload.node, Reading::Value(Frame::Outermost)));
                }
            }
        }
        for (position, reading) in seeds {
            self.read(position, reading);
        }
        for position in payloads {
            if let Some(held) = self.payload.get_mut(usize::from(position)) {
                *held = InPayload(true);
            }
        }

        Ok(())
    }

    /// The form a payload is written as, and whether it can stand as a value.
    ///
    /// # Specification
    /// trivial.
    fn payload_former(
        &self,
        payload: Placed,
    ) -> Result<(Shape, ValueForm), LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(payload.node)
        else {
            return Ok((Shape::Layout, ValueForm(false)));
        };
        let shape = shape_of(self.pbg, node)?;
        let value = match shape {
            | Shape::Form { former, .. } => is_value_form(former),
            | Shape::Root | Shape::Repair(_) | Shape::Layout => ValueForm(false),
        };

        Ok((shape, value))
    }

    /// The ascending sweep: classify every read node and plan its mint.
    ///
    /// # Specification
    /// - requires: the seeds have been read.
    /// - ensures: every node carries the reading its parent fixed, the owner
    ///   its parent belongs to and its parent's payload mark, every read form
    ///   has its plan or has offered its refusal to the declaration that owns
    ///   it, and a node under a form that refused stays unread, so a refusal
    ///   costs its subtree nothing.
    /// - provides: everything the mint sweep needs, so the mint sweep decides
    ///   nothing and can fail at nothing.
    /// - fails: every engine fault — [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] — aborts the sweep; every other
    ///   refusal is offered to its declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    fn classify(&mut self) -> Result<(), LoweringRefusal<'source>>
    {
        for position in self.tree.positions() {
            self.fuel.spend()?;
            self.inherit_owner(position);
            self.inherit_payload(position);
            self.inherit_scope(position);
            if let Err(refusal) = self.classify_node(position) {
                if refusal.classify() == FailureClass::EngineFault {
                    return Err(refusal);
                }
                self.collected.offer(position, refusal);
            }
        }

        Ok(())
    }

    /// Give every unowned child of `position` the declaration its parent
    /// belongs to.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   owner is already set when its children are reached.
    /// - ensures: every child of an owned node is owned by the same slot,
    ///   unless the collection pass gave it an owner of its own — a signature
    ///   type written inside a member signature it does not type — so a refusal
    ///   anywhere under a declaration reaches the declaration its type or body
    ///   belongs to.
    /// - provides: the ownership half of the one-refusal-per-declaration rule.
    /// - fails: never.
    /// - panics: none.
    fn inherit_owner(
        &mut self,
        position: NodeIndex,
    )
    {
        let Maybe::Present(slot) = self.collected.owner_of(position)
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Maybe::Absent(_) = self.collected.owner_of(child) {
                self.collected.own(child, slot);
            }
        }
    }

    /// Give every child of `position` the manifest type components `position`
    /// sees.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   scope is already set when its children are reached.
    /// - ensures: every node under a signature type's root sees that root's
    ///   manifest components, an inner root keeping its own.
    /// - provides: the scope a type head inside a signature resolves against.
    /// - fails: never.
    /// - panics: none.
    fn inherit_scope(
        &mut self,
        position: NodeIndex,
    )
    {
        let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(position))
        else {
            return;
        };
        for child in self.tree.children(position) {
            if let Some(held) = self.scopes.get_mut(usize::from(child))
                && let Maybe::Absent(_) = *held
            {
                *held = Maybe::Present(seen);
            }
        }
    }

    /// Mark every child of `position` as inside a payload when `position` is.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order, so its own
    ///   mark is already set when its children are reached.
    /// - ensures: every node under a written payload carries the mark, so the
    ///   mint sweep can tell a payload's subtree from the rest of its
    ///   declaration.
    /// - provides: the payload half of what the mint sweep skips.
    /// - fails: never.
    /// - panics: none.
    fn inherit_payload(
        &mut self,
        position: NodeIndex,
    )
    {
        if !self.in_payload(position).0 {
            return;
        }
        for child in self.tree.children(position) {
            if let Some(held) = self.payload.get_mut(usize::from(child)) {
                *held = InPayload(true);
            }
        }
    }

    /// Whether `position` lies inside an attribute payload.
    ///
    /// # Specification
    /// trivial.
    fn in_payload(
        &self,
        position: NodeIndex,
    ) -> InPayload
    {
        self.payload
            .get(usize::from(position))
            .copied()
            .unwrap_or(InPayload(false))
    }

    /// Classify one node at the reading its parent fixed.
    ///
    /// # Specification
    /// - requires: `position` is visited in ascending arena order.
    /// - ensures: an unread node, an own tile, layout and repairs are skipped;
    ///   a read form is checked in the crate's one order and either planned,
    ///   with its operands read at the sorts it demands, or refused.
    /// - provides: the per-node half of [`Self::classify`].
    /// - fails: yields the form's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    fn classify_node(
        &mut self,
        position: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let reading = self.reading(position);
        if reading == Reading::Unread {
            return Ok(());
        }
        let Some(node) = self.tree.node(position)
        else {
            return Ok(());
        };
        let Shape::Form { name, former } = shape_of(self.pbg, node)?
        else {
            return Ok(());
        };
        let site = Site {
            at: Placed::of(position, node),
            name,
            reading,
        };
        if former == Former::Unadmitted {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }
        let mut pieces = core::mem::take(&mut self.pieces);
        let outcome = read_pieces(self.pbg, self.tree, position, &mut pieces)
            .and_then(|()| self.classify_form(site, former, &pieces));
        self.pieces = pieces;

        outcome
    }

    /// Classify one read form over its pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of the form at `site`.
    /// - ensures: a repair refuses the form; a former of the wrong family for
    ///   the position refuses as the wrong sort, except a type standing where a
    ///   value is read, which is quoted; every other former is handed to its
    ///   own reader, a declaration form to the function reader, the one reading
    ///   of the family that seeds one.
    /// - provides: the dispatch on the grammar's named kind.
    /// - fails: yields the form's first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's first refusal.
    fn classify_form(
        &mut self,
        site: Site,
        former: Former,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        if let Maybe::Present(repaired) = pieces.repair {
            return Err(site.fault(repaired.span, FormFault::Repaired(repaired.repair)));
        }
        let family = family_of(former);
        let quoted = family == Family::Type && matches!(site.reading, Reading::Value(_));
        if family != site.reading.family() && !quoted {
            return Err(site.out(FragmentBoundary::WrongSort));
        }
        let cursor = Cursor::new(&pieces.pieces, site.at.span);
        match former {
            | Former::Name => self.name(site),
            | Former::Constructor => self.constructor(site),
            | Former::Number => self.number(site),
            | Former::Text => self.text(site, pieces),
            | Former::Parenthesized => self.parenthesized(site, cursor),
            | Former::Thunk => self.thunk(site, cursor),
            | Former::Lambda => self.lambda(site, cursor),
            | Former::Return => self.keyed(site, cursor, TileName::RET),
            | Former::Force => self.keyed(site, cursor, TileName::FORCE),
            | Former::Call => self.call(site, cursor),
            | Former::Projection => self.projection(site, pieces),
            | Former::TypeHead => self.type_head(site),
            | Former::Universe => self.universe(site, cursor),
            | Former::TypeApplication => self.type_application(site, cursor),
            | Former::ThunkType | Former::ReturnerType => self.formed_type(site, cursor),
            | Former::ArrowType => self.arrow(site, cursor),
            | Former::ProductType => Err(site.out(FragmentBoundary::Reserved)),
            | Former::ParenthesizedType => self.parenthesized_type(site, cursor),
            | Former::Declaration | Former::Module => self.function(site, cursor),
            | Former::AttributeBlock | Former::Import | Former::Unadmitted => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
        }
    }

    /// The binder frame of a form whose position demands `produced`, with the
    /// bridge the position writes over it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame the position carries when it reads the produced
    ///   sort. An application's head reads a computation and reaches a value by
    ///   a force; a function's result reads a computation type and reaches a
    ///   value type by a returner; a value position reaches a type of either
    ///   sort by a quote; the bridge is recorded for the form's node, and every
    ///   other match records none.
    /// - provides: the sort check every former takes, and the three insertions
    ///   decided by the sort of a position.
    /// - fails: yields the wrong-sort refusal when the position reads another
    ///   sort no bridge reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each bridge separated from its bare neighbour: a
    ///   value and a computation at a head, a value type and a computation type
    ///   at a result, a value and a type at a value, each asserted through the
    ///   lowered node and its origin's provenance.
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    /// - witness: `lower::tests::an_author_written_force_is_not_marked_inserted`
    /// - witness: `lower::tests::a_positive_result_gains_a_returner_once`
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    fn require(
        &mut self,
        site: Site,
        produced: Produced,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let (frame, bridge) = match (site.reading, produced) {
            | (Reading::Value(frame), Produced::Value)
            | (Reading::Computation(frame) | Reading::Head(frame), Produced::Computation)
            | (Reading::ValueType(frame), Produced::ValueType)
            | (Reading::CompType(frame) | Reading::Result(frame), Produced::CompType) => {
                (frame, Bridge::Bare)
            },
            | (Reading::Head(frame), Produced::Value) => {
                (frame, Bridge::Inserted(Insertion::Force))
            },
            | (Reading::Result(frame), Produced::ValueType) => {
                (frame, Bridge::Inserted(Insertion::Returner))
            },
            | (Reading::Value(frame), Produced::ValueType | Produced::CompType) => {
                (frame, Bridge::Inserted(Insertion::Quote))
            },
            | _ => return Err(site.out(FragmentBoundary::WrongSort)),
        };
        if let Some(held) = self.bridges.get_mut(usize::from(site.at.node)) {
            *held = bridge;
        }

        Ok(frame)
    }

    /// What `name`, written at `site` under `frame`, resolves to: the
    /// innermost binder carrying it, else a declaration strictly earlier than
    /// the one `site` belongs to, searched from that declaration's own module
    /// outward to the top level.
    ///
    /// # Specification
    /// - requires: `site` is the name's own node.
    /// - ensures: the binder with its index and its written type; else the
    ///   first module, innermost first, whose body declares the name: its
    ///   member when that member's admission position is strictly earlier, and
    ///   the forward-member refusal when it is not; else a top-level
    ///   declaration strictly earlier, with its admission position and its
    ///   signature's written type; the unresolved absence when nothing answers.
    /// - provides: the one resolution term names, capitalised names and type
    ///   heads share.
    /// - fails: [`LoweringRefusal::ForwardMemberReference`] for a member of an
    ///   enclosing module declared at or after the referring declaration;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`] and
    /// [`LoweringRefusal::BudgetExceeded`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a member named by an earlier sibling, by a later one,
    ///   by itself, from a nested module and from the top level, each asserted
    ///   as the exact constant or refusal.
    /// - witness: `modules::modules::a_forward_member_reference_is_refused_by_position`
    /// - witness: `modules::modules::a_backward_member_reference_resolves`
    /// - witness: `lower::tests::a_self_reference_is_unresolved`
    /// - witness: `lower::tests::an_earlier_declaration_resolves_as_a_constant`
    fn resolve_name(
        &mut self,
        site: Site,
        frame: Frame,
        name: SurfaceName<'source>,
    ) -> Result<Maybe<Resolved, named::Absent>, LoweringRefusal<'source>>
    {
        if let Maybe::Present(bound) = self.scope.resolve(frame, name, &mut self.fuel)? {
            return Ok(Maybe::Present(Resolved::Binder(bound)));
        }
        let Maybe::Present(own) = self.collected.owner_of(site.at.node)
        else {
            return Ok(Maybe::Absent(named::Absent::Unresolved));
        };
        let mut container = self
            .collected
            .slots
            .get(usize::from(own))
            .map_or(Container::TopLevel, |slot| slot.container);
        loop {
            self.fuel.spend()?;
            if let Some(&target) = self.collected.by_name.get(&(container, name))
                && let Some(entry) = self.collected.slots.get(usize::from(target))
            {
                if target < own {
                    let declared = match entry.signature {
                        | Maybe::Present(Half {
                            operand: Operand::Written(written),
                            ..
                        }) => Maybe::Present(written.node),
                        | Maybe::Present(_) | Maybe::Absent(_) => {
                            Maybe::Absent(binder_type::Absent::Untyped)
                        },
                    };
                    return Ok(Maybe::Present(Resolved::Declaration {
                        constant: entry.constant,
                        declared,
                    }));
                }
                if let Container::Module(_) = container {
                    return Err(LoweringRefusal::ForwardMemberReference {
                        span: site.at.span,
                        name,
                        declared: entry.named.span,
                    });
                }
            }
            let Container::Module(module) = container
            else {
                return Ok(Maybe::Absent(named::Absent::Unresolved));
            };
            container = self
                .collected
                .structures
                .get(usize::from(module))
                .map_or(Container::TopLevel, |structure| structure.container);
        }
    }

    /// Classify a term name.
    ///
    /// # Specification
    /// - requires: `site` is an identifier in term position.
    /// - ensures: a name standing as a value resolves against the binder frame
    ///   first and the declarations strictly earlier than its own second, and
    ///   is planned as the variable or constant it resolved to.
    /// - provides: the term-name half of resolution.
    /// - fails: yields the wrong-sort refusal for a name in computation
    ///   position, and the unresolved-name refusal when no scope answers;
    ///   propagates [`LoweringRefusal::BudgetExceeded`] from the binder walk.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    fn name(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let name = self.name_at(site.at);
        match self.resolve_name(site, frame, name)? {
            | Maybe::Present(resolved) => {
                self.plan(site, resolved.term());
                Ok(())
            },
            | Maybe::Absent(_) => Err(LoweringRefusal::UnresolvedName {
                span: site.at.span,
                name,
            }),
        }
    }

    /// Classify a capitalised name in term position.
    ///
    /// # Specification
    /// - requires: `site` is a constructor in term position.
    /// - ensures: a name a binder or an earlier declaration answers stands as
    ///   the value it resolved to; otherwise a type atom, or `Type` for the
    ///   value universe at the fuss-free level, stands as a type, which a value
    ///   position quotes.
    /// - provides: the term-position spelling of a type, and of a declaration
    ///   named with a capital.
    /// - fails: yields the wrong-sort refusal for a resolved name or a type
    ///   where its position reads neither; a name nothing answers is a
    ///   constructor, which the fragment does not admit.
    /// - panics: none.
    ///
    /// # Errors
    /// The name's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaration, a type atom, the universe and an
    ///   unanswered constructor each written where a value is read, asserted as
    ///   the exact core node or refusal.
    /// - witness: `lower::tests::a_type_where_a_value_is_read_is_quoted`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    fn constructor(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Maybe::Present(resolved) = self.resolve_name(site, site.reading.frame(), name)? {
            let _frame = self.require(site, Produced::Value)?;
            self.plan(site, resolved.term());
            return Ok(());
        }
        let quoted = match type_atom(name) {
            | Maybe::Present(atom) => Plan::Atom(atom),
            | Maybe::Absent(_) if name.as_ref() == TileName::UNIVERSE.as_ref() => {
                Plan::Universe(Universe::FUSS_FREE)
            },
            | Maybe::Absent(_) => return Err(site.out(FragmentBoundary::Unadmitted)),
        };
        let _frame = self.require(site, Produced::ValueType)?;
        self.plan(site, quoted);

        Ok(())
    }

    /// Classify a number literal.
    ///
    /// # Specification
    /// - requires: `site` is a number.
    /// - ensures: a number standing as a value whose lexeme is decimal digits
    ///   is planned as its canonical integer.
    /// - provides: the integer half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; a
    ///   fraction or an exponent is a number the fragment does not admit; any
    ///   other text is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The number's refusal.
    fn number(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let text = self.text_at(site.at);
        if let Maybe::Present(literal) = parse_literal(Former::Number, text) {
            self.plan(site, Plan::Literal(literal));
            return Ok(());
        }
        if fractional(text).0 {
            return Err(site.out(FragmentBoundary::Unadmitted));
        }

        Err(LoweringRefusal::MalformedLiteral {
            span: site.at.span,
            form: site.name,
        })
    }

    /// Classify a string literal.
    ///
    /// # Specification
    /// - requires: `site` is a string; `pieces` is its reading.
    /// - ensures: a string standing as a value with no interpolation is planned
    ///   as its decoded text.
    /// - provides: the text half of the literal reading.
    /// - fails: yields the wrong-sort refusal outside value position; an
    ///   interpolation is a form the fragment does not admit; a string missing
    ///   a delimiter is a malformed literal.
    /// - panics: none.
    ///
    /// # Errors
    /// The string's refusal.
    fn text(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let interpolated = pieces.pieces.iter().any(
            |piece| matches!(*piece, Piece::Tile { label, .. } if label == TileName::INTERPOLATION),
        );
        if interpolated {
            return Err(site.folded(FormName::INTERPOLATION, FragmentBoundary::Unadmitted));
        }
        let Maybe::Present(literal) = parse_literal(Former::Text, self.text_at(site.at))
        else {
            return Err(LoweringRefusal::MalformedLiteral {
                span: site.at.span,
                form: site.name,
            });
        };

        self.plan(site, Plan::Literal(literal));

        Ok(())
    }

    /// Classify a parenthesised expression: the unit, a grouping, the reserved
    /// tuple or an annotation.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised expression in term position.
    /// - ensures: `()` standing as a value is planned as the unit; `(e)` reads
    ///   its operand at its own reading and adopts it.
    /// - provides: the reading of every form the grammar folds into
    ///   parentheses.
    /// - fails: yields the reserved refusal for a tuple, the unadmitted refusal
    ///   for an annotation, the wrong-sort refusal for a unit outside value
    ///   position, and the extra-operand refusal for a juxtaposition.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    fn parenthesized(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let run = cursor.operands();
        if let Maybe::Present(_) = cursor.at(TileName::COMMA) {
            return Err(site.folded(FormName::TUPLE, FragmentBoundary::Reserved));
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return Err(site.folded(FormName::ANNOTATION, FragmentBoundary::Unadmitted));
        }
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        if let Run::Empty(_) = run {
            let unit = Site {
                name: FormName::UNIT,
                ..site
            };
            let _frame = self.require(unit, Produced::Value)?;
            self.plan(site, Plan::Unit);
            return Ok(());
        }
        let inner = site.one(run)?;
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// Classify a thunk, `thunk { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk in term position.
    /// - ensures: a thunk standing as a value reads its block in its own frame
    ///   and is planned over it.
    /// - provides: the value former that suspends a computation.
    /// - fails: yields the wrong-sort refusal outside value position, the
    ///   unadmitted refusal for a grade, and the block's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The thunk's refusal.
    fn thunk(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Value)?;
        let _keyword = cursor.tile(TileName::THUNK);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
        }
        let body = self.block(site, &mut cursor, frame)?;

        self.plan(site, Plan::Thunk(body));

        Ok(())
    }

    /// Classify a lambda, `fn (x) { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a lambda in term position.
    /// - ensures: a lambda standing as a computation binds its one parameter in
    ///   a frame extending its own, reads its block under that frame, and is
    ///   planned over it.
    /// - provides: the binder of the fragment.
    /// - fails: yields the wrong-sort refusal outside computation position; the
    ///   unadmitted refusal for a type abstraction or a typed parameter; the
    ///   arity refusal for any parameter count but one; the block's own
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The lambda's refusal.
    fn lambda(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _keyword = cursor.tile(TileName::FN);
        if let Maybe::Present(_) = cursor.at(TileName::BRACKET_OPEN) {
            return Err(site.folded(FormName::TYPE_ABSTRACTION, FragmentBoundary::Unadmitted));
        }
        let binder = parameter(site, &mut cursor)?;
        let name = self.name_at(binder);
        self.note_binder(binder, name)?;
        let extended = self.scope.extend(frame, name);
        let body = self.block(site, &mut cursor, Frame::Inner(extended))?;

        self.plan(site, Plan::Lambda(body));

        Ok(())
    }

    /// Classify a function tail, `def f(x: A, …) -> B { … }`.
    ///
    /// # Specification
    /// - requires: `site` is a declaration form read as a function, whose tail
    ///   opens on `(`.
    /// - ensures: each parameter binds in a frame extending the one before it,
    ///   left to right, with its type, when written, read as a value type under
    ///   the frame before it and recorded on the binder; the result, when
    ///   written, is read at the result position under the last parameter's
    ///   frame, as the block is; the form is planned as the function's declared
    ///   type and body.
    /// - provides: the function tail, lowered once at the declaration form for
    ///   both halves it writes.
    /// - fails: yields the unadmitted refusal for a parameter spelled as a type
    ///   or a type variable; a fault naming the function form for a parameter
    ///   list, a type or a result out of shape; and the block's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The function's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parameter count is separated by none and two,
    ///   each lowered tail asserted as the exact core node read back out of the
    ///   arena, and the refusals by a type-spelled parameter and a juxtaposed
    ///   parameter type, each asserted as the exact variant.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::an_empty_parameter_list_lowers_to_a_thunked_computation`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_juxtaposed_operand_is_refused`
    fn function(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let function = Site {
            name: FormName::FUNCTION,
            ..site
        };
        loop {
            match cursor.read() {
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::DEF => break,
                | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) => {},
                | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
        let _name = cursor.tile(TileName::IDENTIFIER);
        closed(function, &mut cursor, TileName::PAREN_OPEN)?;
        let start = self.parameters.len();
        let mut frame = Frame::Outermost;
        loop {
            let binder = match cursor.peek() {
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::PAREN_CLOSE => {
                    let _close = cursor.tile(TileName::PAREN_CLOSE);
                    break;
                },
                | Maybe::Present(Piece::Tile { label, at }) if label == TileName::IDENTIFIER => at,
                | Maybe::Present(Piece::Tile { label, at }) if TileName::BINDERS.contains(&label) =>
                {
                    let parameter = Site {
                        at,
                        name: FormName::PARAMETER,
                        ..function
                    };
                    return Err(parameter.out(FragmentBoundary::Unadmitted));
                },
                | Maybe::Present(Piece::Tile { .. } | Piece::Operand(_)) | Maybe::Absent(_) => {
                    return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
                },
            };
            let _binder = cursor.tile(TileName::IDENTIFIER);
            let declared = match cursor.tile(TileName::COLON) {
                | Maybe::Present(_) => {
                    let declared = function.one(cursor.operands())?;
                    self.read(declared.node, Reading::ValueType(frame));
                    Maybe::Present(declared.node)
                },
                | Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
            };
            let name = self.name_at(binder);
            self.note_binder(binder, name)?;
            let bound = match declared {
                | Maybe::Present(written) => self.scope.extend_typed(frame, name, written),
                | Maybe::Absent(_) => self.scope.extend(frame, name),
            };
            self.parameters.push(Parameter {
                binder: binder.node,
                frame: bound,
                declared,
            });
            frame = Frame::Inner(bound);
            if let Maybe::Absent(_) = cursor.tile(TileName::COMMA)
                && let Maybe::Absent(_) = cursor.at(TileName::PAREN_CLOSE)
            {
                return Err(function.fault(cursor.here(), FormFault::MisplacedTile));
            }
        }
        let parameters = Stretch {
            start,
            end: self.parameters.len(),
        };
        let result = match cursor.tile(TileName::ARROW) {
            | Maybe::Present(_) => {
                let result = function.one(cursor.operands())?;
                self.read(result.node, Reading::Result(frame));
                Maybe::Present(result.node)
            },
            | Maybe::Absent(_) => Maybe::Absent(stated::Absent::Unstated),
        };
        let block = self.block(function, &mut cursor, frame)?;

        self.plan(
            site,
            Plan::Function(Function {
                parameters,
                result,
                block,
            }),
        );

        Ok(())
    }

    /// Read a block, `{ s… c }`, whose first statement reads under `frame`.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the block's `{`, which the form's last
    ///   piece closes.
    /// - ensures: each `run x <- c ;` statement reads its computation under the
    ///   frame the statements before it extended and binds `x` in a frame
    ///   extending that one; the last computation reads under the frame every
    ///   statement extended; the statements and the last computation are
    ///   returned, with the cursor past the closing `}` and nothing after it.
    /// - provides: the body reading of thunks, lambdas and function tails.
    /// - fails: yields the unadmitted refusal for a statement the fragment does
    ///   not read, by the statement's own name; the arity refusal, as a block,
    ///   for a block with no last computation; and each statement's and hole's
    ///   own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The block's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the statement count is separated by none and two, the
    ///   second binding over the first, each asserted as the exact bind chain
    ///   read back out of the arena; the residue by one witness row per refused
    ///   statement form, asserted as the exact refusal.
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    /// - witness: `lower::tests::a_block_binds_each_statement_over_the_next`
    /// - witness: `lower::tests::forms_outside_the_fragment_are_unadmitted`
    /// - witness: `lower::tests::a_form_offered_the_wrong_operand_count_is_refused`
    fn block(
        &mut self,
        site: Site,
        cursor: &mut Cursor<'_>,
        frame: Frame,
    ) -> Result<Block, LoweringRefusal<'source>>
    {
        let Maybe::Present(open) = cursor.tile(TileName::BRACE_OPEN)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let start = self.statements.len();
        let mut frame = frame;
        loop {
            match cursor.peek() {
                | Maybe::Present(Piece::Tile { label, at }) if label == TileName::RUN => {
                    let _run = cursor.tile(TileName::RUN);
                    frame = self.statement(cursor, at, frame)?;
                },
                | Maybe::Present(Piece::Operand(_)) => {
                    let run = cursor.operands();
                    if let Maybe::Present(semicolon) = cursor.at(TileName::SEMICOLON) {
                        let first = match run {
                            | Run::One(written) | Run::Several { first: written, .. } => {
                                written.span
                            },
                            | Run::Empty(gap) => gap,
                        };
                        return Err(LoweringRefusal::OutOfFragment {
                            span: first.join(semicolon.span),
                            form: FormName::EXPRESSION_STATEMENT,
                            sort: FragmentSort::Computation,
                            boundary: FragmentBoundary::Unadmitted,
                        });
                    }
                    let last = site.one(run)?;
                    closed(site, cursor, TileName::BRACE_CLOSE)?;
                    exhausted(site, cursor)?;
                    self.read(last.node, Reading::Computation(frame));
                    return Ok(Block {
                        statements: Stretch {
                            start,
                            end: self.statements.len(),
                        },
                        last: last.node,
                    });
                },
                | Maybe::Present(Piece::Tile { label, .. }) if label == TileName::BRACE_CLOSE => {
                    let braced = ByteSpan::new(open.span.start(), site.at.span.end())
                        .unwrap_or(site.at.span);
                    let as_block = Site {
                        at: Placed {
                            node: site.at.node,
                            span: braced,
                        },
                        name: FormName::BLOCK,
                        reading: Reading::Computation(frame),
                    };
                    return Err(as_block.out(FragmentBoundary::Arity(OperandCount::from(0_usize))));
                },
                | Maybe::Present(Piece::Tile { label, at }) => {
                    return Err(match statement_form(label, cursor) {
                        | Maybe::Present(form) => LoweringRefusal::OutOfFragment {
                            span: at.span,
                            form,
                            sort: FragmentSort::Computation,
                            boundary: FragmentBoundary::Unadmitted,
                        },
                        | Maybe::Absent(_) => site.fault(at.span, FormFault::MisplacedTile),
                    });
                },
                | Maybe::Absent(_) => {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                },
            }
        }
    }

    /// Read one `run x <- c ;` statement, its `run` tile already read.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the statement's `run` tile `run`;
    ///   `frame` is the frame the statement reads under.
    /// - ensures: the statement's computation is read under `frame` and the
    ///   statement recorded with its `run` tile; the frame binding the
    ///   statement's name over `frame`, which the rest of the block reads
    ///   under, is returned.
    /// - provides: the one statement the fragment reads.
    /// - fails: yields the unadmitted refusal for an annotated binder and for a
    ///   binder pattern other than a name, and a fault naming the bind
    ///   statement for a hole or a tile out of shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The statement's refusal.
    fn statement(
        &mut self,
        cursor: &mut Cursor<'_>,
        run: Placed,
        frame: Frame,
    ) -> Result<Frame, LoweringRefusal<'source>>
    {
        let statement = Site {
            at: run,
            name: FormName::BIND_STATEMENT,
            reading: Reading::Computation(frame),
        };
        let binder = statement.one(cursor.operands())?;
        if let Maybe::Present(colon) = cursor.at(TileName::COLON) {
            return Err(LoweringRefusal::OutOfFragment {
                span: colon.span,
                form: FormName::ANNOTATION,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Unadmitted,
            });
        }
        closed(statement, cursor, TileName::BIND)?;
        let bound = statement.one(cursor.operands())?;
        closed(statement, cursor, TileName::SEMICOLON)?;
        let name = self.binder_name(statement, binder)?;
        self.note_binder(binder, name)?;
        self.read(bound.node, Reading::Computation(frame));
        self.statements.push(Statement {
            run: run.node,
            bound: bound.node,
        });

        Ok(Frame::Inner(self.scope.extend(frame, name)))
    }

    /// The name a `run` statement's pattern binds.
    ///
    /// # Specification
    /// - requires: `binder` is the pattern operand of the statement at
    ///   `statement`.
    /// - ensures: the name an identifier pattern spells.
    /// - provides: the binder reading of the bind statement.
    /// - fails: yields the unadmitted refusal, at pattern sort and by the
    ///   pattern's own name, for every other pattern;
    ///   [`LoweringRefusal::UnknownMold`] for a foreign mold.
    /// - panics: none.
    ///
    /// # Errors
    /// The pattern's refusal.
    fn binder_name(
        &self,
        statement: Site,
        binder: Placed,
    ) -> Result<SurfaceName<'source>, LoweringRefusal<'source>>
    {
        let Some(node) = self.tree.node(binder.node)
        else {
            return Err(statement.fault(binder.span, FormFault::MisplacedTile));
        };
        match shape_of(self.pbg, node)? {
            | Shape::Form {
                former: Former::Name,
                ..
            } => Ok(self.name_at(binder)),
            | Shape::Form { name, .. } => Err(LoweringRefusal::OutOfFragment {
                span: binder.span,
                form: name,
                sort: FragmentSort::Pattern,
                boundary: FragmentBoundary::Unadmitted,
            }),
            | Shape::Repair(repair) => {
                Err(statement.fault(binder.span, FormFault::Repaired(repair)))
            },
            | Shape::Root | Shape::Layout => {
                Err(statement.fault(binder.span, FormFault::MisplacedTile))
            },
        }
    }

    /// Classify a keyword form of one value operand: `ret v` or `force v`.
    ///
    /// # Specification
    /// - requires: `site` is a returner or a force in term position, whose
    ///   keyword tile is `keyword`.
    /// - ensures: the form standing as a computation reads its one operand as a
    ///   value in its own frame and is planned over it.
    /// - provides: the two computation formers over a value.
    /// - fails: yields the wrong-sort refusal outside computation position, and
    ///   the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    fn keyed(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
        keyword: TileName,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let _keyword = cursor.tile(keyword);
        let operand = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(operand.node, Reading::Value(frame));
        let plan = if keyword == TileName::FORCE {
            Plan::Force(operand.node)
        }
        else {
            Plan::Return(operand.node)
        };

        self.plan(site, plan);

        Ok(())
    }

    /// Classify an application, `c(v, …)`.
    ///
    /// # Specification
    /// - requires: `site` is a call in term position.
    /// - ensures: a call standing as a computation reads its head at the head
    ///   position and each argument as a value, all in its own frame, and is
    ///   planned as the head applied to the arguments left to right; a call of
    ///   no arguments is its head.
    /// - provides: the elimination of a lambda, curried over any argument
    ///   count.
    /// - fails: yields the wrong-sort refusal outside computation position, and
    ///   the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The call's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the argument count is separated by none, one and two,
    ///   each asserted as the exact application chain read back out of the
    ///   arena.
    /// - witness: `lower::tests::force_and_application_lower_over_their_children`
    /// - witness: `lower::tests::a_call_applies_its_arguments_left_to_right`
    /// - witness: `lower::tests::a_value_head_is_forced_and_marked_inserted`
    fn call(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::Computation)?;
        let head = site.one(cursor.operands())?;
        let start = self.operands.len();
        arguments(site, &mut cursor, &mut self.operands)?;
        let written = Stretch {
            start,
            end: self.operands.len(),
        };
        self.read(head.node, Reading::Head(frame));
        for position in written.start .. written.end {
            if let Some(&argument) = self.operands.get(position) {
                self.read(argument, Reading::Value(frame));
            }
        }

        self.plan(site, Plan::Application(head.node, written));

        Ok(())
    }

    /// Classify a selection `e.name`.
    ///
    /// # Specification
    /// - requires: `site` is a projection; `pieces` is its reading.
    /// - ensures: a chain of selections whose head is a capitalised name is a
    ///   path, resolved through the outermost scope at the depth that binds it:
    ///   a path ending at an exported value component stands as that member's
    ///   constant when the member is declared strictly before the declaration
    ///   the path is written in. The chain is walked by an explicit loop, and
    ///   its links are left unread.
    /// - provides: the governed reading of a module path.
    /// - fails: yields [`LoweringRefusal::UnknownMember`], naming the module as
    ///   the path spells it and the member, for a selection a governing module
    ///   does not export; the forward-member refusal for a member declared at
    ///   or after the referring declaration; the wrong-sort refusal for a path
    ///   ending at a module, which is not a value; the wrong-sort refusal
    ///   outside value position; and the unadmitted refusal for a selection no
    ///   module governs, a record projection the fragment does not admit.
    /// - panics: none.
    ///
    /// # Errors
    /// The selection's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a path to an exported component at depth two and at
    ///   depth nine, to a hidden member, to an absent member at each depth, to
    ///   a module, to a member declared later, and a selection off a free name,
    ///   each asserted as the exact constant or refusal.
    /// - witness: `modules::modules::a_user_module_selection_is_governed_and_a_free_target_still_projects`
    /// - witness: `modules::modules::a_module_path_is_governed_through_lowering_not_merely_registered`
    /// - witness: `modules::modules::a_deep_module_path_is_governed_at_the_depth_that_binds_it`
    /// - witness: `modules::modules::a_module_namespace_is_not_a_projectable_record`
    /// - witness: `modules::modules::a_hidden_or_absent_user_module_component_is_declined_as_a_hole`
    fn projection(
        &mut self,
        site: Site,
        pieces: &Pieces,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::Value)?;
        let mut links: Vec<(Placed, Placed)> = Vec::new();
        let (mut target, member) = Self::link(site, &pieces.pieces, site.at.span)?;
        links.push((target, member));
        let mut chain = Pieces::new();
        let head = loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(target.node)
            else {
                return Err(site.out(FragmentBoundary::Unadmitted));
            };
            match shape_of(self.pbg, node)? {
                | Shape::Form {
                    former: Former::Projection,
                    ..
                } => {
                    read_pieces(self.pbg, self.tree, target.node, &mut chain)?;
                    if let Maybe::Present(repaired) = chain.repair {
                        return Err(site.fault(repaired.span, FormFault::Repaired(repaired.repair)));
                    }
                    let (inner, selected) = Self::link(site, &chain.pieces, target.span)?;
                    links.push((inner, selected));
                    target = inner;
                },
                | Shape::Form {
                    former: Former::Constructor,
                    ..
                } => break target,
                | Shape::Form { .. } | Shape::Root | Shape::Repair(_) | Shape::Layout => {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                },
            }
        };
        let mut segments = Vec::with_capacity(links.len().saturating_add(1_usize));
        segments.push(Segment::from(self.text_at(head).as_ref()));
        for &(_prefix, selected) in links.iter().rev() {
            segments.push(Segment::from(self.text_at(selected).as_ref()));
        }
        let path = NamePath::from(segments);
        match self.recognition.resolve_path(&path) {
            | PathResolution::Complete(Recognized::ModuleComponent) => {
                let Some(&exported) = self.exported.get(&path)
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                self.select(site, exported)
            },
            | PathResolution::Complete(Recognized::ModuleNamespace) => {
                Err(site.out(FragmentBoundary::WrongSort))
            },
            | PathResolution::UnknownMember { depth, .. } => {
                let Some(&(prefix, selected)) = links
                    .len()
                    .checked_sub(usize::from(depth))
                    .and_then(|link| links.get(link))
                else {
                    return Err(site.out(FragmentBoundary::Unadmitted));
                };
                Err(LoweringRefusal::UnknownMember {
                    span: selected.span,
                    module: self.name_at(prefix),
                    member: self.name_at(selected),
                })
            },
            | PathResolution::Complete(_) | PathResolution::Ungoverned => {
                Err(site.out(FragmentBoundary::Unadmitted))
            },
        }
    }

    /// The target and the selected name of one selection, read from its
    /// pieces.
    ///
    /// # Specification
    /// - requires: `pieces` is the reading of a projection covering `span`.
    /// - ensures: the operand the selection is taken from and the name tile
    ///   after its dot.
    /// - provides: the one-link half of [`Self::projection`].
    /// - fails: yields the misplaced-tile refusal when the pieces are not an
    ///   operand, a dot and a name.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::MalformedForm`] for a malformed selection.
    fn link(
        site: Site,
        pieces: &[Piece],
        span: ByteSpan,
    ) -> Result<(Placed, Placed), LoweringRefusal<'source>>
    {
        let mut cursor = Cursor::new(pieces, span);
        let Maybe::Present(Piece::Operand(target)) = cursor.read()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let (Maybe::Present(_dot), Maybe::Present(selected)) = (
            cursor.tile(TileName::DOT),
            cursor.tile(TileName::IDENTIFIER),
        )
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };

        Ok((target, selected))
    }

    /// Plan the selection at `site` as the exported member at `target`.
    ///
    /// # Specification
    /// - requires: `target` is the member an exported path resolved to.
    /// - ensures: the member's constant, when the member is declared strictly
    ///   before the declaration `site` belongs to.
    /// - provides: the position rule for a path.
    /// - fails: yields [`LoweringRefusal::ForwardMemberReference`] for a member
    ///   declared at or after it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::ForwardMemberReference`].
    fn select(
        &mut self,
        site: Site,
        target: SlotIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Some(entry) = self.collected.slots.get(usize::from(target))
        else {
            return Err(site.out(FragmentBoundary::Unadmitted));
        };
        let (constant, name, declared) = (entry.constant, entry.name, entry.named.span);
        if let Maybe::Present(own) = self.collected.owner_of(site.at.node)
            && target >= own
        {
            return Err(LoweringRefusal::ForwardMemberReference {
                span: site.at.span,
                name,
                declared,
            });
        }
        self.plan(site, Plan::Constant(constant));

        Ok(())
    }

    /// Classify a bare type head.
    ///
    /// # Specification
    /// - requires: `site` is a primitive type, a type identifier or a type
    ///   variable in type position.
    /// - ensures: inside a module signature, a head naming a manifest type
    ///   component written before the head's own component stands for the type
    ///   that component names, adopted as it lowered. Otherwise a head a binder
    ///   or an earlier declaration answers is that code, decoded in the
    ///   universe its type was written at — the value types at the fuss-free
    ///   level when it was written at none — and stands at the sort of that
    ///   universe; a binder so named is recorded as mentioned by a type. Any
    ///   other head resolves against the nullary table and is planned as its
    ///   atom.
    /// - provides: the type-head half of resolution, the expansion of a
    ///   manifest type component, and the decode of a value name in type
    ///   position.
    /// - fails: yields the wrong-sort refusal for a head whose sort does not
    ///   suit the position and the unresolved-head refusal for a head nothing
    ///   answers.
    /// - panics: none.
    ///
    /// # Errors
    /// The head's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at the bare universe, a binder
    ///   written at a sorted and levelled one, a declaration, an atom and a
    ///   manifest component, each asserted as the exact core type read back out
    ///   of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    /// - witness: `lower::tests::u_and_f_are_names`
    /// - witness: `lower::tests::every_type_atom_lowers_to_its_core_type`
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    fn type_head(
        &mut self,
        site: Site,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let name = self.name_at(site.at);
        if let Some(&Maybe::Present(seen)) = self.scopes.get(usize::from(site.at.node))
            && let Some(manifest) = self
                .collected
                .structures
                .get(usize::from(seen.structure))
                .and_then(|structure| structure.types.get(.. seen.before))
                .and_then(|visible| visible.iter().rev().find(|manifest| manifest.name == name))
        {
            let (held, defined) = (manifest.held, manifest.defined.node);
            let _frame = self.require(site, Produced::ValueType)?;
            self.manifests.push((held, site.at.node));
            self.plan(site, Plan::Transparent(defined));
            return Ok(());
        }
        let from = site.reading.frame();
        if let Maybe::Present(resolved) = self.resolve_name(site, from, name)? {
            let (code, declared) = match resolved {
                | Resolved::Binder(bound) => (
                    Code::Bound {
                        from,
                        binder: bound.binder,
                    },
                    bound.declared,
                ),
                | Resolved::Declaration { constant, declared } => {
                    (Code::Constant(constant), declared)
                },
            };
            let universe = self.written_universe(declared)?;
            let produced = match universe.sort {
                | GroundSort::Value => Produced::ValueType,
                | GroundSort::Computation => Produced::CompType,
            };
            let _frame = self.require(site, produced)?;
            if let Code::Bound { binder, .. } = code {
                self.scope.mention(binder);
            }
            self.plan(site, Plan::Decode(code, universe));
            return Ok(());
        }
        let _frame = self.require(site, Produced::ValueType)?;
        let Maybe::Present(atom) = type_atom(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: site.at.span,
                name,
                arity: HeadArity::Nullary,
            });
        };

        self.plan(site, Plan::Atom(atom));

        Ok(())
    }

    /// Classify a universe, `Type[s, l]`.
    ///
    /// # Specification
    /// - requires: `site` is a universe in type position, or in value position
    ///   where it is quoted.
    /// - ensures: a universe standing as a value type is planned at the sort
    ///   and level written, the value sort and the fuss-free level supplied for
    ///   whichever is left off.
    /// - provides: the universe former of the fragment.
    /// - fails: yields the wrong-sort refusal where its position reads no value
    ///   type, a misplaced-tile fault for a bracket out of shape, and the
    ///   unadmitted refusal for a level beyond the core's level width.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bare spelling, a sort alone and a sort with a
    ///   level at each sort, each asserted as the exact core universe.
    /// - witness: `lower::tests::every_universe_spelling_lowers_to_its_universe`
    fn universe(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _frame = self.require(site, Produced::ValueType)?;
        let universe = self.universe_of(site, &mut cursor)?;

        self.plan(site, Plan::Universe(universe));

        Ok(())
    }

    /// The universe a universe form's pieces spell.
    ///
    /// # Specification
    /// - requires: `cursor` stands at the form's `Type` tile.
    /// - ensures: the sort `+` or `-` and the level numeral written, the value
    ///   sort and level zero for whichever is left off.
    /// - provides: the one reading of a universe's spelling, shared by the
    ///   universe former and the decode that reads a binder's written type.
    /// - fails: a misplaced-tile fault for a bracket out of shape; the
    ///   unadmitted refusal for a level numeral wider than a level constant.
    /// - panics: none.
    ///
    /// # Errors
    /// The universe's refusal.
    fn universe_of(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let _keyword = cursor.tile(TileName::UNIVERSE);
        if let Maybe::Absent(_) = cursor.tile(TileName::BRACKET_OPEN) {
            exhausted(site, cursor)?;
            return Ok(Universe::FUSS_FREE);
        }
        let sort = match (cursor.tile(TileName::PLUS), cursor.tile(TileName::MINUS)) {
            | (Maybe::Present(_), _) => GroundSort::Value,
            | (Maybe::Absent(_), Maybe::Present(_)) => GroundSort::Computation,
            | (Maybe::Absent(_), Maybe::Absent(_)) => {
                return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
            },
        };
        let level = match cursor.tile(TileName::COMMA) {
            | Maybe::Present(_) => {
                let Maybe::Present(numeral) = cursor.tile(TileName::NUMBER)
                else {
                    return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
                };
                let text = self.text_at(numeral);
                let spelled: &str = text.as_ref();
                let Ok(level) = spelled.parse::<u64>()
                else {
                    let level = Site {
                        at: numeral,
                        ..site
                    };
                    return Err(level.out(FragmentBoundary::Unadmitted));
                };
                LevelConstant::from(level)
            },
            | Maybe::Absent(_) => LevelConstant::ZERO,
        };
        closed(site, cursor, TileName::BRACKET_CLOSE)?;
        exhausted(site, cursor)?;

        Ok(Universe { sort, level })
    }

    /// The universe the type at `declared` was written as, the fuss-free
    /// default when it is none.
    ///
    /// # Specification
    /// - requires: `declared`, when present, is a node of the tree.
    /// - ensures: the universe a universe form spells, read through any
    ///   grouping parentheses around it; [`Universe::FUSS_FREE`] for an absent
    ///   type, any other form, or a universe out of shape, whose own reading
    ///   reports it.
    /// - provides: the sort and level a decode of a binder or a declaration is
    ///   minted at.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the walk through the
    ///   parentheses outruns the allowance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binder written at a sorted, levelled universe
    ///   inside a grouping and a declaration signed at one, each observed
    ///   through the decode it mints.
    /// - witness: `lower::tests::a_decode_reads_the_universe_its_code_was_written_at`
    fn written_universe(
        &mut self,
        declared: Maybe<NodeIndex, binder_type::Absent>,
    ) -> Result<Universe, LoweringRefusal<'source>>
    {
        let Maybe::Present(mut position) = declared
        else {
            return Ok(Universe::FUSS_FREE);
        };
        loop {
            self.fuel.spend()?;
            let Some(node) = self.tree.node(position)
            else {
                return Ok(Universe::FUSS_FREE);
            };
            let Ok(Shape::Form { name, former }) = shape_of(self.pbg, node)
            else {
                return Ok(Universe::FUSS_FREE);
            };
            let mut scratch = core::mem::take(&mut self.scratch);
            let read = read_pieces(self.pbg, self.tree, position, &mut scratch);
            let site = Site {
                at: Placed::of(position, node),
                name,
                reading: Reading::ValueType(Frame::Outermost),
            };
            let mut cursor = Cursor::new(&scratch.pieces, site.at.span);
            let step = match (read, former) {
                | (Ok(()), Former::Universe) => ControlFlow::Break(
                    self.universe_of(site, &mut cursor)
                        .unwrap_or(Universe::FUSS_FREE),
                ),
                | (Ok(()), Former::ParenthesizedType) => {
                    let _open = cursor.tile(TileName::PAREN_OPEN);
                    match cursor.operands() {
                        | Run::One(operand) => ControlFlow::Continue(operand.node),
                        | Run::Empty(_) | Run::Several { .. } => {
                            ControlFlow::Break(Universe::FUSS_FREE)
                        },
                    }
                },
                | _ => ControlFlow::Break(Universe::FUSS_FREE),
            };
            self.scratch = scratch;
            match step {
                | ControlFlow::Continue(operand) => position = operand,
                | ControlFlow::Break(universe) => return Ok(universe),
            }
        }
    }

    /// Classify a type head applied to arguments, `Foo(A)`.
    ///
    /// # Specification
    /// - requires: `site` is a type application in type position.
    /// - ensures: a head applied to one argument resolves against the unary
    ///   table, stands at the sort its former produces, reads its argument at
    ///   the sort the former takes, and is planned over it.
    /// - provides: the applied half of type-head resolution.
    /// - fails: yields the unresolved-head refusal for a head no former answers
    ///   at the arity it was written with, the wrong-sort refusal for a former
    ///   whose sort does not suit the position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The application's refusal.
    fn type_application(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(head) = cursor.tile(TileName::TYPE_IDENTIFIER)
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let name = self.name_at(head);
        let start = self.operands.len();
        let read = arguments(site, &mut cursor, &mut self.operands);
        let count = self.operands.len().saturating_sub(start);
        let first = self.operands.get(start).copied();
        self.operands.truncate(start);
        read?;
        let unresolved = |arity| LoweringRefusal::UnresolvedTypeHead {
            span: head.span,
            name,
            arity,
        };
        let (Some(argument), 1_usize) = (first, count)
        else {
            return Err(unresolved(HeadArity::Polyadic(OperandCount::from(count))));
        };
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(unresolved(HeadArity::Unary));
        };

        self.apply_former(site, former, argument)
    }

    /// Classify a type former written as its own keyword: `+U C` or `-F A`.
    ///
    /// # Specification
    /// - requires: `site` is a thunk type or a returner type in type position.
    /// - ensures: the keyword resolves against the unary table, a thunk type's
    ///   grade `[ω]` reads as no grade written, the form stands at the sort its
    ///   former produces, reads its one operand at the sort the former takes,
    ///   and is planned over it.
    /// - provides: the keyword spelling of the two type formers.
    /// - fails: yields the unresolved-head refusal for a keyword no former
    ///   answers, [`LoweringRefusal::GradedBridge`] for a thunk type graded
    ///   other than `ω`, the unadmitted refusal for a grade on a returner type,
    ///   the wrong-sort refusal for a former whose sort does not suit the
    ///   position, and the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    fn formed_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        let _keyword = cursor.tile(label);
        let name = self.name_at(at);
        let Maybe::Present(former) = type_former(name)
        else {
            return Err(LoweringRefusal::UnresolvedTypeHead {
                span: at.span,
                name,
                arity: HeadArity::Unary,
            });
        };
        if let Maybe::Present(_) = cursor.tile(TileName::BRACKET_OPEN) {
            if former != TypeFormer::Thunk {
                return Err(site.folded(FormName::GRADE, FragmentBoundary::Unadmitted));
            }
            self.grade(site, &mut cursor)?;
        }
        let argument = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;

        self.apply_former(site, former, argument.node)
    }

    /// Read a bridge's grade, `[r]`, admitting only the default `ω`.
    ///
    /// # Specification
    /// - requires: `cursor` stands just past the grade's `[`.
    /// - ensures: `ω` followed by `]` reads as the bridge with no grade
    ///   written, the cursor past the `]`.
    /// - provides: the one grade the core's bridge carries.
    /// - fails: [`LoweringRefusal::GradedBridge`] for a numeral or a name as
    ///   the grade, at the grade; a misplaced-tile fault for a grade out of
    ///   shape.
    /// - panics: none.
    ///
    /// # Errors
    /// The grade's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the default grade, a numeral and a name, each
    ///   asserted as the lowered bridge or the exact refusal.
    /// - witness: `lower::tests::a_graded_bridge_is_refused_by_name`
    fn grade(
        &self,
        site: Site,
        cursor: &mut Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let Maybe::Present(Piece::Tile { label, at }) = cursor.peek()
        else {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        };
        if label == TileName::NUMBER || label == TileName::IDENTIFIER {
            return Err(LoweringRefusal::GradedBridge {
                span: at.span,
                grade: self.name_at(at),
            });
        }
        closed(site, cursor, TileName::OMEGA)?;

        closed(site, cursor, TileName::BRACKET_CLOSE)
    }

    /// Plan `former` applied to `argument` at `site`.
    ///
    /// # Specification
    /// - requires: `argument` is the one operand the former was written with.
    /// - ensures: the thunk former stands at value-type sort with its argument
    ///   read at computation-type sort, and the returner former stands at
    ///   computation-type sort with its argument read at value-type sort; the
    ///   former decides both, so nothing is pushed down that has to be
    ///   re-derived.
    /// - provides: the one place a type former's sorts are decided.
    /// - fails: yields the wrong-sort refusal for a former whose produced sort
    ///   does not suit the position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::OutOfFragment`] for a sort mismatch.
    fn apply_former(
        &mut self,
        site: Site,
        former: TypeFormer,
        argument: NodeIndex,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let produced = match former {
            | TypeFormer::Thunk => Produced::ValueType,
            | TypeFormer::Returner => Produced::CompType,
        };
        let frame = self.require(site, produced)?;
        let inner = match former {
            | TypeFormer::Thunk => Reading::CompType(frame),
            | TypeFormer::Returner => Reading::ValueType(frame),
        };
        self.read(argument, inner);

        self.plan(site, Plan::Former(former, argument));

        Ok(())
    }

    /// Classify an arrow type, `A -> C`.
    ///
    /// # Specification
    /// - requires: `site` is an arrow in type position.
    /// - ensures: an arrow standing as a computation type reads its domain as a
    ///   value type and its codomain as a computation type, and is planned over
    ///   both.
    /// - provides: the function type of the fragment.
    /// - fails: yields the wrong-sort refusal outside computation-type
    ///   position, and either hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The arrow's refusal.
    fn arrow(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let frame = self.require(site, Produced::CompType)?;
        let domain = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::ARROW)?;
        let codomain = site.one(cursor.operands())?;
        exhausted(site, &cursor)?;
        self.read(domain.node, Reading::ValueType(frame));
        self.read(codomain.node, Reading::CompType(frame));

        self.plan(site, Plan::Arrow(domain.node, codomain.node));

        Ok(())
    }

    /// Classify a parenthesised type, `(T)`.
    ///
    /// # Specification
    /// - requires: `site` is a parenthesised type in type position.
    /// - ensures: the one operand is read at the form's own reading and
    ///   adopted.
    /// - provides: grouping in type position.
    /// - fails: yields the hole's own refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The form's refusal.
    fn parenthesized_type(
        &mut self,
        site: Site,
        mut cursor: Cursor<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let _open = cursor.tile(TileName::PAREN_OPEN);
        let inner = site.one(cursor.operands())?;
        closed(site, &mut cursor, TileName::PAREN_CLOSE)?;
        self.read(inner.node, site.reading);

        self.plan(site, Plan::Transparent(inner.node));

        Ok(())
    }

    /// How `position` is read.
    ///
    /// # Specification
    /// trivial.
    fn reading(
        &self,
        position: NodeIndex,
    ) -> Reading
    {
        self.readings
            .get(usize::from(position))
            .copied()
            .unwrap_or(Reading::Unread)
    }

    /// Read `position` as `reading`.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        position: NodeIndex,
        reading: Reading,
    )
    {
        if let Some(held) = self.readings.get_mut(usize::from(position)) {
            *held = reading;
        }
    }

    /// Record `plan` for the form at `site`.
    ///
    /// # Specification
    /// trivial.
    fn plan(
        &mut self,
        site: Site,
        plan: Plan,
    )
    {
        if let Some(held) = self.plans.get_mut(usize::from(site.at.node)) {
            *held = plan;
        }
    }

    /// The source text of `placed`.
    ///
    /// # Specification
    /// trivial.
    fn text_at(
        &self,
        placed: Placed,
    ) -> SourceFragment<'source>
    {
        self.tree
            .fragment(placed.node)
            .unwrap_or_else(|| SourceFragment::from(""))
    }

    /// The name `placed` spells.
    ///
    /// # Specification
    /// trivial.
    fn name_at(
        &self,
        placed: Placed,
    ) -> SurfaceName<'source>
    {
        SurfaceName::from(self.text_at(placed))
    }

    /// The descending sweep: mint every planned node and record its origin.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: every manifest type component's type is minted first, one
    ///   component at a time in signature order, each subtree descending, so a
    ///   type head that stands for a component adopts a type already minted
    ///   wherever it sits. Every other planned node is then minted, with its
    ///   children already minted because the level-order layout puts them at
    ///   strictly higher positions; every minted node gets an origin naming the
    ///   syntax node that produced it, terms and types alike, while an adopted
    ///   child keeps its own. A node whose position bridges its sort has the
    ///   bridge minted over its own core node, with the same syntax node's
    ///   origin marked as inserted. A node under a declaration that refused is
    ///   not minted, and neither is any node above it, unless it lies inside an
    ///   attribute payload: the side table files a payload whatever its
    ///   declaration's outcome, so an expectation about a refused declaration
    ///   stays readable. Last, the body of every witness whose member and own
    ///   type are unrefused is minted as that member's constant, its origin the
    ///   form that stated the second type.
    /// - provides: the whole allocation half of the lowering.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] when the sweep outruns the
    ///   allowance; nothing else, because every decision was made ascending.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] when the allowance runs out.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest component named before and after its own
    ///   position in the tree, and a witness agreeing and disagreeing with its
    ///   member, each asserted through the checker's verdict.
    /// - witness: `modules::modules::a_manifest_type_component_expands_in_later_components`
    /// - witness: `modules::modules::nested_member_signature_constrains_the_parent_binding`
    /// - witness: `lower::tests::every_minted_node_has_an_origin`
    fn mint(
        &mut self,
        sink: &mut Sink<'_>,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut manifests: Vec<NodeIndex> = self
            .collected
            .structures
            .iter()
            .flat_map(|structure| structure.types.iter().map(|manifest| manifest.defined.node))
            .collect();
        manifests.reverse();
        let mut subtree: Vec<NodeIndex> = Vec::new();
        let mut work: Vec<NodeIndex> = Vec::new();
        while let Some(root) = manifests.pop() {
            subtree.clear();
            work.push(root);
            while let Some(position) = work.pop() {
                self.fuel.spend()?;
                subtree.push(position);
                work.extend(self.tree.children(position));
            }
            subtree.sort_unstable_by(|left, right| right.cmp(left));
            for &position in &subtree {
                self.mint_at(position, sink);
            }
        }
        let mut remaining = usize::from(self.tree.node_count());
        while let Some(next) = remaining.checked_sub(1_usize) {
            remaining = next;
            self.fuel.spend()?;
            self.mint_at(NodeIndex::from(next), sink);
        }
        for (position, slot) in self.collected.slots.iter().enumerate() {
            if let Maybe::Present(Half {
                declaration,
                operand: Operand::Member(target),
            }) = slot.definition
                && let Maybe::Absent(_) = slot.refusal
                && let Some(member) = self.collected.slots.get(usize::from(target))
                && let Maybe::Absent(_) = member.refusal
                && let Maybe::Present(origin) = self.origin_at(declaration.node)
            {
                let id = sink.arena.value_constant(member.constant);
                let _minted = sink.value(id, origin);
                let _replaced = self.witnessed.insert(SlotIndex::from(position), id);
            }
        }

        Ok(())
    }

    /// Mint the node at `position` by its plan, once.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the node's plan is taken and minted, its bridge written over
    ///   it and the result kept as the node's lowered core node; a node with no
    ///   plan left, or under a refused declaration outside a payload, is left
    ///   as it is.
    /// - provides: the per-position half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    fn mint_at(
        &mut self,
        position: NodeIndex,
        sink: &mut Sink<'_>,
    )
    {
        if self.collected.refused(position).0 && !self.in_payload(position).0 {
            return;
        }
        let Some(planned) = self.plans.get_mut(usize::from(position))
        else {
            return;
        };
        let plan = core::mem::replace(planned, Plan::Unplanned);
        if plan == Plan::Unplanned {
            return;
        }
        let Maybe::Present(origin) = self.origin_at(position)
        else {
            return;
        };
        let bridge = self
            .bridges
            .get(usize::from(position))
            .copied()
            .unwrap_or(Bridge::Bare);
        let minted = self.mint_plan(plan, sink, origin);
        let bridged = sink.bridge(minted, bridge, origin);
        if let Some(held) = self.lowered.get_mut(usize::from(position)) {
            *held = bridged;
        }
    }

    /// The origin of a core node the syntax node at `position` wrote.
    ///
    /// # Specification
    /// trivial.
    fn origin_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Origin, lowered::Absent>
    {
        self.tree
            .node(position)
            .map_or(Maybe::Absent(lowered::Absent::Unminted), |node| {
                Maybe::Present(Origin::new(position, node.digest(), node.span()))
            })
    }

    /// Carry out one plan.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: the plan's core node, minted over its children's lowered
    ///   nodes with its origin recorded; an adopted child's own node for a
    ///   transparent plan; nothing when a child did not lower at the sort the
    ///   plan takes. Every variable is minted in the intuitionistic zone, the
    ///   only zone the fragment binds into; a decode's code carries the written
    ///   origin and its type the inserted one.
    /// - provides: the per-node half of [`Self::mint`].
    /// - fails: never.
    /// - panics: none.
    fn mint_plan(
        &self,
        plan: Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match plan {
            | Plan::Unplanned => Maybe::Absent(lowered::Absent::Unminted),
            | Plan::Variable(index) => {
                let id = sink.arena.value_variable(Zone::Intuitionistic, index);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Constant(constant) => {
                let id = sink.arena.value_constant(constant);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Unit => {
                let id = sink.arena.value_unit();
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Literal(literal) => {
                let id = sink.arena.value_literal(literal);
                Maybe::Present(sink.value(id, origin))
            },
            | Plan::Atom(atom) => Maybe::Present(sink.atom(atom, origin)),
            | Plan::Universe(universe) => {
                let id = sink.arena.value_type_universe(
                    Sort::Ground(universe.sort),
                    Level::constant(universe.level),
                );
                sink.origins.record_value_type(id, origin);
                Maybe::Present(Lowered::ValueType(id))
            },
            | Plan::Decode(code, universe) => {
                Maybe::Present(self.mint_decode(code, universe, sink, origin))
            },
            | Plan::Transparent(child) => self.lowered_at(child),
            | Plan::Former(former, argument) => self.mint_former(former, argument, sink, origin),
            | Plan::Application(head, arguments) => {
                self.mint_application(head, arguments, sink, origin)
            },
            | Plan::Function(function) => self.mint_function(&function, sink, origin),
            | Plan::Arrow(..)
            | Plan::Thunk(_)
            | Plan::Return(_)
            | Plan::Force(_)
            | Plan::Lambda(_) => self.mint_over(&plan, sink, origin),
        }
    }

    /// Carry out a decode's plan: the code, and the type it denotes.
    ///
    /// # Specification
    /// - requires: every type position has been classified, so every binder a
    ///   type names is recorded as mentioned.
    /// - ensures: a binder's code is the variable at its telescope index from
    ///   the use site and a declaration's the constant, each with the written
    ///   origin; the type is the decode of that code at the universe's level, a
    ///   value type for the value sort and a computation type for the
    ///   computation sort, with the origin marked inserted.
    /// - provides: the decode half of a value name in type position.
    /// - fails: never.
    /// - panics: none.
    fn mint_decode(
        &self,
        code: Code,
        universe: Universe,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Lowered
    {
        let value = match code {
            | Code::Bound { from, binder } => sink.arena.value_variable(
                Zone::Intuitionistic,
                self.scope.telescope_index(from, binder),
            ),
            | Code::Constant(constant) => sink.arena.value_constant(constant),
        };
        sink.origins.record_value(value, origin);
        let level = Level::constant(universe.level);
        let decoded = origin.inserted(Insertion::Decode);
        match universe.sort {
            | GroundSort::Value => {
                let id = sink.arena.value_type_element(value, level);
                sink.origins.record_value_type(id, decoded);
                Lowered::ValueType(id)
            },
            | GroundSort::Computation => {
                let id = sink.arena.comp_type_element(value, level);
                sink.origins.record_comp_type(id, decoded);
                Lowered::CompType(id)
            },
        }
    }
    /// Carry out a type former's plan.
    ///
    /// # Specification
    /// trivial.
    fn mint_former(
        &self,
        former: TypeFormer,
        argument: NodeIndex,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match former {
            | TypeFormer::Thunk => self.comp_type_at(argument).map(|inner| {
                let id = sink.arena.value_type_thunk(inner);
                sink.origins.record_value_type(id, origin);
                Lowered::ValueType(id)
            }),
            | TypeFormer::Returner => self.value_type_at(argument).map(|inner| {
                let id = sink.arena.comp_type_returner(inner);
                sink.origins.record_comp_type(id, origin);
                Lowered::CompType(id)
            }),
        }
    }

    /// Carry out the plan of a former over already-minted children.
    ///
    /// # Specification
    /// trivial.
    fn mint_over(
        &self,
        plan: &Plan,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        match *plan {
            | Plan::Arrow(domain, codomain) => self.value_type_at(domain).and_then(|from| {
                self.comp_type_at(codomain).map(|to| {
                    let id = sink.arena.comp_type_arrow(from, to);
                    sink.origins.record_comp_type(id, origin);
                    Lowered::CompType(id)
                })
            }),
            | Plan::Thunk(body) => self.mint_block(body, sink).map(|suspended| {
                let id = sink.arena.value_thunk(suspended);
                sink.value(id, origin)
            }),
            | Plan::Return(value) => self.value_at(value).map(|returned| {
                let id = sink.arena.computation_return(returned);
                sink.computation(id, origin)
            }),
            | Plan::Force(value) => self.value_at(value).map(|forced| {
                let id = sink.arena.computation_force(forced);
                sink.computation(id, origin)
            }),
            | Plan::Lambda(body) => self.mint_block(body, sink).map(|under| {
                let id = sink.arena.computation_lambda(under);
                sink.computation(id, origin)
            }),
            | Plan::Unplanned
            | Plan::Variable(_)
            | Plan::Constant(_)
            | Plan::Unit
            | Plan::Literal(_)
            | Plan::Atom(_)
            | Plan::Universe(_)
            | Plan::Decode(..)
            | Plan::Former(..)
            | Plan::Transparent(_)
            | Plan::Application(..)
            | Plan::Function(_) => Maybe::Absent(lowered::Absent::Unminted),
        }
    }

    /// Mint a block: its statements bound over its last computation.
    ///
    /// # Specification
    /// - requires: every node the block names is already minted or absent.
    /// - ensures: `run x1 <- c1 ; … run xn <- cn ; c` mints as `bind(c1, …
    ///   bind(cn, c))`, each bind's origin its statement's `run` tile; a block
    ///   of no statements is its last computation; nothing is minted when any
    ///   computation of the block did not lower.
    /// - provides: the block half of thunks, lambdas and function tails.
    /// - fails: never.
    /// - panics: none.
    fn mint_block(
        &self,
        block: Block,
        sink: &mut Sink<'_>,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        let statements = stretch(&self.statements, block.statements);
        let mut chain = match self.computation_at(block.last) {
            | Maybe::Present(last) => last,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for statement in statements {
            if let Maybe::Absent(reason) = self.computation_at(statement.bound) {
                return Maybe::Absent(reason);
            }
            if let Maybe::Absent(reason) = self.origin_at(statement.run) {
                return Maybe::Absent(reason);
            }
        }
        for statement in statements.iter().rev() {
            let (Maybe::Present(bound), Maybe::Present(origin)) = (
                self.computation_at(statement.bound),
                self.origin_at(statement.run),
            )
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_bind(bound, chain);
            sink.origins.record_computation(id, origin);
            chain = id;
        }

        Maybe::Present(chain)
    }

    /// Mint an application of `head` to `arguments`, left to right.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `c(v1, …, vn)` mints as `app(… app(c, v1) …, vn)`, every
    ///   application carrying the call's origin; a call of no arguments is its
    ///   head's own computation; nothing is minted when the head or an argument
    ///   did not lower.
    /// - provides: the curried elimination of a lambda.
    /// - fails: never.
    /// - panics: none.
    fn mint_application(
        &self,
        head: NodeIndex,
        arguments: Stretch,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let mut applied = match self.computation_at(head) {
            | Maybe::Present(called) => called,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let arguments = stretch(&self.operands, arguments);
        for &argument in arguments {
            if let Maybe::Absent(reason) = self.value_at(argument) {
                return Maybe::Absent(reason);
            }
        }
        for &argument in arguments {
            let passed = match self.value_at(argument) {
                | Maybe::Present(passed) => passed,
                | Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            let id = sink.arena.computation_application(applied, passed);
            sink.origins.record_computation(id, origin);
            applied = id;
        }

        Maybe::Present(Lowered::Computation(applied))
    }

    /// Mint a function tail: its body, and its declared type when it states
    /// one.
    ///
    /// # Specification
    /// - requires: every node the plan names is already minted or absent.
    /// - ensures: `(x1: A1, …, xn: An) -> C { b }` mints its body as `thunk (λ
    ///   … λ. b)`, one lambda per parameter with the binder tile's origin and
    ///   the thunk marked as inserted at the declaration form, and its declared
    ///   type as `+U (A1 -> … -> An -> C)`, one arrow per parameter with the
    ///   binder tile's origin and `+U` the declaration form's, an arrow
    ///   dependent where a later type names its parameter; a tail missing a
    ///   parameter or result type mints the body alone; nothing is minted when
    ///   the block did not lower.
    /// - provides: the function tail's two halves, from one reading.
    /// - fails: never.
    /// - panics: none.
    fn mint_function(
        &self,
        function: &Function,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let parameters = stretch(&self.parameters, function.parameters);
        for parameter in parameters {
            if let Maybe::Absent(reason) = self.origin_at(parameter.binder) {
                return Maybe::Absent(reason);
            }
        }
        let mut body = match self.mint_block(function.block, sink) {
            | Maybe::Present(block) => block,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for parameter in parameters.iter().rev() {
            let Maybe::Present(binder) = self.origin_at(parameter.binder)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = sink.arena.computation_lambda(body);
            sink.origins.record_computation(id, binder);
            body = id;
        }
        let thunk = sink.arena.value_thunk(body);
        sink.origins
            .record_value(thunk, origin.inserted(Insertion::Thunk));

        Maybe::Present(Lowered::Function {
            signature: self.mint_signature(function, parameters, sink, origin),
            body: thunk,
        })
    }

    /// Mint a function tail's declared type, `+U (A1 -> … -> An -> C)`.
    ///
    /// # Specification
    /// - requires: `parameters` are the function's own, and every type position
    ///   has been classified, so every parameter a type names is recorded as
    ///   mentioned.
    /// - ensures: the declared type, as [`Self::mint_function`] states it, with
    ///   each parameter's arrow dependent exactly when a later parameter's type
    ///   or the result names it, and plain otherwise; nothing is minted when a
    ///   type is unstated or did not lower.
    /// - provides: the signature half of [`Self::mint_function`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parameter a later type names beside one no type
    ///   names, each asserted as the exact arrow read back out of the arena.
    /// - witness: `lower::tests::a_bare_type_binder_is_positive_at_the_fuss_free_level`
    /// - witness: `lower::tests::a_function_tail_lowers_to_a_thunked_lambda_chain`
    fn mint_signature(
        &self,
        function: &Function,
        parameters: &[Parameter],
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        let Maybe::Present(result) = function.result
        else {
            return Maybe::Absent(lowered::Absent::Unstated);
        };
        let mut declared = match self.comp_type_at(result) {
            | Maybe::Present(result) => result,
            | Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        for parameter in parameters {
            let Maybe::Present(written) = parameter.declared
            else {
                return Maybe::Absent(lowered::Absent::Unstated);
            };
            if let Maybe::Absent(reason) = self.value_type_at(written) {
                return Maybe::Absent(reason);
            }
        }
        for parameter in parameters.iter().rev() {
            let (Maybe::Present(written), Maybe::Present(binder)) =
                (parameter.declared, self.origin_at(parameter.binder))
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let Maybe::Present(domain) = self.value_type_at(written)
            else {
                return Maybe::Absent(lowered::Absent::Unminted);
            };
            let id = if bool::from(self.scope.mentioned(parameter.frame)) {
                sink.arena.comp_type_pi(domain, declared)
            }
            else {
                sink.arena.comp_type_arrow(domain, declared)
            };
            sink.origins.record_comp_type(id, binder);
            declared = id;
        }
        let id = sink.arena.value_type_thunk(declared);
        sink.origins.record_value_type(id, origin);

        Maybe::Present(id)
    }

    /// What `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn lowered_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        self.lowered
            .get(usize::from(position))
            .copied()
            .unwrap_or(Maybe::Absent(lowered::Absent::Unminted))
    }

    /// The value `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn value_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Value(id) => Maybe::Present(id),
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn computation_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ComputationId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Computation(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The value type `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn value_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::ValueType(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::CompType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The computation type `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn comp_type_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<CompTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::CompType(id) => Maybe::Present(id),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::Function { .. } => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The declared type the function tail at `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn signature_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueTypeId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Function { signature, .. } => signature,
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// The body the function tail at `position` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn function_body_at(
        &self,
        position: NodeIndex,
    ) -> Maybe<ValueId, lowered::Absent>
    {
        self.lowered_at(position).and_then(|held| match held {
            | Lowered::Function { body, .. } => Maybe::Present(body),
            | Lowered::Value(_)
            | Lowered::Computation(_)
            | Lowered::ValueType(_)
            | Lowered::CompType(_) => Maybe::Absent(lowered::Absent::OtherSort),
        })
    }

    /// Resolve every attribute against the registry and file it.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so an admitted payload already has
    ///   its core value.
    /// - ensures: every attribute of every declaration, refused or not, is
    ///   resolved against the registry and filed under the content identity of
    ///   the declaration form it decorates, in source order; an attribute
    ///   written twice for one declared name is refused wherever its two
    ///   spellings sit, and the earlier one is the one kept. A declaration's
    ///   lowering outcome does not gate its attributes: an expectation about a
    ///   refusal is read off the refused declaration, and an attribute's own
    ///   refusal competes with the declaration's other refusals by position.
    /// - provides: the attribute side table of the lowered module.
    /// - fails: [`LoweringRefusal::BudgetExceeded`] and
    ///   [`LoweringRefusal::UnknownMold`] abort the pass. Every other refusal
    ///   is offered to the declaration that owns the attribute rather than
    ///   raised.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::BudgetExceeded`] and
    /// [`LoweringRefusal::UnknownMold`].
    fn attribute(
        &mut self,
        table: &mut AttributeTable,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        let mut slots = core::mem::take(&mut self.collected.slots);
        let outcome = self.attribute_slots(&mut slots, table);
        self.collected.slots = slots;

        outcome
    }

    /// Resolve and file the attributes of every slot in `slots`.
    ///
    /// # Specification
    /// - requires: as [`Self::attribute`], over the slots taken out of the
    ///   collection.
    /// - ensures: as [`Self::attribute`].
    /// - provides: the slot walk of [`Self::attribute`].
    /// - fails: as [`Self::attribute`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::attribute`].
    fn attribute_slots(
        &mut self,
        slots: &mut [DeclarationSlot<'source>],
        table: &mut AttributeTable,
    ) -> Result<(), LoweringRefusal<'source>>
    {
        for slot in slots {
            let mut seen: Vec<(RegisteredAttribute, ByteSpan)> = Vec::new();
            for written in core::mem::take(&mut slot.attributes) {
                self.fuel.spend()?;
                match self.read_attribute(&written, &mut seen) {
                    | Ok(Filing::Filed(entry)) => {
                        table.file(self.digest_at(written.decorates), entry);
                    },
                    | Ok(Filing::Unlowered) => {},
                    | Err(refusal) => {
                        if refusal.classify() == FailureClass::EngineFault {
                            return Err(refusal);
                        }
                        slot.refuse(written.at.node, refusal);
                    },
                }
            }
        }

        Ok(())
    }

    /// Read one written attribute into an entry, or into the refusal it earns.
    ///
    /// # Specification
    /// - requires: `seen` holds the attributes already filed for this declared
    ///   name, with their spans.
    /// - ensures: a registered name whose payload its schema admits yields an
    ///   entry carrying the payload's already-minted value, and joins `seen`; a
    ///   payload whose form is not a value at all is refused before its schema
    ///   is consulted, because being no value is a different fact from being
    ///   the wrong one; nothing is filed for a payload the mint sweep left
    ///   unlowered, which is the case of a payload that itself refused.
    /// - provides: the per-attribute half of the attribute pass.
    /// - fails: yields the unknown-attribute refusal with its bounded
    ///   suggestion, the duplicate refusal naming the first spelling, the
    ///   non-value-payload refusal, the missing-payload refusal, or the
    ///   ill-typed-payload refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// The attribute's refusal.
    fn read_attribute(
        &self,
        written: &WrittenAttribute<'source>,
        seen: &mut Vec<(RegisteredAttribute, ByteSpan)>,
    ) -> Result<Filing, LoweringRefusal<'source>>
    {
        let Maybe::Present((name, schema)) = AttributeRegistry::lookup(written.name)
        else {
            return Err(LoweringRefusal::UnknownAttribute {
                span: written.span,
                name: written.name,
                suggestion: AttributeRegistry::suggestion(written.name),
            });
        };
        if let Some(&(_held, first)) = seen.iter().find(|&&(held, _first)| held == name) {
            return Err(LoweringRefusal::DuplicateAttribute {
                span: written.span,
                name: written.name,
                first,
            });
        }
        let form = self.payload_form_of(written, name)?;
        match payload_verdict(schema, form) {
            | PayloadVerdict::Admitted => {},
            | PayloadVerdict::Missing => {
                return Err(LoweringRefusal::MissingPayload {
                    span: written.span,
                    name,
                    expected: schema,
                });
            },
            | PayloadVerdict::IllTyped => {
                let span = match written.payload {
                    | Payload::Written(payload) => payload.span,
                    | Payload::Unwritten => written.span,
                };
                return Err(LoweringRefusal::IllTypedPayload {
                    span,
                    name,
                    expected: schema,
                    written: form,
                });
            },
        }
        let value = match written.payload {
            | Payload::Unwritten => Maybe::Absent(payload::Absent::Marker),
            | Payload::Written(placed) => {
                let Maybe::Present(value) = self.value_at(placed.node)
                else {
                    return Ok(Filing::Unlowered);
                };
                Maybe::Present(value)
            },
        };
        seen.push((name, written.span));

        Ok(Filing::Filed(AttributeEntry::new(
            name,
            schema,
            value,
            written.span,
        )))
    }

    /// The form an attribute's payload was written in.
    ///
    /// # Specification
    /// - requires: `name` is the registered name `written` resolved to.
    /// - ensures: the absent form for no payload, and the payload form of the
    ///   payload's former otherwise.
    /// - provides: the syntactic half of the payload verdict.
    /// - fails: yields the non-value-payload refusal for a payload that cannot
    ///   stand as a value, and [`LoweringRefusal::UnknownMold`] for a foreign
    ///   mold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LoweringRefusal::NonValuePayload`] and
    /// [`LoweringRefusal::UnknownMold`].
    fn payload_form_of(
        &self,
        written: &WrittenAttribute<'source>,
        name: RegisteredAttribute,
    ) -> Result<PayloadForm, LoweringRefusal<'source>>
    {
        let Payload::Written(placed) = written.payload
        else {
            return Ok(PayloadForm::Absent);
        };
        let (shape, value) = self.payload_former(placed)?;
        let Shape::Form { name: form, former } = shape
        else {
            return Ok(PayloadForm::OtherValue);
        };
        if !value.0 {
            return Err(LoweringRefusal::NonValuePayload {
                span: placed.span,
                name,
                form,
            });
        }

        Ok(payload_form(former))
    }

    /// The content identity of the node at `position`.
    ///
    /// # Specification
    /// trivial.
    fn digest_at(
        &self,
        position: NodeIndex,
    ) -> NodeDigest
    {
        self.tree
            .node(position)
            .map_or_else(|| NodeDigest::from([0_u8; 32_usize]), Node::digest)
    }

    /// Assemble one declaration per slot, in admission order.
    ///
    /// # Specification
    /// - requires: the classification, the mint sweep and the attribute pass
    ///   have all run.
    /// - ensures: a slot holding a refusal yields the refused outcome; a slot
    ///   whose signature and definition both lowered yields the completed
    ///   outcome — a witness's definition being the member it re-states; a
    ///   signature alone yields the uncompleted outcome, which is the
    ///   obligation this module owes; a definition alone yields the bodiless
    ///   outcome. A held slot holding no refusal yields nothing, and neither
    ///   does a witness whose member refused: there is no member to state a
    ///   second type for. Each declaration keeps its container and its role,
    ///   and takes its own origin token, handed out in admission order.
    /// - provides: the declaration list a checker drives.
    /// - fails: never — a slot with neither half lowered and no refusal
    ///   contributes no declaration, which the classification makes unreachable
    ///   for every slot but a held one.
    /// - panics: none.
    fn assemble(
        &self,
        origins: &mut OriginTable,
    ) -> Vec<LoweredDeclaration<'source>>
    {
        let mut declarations = Vec::with_capacity(self.collected.slots.len());
        for (position, slot) in self.collected.slots.iter().enumerate() {
            let Maybe::Present(outcome) = self.outcome(SlotIndex::from(position), slot)
            else {
                continue;
            };
            let introduced = slot.introduced_by;
            let origin = origins.record_declaration(Origin::new(
                introduced.node,
                self.digest_at(introduced.node),
                introduced.span,
            ));
            declarations.push(LoweredDeclaration::from(DeclarationParts {
                name: slot.name,
                container: slot.container,
                role: slot.role,
                constant: slot.constant,
                span: introduced.span,
                origin,
                signature: slot
                    .signature
                    .map(|half| self.digest_at(half.declaration.node)),
                definition: slot
                    .definition
                    .map(|half| self.digest_at(half.declaration.node)),
                outcome,
            }));
        }

        declarations
    }

    /// What the slot at `position` amounts to.
    ///
    /// # Specification
    /// trivial.
    fn outcome(
        &self,
        position: SlotIndex,
        slot: &DeclarationSlot<'source>,
    ) -> Maybe<DeclarationOutcome<'source>, lowered::Absent>
    {
        if let Maybe::Present((_at, refusal)) = slot.refusal {
            return Maybe::Present(DeclarationOutcome::Refused(refusal));
        }
        if let Maybe::Present(Half {
            operand: Operand::Member(target),
            ..
        }) = slot.definition
            && let Some(Maybe::Present(_)) = self
                .collected
                .slots
                .get(usize::from(target))
                .map(|member| member.refusal)
        {
            return Maybe::Absent(lowered::Absent::Unminted);
        }
        let declared = match slot.signature {
            | Maybe::Present(half) => match half.operand {
                | Operand::Written(written) => self.value_type_at(written.node),
                | Operand::Function => self.signature_at(half.declaration.node),
                | Operand::Member(_) => Maybe::Absent(lowered::Absent::Unminted),
            },
            | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        let body = match slot.definition {
            | Maybe::Present(half) => match half.operand {
                | Operand::Written(written) => self.value_at(written.node),
                | Operand::Function => self.function_body_at(half.declaration.node),
                | Operand::Member(_) => self
                    .witnessed
                    .get(&position)
                    .copied()
                    .map_or(Maybe::Absent(lowered::Absent::Unminted), Maybe::Present),
            },
            | Maybe::Absent(_) => Maybe::Absent(lowered::Absent::Unminted),
        };
        match (declared, body) {
            | (Maybe::Present(declared_type), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Completed {
                    declared_type,
                    body,
                })
            },
            | (Maybe::Present(declared_type), Maybe::Absent(_)) => {
                Maybe::Present(DeclarationOutcome::Uncompleted { declared_type })
            },
            | (Maybe::Absent(_), Maybe::Present(body)) => {
                Maybe::Present(DeclarationOutcome::Bodied { body })
            },
            | (Maybe::Absent(reason), Maybe::Absent(_)) => Maybe::Absent(reason),
        }
    }

    /// Carry each refused manifest type component's refusal to every
    /// declaration whose type names it.
    ///
    /// # Specification
    /// - requires: the classification has run.
    /// - ensures: a declaration owning a type head that stands for a manifest
    ///   component whose type refused holds that refusal too, at the head's
    ///   position, so it keeps the lowest-positioned refusal it has; the
    ///   components are taken in signature order, so a component naming an
    ///   earlier refused one passes the refusal on.
    /// - provides: the rule that a declaration is not minted over a type that
    ///   did not lower.
    /// - fails: never.
    /// - panics: none.
    fn propagate_manifests(&mut self)
    {
        let mut named = core::mem::take(&mut self.manifests);
        named.sort_by_key(|&(held, _head)| held);
        for &(held, head) in &named {
            let Some(Maybe::Present((_at, refusal))) = self
                .collected
                .slots
                .get(usize::from(held))
                .map(|slot| slot.refusal)
            else {
                continue;
            };
            let Maybe::Present(owner) = self.collected.owner_of(head)
            else {
                continue;
            };
            if let Some(slot) = self.collected.slots.get_mut(usize::from(owner)) {
                slot.refuse(head, refusal);
            }
        }
        self.manifests = named;
    }

    /// One stratum item per module, in pre-order.
    ///
    /// # Specification
    /// - requires: the mint sweep has run.
    /// - ensures: each module's path, its form's bytes, the value components
    ///   and nested modules it exports in export order, each manifest type
    ///   component with the type it lowered to, and whether matching coerced
    ///   its body; a hidden member appears in no item.
    /// - provides: the stratum half of [`LoweredModule`].
    /// - fails: never.
    /// - panics: none.
    fn structures(&self) -> Vec<LoweredStructure<'source>>
    {
        let mut lowered = Vec::with_capacity(self.collected.structures.len());
        for (position, structure) in self.collected.structures.iter().enumerate() {
            let mut values = Vec::new();
            let mut modules = Vec::new();
            for &export in &structure.exports {
                match export {
                    | Member::Slot(slot) => {
                        if let Some(member) = self.collected.slots.get(usize::from(slot)) {
                            values.push(ValueComponent {
                                name: member.name,
                                constant: member.constant,
                            });
                        }
                    },
                    | Member::Module(nested) => {
                        if let Some(member) = self.collected.structures.get(usize::from(nested)) {
                            modules.push(member.name);
                        }
                    },
                }
            }
            let types = structure
                .types
                .iter()
                .map(|manifest| ManifestComponent {
                    name: manifest.name,
                    defined: match self.value_type_at(manifest.defined.node) {
                        | Maybe::Present(defined) => Maybe::Present(defined),
                        | Maybe::Absent(_) => Maybe::Absent(manifest_type::Absent::Unlowered),
                    },
                })
                .collect();
            lowered.push(LoweredStructure::new(
                self.collected
                    .path(Container::Module(StructureIndex::from(position))),
                structure.declared_by.span,
                values,
                modules,
                types,
                structure.coerced,
            ));
        }

        lowered
    }
}

/// What reading one attribute produced, short of a refusal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Filing
{
    /// The entry to file.
    Filed(AttributeEntry),
    /// Nothing: the payload did not lower, which only a payload that itself
    /// refused leaves behind.
    Unlowered,
}

impl Sink<'_>
{
    /// Write `bridge` over `minted`, the core node of the syntax node at
    /// `origin`.
    ///
    /// # Specification
    /// - requires: `minted` is what the node's own plan minted.
    /// - ensures: a bare node is `minted` unchanged; a forced value is minted
    ///   as a force over it, a returned value type as a returner over it, and a
    ///   quoted type as the quote of it at its own sort, each with `origin`
    ///   marked as the insertion it is; nothing when the node did not lower at
    ///   the sort its bridge leaves, which the classification makes
    ///   unreachable.
    /// - provides: the minting half of the insertions a position's sort
    ///   decides.
    /// - fails: never.
    /// - panics: none.
    fn bridge(
        &mut self,
        minted: Maybe<Lowered, lowered::Absent>,
        bridge: Bridge,
        origin: Origin,
    ) -> Maybe<Lowered, lowered::Absent>
    {
        let Bridge::Inserted(insertion) = bridge
        else {
            return minted;
        };
        let inserted = origin.inserted(insertion);
        match (minted, insertion) {
            | (Maybe::Present(Lowered::Value(forced)), Insertion::Force) => {
                let id = self.arena.computation_force(forced);
                Maybe::Present(self.computation(id, inserted))
            },
            | (Maybe::Present(Lowered::ValueType(returned)), Insertion::Returner) => {
                let id = self.arena.comp_type_returner(returned);
                self.origins.record_comp_type(id, inserted);
                Maybe::Present(Lowered::CompType(id))
            },
            | (Maybe::Present(Lowered::ValueType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            | (Maybe::Present(Lowered::CompType(quoted)), Insertion::Quote) => {
                let id = self.arena.value_quote_computation(quoted);
                Maybe::Present(self.value(id, inserted))
            },
            | (
                Maybe::Present(_),
                Insertion::Force
                | Insertion::Thunk
                | Insertion::Returner
                | Insertion::Quote
                | Insertion::Decode,
            ) => Maybe::Absent(lowered::Absent::OtherSort),
            | (Maybe::Absent(reason), _) => Maybe::Absent(reason),
        }
    }

    /// Record `id`'s origin and wrap it as a lowered value.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        id: ValueId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_value(id, origin);

        Lowered::Value(id)
    }

    /// Record `id`'s origin and wrap it as a lowered computation.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        id: ComputationId,
        origin: Origin,
    ) -> Lowered
    {
        self.origins.record_computation(id, origin);

        Lowered::Computation(id)
    }

    /// Mint `atom`'s value type and record its origin.
    ///
    /// # Specification
    /// trivial.
    fn atom(
        &mut self,
        atom: TypeAtom,
        origin: Origin,
    ) -> Lowered
    {
        let id = match atom {
            | TypeAtom::Unit => self.arena.value_type_unit(),
            | TypeAtom::Integer => self.arena.value_type_base(BaseType::Integer),
            | TypeAtom::Text => self.arena.value_type_base(BaseType::String),
        };
        self.origins.record_value_type(id, origin);

        Lowered::ValueType(id)
    }
}

/// The parameter of a lambda: exactly one identifier between parentheses.
///
/// # Specification
/// - requires: `cursor` stands just past the lambda's `fn`.
/// - ensures: the one parameter's tile, with the cursor past the closing
///   parenthesis.
/// - provides: the binder reading of the lambda.
/// - fails: yields the unadmitted refusal for a typed parameter, the arity
///   refusal for any parameter count but one, and a misplaced-tile refusal for
///   a parameter list out of shape.
/// - panics: none.
///
/// # Errors
/// The lambda's refusal.
fn parameter<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
) -> Result<Placed, LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    let mut first: Option<Placed> = None;
    let mut count = 0_usize;
    loop {
        if let Maybe::Present(binder) = cursor.tile(TileName::IDENTIFIER) {
            count = count.saturating_add(1_usize);
            first = first.or(Some(binder));
            continue;
        }
        if let Maybe::Present(_) = cursor.tile(TileName::COMMA) {
            continue;
        }
        if let Maybe::Present(_) = cursor.at(TileName::COLON) {
            return Err(site.folded(FormName::PARAMETER, FragmentBoundary::Unadmitted));
        }
        if let Maybe::Present(_) = cursor.tile(TileName::PAREN_CLOSE) {
            break;
        }
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    match first {
        | Some(binder) if count == 1_usize => Ok(binder),
        | Some(_) | None => Err(site.out(FragmentBoundary::Arity(OperandCount::from(count)))),
    }
}

/// The statements a block opens with a keyword the fragment does not read, by
/// that keyword, with the form a refusal names each by; `fork` is read apart,
/// because its two statements share the keyword.
const UNREAD_STATEMENTS: [(TileName, FormName); 6_usize] = [
    (TileName::VAL, FormName::LET_STATEMENT),
    (TileName::UNPACK, FormName::UNPACK_STATEMENT),
    (TileName::LETA, FormName::LETA_STATEMENT),
    (TileName::RECV, FormName::RECV_STATEMENT),
    (TileName::ACQUIRE, FormName::ACQUIRE_STATEMENT),
    (TileName::RELEASE, FormName::RELEASE_STATEMENT),
];

/// The statement the tile `label`, at `cursor`, opens.
///
/// # Specification
/// - requires: `cursor` stands at the tile `label`, in a block, at a place a
///   statement may start.
/// - ensures: the statement form the keyword opens — `fork` followed by `!` the
///   shared fork — and the absence for a tile that opens no statement.
/// - provides: the names a block's refused statements are written as;
///   [`statement::Absent::NotAKeyword`] for a tile no statement starts with.
/// - fails: never.
/// - panics: none.
fn statement_form(
    label: TileName,
    cursor: &Cursor<'_>,
) -> Maybe<FormName, statement::Absent>
{
    if label == TileName::FORK {
        let mut ahead = cursor.clone();
        let _fork = ahead.read();
        return Maybe::Present(match ahead.at(TileName::BANG) {
            | Maybe::Present(_) => FormName::FORK_SHARED_STATEMENT,
            | Maybe::Absent(_) => FormName::FORK_STATEMENT,
        });
    }

    UNREAD_STATEMENTS
        .iter()
        .find(|&&(keyword, _form)| keyword == label)
        .map_or(
            Maybe::Absent(statement::Absent::NotAKeyword),
            |&(_keyword, form)| Maybe::Present(form),
        )
}

/// Read a parenthesised, comma-separated argument list into `written`.
///
/// # Specification
/// - requires: `cursor` stands at the list's `(`.
/// - ensures: every argument written is appended to `written`, left to right,
///   with the cursor past the closing `)` and nothing after it; empty
///   parentheses append nothing.
/// - provides: the argument reading of calls and type applications.
/// - fails: yields the hole's own refusal for an empty or juxtaposed argument,
///   and a misplaced-tile refusal for a list out of shape; the arguments read
///   before the refusal stay appended.
/// - panics: none.
///
/// # Errors
/// The form's refusal.
fn arguments<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    written: &mut Vec<NodeIndex>,
) -> Result<(), LoweringRefusal<'source>>
{
    if let Maybe::Absent(_) = cursor.tile(TileName::PAREN_OPEN) {
        return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
    }
    let start = written.len();
    loop {
        let run = cursor.operands();
        let closing = cursor.tile(TileName::PAREN_CLOSE);
        if let (Run::Empty(_), Maybe::Present(_)) = (run, closing)
            && written.len() == start
        {
            break;
        }
        let argument = site.one(run)?;
        written.push(argument.node);
        if let Maybe::Present(_) = closing {
            break;
        }
        if let Maybe::Absent(_) = cursor.tile(TileName::COMMA) {
            return Err(site.fault(cursor.here(), FormFault::MisplacedTile));
        }
    }

    exhausted(site, cursor)
}

/// The entries of `store` that `stretch` names.
///
/// # Specification
/// trivial.
fn stretch<Entry>(
    store: &[Entry],
    stretch: Stretch,
) -> &[Entry]
{
    store.get(stretch.start .. stretch.end).unwrap_or(&[])
}

/// Read the closing tile `label`, refusing anything else in its place.
///
/// # Specification
/// trivial.
fn closed<'source>(
    site: Site,
    cursor: &mut Cursor<'_>,
    label: TileName,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.tile(label) {
        | Maybe::Present(_) => Ok(()),
        | Maybe::Absent(_) => Err(site.fault(cursor.here(), FormFault::MisplacedTile)),
    }
}

/// Refuse a piece left after a form's last.
///
/// # Specification
/// trivial.
fn exhausted<'source>(
    site: Site,
    cursor: &Cursor<'_>,
) -> Result<(), LoweringRefusal<'source>>
{
    match cursor.peek() {
        | Maybe::Absent(_) => Ok(()),
        | Maybe::Present(Piece::Operand(stray)) => {
            Err(site.fault(stray.span, FormFault::ExtraOperand))
        },
        | Maybe::Present(Piece::Tile { at, .. }) => {
            Err(site.fault(at.span, FormFault::MisplacedTile))
        },
    }
}

/// Whether a form can stand where a value is expected.
///
/// # Specification
/// - requires: nothing; the function is total over the former vocabulary.
/// - ensures: exactly the value-producing formers answer affirmatively — a
///   name, a capitalised name, a number, a string, a parenthesised expression
///   and a thunk — the reserved tuple among them, since a reserved form is a
///   value the fragment declines rather than a form of another sort, and
///   keeping the two apart is what lets an attribute payload written as a
///   computation be reported as a non-value rather than as a sort error.
/// - provides: the guard the attribute payload reading takes.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the vocabulary is a finite class, enumerated exhaustively
///   with each former's exact answer asserted, so promoting or demoting any
///   single former breaks one row.
/// - witness: `lower::tests::only_the_value_forms_can_stand_as_a_payload`
const fn is_value_form(former: Former) -> ValueForm
{
    ValueForm(matches!(
        former,
        Former::Name
            | Former::Constructor
            | Former::Number
            | Former::Text
            | Former::Parenthesized
            | Former::Thunk
    ))
}

/// Parse a literal's own text into a core literal.
///
/// # Specification
/// - requires: `text` is the literal node's whole source text.
/// - ensures: a number is the canonical non-negative magnitude of its digits,
///   so a padded spelling and its unpadded form are one literal; a string is
///   the text between its delimiting quotes with its escapes decoded — `\n`,
///   `\t`, `\r`, `\0`, `\\`, `\"` and `\'` to the character each names, a
///   backslash before a line break elided with the break, any other escaped
///   character to itself, and a trailing lone backslash dropped.
/// - provides: the only place a lexeme becomes a core literal.
/// - fails: never; the malformed absence for a number holding a non-digit or
///   nothing at all and a string missing either delimiter, and the
///   not-a-literal absence for every other former.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two decision surfaces (the magnitude guard and the
///   delimiter strip) and the escape table, separated by a padded integer, an
///   empty integer, an integer holding a letter, a quoted text, an escaped
///   text, an unterminated text, a bare quote and an unquoted text, each
///   asserted as an exact literal or absence.
/// - witness: `lower::tests::an_integer_literal_is_its_canonical_magnitude`
/// - witness: `lower::tests::a_text_literal_is_the_bytes_between_its_quotes`
/// - witness: `lower::tests::a_lexeme_of_the_wrong_shape_parses_to_nothing`
fn parse_literal(
    former: Former,
    text: SourceFragment<'_>,
) -> Maybe<Literal, literal::Absent>
{
    let spelled: &str = text.as_ref();
    let found = match former {
        | Former::Number => Magnitude::from_decimal_text(String::from(spelled))
            .map(|magnitude| Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))),
        | Former::Text => spelled
            .strip_prefix('"')
            .and_then(|opened| opened.strip_suffix('"'))
            .map(|content| {
                Literal::Text(StringLiteral::new(decode_escapes(SourceFragment::from(
                    content,
                ))))
            }),
        | Former::Name
        | Former::Constructor
        | Former::Parenthesized
        | Former::Thunk
        | Former::Lambda
        | Former::Return
        | Former::Force
        | Former::Call
        | Former::Projection
        | Former::TypeHead
        | Former::Universe
        | Former::TypeApplication
        | Former::ThunkType
        | Former::ReturnerType
        | Former::ArrowType
        | Former::ProductType
        | Former::ParenthesizedType
        | Former::Declaration
        | Former::AttributeBlock
        | Former::Import
        | Former::Module
        | Former::Unadmitted => return Maybe::Absent(literal::Absent::NotALiteral),
    };

    found.map_or(Maybe::Absent(literal::Absent::Malformed), Maybe::Present)
}

/// Decode the escapes of a string literal's or an import address's content.
///
/// # Specification
/// trivial.
#[inline]
pub fn decode_escapes(content: SourceFragment<'_>) -> String
{
    let spelled: &str = content.as_ref();
    let mut decoded = String::with_capacity(spelled.len());
    let mut chars = spelled.chars().peekable();
    while let Some(character) = chars.next() {
        if character != '\\' {
            decoded.push(character);
            continue;
        }
        match chars.next() {
            | Some('n') => decoded.push('\n'),
            | Some('t') => decoded.push('\t'),
            | Some('r') => decoded.push('\r'),
            | Some('0') => decoded.push('\0'),
            | Some('\r') => {
                if chars.peek() == Some(&'\n') {
                    let _break = chars.next();
                }
            },
            | Some('\n') | None => {},
            | Some(other) => decoded.push(other),
        }
    }

    decoded
}

/// Whether `text` is a numeric lexeme with a fraction or an exponent.
///
/// # Specification
/// trivial.
fn fractional(text: SourceFragment<'_>) -> Fractional
{
    let spelled: &str = text.as_ref();
    let (mantissa, exponent) = spelled
        .split_once(['e', 'E'])
        .map_or((spelled, None), |(left, right)| (left, Some(right)));
    let (whole, fraction) = mantissa
        .split_once('.')
        .map_or((mantissa, None), |(left, right)| (left, Some(right)));
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let fraction_ok = fraction.is_none_or(digits);
    let exponent_ok =
        exponent.is_none_or(|part| digits(part.strip_prefix(['+', '-']).unwrap_or(part)));
    let marked = fraction.is_some() || exponent.is_some();

    Fractional(marked && digits(whole) && fraction_ok && exponent_ok)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_term::CompType;
    use gandr_core_term::Computation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::SyntaxTree;
    use quenchant_shape::shape::Maybe;

    use super::Fuel;
    use super::LoweringBudget;
    use super::is_value_form;
    use super::literal;
    use super::lower_module;
    use super::parse_literal;
    use crate::attribute::AttributeRegistry;
    use crate::attribute::AttributeSchema;
    use crate::attribute::payload_form;
    use crate::classify::FailureClass;
    use crate::error::FormFault;
    use crate::error::FragmentBoundary;
    use crate::error::FragmentSort;
    use crate::error::LoweringRefusal;
    use crate::error::refusal_span;
    use crate::fixture::Handmade;
    use crate::fixture::Rule;
    use crate::fixture::Spelled;
    use crate::fixture::grammar;
    use crate::fixture::parsed;
    use crate::fixture::registered;
    use crate::fixture::repaired;
    use crate::fixture::span;
    use crate::form::FormName;
    use crate::form::Former;
    use crate::form::Repair;
    use crate::module::DeclarationOutcome;
    use crate::module::LoweredDeclaration;
    use crate::module::LoweredModule;
    use crate::namespace::Recognition;
    use crate::origin::Insertion;
    use crate::origin::OriginCount;
    use crate::origin::Provenance;
    use crate::resolve::HeadArity;
    use crate::resolve::OperandCount;
    use crate::resolve::SurfaceName;

    /// The module the parser and the lowering make of `source`, which both
    /// must accept.
    ///
    /// # Specification
    /// trivial.
    fn lowered<'source>(
        source: SourceText<'source>,
        arena: &mut CoreArena,
    ) -> LoweredModule<'source>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        lower_module(
            &pbg,
            &tree,
            arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap()
    }

    /// What each declaration of `module` amounts to, in admission order.
    ///
    /// # Specification
    /// trivial.
    fn outcomes<'source>(module: &LoweredModule<'source>) -> Vec<DeclarationOutcome<'source>>
    {
        module
            .declarations()
            .iter()
            .map(LoweredDeclaration::outcome)
            .collect()
    }

    /// The refusal the first declaration of `tree` carries.
    ///
    /// # Specification
    /// trivial.
    fn refusal_in<'source>(
        pbg: &Pbg,
        tree: &SyntaxTree<'source>,
    ) -> LoweringRefusal<'source>
    {
        let mut arena = CoreArena::new();
        let module = lower_module(
            pbg,
            tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap();
        let Some(DeclarationOutcome::Refused(refusal)) = outcomes(&module).first().copied()
        else {
            panic!("the first declaration is refused");
        };

        refusal
    }

    /// The refusal the first declaration of `source` carries, which the
    /// parser must accept cleanly.
    ///
    /// # Specification
    /// trivial.
    fn refusal(source: SourceText<'_>) -> LoweringRefusal<'_>
    {
        let pbg = grammar();
        let tree = parsed(&pbg, source);

        refusal_in(&pbg, &tree)
    }

    /// The value `body` of `outcome`, which must lower a body.
    ///
    /// # Specification
    /// trivial.
    fn body_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueId
    {
        match outcome {
            | DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body } => {
                body
            },
            | DeclarationOutcome::Uncompleted { .. } | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a body")
            },
        }
    }

    /// The declared type of `outcome`, which must lower a signature.
    ///
    /// # Specification
    /// trivial.
    fn declared_of(outcome: DeclarationOutcome<'_>) -> gandr_core_term::ValueTypeId
    {
        match outcome {
            | DeclarationOutcome::Completed { declared_type, .. }
            | DeclarationOutcome::Uncompleted { declared_type } => declared_type,
            | DeclarationOutcome::Bodied { .. } | DeclarationOutcome::Refused(_) => {
                panic!("the declaration lowers a signature")
            },
        }
    }

    /// The schema `name` is registered with.
    ///
    /// # Specification
    /// trivial.
    fn schema_of(name: SurfaceName<'_>) -> AttributeSchema
    {
        let Maybe::Present((_entry, schema)) = AttributeRegistry::lookup(name)
        else {
            panic!("the name is registered");
        };

        schema
    }

    /// The integer literal `digits` spell.
    ///
    /// # Specification
    /// trivial.
    fn integer(digits: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = digits.as_ref();
        let magnitude = Magnitude::from_decimal_text(String::from(spelled)).unwrap();

        Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
    }

    /// The text literal holding `content`.
    ///
    /// # Specification
    /// trivial.
    fn text(content: SourceFragment<'_>) -> Literal
    {
        let spelled: &str = content.as_ref();

        Literal::Text(StringLiteral::new(String::from(spelled)))
    }

    #[test]
    fn a_completed_declaration_lowers_both_halves()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a signature and its definition pair into one completed declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the signature lowers to the declared type"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the definition lowers to the body"
        );
    }

    #[test]
    fn an_uncompleted_signature_is_the_obligation_producer()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : Integer ;"), &mut arena);
        let [DeclarationOutcome::Uncompleted { declared_type }] = outcomes(&module)[..]
        else {
            panic!("a signature alone is an uncompleted declaration");
        };

        assert_eq!(
            arena.value_type(declared_type),
            Some(&ValueType::Base(BaseType::Integer)),
            "the obligation carries the declared type"
        );
    }

    #[test]
    fn a_bodiless_definition_lowers_its_body_alone()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = 3 ;"), &mut arena);
        let [DeclarationOutcome::Bodied { body }] = outcomes(&module)[..]
        else {
            panic!("a definition alone is a bodiless declaration");
        };

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the body lowers alone"
        );
    }

    #[test]
    fn the_thunk_and_returner_heads_lower_to_their_formers()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : +U (-F Integer) ;"), &mut arena);
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Returner(returned)) = arena.comp_type(suspended)
        else {
            panic!("`-F` lowers to the returner type");
        };

        assert_eq!(
            arena.value_type(returned),
            Some(&ValueType::Base(BaseType::Integer)),
            "the returner carries its value type"
        );
    }

    #[test]
    fn the_bridge_tokens_are_compound_and_sum_is_unaffected()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let sum = |start: usize, end: usize| LoweringRefusal::OutOfFragment {
            span: at(start, end),
            form: FormName::from(NamedKind("sum_type")),
            sort: FragmentSort::ValueType,
            boundary: FragmentBoundary::Unadmitted,
        };

        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x : +U(-F Integer) ;"), &mut arena);
        assert!(
            matches!(
                arena.value_type(declared_of(outcomes(&module)[0])),
                Some(&ValueType::Thunk(_))
            ),
            "`+U` against a bracket is the bridge"
        );
        assert_eq!(
            refusal(SourceText::from("def s : Integer + Unit ;")),
            sum(8_usize, 22_usize),
            "`A + B` is the sum"
        );
        assert_eq!(
            refusal(SourceText::from("def s : Integer +Unit ;")),
            sum(8_usize, 21_usize),
            "a sign against a word that begins with the bridge letter is still the sum"
        );
        for source in [
            "def x : Integer +U Integer ;",
            "def x : Integer -F Integer ;",
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::MalformedForm {
                    span: at(16_usize, 26_usize),
                    form: FormName::DECLARATION,
                    fault: FormFault::ExtraOperand,
                },
                "a bridge after an operand is no sum, and `{source}` is refused"
            );
        }
    }

    #[test]
    fn an_arrow_lowers_under_a_thunk_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g : +U (Integer -> -F Integer) ;"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("`+U` lowers to the thunk type");
        };
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(suspended)
        else {
            panic!("the arrow lowers to the function type");
        };

        assert_eq!(
            arena.value_type(domain),
            Some(&ValueType::Base(BaseType::Integer)),
            "the domain is a value type"
        );
        assert!(
            matches!(arena.comp_type(codomain), Some(&CompType::Returner(_))),
            "the codomain is a computation type"
        );
    }

    #[test]
    fn every_type_atom_lowers_to_its_core_type()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def u : Unit ; def i : Integer ; def s : String ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                Some(ValueType::Unit),
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
            ],
            "each atom lowers to its own core type"
        );
    }

    #[test]
    fn every_universe_spelling_lowers_to_its_universe()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a : Type ; def b : Type[+] ; def c : Type[-] ; def d : Type[+, 3] ; def e : \
                 Type[-, 1] ;",
            ),
            &mut arena,
        );
        let universe = |sort: GroundSort, level: u64| {
            Some(ValueType::Universe {
                sort: Sort::Ground(sort),
                level: Level::constant(LevelConstant::from(level)),
            })
        };
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| arena.value_type(declared_of(outcome)).cloned())
            .collect();

        assert_eq!(
            lowered,
            [
                universe(GroundSort::Value, 0),
                universe(GroundSort::Value, 0),
                universe(GroundSort::Computation, 0),
                universe(GroundSort::Value, 3),
                universe(GroundSort::Computation, 1),
            ],
            "a universe is the sort and the level written, the value sort and level zero for \
             whichever is left off"
        );
    }

    #[test]
    fn u_and_f_are_names()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, name, arity) in [
            ("def x : U ;", "U", HeadArity::Nullary),
            ("def x : F ;", "F", HeadArity::Nullary),
            ("def x : U(Integer) ;", "U", HeadArity::Unary),
            ("def x : F(Integer) ;", "F", HeadArity::Unary),
        ] {
            assert_eq!(
                refusal(SourceText::from(source)),
                LoweringRefusal::UnresolvedTypeHead {
                    span: at(8_usize, 9_usize),
                    name: SurfaceName::from(name),
                    arity,
                },
                "the bridges are `+U` and `-F`, so `{source}` names a type nothing declares"
            );
        }
    }

    #[test]
    fn a_bare_type_binder_is_positive_at_the_fuss_free_level()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def id(a : Type, x : a) -> -F a { ret x }"),
            &mut arena,
        );
        let declared = declared_of(outcomes(&module)[0]);
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi {
            domain: universe,
            codomain,
        }) = arena.comp_type(suspended)
        else {
            panic!("`a`, which a later type names, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`x`, which no type names, binds a plain arrow");
        };
        let Some(&CompType::Returner(returned)) = arena.comp_type(result)
        else {
            panic!("the result is a returner");
        };
        let decoded = |id| match arena.value_type(id) {
            | Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        let fuss_free = Level::constant(LevelConstant::ZERO);
        let innermost = Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        };

        assert_eq!(
            arena.value_type(universe),
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: fuss_free.clone(),
            }),
            "a bare `Type` is the value universe at the fuss-free level"
        );
        assert_eq!(
            decoded(domain),
            (Some(innermost.clone()), Some(fuss_free.clone())),
            "`x : a` decodes `a` out of the universe it was bound at"
        );
        assert_eq!(
            decoded(returned),
            (Some(innermost), Some(fuss_free)),
            "the plain arrow binds nothing, so the result names `a` at the same index"
        );
        assert_eq!(
            module
                .origins()
                .value_type(domain)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Decode)),
            "the decode is the lowering's, not the source's"
        );
    }

    #[test]
    fn a_decode_reads_the_universe_its_code_was_written_at()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def small : Type[+, 1] ; def n : small ; def k(c : (Type[-, 2]), t : +U c) -> c \
                 { force t }",
            ),
            &mut arena,
        );
        let lowered = outcomes(&module);
        let decoded = |id| match arena.value_type(id) {
            | Some(&ValueType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        assert_eq!(
            decoded(declared_of(lowered[1])),
            (
                Some(Value::Constant(ConstantIndex::from(0_usize))),
                Some(Level::constant(LevelConstant::from(1_u64)))
            ),
            "a declaration signed at a universe decodes at that universe's level"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(lowered[2]))
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(suspended)
        else {
            panic!("`c`, which later types name, binds a dependent arrow");
        };
        let Some(&CompType::Arrow {
            domain,
            codomain: result,
        }) = arena.comp_type(codomain)
        else {
            panic!("`t`, which no type names, binds a plain arrow");
        };
        let Some(&ValueType::Thunk(thunked)) = arena.value_type(domain)
        else {
            panic!("`+U c` is a thunk type");
        };
        let comp_decoded = |id| match arena.comp_type(id) {
            | Some(&CompType::Element { code, ref target }) => {
                (arena.value(code).cloned(), Some(target.clone()))
            },
            | _ => (None, None),
        };
        let code = (
            Some(Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            Some(Level::constant(LevelConstant::from(2_u64))),
        );
        assert_eq!(
            comp_decoded(thunked),
            code,
            "a binder written at the computation universe, through a grouping, decodes a \
             computation type at its level"
        );
        assert_eq!(
            comp_decoded(result),
            code,
            "and a result naming it is that computation type, with no returner"
        );
    }

    #[test]
    fn a_type_where_a_value_is_read_is_quoted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def a = Integer ; def b = -F Integer ; def c = Type ; def d = +U (-F Integer) ;",
            ),
            &mut arena,
        );
        let quoted = |declaration: usize| {
            let body = body_of(outcomes(&module)[declaration]);
            let provenance = module
                .origins()
                .value(body)
                .map(|origin| origin.provenance());
            match arena.value(body) {
                | Some(&Value::Quote(inner)) => {
                    (arena.value_type(inner).cloned(), None, provenance)
                },
                | Some(&Value::QuoteComputation(inner)) => {
                    (None, arena.comp_type(inner).cloned(), provenance)
                },
                | _ => (None, None, provenance),
            }
        };
        let inserted = Maybe::Present(Provenance::Inserted(Insertion::Quote));

        assert_eq!(
            quoted(0_usize),
            (Some(ValueType::Base(BaseType::Integer)), None, inserted),
            "a type atom where a value is read is its code"
        );
        assert!(
            matches!(quoted(1_usize), (None, Some(CompType::Returner(_)), _)),
            "a computation type is quoted at its own sort"
        );
        assert_eq!(
            quoted(2_usize).0,
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: Level::constant(LevelConstant::ZERO),
            }),
            "`Type` where a value is read is the code of the fuss-free universe"
        );
        assert!(
            matches!(quoted(3_usize), (Some(ValueType::Thunk(_)), None, _)),
            "a bridge where a value is read is the code of its thunk type"
        );
    }

    #[test]
    fn the_producer_does_not_admit_a_graded_bridge()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a : +U[ω] (-F Integer) ; def b : +U (-F Integer) ;"),
            &mut arena,
        );
        let lowered: Vec<_> = outcomes(&module)
            .into_iter()
            .map(|outcome| {
                let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_of(outcome))
                else {
                    panic!("the bridge lowers to the thunk type");
                };
                let Some(&CompType::Returner(returned)) = arena.comp_type(suspended)
                else {
                    panic!("the bridged computation is the returner");
                };
                arena.value_type(returned).cloned()
            })
            .collect();
        assert_eq!(
            lowered,
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the default grade `ω` is the bridge the core carries, the same as none written"
        );
        assert!(
            matches!(
                refusal(SourceText::from("def c : +U[1] (-F Integer) ;")),
                LoweringRefusal::GradedBridge { .. }
            ),
            "any other grade mints no thunk type"
        );
    }

    #[test]
    fn a_graded_bridge_is_refused_by_name()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        for (source, grade) in [
            ("def c : +U[1] (-F Integer) ;", "1"),
            ("def c : +U[r] (-F Integer) ;", "r"),
        ] {
            let refused = refusal(SourceText::from(source));
            assert_eq!(
                refused,
                LoweringRefusal::GradedBridge {
                    span: at(11_usize, 12_usize),
                    grade: SurfaceName::from(grade),
                },
                "`{source}` is refused at its grade, naming it"
            );
            assert_eq!(
                refused.classify(),
                FailureClass::Unrepresentable,
                "a grade is a form the fragment does not represent"
            );
        }
    }

    #[test]
    fn a_lambda_body_binds_its_own_de_bruijn_index()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x = thunk { fn (y) { ret y } } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Lambda(under)) = arena.computation(suspended)
        else {
            panic!("the lambda lowers to a lambda");
        };
        let Some(&Computation::Return(returned)) = arena.computation(under)
        else {
            panic!("the lambda's body lowers to a returner");
        };

        assert_eq!(
            arena.value(returned),
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            }),
            "the parameter is the innermost binder"
        );
    }

    #[test]
    fn an_earlier_declaration_resolves_as_a_constant()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = 3 ; def b = a ;"), &mut arena);
        let body = body_of(outcomes(&module)[1]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "a name declared earlier resolves to its admission position"
        );
    }

    #[test]
    fn the_empty_parentheses_lower_to_the_unit_value()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = () ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Unit),
            "`()` is the unit value"
        );
    }

    #[test]
    fn an_identifier_spelled_unit_is_an_ordinary_name()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def x = unit ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 12_usize),
                name: SurfaceName::from("unit"),
            },
            "`unit` is resolved like any other name, and nothing answers it"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unresolved name is the author's mistake"
        );
    }

    #[test]
    fn a_grouping_lowers_to_what_it_wraps()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def x = ( 3 ) ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the grouping mints nothing of its own"
        );
        assert_eq!(
            module.origins().value(body).map(|origin| origin.span()),
            Maybe::Present(at(10_usize, 11_usize)),
            "the value's origin is the wrapped form, not the parentheses"
        );
    }

    #[test]
    fn a_text_literal_lowers_with_its_escapes_decoded()
    {
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def s = \"a\\nb\" ;"), &mut arena);
        let body = body_of(outcomes(&module)[0]);

        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(text(SourceFragment::from("a\nb")))),
            "the escape is decoded into the character it names"
        );
    }

    #[test]
    fn force_and_application_lower_over_their_children()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { (force g)(3) } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[1]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the grouped force lowers to a force");
        };

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the forced value is the earlier declaration"
        );
        assert_eq!(
            arena.value(argument),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the argument is a value"
        );
    }

    #[test]
    fn a_function_tail_lowers_to_a_thunked_lambda_chain()
    {
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x: Integer, y: String) -> -F Integer { run z <- ret y ; ret x }",
            ),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("the tail declares one name");
        };
        let DeclarationOutcome::Completed {
            declared_type,
            body,
        } = declaration.outcome()
        else {
            panic!("a tail typing every parameter and its result writes both halves");
        };
        assert!(
            matches!(declaration.signature(), Maybe::Present(_))
                && declaration.signature() == declaration.definition(),
            "both halves are the one declaration form"
        );

        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&CompType::Arrow {
            domain: first,
            codomain: rest,
        }) = arena.comp_type(suspended)
        else {
            panic!("the first parameter is the outer arrow");
        };
        let Some(&CompType::Arrow {
            domain: second,
            codomain: result,
        }) = arena.comp_type(rest)
        else {
            panic!("the second parameter is the inner arrow");
        };
        let Some(&CompType::Returner(returned)) = arena.comp_type(result)
        else {
            panic!("the result is the written returner");
        };
        assert_eq!(
            [first, second, returned].map(|id| arena.value_type(id).cloned()),
            [
                Some(ValueType::Base(BaseType::Integer)),
                Some(ValueType::Base(BaseType::String)),
                Some(ValueType::Base(BaseType::Integer)),
            ],
            "the declared type is `+U (Integer -> String -> -F Integer)`"
        );

        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };
        let Some(&Computation::Lambda(outer)) = arena.computation(suspended)
        else {
            panic!("the first parameter is the outer lambda");
        };
        let Some(&Computation::Lambda(inner)) = arena.computation(outer)
        else {
            panic!("the second parameter is the inner lambda");
        };
        let Some(&Computation::Bind(bound, rest)) = arena.computation(inner)
        else {
            panic!("the statement is a bind");
        };
        let (Some(&Computation::Return(read)), Some(&Computation::Return(last))) =
            (arena.computation(bound), arena.computation(rest))
        else {
            panic!("the bound and the last computation are returners");
        };
        assert_eq!(
            [read, last].map(|id| arena.value(id).cloned()),
            [Some(variable(0_u32)), Some(variable(2_u32))],
            "`y` is innermost before the statement, and `x` sits under `y` and `z` after it"
        );
        assert_eq!(
            module
                .origins()
                .value(body)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Thunk)),
            "the body's thunk is the lowering's, not the source's"
        );
        assert_eq!(
            module
                .origins()
                .value_type(declared_type)
                .map(|origin| origin.provenance()),
            Maybe::Present(Provenance::Written),
            "the declared type is the function form's own"
        );
    }

    #[test]
    fn an_empty_parameter_list_lowers_to_a_thunked_computation()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def main() -> -F Integer { ret 3 }"),
            &mut arena,
        );
        let [
            DeclarationOutcome::Completed {
                declared_type,
                body,
            },
        ] = outcomes(&module)[..]
        else {
            panic!("a tail of no parameters writes both halves");
        };
        let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared_type)
        else {
            panic!("the declared type is a thunk type");
        };
        let Some(&Value::Thunk(computation)) = arena.value(body)
        else {
            panic!("the body is a thunk");
        };

        assert!(
            matches!(arena.comp_type(suspended), Some(&CompType::Returner(_))),
            "no arrow stands between `+U` and the result"
        );
        assert!(
            matches!(
                arena.computation(computation),
                Some(&Computation::Return(_))
            ),
            "no lambda stands between the thunk and the block"
        );
    }

    #[test]
    fn a_tail_missing_a_type_writes_its_definition_alone()
    {
        for source in [
            "def f(x: Integer) { ret x }",
            "def f(x, y: Integer) -> -F Integer { ret y }",
        ] {
            let mut arena = CoreArena::new();
            let module = lowered(SourceText::from(source), &mut arena);
            let [ref declaration] = *module.declarations()
            else {
                panic!("`{source}` declares one name");
            };

            assert!(
                matches!(declaration.outcome(), DeclarationOutcome::Bodied { .. }),
                "`{source}` lowers its body alone"
            );
            assert!(
                matches!(declaration.signature(), Maybe::Absent(_)),
                "`{source}` writes no signature"
            );
        }
    }

    #[test]
    fn a_block_binds_each_statement_over_the_next()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let variable = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def a = thunk { run x <- ret 1 ; run y <- ret x ; ret x } ;"),
            &mut arena,
        );
        let body = body_of(outcomes(&module)[0]);
        let Some(&Value::Thunk(suspended)) = arena.value(body)
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Bind(first, rest)) = arena.computation(suspended)
        else {
            panic!("the first statement is the outer bind");
        };
        let Some(&Computation::Bind(second, last)) = arena.computation(rest)
        else {
            panic!("the second statement binds over the rest of the block");
        };
        let returned = |id| match arena.computation(id) {
            | Some(&Computation::Return(value)) => arena.value(value).cloned(),
            | _ => None,
        };

        assert_eq!(
            [returned(first), returned(second), returned(last)],
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(variable(0_u32)),
                Some(variable(1_u32)),
            ],
            "each statement's name binds over everything after it"
        );
        assert_eq!(
            module
                .origins()
                .computation(suspended)
                .map(|origin| origin.span()),
            Maybe::Present(at(16_usize, 19_usize)),
            "a bind's origin is its statement's `run`"
        );
    }

    #[test]
    fn a_call_applies_its_arguments_left_to_right()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def g = thunk { fn (x) { fn (y) { ret x } } } ; def h = thunk { g(1, 2) } ; \
                 def k = thunk { g() } ;",
            ),
            &mut arena,
        );
        let called = |declaration: usize| {
            let Some(&Value::Thunk(suspended)) =
                arena.value(body_of(outcomes(&module)[declaration]))
            else {
                panic!("the thunk lowers to a thunk value");
            };
            suspended
        };
        let Some(&Computation::Application(inner, second)) = arena.computation(called(1_usize))
        else {
            panic!("the last argument is the outer application");
        };
        let Some(&Computation::Application(head, first)) = arena.computation(inner)
        else {
            panic!("the first argument is the inner application");
        };

        assert_eq!(
            [first, second].map(|id| arena.value(id).cloned()),
            [
                Some(Value::Literal(integer(SourceFragment::from("1")))),
                Some(Value::Literal(integer(SourceFragment::from("2")))),
            ],
            "the arguments apply left to right"
        );
        assert!(
            matches!(arena.computation(head), Some(&Computation::Force(_))),
            "the head is applied to the first argument"
        );
        assert!(
            matches!(
                arena.computation(called(2_usize)),
                Some(&Computation::Force(_))
            ),
            "a call of no arguments is its head"
        );
    }

    #[test]
    fn a_value_head_is_forced_and_marked_inserted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = thunk { fn (x) { ret x } } ; def h = thunk { g(1) } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the value head is forced");
        };
        let origin = module.origins().computation(head);

        assert_eq!(
            arena.value(forced),
            Some(&Value::Constant(ConstantIndex::from(0_usize))),
            "the force is over the name the source wrote"
        );
        assert_eq!(
            origin.map(|inserted| inserted.provenance()),
            Maybe::Present(Provenance::Inserted(Insertion::Force)),
            "the force is the lowering's, not the source's"
        );
        assert_eq!(
            origin.map(|inserted| inserted.span()),
            Maybe::Present(at(53_usize, 54_usize)),
            "the inserted force names the head whose position demanded it"
        );
    }

    #[test]
    fn an_author_written_force_is_not_marked_inserted()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def g = 3 ; def a = thunk { (force g)(3) } ;"),
            &mut arena,
        );
        let Some(&Value::Thunk(suspended)) = arena.value(body_of(outcomes(&module)[1]))
        else {
            panic!("the thunk lowers to a thunk value");
        };
        let Some(&Computation::Application(head, _argument)) = arena.computation(suspended)
        else {
            panic!("the call lowers to an application");
        };
        let Some(&Computation::Force(forced)) = arena.computation(head)
        else {
            panic!("the written force is the head");
        };

        assert!(
            matches!(arena.value(forced), Some(&Value::Constant(_))),
            "a computation head gains no second force"
        );
        assert_eq!(
            module
                .origins()
                .computation(head)
                .map(|written| written.provenance()),
            Maybe::Present(Provenance::Written),
            "the force the source wrote is the source's"
        );
    }

    #[test]
    fn a_positive_result_gains_a_returner_once()
    {
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                "def f(x: Integer) -> Integer { ret x } def g(x: Integer) -> -F Integer { ret x }",
            ),
            &mut arena,
        );
        let result = |declaration: usize| {
            let declared = declared_of(outcomes(&module)[declaration]);
            let Some(&ValueType::Thunk(suspended)) = arena.value_type(declared)
            else {
                panic!("the declared type is a thunk type");
            };
            let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(suspended)
            else {
                panic!("the parameter is an arrow");
            };
            let Some(&CompType::Returner(returned)) = arena.comp_type(codomain)
            else {
                panic!("the result is a returner");
            };
            (
                arena.value_type(returned).cloned(),
                module
                    .origins()
                    .comp_type(codomain)
                    .map(|origin| origin.provenance()),
            )
        };

        assert_eq!(
            result(0_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Inserted(Insertion::Returner))
            ),
            "a value type at the result gains the lowering's returner"
        );
        assert_eq!(
            result(1_usize),
            (
                Some(ValueType::Base(BaseType::Integer)),
                Maybe::Present(Provenance::Written)
            ),
            "a written returner is the only one, and the source's"
        );
    }

    #[test]
    fn a_self_reference_is_unresolved()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = a ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("a"),
            },
            "a declaration is not in scope in its own body"
        );
    }

    #[test]
    fn an_undefined_term_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = b ;")),
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "a name nothing declares is refused where it stands"
        );
    }

    #[test]
    fn an_undefined_type_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : Intgr ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 13_usize),
                name: SurfaceName::from("Intgr"),
                arity: HeadArity::Nullary,
            },
            "a misspelt head is a mistake, not a new nominal type"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unresolved head is the author's mistake"
        );
    }

    #[test]
    fn an_applied_nullary_head_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Unit Integer ;")),
            LoweringRefusal::MalformedForm {
                span: at(13_usize, 20_usize),
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            "juxtaposition is not application: the second head is an operand too many"
        );
    }

    #[test]
    fn an_applied_head_no_former_answers_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Unary,
            },
            "a head applied to one argument is looked up among the unary formers"
        );
        assert_eq!(
            refusal(SourceText::from("def a : Foo(Integer, String) ;")),
            LoweringRefusal::UnresolvedTypeHead {
                span: at(8_usize, 11_usize),
                name: SurfaceName::from("Foo"),
                arity: HeadArity::Polyadic(OperandCount::from(2_usize)),
            },
            "no former takes two arguments, and the refusal says how many were written"
        );
    }

    #[test]
    fn the_reserved_product_is_declined()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("def a : Integer * Integer ;"));

        assert_eq!(
            refused,
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 25_usize),
                form: FormName::from(NamedKind("product_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::Reserved,
            },
            "the product parses and is declined by name"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::Unrepresentable,
            "a reserved form is outside the fragment, not the author's mistake"
        );
    }

    #[test]
    fn the_reserved_pair_is_declined()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = ( 1 , 2 ) ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 17_usize),
                form: FormName::TUPLE,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Reserved,
            },
            "the pair parses and is declined by name"
        );
    }

    #[test]
    fn an_arrow_at_declaration_sort_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a : Integer -> -F Integer ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 29_usize),
                form: FormName::from(NamedKind("function_type")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "a declaration's type is a value type, and an arrow is a computation type"
        );
    }

    #[test]
    fn a_lambda_in_value_position_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("def a = fn (y) { ret y } ;")),
            LoweringRefusal::OutOfFragment {
                span: at(8_usize, 24_usize),
                form: FormName::from(NamedKind("lambda_expression")),
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            "a lambda is a computation and must be suspended to stand as a value"
        );
    }

    #[test]
    fn forms_outside_the_fragment_are_unadmitted()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let unadmitted = |start: usize, end: usize, form: FormName, sort: FragmentSort| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort,
                boundary: FragmentBoundary::Unadmitted,
            }
        };
        let rows = [
            (
                "def a = 1.5 ;",
                unadmitted(
                    8_usize,
                    11_usize,
                    FormName::from(NamedKind("number")),
                    FragmentSort::Value,
                ),
            ),
            (
                "def a = thunk { val y = 3; ret y } ;",
                unadmitted(
                    16_usize,
                    19_usize,
                    FormName::LET_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { fork (x : Integer) { ret 1 } as y ; ret 2 } ;",
                unadmitted(
                    16_usize,
                    20_usize,
                    FormName::FORK_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { ret 1; ret 2 } ;",
                unadmitted(
                    16_usize,
                    22_usize,
                    FormName::EXPRESSION_STATEMENT,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def a = thunk { run _ <- ret 1; ret 2 } ;",
                unadmitted(
                    20_usize,
                    21_usize,
                    FormName::from(NamedKind("wildcard")),
                    FragmentSort::Pattern,
                ),
            ),
            (
                "def a = thunk { run y : -F Integer <- ret 1; ret y } ;",
                unadmitted(
                    22_usize,
                    23_usize,
                    FormName::ANNOTATION,
                    FragmentSort::Computation,
                ),
            ),
            (
                "def f @[a : Type] (x) { ret x }",
                unadmitted(
                    0_usize,
                    31_usize,
                    FormName::PARAMETERS,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def rec f(x) { ret x }",
                unadmitted(
                    0_usize,
                    22_usize,
                    FormName::RECURSIVE,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def f(A) { ret 1 }",
                unadmitted(
                    6_usize,
                    7_usize,
                    FormName::PARAMETER,
                    FragmentSort::Declaration,
                ),
            ),
            (
                "def a = (3 : Integer) ;",
                unadmitted(8_usize, 21_usize, FormName::ANNOTATION, FragmentSort::Value),
            ),
            (
                "def a = \"a${b}\" ;",
                unadmitted(
                    8_usize,
                    15_usize,
                    FormName::INTERPOLATION,
                    FragmentSort::Value,
                ),
            ),
        ];
        for (source, expected) in rows {
            let refused = refusal(SourceText::from(source));
            assert_eq!(refused, expected, "`{source}` is outside the fragment");
            assert_eq!(
                refused.classify(),
                FailureClass::Unrepresentable,
                "`{source}` is unrepresentable, not malformed"
            );
        }
    }

    #[test]
    fn a_form_offered_the_wrong_operand_count_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let arity = |start: usize, end: usize, form: FormName, count: usize| {
            LoweringRefusal::OutOfFragment {
                span: at(start, end),
                form,
                sort: FragmentSort::Computation,
                boundary: FragmentBoundary::Arity(OperandCount::from(count)),
            }
        };
        let rows = [
            (
                "def a = thunk { fn (x, y) { ret x } } ;",
                arity(
                    16_usize,
                    35_usize,
                    FormName::from(NamedKind("lambda_expression")),
                    2_usize,
                ),
            ),
            (
                "def a = thunk {} ;",
                arity(14_usize, 16_usize, FormName::BLOCK, 0_usize),
            ),
            (
                "def a = thunk { run x <- ret 1; } ;",
                arity(14_usize, 33_usize, FormName::BLOCK, 0_usize),
            ),
        ];
        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "`{source}` offers its form the wrong number of operands"
            );
        }
    }

    #[test]
    fn a_malformed_integer_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 10_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(11_usize, 12_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 12_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 12_usize), &[declaration]);
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 10_usize),
                form: FormName::from(NamedKind("number")),
            },
            "a number whose text is not digits is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a malformed literal is the author's mistake"
        );
    }

    #[test]
    fn a_malformed_text_literal_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = \"abc ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("string.expression"),
            Spelled("\""),
            at(8_usize, 12_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(13_usize, 14_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 14_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.module(at(0_usize, 14_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedLiteral {
                span: at(8_usize, 12_usize),
                form: FormName::from(NamedKind("string")),
            },
            "a string missing its closing quote is refused"
        );
    }

    #[test]
    fn a_repaired_declaration_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let tree = repaired(&pbg, SourceText::from("def x ;"));
        let refused = refusal_in(&pbg, &tree);

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(5_usize, 5_usize),
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(Repair::Grout(GroutShape::Postfix)),
            },
            "the grout the parser inserted is reported where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a repaired form is the author's mistake"
        );
    }

    #[test]
    fn a_juxtaposed_operand_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        let refused = refusal(SourceText::from("def a = thunk { ret 1 2 } ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MalformedForm {
                span: at(22_usize, 23_usize),
                form: FormName::from(NamedKind("thunk_expression")),
                fault: FormFault::ExtraOperand,
            },
            "a thunk's block holds one computation, and a second juxtaposed beside it is \
             refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a juxtaposition is the author's mistake"
        );
        assert_eq!(
            refusal(SourceText::from("def f(x: Integer Integer) { ret x }")),
            LoweringRefusal::MalformedForm {
                span: at(17_usize, 24_usize),
                form: FormName::FUNCTION,
                fault: FormFault::ExtraOperand,
            },
            "a parameter's type is one form, and a second juxtaposed beside it is refused as \
             the function's"
        );
    }

    #[test]
    fn a_tile_out_of_place_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def x ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(6_usize, 7_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 7_usize), &[
            keyword, name, close,
        ]);
        let tree = made.module(at(0_usize, 7_usize), &[declaration]);

        assert_eq!(
            refusal_in(&pbg, &tree),
            LoweringRefusal::MalformedForm {
                span: at(6_usize, 7_usize),
                form: FormName::DECLARATION,
                fault: FormFault::MisplacedTile,
            },
            "a declaration with no tail closes where its tail should open"
        );
    }

    #[test]
    fn a_root_that_is_not_a_module_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let mut made = Handmade::new(&pbg, SourceText::from("def a = 3 ;"));
        let keyword = made.tile(Rule("def_value"), Spelled("def"), at(0_usize, 3_usize));
        let name = made.tile(
            Rule("def_value"),
            Spelled("identifier"),
            at(4_usize, 5_usize),
        );
        let equals = made.tile(Rule("def_value"), Spelled("="), at(6_usize, 7_usize));
        let body = made.tile(
            Rule("number.expression"),
            Spelled("number"),
            at(8_usize, 9_usize),
        );
        let close = made.tile(Rule("def_value"), Spelled(";"), at(10_usize, 11_usize));
        let declaration = made.meld(Rule("def_value"), Spelled("def"), at(0_usize, 11_usize), &[
            keyword, name, equals, body, close,
        ]);
        let tree = made.finish(declaration);
        let mut arena = CoreArena::new();

        assert_eq!(
            lower_module(
                &pbg,
                &tree,
                &mut arena,
                LoweringBudget::DEFAULT,
                Recognition::default()
            ),
            Err(LoweringRefusal::OutOfFragment {
                span: at(0_usize, 11_usize),
                form: FormName::DECLARATION,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            }),
            "a tree rooted at a declaration is not a module"
        );
    }

    #[test]
    fn a_tree_of_another_grammar_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = GrammarFingerprint::from(0_u64);
        let mut made = Handmade::under(&pbg, SourceText::from("x"), foreign);
        let name = made.tile(
            Rule("identifier.expression"),
            Spelled("identifier"),
            at(0_usize, 1_usize),
        );
        let tree = made.module(at(0_usize, 1_usize), &[name]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::GrammarMismatch {
                tree: foreign,
                grammar: pbg.fingerprint(),
            },
            "a tree molded under another grammar is refused before any mold is read"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "the caller paired the wrong tree and grammar"
        );
        assert_eq!(
            refused.span(),
            Maybe::Absent(refusal_span::Absent::Run),
            "the refusal is about the run, not a position in the source"
        );
    }

    #[test]
    fn a_mold_the_grammar_does_not_hold_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let pbg = grammar();
        let foreign = MoldId::from(u32::MAX);
        let mut made = Handmade::new(&pbg, SourceText::from("x"));
        let stray = made.raw(NodeLabel::Tile(foreign), at(0_usize, 1_usize), &[]);
        let tree = made.module(at(0_usize, 1_usize), &[stray]);
        let mut arena = CoreArena::new();
        let refused = lower_module(
            &pbg,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::UnknownMold {
                span: at(0_usize, 1_usize),
                mold: foreign,
            },
            "a mold outside the grammar's table is refused where it stands"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "a foreign mold is the engine's fault, not the author's"
        );
    }

    #[test]
    fn an_unknown_attribute_is_refused_with_its_suggestion()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ check ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::UnknownAttribute {
                span: at(3_usize, 8_usize),
                name: SurfaceName::from("check"),
                suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
            },
            "a near miss is refused with the registered name it nearly spells"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an unknown attribute is the author's mistake"
        );
    }

    #[test]
    fn an_attribute_written_twice_for_one_name_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ checks ] @[ checks ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::DuplicateAttribute {
                span: at(15_usize, 21_usize),
                name: SurfaceName::from("checks"),
                first: at(3_usize, 9_usize),
            },
            "the second spelling is refused, naming the first"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a duplicate attribute is the author's mistake"
        );
    }

    #[test]
    fn a_schema_taking_a_payload_refuses_an_absent_one()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::MissingPayload {
                span: at(3_usize, 7_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
            },
            "an attribute whose schema takes a payload is refused without one"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a missing payload is the author's mistake"
        );
    }

    #[test]
    fn a_non_value_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(ret 1) ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::NonValuePayload {
                span: at(8_usize, 13_usize),
                name: registered(SurfaceName::from("owes")),
                form: FormName::from(NamedKind("ret_expression")),
            },
            "a computation cannot stand as a payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "a non-value payload is the author's mistake"
        );
    }

    #[test]
    fn a_payload_of_the_wrong_form_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let refused = refusal(SourceText::from("@[ owes(\"one\") ] def a = 3 ;"));

        assert_eq!(
            refused,
            LoweringRefusal::IllTypedPayload {
                span: at(8_usize, 13_usize),
                name: registered(SurfaceName::from("owes")),
                expected: schema_of(SurfaceName::from("owes")),
                written: payload_form(Former::Text),
            },
            "a payload whose form the schema does not admit is refused at the payload"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::MalformedSource,
            "an ill-typed payload is the author's mistake"
        );
    }

    #[test]
    fn a_marker_given_a_payload_is_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));

        assert_eq!(
            refusal(SourceText::from("@[ checks(1) ] def a = 3 ;")),
            LoweringRefusal::IllTypedPayload {
                span: at(10_usize, 11_usize),
                name: registered(SurfaceName::from("checks")),
                expected: AttributeSchema::Marker,
                written: payload_form(Former::Number),
            },
            "a marker takes no payload, and one written is refused at the payload"
        );
    }

    #[test]
    fn an_attribute_is_filed_under_its_declaration_digest()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("@[ owes(1) ] def a : Integer ;"),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("one name is declared");
        };
        let Maybe::Present(key) = declaration.signature()
        else {
            panic!("the name has a signature");
        };
        let [ref entry] = *module.attributes().entries(key)
        else {
            panic!("one attribute is filed under the signature");
        };

        assert_eq!(
            (entry.name(), entry.span()),
            (registered(SurfaceName::from("owes")), at(3_usize, 10_usize)),
            "the entry names the attribute and where it was written"
        );
        let Maybe::Present(payload) = entry.payload()
        else {
            panic!("the entry carries its payload");
        };
        assert_eq!(
            arena.value(payload),
            Some(&Value::Literal(integer(SourceFragment::from("1")))),
            "the payload is the lowered value"
        );
    }

    #[test]
    fn a_refused_declarations_attributes_are_filed_under_its_digest()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from(
                r#"@[ refuses("UnresolvedName") ] def a = b ; @[ owes(1) ] def c : Intgr ;"#,
            ),
            &mut arena,
        );
        let [ref defined, ref signed] = *module.declarations()
        else {
            panic!("two names are declared");
        };

        assert_eq!(
            (defined.outcome(), signed.outcome()),
            (
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedName {
                    span: at(39_usize, 40_usize),
                    name: SurfaceName::from("b"),
                }),
                DeclarationOutcome::Refused(LoweringRefusal::UnresolvedTypeHead {
                    span: at(64_usize, 69_usize),
                    name: SurfaceName::from("Intgr"),
                    arity: HeadArity::Nullary,
                }),
            ),
            "both declarations are refused by their operands"
        );
        let (Maybe::Present(definition), Maybe::Present(signature)) =
            (defined.definition(), signed.signature())
        else {
            panic!("each refused name keeps the digest of the form it wrote");
        };
        let [ref refuses] = *module.attributes().entries(definition)
        else {
            panic!("one attribute is filed under the refused definition");
        };
        let [ref owes] = *module.attributes().entries(signature)
        else {
            panic!("one attribute is filed under the refused signature");
        };
        assert_eq!(
            ((refuses.name(), refuses.span()), (owes.name(), owes.span())),
            (
                (
                    registered(SurfaceName::from("refuses")),
                    at(3_usize, 28_usize)
                ),
                (
                    registered(SurfaceName::from("owes")),
                    at(46_usize, 53_usize)
                ),
            ),
            "each entry names its attribute and where it was written"
        );
        let (Maybe::Present(named), Maybe::Present(counted)) = (refuses.payload(), owes.payload())
        else {
            panic!("each entry carries its payload");
        };
        assert_eq!(
            (arena.value(named), arena.value(counted)),
            (
                Some(&Value::Literal(text(SourceFragment::from(
                    "UnresolvedName"
                )))),
                Some(&Value::Literal(integer(SourceFragment::from("1")))),
            ),
            "a refused declaration's payloads are lowered all the same"
        );
    }

    #[test]
    fn the_attribute_diagnostics_fire_on_a_refused_declaration()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let owes = registered(SurfaceName::from("owes"));
        let rows = [
            (
                r#"@[ check ] def a = b ;"#,
                LoweringRefusal::UnknownAttribute {
                    span: at(3_usize, 8_usize),
                    name: SurfaceName::from("check"),
                    suggestion: Maybe::Present(registered(SurfaceName::from("checks"))),
                },
            ),
            (
                r#"@[ checks ] @[ checks ] def a = b ;"#,
                LoweringRefusal::DuplicateAttribute {
                    span: at(15_usize, 21_usize),
                    name: SurfaceName::from("checks"),
                    first: at(3_usize, 9_usize),
                },
            ),
            (
                r#"@[ owes ] def a = b ;"#,
                LoweringRefusal::MissingPayload {
                    span: at(3_usize, 7_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                },
            ),
            (
                r#"@[ owes(ret 1) ] def a = b ;"#,
                LoweringRefusal::NonValuePayload {
                    span: at(8_usize, 13_usize),
                    name: owes,
                    form: FormName::from(NamedKind("ret_expression")),
                },
            ),
            (
                r#"@[ owes("one") ] def a = b ;"#,
                LoweringRefusal::IllTypedPayload {
                    span: at(8_usize, 13_usize),
                    name: owes,
                    expected: schema_of(SurfaceName::from("owes")),
                    written: payload_form(Former::Text),
                },
            ),
        ];

        for (source, expected) in rows {
            assert_eq!(
                refusal(SourceText::from(source)),
                expected,
                "the attribute's refusal sits before the body's in `{source}` and is the one kept"
            );
        }
    }

    #[test]
    fn every_minted_node_has_an_origin()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(
            SourceText::from("def x : Integer ; def x = 3 ;"),
            &mut arena,
        );
        let [ref declaration] = *module.declarations()
        else {
            panic!("one name is declared");
        };
        let origins = module.origins();

        assert_eq!(
            origins
                .value_type(declared_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(8_usize, 15_usize)),
            "the declared type's origin is the type it was written as"
        );
        assert_eq!(
            origins
                .value(body_of(declaration.outcome()))
                .map(|origin| origin.span()),
            Maybe::Present(at(26_usize, 27_usize)),
            "the body's origin is the value it was written as"
        );
        assert_eq!(
            origins
                .declaration(declaration.origin())
                .map(|origin| origin.span()),
            Maybe::Present(at(0_usize, 17_usize)),
            "the declaration's origin is the form that introduced the name"
        );
        assert_eq!(
            origins.recorded_count(),
            OriginCount::from(2_usize),
            "exactly the two minted nodes have origins"
        );
    }

    #[test]
    fn a_refused_declaration_leaves_the_others_lowered()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from("def a = b ; def c = 3 ;"), &mut arena);
        let [
            DeclarationOutcome::Refused(refused),
            DeclarationOutcome::Bodied { body },
        ] = outcomes(&module)[..]
        else {
            panic!("the first declaration refuses and the second lowers");
        };

        assert_eq!(
            refused,
            LoweringRefusal::UnresolvedName {
                span: at(8_usize, 9_usize),
                name: SurfaceName::from("b"),
            },
            "the first declaration carries its own refusal"
        );
        assert_eq!(
            arena.value(body),
            Some(&Value::Literal(integer(SourceFragment::from("3")))),
            "the second declaration lowers regardless"
        );
    }

    #[test]
    fn a_module_past_the_allowance_is_refused()
    {
        let pbg = grammar();
        let tree = parsed(&pbg, SourceText::from("def a = 3 ;"));
        let mut arena = CoreArena::new();
        let budget = LoweringBudget::from(1_usize);
        let refused =
            lower_module(&pbg, &tree, &mut arena, budget, Recognition::default()).unwrap_err();

        assert_eq!(
            refused,
            LoweringRefusal::BudgetExceeded { budget },
            "a module costing more than the allowance is refused"
        );
        assert_eq!(
            refused.classify(),
            FailureClass::EngineFault,
            "running out of allowance is the engine's fault, not the author's"
        );
    }

    #[test]
    fn only_the_value_forms_can_stand_as_a_payload()
    {
        let values = [
            Former::Name,
            Former::Constructor,
            Former::Number,
            Former::Text,
            Former::Parenthesized,
            Former::Thunk,
        ];
        for former in Former::ALL {
            assert_eq!(
                is_value_form(former).0,
                values.contains(&former),
                "{former:?} can stand as a value exactly when it produces one"
            );
        }
    }

    #[test]
    fn an_integer_literal_is_its_canonical_magnitude()
    {
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("007")),
            Maybe::Present(integer(SourceFragment::from("7"))),
            "a padded spelling is the unpadded literal"
        );
        assert_eq!(
            parse_literal(Former::Number, SourceFragment::from("0")),
            Maybe::Present(integer(SourceFragment::from("0"))),
            "zero is a literal"
        );
    }

    #[test]
    fn a_text_literal_is_the_bytes_between_its_quotes()
    {
        let rows = [
            ("\"abc\"", "abc"),
            ("\"\"", ""),
            ("\"a\\tb\\\\c\\q\"", "a\tb\\cq"),
            ("\"a\\\"b\\'c\\0\\r\"", "a\"b'c\0\r"),
            ("\"a\\\nb\"", "ab"),
            ("\"a\\\r\nb\"", "ab"),
            ("\"ab\\\"", "ab"),
        ];
        for (spelled, content) in rows {
            assert_eq!(
                parse_literal(Former::Text, SourceFragment::from(spelled)),
                Maybe::Present(text(SourceFragment::from(content))),
                "`{spelled}` decodes to its content"
            );
        }
    }

    #[test]
    fn a_lexeme_of_the_wrong_shape_parses_to_nothing()
    {
        let rows = [
            (Former::Number, "", literal::Absent::Malformed),
            (Former::Number, "3x", literal::Absent::Malformed),
            (Former::Text, "\"abc", literal::Absent::Malformed),
            (Former::Text, "\"", literal::Absent::Malformed),
            (Former::Text, "abc", literal::Absent::Malformed),
            (Former::Name, "abc", literal::Absent::NotALiteral),
        ];
        for (former, spelled, reason) in rows {
            assert_eq!(
                parse_literal(former, SourceFragment::from(spelled)),
                Maybe::Absent(reason),
                "`{spelled}` is not a {former:?} literal"
            );
        }
    }

    #[test]
    fn the_last_step_of_an_allowance_is_spendable()
    {
        let mut fuel = Fuel::new(LoweringBudget::from(1_usize));

        assert_eq!(fuel.spend(), Ok(()), "an allowance of one admits one step");
    }

    #[test]
    fn a_step_past_the_allowance_is_refused()
    {
        let budget = LoweringBudget::from(1_usize);
        let mut fuel = Fuel::new(budget);
        let _first = fuel.spend();

        assert_eq!(
            fuel.spend(),
            Err(LoweringRefusal::BudgetExceeded { budget }),
            "the step past the allowance is refused, naming the allowance"
        );
    }
}
